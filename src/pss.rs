//! Support for the [Probabilistic Signature Scheme] (PSS) a.k.a. RSASSA-PSS.
//!
//! Designed by Mihir Bellare and Phillip Rogaway. Specified in [RFC8017 § 8.1].
//!
//! # Usage
//!
//! See [code example in the toplevel rustdoc](../index.html#pss-signatures).
//!
//! [Probabilistic Signature Scheme]: https://en.wikipedia.org/wiki/Probabilistic_signature_scheme
//! [RFC8017 § 8.1]: https://datatracker.ietf.org/doc/html/rfc8017#section-8.1

use alloc::boxed::Box;
use alloc::vec::Vec;

use core::fmt::{Debug, Display, Formatter, LowerHex, UpperHex};
use core::marker::PhantomData;
use digest::{Digest, DynDigest, FixedOutputReset};
use pkcs8::{Document, EncodePrivateKey, EncodePublicKey, SecretDocument};
use rand_core::CryptoRngCore;
use signature::{
    hazmat::{PrehashVerifier, RandomizedPrehashSigner},
    DigestVerifier, Keypair, RandomizedDigestSigner, RandomizedSigner, SignatureEncoding, Verifier,
};
use subtle::ConstantTimeEq;

use crate::algorithms::{mgf1_xor, mgf1_xor_digest};
use crate::errors::{Error, Result};
use crate::key::{PrivateKey, PublicKey};
use crate::{RsaPrivateKey, RsaPublicKey};

/// RSASSA-PSS signatures as described in [RFC8017 § 8.1].
///
/// [RFC8017 § 8.1]: https://datatracker.ietf.org/doc/html/rfc8017#section-8.1
#[derive(Clone, PartialEq, Eq)]
pub struct Signature {
    bytes: Box<[u8]>,
}

impl SignatureEncoding for Signature {
    type Repr = Box<[u8]>;
}

impl From<Box<[u8]>> for Signature {
    fn from(bytes: Box<[u8]>) -> Self {
        Self { bytes }
    }
}

impl<'a> TryFrom<&'a [u8]> for Signature {
    type Error = signature::Error;

    fn try_from(bytes: &'a [u8]) -> signature::Result<Self> {
        Ok(Self {
            bytes: bytes.into(),
        })
    }
}

impl From<Signature> for Box<[u8]> {
    fn from(signature: Signature) -> Box<[u8]> {
        signature.bytes
    }
}

impl Debug for Signature {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> core::result::Result<(), core::fmt::Error> {
        fmt.debug_list().entries(self.bytes.iter()).finish()
    }
}

impl AsRef<[u8]> for Signature {
    fn as_ref(&self) -> &[u8] {
        self.bytes.as_ref()
    }
}

impl LowerHex for Signature {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        for byte in self.bytes.iter() {
            write!(f, "{:02x}", byte)?;
        }
        Ok(())
    }
}

impl UpperHex for Signature {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        for byte in self.bytes.iter() {
            write!(f, "{:02X}", byte)?;
        }
        Ok(())
    }
}

impl Display for Signature {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:X}", self)
    }
}

pub(crate) fn verify<PK: PublicKey>(
    pub_key: &PK,
    hashed: &[u8],
    sig: &[u8],
    digest: &mut dyn DynDigest,
) -> Result<()> {
    if sig.len() != pub_key.size() {
        return Err(Error::Verification);
    }

    let em_bits = pub_key.n().bits() - 1;
    let em_len = (em_bits + 7) / 8;
    let mut em = pub_key.raw_encryption_primitive(sig, em_len)?;

    emsa_pss_verify(hashed, &mut em, em_bits, None, digest)
}

pub(crate) fn verify_digest<PK, D>(pub_key: &PK, hashed: &[u8], sig: &[u8]) -> Result<()>
where
    PK: PublicKey,
    D: Digest + FixedOutputReset,
{
    if sig.len() != pub_key.size() {
        return Err(Error::Verification);
    }

    let em_bits = pub_key.n().bits() - 1;
    let em_len = (em_bits + 7) / 8;
    let mut em = pub_key.raw_encryption_primitive(sig, em_len)?;

    emsa_pss_verify_digest::<D>(hashed, &mut em, em_bits, None)
}

/// SignPSS calculates the signature of hashed using RSASSA-PSS.
///
/// Note that hashed must be the result of hashing the input message using the
/// given hash function. The opts argument may be nil, in which case sensible
/// defaults are used.
pub(crate) fn sign<T: CryptoRngCore, SK: PrivateKey>(
    rng: &mut T,
    blind: bool,
    priv_key: &SK,
    hashed: &[u8],
    salt_len: Option<usize>,
    digest: &mut dyn DynDigest,
) -> Result<Vec<u8>> {
    let salt = generate_salt(rng, priv_key, salt_len, digest.output_size());

    sign_pss_with_salt(blind.then(|| rng), priv_key, hashed, &salt, digest)
}

pub(crate) fn sign_digest<
    T: CryptoRngCore + ?Sized,
    SK: PrivateKey,
    D: Digest + FixedOutputReset,
>(
    rng: &mut T,
    blind: bool,
    priv_key: &SK,
    hashed: &[u8],
    salt_len: Option<usize>,
) -> Result<Vec<u8>> {
    let salt = generate_salt(rng, priv_key, salt_len, <D as Digest>::output_size());

    sign_pss_with_salt_digest::<_, _, D>(blind.then(|| rng), priv_key, hashed, &salt)
}

fn generate_salt<T: CryptoRngCore + ?Sized, SK: PrivateKey>(
    rng: &mut T,
    priv_key: &SK,
    salt_len: Option<usize>,
    digest_size: usize,
) -> Vec<u8> {
    let salt_len = salt_len.unwrap_or_else(|| priv_key.size() - 2 - digest_size);

    let mut salt = vec![0; salt_len];
    rng.fill_bytes(&mut salt[..]);

    salt
}

/// signPSSWithSalt calculates the signature of hashed using PSS with specified salt.
///
/// Note that hashed must be the result of hashing the input message using the
/// given hash function. salt is a random sequence of bytes whose length will be
/// later used to verify the signature.
fn sign_pss_with_salt<T: CryptoRngCore, SK: PrivateKey>(
    blind_rng: Option<&mut T>,
    priv_key: &SK,
    hashed: &[u8],
    salt: &[u8],
    digest: &mut dyn DynDigest,
) -> Result<Vec<u8>> {
    let em_bits = priv_key.n().bits() - 1;
    let em = emsa_pss_encode(hashed, em_bits, salt, digest)?;

    priv_key.raw_decryption_primitive(blind_rng, &em, priv_key.size())
}

fn sign_pss_with_salt_digest<
    T: CryptoRngCore + ?Sized,
    SK: PrivateKey,
    D: Digest + FixedOutputReset,
>(
    blind_rng: Option<&mut T>,
    priv_key: &SK,
    hashed: &[u8],
    salt: &[u8],
) -> Result<Vec<u8>> {
    let em_bits = priv_key.n().bits() - 1;
    let em = emsa_pss_encode_digest::<D>(hashed, em_bits, salt)?;

    priv_key.raw_decryption_primitive(blind_rng, &em, priv_key.size())
}

fn emsa_pss_encode(
    m_hash: &[u8],
    em_bits: usize,
    salt: &[u8],
    hash: &mut dyn DynDigest,
) -> Result<Vec<u8>> {
    // See [1], section 9.1.1
    let h_len = hash.output_size();
    let s_len = salt.len();
    let em_len = (em_bits + 7) / 8;

    // 1. If the length of M is greater than the input limitation for the
    //     hash function (2^61 - 1 octets for SHA-1), output "message too
    //     long" and stop.
    //
    // 2.  Let mHash = Hash(M), an octet string of length hLen.
    if m_hash.len() != h_len {
        return Err(Error::InputNotHashed);
    }

    // 3. If em_len < h_len + s_len + 2, output "encoding error" and stop.
    if em_len < h_len + s_len + 2 {
        // TODO: Key size too small
        return Err(Error::Internal);
    }

    let mut em = vec![0; em_len];

    let (db, h) = em.split_at_mut(em_len - h_len - 1);
    let h = &mut h[..(em_len - 1) - db.len()];

    // 4. Generate a random octet string salt of length s_len; if s_len = 0,
    //     then salt is the empty string.
    //
    // 5.  Let
    //       M' = (0x)00 00 00 00 00 00 00 00 || m_hash || salt;
    //
    //     M' is an octet string of length 8 + h_len + s_len with eight
    //     initial zero octets.
    //
    // 6.  Let H = Hash(M'), an octet string of length h_len.
    let prefix = [0u8; 8];

    hash.update(&prefix);
    hash.update(m_hash);
    hash.update(salt);

    let hashed = hash.finalize_reset();
    h.copy_from_slice(&hashed);

    // 7.  Generate an octet string PS consisting of em_len - s_len - h_len - 2
    //     zero octets. The length of PS may be 0.
    //
    // 8.  Let DB = PS || 0x01 || salt; DB is an octet string of length
    //     emLen - hLen - 1.
    db[em_len - s_len - h_len - 2] = 0x01;
    db[em_len - s_len - h_len - 1..].copy_from_slice(salt);

    // 9.  Let dbMask = MGF(H, emLen - hLen - 1).
    //
    // 10. Let maskedDB = DB \xor dbMask.
    mgf1_xor(db, hash, h);

    // 11. Set the leftmost 8 * em_len - em_bits bits of the leftmost octet in
    //     maskedDB to zero.
    db[0] &= 0xFF >> (8 * em_len - em_bits);

    // 12. Let EM = maskedDB || H || 0xbc.
    em[em_len - 1] = 0xBC;

    Ok(em)
}

fn emsa_pss_encode_digest<D>(m_hash: &[u8], em_bits: usize, salt: &[u8]) -> Result<Vec<u8>>
where
    D: Digest + FixedOutputReset,
{
    // See [1], section 9.1.1
    let h_len = <D as Digest>::output_size();
    let s_len = salt.len();
    let em_len = (em_bits + 7) / 8;

    // 1. If the length of M is greater than the input limitation for the
    //     hash function (2^61 - 1 octets for SHA-1), output "message too
    //     long" and stop.
    //
    // 2.  Let mHash = Hash(M), an octet string of length hLen.
    if m_hash.len() != h_len {
        return Err(Error::InputNotHashed);
    }

    // 3. If em_len < h_len + s_len + 2, output "encoding error" and stop.
    if em_len < h_len + s_len + 2 {
        // TODO: Key size too small
        return Err(Error::Internal);
    }

    let mut em = vec![0; em_len];

    let (db, h) = em.split_at_mut(em_len - h_len - 1);
    let h = &mut h[..(em_len - 1) - db.len()];

    // 4. Generate a random octet string salt of length s_len; if s_len = 0,
    //     then salt is the empty string.
    //
    // 5.  Let
    //       M' = (0x)00 00 00 00 00 00 00 00 || m_hash || salt;
    //
    //     M' is an octet string of length 8 + h_len + s_len with eight
    //     initial zero octets.
    //
    // 6.  Let H = Hash(M'), an octet string of length h_len.
    let prefix = [0u8; 8];

    let mut hash = D::new();

    Digest::update(&mut hash, &prefix);
    Digest::update(&mut hash, m_hash);
    Digest::update(&mut hash, salt);

    let hashed = hash.finalize_reset();
    h.copy_from_slice(&hashed);

    // 7.  Generate an octet string PS consisting of em_len - s_len - h_len - 2
    //     zero octets. The length of PS may be 0.
    //
    // 8.  Let DB = PS || 0x01 || salt; DB is an octet string of length
    //     emLen - hLen - 1.
    db[em_len - s_len - h_len - 2] = 0x01;
    db[em_len - s_len - h_len - 1..].copy_from_slice(salt);

    // 9.  Let dbMask = MGF(H, emLen - hLen - 1).
    //
    // 10. Let maskedDB = DB \xor dbMask.
    mgf1_xor_digest(db, &mut hash, h);

    // 11. Set the leftmost 8 * em_len - em_bits bits of the leftmost octet in
    //     maskedDB to zero.
    db[0] &= 0xFF >> (8 * em_len - em_bits);

    // 12. Let EM = maskedDB || H || 0xbc.
    em[em_len - 1] = 0xBC;

    Ok(em)
}

fn emsa_pss_verify_pre<'a>(
    m_hash: &[u8],
    em: &'a mut [u8],
    em_bits: usize,
    s_len: Option<usize>,
    h_len: usize,
) -> Result<(&'a mut [u8], &'a mut [u8])> {
    // 1. If the length of M is greater than the input limitation for the
    //    hash function (2^61 - 1 octets for SHA-1), output "inconsistent"
    //    and stop.
    //
    // 2. Let mHash = Hash(M), an octet string of length hLen
    if m_hash.len() != h_len {
        return Err(Error::Verification);
    }

    // 3. If emLen < hLen + sLen + 2, output "inconsistent" and stop.
    let em_len = em.len(); //(em_bits + 7) / 8;
    if em_len < h_len + s_len.unwrap_or_default() + 2 {
        return Err(Error::Verification);
    }

    // 4. If the rightmost octet of EM does not have hexadecimal value
    //    0xbc, output "inconsistent" and stop.
    if em[em.len() - 1] != 0xBC {
        return Err(Error::Verification);
    }

    // 5. Let maskedDB be the leftmost emLen - hLen - 1 octets of EM, and
    //    let H be the next hLen octets.
    let (db, h) = em.split_at_mut(em_len - h_len - 1);
    let h = &mut h[..h_len];

    // 6. If the leftmost 8 * em_len - em_bits bits of the leftmost octet in
    //    maskedDB are not all equal to zero, output "inconsistent" and
    //    stop.
    if db[0] & (0xFF << /*uint*/(8 - (8 * em_len - em_bits))) != 0 {
        return Err(Error::Verification);
    }

    Ok((db, h))
}

fn emsa_pss_get_salt(
    db: &[u8],
    em_len: usize,
    s_len: Option<usize>,
    h_len: usize,
) -> Result<&[u8]> {
    let s_len = match s_len {
        None => (0..=em_len - (h_len + 2))
            .rev()
            .try_fold(None, |state, i| match (state, db[em_len - h_len - i - 2]) {
                (Some(i), _) => Ok(Some(i)),
                (_, 1) => Ok(Some(i)),
                (_, 0) => Ok(None),
                _ => Err(Error::Verification),
            })?
            .ok_or(Error::Verification)?,
        Some(s_len) => {
            // 10. If the emLen - hLen - sLen - 2 leftmost octets of DB are not zero
            //     or if the octet at position emLen - hLen - sLen - 1 (the leftmost
            //     position is "position 1") does not have hexadecimal value 0x01,
            //     output "inconsistent" and stop.
            let (zeroes, rest) = db.split_at(em_len - h_len - s_len - 2);
            if zeroes.iter().any(|e| *e != 0x00) || rest[0] != 0x01 {
                return Err(Error::Verification);
            }

            s_len
        }
    };

    // 11. Let salt be the last s_len octets of DB.
    let salt = &db[db.len() - s_len..];

    Ok(salt)
}

fn emsa_pss_verify(
    m_hash: &[u8],
    em: &mut [u8],
    em_bits: usize,
    s_len: Option<usize>,
    hash: &mut dyn DynDigest,
) -> Result<()> {
    let em_len = em.len(); //(em_bits + 7) / 8;
    let h_len = hash.output_size();

    let (db, h) = emsa_pss_verify_pre(m_hash, em, em_bits, s_len, h_len)?;

    // 7. Let dbMask = MGF(H, em_len - h_len - 1)
    //
    // 8. Let DB = maskedDB \xor dbMask
    mgf1_xor(db, hash, &*h);

    // 9.  Set the leftmost 8 * emLen - emBits bits of the leftmost octet in DB
    //     to zero.
    db[0] &= 0xFF >> /*uint*/(8 * em_len - em_bits);

    let salt = emsa_pss_get_salt(db, em_len, s_len, h_len)?;

    // 12. Let
    //          M' = (0x)00 00 00 00 00 00 00 00 || mHash || salt ;
    //     M' is an octet string of length 8 + hLen + sLen with eight
    //     initial zero octets.
    //
    // 13. Let H' = Hash(M'), an octet string of length hLen.
    let prefix = [0u8; 8];

    hash.update(&prefix[..]);
    hash.update(m_hash);
    hash.update(salt);
    let h0 = hash.finalize_reset();

    // 14. If H = H', output "consistent." Otherwise, output "inconsistent."
    if h0.ct_eq(h).into() {
        Ok(())
    } else {
        Err(Error::Verification)
    }
}

fn emsa_pss_verify_digest<D>(
    m_hash: &[u8],
    em: &mut [u8],
    em_bits: usize,
    s_len: Option<usize>,
) -> Result<()>
where
    D: Digest + FixedOutputReset,
{
    let em_len = em.len(); //(em_bits + 7) / 8;
    let h_len = <D as Digest>::output_size();

    let (db, h) = emsa_pss_verify_pre(m_hash, em, em_bits, s_len, h_len)?;

    let mut hash = D::new();

    // 7. Let dbMask = MGF(H, em_len - h_len - 1)
    //
    // 8. Let DB = maskedDB \xor dbMask
    mgf1_xor_digest::<D>(db, &mut hash, &*h);

    // 9.  Set the leftmost 8 * emLen - emBits bits of the leftmost octet in DB
    //     to zero.
    db[0] &= 0xFF >> /*uint*/(8 * em_len - em_bits);

    let salt = emsa_pss_get_salt(db, em_len, s_len, h_len)?;

    // 12. Let
    //          M' = (0x)00 00 00 00 00 00 00 00 || mHash || salt ;
    //     M' is an octet string of length 8 + hLen + sLen with eight
    //     initial zero octets.
    //
    // 13. Let H' = Hash(M'), an octet string of length hLen.
    let prefix = [0u8; 8];

    Digest::update(&mut hash, &prefix[..]);
    Digest::update(&mut hash, m_hash);
    Digest::update(&mut hash, salt);
    let h0 = hash.finalize_reset();

    // 14. If H = H', output "consistent." Otherwise, output "inconsistent."
    if h0.ct_eq(h).into() {
        Ok(())
    } else {
        Err(Error::Verification)
    }
}

/// Signing key for producing RSASSA-PSS signatures as described in
/// [RFC8017 § 8.1].
///
/// [RFC8017 § 8.1]: https://datatracker.ietf.org/doc/html/rfc8017#section-8.1
#[derive(Debug, Clone)]
pub struct SigningKey<D>
where
    D: Digest,
{
    inner: RsaPrivateKey,
    salt_len: Option<usize>,
    phantom: PhantomData<D>,
}

impl<D> SigningKey<D>
where
    D: Digest,
{
    /// Create a new RSASSA-PSS signing key.
    pub fn new(key: RsaPrivateKey) -> Self {
        Self {
            inner: key,
            salt_len: None,
            phantom: Default::default(),
        }
    }

    /// Create a new RSASSA-PSS signing key with a salt of the given length.
    pub fn new_with_salt_len(key: RsaPrivateKey, salt_len: usize) -> Self {
        Self {
            inner: key,
            salt_len: Some(salt_len),
            phantom: Default::default(),
        }
    }

    /// Generate a new random RSASSA-PSS signing key.
    pub fn random<R: CryptoRngCore + ?Sized>(rng: &mut R, bit_size: usize) -> Result<Self> {
        Ok(Self {
            inner: RsaPrivateKey::new(rng, bit_size)?,
            salt_len: None,
            phantom: Default::default(),
        })
    }

    /// Generate a new random RSASSA-PSS signing key with a salt of the given length.
    pub fn random_with_salt_len<R: CryptoRngCore + ?Sized>(
        rng: &mut R,
        bit_size: usize,
        salt_len: usize,
    ) -> Result<Self> {
        Ok(Self {
            inner: RsaPrivateKey::new(rng, bit_size)?,
            salt_len: Some(salt_len),
            phantom: Default::default(),
        })
    }
}

impl<D> From<RsaPrivateKey> for SigningKey<D>
where
    D: Digest,
{
    fn from(key: RsaPrivateKey) -> Self {
        Self::new(key)
    }
}

impl<D> From<SigningKey<D>> for RsaPrivateKey
where
    D: Digest,
{
    fn from(key: SigningKey<D>) -> Self {
        key.inner
    }
}

impl<D> EncodePrivateKey for SigningKey<D>
where
    D: Digest,
{
    fn to_pkcs8_der(&self) -> pkcs8::Result<SecretDocument> {
        self.inner.to_pkcs8_der()
    }
}

impl<D> Keypair for SigningKey<D>
where
    D: Digest,
{
    type VerifyingKey = VerifyingKey<D>;
    fn verifying_key(&self) -> Self::VerifyingKey {
        VerifyingKey {
            inner: self.inner.to_public_key(),
            phantom: Default::default(),
        }
    }
}

impl<D> RandomizedSigner<Signature> for SigningKey<D>
where
    D: Digest + FixedOutputReset,
{
    fn try_sign_with_rng<R: CryptoRngCore + ?Sized>(
        &self,
        rng: &mut R,
        msg: &[u8],
    ) -> signature::Result<Signature> {
        sign_digest::<_, _, D>(rng, false, &self.inner, &D::digest(msg), self.salt_len)
            .map(|v| v.into_boxed_slice().into())
            .map_err(|e| e.into())
    }
}

impl<D> RandomizedDigestSigner<D, Signature> for SigningKey<D>
where
    D: Digest + FixedOutputReset,
{
    fn try_sign_digest_with_rng<R: CryptoRngCore + ?Sized>(
        &self,
        rng: &mut R,
        digest: D,
    ) -> signature::Result<Signature> {
        sign_digest::<_, _, D>(rng, false, &self.inner, &digest.finalize(), self.salt_len)
            .map(|v| v.into_boxed_slice().into())
            .map_err(|e| e.into())
    }
}

impl<D> RandomizedPrehashSigner<Signature> for SigningKey<D>
where
    D: Digest + FixedOutputReset,
{
    fn sign_prehash_with_rng<R: CryptoRngCore + ?Sized>(
        &self,
        rng: &mut R,
        prehash: &[u8],
    ) -> signature::Result<Signature> {
        sign_digest::<_, _, D>(rng, false, &self.inner, prehash, self.salt_len)
            .map(|v| v.into_boxed_slice().into())
            .map_err(|e| e.into())
    }
}

impl<D> AsRef<RsaPrivateKey> for SigningKey<D>
where
    D: Digest,
{
    fn as_ref(&self) -> &RsaPrivateKey {
        &self.inner
    }
}

/// Signing key for producing "blinded" RSASSA-PSS signatures as described in
/// [draft-irtf-cfrg-rsa-blind-signatures](https://datatracker.ietf.org/doc/draft-irtf-cfrg-rsa-blind-signatures/).
#[derive(Debug, Clone)]
pub struct BlindedSigningKey<D>
where
    D: Digest,
{
    inner: RsaPrivateKey,
    salt_len: Option<usize>,
    phantom: PhantomData<D>,
}

impl<D> BlindedSigningKey<D>
where
    D: Digest,
{
    /// Create a new RSASSA-PSS signing key which produces "blinded"
    /// signatures.
    pub fn new(key: RsaPrivateKey) -> Self {
        Self {
            inner: key,
            salt_len: None,
            phantom: Default::default(),
        }
    }

    /// Create a new RSASSA-PSS signing key which produces "blinded"
    /// signatures with a salt of the given length.
    pub fn new_with_salt_len(key: RsaPrivateKey, salt_len: usize) -> Self {
        Self {
            inner: key,
            salt_len: Some(salt_len),
            phantom: Default::default(),
        }
    }
}

impl<D> From<RsaPrivateKey> for BlindedSigningKey<D>
where
    D: Digest,
{
    fn from(key: RsaPrivateKey) -> Self {
        Self::new(key)
    }
}

impl<D> From<BlindedSigningKey<D>> for RsaPrivateKey
where
    D: Digest,
{
    fn from(key: BlindedSigningKey<D>) -> Self {
        key.inner
    }
}

impl<D> EncodePrivateKey for BlindedSigningKey<D>
where
    D: Digest,
{
    fn to_pkcs8_der(&self) -> pkcs8::Result<SecretDocument> {
        self.inner.to_pkcs8_der()
    }
}

impl<D> Keypair for BlindedSigningKey<D>
where
    D: Digest,
{
    type VerifyingKey = VerifyingKey<D>;
    fn verifying_key(&self) -> Self::VerifyingKey {
        VerifyingKey {
            inner: self.inner.to_public_key(),
            phantom: Default::default(),
        }
    }
}

impl<D> RandomizedSigner<Signature> for BlindedSigningKey<D>
where
    D: Digest + FixedOutputReset,
{
    fn try_sign_with_rng<R: CryptoRngCore + ?Sized>(
        &self,
        rng: &mut R,
        msg: &[u8],
    ) -> signature::Result<Signature> {
        sign_digest::<_, _, D>(rng, true, &self.inner, &D::digest(msg), self.salt_len)
            .map(|v| v.into_boxed_slice().into())
            .map_err(|e| e.into())
    }
}

impl<D> RandomizedDigestSigner<D, Signature> for BlindedSigningKey<D>
where
    D: Digest + FixedOutputReset,
{
    fn try_sign_digest_with_rng<R: CryptoRngCore + ?Sized>(
        &self,
        rng: &mut R,
        digest: D,
    ) -> signature::Result<Signature> {
        sign_digest::<_, _, D>(rng, true, &self.inner, &digest.finalize(), self.salt_len)
            .map(|v| v.into_boxed_slice().into())
            .map_err(|e| e.into())
    }
}

impl<D> RandomizedPrehashSigner<Signature> for BlindedSigningKey<D>
where
    D: Digest + FixedOutputReset,
{
    fn sign_prehash_with_rng<R: CryptoRngCore + ?Sized>(
        &self,
        rng: &mut R,
        prehash: &[u8],
    ) -> signature::Result<Signature> {
        sign_digest::<_, _, D>(rng, true, &self.inner, prehash, self.salt_len)
            .map(|v| v.into_boxed_slice().into())
            .map_err(|e| e.into())
    }
}

impl<D> AsRef<RsaPrivateKey> for BlindedSigningKey<D>
where
    D: Digest,
{
    fn as_ref(&self) -> &RsaPrivateKey {
        &self.inner
    }
}

/// Verifying key for checking the validity of RSASSA-PSS signatures as
/// described in [RFC8017 § 8.1].
///
/// [RFC8017 § 8.1]: https://datatracker.ietf.org/doc/html/rfc8017#section-8.1
#[derive(Debug)]
pub struct VerifyingKey<D>
where
    D: Digest,
{
    inner: RsaPublicKey,
    phantom: PhantomData<D>,
}

/* Implemented manually so we don't have to bind D with Clone */
impl<D> Clone for VerifyingKey<D>
where
    D: Digest,
{
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
            phantom: Default::default(),
        }
    }
}

impl<D> VerifyingKey<D>
where
    D: Digest,
{
    /// Create a new RSASSA-PSS verifying key.
    pub fn new(key: RsaPublicKey) -> Self {
        Self {
            inner: key,
            phantom: Default::default(),
        }
    }
}

impl<D> From<RsaPublicKey> for VerifyingKey<D>
where
    D: Digest,
{
    fn from(key: RsaPublicKey) -> Self {
        Self::new(key)
    }
}

impl<D> From<VerifyingKey<D>> for RsaPublicKey
where
    D: Digest,
{
    fn from(key: VerifyingKey<D>) -> Self {
        key.inner
    }
}

impl<D> Verifier<Signature> for VerifyingKey<D>
where
    D: Digest + FixedOutputReset,
{
    fn verify(&self, msg: &[u8], signature: &Signature) -> signature::Result<()> {
        verify_digest::<_, D>(&self.inner, &D::digest(msg), signature.as_ref())
            .map_err(|e| e.into())
    }
}

impl<D> DigestVerifier<D, Signature> for VerifyingKey<D>
where
    D: Digest + FixedOutputReset,
{
    fn verify_digest(&self, digest: D, signature: &Signature) -> signature::Result<()> {
        verify_digest::<_, D>(&self.inner, &digest.finalize(), signature.as_ref())
            .map_err(|e| e.into())
    }
}

impl<D> PrehashVerifier<Signature> for VerifyingKey<D>
where
    D: Digest + FixedOutputReset,
{
    fn verify_prehash(&self, prehash: &[u8], signature: &Signature) -> signature::Result<()> {
        verify_digest::<_, D>(&self.inner, prehash, signature.as_ref()).map_err(|e| e.into())
    }
}

impl<D> AsRef<RsaPublicKey> for VerifyingKey<D>
where
    D: Digest,
{
    fn as_ref(&self) -> &RsaPublicKey {
        &self.inner
    }
}

impl<D> EncodePublicKey for VerifyingKey<D>
where
    D: Digest,
{
    fn to_public_key_der(&self) -> pkcs8::spki::Result<Document> {
        self.inner.to_public_key_der()
    }
}

#[cfg(test)]
mod test {
    use std::println;
    use crate::pss::{BlindedSigningKey, sign, Signature, SigningKey, VerifyingKey};
    use crate::{PaddingScheme, PublicKey, RsaPrivateKey, RsaPublicKey};

    use hex_literal::hex;
    use num_bigint::BigUint;
    use num_traits::{FromPrimitive, Num};
    use pkcs8::EncodePrivateKey;
    use rand_chacha::{rand_core::SeedableRng, ChaCha8Rng};
    use sha1::{Digest, Sha1};
    use signature::hazmat::{PrehashVerifier, RandomizedPrehashSigner};
    use signature::{DigestVerifier, Keypair, RandomizedDigestSigner, RandomizedSigner, SignatureEncoding, Verifier};
    use openssl::pkey::PKey;
    use openssl::hash::MessageDigest;

    fn get_private_key() -> RsaPrivateKey {
        // In order to generate new test vectors you'll need the PEM form of this key:
        // -----BEGIN RSA PRIVATE KEY-----
        // MIIBOgIBAAJBALKZD0nEffqM1ACuak0bijtqE2QrI/KLADv7l3kK3ppMyCuLKoF0
        // fd7Ai2KW5ToIwzFofvJcS/STa6HA5gQenRUCAwEAAQJBAIq9amn00aS0h/CrjXqu
        // /ThglAXJmZhOMPVn4eiu7/ROixi9sex436MaVeMqSNf7Ex9a8fRNfWss7Sqd9eWu
        // RTUCIQDasvGASLqmjeffBNLTXV2A5g4t+kLVCpsEIZAycV5GswIhANEPLmax0ME/
        // EO+ZJ79TJKN5yiGBRsv5yvx5UiHxajEXAiAhAol5N4EUyq6I9w1rYdhPMGpLfk7A
        // IU2snfRJ6Nq2CQIgFrPsWRCkV+gOYcajD17rEqmuLrdIRexpg8N1DOSXoJ8CIGlS
        // tAboUGBxTDq3ZroNism3DaMIbKPyYrAqhKov1h5V
        // -----END RSA PRIVATE KEY-----

        RsaPrivateKey::from_components(
            BigUint::from_str_radix("9353930466774385905609975137998169297361893554149986716853295022578535724979677252958524466350471210367835187480748268864277464700638583474144061408845077", 10).unwrap(),
            BigUint::from_u64(65537).unwrap(),
            BigUint::from_str_radix("7266398431328116344057699379749222532279343923819063639497049039389899328538543087657733766554155839834519529439851673014800261285757759040931985506583861", 10).unwrap(),
            vec![
                BigUint::from_str_radix("98920366548084643601728869055592650835572950932266967461790948584315647051443",10).unwrap(),
                BigUint::from_str_radix("94560208308847015747498523884063394671606671904944666360068158221458669711639", 10).unwrap()
            ],
        ).unwrap()
    }

    #[test]
    fn test_verify_pss_openssl() {
        let d = hex!("542fd4042926629451ee9a4dace812428b6494acbf45370ddd2308c01e9ab9bf3974b561d5064f6f315f1a39632024bc18f2738c3acb11a1c1d25919477b0acc4f3e8b865aa50a9c3e781535079a06a668aa262ed675bb8ff979b93b5c877044528a0a89aa0a13855b37d96d1c213f237c2739a26aeca46427c517ecf0bc778becda2afb0be236988ed5d162c87ecca8db123af41129f8dfb3893f66293c64dd09d7313190ae66af5a2bef053ed25594a97bda6aa2c7eff560c815b9fe28ce2b68e89988a88322c34ef0e7e4c0822b2018545379900553d18c71de88bed451ef814c739296586d238bef428945ecb9f1eda9c098ba2345daf59229659b1588f2374438e978f94cf03ece881ded34790416d0f746b0701f7096aa74f381a21725dba3702b32670a5db7693763e95e751ae0ef5cd875ac38a4427dd716dd1d61d6c0e234ff64f80dbf0f1c2632883ac74b9e9387ad58e5ca928b7880d9844b513b448447c31b94d04160cfa83b0381b4e59b23deafd1cca01639e405bc494fa63758246eab4d25f94a6c2dfed72be6127217d7f806b05b573070850307a8c594233851a7efdb55e27f1624f2a9ca2a0c3e803024b1cbce919e7ae7e0b730d357a6ca62cd15978940f7998524404cb5837ccc93bca22caeb5156aa36abd92c83e047addef10d2e8f78e8c94a50fc305f9fe35a7f45f76271bd794b2f111db2eae41");
        let n = hex!("c41a50ed2155a5740b45df8e3815774d6b8d193e5ad80c9efaaf6d6d0253f350c85becf39eb7056d75841f6a064acf8381383eceb218e16859ef72be7273321a2b4855b87bc6f14c734e2a9c90850c34a8a0a4279ac9be3186b086db5b302fb68176b4c1fee337456c42f972c7993f618fdedc0bf1658c2d59cf2c0c6ac31a61ac1260e0fd4a761ca3707e27611c14b4c6b6abe698c11009ddf5d1511ae47ea271079b6892d229a27d0822e0c7aa12a4cf7f7c28fe23d201eae2adb7f403c9c5a1762c2d8cc96898ce41fe529ab0ef8184e50063e6fc62e0a808e8602254c142c9e7f7e94e6ef2c767ac0e99810d09a44bfde8db46298bc0e25b4a333b4ef86cd7ce658ff661ab0d1789b603b8770a6b433851a91c8ff07a7a8a0767702f6887098ea34bf4a8309eaab9baadd16d45cdd9b1899b6a303a2dce23745cec9fc2ecd9735a66c77fdea1bfd4cdb2be7bfb407a4fd5d3405c3cb33b5316e16559f0c4bf0bc7d1a3ada78917217b289c4d75eb60e0396f03035fd8d553727c790189cfd8dabcee8a4ae6607925b9a27ff7ad7ede26b98f8acd2532cf3175693f3eede9989a0aeedbdb3ff14fec823017531aead4cd22733ab30dbce76cebcdac64424128d6eeff3cdc1825d7cdb7113e74db126e6d931544467c6979aa8d50ac803f36084ed7077f34acfcf3f77bb13d5ebb723fc5d3f45212d2dd6ef20ea757fb4c95");
        let p = hex!("fdec3a1aee520780ca4058402d0422b5cd5950b715728f532499dd4bbcb68e5d44650818b43656782237316c4b0e2faa2b15c245fb82d10cf4f5b420f1f293ba75b2c8d8cef6ad899c34ce9de482cb248cc5ab802fd93094a63577590d812d5dd781846ef7d4f5d9018199c293966371c2349b0f847c818ec99caad800116e02085d35a39a913bc735327705161761ae30a4ec775f127fbb5165418c0fe08e54ae0aff8b2dab2b82d3b4b9c807de5fae116096075cf6d5b77450d743d743e7dcc56e7cafdcc555f228e57b363488e171d099876993e93e37a94983ccc12dba894c58ca84ac154c1343922c6a99008fabd0fa7010d3cc34f69884fec902984771");
        let q = hex!("c5b50031ba31ab7c8b76453ce771f048b84fb89a3e4d44c222c3d8c823c683988b0dbf354d8b8cbf65f3db53e1365d3c5e043f0155b41d1ebeca6e20b2d6778600b5c98ffdba33961dae73b018307ef2bce9d217bbdf32964080f8db6f0cf7ef27ac825fcaf98d5143690a5d7e138f4875280ed6de581e66ed17f83371c268a073e4594814bcc88a33cbb4ec8819cc722ea15490312b85fed06e39274c4f73ac91c7f4d1b899729691cce616fb1a5feee1972456addcb51ac830e947fcc1b823468f0eefbaf195ac3b34f0baf96afc6fa77ee2e176081d6d91ce8c93c3d0f3547e48d059c9da447ba05ee3984703bebfd6d704b7f327ffaea7d0f63d0d3c6d65");
        let e = base64::decode("AQAB").unwrap();
        let priv_key = RsaPrivateKey::from_components(
            BigUint::from_bytes_be(&n),
            BigUint::from_bytes_be(&e),
            BigUint::from_bytes_be(&d),
            [BigUint::from_bytes_be(&p), BigUint::from_bytes_be(&q)].to_vec(),
        ).unwrap();
        let data =  "test\n".as_bytes();
        let private_key_der = priv_key.to_pkcs8_der().unwrap();
        let pkey = PKey::private_key_from_der(private_key_der.as_bytes()).unwrap();
        let mut signer = openssl::sign::Signer::new(MessageDigest::sha256(), &pkey).unwrap();
        signer.set_rsa_padding(openssl::rsa::Padding::PKCS1_PSS).unwrap();
        signer
            .set_rsa_pss_saltlen(openssl::sign::RsaPssSaltlen::custom(32)).unwrap();
        signer.update(data).unwrap();
        let signature = signer.sign_to_vec().unwrap();
        let mut verifier = openssl::sign::Verifier::new(MessageDigest::sha256(), &pkey).unwrap();
        verifier.set_rsa_padding(openssl::rsa::Padding::PKCS1_PSS).unwrap();
        verifier.set_rsa_pss_saltlen(openssl::sign::RsaPssSaltlen::custom(32)).unwrap();
        verifier.update(data).unwrap();
        let result = verifier.verify(&signature);
        match result {
            Ok(true) => println!("openssl verify succeed"),
            _ => {
                println!("openssl expected verifying error");
            }
        }

        let pub_key: RsaPublicKey = priv_key.into();
        // let verifying_key = VerifyingKey::new(pub_key);
        let verifying_key: VerifyingKey<sha2::Sha256> = VerifyingKey::new(pub_key);
        let result = verifying_key.verify(
            data,
            &Signature::try_from(signature.as_slice()).unwrap(),
        );
        match result {
            Ok(()) => println!("verify succeed"),
            _ => {
                println!("expected verifying error");
            }
        }
    }

    #[test]
    fn test_sign_pss_openssl() {
        let d = hex!("542fd4042926629451ee9a4dace812428b6494acbf45370ddd2308c01e9ab9bf3974b561d5064f6f315f1a39632024bc18f2738c3acb11a1c1d25919477b0acc4f3e8b865aa50a9c3e781535079a06a668aa262ed675bb8ff979b93b5c877044528a0a89aa0a13855b37d96d1c213f237c2739a26aeca46427c517ecf0bc778becda2afb0be236988ed5d162c87ecca8db123af41129f8dfb3893f66293c64dd09d7313190ae66af5a2bef053ed25594a97bda6aa2c7eff560c815b9fe28ce2b68e89988a88322c34ef0e7e4c0822b2018545379900553d18c71de88bed451ef814c739296586d238bef428945ecb9f1eda9c098ba2345daf59229659b1588f2374438e978f94cf03ece881ded34790416d0f746b0701f7096aa74f381a21725dba3702b32670a5db7693763e95e751ae0ef5cd875ac38a4427dd716dd1d61d6c0e234ff64f80dbf0f1c2632883ac74b9e9387ad58e5ca928b7880d9844b513b448447c31b94d04160cfa83b0381b4e59b23deafd1cca01639e405bc494fa63758246eab4d25f94a6c2dfed72be6127217d7f806b05b573070850307a8c594233851a7efdb55e27f1624f2a9ca2a0c3e803024b1cbce919e7ae7e0b730d357a6ca62cd15978940f7998524404cb5837ccc93bca22caeb5156aa36abd92c83e047addef10d2e8f78e8c94a50fc305f9fe35a7f45f76271bd794b2f111db2eae41");
        let n = hex!("c41a50ed2155a5740b45df8e3815774d6b8d193e5ad80c9efaaf6d6d0253f350c85becf39eb7056d75841f6a064acf8381383eceb218e16859ef72be7273321a2b4855b87bc6f14c734e2a9c90850c34a8a0a4279ac9be3186b086db5b302fb68176b4c1fee337456c42f972c7993f618fdedc0bf1658c2d59cf2c0c6ac31a61ac1260e0fd4a761ca3707e27611c14b4c6b6abe698c11009ddf5d1511ae47ea271079b6892d229a27d0822e0c7aa12a4cf7f7c28fe23d201eae2adb7f403c9c5a1762c2d8cc96898ce41fe529ab0ef8184e50063e6fc62e0a808e8602254c142c9e7f7e94e6ef2c767ac0e99810d09a44bfde8db46298bc0e25b4a333b4ef86cd7ce658ff661ab0d1789b603b8770a6b433851a91c8ff07a7a8a0767702f6887098ea34bf4a8309eaab9baadd16d45cdd9b1899b6a303a2dce23745cec9fc2ecd9735a66c77fdea1bfd4cdb2be7bfb407a4fd5d3405c3cb33b5316e16559f0c4bf0bc7d1a3ada78917217b289c4d75eb60e0396f03035fd8d553727c790189cfd8dabcee8a4ae6607925b9a27ff7ad7ede26b98f8acd2532cf3175693f3eede9989a0aeedbdb3ff14fec823017531aead4cd22733ab30dbce76cebcdac64424128d6eeff3cdc1825d7cdb7113e74db126e6d931544467c6979aa8d50ac803f36084ed7077f34acfcf3f77bb13d5ebb723fc5d3f45212d2dd6ef20ea757fb4c95");
        let p = hex!("fdec3a1aee520780ca4058402d0422b5cd5950b715728f532499dd4bbcb68e5d44650818b43656782237316c4b0e2faa2b15c245fb82d10cf4f5b420f1f293ba75b2c8d8cef6ad899c34ce9de482cb248cc5ab802fd93094a63577590d812d5dd781846ef7d4f5d9018199c293966371c2349b0f847c818ec99caad800116e02085d35a39a913bc735327705161761ae30a4ec775f127fbb5165418c0fe08e54ae0aff8b2dab2b82d3b4b9c807de5fae116096075cf6d5b77450d743d743e7dcc56e7cafdcc555f228e57b363488e171d099876993e93e37a94983ccc12dba894c58ca84ac154c1343922c6a99008fabd0fa7010d3cc34f69884fec902984771");
        let q = hex!("c5b50031ba31ab7c8b76453ce771f048b84fb89a3e4d44c222c3d8c823c683988b0dbf354d8b8cbf65f3db53e1365d3c5e043f0155b41d1ebeca6e20b2d6778600b5c98ffdba33961dae73b018307ef2bce9d217bbdf32964080f8db6f0cf7ef27ac825fcaf98d5143690a5d7e138f4875280ed6de581e66ed17f83371c268a073e4594814bcc88a33cbb4ec8819cc722ea15490312b85fed06e39274c4f73ac91c7f4d1b899729691cce616fb1a5feee1972456addcb51ac830e947fcc1b823468f0eefbaf195ac3b34f0baf96afc6fa77ee2e176081d6d91ce8c93c3d0f3547e48d059c9da447ba05ee3984703bebfd6d704b7f327ffaea7d0f63d0d3c6d65");
        let e = base64::decode("AQAB").unwrap();
        let priv_key = RsaPrivateKey::from_components(
            BigUint::from_bytes_be(&n),
            BigUint::from_bytes_be(&e),
            BigUint::from_bytes_be(&d),
            [BigUint::from_bytes_be(&p), BigUint::from_bytes_be(&q)].to_vec(),
        ).unwrap();
        let data =  "test\n".as_bytes();
        let private_key_der = priv_key.to_pkcs8_der().unwrap();
        let pkey = PKey::private_key_from_der(private_key_der.as_bytes()).unwrap();
        let signing_key = SigningKey::<sha2::Sha256>::new_with_salt_len(priv_key.clone(), 32);
        let mut rng = ChaCha8Rng::from_seed([42; 32]);
        let mut digest = sha2::Sha256::new();
        digest.update(data);
        let signature = signing_key.sign_digest_with_rng(&mut rng, digest);

        // let mut signer = openssl::sign::Signer::new(MessageDigest::sha256(), &pkey).unwrap();
        // signer.set_rsa_padding(openssl::rsa::Padding::PKCS1_PSS).unwrap();
        // signer
        //     .set_rsa_pss_saltlen(openssl::sign::RsaPssSaltlen::custom(32)).unwrap();
        // signer.update(data).unwrap();
        // let signature = signer.sign_to_vec().unwrap();
        let mut verifier = openssl::sign::Verifier::new(MessageDigest::sha256(), &pkey).unwrap();
        verifier.set_rsa_padding(openssl::rsa::Padding::PKCS1_PSS).unwrap();
        verifier.set_rsa_pss_saltlen(openssl::sign::RsaPssSaltlen::custom(32)).unwrap();
        verifier.update(data).unwrap();
        let result = verifier.verify(&signature.to_vec());
        match result {
            Ok(true) => println!("openssl verify succeed"),
            _ => {
                println!("openssl expected verifying error");
            }
        }

        let pub_key: RsaPublicKey = priv_key.into();
        // let verifying_key = VerifyingKey::new(pub_key);
        let verifying_key: VerifyingKey<sha2::Sha256> = VerifyingKey::new(pub_key);
        let result = verifying_key.verify(
            data,
            &Signature::try_from(&*signature.to_bytes()).unwrap(),
        );
        match result {
            Ok(()) => println!("verify succeed"),
            _ => {
                println!("expected verifying error");
            }
        }
    }

    #[test]
    fn test_verify_pss_signer() {
        let priv_key = get_private_key();

        let tests = [
            (
                "test\n",
                hex!(
                    "6f86f26b14372b2279f79fb6807c49889835c204f71e38249b4c5601462da8ae"
                    "30f26ffdd9c13f1c75eee172bebe7b7c89f2f1526c722833b9737d6c172a962f"
                ),
                true,
            ),
            (
                "test\n",
                hex!(
                    "6f86f26b14372b2279f79fb6807c49889835c204f71e38249b4c5601462da8ae"
                    "30f26ffdd9c13f1c75eee172bebe7b7c89f2f1526c722833b9737d6c172a962e"
                ),
                false,
            ),
        ];
        let pub_key: RsaPublicKey = priv_key.into();
        let verifying_key: VerifyingKey<Sha1> = VerifyingKey::new(pub_key);

        for (text, sig, expected) in &tests {
            let result = verifying_key.verify(
                text.as_bytes(),
                &Signature::try_from(sig.as_slice()).unwrap(),
            );
            match expected {
                true => result.expect("failed to verify"),
                false => {
                    result.expect_err("expected verifying error");
                }
            }
        }
    }

    #[test]
    fn test_verify_pss_digest_signer() {
        let priv_key = get_private_key();

        let tests = [
            (
                "test\n",
                hex!(
                    "6f86f26b14372b2279f79fb6807c49889835c204f71e38249b4c5601462da8ae"
                    "30f26ffdd9c13f1c75eee172bebe7b7c89f2f1526c722833b9737d6c172a962f"
                ),
                true,
            ),
            (
                "test\n",
                hex!(
                    "6f86f26b14372b2279f79fb6807c49889835c204f71e38249b4c5601462da8ae"
                    "30f26ffdd9c13f1c75eee172bebe7b7c89f2f1526c722833b9737d6c172a962e"
                ),
                false,
            ),
        ];
        let pub_key: RsaPublicKey = priv_key.into();
        let verifying_key = VerifyingKey::new(pub_key);

        for (text, sig, expected) in &tests {
            let mut digest = Sha1::new();
            digest.update(text.as_bytes());
            let result =
                verifying_key.verify_digest(digest, &Signature::try_from(sig.as_slice()).unwrap());
            match expected {
                true => result.expect("failed to verify"),
                false => {
                    result.expect_err("expected verifying error");
                }
            }
        }
    }

    #[test]
    fn test_sign_and_verify_roundtrip() {
        let priv_key = get_private_key();

        let tests = ["test\n"];
        let rng = ChaCha8Rng::from_seed([42; 32]);

        for test in &tests {
            let digest = Sha1::digest(test.as_bytes()).to_vec();
            let sig = priv_key
                .sign_with_rng(&mut rng.clone(), PaddingScheme::new_pss::<Sha1>(), &digest)
                .expect("failed to sign");

            priv_key
                .verify(PaddingScheme::new_pss::<Sha1>(), &digest, &sig)
                .expect("failed to verify");
        }
    }

    #[test]
    fn test_sign_blinded_and_verify_roundtrip() {
        let priv_key = get_private_key();

        let tests = ["test\n"];
        let rng = ChaCha8Rng::from_seed([42; 32]);

        for test in &tests {
            let digest = Sha1::digest(test.as_bytes()).to_vec();
            let sig = priv_key
                .sign_blinded(&mut rng.clone(), PaddingScheme::new_pss::<Sha1>(), &digest)
                .expect("failed to sign");

            priv_key
                .verify(PaddingScheme::new_pss::<Sha1>(), &digest, &sig)
                .expect("failed to verify");
        }
    }

    #[test]
    fn test_sign_and_verify_roundtrip_signer() {
        let priv_key = get_private_key();

        let tests = ["test\n"];
        let mut rng = ChaCha8Rng::from_seed([42; 32]);
        let signing_key = SigningKey::<Sha1>::new(priv_key);
        let verifying_key = signing_key.verifying_key();

        for test in &tests {
            let sig = signing_key.sign_with_rng(&mut rng, test.as_bytes());
            verifying_key
                .verify(test.as_bytes(), &sig)
                .expect("failed to verify");
        }
    }

    #[test]
    fn test_sign_and_verify_roundtrip_blinded_signer() {
        let priv_key = get_private_key();

        let tests = ["test\n"];
        let mut rng = ChaCha8Rng::from_seed([42; 32]);
        let signing_key = BlindedSigningKey::<Sha1>::new(priv_key);
        let verifying_key = signing_key.verifying_key();

        for test in &tests {
            let sig = signing_key.sign_with_rng(&mut rng, test.as_bytes());
            verifying_key
                .verify(test.as_bytes(), &sig)
                .expect("failed to verify");
        }
    }

    #[test]
    fn test_sign_and_verify_roundtrip_digest_signer() {
        let priv_key = get_private_key();

        let tests = ["test\n"];
        let mut rng = ChaCha8Rng::from_seed([42; 32]);
        let signing_key = SigningKey::new(priv_key);
        let verifying_key = signing_key.verifying_key();

        for test in &tests {
            let mut digest = Sha1::new();
            digest.update(test.as_bytes());
            let sig = signing_key.sign_digest_with_rng(&mut rng, digest);

            let mut digest = Sha1::new();
            digest.update(test.as_bytes());
            verifying_key
                .verify_digest(digest, &sig)
                .expect("failed to verify");
        }
    }

    #[test]
    fn test_sign_and_verify_roundtrip_blinded_digest_signer() {
        let priv_key = get_private_key();

        let tests = ["test\n"];
        let mut rng = ChaCha8Rng::from_seed([42; 32]);
        let signing_key = BlindedSigningKey::<Sha1>::new(priv_key);
        let verifying_key = signing_key.verifying_key();

        for test in &tests {
            let mut digest = Sha1::new();
            digest.update(test.as_bytes());
            let sig = signing_key.sign_digest_with_rng(&mut rng, digest);

            let mut digest = Sha1::new();
            digest.update(test.as_bytes());
            verifying_key
                .verify_digest(digest, &sig)
                .expect("failed to verify");
        }
    }

    #[test]
    fn test_verify_pss_hazmat() {
        let priv_key = get_private_key();

        let tests = [
            (
                Sha1::digest("test\n"),
                hex!(
                    "6f86f26b14372b2279f79fb6807c49889835c204f71e38249b4c5601462da8ae"
                    "30f26ffdd9c13f1c75eee172bebe7b7c89f2f1526c722833b9737d6c172a962f"
                ),
                true,
            ),
            (
                Sha1::digest("test\n"),
                hex!(
                    "6f86f26b14372b2279f79fb6807c49889835c204f71e38249b4c5601462da8ae"
                    "30f26ffdd9c13f1c75eee172bebe7b7c89f2f1526c722833b9737d6c172a962e"
                ),
                false,
            ),
        ];
        let pub_key: RsaPublicKey = priv_key.into();
        let verifying_key = VerifyingKey::<Sha1>::new(pub_key);

        for (text, sig, expected) in &tests {
            let result = verifying_key
                .verify_prehash(text.as_ref(), &Signature::try_from(sig.as_slice()).unwrap());
            match expected {
                true => result.expect("failed to verify"),
                false => {
                    result.expect_err("expected verifying error");
                }
            }
        }
    }

    #[test]
    fn test_sign_and_verify_pss_hazmat() {
        let priv_key = get_private_key();

        let tests = [Sha1::digest("test\n")];
        let mut rng = ChaCha8Rng::from_seed([42; 32]);
        let signing_key = SigningKey::<Sha1>::new(priv_key);
        let verifying_key = signing_key.verifying_key();

        for test in &tests {
            let sig = signing_key
                .sign_prehash_with_rng(&mut rng, &test)
                .expect("failed to sign");
            verifying_key
                .verify_prehash(&test, &sig)
                .expect("failed to verify");
        }
    }

    #[test]
    fn test_sign_and_verify_pss_blinded_hazmat() {
        let priv_key = get_private_key();

        let tests = [Sha1::digest("test\n")];
        let mut rng = ChaCha8Rng::from_seed([42; 32]);
        let signing_key = BlindedSigningKey::<Sha1>::new(priv_key);
        let verifying_key = signing_key.verifying_key();

        for test in &tests {
            let sig = signing_key
                .sign_prehash_with_rng(&mut rng, &test)
                .expect("failed to sign");
            verifying_key
                .verify_prehash(&test, &sig)
                .expect("failed to verify");
        }
    }
}
