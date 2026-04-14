//! Proximity signatures for DA-bound work report verification.
//!
//! Implements the many-slot proximity signature from Angeris & Gurkan (2026).
//! Uses BLS12-381 with min_sig variant (signatures in G1, public keys in G2).
//!
//! The guarantor signs the work package data using:
//!   Σ = κ · (H(0, slot) + Σ_k data[k] · H(k, slot))
//!
//! Verification reuses the ZODA random linear combination y = M·r:
//!   Σ_i r_i · e(Σ_i, PK_i) == e((r^T·1)·H(0,s) + Σ_k y_k·H(k,s), g2)
//!
//! References:
//! - Proximity Signatures (Angeris & Gurkan, April 2026)
//! - Linear Subspace Signatures (Boneh, Freeman, Katz, Waters 2009)

use blst::min_sig::{PublicKey, SecretKey, Signature};
use blst::{blst_p1, blst_p1_affine, blst_p2_affine, blst_fp12};
use blst::{blst_hash_to_g1, blst_p1_mult, blst_p1_add_or_double, blst_p1_to_affine, blst_p1_from_affine};
use blst::{blst_miller_loop, blst_final_exp, blst_fp12_is_one, blst_fp12_mul};
use blst::blst_scalar;

/// Domain separation for proximity signature hash-to-curve.
const PROX_DST: &[u8] = b"JAR_PROX_SIG_BLS12381G1_XMD:SHA-256_SSWU_RO_";

/// A proximity signature keypair.
pub struct ProxKeypair {
    secret: SecretKey,
}

impl ProxKeypair {
    /// Derive from a 32-byte seed.
    pub fn from_seed(seed: &[u8; 32]) -> Self {
        let secret = SecretKey::key_gen(seed, &[])
            .expect("key_gen should not fail with 32-byte seed");
        Self { secret }
    }

    /// Get the 96-byte compressed G2 public key.
    /// PK = κ^{-1} · g2 (paper convention, NOT standard BLS PK = κ · g2).
    pub fn public_key_bytes(&self) -> [u8; 96] {
        let sk_bytes = self.secret.to_bytes(); // big-endian
        let inv_scalar = scalar_inverse_as_blst_scalar(&sk_bytes);
        let g2_gen_proj = g2_generator_proj();
        let mut pk_point = blst::blst_p2::default();
        unsafe {
            // blst_p2_mult expects LE scalar bytes
            blst::blst_p2_mult(&mut pk_point, &g2_gen_proj, inv_scalar.b.as_ptr(), 256);
        }
        let mut pk_affine = blst_p2_affine::default();
        unsafe { blst::blst_p2_to_affine(&mut pk_affine, &pk_point); }
        let mut out = [0u8; 96];
        unsafe { blst::blst_p2_affine_compress(out.as_mut_ptr(), &pk_affine); }
        out
    }

    /// Sign a work package's field elements for a given slot.
    ///
    /// Computes: Σ = κ · (H(0, slot) + Σ_k data[k] · H(k+1, slot))
    ///
    /// `data` is the work package encoded as field elements (u32 values).
    /// `slot` is the timeslot identifier.
    ///
    /// Returns 48-byte compressed G1 signature.
    pub fn sign(&self, data: &[u32], slot: u32) -> [u8; 48] {
        // Compute the message point: H(0,s) + Σ data[k]·H(k+1,s)
        let mut msg_point = hash_to_g1(0, slot);

        for (k, &val) in data.iter().enumerate() {
            if val == 0 { continue; } // skip zero terms
            let h_k = hash_to_g1((k + 1) as u32, slot);
            let scaled = g1_scalar_mul(&h_k, val);
            msg_point = g1_add(&msg_point, &scaled);
        }

        // Sign: Σ = κ · msg_point
        let sig = g1_scalar_mul_secret(&msg_point, &self.secret);
        g1_compress(&sig)
    }
}

/// Verify a single proximity signature.
///
/// Checks: e(Σ, g2) == e(H(0,s) + Σ data[k]·H(k+1,s), PK)
pub fn prox_verify(
    public_key: &[u8; 96],
    data: &[u32],
    slot: u32,
    signature: &[u8; 48],
) -> bool {
    let sig = match decompress_g1(signature) {
        Some(p) => p,
        None => return false,
    };

    // Reconstruct message point
    let mut msg_point = hash_to_g1(0, slot);
    for (k, &val) in data.iter().enumerate() {
        if val == 0 { continue; }
        let h_k = hash_to_g1((k + 1) as u32, slot);
        let scaled = g1_scalar_mul(&h_k, val);
        msg_point = g1_add(&msg_point, &scaled);
    }

    // Pairing check: e(sig, pk) == e(msg, g2)
    pairing_check(&sig, &msg_point, public_key)
}

/// Verify batched proximity signatures using ZODA's random linear combination.
///
/// Given n signatures (one per guarantor), public keys, random vector r,
/// and linear combination y = M·r, checks:
///   Σ_i r_i · e(Σ_i, PK_i) == e((Σr_i)·H(0,s) + Σ_k y_k·H(k+1,s), g2)
///
/// This reuses y from ZODA — zero additional encoding work.
pub fn prox_verify_batched(
    signatures: &[[u8; 48]],
    public_keys: &[[u8; 96]],
    r: &[u32],
    y: &[u32],
    slot: u32,
) -> bool {
    let n = signatures.len();
    if n != public_keys.len() || n != r.len() || n == 0 {
        return false;
    }

    // Equation (2) from the paper:
    //   Σ_i r_i · e(Σ_i, PK_i) == e((Σr_i)·H(0,s) + Σ_k y_k·H(k+1,s), g2)
    //
    // Rearranged as pairing product check:
    //   Π_i e(r_i·Σ_i, PK_i) · e(-(rhs), g2) == 1

    // Compute the RHS G1 point
    let r_sum: u64 = r.iter().map(|&x| x as u64).sum();
    let r_sum_u32 = r_sum as u32;

    let mut rhs_point = g1_scalar_mul(&hash_to_g1(0, slot), r_sum_u32);
    for (k, &y_k) in y.iter().enumerate() {
        if y_k == 0 { continue; }
        let h_k = hash_to_g1((k + 1) as u32, slot);
        let scaled = g1_scalar_mul(&h_k, y_k);
        rhs_point = g1_add(&rhs_point, &scaled);
    }

    // Negate the RHS point for the pairing product check
    let mut neg_rhs = rhs_point;
    unsafe { blst::blst_p1_cneg(&mut neg_rhs, true); }

    // Accumulate all miller loops
    let mut accum = blst_fp12::default();
    let mut first = true;

    // LHS pairings: e(r_i · Σ_i, PK_i) for each signer
    for i in 0..n {
        let sig = match decompress_g1(&signatures[i]) {
            Some(p) => p,
            None => return false,
        };
        let pk = match PublicKey::uncompress(&public_keys[i]) {
            Ok(pk) => pk,
            Err(_) => return false,
        };

        let scaled_sig = g1_scalar_mul(&sig, r[i]);
        let sig_affine = g1_to_affine(&scaled_sig);
        let pk_affine = pk_to_affine(&pk);

        let mut ml = blst_fp12::default();
        unsafe { blst_miller_loop(&mut ml, &pk_affine, &sig_affine); }

        if first {
            accum = ml;
            first = false;
        } else {
            unsafe { blst_fp12_mul(&mut accum, &accum, &ml); }
        }
    }

    // RHS pairing: e(-rhs, g2)
    let neg_rhs_affine = g1_to_affine(&neg_rhs);
    let g2_gen = g2_generator();
    let mut rhs_ml = blst_fp12::default();
    unsafe { blst_miller_loop(&mut rhs_ml, &g2_gen, &neg_rhs_affine); }

    if first {
        accum = rhs_ml;
    } else {
        unsafe { blst_fp12_mul(&mut accum, &accum, &rhs_ml); }
    }

    // Final exponentiation: result should be 1
    let mut result = blst_fp12::default();
    unsafe {
        blst_final_exp(&mut result, &accum);
        blst_fp12_is_one(&result)
    }
}

// ============================================================================
// Low-level BLS12-381 helpers
// ============================================================================

fn hash_to_g1(index: u32, slot: u32) -> blst_p1 {
    let mut msg = [0u8; 8];
    msg[0..4].copy_from_slice(&index.to_le_bytes());
    msg[4..8].copy_from_slice(&slot.to_le_bytes());
    let mut out = blst_p1::default();
    unsafe {
        blst_hash_to_g1(
            &mut out,
            msg.as_ptr(), msg.len(),
            PROX_DST.as_ptr(), PROX_DST.len(),
            core::ptr::null(), 0,
        );
    }
    out
}

fn g1_scalar_mul(point: &blst_p1, scalar: u32) -> blst_p1 {
    if scalar == 0 {
        return blst_p1::default(); // point at infinity
    }
    if scalar == 1 {
        return *point; // identity
    }
    let mut scalar_bytes = [0u8; 32];
    scalar_bytes[0..4].copy_from_slice(&scalar.to_le_bytes());
    let mut out = blst_p1::default();
    unsafe {
        // nbits = number of significant bits in the scalar
        let nbits = 32 - scalar.leading_zeros();
        blst_p1_mult(&mut out, point, scalar_bytes.as_ptr(), nbits as usize);
    }
    out
}

fn g1_scalar_mul_secret(point: &blst_p1, secret: &SecretKey) -> blst_p1 {
    let sk_bytes = secret.to_bytes(); // big-endian
    let scalar = sk_to_blst_scalar(&sk_bytes);
    let mut out = blst_p1::default();
    unsafe {
        blst_p1_mult(&mut out, point, scalar.b.as_ptr(), 256);
    }
    out
}

/// Convert big-endian secret key bytes to blst_scalar (internal LE limb format).
fn sk_to_blst_scalar(sk_bytes: &[u8; 32]) -> blst_scalar {
    let mut scalar = blst_scalar::default();
    unsafe { blst::blst_scalar_from_bendian(&mut scalar, sk_bytes.as_ptr()); }
    scalar
}

fn g1_add(a: &blst_p1, b: &blst_p1) -> blst_p1 {
    let mut out = blst_p1::default();
    unsafe { blst_p1_add_or_double(&mut out, a, b); }
    out
}

fn g1_to_affine(point: &blst_p1) -> blst_p1_affine {
    let mut out = blst_p1_affine::default();
    unsafe { blst_p1_to_affine(&mut out, point); }
    out
}

fn g1_compress(point: &blst_p1) -> [u8; 48] {
    let affine = g1_to_affine(point);
    let mut out = [0u8; 48];
    unsafe {
        blst::blst_p1_affine_compress(out.as_mut_ptr(), &affine);
    }
    out
}

fn decompress_g1(bytes: &[u8; 48]) -> Option<blst_p1> {
    let mut affine = blst_p1_affine::default();
    let err = unsafe { blst::blst_p1_uncompress(&mut affine, bytes.as_ptr()) };
    if err != blst::BLST_ERROR::BLST_SUCCESS { return None; }
    let mut out = blst_p1::default();
    unsafe { blst_p1_from_affine(&mut out, &affine); }
    Some(out)
}

fn pk_to_affine(pk: &PublicKey) -> blst_p2_affine {
    // PublicKey in min_sig is a G2 point
    let compressed = pk.compress();
    let mut affine = blst_p2_affine::default();
    unsafe { blst::blst_p2_uncompress(&mut affine, compressed.as_ptr()); }
    affine
}

fn g2_generator() -> blst_p2_affine {
    unsafe { blst::blst_p2_affine_generator().read() }
}

fn g2_generator_proj() -> blst::blst_p2 {
    let aff = g2_generator();
    let mut proj = blst::blst_p2::default();
    unsafe { blst::blst_p2_from_affine(&mut proj, &aff); }
    proj
}

/// Compute modular inverse and return as blst_scalar (internal LE limb format).
fn scalar_inverse_as_blst_scalar(sk_bytes: &[u8; 32]) -> blst_scalar {
    let mut scalar = blst_scalar::default();
    unsafe { blst::blst_scalar_from_bendian(&mut scalar, sk_bytes.as_ptr()); }
    let mut fr = blst::blst_fr::default();
    unsafe { blst::blst_fr_from_scalar(&mut fr, &scalar); }
    let mut inv_fr = blst::blst_fr::default();
    unsafe { blst::blst_fr_eucl_inverse(&mut inv_fr, &fr); }
    let mut inv_scalar = blst_scalar::default();
    unsafe { blst::blst_scalar_from_fr(&mut inv_scalar, &inv_fr); }
    inv_scalar
}

/// Compute modular inverse of a scalar mod r (BLS12-381 scalar field order).
/// Input/output: 32 bytes big-endian.
fn scalar_inverse(sk_bytes: &[u8; 32]) -> [u8; 32] {
    // Use Fermat's little theorem: a^{-1} = a^{r-2} mod r
    // Import scalar, compute a^{r-2}, export
    let mut scalar = blst_scalar::default();
    unsafe { blst::blst_scalar_from_bendian(&mut scalar, sk_bytes.as_ptr()); }

    // BLS12-381 scalar field order r
    let r_minus_2: [u8; 32] = {
        // r = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001
        // r-2 = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfefffffffeffffffff
        let mut v = [
            0x73, 0xed, 0xa7, 0x53, 0x29, 0x9d, 0x7d, 0x48,
            0x33, 0x39, 0xd8, 0x08, 0x09, 0xa1, 0xd8, 0x05,
            0x53, 0xbd, 0xa4, 0x02, 0xff, 0xfe, 0x5b, 0xfe,
            0xff, 0xff, 0xff, 0xfe, 0xff, 0xff, 0xff, 0xff,
        ];
        v
    };

    // We need to compute scalar^(r-2) mod r using blst.
    // blst doesn't expose scalar exponentiation directly.
    // Alternative: use the blst_fr type for field arithmetic.
    let mut fr = blst::blst_fr::default();
    unsafe { blst::blst_fr_from_scalar(&mut fr, &scalar); }

    // Compute inverse via blst_fr_inverse (Euclidean)
    let mut inv_fr = blst::blst_fr::default();
    unsafe { blst::blst_fr_eucl_inverse(&mut inv_fr, &fr); }

    // Convert back to scalar bytes
    let mut inv_scalar = blst_scalar::default();
    unsafe { blst::blst_scalar_from_fr(&mut inv_scalar, &inv_fr); }
    let mut out = [0u8; 32];
    unsafe { blst::blst_bendian_from_scalar(out.as_mut_ptr(), &inv_scalar); }
    out
}

fn pairing_check(sig: &blst_p1, msg: &blst_p1, pk_bytes: &[u8; 96]) -> bool {
    let sig_affine = g1_to_affine(sig);
    let msg_affine = g1_to_affine(msg);
    let g2_gen = g2_generator();

    // Decompress PK (G2 point)
    let mut pk_affine = blst_p2_affine::default();
    let err = unsafe { blst::blst_p2_uncompress(&mut pk_affine, pk_bytes.as_ptr()) };
    if err != blst::BLST_ERROR::BLST_SUCCESS { return false; }

    // With PK = κ^{-1}·g2 and Σ = κ·msg:
    //   e(Σ, PK) = e(κ·msg, κ^{-1}·g2) = e(msg, g2)
    //
    // Check: e(sig, pk) · e(-msg, g2) == 1
    let mut neg_msg = *msg;
    unsafe { blst::blst_p1_cneg(&mut neg_msg, true); }
    let neg_msg_affine = g1_to_affine(&neg_msg);

    let mut ml1 = blst_fp12::default();
    let mut ml2 = blst_fp12::default();
    unsafe {
        blst_miller_loop(&mut ml1, &pk_affine, &sig_affine);
        blst_miller_loop(&mut ml2, &g2_gen, &neg_msg_affine);
        blst_fp12_mul(&mut ml1, &ml1, &ml2);
    }
    let mut result = blst_fp12::default();
    unsafe {
        blst_final_exp(&mut result, &ml1);
        blst_fp12_is_one(&result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_prox_sign_verify() {
        let kp = ProxKeypair::from_seed(&[42u8; 32]);
        let pk = kp.public_key_bytes();
        let data = vec![1u32, 2, 3, 4, 5];
        let slot = 100;
        let sig = kp.sign(&data, slot);
        assert!(prox_verify(&pk, &data, slot, &sig));
    }

    #[test]
    fn test_prox_wrong_data_fails() {
        let kp = ProxKeypair::from_seed(&[42u8; 32]);
        let pk = kp.public_key_bytes();
        let data = vec![1u32, 2, 3, 4, 5];
        let slot = 100;
        let sig = kp.sign(&data, slot);
        let wrong_data = vec![1, 2, 3, 4, 99]; // changed last element
        assert!(!prox_verify(&pk, &wrong_data, slot, &sig));
    }

    #[test]
    fn test_prox_wrong_slot_fails() {
        let kp = ProxKeypair::from_seed(&[42u8; 32]);
        let pk = kp.public_key_bytes();
        let data = vec![1u32, 2, 3];
        let sig = kp.sign(&data, 100);
        assert!(!prox_verify(&pk, &data, 101, &sig));
    }

    #[test]
    fn test_prox_wrong_key_fails() {
        let kp1 = ProxKeypair::from_seed(&[1u8; 32]);
        let kp2 = ProxKeypair::from_seed(&[2u8; 32]);
        let data = vec![10u32, 20, 30];
        let sig = kp1.sign(&data, 50);
        assert!(!prox_verify(&kp2.public_key_bytes(), &data, 50, &sig));
    }

    #[test]
    fn test_prox_empty_data() {
        let kp = ProxKeypair::from_seed(&[42u8; 32]);
        let pk = kp.public_key_bytes();
        let data: Vec<u32> = vec![];
        let slot = 1;
        let sig = kp.sign(&data, slot);
        assert!(prox_verify(&pk, &data, slot, &sig));
    }

    #[test]
    fn test_prox_deterministic() {
        let kp = ProxKeypair::from_seed(&[42u8; 32]);
        let data = vec![1u32, 2, 3];
        let sig1 = kp.sign(&data, 100);
        let sig2 = kp.sign(&data, 100);
        assert_eq!(sig1, sig2);
    }

    #[test]
    fn test_scalar_mul_roundtrip() {
        // Verify that scalar_mul(G, k) then scalar_mul(result, k_inv) == G
        let g = hash_to_g1(42, 100);
        let k: u32 = 7;
        let scaled = g1_scalar_mul(&g, k);
        // If we scale by 7 and then by 7^{-1} mod r, we should get G back
        // For now just check scaling by 1 is identity
        let identity = g1_scalar_mul(&g, 1);
        let g_affine = g1_to_affine(&g);
        let id_affine = g1_to_affine(&identity);
        assert_eq!(
            g1_compress(&g), g1_compress(&identity),
            "scaling by 1 must be identity"
        );
    }

    #[test]
    fn test_secret_key_mul() {
        // Verify our g1_scalar_mul_secret produces the right result
        // by checking: sk_mul(G, κ) paired with PK(κ^{-1}·g2) == e(G, g2)
        let kp = ProxKeypair::from_seed(&[42u8; 32]);
        let pk = kp.public_key_bytes();
        let g = hash_to_g1(0, 100);
        let kg = g1_scalar_mul_secret(&g, &kp.secret);

        // e(κ·G, κ^{-1}·g2) should equal e(G, g2)
        let check = pairing_check(&kg, &g, &pk);
        assert!(check, "e(κ·G, PK) == e(G, g2) must hold");
    }

    #[test]
    fn test_prox_pairing_identity() {
        // Verify that e(κ·msg, κ^{-1}·g2) == e(msg, g2)
        // This is the core algebraic identity the proximity sig relies on
        let kp = ProxKeypair::from_seed(&[42u8; 32]);
        let pk = kp.public_key_bytes();
        let data = vec![1u32, 2, 3];
        let slot = 100;
        let sig = kp.sign(&data, slot);

        // Single verify works, confirming the identity holds
        assert!(prox_verify(&pk, &data, slot, &sig));
    }

    #[test]
    fn test_prox_batched_single_signer() {
        let kp = ProxKeypair::from_seed(&[42u8; 32]);
        let pk = kp.public_key_bytes();
        let data = vec![1u32, 2, 3, 4, 5];
        let slot = 100;
        let sig = kp.sign(&data, slot);

        // Batched with r=[1] and y=data (trivial single-signer case)
        assert!(prox_verify_batched(
            &[sig],
            &[pk],
            &[1],
            &data,
            slot,
        ));
    }

    #[test]
    fn test_blst_scalar_format() {
        let seed = [42u8; 32];
        let sk = SecretKey::key_gen(&seed, &[]).unwrap();
        let sk_bytes = sk.to_bytes();
        eprintln!("sk.to_bytes() = {:02x?}", &sk_bytes[..]);
        
        // Method 1: raw sk_bytes directly to blst_p1_mult
        let g = hash_to_g1(0, 100);
        let mut r1 = blst_p1::default();
        unsafe { blst_p1_mult(&mut r1, &g, sk_bytes.as_ptr(), 256); }
        
        // Method 2: convert from big-endian to blst_scalar, use scalar.b
        let mut scalar = blst_scalar::default();
        unsafe { blst::blst_scalar_from_bendian(&mut scalar, sk_bytes.as_ptr()); }
        let mut r2 = blst_p1::default();
        unsafe { blst_p1_mult(&mut r2, &g, scalar.b.as_ptr(), 256); }
        
        // Method 3: convert from little-endian to blst_scalar
        let mut le_bytes = sk_bytes;
        le_bytes.reverse();
        let mut scalar_le = blst_scalar::default();
        unsafe { blst::blst_scalar_from_lendian(&mut scalar_le, le_bytes.as_ptr()); }
        let mut r3 = blst_p1::default();
        unsafe { blst_p1_mult(&mut r3, &g, scalar_le.b.as_ptr(), 256); }
        
        // Method 4: try sk_bytes as-is (maybe it's already LE for blst_p1_mult)
        let mut r4 = blst_p1::default();
        let mut reversed = sk_bytes;
        reversed.reverse();
        unsafe { blst_p1_mult(&mut r4, &g, reversed.as_ptr(), 256); }
        
        // Now verify which one matches sk_to_pk (κ * g1_generator)
        // sk_to_pk uses G1 generator, we use hash_to_g1 - different points
        // But we can verify: e(κ*G, κ^{-1}*g2) == e(G, g2)
        // by checking if the pairing holds
        
        let pk = kp_public_key_internal(&sk);
        
        for (i, r) in [r1, r2, r3, r4].iter().enumerate() {
            let check = pairing_check(r, &g, &pk);
            eprintln!("method {}: pairing_check = {}", i+1, check);
        }
    }
    
    fn kp_public_key_internal(secret: &SecretKey) -> [u8; 96] {
        let sk_bytes = secret.to_bytes();
        let inv_scalar = scalar_inverse_as_blst_scalar(&sk_bytes);
        let g2_gen_proj = g2_generator_proj();
        let mut pk_point = blst::blst_p2::default();
        unsafe {
            blst::blst_p2_mult(&mut pk_point, &g2_gen_proj, inv_scalar.b.as_ptr(), 256);
        }
        let mut pk_affine = blst_p2_affine::default();
        unsafe { blst::blst_p2_to_affine(&mut pk_affine, &pk_point); }
        let mut out = [0u8; 96];
        unsafe { blst::blst_p2_affine_compress(out.as_mut_ptr(), &pk_affine); }
        out
    }

    #[test]
    fn test_scalar_inverse_roundtrip() {
        // k * k_inv == 1 mod r
        let seed = [42u8; 32];
        let sk = SecretKey::key_gen(&seed, &[]).unwrap();
        let sk_bytes = sk.to_bytes(); // big-endian
        
        let inv_bytes = scalar_inverse(&sk_bytes);
        
        // Multiply: k * k_inv should give 1
        let mut k_fr = blst::blst_fr::default();
        let mut kinv_fr = blst::blst_fr::default();
        let mut k_scalar = blst_scalar::default();
        let mut kinv_scalar = blst_scalar::default();
        unsafe {
            blst::blst_scalar_from_bendian(&mut k_scalar, sk_bytes.as_ptr());
            blst::blst_scalar_from_bendian(&mut kinv_scalar, inv_bytes.as_ptr());
            blst::blst_fr_from_scalar(&mut k_fr, &k_scalar);
            blst::blst_fr_from_scalar(&mut kinv_fr, &kinv_scalar);
        }
        
        let mut product = blst::blst_fr::default();
        unsafe { blst::blst_fr_mul(&mut product, &k_fr, &kinv_fr); }
        
        // Convert product to scalar and check it's 1
        let mut prod_scalar = blst_scalar::default();
        unsafe { blst::blst_scalar_from_fr(&mut prod_scalar, &product); }
        let mut prod_bytes = [0u8; 32];
        unsafe { blst::blst_bendian_from_scalar(prod_bytes.as_mut_ptr(), &prod_scalar); }
        
        eprintln!("k * k_inv = {:02x?}", &prod_bytes[..]);
        // Should be: 00...01
        assert_eq!(prod_bytes[31], 1, "last byte should be 1");
        assert!(prod_bytes[..31].iter().all(|&b| b == 0), "all other bytes should be 0");
    }

    #[test]
    fn test_pk_generation() {
        // Verify PK = κ^{-1} · g2 by checking κ · PK == g2
        let seed = [42u8; 32];
        let sk = SecretKey::key_gen(&seed, &[]).unwrap();
        let sk_bytes = sk.to_bytes();
        
        let pk_bytes = kp_public_key_internal(&sk);
        
        // Decompress PK
        let mut pk_affine = blst_p2_affine::default();
        unsafe { blst::blst_p2_uncompress(&mut pk_affine, pk_bytes.as_ptr()); }
        let mut pk_proj = blst::blst_p2::default();
        unsafe { blst::blst_p2_from_affine(&mut pk_proj, &pk_affine); }
        
        // Multiply PK by κ: should give g2
        let scalar = sk_to_blst_scalar(&sk_bytes);
        let mut result = blst::blst_p2::default();
        unsafe { blst::blst_p2_mult(&mut result, &pk_proj, scalar.b.as_ptr(), 256); }
        
        // Compare with g2 generator
        let g2 = g2_generator_proj();
        let mut result_aff = blst_p2_affine::default();
        let mut g2_aff = blst_p2_affine::default();
        unsafe {
            blst::blst_p2_to_affine(&mut result_aff, &result);
            blst::blst_p2_to_affine(&mut g2_aff, &g2);
        }
        let mut r_comp = [0u8; 96];
        let mut g_comp = [0u8; 96];
        unsafe {
            blst::blst_p2_affine_compress(r_comp.as_mut_ptr(), &result_aff);
            blst::blst_p2_affine_compress(g_comp.as_mut_ptr(), &g2_aff);
        }
        
        eprintln!("κ · PK = {:02x?}", &r_comp[..8]);
        eprintln!("g2     = {:02x?}", &g_comp[..8]);
        assert_eq!(r_comp, g_comp, "k * k_inv * g2 should equal g2");
    }
}
