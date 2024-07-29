//! Modular reduction implementation.

use crate::{Limb, Odd, Uint, U256};

#[cfg(feature = "alloc")]
use {crate::BoxedUint, subtle::Choice};

/// Implement the Montgomery reduction algorithm.
///
/// This is implemented as a macro to abstract over `const fn` and boxed use cases, since the latter
/// needs mutable references and thus the unstable `const_mut_refs` feature (rust-lang/rust#57349).
// TODO(tarcieri): change this into a `const fn` when `const_mut_refs` is stable
macro_rules! impl_montgomery_reduction {
    ($upper:expr, $lower:expr, $modulus:expr, $mod_neg_inv:expr, $limbs:expr) => {{
        let mut meta_carry = Limb::ZERO;
        let mut new_sum;

        let mut i = 0;
        while i < $limbs {
            let u = $lower[i].wrapping_mul($mod_neg_inv);

            let (_, mut carry) = $lower[i].mac(u, $modulus[0], Limb::ZERO);
            let mut new_limb;

            let mut j = 1;
            while j < ($limbs - i) {
                (new_limb, carry) = $lower[i + j].mac(u, $modulus[j], carry);
                $lower[i + j] = new_limb;
                j += 1;
            }
            while j < $limbs {
                (new_limb, carry) = $upper[i + j - $limbs].mac(u, $modulus[j], carry);
                $upper[i + j - $limbs] = new_limb;
                j += 1;
            }

            (new_sum, meta_carry) = $upper[i].adc(carry, meta_carry);
            $upper[i] = new_sum;

            i += 1;
        }

        meta_carry
    }};
}

/// Algorithm 14.32 in Handbook of Applied Cryptography <https://cacr.uwaterloo.ca/hac/about/chap14.pdf>
pub const fn montgomery_reduction<const LIMBS: usize>(
    lower_upper: &(Uint<LIMBS>, Uint<LIMBS>),
    modulus: &Odd<Uint<LIMBS>>,
    mod_neg_inv: Limb,
) -> Uint<LIMBS> {
    let (mut lower, mut upper) = *lower_upper;
    let meta_carry = impl_montgomery_reduction!(
        upper.limbs,
        lower.limbs,
        &modulus.0.limbs,
        mod_neg_inv,
        LIMBS
    );

    // Division is simply taking the upper half of the limbs
    // Final reduction (at this point, the value is at most 2 * modulus,
    // so `meta_carry` is either 0 or 1)
    upper.sub_mod_with_carry(meta_carry, &modulus.0, &modulus.0)
}

/// Algorithm 14.32 in Handbook of Applied Cryptography <https://cacr.uwaterloo.ca/hac/about/chap14.pdf>
///
/// This version writes the result into the provided [`BoxedUint`].
#[cfg(feature = "alloc")]
pub(crate) fn montgomery_reduction_boxed_mut(
    x: &mut BoxedUint,
    modulus: &BoxedUint,
    mod_neg_inv: Limb,
    out: &mut BoxedUint,
) {
    debug_assert_eq!(x.nlimbs(), modulus.nlimbs() * 2);
    debug_assert_eq!(out.nlimbs(), modulus.nlimbs());

    let (lower, upper) = x.limbs.split_at_mut(modulus.nlimbs());
    let meta_carry =
        impl_montgomery_reduction!(upper, lower, &modulus.limbs, mod_neg_inv, modulus.nlimbs());

    out.limbs.copy_from_slice(upper);
    let borrow = out.sbb_assign(modulus, Limb::ZERO);

    // The new `borrow = Word::MAX` iff `carry == 0` and `borrow == Word::MAX`.
    let borrow = Limb((!meta_carry.0.wrapping_neg()) & borrow.0);

    // If underflow occurred on the final limb, borrow = 0xfff...fff, otherwise
    // borrow = 0x000...000. Thus, we use it as a mask to conditionally add the modulus.
    out.conditional_adc_assign(modulus, Choice::from((borrow.0 & 1) as u8));
}

/// Algorithm 14.32 in Handbook of Applied Cryptography <https://cacr.uwaterloo.ca/hac/about/chap14.pdf>
///
/// This version allocates and returns a [`BoxedUint`].
#[cfg(feature = "alloc")]
#[inline]
pub(crate) fn montgomery_reduction_boxed(
    x: &mut BoxedUint,
    modulus: &BoxedUint,
    mod_neg_inv: Limb,
) -> BoxedUint {
    let mut ret = BoxedUint::zero_with_precision(modulus.bits_precision());
    montgomery_reduction_boxed_mut(x, modulus, mod_neg_inv, &mut ret);
    ret
}
// barrett reduction
  #[inline]
  #[allow(clippy::too_many_arguments)]
  pub fn barrett_reduce(lo: U256, hi: U256, mu:[u64;5], modulus: [u64; 4]) -> U256 {
      let lo = lo.as_words();
      let hi = hi.as_words();
      let a0 = lo[0];
      let a1 = lo[1];
      let a2 = lo[2];
      let a3 = lo[3];
      let a4 = hi[0];
      let a5 = hi[1];
      let a6 = hi[2];
      let a7 = hi[3];
      let q1: [u64; 5] = [a3, a4, a5, a6, a7];
      let q3 = q1_times_mu_shift_five(&q1, &mu);

      let r1: [u64; 5] = [a0, a1, a2, a3, a4];
      let r2: [u64; 5] = q3_times_n_keep_five(&q3, &modulus);
      let r: [u64; 5] = sub_inner_five(r1, r2);

      // Result is in range (0, 3*n - 1),
      // and 90% of the time, no subtraction will be needed.
      let r = subtract_n_if_necessary(r[0], r[1], r[2], r[3], r[4], modulus);
      let r = subtract_n_if_necessary(r[0], r[1], r[2], r[3], r[4], modulus);
      U256::from_words([r[0], r[1], r[2], r[3]])
  }
// // helper for. barret reduce function
  #[allow(unused)]
  const fn q1_times_mu_shift_five(q1: &[u64; 5], mu: &[u64; 5]) -> [u64; 5] {
      // Schoolbook multiplication.
      let (_w0, carry) = mac(0, q1[0], mu[0], 0);
      let (w1, carry) = mac(0, q1[0], mu[1], carry);
      let (w2, carry) = mac(0, q1[0], mu[2], carry);
      let (w3, carry) = mac(0, q1[0], mu[3], carry);
      let (w4, w5) = mac(0, q1[0], mu[4], carry);
      let (_w1, carry) = mac(w1, q1[1], mu[0], 0);
      let (w2, carry) = mac(w2, q1[1], mu[1], carry);
      let (w3, carry) = mac(w3, q1[1], mu[2], carry);
      let (w4, carry) = mac(w4, q1[1], mu[3], carry);
      let (w5, w6) = mac(w5, q1[1], mu[4], carry);
      let (_w2, carry) = mac(w2, q1[2], mu[0], 0);
      let (w3, carry) = mac(w3, q1[2], mu[1], carry);
      let (w4, carry) = mac(w4, q1[2], mu[2], carry);
      let (w5, carry) = mac(w5, q1[2], mu[3], carry);
      let (w6, w7) = mac(w6, q1[2], mu[4], carry);
      let (_w3, carry) = mac(w3, q1[3], mu[0], 0);
      let (w4, carry) = mac(w4, q1[3], mu[1], carry);
      let (w5, carry) = mac(w5, q1[3], mu[2], carry);
      let (w6, carry) = mac(w6, q1[3], mu[3], carry);
      let (w7, w8) = mac(w7, q1[3], mu[4], carry);
      let (_w4, carry) = mac(w4, q1[4], mu[0], 0);
      let (w5, carry) = mac(w5, q1[4], mu[1], carry);
      let (w6, carry) = mac(w6, q1[4], mu[2], carry);
      let (w7, carry) = mac(w7, q1[4], mu[3], carry);
      let (w8, w9) = mac(w8, q1[4], mu[4], carry);
      // let q2 = [_w0, _w1, _w2, _w3, _w4, w5, w6, w7, w8, w9];
      [w5, w6, w7, w8, w9]
  }
  #[allow(unused)]
  const fn q3_times_n_keep_five(q3: &[u64; 5], modulus: &[u64; 4]) -> [u64; 5] {
      // Schoolbook multiplication.
    //   let modulus = $modulus.as_words();
      let (w0, carry) = mac(0, q3[0], modulus[0], 0);
      let (w1, carry) = mac(0, q3[0], modulus[1], carry);
      let (w2, carry) = mac(0, q3[0], modulus[2], carry);
      let (w3, carry) = mac(0, q3[0], modulus[3], carry);
      let (w4, _) = mac(0, q3[0], 0, carry);
      let (w1, carry) = mac(w1, q3[1], modulus[0], 0);
      let (w2, carry) = mac(w2, q3[1], modulus[1], carry);
      let (w3, carry) = mac(w3, q3[1], modulus[2], carry);
      let (w4, _) = mac(w4, q3[1], modulus[3], carry);
      let (w2, carry) = mac(w2, q3[2], modulus[0], 0);
      let (w3, carry) = mac(w3, q3[2], modulus[1], carry);
      let (w4, _) = mac(w4, q3[2], modulus[2], carry);
      let (w3, carry) = mac(w3, q3[3], modulus[0], 0);
      let (w4, _) = mac(w4, q3[3], modulus[1], carry);
      let (w4, _) = mac(w4, q3[4], modulus[0], 0);
      [w0, w1, w2, w3, w4]
  }
  #[inline]
  #[allow(unused)]
  #[allow(clippy::too_many_arguments)]
  const fn sub_inner_five(l: [u64; 5], r: [u64; 5]) -> [u64; 5] {
      let (w0, borrow) = sbb(l[0], r[0], 0);
      let (w1, borrow) = sbb(l[1], r[1], borrow);
      let (w2, borrow) = sbb(l[2], r[2], borrow);
      let (w3, borrow) = sbb(l[3], r[3], borrow);
      let (w4, _borrow) = sbb(l[4], r[4], borrow);
      // If underflow occurred on the final limb - don't care (= add b^{k+1}).
      [w0, w1, w2, w3, w4]
  }
  #[inline]
  #[allow(unused)]
  #[allow(clippy::too_many_arguments)]
  const fn subtract_n_if_necessary(r0: u64, r1: u64, r2: u64, r3: u64, r4: u64, modulus: [u64; 4]) -> [u64; 5] {
    //   let modulus = $modulus.as_words();
      let (w0, borrow) = sbb(r0, modulus[0], 0);
      let (w1, borrow) = sbb(r1, modulus[1], borrow);
      let (w2, borrow) = sbb(r2, modulus[2], borrow);
      let (w3, borrow) = sbb(r3, modulus[3], borrow);
      let (w4, borrow) = sbb(r4, 0, borrow);
      // If underflow occurred on the final limb, borrow = 0xfff...fff, otherwise
      // borrow = 0x000...000. Thus, we use it as a mask to conditionally add the
      // modulus.
      let (w0, carry) = adc(w0, modulus[0] & borrow, 0);
      let (w1, carry) = adc(w1, modulus[1] & borrow, carry);
      let (w2, carry) = adc(w2, modulus[2] & borrow, carry);
      let (w3, carry) = adc(w3, modulus[3] & borrow, carry);
      let (w4, _carry) = adc(w4, 0, carry);
      [w0, w1, w2, w3, w4]
  }
  /// Computes `a + b + carry`, returning the result along with the new carry. 64-bit version.
  #[inline(always)]
  pub const fn adc(a: u64, b: u64, carry: u64) -> (u64, u64) {
      let ret = (a as u128) + (b as u128) + (carry as u128);
      (ret as u64, (ret >> 64) as u64)
  }

  /// Computes `a - (b + borrow)`, returning the result along with the new borrow. 64-bit version.
  #[inline(always)]
  pub const fn sbb(a: u64, b: u64, borrow: u64) -> (u64, u64) {
      let ret = (a as u128).wrapping_sub((b as u128) + ((borrow >> 63) as u128));
      (ret as u64, (ret >> 64) as u64)
  }

  /// Computes `a + (b * c) + carry`, returning the result along with the new carry.
  #[inline(always)]
  pub const fn mac(a: u64, b: u64, c: u64, carry: u64) -> (u64, u64) {
      let ret = (a as u128) + ((b as u128) * (c as u128)) + (carry as u128);
      (ret as u64, (ret >> 64) as u64)
  }
