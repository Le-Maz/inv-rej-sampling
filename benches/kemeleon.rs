#![feature(test)]

extern crate test;

use test::Bencher;

use std::{cmp::Ordering, num::NonZero};

/// A simple, fixed-size big integer representation.
/// 49 limbs of 64 bits = 3136 bits, which safely holds our 3072-bit target.
#[derive(Clone, Copy)]
struct BigInt {
    limbs: [u64; 49],
}

impl BigInt {
    const fn zero() -> Self {
        Self { limbs: [0; 49] }
    }

    const fn one() -> Self {
        let mut b = Self::zero();
        b.limbs[0] = 1;
        b
    }

    /// Add another big integer to this one.
    #[inline]
    fn add(&mut self, other: &Self) {
        let mut carry: u128 = 0;
        for i in 0..49 {
            let sum = (self.limbs[i] as u128) + (other.limbs[i] as u128) + carry;
            self.limbs[i] = sum as u64;
            carry = sum >> 64;
        }
    }

    /// Subtract another big integer from this one (assumes self >= other).
    #[inline]
    fn sub(&mut self, other: &Self) {
        let mut borrow: u64 = 0;
        for i in 0..49 {
            let (res1, b1) = self.limbs[i].overflowing_sub(other.limbs[i]);
            let (res2, b2) = res1.overflowing_sub(borrow);
            self.limbs[i] = res2;
            borrow = (b1 || b2) as u64;
        }
    }

    /// Compare with another big integer.
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        for i in (0..49).rev() {
            if self.limbs[i] > other.limbs[i] {
                return Ordering::Greater;
            } else if self.limbs[i] < other.limbs[i] {
                return Ordering::Less;
            }
        }
        Ordering::Equal
    }
}

impl BigInt {
    /// Multiply the big integer by a single 64-bit limb.
    #[inline]
    fn mul_limb(&mut self, limb: u64) {
        #[cfg(target_arch = "x86_64")]
        {
            self.mul_limb_x86_64(limb)
        }
        #[cfg(not(target_arch = "x86_64"))]
        {
            self.mul_limb_portable(limb)
        }
    }

    #[cfg(not(target_arch = "x86_64"))]
    #[inline]
    fn mul_limb_portable(&mut self, limb: u64) {
        let mut carry: u128 = 0;
        for i in 0..49 {
            let prod = (self.limbs[i] as u128) * (limb as u128) + carry;
            self.limbs[i] = prod as u64;
            carry = prod >> 64;
        }
    }

    /// x86-64 fast path: MUL gives the full 128-bit product in RDX:RAX in one
    /// instruction; ADD/ADC folds the incoming carry into that same 128-bit
    /// value instead of emulating it with u128 arithmetic.
    #[cfg(target_arch = "x86_64")]
    #[inline]
    fn mul_limb_x86_64(&mut self, limb: u64) {
        // SAFETY: operates purely on `self.limbs` (49 x 8 = 392 bytes) via a
        // pointer we own, walking forward exactly 49 iterations. No reads or
        // writes occur outside that range. `mul` cannot fault (unlike `div`,
        // it has no zero-divisor / overflow case to worry about).
        unsafe {
            core::arch::asm!(
                "xor r8, r8",           // carry = 0
                "mov rcx, 49",          // loop counter
                "2:",
                "mov rax, [{ptr}]",     // rax = limbs[i]
                "mul {limb}",           // rdx:rax = limbs[i] * limb
                "add rax, r8",          // fold carry into the 128-bit product
                "adc rdx, 0",
                "mov [{ptr}], rax",     // limbs[i] = low 64 bits
                "mov r8, rdx",          // carry = high 64 bits
                "add {ptr}, 8",
                "dec rcx",
                "jnz 2b",
                ptr = inout(reg) self.limbs.as_mut_ptr() => _,
                limb = in(reg) limb,
                out("rax") _,
                out("rdx") _,
                out("rcx") _,
                out("r8") _,
                options(nostack),
            );
        }
    }

    /// Add a single 64-bit limb to the big integer.
    #[inline]
    fn add_limb(&mut self, limb: u64) {
        #[cfg(target_arch = "x86_64")]
        {
            self.add_limb_x86_64(limb)
        }
        #[cfg(not(target_arch = "x86_64"))]
        {
            self.add_limb_portable(limb)
        }
    }

    #[cfg(not(target_arch = "x86_64"))]
    #[inline]
    fn add_limb_portable(&mut self, limb: u64) {
        let mut carry: u128 = limb as u128;
        for i in 0..49 {
            if carry == 0 {
                break;
            }
            let sum = (self.limbs[i] as u128) + carry;
            self.limbs[i] = sum as u64;
            carry = sum >> 64;
        }
    }

    /// x86-64 fast path: a single ADD seeds the carry flag, then a tight
    /// ADC chain propagates it limb by limb, exiting via `jnc` the moment
    /// the flag clears — mirroring the original's early `break`, but as a
    /// branch on a hardware flag instead of a boolean carry check.
    #[cfg(target_arch = "x86_64")]
    #[inline]
    fn add_limb_x86_64(&mut self, limb: u64) {
        // SAFETY: same bounds reasoning as mul_limb_x86_64 — walks forward
        // within self.limbs (49 x 8 bytes), stopping at 49 iterations
        // whether via early exit (jnc) or the counter reaching zero.
        unsafe {
            core::arch::asm!(
                "mov rax, [{ptr}]",
                "add rax, {limb}",
                "mov [{ptr}], rax",
                "jnc 3f",               // no carry out of limb 0: done
                "mov rcx, 48",          // remaining limbs to potentially touch
                "2:",
                "add {ptr}, 8",
                "mov rax, [{ptr}]",
                "adc rax, 0",
                "mov [{ptr}], rax",
                "jnc 3f",               // carry absorbed: stop early
                "dec rcx",
                "jnz 2b",
                "3:",
                ptr = inout(reg) self.limbs.as_mut_ptr() => _,
                limb = in(reg) limb,
                out("rax") _,
                out("rcx") _,
                options(nostack),
            );
        }
    }
}

impl BigInt {
    /// Divide by a single 32-bit limb, modifying in place and returning the remainder.
    ///
    /// `limb` is `NonZero<u32>` because a zero divisor is a contract violation,
    /// not a runtime condition to check — this also removes the last precondition
    /// the x86-64 fast path needed to assert manually.
    #[inline]
    fn div_limb(&mut self, limb: NonZero<u32>) -> u32 {
        #[cfg(target_arch = "x86_64")]
        {
            self.div_limb_x86_64(limb)
        }
        #[cfg(not(target_arch = "x86_64"))]
        {
            self.div_limb_portable(limb)
        }
    }

    /// Portable fallback: 128-bit software division per limb.
    #[cfg(not(target_arch = "x86_64"))]
    #[inline]
    fn div_limb_portable(&mut self, limb: NonZero<u32>) -> u32 {
        let divisor = limb.get() as u128;
        let mut rem: u128 = 0;
        for i in (0..49).rev() {
            let num = (rem << 64) | (self.limbs[i] as u128);
            self.limbs[i] = (num / divisor) as u64;
            rem = num % divisor;
        }
        rem as u32
    }

    /// x86-64 fast path: uses the DIV instruction directly for a 128-bit/64-bit
    /// division per limb, instead of emulating it with u128 arithmetic.
    ///
    /// Safety invariant: `rem` is always `< limb` (a u32) at the start of each
    /// iteration, so the 128-bit dividend `(rem << 64) | self.limbs[i]` is always
    /// `< (limb as u128) << 64`. That guarantees the quotient fits in 64 bits,
    /// so DIV cannot trigger a #DE (quotient-overflow) fault. `limb: NonZero<u32>`
    /// rules out the other #DE case (division by zero) at the type level.
    #[cfg(target_arch = "x86_64")]
    #[inline]
    fn div_limb_x86_64(&mut self, limb: NonZero<u32>) -> u32 {
        let divisor = limb.get() as u64;
        let mut rem: u64 = 0;

        for i in (0..49).rev() {
            let lo = self.limbs[i];
            let hi = rem;
            let quotient: u64;
            let remainder: u64;

            // SAFETY: `divisor` is nonzero by construction (NonZero<u32>), and
            // by the invariant above, hi:lo / divisor fits in 64 bits, so this
            // cannot fault. No memory is touched; only registers.
            unsafe {
                core::arch::asm!(
                    "div {divisor}",
                    divisor = in(reg) divisor,
                    inout("rax") lo => quotient,
                    inout("rdx") hi => remainder,
                    options(pure, nomem, nostack),
                );
            }

            self.limbs[i] = quotient;
            rem = remainder;
        }

        rem as u32
    }
}

/// Draws a full 64-bit value from a u32-producing RNG by combining two calls.
#[inline]
fn next_u64(rng: &mut impl FnMut() -> u32) -> u64 {
    let lo = rng() as u64;
    let hi = rng() as u64;
    (hi << 32) | lo
}

/// Encodes a vector of length `n=256` of coefficients modulo `q=3329` to a byte-aligned integer.
#[allow(non_snake_case)]
pub fn VectorEncode(a: &[u32; 256], mut rng: impl FnMut() -> u32) -> [u8; 384] {
    let mut r = BigInt::zero();

    // Accumulate coefficients using Horner's method to avoid computing q^(i-1) explicitly.
    // r = a[0] + a[1]*q + a[2]*q^2 + ... + a[255]*q^255
    for i in (0..256).rev() {
        r.mul_limb(3329);
        r.add_limb(a[i] as u64);
    }

    // Compute q^n (where q = 3329, n = 256)
    let mut q_pow = BigInt::one();
    for _ in 0..256 {
        q_pow.mul_limb(3329);
    }

    // Compute 2^3072 (48th limb is 1 since 48 * 64 = 3072)
    let mut two_3072 = BigInt::zero();
    two_3072.limbs[48] = 1;

    let mut rem = two_3072;
    rem.sub(&r);

    // To compute max_m = floor((2^3072 - r) / q^n), we can avoid a full large-integer
    // division by utilizing a simple shift-and-subtract approach.
    // The quotient fits easily within 79 bits.
    let mut q_shifted = [BigInt::zero(); 79];
    q_shifted[0] = q_pow;
    for i in 1..=78 {
        q_shifted[i] = q_shifted[i - 1];
        q_shifted[i].mul_limb(2);
    }

    let mut max_m = [0u64; 2];
    for i in (0..=78).rev() {
        if rem.cmp(&q_shifted[i]) != Ordering::Less {
            rem.sub(&q_shifted[i]);
            max_m[i / 64] |= 1u64 << (i % 64);
        }
    }

    // Sample `m` uniformly from [0, max_m] using rejection sampling.
    let mut m = [0u64; 2];
    loop {
        m[0] = next_u64(&mut rng);
        m[1] = (rng() as u64) & 0x7FFF; // 15 bits, making 79 bits total limit

        if m[1] < max_m[1] {
            break;
        }
        if m[1] == max_m[1] && m[0] <= max_m[0] {
            break;
        }
    }

    // Add m * q^n to r using our shifted multiples.
    let mut m_q_pow = BigInt::zero();
    for i in 0..79 {
        if (m[i / 64] & (1u64 << (i % 64))) != 0 {
            m_q_pow.add(&q_shifted[i]);
        }
    }
    r.add(&m_q_pow);

    // Serialize output into a 384-byte array (Little Endian).
    let mut out = [0u8; 384];
    for i in 0..48 {
        let bytes = r.limbs[i].to_le_bytes();
        out[i * 8..i * 8 + 8].copy_from_slice(&bytes);
    }
    out
}

/// Inverts the VectorEncode mapping, recovering the original vector of coefficients.
#[allow(non_snake_case)]
pub fn VectorDecode(encoded: &[u8; 384]) -> [u32; 256] {
    let mut r = BigInt::zero();
    for i in 0..48 {
        let mut bytes = [0u8; 8];
        bytes.copy_from_slice(&encoded[i * 8..i * 8 + 8]);
        r.limbs[i] = u64::from_le_bytes(bytes);
    }

    let mut a = [0u32; 256];

    // Extract coefficients sequentially. Because of polynomial base encoding, dividing by `q`
    // accurately pops the lowest coefficient remainder. This process handles the `r % q^n` requirement
    // automatically by leaving the `m` multiplier untouched as the final discarded quotient.
    for i in 0..256 {
        a[i] = r.div_limb(NonZero::new(3329).unwrap());
    }

    a
}

/// A simple Xorshift pseudo-random number generator for testing purposes.
struct TestRng {
    state: u32,
}

impl TestRng {
    fn new(seed: u32) -> Self {
        Self {
            state: if seed == 0 { 1 } else { seed },
        }
    }

    fn next_u32(&mut self) -> u32 {
        self.state ^= self.state << 13;
        self.state ^= self.state >> 17;
        self.state ^= self.state << 5;
        self.state
    }
}

#[test]
fn test_encode_decode_roundtrip() {
    let mut rng = TestRng::new(42);
    let mut original_vector = [0u32; 256];

    for i in 0..256 {
        original_vector[i] = rng.next_u32() % 3329;
    }

    let encoded_value = VectorEncode(&original_vector, || rng.next_u32());
    let decoded_vector = VectorDecode(&encoded_value);

    assert_eq!(
        original_vector, decoded_vector,
        "The decoded vector did not match the original encoded vector."
    );
}

#[bench]
fn bench_vector_encode(b: &mut Bencher) {
    let mut rng = TestRng::new(42);
    let mut original_vector = [0u32; 256];

    for i in 0..256 {
        original_vector[i] = rng.next_u32() % 3329;
    }

    b.bytes = 384;
    b.iter(|| VectorEncode(&original_vector, || rng.next_u32()));
}

#[bench]
fn bench_vector_decode(b: &mut Bencher) {
    let mut rng = TestRng::new(42);
    let mut original_vector = [0u32; 256];

    for i in 0..256 {
        original_vector[i] = rng.next_u32() % 3329;
    }

    let encoded_value = VectorEncode(&original_vector, || rng.next_u32());

    b.bytes = 384;
    b.iter(|| VectorDecode(&encoded_value));
}
