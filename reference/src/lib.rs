//! Inverse Rejection Sampling
//!
//! This module provides a reference implementation of an inverse rejection sampling scheme.
//! The scheme is utilized for embedding uniform data in near-uniform sequences over a domain where traditional data packing cannot be applied.
//!
//! This code embeds ML-KEM prime field `q = 3329` into a vector of 12-bit integers.
//!
//! To ensure cryptographic security, this module implements vector encoding and decoding using two distinct constant-time models:
//!
//! * **Program-Counter Constant-Time (PC-Sec):**
//!   This model performs conditionally placing elements from `data` into `mask` positions where the mask item is valid (`< 3329`).
//!   It prevents timing attacks based on control flow by ensuring the instruction pointer's path is independent of the secret data, though memory access patterns may still leak information.
//!
//! * **Memory Pattern Constant-Time (Mem-Sec):**
//!   This model provides vector encoding and decoding that is designed to be secure against cache attacks.
//!   It utilizes a data-oblivious Bitonic sort network to obscure both control flow and memory access patterns.
//!   
//! ## Implementation Details
//!
//! The memory-secure variants rely on sorting to move valid mask elements to the front of the array.
//! After sequentially overwriting these valid elements with the secret data, an unsorting operation is performed to route them back to their original positions within the mask.
//! Internal arrays are padded to the next power of two using `4095` - any other rejected item would work as well though.
//!
//! Decoding under the memory-secure model also reconstructs the dense array by moving valid elements to the front.
//! The implementation provides both unstable and stable sorting variants, where the stable sort preserves the original relative order of elements by using their original indices to break ties.
//! The stable memory-secure variant is specifically designed to be fully compatible with the output of the PC-secure variant.

use std::iter::repeat;

use ctutils::{Choice, CtEq, CtGt, CtLt, CtOption, CtSelect};

/// Calculates the number of comparators in a bitonic sorting network of size `m`.
pub const fn comparator_count(m: usize) -> usize {
    if m == 0 {
        return 0;
    }
    (m / 2) * m.ilog2() as usize * (m.ilog2() as usize + 1) / 2
}

/// Generates a sequence of comparator index pairs for a Bitonic sorting network of size `m`.
///
/// Requires `m` to be a power of two.
#[inline]
pub fn comparator_iter(m: usize) -> impl DoubleEndedIterator<Item = (usize, usize)> {
    assert!(m.is_power_of_two());

    (1..=m.ilog2()).flat_map(move |stage| {
        let k = 1 << stage;

        (0..stage).flat_map(move |step| {
            let j = 1 << (stage - 1 - step);

            (0..m).flat_map(move |i| {
                ((i & j) == 0).then(|| {
                    let l = i | j;
                    let dir = (i & k) == 0;

                    if dir { (i, l) } else { (l, i) }
                })
            })
        })
    })
}

/// Memory pattern model constant-time sorting array using the Bitonic sort network.
///
/// Uses constant-time selection for oblivious swaps and populates a transcript of decisions for later un-sorting.
/// Elements `< 3329` are treated as smaller, while elements `>= 3329` are treated as larger.
/// If `STABLE` is true, uses original element indices to break ties to maintain stability.
///
/// # Critical: the comparator must be a binary validity predicate, never a full-value comparison
///
/// This sort MUST partition strictly on validity (`< 3329` vs. `>= 3329`) and must never rank
/// valid elements against each other by their exact numeric value. It's tempting to "just sort
/// normally," since a full numeric sort still produces a valid trace and round-trips correctly
/// through `sort`/`unsort` — but it silently introduces a statistical bias.
///
/// `encode_vector_mem_sec` overwrites the front `data.len()` positions after sorting, then unsorts
/// to restore the rest. If ranking depended on exact value rather than only on the validity bit
/// (with `STABLE` breaking ties by original index, not by value), the smallest valid mask values
/// would always be pushed to the very front — and therefore always be the ones overwritten by
/// `data` whenever `data.len()` is less than the number of valid slots. The valid elements left
/// untouched would then be skewed toward the larger end of the `< 3329` range, pulling their mean
/// upward relative to a true uniform sample. That skew is an observable distribution mismatch: an
/// adversary inspecting the output's surviving valid values could detect the bias and learn that
/// encoding took place. The comparator below therefore always reduces both operands to a single
/// bit via `ct_lt(&3329)` and never compares `lhs_val` against `rhs_val` by magnitude.
#[inline]
pub fn sort<const STABLE: bool>(arr: &mut [u16], transcript: &mut [Choice]) {
    assert!(arr.len().is_power_of_two());
    assert_eq!(transcript.len(), comparator_count(arr.len()));

    let mut idx_tracker: Vec<usize> = if STABLE {
        (0..arr.len()).collect()
    } else {
        Vec::new()
    };

    let comparators = comparator_iter(arr.len());
    for (transcript_slot, (lhs_idx, rhs_idx)) in transcript.iter_mut().zip(comparators) {
        let [lhs_val, rhs_val] = arr.get_disjoint_mut([lhs_idx, rhs_idx]).unwrap();
        let (lhs_key, rhs_key) = (!lhs_val.ct_lt(&3329), !rhs_val.ct_lt(&3329));
        let mut should_swap = lhs_key & (!rhs_key);
        if STABLE {
            let keys_equal = lhs_key.ct_eq(&rhs_key);
            let [lhs_real_idx, rhs_real_idx] =
                idx_tracker.get_disjoint_mut([lhs_idx, rhs_idx]).unwrap();
            should_swap |= keys_equal & lhs_real_idx.ct_gt(&rhs_real_idx);
            lhs_real_idx.ct_swap(rhs_real_idx, should_swap);
        }
        lhs_val.ct_swap(rhs_val, should_swap);
        *transcript_slot = should_swap;
    }
}

/// Memory pattern model constant-time sorting array that ignores the swap transcript.
///
/// See [`sort`] for why the comparator must remain a binary validity check (`< 3329`)
/// rather than a full-value comparison — using magnitude instead of validity biases which
/// valid elements end up overwritten in `encode_vector_mem_sec`, skewing the mean of the
/// surviving values.
#[inline]
pub fn sort_without_transcript<const STABLE: bool>(arr: &mut [u16]) {
    assert!(arr.len().is_power_of_two());

    let mut idx_tracker: Vec<usize> = if STABLE {
        (0..arr.len()).collect()
    } else {
        Vec::new()
    };

    let comparators = comparator_iter(arr.len());
    for (lhs_idx, rhs_idx) in comparators {
        let [lhs_val, rhs_val] = arr.get_disjoint_mut([lhs_idx, rhs_idx]).unwrap();
        let (lhs_key, rhs_key) = (!lhs_val.ct_lt(&3329), !rhs_val.ct_lt(&3329));
        let mut should_swap = lhs_key & (!rhs_key);
        if STABLE {
            let keys_equal = lhs_key.ct_eq(&rhs_key);
            let [lhs_real_idx, rhs_real_idx] =
                idx_tracker.get_disjoint_mut([lhs_idx, rhs_idx]).unwrap();
            should_swap |= keys_equal & lhs_real_idx.ct_gt(&rhs_real_idx);
            lhs_real_idx.ct_swap(rhs_real_idx, should_swap);
        }
        lhs_val.ct_swap(rhs_val, should_swap);
    }
}

/// Memory pattern model constant-time unsorting.
///
/// Traverses the Bitonic sort comparison network in reverse, applying the swaps recorded in the transcript using constant-time selection.
#[inline]
pub fn unsort(arr: &mut [u16], transcript: &[Choice]) {
    assert!(arr.len().is_power_of_two());
    assert_eq!(transcript.len(), comparator_count(arr.len()));
    let comparators_rev = comparator_iter(arr.len()).rev();
    for (&should_swap, (lhs_idx, rhs_idx)) in transcript.iter().rev().zip(comparators_rev) {
        let [lhs_val, rhs_val] = arr.get_disjoint_mut([lhs_idx, rhs_idx]).unwrap();
        lhs_val.ct_swap(rhs_val, should_swap);
    }
}

/// Program-counter model constant-time vector encoding.
///
/// Conditionally places elements from `data` into `mask` positions where the mask item is valid (`< 3329`).
/// Returns a `CtOption` indicating whether all `data` elements were successfully encoded.
pub fn encode_vector_pc_sec(data: &[u16], mask: &[u16]) -> CtOption<Vec<u16>> {
    let mut output = vec![0u16; mask.len()];
    if data.len() == 0 {
        output.clone_from_slice(mask);
        return CtOption::new(output, Choice::TRUE);
    }

    let mut data_cur = 0;
    for (&mask_item, output_item) in mask.iter().zip(output.iter_mut()) {
        let has_data = !data.len().ct_eq(&data_cur);
        let safe_data_cur = (data.len() - 1).ct_select(&data_cur, has_data);
        let data_item = data[safe_data_cur];
        let use_data = mask_item.ct_lt(&3329) & has_data;
        *output_item = mask_item.ct_select(&data_item, use_data);
        data_cur = data_cur.ct_select(&(data_cur + 1), use_data);
    }
    CtOption::new(output, data.len().ct_eq(&data_cur))
}

/// Memory pattern model constant-time vector encoding free of cache attacks.
///
/// Relies on data-oblivious sorting to move valid mask elements to the front, overwriting them sequentially, and unsorting to route them back to their original positions.
/// Pads the internal array to a power of two with 4095.
pub fn encode_vector_mem_sec<const STABLE: bool>(data: &[u16], mask: &[u16]) -> CtOption<Vec<u16>> {
    let mut output = vec![0u16; mask.len()];
    if data.len() == 0 {
        output.clone_from_slice(mask);
        return CtOption::new(output, Choice::TRUE);
    }
    if mask.len() < data.len() {
        output.clone_from_slice(mask);
        return CtOption::new(output, Choice::FALSE);
    }

    let padded_len = mask.len().next_power_of_two();
    let mut arr = Vec::with_capacity(padded_len);
    let mut transcript = vec![Choice::FALSE; comparator_count(padded_len)];

    arr.extend_from_slice(mask);
    arr.extend(repeat(4095).take(padded_len - mask.len()));

    sort::<STABLE>(&mut arr, &mut transcript);
    let success = arr[data.len() - 1].ct_lt(&3329);
    arr[..data.len()].clone_from_slice(data);
    unsort(&mut arr, &transcript);

    output.clone_from_slice(&arr[..mask.len()]);

    CtOption::new(output, success)
}

/// Program-counter model constant-time vector decoding.
///
/// Extracts valid elements (`< 3329`) sequentially from `output` to reconstruct the original data vector.
/// Returns a `CtOption` indicating whether enough valid elements were found.
pub fn decode_vector_pc_sec(output: &[u16], data_len: usize) -> CtOption<Vec<u16>> {
    let mut data = vec![0u16; data_len];
    if data_len == 0 {
        return CtOption::new(data, Choice::TRUE);
    }
    if output.len() < data_len {
        return CtOption::new(data, Choice::FALSE);
    }

    let mut data_cur = 0;
    for &output_item in output.iter() {
        let is_valid = output_item.ct_lt(&3329);
        let has_space = !data_len.ct_eq(&data_cur);

        let safe_data_cur = (data_len - 1).ct_select(&data_cur, has_space);
        let current_val = data[safe_data_cur];

        let write_data = is_valid & has_space;
        data[safe_data_cur] = current_val.ct_select(&output_item, write_data);

        data_cur = data_cur.ct_select(&(data_cur + 1), write_data);
    }

    CtOption::new(data, data_len.ct_eq(&data_cur))
}

/// Memory pattern model constant-time vector decoding.
///
/// Reconstructs the dense array by moving valid elements to the front using a bitonic sort, avoiding timing and memory-pattern leakage.
#[inline]
pub fn decode_vector_mem_sec<const STABLE: bool>(
    output: &[u16],
    data_len: usize,
) -> CtOption<Vec<u16>> {
    let mut data = vec![0u16; data_len];
    if data_len == 0 {
        return CtOption::new(data, Choice::TRUE);
    }
    if output.len() < data_len {
        return CtOption::new(data, Choice::FALSE);
    }

    let padded_len = output.len().next_power_of_two();
    let mut arr = Vec::with_capacity(padded_len);

    arr.extend_from_slice(output);
    arr.extend(repeat(4095).take(padded_len - output.len()));

    sort_without_transcript::<STABLE>(&mut arr);
    let success = arr[data_len - 1].ct_lt(&3329);

    for (out_item, &arr_item) in data.iter_mut().zip(arr[..data_len].iter()) {
        let is_valid = arr_item.ct_lt(&3329);
        *out_item = 0.ct_select(&arr_item, is_valid);
    }

    CtOption::new(data, success)
}

#[cfg(test)]
mod tests {
    use super::*;

    struct XorShift64 {
        state: u64,
    }

    impl XorShift64 {
        fn new(seed: u64) -> Self {
            Self {
                state: if seed == 0 { 1 } else { seed },
            }
        }

        fn next(&mut self) -> u64 {
            let mut x = self.state;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.state = x;
            x
        }

        fn next_u16(&mut self) -> u16 {
            self.next() as u16
        }
    }

    fn generate_mask(rng: &mut XorShift64, len: usize, valid_prob: u16) -> Vec<u16> {
        (0..len)
            .map(|_| {
                let val = rng.next_u16();
                if val % 100 < valid_prob {
                    val % 3329
                } else {
                    3329 + (val % 1000)
                }
            })
            .collect()
    }

    fn generate_data(rng: &mut XorShift64, len: usize) -> Vec<u16> {
        (0..len).map(|_| rng.next_u16() % 3329).collect()
    }

    #[test]
    fn test_comparator_count() {
        assert_eq!(comparator_count(0), 0);
        assert_eq!(comparator_count(2), 1);
        assert_eq!(comparator_count(4), 6);
        assert_eq!(comparator_count(8), 24);
        assert_eq!(comparator_count(16), 80);
    }

    fn test_sort_and_unsort<const STABLE: bool>() {
        let mut rng = XorShift64::new(42);
        let original_arr = generate_mask(&mut rng, 16, 50);
        let mut arr = original_arr.clone();

        let mut transcript = vec![Choice::from(0); comparator_count(arr.len())];

        sort::<STABLE>(&mut arr, &mut transcript);

        let mut previous_was_invalid = false;
        for &val in &arr {
            let is_invalid = val >= 3329;
            if previous_was_invalid {
                assert!(is_invalid);
            }
            previous_was_invalid = is_invalid;
        }

        unsort(&mut arr, &transcript);
        assert_eq!(arr, original_arr);
    }

    #[test]
    fn test_sort_and_unsort_stable() {
        test_sort_and_unsort::<true>();
    }

    #[test]
    fn test_sort_and_unsort_unstable() {
        test_sort_and_unsort::<false>();
    }

    fn test_sort_without_transcript<const STABLE: bool>() {
        let mut rng = XorShift64::new(1337);
        let mut arr = generate_mask(&mut rng, 32, 50);

        sort_without_transcript::<STABLE>(&mut arr);

        let mut previous_was_invalid = false;
        for &val in &arr {
            let is_invalid = val >= 3329;
            if previous_was_invalid {
                assert!(is_invalid);
            }
            previous_was_invalid = is_invalid;
        }
    }

    #[test]
    fn test_sort_without_transcript_stable() {
        test_sort_without_transcript::<true>();
    }

    #[test]
    fn test_sort_without_transcript_unstable() {
        test_sort_without_transcript::<false>();
    }

    #[test]
    fn test_pc_sec_encode_decode() {
        let mask = vec![4000, 100, 4001, 200, 4002, 300, 4003, 4004];
        let data = vec![10, 20, 30];

        let encoded = encode_vector_pc_sec(&data, &mask).unwrap();
        let expected = vec![4000, 10, 4001, 20, 4002, 30, 4003, 4004];
        assert_eq!(encoded, expected);

        let decoded = decode_vector_pc_sec(&encoded, data.len()).unwrap();
        assert_eq!(decoded, data);
    }

    fn test_mem_sec_encode_decode<const STABLE: bool>() {
        let mask = vec![4000, 100, 4001, 200, 4002, 300, 4003, 4004];
        let data = vec![10, 20, 30];

        let encoded = encode_vector_mem_sec::<STABLE>(&data, &mask).unwrap();
        let expected = vec![4000, 10, 4001, 20, 4002, 30, 4003, 4004];
        assert_eq!(encoded, expected);

        let decoded = decode_vector_mem_sec::<STABLE>(&encoded, data.len()).unwrap();
        assert_eq!(decoded, data);
    }

    #[test]
    fn test_mem_sec_encode_decode_stable() {
        test_mem_sec_encode_decode::<true>();
    }

    #[test]
    fn test_mem_sec_encode_decode_unstable() {
        test_mem_sec_encode_decode::<false>();
    }

    #[test]
    fn e2e_randomized_pc_sec() {
        let mut rng = XorShift64::new(999);

        for _ in 0..100 {
            let mask_len = (rng.next_u16() % 128 + 10) as usize;
            let mask = generate_mask(&mut rng, mask_len, 30);

            let valid_slots = mask.iter().filter(|&&x| x < 3329).count();
            let data_len = if valid_slots > 0 {
                (rng.next_u16() as usize) % valid_slots
            } else {
                0
            };

            let data = generate_data(&mut rng, data_len);

            let encoded = encode_vector_pc_sec(&data, &mask).unwrap();
            let decoded = decode_vector_pc_sec(&encoded, data_len).unwrap();

            assert_eq!(decoded, data);
        }
    }

    fn e2e_randomized_mem_sec<const STABLE: bool>() {
        let mut rng = XorShift64::new(12345);

        for _ in 0..50 {
            let mask_len = (rng.next_u16() % 64 + 10) as usize;
            let mask = generate_mask(&mut rng, mask_len, 40);

            let valid_slots = mask.iter().filter(|&&x| x < 3329).count();
            let data_len = if valid_slots > 0 {
                (rng.next_u16() as usize) % valid_slots
            } else {
                0
            };

            let data = generate_data(&mut rng, data_len);

            let encoded = encode_vector_mem_sec::<STABLE>(&data, &mask).unwrap();
            let decoded = decode_vector_mem_sec::<STABLE>(&encoded, data_len).unwrap();
            assert_eq!(decoded, data);
        }
    }

    #[test]
    fn e2e_randomized_mem_sec_stable() {
        e2e_randomized_mem_sec::<true>();
    }

    #[test]
    fn e2e_randomized_mem_sec_unstable() {
        e2e_randomized_mem_sec::<false>();
    }

    #[test]
    fn e2e_mem_sec_stable_matches_pc_sec() {
        let mut rng = XorShift64::new(55555);

        for _ in 0..100 {
            let mask_len = (rng.next_u16() % 128 + 10) as usize;
            let mask = generate_mask(&mut rng, mask_len, 40);

            let valid_slots = mask.iter().filter(|&&x| x < 3329).count();
            let data_len = if valid_slots > 0 {
                (rng.next_u16() as usize) % valid_slots
            } else {
                0
            };

            let data = generate_data(&mut rng, data_len);

            let encoded_pc = encode_vector_pc_sec(&data, &mask).unwrap();
            let encoded_mem_stable = encode_vector_mem_sec::<true>(&data, &mask).unwrap();

            assert_eq!(encoded_pc, encoded_mem_stable);
        }
    }

    #[test]
    fn e2e_failure_conditions_pc_sec() {
        let mut rng = XorShift64::new(8888);

        for _ in 0..100 {
            let mask_len = (rng.next_u16() % 128 + 10) as usize;
            let mask = generate_mask(&mut rng, mask_len, 20);

            let valid_slots = mask.iter().filter(|&&x| x < 3329).count();
            let data_len = valid_slots + (rng.next_u16() as usize % 10) + 1;
            let data = generate_data(&mut rng, data_len);

            let encoded = encode_vector_pc_sec(&data, &mask);
            assert!(!bool::from(encoded.is_some()));

            let decoded = decode_vector_pc_sec(&mask, data_len);
            assert!(!bool::from(decoded.is_some()));
        }
    }

    fn e2e_failure_conditions_mem_sec<const STABLE: bool>() {
        let mut rng = XorShift64::new(8888);

        for _ in 0..100 {
            let mask_len = (rng.next_u16() % 128 + 10) as usize;
            let mask = generate_mask(&mut rng, mask_len, 20);

            let valid_slots = mask.iter().filter(|&&x| x < 3329).count();
            let data_len = valid_slots + (rng.next_u16() as usize % 10) + 1;
            let data = generate_data(&mut rng, data_len);

            let encoded = encode_vector_mem_sec::<STABLE>(&data, &mask);
            assert!(!bool::from(encoded.is_some()));

            let decoded = decode_vector_mem_sec::<STABLE>(&mask, data_len);
            assert!(!bool::from(decoded.is_some()));
        }
    }

    #[test]
    fn e2e_failure_conditions_mem_sec_stable() {
        e2e_failure_conditions_mem_sec::<true>();
    }

    #[test]
    fn e2e_failure_conditions_mem_sec_unstable() {
        e2e_failure_conditions_mem_sec::<false>();
    }
}
