#![allow(unsafe_op_in_unsafe_fn)]

use ctutils::{Choice, CtEq, CtLt, CtOption, CtSelect};
use std::iter::repeat;

/// The ML-KEM field modulus
pub const Q: i16 = 3329;
const MASK_12BIT: u16 = 0x0FFF;

/// Calculates the number of transcript bytes needed to pack bits for a bitonic sorting network of size `m`.
const fn transcript_bytes_count(m: usize) -> usize {
    if m == 0 {
        return 0;
    }
    let bits = (m / 2) * m.ilog2() as usize * (m.ilog2() as usize + 1) / 2;
    (bits + 7) / 8
}

/// Generates a sequence of stage offsets for a bitonic sort of a given padded length.
fn generate_stage_offsets(padded_m: usize) -> Vec<(usize, usize, usize)> {
    let mut stages = Vec::new();
    let mut offset = 0usize;
    let mut k = 2usize;

    while k <= padded_m {
        let mut j = k / 2;
        while j > 0 {
            stages.push((k, j, offset));
            offset += padded_m / 16;
            j /= 2;
        }
        k *= 2;
    }
    stages
}

#[inline(always)]
fn pack_msb_flag(val: u16) -> u16 {
    let trimmed = val & MASK_12BIT;
    let is_lt = trimmed.ct_lt(&(Q as u16));
    let is_lt_bit = is_lt.to_u16_mask() & 1;
    trimmed | (is_lt_bit << 15)
}

mod avx2;
mod portable;

pub fn sort_ct(arr: &mut [u16], transcript: &mut [u8]) {
    let has_avx2 = is_x86_feature_detected!("avx2");
    let mut t_idx = 0;
    let mut k = 2usize;
    let padded_m = arr.len();

    while k <= padded_m {
        let mut j = k / 2;
        while j > 0 {
            if j >= 16 && has_avx2 {
                unsafe { avx2::stage_vec256_bitonic(arr, k, j, transcript, &mut t_idx) };
            } else if j == 8 && has_avx2 {
                unsafe { avx2::stage_vec_k8_bitonic(arr, k, transcript, &mut t_idx) };
            } else if has_avx2 {
                unsafe { avx2::stage_vec256_inreg_bitonic(arr, k, j, transcript, &mut t_idx) };
            } else {
                portable::stage_scalar_bitonic(arr, k, j, transcript, &mut t_idx);
            }
            j /= 2;
        }
        k *= 2;
    }
}

pub fn sort_ct_no_transcript(arr: &mut [u16]) {
    let has_avx2 = is_x86_feature_detected!("avx2");
    let mut k = 2usize;
    let padded_m = arr.len();

    while k <= padded_m {
        let mut j = k / 2;
        while j > 0 {
            if j >= 16 && has_avx2 {
                unsafe { avx2::stage_vec256_bitonic_no_transcript(arr, k, j) };
            } else if j == 8 && has_avx2 {
                unsafe { avx2::stage_vec_k8_bitonic_no_transcript(arr, k) };
            } else if has_avx2 {
                unsafe { avx2::stage_vec256_inreg_bitonic_no_transcript(arr, k, j) };
            } else {
                portable::stage_scalar_bitonic_no_transcript(arr, k, j);
            }
            j /= 2;
        }
        k *= 2;
    }
}

pub fn unsort_ct(arr: &mut [u16], transcript: &[u8]) {
    let has_avx2 = is_x86_feature_detected!("avx2");
    let stages = generate_stage_offsets(arr.len());

    for &(_k, j, offset) in stages.iter().rev() {
        if j >= 16 && has_avx2 {
            unsafe { avx2::stage_vec256_bitonic_undo(arr, j, transcript, offset) };
        } else if j == 8 && has_avx2 {
            unsafe { avx2::stage_vec_k8_bitonic_undo(arr, transcript, offset) };
        } else if has_avx2 {
            unsafe { avx2::stage_vec256_inreg_bitonic_undo(arr, j, transcript, offset) };
        } else {
            portable::stage_scalar_bitonic_undo(arr, j, transcript, offset);
        }
    }
}

/// Program-counter model constant-time vector encoding.
///
/// Conditionally places elements from `data` into `mask` positions where the mask item is valid (`< 3329`).
/// Returns a `CtOption` indicating whether all `data` elements were successfully encoded.
pub fn encode_vector_pc_sec(data: &[u16], mask: &[u16]) -> CtOption<Vec<u16>> {
    let mut output = vec![0u16; mask.len()];
    if data.is_empty() {
        output.clone_from_slice(mask);
        return CtOption::new(output, Choice::TRUE);
    }

    let mut data_cur = 0usize;
    let data_last = data.len() - 1;

    for (r, &e) in output.iter_mut().zip(mask.iter()) {
        let e_trim = e & MASK_12BIT;
        let is_candidate = e_trim.ct_lt(&(Q as u16));

        let valid_cursor = data_cur.ct_lt(&data.len());
        let safe_cursor = data_last.ct_select(&data_cur, valid_cursor);

        let data_val = data[safe_cursor];
        let should_replace = is_candidate & valid_cursor;

        *r = e_trim.ct_select(&data_val, should_replace);

        let data_cursor_inc = data_cur + 1;
        data_cur = data_cur.ct_select(&data_cursor_inc, should_replace);
    }

    let success = data_cur.ct_eq(&data.len());
    CtOption::new(output, success)
}

/// Program-counter model constant-time vector decoding.
///
/// Extracts valid elements (`< 3329`) sequentially from `output` to reconstruct the original data vector.
/// Returns a `CtOption` indicating whether enough valid elements were found.
pub fn decode_vector_pc_sec(output: &[u16], data_len: usize) -> CtOption<Vec<u16>> {
    let mut result = vec![0u16; data_len];
    if data_len == 0 {
        return CtOption::new(result, Choice::TRUE);
    }

    let mut data_cur = 0usize;
    let data_last = data_len - 1;

    for &e in output {
        let is_candidate = e.ct_lt(&(Q as u16));

        let valid_cursor = data_cur.ct_lt(&data_len);
        let safe_cursor = data_last.ct_select(&data_cur, valid_cursor);

        let current_val = result[safe_cursor];

        let should_update = is_candidate & valid_cursor;
        result[safe_cursor] = current_val.ct_select(&e, should_update);

        let data_cursor_inc = data_cur + 1;
        data_cur = data_cur.ct_select(&data_cursor_inc, should_update);
    }

    let success = data_cur.ct_eq(&data_len);
    CtOption::new(result, success)
}

/// Memory pattern model constant-time vector encoding free of cache attacks.
///
/// Relies on data-oblivious sorting to move valid mask elements to the front, overwriting them sequentially, and unsorting to route them back to their original positions.
/// Pads the internal array to a power of two with 4095.
pub fn encode_vector_mem_sec<const STABLE: bool>(data: &[u16], mask: &[u16]) -> CtOption<Vec<u16>> {
    if STABLE {
        todo!()
    }

    let mut output = vec![0u16; mask.len()];
    if data.is_empty() {
        output.clone_from_slice(mask);
        return CtOption::new(output, Choice::TRUE);
    }
    if mask.len() < data.len() {
        output.clone_from_slice(mask);
        return CtOption::new(output, Choice::FALSE);
    }

    let padded_len = mask.len().next_power_of_two();
    let mut arr = Vec::with_capacity(padded_len);
    let mut transcript = vec![0u8; transcript_bytes_count(padded_len)];

    for &m in mask {
        arr.push(pack_msb_flag(m));
    }
    arr.extend(repeat(pack_msb_flag(4095)).take(padded_len - mask.len()));

    sort_ct(&mut arr, &mut transcript);

    let success_bit = (arr[data.len() - 1] >> 15) & 1;
    let success = Choice::from(success_bit as u8);

    for i in 0..data.len() {
        let mask_item = arr[i];
        let data_item = pack_msb_flag(data[i]);

        let use_data = (mask_item >> 15) & 1;
        let use_data_mask = 0u16.wrapping_sub(use_data);

        arr[i] = (mask_item & !use_data_mask) | (data_item & use_data_mask);
    }

    unsort_ct(&mut arr, &transcript);

    for i in 0..mask.len() {
        output[i] = arr[i] & MASK_12BIT;
    }

    CtOption::new(output, success)
}

/// Memory pattern model constant-time vector decoding.
///
/// Reconstructs the dense array by moving valid elements to the front using a bitonic sort, avoiding timing and memory-pattern leakage.
pub fn decode_vector_mem_sec<const STABLE: bool>(
    output: &[u16],
    data_len: usize,
) -> CtOption<Vec<u16>> {
    if STABLE {
        todo!()
    }

    let mut data = vec![0u16; data_len];
    if data_len == 0 {
        return CtOption::new(data, Choice::TRUE);
    }
    if output.len() < data_len {
        return CtOption::new(data, Choice::FALSE);
    }

    let padded_len = output.len().next_power_of_two();
    let mut arr = Vec::with_capacity(padded_len);

    for &o in output {
        arr.push(pack_msb_flag(o));
    }
    arr.extend(repeat(pack_msb_flag(4095)).take(padded_len - output.len()));

    sort_ct_no_transcript(&mut arr);

    let success_bit = (arr[data_len - 1] >> 15) & 1;
    let success = Choice::from(success_bit as u8);

    for (out_item, &arr_item) in data.iter_mut().zip(arr[..data_len].iter()) {
        let is_valid = (arr_item >> 15) & 1;
        let is_valid_mask = 0u16.wrapping_sub(is_valid);
        *out_item = (arr_item & MASK_12BIT) & is_valid_mask;
    }

    CtOption::new(data, success)
}

pub fn pack_data(data: &[u16], packed: &mut [u8]) {
    if is_x86_feature_detected!("avx2") {
        unsafe { avx2::pack_data_avx2(data, packed) };
    } else {
        portable::pack_data_portable(data, packed);
    }
}

pub fn unpack_data(packed: &[u8], data: &mut [u16]) {
    if is_x86_feature_detected!("avx2") {
        unsafe { avx2::unpack_data_avx2(packed, data) };
    } else {
        portable::unpack_data_portable(packed, data);
    }
}
