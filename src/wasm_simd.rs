use std::arch::wasm32::*;

#[target_feature(enable = "simd128")]
unsafe fn bitonic_cmpexch_vec8(
    arr: &mut [u16],
    left: usize,
    j: usize,
    dir: bool,
    transcript: &mut [u8],
    t_idx: &mut usize,
) {
    let ptr = arr.as_mut_ptr();
    let v = v128_load(ptr.add(left) as *const v128);
    let w = v128_load(ptr.add(left + j) as *const v128);

    let zero = i16x8_splat(0);
    let key_v = i16x8_gt(zero, v);
    let key_w = i16x8_gt(zero, w);

    let swap_mask = if dir {
        v128_andnot(key_w, key_v) // ~key_v & key_w
    } else {
        v128_andnot(key_v, key_w) // ~key_w & key_v
    };

    let mask8 = i16x8_bitmask(swap_mask) as u8;
    *transcript.get_unchecked_mut(*t_idx) = mask8;
    *t_idx += 1;

    let new_left = v128_bitselect(w, v, swap_mask);
    let new_right = v128_bitselect(v, w, swap_mask);

    v128_store(ptr.add(left) as *mut v128, new_left);
    v128_store(ptr.add(left + j) as *mut v128, new_right);
}

#[target_feature(enable = "simd128")]
unsafe fn bitonic_cmpexch_vec8_no_transcript(arr: &mut [u16], left: usize, j: usize, dir: bool) {
    let ptr = arr.as_mut_ptr();
    let v = v128_load(ptr.add(left) as *const v128);
    let w = v128_load(ptr.add(left + j) as *const v128);

    let zero = i16x8_splat(0);
    let key_v = i16x8_gt(zero, v);
    let key_w = i16x8_gt(zero, w);

    let swap_mask = if dir {
        v128_andnot(key_w, key_v)
    } else {
        v128_andnot(key_v, key_w)
    };

    let new_left = v128_bitselect(w, v, swap_mask);
    let new_right = v128_bitselect(v, w, swap_mask);

    v128_store(ptr.add(left) as *mut v128, new_left);
    v128_store(ptr.add(left + j) as *mut v128, new_right);
}

#[target_feature(enable = "simd128")]
pub(crate) unsafe fn stage_vec128_bitonic(
    arr: &mut [u16],
    k: usize,
    j: usize,
    transcript: &mut [u8],
    t_idx: &mut usize,
) {
    let n = arr.len();
    for i in (0..n).step_by(2 * j) {
        let dir = (i & k) == 0;
        for step in (0..j).step_by(8) {
            bitonic_cmpexch_vec8(arr, i + step, j, dir, transcript, t_idx);
        }
    }
}

#[target_feature(enable = "simd128")]
pub(crate) unsafe fn stage_vec128_bitonic_no_transcript(arr: &mut [u16], k: usize, j: usize) {
    let n = arr.len();
    for i in (0..n).step_by(2 * j) {
        let dir = (i & k) == 0;
        for step in (0..j).step_by(8) {
            bitonic_cmpexch_vec8_no_transcript(arr, i + step, j, dir);
        }
    }
}

#[target_feature(enable = "simd128")]
unsafe fn bitonic_cmpexch_inreg_vec8(
    arr: &mut [u16],
    left: usize,
    k: usize,
    j: usize,
) -> (v128, u8) {
    let ptr = arr.as_mut_ptr();
    let v = v128_load(ptr.add(left) as *const v128);

    let w = if j == 1 {
        i16x8_shuffle::<1, 0, 3, 2, 5, 4, 7, 6>(v, v)
    } else if j == 2 {
        u32x4_shuffle::<1, 0, 3, 2>(v, v)
    } else {
        u32x4_shuffle::<2, 3, 0, 1>(v, v)
    };

    let zero = i16x8_splat(0);
    let key_v = i16x8_gt(zero, v);
    let key_w = i16x8_gt(zero, w);

    let swap_if_dir = v128_andnot(key_w, key_v);

    let mut left_swap = if k >= 8 {
        if (left & k) == 0 {
            swap_if_dir
        } else {
            v128_andnot(key_v, key_w)
        }
    } else {
        let swap_if_not_dir = v128_andnot(key_v, key_w);
        let dir_mask = if k == 4 {
            i16x8(-1, -1, -1, -1, 0, 0, 0, 0)
        } else {
            i16x8(-1, -1, 0, 0, -1, -1, 0, 0)
        };
        v128_bitselect(swap_if_dir, swap_if_not_dir, dir_mask)
    };

    let left_mask = if j == 1 {
        i16x8(-1, 0, -1, 0, -1, 0, -1, 0)
    } else if j == 2 {
        i16x8(-1, -1, 0, 0, -1, -1, 0, 0)
    } else {
        i16x8(-1, -1, -1, -1, 0, 0, 0, 0)
    };
    left_swap = v128_and(left_swap, left_mask);

    let m = i16x8_bitmask(left_swap);
    let mask4 = match j {
        1 => ((m & 0x01) | ((m & 0x04) >> 1) | ((m & 0x10) >> 2) | ((m & 0x40) >> 3)) as u8,
        2 => ((m & 0x03) | ((m & 0x30) >> 2)) as u8,
        4 => (m & 0x0F) as u8,
        _ => std::hint::unreachable_unchecked(),
    };

    let right_swap = if j == 1 {
        i16x8_shuffle::<1, 0, 3, 2, 5, 4, 7, 6>(left_swap, left_swap)
    } else if j == 2 {
        u32x4_shuffle::<1, 0, 3, 2>(left_swap, left_swap)
    } else {
        u32x4_shuffle::<2, 3, 0, 1>(left_swap, left_swap)
    };

    let full_swap = v128_or(left_swap, right_swap);
    let new_v = v128_bitselect(w, v, full_swap);

    (new_v, mask4)
}

#[target_feature(enable = "simd128")]
pub(crate) unsafe fn stage_vec128_inreg_bitonic(
    arr: &mut [u16],
    k: usize,
    j: usize,
    transcript: &mut [u8],
    t_idx: &mut usize,
) {
    let n = arr.len();
    let ptr = arr.as_mut_ptr();
    for i in (0..n).step_by(16) {
        let (new_v0, mask_lo) = bitonic_cmpexch_inreg_vec8(arr, i, k, j);
        let (new_v1, mask_hi) = bitonic_cmpexch_inreg_vec8(arr, i + 8, k, j);

        v128_store(ptr.add(i) as *mut v128, new_v0);
        v128_store(ptr.add(i + 8) as *mut v128, new_v1);

        *transcript.get_unchecked_mut(*t_idx) = mask_lo | (mask_hi << 4);
        *t_idx += 1;
    }
}

#[target_feature(enable = "simd128")]
pub(crate) unsafe fn stage_vec128_inreg_bitonic_no_transcript(arr: &mut [u16], k: usize, j: usize) {
    let n = arr.len();
    let ptr = arr.as_mut_ptr();
    for i in (0..n).step_by(16) {
        let (new_v0, _) = bitonic_cmpexch_inreg_vec8(arr, i, k, j);
        let (new_v1, _) = bitonic_cmpexch_inreg_vec8(arr, i + 8, k, j);

        v128_store(ptr.add(i) as *mut v128, new_v0);
        v128_store(ptr.add(i + 8) as *mut v128, new_v1);
    }
}

#[target_feature(enable = "simd128")]
unsafe fn bitonic_cmpexch_vec8_undo(
    arr: &mut [u16],
    left: usize,
    j: usize,
    transcript: &[u8],
    t_idx: usize,
) {
    let ptr = arr.as_mut_ptr();
    let lo = v128_load(ptr.add(left) as *const v128);
    let hi = v128_load(ptr.add(left + j) as *const v128);

    let t_val = *transcript.get_unchecked(t_idx) as i16;
    let b = i16x8_splat(t_val);

    let bit_masks = i16x8(1, 2, 4, 8, 16, 32, 64, 128);
    let and_res = v128_and(b, bit_masks);
    let swap_mask = i16x8_gt(and_res, i16x8_splat(0));

    let new_lo = v128_bitselect(hi, lo, swap_mask);
    let new_hi = v128_bitselect(lo, hi, swap_mask);

    v128_store(ptr.add(left) as *mut v128, new_lo);
    v128_store(ptr.add(left + j) as *mut v128, new_hi);
}

#[target_feature(enable = "simd128")]
unsafe fn bitonic_inreg_undo_vec8(arr: &mut [u16], left: usize, j: usize, mask4: u8) {
    let ptr = arr.as_mut_ptr();
    let v = v128_load(ptr.add(left) as *const v128);

    let b = i16x8_splat(mask4 as i16);

    let bit_masks = if j == 1 {
        i16x8(1, 0, 2, 0, 4, 0, 8, 0)
    } else if j == 2 {
        i16x8(1, 2, 0, 0, 4, 8, 0, 0)
    } else {
        i16x8(1, 2, 4, 8, 0, 0, 0, 0)
    };

    let and_res = v128_and(b, bit_masks);
    let left_swap = i16x8_gt(and_res, i16x8_splat(0));

    let (w, right_swap) = if j == 1 {
        (
            i16x8_shuffle::<1, 0, 3, 2, 5, 4, 7, 6>(v, v),
            i16x8_shuffle::<1, 0, 3, 2, 5, 4, 7, 6>(left_swap, left_swap),
        )
    } else if j == 2 {
        (
            u32x4_shuffle::<1, 0, 3, 2>(v, v),
            u32x4_shuffle::<1, 0, 3, 2>(left_swap, left_swap),
        )
    } else {
        (
            u32x4_shuffle::<2, 3, 0, 1>(v, v),
            u32x4_shuffle::<2, 3, 0, 1>(left_swap, left_swap),
        )
    };

    let full_swap = v128_or(left_swap, right_swap);
    let new_v = v128_bitselect(w, v, full_swap);

    v128_store(ptr.add(left) as *mut v128, new_v);
}

#[target_feature(enable = "simd128")]
pub(crate) unsafe fn stage_vec128_inreg_bitonic_undo(
    arr: &mut [u16],
    j: usize,
    transcript: &[u8],
    base: usize,
) {
    let n = arr.len();
    let mut t_idx = base;
    for i in (0..n).step_by(16) {
        let byte_val = *transcript.get_unchecked(t_idx);
        let mask_lo = byte_val & 0x0F;
        let mask_hi = (byte_val >> 4) & 0x0F;

        bitonic_inreg_undo_vec8(arr, i, j, mask_lo);
        bitonic_inreg_undo_vec8(arr, i + 8, j, mask_hi);

        t_idx += 1;
    }
}

#[target_feature(enable = "simd128")]
pub(crate) unsafe fn stage_vec128_bitonic_undo(
    arr: &mut [u16],
    j: usize,
    transcript: &[u8],
    base: usize,
) {
    let n = arr.len();
    let mut t_idx = base;
    for i in (0..n).step_by(2 * j) {
        for step in (0..j).step_by(8) {
            bitonic_cmpexch_vec8_undo(arr, i + step, j, transcript, t_idx);
            t_idx += 1;
        }
    }
}

#[target_feature(enable = "simd128")]
pub(crate) unsafe fn pack_data_wasm(data: &[u16], packed: &mut [u8]) {
    use crate::MASK_12BIT;
    let chunks = data.len() / 8;
    for i in 0..chunks {
        let in_ptr = data.as_ptr().add(i * 8);
        let out_ptr = packed.as_mut_ptr().add(i * 12);

        let v = v128_load(in_ptr as *const v128);
        let mut temp = [0u16; 8];
        v128_store(temp.as_mut_ptr() as *mut v128, v);

        for j in 0..4 {
            let a = temp[j * 2] & MASK_12BIT;
            let b = temp[j * 2 + 1] & MASK_12BIT;
            *out_ptr.add(j * 3) = a as u8;
            *out_ptr.add(j * 3 + 1) = ((a >> 8) | (b << 4)) as u8;
            *out_ptr.add(j * 3 + 2) = (b >> 4) as u8;
        }
    }
}

#[target_feature(enable = "simd128")]
pub(crate) unsafe fn unpack_data_wasm(packed: &[u8], data: &mut [u16]) {
    let chunks = data.len() / 8;
    for i in 0..chunks {
        let in_ptr = packed.as_ptr().add(i * 12);
        let out_ptr = data.as_mut_ptr().add(i * 8);

        let mut temp = [0u16; 8];
        for j in 0..4 {
            let b0 = *in_ptr.add(j * 3) as u16;
            let b1 = *in_ptr.add(j * 3 + 1) as u16;
            let b2 = *in_ptr.add(j * 3 + 2) as u16;
            temp[j * 2] = b0 | ((b1 & 0x0F) << 8);
            temp[j * 2 + 1] = (b1 >> 4) | (b2 << 4);
        }

        let v = v128_load(temp.as_ptr() as *const v128);
        v128_store(out_ptr as *mut v128, v);
    }
}
