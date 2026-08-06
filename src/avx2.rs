use std::arch::x86_64::*;

#[target_feature(enable = "avx2")]
unsafe fn bitonic_cmpexch_vec16(
    arr: &mut [u16],
    left: usize,
    j: usize,
    dir: bool,
    transcript: &mut [u8],
    t_idx: &mut usize,
) {
    let ptr = arr.as_mut_ptr();

    let v = _mm256_loadu_si256(ptr.add(left) as *const __m256i);
    let w = _mm256_loadu_si256(ptr.add(left + j) as *const __m256i);

    let zero = _mm256_setzero_si256();
    let key_v = _mm256_cmpgt_epi16(zero, v);
    let key_w = _mm256_cmpgt_epi16(zero, w);

    let swap_mask = if dir {
        _mm256_andnot_si256(key_v, key_w)
    } else {
        _mm256_andnot_si256(key_w, key_v)
    };

    let mask32 = _mm256_movemask_epi8(swap_mask) as u32;
    let mut m = mask32 & 0x55555555;
    m = (m | (m >> 1)) & 0x33333333;
    m = (m | (m >> 2)) & 0x0F0F0F0F;
    m = (m | (m >> 4)) & 0x00FF00FF;
    m = (m | (m >> 8)) & 0x0000FFFF;

    std::ptr::write_unaligned(transcript.as_mut_ptr().add(*t_idx) as *mut u16, m as u16);
    *t_idx += 2;

    let new_left = _mm256_blendv_epi8(v, w, swap_mask);
    let new_right = _mm256_blendv_epi8(w, v, swap_mask);

    _mm256_storeu_si256(ptr.add(left) as *mut __m256i, new_left);
    _mm256_storeu_si256(ptr.add(left + j) as *mut __m256i, new_right);
}

#[target_feature(enable = "avx2")]
unsafe fn bitonic_cmpexch_vec16_no_transcript(arr: &mut [u16], left: usize, j: usize, dir: bool) {
    let ptr = arr.as_mut_ptr();
    let v = _mm256_loadu_si256(ptr.add(left) as *const __m256i);
    let w = _mm256_loadu_si256(ptr.add(left + j) as *const __m256i);

    let zero = _mm256_setzero_si256();
    let key_v = _mm256_cmpgt_epi16(zero, v);
    let key_w = _mm256_cmpgt_epi16(zero, w);

    let swap_mask = if dir {
        _mm256_andnot_si256(key_v, key_w)
    } else {
        _mm256_andnot_si256(key_w, key_v)
    };

    let new_left = _mm256_blendv_epi8(v, w, swap_mask);
    let new_right = _mm256_blendv_epi8(w, v, swap_mask);

    _mm256_storeu_si256(ptr.add(left) as *mut __m256i, new_left);
    _mm256_storeu_si256(ptr.add(left + j) as *mut __m256i, new_right);
}

#[target_feature(enable = "avx2")]
pub(crate) unsafe fn stage_vec256_bitonic(
    arr: &mut [u16],
    k: usize,
    j: usize,
    transcript: &mut [u8],
    t_idx: &mut usize,
) {
    let n = arr.len();
    for i in (0..n).step_by(2 * j) {
        let dir = (i & k) == 0;
        for step in (0..j).step_by(16) {
            bitonic_cmpexch_vec16(arr, i + step, j, dir, transcript, t_idx);
        }
    }
}

#[target_feature(enable = "avx2")]
pub(crate) unsafe fn stage_vec256_bitonic_no_transcript(arr: &mut [u16], k: usize, j: usize) {
    let n = arr.len();
    for i in (0..n).step_by(2 * j) {
        let dir = (i & k) == 0;
        for step in (0..j).step_by(16) {
            bitonic_cmpexch_vec16_no_transcript(arr, i + step, j, dir);
        }
    }
}

#[target_feature(enable = "avx2")]
unsafe fn bitonic_cmpexch_vec8(
    arr: &mut [u16],
    left: usize,
    dir: bool,
    transcript: &mut [u8],
    t_idx: &mut usize,
) {
    let ptr = arr.as_mut_ptr();
    let v = _mm_loadu_si128(ptr.add(left) as *const __m128i);
    let w = _mm_loadu_si128(ptr.add(left + 8) as *const __m128i);

    let zero = _mm_setzero_si128();
    let key_v = _mm_cmpgt_epi16(zero, v);
    let key_w = _mm_cmpgt_epi16(zero, w);

    let swap_mask = if dir {
        _mm_andnot_si128(key_v, key_w)
    } else {
        _mm_andnot_si128(key_w, key_v)
    };

    let mask16 = _mm_movemask_epi8(swap_mask) as u32;
    let mut m = mask16 & 0x5555;
    m = (m | (m >> 1)) & 0x3333;
    m = (m | (m >> 2)) & 0x0F0F;
    m = (m | (m >> 4)) & 0x00FF;

    *transcript.get_unchecked_mut(*t_idx) = m as u8;
    *t_idx += 1;

    let new_left = _mm_blendv_epi8(v, w, swap_mask);
    let new_right = _mm_blendv_epi8(w, v, swap_mask);

    _mm_storeu_si128(ptr.add(left) as *mut __m128i, new_left);
    _mm_storeu_si128(ptr.add(left + 8) as *mut __m128i, new_right);
}

#[target_feature(enable = "avx2")]
unsafe fn bitonic_cmpexch_vec8_no_transcript(arr: &mut [u16], left: usize, dir: bool) {
    let ptr = arr.as_mut_ptr();
    let v = _mm_loadu_si128(ptr.add(left) as *const __m128i);
    let w = _mm_loadu_si128(ptr.add(left + 8) as *const __m128i);

    let zero = _mm_setzero_si128();
    let key_v = _mm_cmpgt_epi16(zero, v);
    let key_w = _mm_cmpgt_epi16(zero, w);

    let swap_mask = if dir {
        _mm_andnot_si128(key_v, key_w)
    } else {
        _mm_andnot_si128(key_w, key_v)
    };

    let new_left = _mm_blendv_epi8(v, w, swap_mask);
    let new_right = _mm_blendv_epi8(w, v, swap_mask);

    _mm_storeu_si128(ptr.add(left) as *mut __m128i, new_left);
    _mm_storeu_si128(ptr.add(left + 8) as *mut __m128i, new_right);
}

#[target_feature(enable = "avx2")]
pub(crate) unsafe fn stage_vec_k8_bitonic(
    arr: &mut [u16],
    k: usize,
    transcript: &mut [u8],
    t_idx: &mut usize,
) {
    let j = 8usize;
    let n = arr.len();
    for i in (0..n).step_by(2 * j) {
        let dir = (i & k) == 0;
        bitonic_cmpexch_vec8(arr, i, dir, transcript, t_idx);
    }
}

#[target_feature(enable = "avx2")]
pub(crate) unsafe fn stage_vec_k8_bitonic_no_transcript(arr: &mut [u16], k: usize) {
    let j = 8usize;
    let n = arr.len();
    for i in (0..n).step_by(2 * j) {
        let dir = (i & k) == 0;
        bitonic_cmpexch_vec8_no_transcript(arr, i, dir);
    }
}

#[target_feature(enable = "avx2")]
unsafe fn bitonic_cmpexch_inreg(
    arr: &mut [u16],
    left: usize,
    k: usize,
    j: usize,
    transcript: &mut [u8],
    t_idx: &mut usize,
) {
    let ptr = arr.as_mut_ptr();
    let v = _mm256_loadu_si256(ptr.add(left) as *const __m256i);

    let w = if j == 1 {
        let s1 = _mm256_shufflelo_epi16(v, 0xB1);
        _mm256_shufflehi_epi16(s1, 0xB1)
    } else if j == 2 {
        _mm256_shuffle_epi32(v, 0xB1)
    } else {
        _mm256_shuffle_epi32(v, 0x4E)
    };

    let zero = _mm256_setzero_si256();
    let key_v = _mm256_cmpgt_epi16(zero, v);
    let key_w = _mm256_cmpgt_epi16(zero, w);

    let swap_if_dir = _mm256_andnot_si256(key_v, key_w);

    let mut left_swap = if k >= 16 {
        if (left & k) == 0 {
            swap_if_dir
        } else {
            _mm256_andnot_si256(key_w, key_v)
        }
    } else {
        let swap_if_not_dir = _mm256_andnot_si256(key_w, key_v);
        let dir_mask = if k == 8 {
            _mm256_setr_epi16(-1, -1, -1, -1, -1, -1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0)
        } else if k == 4 {
            _mm256_setr_epi16(-1, -1, -1, -1, 0, 0, 0, 0, -1, -1, -1, -1, 0, 0, 0, 0)
        } else {
            _mm256_setr_epi16(-1, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0)
        };
        _mm256_blendv_epi8(swap_if_not_dir, swap_if_dir, dir_mask)
    };

    let left_mask = if j == 1 {
        _mm256_set1_epi32(0x0000FFFF)
    } else if j == 2 {
        _mm256_set1_epi64x(0x0000_0000_FFFF_FFFF_u64 as i64)
    } else {
        _mm256_setr_epi64x(-1, 0, -1, 0)
    };
    left_swap = _mm256_and_si256(left_swap, left_mask);

    let mask32 = _mm256_movemask_epi8(left_swap) as u32;
    let mask8 = match j {
        1 => {
            let mut m = mask32 & 0x11111111;
            m = (m | (m >> 3)) & 0x03030303;
            m = (m | (m >> 6)) & 0x0F0F0F0F;
            m = (m | (m >> 12)) & 0x000000FF;
            m as u8
        }
        2 => {
            let mut m = mask32 & 0x05050505;
            m = (m | (m >> 1)) & 0x03030303;
            m = (m | (m >> 6)) & 0x0F0F0F0F;
            m = (m | (m >> 12)) & 0x000000FF;
            m as u8
        }
        4 => {
            let mut m = mask32 & 0x00550055;
            m = (m | (m >> 1)) & 0x00330033;
            m = (m | (m >> 2)) & 0x000F000F;
            m = (m | (m >> 12)) & 0x000000FF;
            m as u8
        }
        _ => std::hint::unreachable_unchecked(),
    };

    *transcript.get_unchecked_mut(*t_idx) = mask8;
    *t_idx += 1;

    let right_swap = if j == 1 {
        let s1 = _mm256_shufflelo_epi16(left_swap, 0xB1);
        _mm256_shufflehi_epi16(s1, 0xB1)
    } else if j == 2 {
        _mm256_shuffle_epi32(left_swap, 0xB1)
    } else {
        _mm256_shuffle_epi32(left_swap, 0x4E)
    };

    let full_swap = _mm256_or_si256(left_swap, right_swap);
    let new_v = _mm256_blendv_epi8(v, w, full_swap);

    _mm256_storeu_si256(ptr.add(left) as *mut __m256i, new_v);
}

#[target_feature(enable = "avx2")]
unsafe fn bitonic_cmpexch_inreg_no_transcript(arr: &mut [u16], left: usize, k: usize, j: usize) {
    let ptr = arr.as_mut_ptr();
    let v = _mm256_loadu_si256(ptr.add(left) as *const __m256i);

    let w = if j == 1 {
        let s1 = _mm256_shufflelo_epi16(v, 0xB1);
        _mm256_shufflehi_epi16(s1, 0xB1)
    } else if j == 2 {
        _mm256_shuffle_epi32(v, 0xB1)
    } else {
        _mm256_shuffle_epi32(v, 0x4E)
    };

    let zero = _mm256_setzero_si256();
    let key_v = _mm256_cmpgt_epi16(zero, v);
    let key_w = _mm256_cmpgt_epi16(zero, w);

    let swap_if_dir = _mm256_andnot_si256(key_v, key_w);

    let mut left_swap = if k >= 16 {
        if (left & k) == 0 {
            swap_if_dir
        } else {
            _mm256_andnot_si256(key_w, key_v)
        }
    } else {
        let swap_if_not_dir = _mm256_andnot_si256(key_w, key_v);
        let dir_mask = if k == 8 {
            _mm256_setr_epi16(-1, -1, -1, -1, -1, -1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0)
        } else if k == 4 {
            _mm256_setr_epi16(-1, -1, -1, -1, 0, 0, 0, 0, -1, -1, -1, -1, 0, 0, 0, 0)
        } else {
            _mm256_setr_epi16(-1, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0)
        };
        _mm256_blendv_epi8(swap_if_not_dir, swap_if_dir, dir_mask)
    };

    let left_mask = if j == 1 {
        _mm256_set1_epi32(0x0000FFFF)
    } else if j == 2 {
        _mm256_set1_epi64x(0x0000_0000_FFFF_FFFF_u64 as i64)
    } else {
        _mm256_setr_epi64x(-1, 0, -1, 0)
    };
    left_swap = _mm256_and_si256(left_swap, left_mask);

    let right_swap = if j == 1 {
        let s1 = _mm256_shufflelo_epi16(left_swap, 0xB1);
        _mm256_shufflehi_epi16(s1, 0xB1)
    } else if j == 2 {
        _mm256_shuffle_epi32(left_swap, 0xB1)
    } else {
        _mm256_shuffle_epi32(left_swap, 0x4E)
    };

    let full_swap = _mm256_or_si256(left_swap, right_swap);
    let new_v = _mm256_blendv_epi8(v, w, full_swap);

    _mm256_storeu_si256(ptr.add(left) as *mut __m256i, new_v);
}

#[target_feature(enable = "avx2")]
pub(crate) unsafe fn stage_vec256_inreg_bitonic(
    arr: &mut [u16],
    k: usize,
    j: usize,
    transcript: &mut [u8],
    t_idx: &mut usize,
) {
    let n = arr.len();
    for i in (0..n).step_by(16) {
        bitonic_cmpexch_inreg(arr, i, k, j, transcript, t_idx);
    }
}

#[target_feature(enable = "avx2")]
pub(crate) unsafe fn stage_vec256_inreg_bitonic_no_transcript(arr: &mut [u16], k: usize, j: usize) {
    let n = arr.len();
    for i in (0..n).step_by(16) {
        bitonic_cmpexch_inreg_no_transcript(arr, i, k, j);
    }
}

#[target_feature(enable = "avx2")]
unsafe fn bitonic_cmpexch_vec16_undo(
    arr: &mut [u16],
    left: usize,
    j: usize,
    transcript: &[u8],
    t_idx: usize,
) {
    let ptr = arr.as_mut_ptr();
    let v = _mm256_loadu_si256(ptr.add(left) as *const __m256i);
    let w = _mm256_loadu_si256(ptr.add(left + j) as *const __m256i);

    let t_val = std::ptr::read_unaligned(transcript.as_ptr().add(t_idx) as *const i16);
    let b = _mm256_set1_epi16(t_val);

    let bit_masks = _mm256_set_epi16(
        1 << 15,
        1 << 14,
        1 << 13,
        1 << 12,
        1 << 11,
        1 << 10,
        1 << 9,
        1 << 8,
        1 << 7,
        1 << 6,
        1 << 5,
        1 << 4,
        1 << 3,
        1 << 2,
        1 << 1,
        1 << 0,
    );

    let and_res = _mm256_and_si256(b, bit_masks);
    let swap_mask = _mm256_cmpeq_epi16(and_res, bit_masks);

    let new_left = _mm256_blendv_epi8(v, w, swap_mask);
    let new_right = _mm256_blendv_epi8(w, v, swap_mask);

    _mm256_storeu_si256(ptr.add(left) as *mut __m256i, new_left);
    _mm256_storeu_si256(ptr.add(left + j) as *mut __m256i, new_right);
}

#[target_feature(enable = "avx2")]
unsafe fn bitonic_cmpexch_vec8_undo(arr: &mut [u16], left: usize, transcript: &[u8], t_idx: usize) {
    let ptr = arr.as_mut_ptr();
    let lo = _mm_loadu_si128(ptr.add(left) as *const __m128i);
    let hi = _mm_loadu_si128(ptr.add(left + 8) as *const __m128i);

    let t_val = *transcript.get_unchecked(t_idx) as i16;
    let b = _mm_set1_epi16(t_val);

    let bit_masks = _mm_set_epi16(
        1 << 7,
        1 << 6,
        1 << 5,
        1 << 4,
        1 << 3,
        1 << 2,
        1 << 1,
        1 << 0,
    );

    let and_res = _mm_and_si128(b, bit_masks);
    let swap_mask = _mm_cmpeq_epi16(and_res, bit_masks);

    let new_lo = _mm_blendv_epi8(lo, hi, swap_mask);
    let new_hi = _mm_blendv_epi8(hi, lo, swap_mask);

    _mm_storeu_si128(ptr.add(left) as *mut __m128i, new_lo);
    _mm_storeu_si128(ptr.add(left + 8) as *mut __m128i, new_hi);
}

#[target_feature(enable = "avx2")]
unsafe fn bitonic_inreg_undo(
    arr: &mut [u16],
    left: usize,
    j: usize,
    transcript: &[u8],
    t_idx: usize,
) {
    let ptr = arr.as_mut_ptr();
    let v = _mm256_loadu_si256(ptr.add(left) as *const __m256i);

    let byte_val = *transcript.get_unchecked(t_idx) as i16;
    let b = _mm256_set1_epi16(byte_val);

    let bit_masks = if j == 1 {
        _mm256_setr_epi16(1, 0, 2, 0, 4, 0, 8, 0, 16, 0, 32, 0, 64, 0, 128, 0)
    } else if j == 2 {
        _mm256_setr_epi16(1, 2, 0, 0, 4, 8, 0, 0, 16, 32, 0, 0, 64, 128, 0, 0)
    } else {
        _mm256_setr_epi16(1, 2, 4, 8, 0, 0, 0, 0, 16, 32, 64, 128, 0, 0, 0, 0)
    };

    let zero = _mm256_setzero_si256();
    let and_res = _mm256_and_si256(b, bit_masks);
    let left_swap = _mm256_cmpgt_epi16(and_res, zero);

    let (w, right_swap) = if j == 1 {
        let s1 = _mm256_shufflelo_epi16(v, 0xB1);
        let s2 = _mm256_shufflehi_epi16(s1, 0xB1);

        let rs1 = _mm256_shufflelo_epi16(left_swap, 0xB1);
        let rs2 = _mm256_shufflehi_epi16(rs1, 0xB1);
        (s2, rs2)
    } else if j == 2 {
        (
            _mm256_shuffle_epi32(v, 0xB1),
            _mm256_shuffle_epi32(left_swap, 0xB1),
        )
    } else {
        (
            _mm256_shuffle_epi32(v, 0x4E),
            _mm256_shuffle_epi32(left_swap, 0x4E),
        )
    };

    let full_swap = _mm256_or_si256(left_swap, right_swap);
    let new_v = _mm256_blendv_epi8(v, w, full_swap);

    _mm256_storeu_si256(ptr.add(left) as *mut __m256i, new_v);
}

#[target_feature(enable = "avx2")]
pub(crate) unsafe fn stage_vec256_inreg_bitonic_undo(
    arr: &mut [u16],
    j: usize,
    transcript: &[u8],
    base: usize,
) {
    let n = arr.len();
    let mut t_idx = base;
    for i in (0..n).step_by(16) {
        bitonic_inreg_undo(arr, i, j, transcript, t_idx);
        t_idx += 1;
    }
}

#[target_feature(enable = "avx2")]
pub(crate) unsafe fn stage_vec256_bitonic_undo(
    arr: &mut [u16],
    j: usize,
    transcript: &[u8],
    base: usize,
) {
    let n = arr.len();
    let mut t_idx = base;
    for i in (0..n).step_by(2 * j) {
        for step in (0..j).step_by(16) {
            bitonic_cmpexch_vec16_undo(arr, i + step, j, transcript, t_idx);
            t_idx += 2;
        }
    }
}

#[target_feature(enable = "avx2")]
pub(crate) unsafe fn stage_vec_k8_bitonic_undo(arr: &mut [u16], transcript: &[u8], base: usize) {
    let j = 8usize;
    let n = arr.len();
    let mut t_idx = base;
    for i in (0..n).step_by(2 * j) {
        bitonic_cmpexch_vec8_undo(arr, i, transcript, t_idx);
        t_idx += 1;
    }
}

#[target_feature(enable = "avx2")]
pub(crate) unsafe fn pack_data_avx2(data: &[u16], packed: &mut [u8]) {
    // Determine the number of chunks dynamically based on the input slice length
    let chunks = data.len() / 16;

    for i in 0..chunks {
        let in_ptr = data.as_ptr().add(i * 16);
        let out_ptr = packed.as_mut_ptr().add(i * 24);

        let v = _mm256_loadu_si256(in_ptr as *const __m256i);

        let mult = _mm256_set1_epi32(0x1000_0001);
        let madd = _mm256_madd_epi16(v, mult);

        let shuf_mask = _mm256_set_epi8(
            -1, -1, -1, -1, 14, 13, 12, 10, 9, 8, 6, 5, 4, 2, 1, 0, -1, -1, -1, -1, 14, 13, 12, 10,
            9, 8, 6, 5, 4, 2, 1, 0,
        );
        let shuf = _mm256_shuffle_epi8(madd, shuf_mask);

        let lane0 = _mm256_castsi256_si128(shuf);
        let lane1 = _mm256_extracti128_si256(shuf, 1);

        let mut temp0 = [0u8; 16];
        _mm_storeu_si128(temp0.as_mut_ptr() as *mut __m128i, lane0);
        std::ptr::copy_nonoverlapping(temp0.as_ptr(), out_ptr, 12);

        let mut temp1 = [0u8; 16];
        _mm_storeu_si128(temp1.as_mut_ptr() as *mut __m128i, lane1);
        std::ptr::copy_nonoverlapping(temp1.as_ptr(), out_ptr.add(12), 12);
    }
}

#[target_feature(enable = "avx2")]
pub(crate) unsafe fn unpack_data_avx2(packed: &[u8], data: &mut [u16]) {
    for i in 0..(data.len() / 16) {
        let in_ptr = packed.as_ptr().add(i * 24);
        let out_ptr = data.as_mut_ptr().add(i * 16);

        let lane0 = _mm_loadu_si128(in_ptr as *const __m128i);

        let mut temp = [0u8; 16];
        std::ptr::copy_nonoverlapping(in_ptr.add(12), temp.as_mut_ptr(), 12);
        let lane1 = _mm_loadu_si128(temp.as_ptr() as *const __m128i);

        let v = _mm256_setr_m128i(lane0, lane1);

        let shuf_mask = _mm256_set_epi8(
            11, 10, 10, 9, 8, 7, 7, 6, 5, 4, 4, 3, 2, 1, 1, 0, 11, 10, 10, 9, 8, 7, 7, 6, 5, 4, 4,
            3, 2, 1, 1, 0,
        );
        let shuf = _mm256_shuffle_epi8(v, shuf_mask);

        let mask0 = _mm256_set1_epi32(0x0000_0FFF);
        let word0 = _mm256_and_si256(shuf, mask0);

        let word1_shifted = _mm256_srli_epi32(shuf, 4);
        let mask1 = _mm256_set1_epi32(0x0FFF_0000);
        let word1 = _mm256_and_si256(word1_shifted, mask1);

        let combined = _mm256_or_si256(word0, word1);

        _mm256_storeu_si256(out_ptr as *mut __m256i, combined);
    }
}
