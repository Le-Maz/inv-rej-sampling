use crate::MASK_12BIT;

#[inline(always)]
fn bitonic_compare_exchange_scalar_val(arr: &mut [u16], i: usize, j: usize, dir: bool) -> u8 {
    debug_assert!(i < arr.len() && j < arr.len());

    unsafe {
        let a = *arr.get_unchecked(i);
        let b = *arr.get_unchecked(j);

        let key_a = (a >> 15) & 1;
        let key_b = (b >> 15) & 1;

        let swap = if dir {
            (key_a ^ 1) & key_b
        } else {
            key_a & (key_b ^ 1)
        };

        let mask = 0u16.wrapping_sub(swap);
        *arr.get_unchecked_mut(i) = (a & !mask) | (b & mask);
        *arr.get_unchecked_mut(j) = (b & !mask) | (a & mask);

        swap as u8
    }
}

#[inline(always)]
fn bitonic_compare_exchange_scalar_no_transcript(arr: &mut [u16], i: usize, j: usize, dir: bool) {
    debug_assert!(i < arr.len() && j < arr.len());
    unsafe {
        let a = *arr.get_unchecked(i);
        let b = *arr.get_unchecked(j);

        let key_a = (a >> 15) & 1;
        let key_b = (b >> 15) & 1;

        let swap = if dir {
            (key_a ^ 1) & key_b
        } else {
            key_a & (key_b ^ 1)
        };

        let mask = 0u16.wrapping_sub(swap);
        *arr.get_unchecked_mut(i) = (a & !mask) | (b & mask);
        *arr.get_unchecked_mut(j) = (b & !mask) | (a & mask);
    }
}

pub(crate) fn stage_scalar_bitonic(
    arr: &mut [u16],
    k: usize,
    j: usize,
    transcript: &mut [u8],
    t_idx: &mut usize,
) {
    let n = arr.len();
    let mut current_byte = 0u8;
    let mut bit_count = 0;

    for i in (0..n).step_by(2 * j) {
        let dir = (i & k) == 0;
        for step in 0..j {
            let bit = bitonic_compare_exchange_scalar_val(arr, i + step, i + step + j, dir);
            current_byte |= bit << bit_count;
            bit_count += 1;

            if bit_count == 8 {
                transcript[*t_idx] = current_byte;
                *t_idx += 1;
                current_byte = 0;
                bit_count = 0;
            }
        }
    }
}

pub(crate) fn stage_scalar_bitonic_no_transcript(arr: &mut [u16], k: usize, j: usize) {
    let n = arr.len();
    for i in (0..n).step_by(2 * j) {
        let dir = (i & k) == 0;
        for step in 0..j {
            bitonic_compare_exchange_scalar_no_transcript(arr, i + step, i + step + j, dir);
        }
    }
}

#[inline(always)]
fn bitonic_compare_exchange_scalar_undo_bit(arr: &mut [u16], i: usize, j: usize, bit: u8) {
    debug_assert!(i < arr.len() && j < arr.len());
    let a = arr[i];
    let b = arr[j];

    let mask = 0u16.wrapping_sub(bit as u16);

    arr[i] = (a & !mask) | (b & mask);
    arr[j] = (b & !mask) | (a & mask);
}

pub(crate) fn stage_scalar_bitonic_undo(arr: &mut [u16], j: usize, transcript: &[u8], base: usize) {
    let n = arr.len();
    let mut t_idx = base;
    let mut current_byte = 0u8;
    let mut bit_count = 0;

    for i in (0..n).step_by(2 * j) {
        for step in 0..j {
            if bit_count == 0 {
                current_byte = transcript[t_idx];
                t_idx += 1;
            }

            let bit = (current_byte >> bit_count) & 1;
            bitonic_compare_exchange_scalar_undo_bit(arr, i + step, i + step + j, bit);

            bit_count = (bit_count + 1) & 7;
        }
    }
}

pub(crate) fn pack_data_portable(data: &[u16], packed: &mut [u8]) {
    for i in 0..(data.len() / 2) {
        let a = data[i * 2] & MASK_12BIT;
        let b = data[i * 2 + 1] & MASK_12BIT;
        packed[i * 3] = a as u8;
        packed[i * 3 + 1] = ((a >> 8) | (b << 4)) as u8;
        packed[i * 3 + 2] = (b >> 4) as u8;
    }
}

pub(crate) fn unpack_data_portable(packed: &[u8], data: &mut [u16]) {
    for i in 0..(data.len() / 2) {
        let b0 = packed[i * 3] as u16;
        let b1 = packed[i * 3 + 1] as u16;
        let b2 = packed[i * 3 + 2] as u16;
        data[i * 2] = b0 | ((b1 & 0x0F) << 8);
        data[i * 2 + 1] = (b1 >> 4) | (b2 << 4);
    }
}
