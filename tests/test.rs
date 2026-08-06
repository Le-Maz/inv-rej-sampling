use std::fs;
use std::iter::repeat;

use inv_rej_sampling::*;

const N: usize = 1024;
const M: usize = 1536;
const PADDED_M: usize = 2048;
const PACKED_N: usize = N * 3 / 2;
const TRANSCRIPT_BYTES: usize = 8448;
const Q: u16 = 3329;

fn test_pack_msb_flag(val: u16) -> u16 {
    let is_lt = if val < Q { 1 } else { 0 };
    (val & 0x0FFF) | (is_lt << 15)
}

#[test]
fn test_against_c_test_vectors() {
    let content = fs::read_to_string("test_vectors.txt").expect("Failed to read test_vectors.txt");

    let mut current_n = 0;

    let mut data = None;
    let mut mask = None;
    let mut pc_status = None;
    let mut pc_output = None;
    let mut mem_status = None;

    for line in content.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }

        if let Some(val) = line.strip_prefix("N=") {
            current_n = val.parse().unwrap();
        } else if line.starts_with("TEST_ID=") {
            data = None;
            mask = None;
            pc_status = None;
            pc_output = None;
            mem_status = None;
        } else if let Some(val) = line.strip_prefix("DATA=") {
            data = Some(
                val.split(',')
                    .map(|s| s.parse::<u16>().unwrap())
                    .collect::<Vec<_>>(),
            );
        } else if let Some(val) = line.strip_prefix("MASK=") {
            mask = Some(
                val.split(',')
                    .map(|s| s.parse::<u16>().unwrap())
                    .collect::<Vec<_>>(),
            );
        } else if let Some(val) = line.strip_prefix("PC_SEC_STATUS=") {
            pc_status = Some(u32::from_str_radix(val.trim_start_matches("0x"), 16).unwrap());
        } else if let Some(val) = line.strip_prefix("PC_SEC_OUTPUT=") {
            pc_output = Some(
                val.split(',')
                    .map(|s| s.parse::<u16>().unwrap())
                    .collect::<Vec<_>>(),
            );
        } else if let Some(val) = line.strip_prefix("MEM_SEC_STATUS=") {
            mem_status = Some(u32::from_str_radix(val.trim_start_matches("0x"), 16).unwrap());
        } else if let Some(val) = line.strip_prefix("MEM_SEC_OUTPUT=") {
            let mem_output = val
                .split(',')
                .map(|s| s.parse::<u16>().unwrap())
                .collect::<Vec<_>>();

            if current_n == N {
                let d = data.as_ref().unwrap();
                let m = mask.as_ref().unwrap();

                let mut data_arr = [0u16; N];
                data_arr.copy_from_slice(d);

                let mut mask_arr = [0u16; M];
                mask_arr.copy_from_slice(m);

                let pc_opt = encode_vector_pc_sec(&data_arr, &mask_arr);
                let pc_ok = bool::from(pc_opt.is_some());
                let pc_out = pc_opt.as_inner_unchecked();

                assert_eq!(pc_ok, pc_status.unwrap() == 0xFFFFFFFF);
                assert_eq!(&pc_out[..], pc_output.as_ref().unwrap().as_slice());

                let mem_opt = encode_vector_mem_sec::<false>(&data_arr, &mask_arr);
                let mem_ok = bool::from(mem_opt.is_some());
                let mem_out = mem_opt.as_inner_unchecked();

                assert_eq!(mem_ok, mem_status.unwrap() == 0xFFFFFFFF);
                assert_eq!(&mem_out[..], mem_output.as_slice());
            }
        }
    }
}

#[test]
fn test_correctness() {
    let mut arr = [0u16; M];
    let mut original_arr = [0u16; M];
    for i in 0..M {
        let val = ((i * 37 + 5) % 4096) as u16;
        arr[i] = val;
        original_arr[i] = val;
    }

    let mut padded = Vec::with_capacity(PADDED_M);
    for &x in arr.iter() {
        padded.push(test_pack_msb_flag(x));
    }
    padded.extend(repeat(test_pack_msb_flag(4095)).take(PADDED_M - M));

    let mut transcript = vec![0u8; TRANSCRIPT_BYTES];
    sort_ct(&mut padded, &mut transcript);

    let mut last_key = true;
    let mut ok = true;
    for &x in padded.iter() {
        let key = (x >> 15) == 1;
        if !last_key && key {
            ok = false;
            break;
        }
        last_key = key;
    }
    assert!(ok, "sort correctness (monotonic key) failed");

    unsort_ct(&mut padded, &transcript);

    let mut unsort_ok = true;
    for i in 0..M {
        let orig = original_arr[i] & 0x0FFF;
        let current = padded[i] & 0x0FFF;
        if orig < Q {
            if orig != current {
                unsort_ok = false;
                break;
            }
        } else {
            if current < Q {
                unsort_ok = false;
                break;
            }
        }
    }
    assert!(
        unsort_ok,
        "unsort correctness (matches original pattern) failed"
    );
}

#[test]
fn test_does_not_sort_by_full_value() {
    let mut arr = [0u16; M];
    for i in 0..M {
        arr[i] = (3000 - i) as u16;
    }

    let mut padded = Vec::with_capacity(PADDED_M);
    for &x in arr.iter() {
        padded.push(test_pack_msb_flag(x));
    }
    padded.extend(repeat(test_pack_msb_flag(4095)).take(PADDED_M - M));

    let mut transcript = vec![0u8; TRANSCRIPT_BYTES];
    sort_ct(&mut padded, &mut transcript);

    let mut values = Vec::with_capacity(M);
    for i in 0..M {
        values.push(padded[i] & 0x0FFF);
    }

    let mut is_sorted = true;
    for i in 0..(M - 1) {
        if values[i] > values[i + 1] {
            is_sorted = false;
            break;
        }
    }

    assert!(
        !is_sorted,
        "Vulnerability detected: algorithm sorted by the full numeric value instead of the 1-bit validity predicate"
    );
}

#[test]
fn test_encode_decode_vector_pc_sec_e2e() {
    let mut data = [0u16; N];
    for i in 0..N {
        data[i] = (i * 11 % 3328) as u16;
    }

    let mut mask = [4000u16; M];
    for i in 0..(N + 50).min(M) {
        mask[i] = (i % 3328) as u16;
    }

    let enc_opt = encode_vector_pc_sec(&data, &mask);
    let enc_success = bool::from(enc_opt.is_some());
    let output = enc_opt.as_inner_unchecked();
    let ref_enc = reference::encode_vector_pc_sec(&data, &mask);

    assert_eq!(enc_success, bool::from(ref_enc.is_some()));
    if enc_success {
        assert_eq!(&output[..], ref_enc.unwrap().as_slice());
    }

    let dec_opt = decode_vector_pc_sec(&output, N);
    let dec_success = bool::from(dec_opt.is_some());
    let decoded_data = dec_opt.as_inner_unchecked();
    let ref_dec = reference::decode_vector_pc_sec(&output, N);

    assert_eq!(dec_success, bool::from(ref_dec.is_some()));
    if dec_success {
        assert_eq!(&decoded_data[..], ref_dec.unwrap().as_slice());
    }
}

#[test]
fn test_encode_decode_vector_mem_sec_e2e() {
    let mut data = [0u16; N];
    for i in 0..N {
        data[i] = (i * 11 % 3328) as u16;
    }

    let mut mask = [4000u16; M];
    for i in 0..(N + 50).min(M) {
        mask[i] = (i % 3328) as u16;
    }

    let enc_opt = encode_vector_mem_sec::<false>(&data, &mask);
    let enc_success = bool::from(enc_opt.is_some());
    let output = enc_opt.as_inner_unchecked();
    let ref_enc = reference::encode_vector_mem_sec::<false>(&data, &mask);

    assert_eq!(enc_success, bool::from(ref_enc.is_some()));
    if enc_success {
        assert_eq!(&output[..], ref_enc.unwrap().as_slice());
    }

    let dec_opt = decode_vector_mem_sec::<false>(&output, N);
    let dec_success = bool::from(dec_opt.is_some());
    let decoded_data = dec_opt.as_inner_unchecked();
    let ref_dec = reference::decode_vector_mem_sec::<false>(&output, N);

    assert_eq!(dec_success, bool::from(ref_dec.is_some()));
    if dec_success {
        assert_eq!(&decoded_data[..], ref_dec.unwrap().as_slice());
    }
}

#[test]
fn test_encode_vector_insufficient_mask_ct() {
    let data = [0u16; N];
    let mask = [4000u16; M];

    let enc_opt = encode_vector_mem_sec::<false>(&data, &mask);
    let enc_success = bool::from(enc_opt.is_some());
    let ref_enc = reference::encode_vector_mem_sec::<false>(&data, &mask);

    assert!(!enc_success);
    assert_eq!(enc_success, bool::from(ref_enc.is_some()));
}

#[test]
fn test_pack_unpack_data() {
    let mut data = [0u16; N];
    for i in 0..N {
        data[i] = (i * 13 % 4096) as u16;
    }

    let mut packed = [0u8; PACKED_N];
    pack_data(&data, &mut packed);

    let mut unpacked = [0u16; N];
    unpack_data(&packed, &mut unpacked);

    assert_eq!(data, unpacked, "Pack/Unpack failed to retain valid output");
}
