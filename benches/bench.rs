#![feature(test)]

extern crate test;

use inv_rej_sampling::*;
use test::Bencher;

const N: usize = 1024;
const M: usize = 1536;
const PACKED_N: usize = N * 3 / 2;

#[bench]
fn bench_encode_vector_pc_sec(b: &mut Bencher) {
    let data = [100u16; N];
    let mut entropy = [0u16; M];
    for i in 0..M {
        entropy[i] = ((i * 37 + 5) % 4096) as u16;
    }

    b.bytes = N as u64 * 3 / 2;
    b.iter(|| {
        let res = encode_vector_pc_sec(&data, &entropy);
        test::black_box(res);
    });
}

#[bench]
fn bench_decode_vector_pc_sec(b: &mut Bencher) {
    let mut encoded = [0u16; M];
    for i in 0..M {
        encoded[i] = ((i * 37 + 5) % 4096) as u16;
    }

    b.bytes = N as u64 * 3 / 2;
    b.iter(|| {
        let res = decode_vector_pc_sec(&encoded, N);
        test::black_box(res);
    });
}

#[bench]
fn bench_encode_vector_mem_sec(b: &mut Bencher) {
    let data = [100u16; N];
    let mut mask = [0u16; M];
    for i in 0..M {
        mask[i] = ((i * 37 + 5) % 4096) as u16;
    }

    b.bytes = N as u64 * 3 / 2;
    b.iter(|| {
        let res = encode_vector_mem_sec::<false>(&data, &mask);
        test::black_box(res);
    });
}

#[bench]
fn bench_decode_vector_mem_sec(b: &mut Bencher) {
    let mut output = [0u16; M];
    for i in 0..M {
        output[i] = ((i * 37 + 5) % 4096) as u16;
    }

    b.bytes = N as u64 * 3 / 2;
    b.iter(|| {
        let res = decode_vector_mem_sec::<false>(&output, N);
        test::black_box(res);
    });
}

#[bench]
fn bench_pack_data(b: &mut Bencher) {
    let data = [100u16; N];
    let mut packed = [0u8; PACKED_N];

    b.bytes = N as u64 * 3 / 2;
    b.iter(|| {
        pack_data(&data, &mut packed);
        test::black_box(&mut packed);
    });
}

#[bench]
fn bench_unpack_data(b: &mut Bencher) {
    let packed = [100u8; PACKED_N];
    let mut data = [0u16; N];

    b.bytes = N as u64 * 3 / 2;
    b.iter(|| {
        unpack_data(&packed, &mut data);
        test::black_box(&mut data);
    });
}
