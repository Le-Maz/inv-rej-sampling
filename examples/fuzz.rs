use rand::{
    Rng, RngExt, SeedableRng,
    rngs::{ChaCha12Rng, ThreadRng},
};
use std::hint::black_box;

use inv_rej_sampling::{
    decode_vector_mem_sec, decode_vector_pc_sec, encode_vector_mem_sec, encode_vector_pc_sec,
    pack_data, unpack_data,
};

const ITERATIONS: usize = 100_000;

/// Fuzzes vector encoding, decoding, packing, and unpacking functions with random input parameters.
fn main() {
    let seed = ThreadRng::default().next_u64();
    println!(
        "Starting fuzzer ({} iterations, PRNG seed: {seed})...",
        ITERATIONS
    );

    let mut prng = ChaCha12Rng::seed_from_u64(seed);

    for iteration in 0..ITERATIONS {
        let n = prng.random_range(1..=64) * 16;
        let m = prng.random_range(n..=2048);
        let packed_n = n * 3 / 2;

        let mut data = vec![0u16; n];
        let mut mask = vec![0u16; m];

        // Generate valid data strictly within the target domain (< 3329)
        for i in 0..n {
            data[i] = prng.random_range(0..3329);
        }

        // Generate arbitrary mask data to fuzz entropy resilience
        let random_domain = prng.random_bool(0.5);
        for i in 0..m {
            mask[i] = if random_domain {
                prng.random_range(0..4096)
            } else {
                prng.random()
            };
        }

        // Fuzz program-counter constant-time variant
        let pc_enc_opt = encode_vector_pc_sec(black_box(&data), black_box(&mask));
        let pc_enc_ok = bool::from(pc_enc_opt.is_some());
        if pc_enc_ok {
            let pc_encoded = pc_enc_opt.unwrap();
            let pc_dec_opt = decode_vector_pc_sec(black_box(&pc_encoded), n);
            let pc_dec_ok = bool::from(pc_dec_opt.is_some());
            let pc_decoded = pc_dec_opt.unwrap();

            assert!(
                pc_dec_ok,
                "Iteration {iteration}: decode_vector_pc_sec failed on successfully encoded vector"
            );
            assert_eq!(
                data[..],
                pc_decoded[..],
                "Iteration {iteration}: decode_vector_pc_sec output mismatch"
            );
        }

        // Fuzz memory pattern constant-time variant
        let mem_enc_opt = encode_vector_mem_sec::<false>(black_box(&data), black_box(&mask));
        let mem_enc_ok = bool::from(mem_enc_opt.is_some());
        if mem_enc_ok {
            let mem_encoded = mem_enc_opt.unwrap();
            let mem_dec_opt = decode_vector_mem_sec::<false>(black_box(&mem_encoded), n);
            let mem_dec_ok = bool::from(mem_dec_opt.is_some());
            let mem_decoded = mem_dec_opt.unwrap();

            assert!(
                mem_dec_ok,
                "Iteration {iteration}: decode_vector_mem_sec failed on successfully encoded vector"
            );
            assert_eq!(
                data[..],
                mem_decoded[..],
                "Iteration {iteration}: decode_vector_mem_sec output mismatch"
            );
        }

        // Fuzz decoding functions directly against arbitrary garbage data to ensure resistance
        let mut arbitrary_encoded = vec![0u16; m];
        for i in 0..m {
            arbitrary_encoded[i] = prng.random();
        }
        let _ = decode_vector_pc_sec(black_box(&arbitrary_encoded), n);
        let _ = decode_vector_mem_sec::<false>(black_box(&arbitrary_encoded), n);

        // Fuzz packing and unpacking roundtrip
        let mut packed = vec![0u8; packed_n];
        let mut unpacked = vec![0u16; n];

        pack_data(black_box(&data), black_box(&mut packed));
        unpack_data(black_box(&packed), black_box(&mut unpacked));

        for i in 0..n {
            assert_eq!(
                data[i] & 0x0FFF,
                unpacked[i],
                "Iteration {iteration}: pack/unpack roundtrip mismatch at index {i}"
            );
        }
    }

    println!(
        "Fuzzing complete. All invariants satisfied across {} iterations.",
        ITERATIONS
    );
}
