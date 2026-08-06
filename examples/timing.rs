use std::arch::x86_64::_rdtsc;
use std::hint::black_box;

use rand::rngs::Xoshiro128PlusPlus;
use rand::{Rng, SeedableRng};

const M: usize = 1024 + 512;
const N: usize = 1024;
const ITERATIONS: usize = 100_000;

fn welchs_t_test(samples_a: &[u64], samples_b: &[u64]) -> f64 {
    let n_a = samples_a.len() as f64;
    let n_b = samples_b.len() as f64;

    let mean_a = samples_a.iter().map(|&x| x as f64).sum::<f64>() / n_a;
    let mean_b = samples_b.iter().map(|&x| x as f64).sum::<f64>() / n_b;

    let var_a = samples_a
        .iter()
        .map(|&x| {
            let diff = (x as f64) - mean_a;
            diff * diff
        })
        .sum::<f64>()
        / (n_a - 1.0);

    let var_b = samples_b
        .iter()
        .map(|&x| {
            let diff = (x as f64) - mean_b;
            diff * diff
        })
        .sum::<f64>()
        / (n_b - 1.0);

    (mean_a - mean_b) / ((var_a / n_a) + (var_b / n_b)).sqrt()
}

#[inline(never)]
unsafe fn measure_cycles<F>(mut f: F) -> u64
where
    F: FnMut(),
{
    f();

    let start = unsafe { _rdtsc() };
    f();
    let end = unsafe { _rdtsc() };

    end - start
}

fn generate_inputs_class_a() -> ([u16; N], [u16; M]) {
    let data = [0u16; N];
    let mask = [0u16; M];
    (data, mask)
}

fn generate_inputs_class_b(prng: &mut Xoshiro128PlusPlus) -> ([u16; N], [u16; M]) {
    let mut data = [0u16; N];
    let mut mask = [0u16; M];

    for i in 0..N {
        data[i] = prng.next_u32() as u16 % 3328;
    }
    for i in 0..M {
        mask[i] = prng.next_u32() as u16 % 4096;
    }

    (data, mask)
}

fn test_encode_mem_sec_timing() {
    println!("Running t-test for encode_vector_mem_sec...");

    let mut prng = Xoshiro128PlusPlus::seed_from_u64(43);
    let mut timings_a = Vec::with_capacity(ITERATIONS);
    let mut timings_b = Vec::with_capacity(ITERATIONS);

    use inv_rej_sampling::encode_vector_mem_sec;

    for _ in 0..ITERATIONS {
        let (data_a, mask_a) = generate_inputs_class_a();
        let (data_b, mask_b) = generate_inputs_class_b(&mut prng);

        let cycles_a = unsafe {
            measure_cycles(|| {
                black_box(encode_vector_mem_sec::<false>(
                    black_box(&data_a),
                    black_box(&mask_a),
                ));
            })
        };

        let cycles_b = unsafe {
            measure_cycles(|| {
                black_box(encode_vector_mem_sec::<false>(
                    black_box(&data_b),
                    black_box(&mask_b),
                ));
            })
        };

        timings_a.push(cycles_a);
        timings_b.push(cycles_b);
    }

    let t_score = welchs_t_test(&timings_a, &timings_b);
    println!("encode_vector_mem_sec t-score: {:.5}", t_score);

    if t_score.abs() > 4.5 {
        println!(
            "WARNING: High t-score indicates potential timing leakage in encode_vector_mem_sec!"
        );
    } else {
        println!("encode_vector_mem_sec timing appears independent of data.");
    }
}

fn test_encode_pc_sec_timing() {
    println!("Running t-test for encode_vector_pc_sec...");

    let mut prng = Xoshiro128PlusPlus::seed_from_u64(44);
    let mut timings_a = Vec::with_capacity(ITERATIONS);
    let mut timings_b = Vec::with_capacity(ITERATIONS);

    use inv_rej_sampling::encode_vector_pc_sec;

    for _ in 0..ITERATIONS {
        let (data_a, mask_a) = generate_inputs_class_a();
        let (data_b, mask_b) = generate_inputs_class_b(&mut prng);

        let cycles_a = unsafe {
            measure_cycles(|| {
                black_box(encode_vector_pc_sec(black_box(&data_a), black_box(&mask_a)));
            })
        };

        let cycles_b = unsafe {
            measure_cycles(|| {
                black_box(encode_vector_pc_sec(black_box(&data_b), black_box(&mask_b)));
            })
        };

        timings_a.push(cycles_a);
        timings_b.push(cycles_b);
    }

    let t_score = welchs_t_test(&timings_a, &timings_b);
    println!("encode_vector_pc_sec t-score: {:.5}", t_score);

    if t_score.abs() > 4.5 {
        println!(
            "WARNING: High t-score indicates potential timing leakage in encode_vector_pc_sec!"
        );
    } else {
        println!("encode_vector_pc_sec timing appears independent of data.");
    }
}

fn test_decode_mem_sec_timing() {
    println!("Running t-test for decode_vector_mem_sec...");

    let mut prng = Xoshiro128PlusPlus::seed_from_u64(12346);
    let mut timings_a = Vec::with_capacity(ITERATIONS);
    let mut timings_b = Vec::with_capacity(ITERATIONS);

    use inv_rej_sampling::decode_vector_mem_sec;

    for _ in 0..ITERATIONS {
        let output_a = [0u16; M];
        let mut output_b = [0u16; M];

        for i in 0..M {
            output_b[i] = prng.next_u32() as u16 % 4096;
        }

        let cycles_a = unsafe {
            measure_cycles(|| {
                black_box(decode_vector_mem_sec::<false>(black_box(&output_a), N));
            })
        };

        let cycles_b = unsafe {
            measure_cycles(|| {
                black_box(decode_vector_mem_sec::<false>(black_box(&output_b), N));
            })
        };

        timings_a.push(cycles_a);
        timings_b.push(cycles_b);
    }

    let t_score = welchs_t_test(&timings_a, &timings_b);
    println!("decode_vector_mem_sec t-score: {:.5}", t_score);

    if t_score.abs() > 4.5 {
        println!(
            "WARNING: High t-score indicates potential timing leakage in decode_vector_mem_sec!"
        );
    } else {
        println!("decode_vector_mem_sec timing appears independent of data.");
    }
}

fn test_decode_pc_sec_timing() {
    println!("Running t-test for decode_vector_pc_sec...");

    let mut prng = Xoshiro128PlusPlus::seed_from_u64(12347);
    let mut timings_a = Vec::with_capacity(ITERATIONS);
    let mut timings_b = Vec::with_capacity(ITERATIONS);

    use inv_rej_sampling::decode_vector_pc_sec;

    for _ in 0..ITERATIONS {
        let output_a = [0u16; M];
        let mut output_b = [0u16; M];

        for i in 0..M {
            output_b[i] = prng.next_u32() as u16 % 4096;
        }

        let cycles_a = unsafe {
            measure_cycles(|| {
                black_box(decode_vector_pc_sec(black_box(&output_a), N));
            })
        };

        let cycles_b = unsafe {
            measure_cycles(|| {
                black_box(decode_vector_pc_sec(black_box(&output_b), N));
            })
        };

        timings_a.push(cycles_a);
        timings_b.push(cycles_b);
    }

    let t_score = welchs_t_test(&timings_a, &timings_b);
    println!("decode_vector_pc_sec t-score: {:.5}", t_score);

    if t_score.abs() > 4.5 {
        println!(
            "WARNING: High t-score indicates potential timing leakage in decode_vector_pc_sec!"
        );
    } else {
        println!("decode_vector_pc_sec timing appears independent of data.");
    }
}

fn main() {
    test_encode_mem_sec_timing();
    println!();
    test_encode_pc_sec_timing();
    println!();
    test_decode_mem_sec_timing();
    println!();
    test_decode_pc_sec_timing();
}
