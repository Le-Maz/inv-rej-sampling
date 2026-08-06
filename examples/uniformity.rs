use rand::{
    Rng, RngExt, SeedableRng,
    rngs::{ChaCha12Rng, ThreadRng},
};

use inv_rej_sampling::{encode_vector_mem_sec, encode_vector_pc_sec};

const M: usize = 1536;
const N: usize = 1024;
const BINS: usize = 4096;
const ITERATIONS: usize = 100_000;

/// Computes the Chi-Square statistic for a given array of observed frequencies.
fn chi_square_test(observed: &[usize; BINS], expected: f64) -> f64 {
    let mut chi_square = 0.0;
    for &obs in observed.iter() {
        let diff = (obs as f64) - expected;
        chi_square += (diff * diff) / expected;
    }
    chi_square
}

fn main() {
    let seed = ThreadRng::default().next_u64();
    println!("PRNG seed: {seed}");

    // Normally seeding with u64 is a bad thing, here it's just
    // a convenience for testing reproducibility so it's fine
    let mut prng = ChaCha12Rng::seed_from_u64(seed);

    println!("Running Chi-Square uniformity tests...");

    let mut observed_pc = [0usize; BINS];
    let mut observed_mem = [0usize; BINS];

    let mut successful_pc = 0;
    let mut successful_mem = 0;

    for _ in 0..ITERATIONS {
        let mut data = [0u16; N];
        let mut mask = [0u16; M];

        // Synthesize uniform data and mask arrays
        for i in 0..N {
            data[i] = prng.random_range(0..3329);
        }
        for i in 0..M {
            mask[i] = prng.random_range(0..4096);
        }

        let out_pc_opt = encode_vector_pc_sec(&data, &mask);
        if bool::from(out_pc_opt.is_some()) {
            successful_pc += 1;
            let out_pc = out_pc_opt.unwrap();
            for &val in out_pc.iter() {
                observed_pc[(val & 0x0FFF) as usize] += 1;
            }
        }

        let out_mem_opt = encode_vector_mem_sec::<false>(&data, &mask);
        if bool::from(out_mem_opt.is_some()) {
            successful_mem += 1;
            let out_mem = out_mem_opt.unwrap();
            for &val in out_mem.iter() {
                observed_mem[(val & 0x0FFF) as usize] += 1;
            }
        }
    }

    let expected_pc = (successful_pc * M) as f64 / (BINS as f64);
    let expected_mem = (successful_mem * M) as f64 / (BINS as f64);

    let chi_pc = chi_square_test(&observed_pc, expected_pc);
    let chi_mem = chi_square_test(&observed_mem, expected_mem);

    let df = BINS - 1;

    // For large degrees of freedom, the mean of the Chi-Square distribution is roughly `df`
    // and the standard deviation is `sqrt(2 * df)`.
    println!("Degrees of freedom (df): {}", df);
    println!("Expected mean approx: {}", df);
    println!("--------------------------------------------------");

    println!(
        "encode_vector_pc_sec  Chi-Square: {:.2} (Success rate: {}/{})",
        chi_pc, successful_pc, ITERATIONS
    );
    println!(
        "encode_vector_mem_sec Chi-Square: {:.2} (Success rate: {}/{})",
        chi_mem, successful_mem, ITERATIONS
    );
}
