# Inverse Rejection Sampling

Efficient constant-time algorithm for obfuscating finite-field vectors (e.g. ML-KEM).

## The Problem

Many post-quantum constructions (notably ML-KEM) work with vectors whose coefficients live in a prime field \(q = 3329\).  
When these coefficients are written as 12-bit integers they are *not* uniform: every value is strictly less than 3329, so the high bits are biased.

Traditional byte packing cannot hide this structure. The resulting bit-strings are trivially distinguishable from random, which prevents their use in protocols that require uniform-looking material (obfuscated key exchange, steganographic channels, anonymity networks, etc.).

## The Algorithm

**Inverse rejection sampling** is the dual of classical rejection sampling.

Classical rejection sampling produces a uniform sample from \{0, ..., q-1\} by drawing 12-bit integers and discarding those \(≥ q\).

Inverse rejection sampling does the opposite:

1. Start from a uniform sequence of 12-bit integers.
2. Replace the *valid* \(< q\) slots, in order, with the payload you wish to hide.
3. Leave the *invalid* \(≥ q\) slots untouched.

When encoding succeeds (i.e. the mask contains at least as many valid slots as the payload length), the resulting sequence is distributed uniformly across vectors of the mask's length with enough valid slots. The statistical distance from a true uniform binary sequence is therefore precisely the failure probability.

Decoding simply extracts the valid slots again.

## Constant-Time Realisations

Two security models are defined:

**Program-counter constant-time (PC-Sec)**  
Control flow never depends on secret data.  
Valid positions are overwritten by a constant-time select; the algorithm simply walks the mask once.

**Memory-pattern constant-time (Mem-Sec)**  
Both control flow *and* memory access patterns are independent of secrets.  
A data-oblivious Bitonic sorting network moves every valid element to the front of the array, the payload is written sequentially, and an unsort step restores the original positions.  
Stable and unstable variants exist; the stable variant is fully compatible with the PC-Sec output.

A critical correctness condition for the Mem-Sec sort is that the comparator must decide solely on the *validity bit* (\(< q\) versus \(≥ q\)).  
Ranking valid elements by their numeric value would bias which of them are overwritten and would create a detectable statistical artefact.

## Properties

- **Correctness** — encode followed by decode recovers the original payload whenever enough valid slots exist.
- **Distributional closeness** — a successful encoding is uniform over vectors that contain enough valid slots; the distinguishing advantage against a truly uniform binary stream is therefore equal to the failure probability.
- **Constant-time execution** under either the PC or the stronger Mem security model.
- **Compatibility** — the stable memory-secure encoding produces identical results to the program-counter encoding.
