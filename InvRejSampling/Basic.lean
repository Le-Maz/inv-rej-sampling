/-- Computes the ceiling of the base-2 logarithm of a natural number. -/
def Nat.ceil_log2 (x : Nat) := if x ≤ 1 then 0 else (x-1).log2 + 1

theorem Nat.le_two_pow_ceil_log2 (x : Nat) : x ≤ 2^x.ceil_log2 := by
  simp [Nat.ceil_log2]
  have _ : (x - 1) < 2 ^ ((x - 1).log2 + 1) := Nat.lt_log2_self
  split <;> omega

namespace InvRejSampling

variable (q : Nat)

/-- Minimal binary representation for `Fin q` -/
abbrev Bin := BitVec q.ceil_log2
abbrev Bin.ofFin (x : Fin q) : Bin q :=
  ⟨x.toNat, calc
    _ < q := x.isLt
    _ ≤ 2^q.ceil_log2 := q.le_two_pow_ceil_log2⟩

def encode : List (Fin q) → List (Bin q) → Option (List (Bin q))
| [], rs => some rs
| _, [] => none
| x::xs', r::rs' => do
  if r.toNat < q then
    let y := Bin.ofFin q x
    let ys' ← encode xs' rs'
    return y::ys'
  else
    let ys' ← encode (x::xs') rs'
    return r::ys'

def decode : Nat → List (Bin q) → Option (List (Fin q))
| 0, _ => some []
| _, [] => none
| n'+1, y::ys' => do
  if hy : y.toNat < q then
    let x := ⟨y.toNat, hy⟩
    let xs' ← decode n' ys'
    return x::xs'
  else
    decode (n'+1) ys'

variable (xs : List (Fin q)) (rs : List (Bin q)) (ys : List (Bin q))

theorem decode_encode
    (h : encode q xs rs = some ys) :
    decode q xs.length ys = some xs := by
  induction rs generalizing xs ys with
  | nil =>
    match xs with
    | [] =>
      simp [encode] at h
      subst h
      simp [decode]
    | x :: xs' =>
      simp [encode] at h
  | cons r rs' ih =>
    match xs with
    | [] =>
      simp [encode] at h
      subst h
      simp [decode]
    | x :: xs' =>
      unfold encode at h
      split at h
      all_goals
        simp [Option.bind_eq_some_iff] at h
        obtain ⟨ys0, hys0, hyseq⟩ := h
        subst hyseq
        rename_i hr
        simp [decode]
      · simp [ih xs' ys0 hys0]
      · simp [hr]
        exact ih (x :: xs') ys0 hys0

end InvRejSampling
