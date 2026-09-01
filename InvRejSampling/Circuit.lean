structure Array.Drain (α : Type u) where
  array : Array α
  current : Nat

def Array.drain {α} (arr : Array α) : Array.Drain α := ⟨arr, 0⟩

instance (α : Type u) : Inhabited (Array.Drain α) where
  default := ⟨#[], 0⟩

def Array.Drain.isEmpty {α} (t : Array.Drain α) : Bool := t.array.size ≤ t.current
def Array.Drain.next {α} (t : Array.Drain α) (h : ¬t.isEmpty) : α × Array.Drain α :=
  have _ : t.current < t.array.size := by
    simpa [isEmpty] using h
  (t.array[t.current], { t with current := t.current + 1 })

def Nat.bitWidth (n : Nat) : Nat :=
  if n ≤ 1 then 0 else Nat.log2 (n - 1) + 1

/--
Represents a logic gate in a boolean circuit.
A gate can be a constant boolean value, a NAND gate, or an invocation of a subcircuit.
-/
inductive Gate
| const (val : Bool)
| nand  (a b : Nat)
| invoke (cIdx : Nat) (args : Array Nat)

/--
A partial circuit representing a collection of gates and nested subcircuit references.
It may potentially contain cyclic references.
-/
structure PartialCircuit where
  /-- Array of referenced subcircuits. -/
  refs    : Array PartialCircuit
  /-- Array of gates making up this circuit layer. -/
  gates   : Array Gate
  /-- Array of input wire indices. -/
  inputs  : Array Nat
  /-- Array of output wire indices. -/
  outputs : Array Nat

/--
Checks if the partial circuit has a maximum reference depth bounded by `u`.
A depth of 0 means the circuit has no subcircuit references.
-/
def PartialCircuit.hasDepth (u : Nat) (c : PartialCircuit) : Bool :=
  match u with
  | 0 => c.refs.isEmpty
  | u + 1 => c.hasDepth u || c.refs.all (PartialCircuit.hasDepth u)

/--
Proves that if a partial circuit has depth `a`,
it is also considered to have any depth `b` where `a ≤ b`.
-/
theorem PartialCircuit.hasDepth_mono {c : PartialCircuit} {a b : Nat} (hle : a ≤ b) (ha : c.hasDepth a = true) : c.hasDepth b = true := by
  induction hle with
  | refl => exact ha
  | step _ ih =>
    unfold PartialCircuit.hasDepth
    simp_all

/--
Calculates the evaluation cost (gate count) of a partial circuit up to a maximum depth `u`.
Constants and NAND gates cost 1. Invocations add the cost of the referenced subcircuit,
or cost 1 if the reference index is out of bounds.
-/
def PartialCircuit.cost : Nat → PartialCircuit → Nat
| 0, c => c.gates.size
| u + 1, c =>
  let refs := c.refs.map (PartialCircuit.cost u)
  c.gates.foldl (fun acc g => acc +
    match g with
    | Gate.invoke cIdx _ => refs[cIdx]?.getD 0
    | _ => 1
  ) 0

/--
A well-formed circuit that is guaranteed to have a finite reference depth.
This prevents infinite cyclic subcircuit invocations.
-/
def Circuit := { c : PartialCircuit // ∃ u : Nat, c.hasDepth u }

namespace Circuit

/--
Calculates the minimal reference depth of a well-formed circuit.
Performs a linear search starting from 0, proven to terminate because
the `Circuit` type guarantees the existence of a finite depth.
-/
def depth (c : Circuit) :=
  let rec search (c : Circuit) (n : Nat) : Nat :=
    if hn : c.val.hasDepth n then n else search c (n + 1)
  termination_by c.property.choose - n
  decreasing_by
    have hk := c.property.choose_spec
    generalize c.property.choose = k at hk ⊢
    have h_not_le : ¬(k ≤ n) := by
      intro hle
      refine hn ?_
      exact PartialCircuit.hasDepth_mono hle hk
    omega
  search c 0

theorem depth.search_ge (c : Circuit) (n : Nat) : Circuit.depth.search c n ≥ n := by
  unfold search
  split <;> simp
  calc
    _ ≤ n + 1 := by simp
    _ ≤ _ := search_ge c (n+1)
termination_by c.property.choose - n
decreasing_by
  have hk := c.property.choose_spec
  generalize c.property.choose = k at hk ⊢
  have h_not_le : ¬(k ≤ n) := by
    intro hle
    have := PartialCircuit.hasDepth_mono hle hk
    contradiction
  omega

theorem depth_spec (c : Circuit) :
    c.val.hasDepth c.depth = true ∧ ∀ k < c.depth, c.val.hasDepth k = false := by
  unfold Circuit.depth
  let rec go (n : Nat) (h_false : ∀ k < n, c.val.hasDepth k = false) :
      c.val.hasDepth (Circuit.depth.search c n) = true ∧
      ∀ k < Circuit.depth.search c n, c.val.hasDepth k = false := by
    unfold Circuit.depth.search
    split
    · next hn =>
      exact ⟨hn, fun k hk => by
        have : k < n := by omega
        exact h_false k this⟩
    · next hn =>
      have hn_false : c.val.hasDepth n = false := by
        cases h_eq : c.val.hasDepth n
        · rfl
        · rw [h_eq] at hn; contradiction
      apply go (n + 1)
      intro k hk
      if hk_eq : k = n then
        subst hk_eq
        exact hn_false
      else
        have : k < n := by omega
        exact h_false k this
  termination_by c.property.choose - n
  decreasing_by
    have hk := c.property.choose_spec
    generalize c.property.choose = k at hk ⊢
    have h_not_le : ¬(k ≤ n) := by
      intro hle
      have := PartialCircuit.hasDepth_mono hle hk
      contradiction
    omega
  exact go 0 (by intro k hk; contradiction)

/--
Calculates the total evaluation cost of a well-formed circuit by evaluating
its partial circuit cost at its exact minimal depth.
-/
def cost (c : Circuit) : Nat :=
  PartialCircuit.cost c.depth c.val

/--
Extracts the referenced subcircuits of a well-formed circuit
into an array of well-formed circuits.
-/
def subcircuits (c : Circuit) : Array Circuit :=
  c.val.refs.attach.map fun ⟨ref, h_mem⟩ => by
    refine ⟨ref, ?_⟩
    obtain ⟨u, hu⟩ := c.property
    induction u with
    | zero =>
      unfold PartialCircuit.hasDepth at hu
      revert h_mem hu
      match c.val.refs with
      | ⟨[]⟩ =>
        intro h_mem _
        simp at h_mem
      | ⟨_::_⟩ =>
        intro _ hu
        revert hu
        simp
    | succ u ih =>
      unfold PartialCircuit.hasDepth at hu
      simp only [Bool.or_eq_true] at hu
      cases hu with
      | inl h =>
        exact ih h
      | inr h =>
        refine ⟨u, ?_⟩
        exact Array.all_eq_true_iff_forall_mem.mp h ref h_mem

structure State where
  circuits  : Array Circuit
  gates     : Array Gate
  outputs   : Array Nat
  current   : Fin (gates.size + 1)
  replacer  : Array.Drain Bool

def stateDepth (st : State) := st.circuits.map (fun c => c.depth + 1) |>.max? |>.getD 0

def terminationMeasure (st : State) : Nat × Nat := (stateDepth st, st.gates.size - st.current.val)

def stageEval (c : Circuit) (inputs : Array Bool) : State :=
  let gates := (c.val.inputs.zip inputs).foldl (fun gs (idx, val) =>
    gs.setIfInBounds idx (.const val)
  ) c.val.gates
  { circuits  := c.subcircuits
    gates     := gates
    outputs   := c.val.outputs
    current   := ⟨0, Nat.zero_lt_succ _⟩
    replacer  := default }

theorem stageEval_stateDepth (c : Circuit) (inputs : Array Bool) :
    stateDepth (c.stageEval inputs) = c.depth := by
  simp [stateDepth, stageEval]
  clear inputs
  match h : c.depth with
  | 0 =>
    simp [Circuit.depth] at h
    unfold Circuit.depth.search at h
    have := Circuit.depth.search_ge c 1
    simp [Nat.le_iff_lt_add_one] at this
    simp [PartialCircuit.hasDepth, Nat.ne_of_lt' this] at h
    have : (Array.map (fun c ↦ c.depth + 1) c.subcircuits).max? = none := by
      simp [Circuit.subcircuits, h]
    rw [this]
    exact Option.getD_none
  | d + 1 =>
    have := Circuit.depth_spec c
    rw [h] at this
    rcases this with ⟨h_true, h_false⟩
    have hd_false := h_false d (Nat.lt_succ_self d)
    unfold PartialCircuit.hasDepth at h_true
    simp only [hd_false, Bool.false_or] at h_true
    have hrefs_not_empty : c.val.refs.isEmpty = false := by
      have h0 := h_false 0 (by omega)
      exact h0
    have hsub_not_empty : c.subcircuits.isEmpty = false := by
      simp at hrefs_not_empty
      simp [Circuit.subcircuits, hrefs_not_empty]
    have : Array.map (fun c ↦ c.depth + 1) c.subcircuits ≠ #[] := by simp; simp [← Array.isEmpty_iff, hsub_not_empty]
    simp [Array.max?, this]
    apply Nat.le_antisymm
    · simp only [Array.max_le_iff]
      intro x hx
      have ⟨a, ha, h_eq⟩ := Array.mem_map.mp hx
      unfold Circuit.subcircuits at ha
      have ⟨y, _, hy_eq⟩ := Array.mem_map.mp ha
      have hd : y.val.hasDepth d = true := Array.all_eq_true_iff_forall_mem.mp h_true y.val y.property
      have h_spec := Circuit.depth_spec a
      have ha_val : a.val = y.val := by rw [← hy_eq]
      refine Nat.le_of_not_lt ?_
      refine fun h_not_le => ?_
      have h_depth_gt : d < a.depth := by omega
      have hd_false' := h_spec.2 d h_depth_gt
      rw [ha_val] at hd_false'
      rw [hd] at hd_false'
      contradiction
    · apply Array.le_max_of_mem
      apply Decidable.byContradiction
      intro h_contra
      simp at h_contra
      have h_all_lt : ∀ a ∈ c.subcircuits, a.depth < d := by
        intro a ha
        have ha_val_mem : a.val ∈ c.val.refs := by
          unfold Circuit.subcircuits at ha
          have ⟨y, _, hy_eq⟩ := Array.mem_map.mp ha
          rw [← hy_eq]
          exact y.2
        have ha_hasDepth : a.val.hasDepth d = true :=
          Array.all_eq_true_iff_forall_mem.mp h_true a.val ha_val_mem
        have ha_depth_le : a.depth ≤ d := by
          apply Decidable.byContradiction
          intro h_gt
          have h_false := (Circuit.depth_spec a).2 d (by omega)
          rw [ha_hasDepth] at h_false
          contradiction
        have h_neq : a.depth ≠ d := by
          intro h_eq
          exact h_contra a ha h_eq
        omega
      cases d with
      | zero =>
        have h_size : 0 < c.subcircuits.size := by
          cases h_eq : c.subcircuits.size
          · simp [Array.isEmpty, h_eq] at hsub_not_empty
          · omega
        have ha_mem : c.subcircuits[0]'(by omega) ∈ c.subcircuits := Array.getElem_mem (by omega)
        have h_lt := h_all_lt _ ha_mem
        omega
      | succ k =>
        have h_all_k_false : c.val.refs.all (PartialCircuit.hasDepth k) = false := by
          have h_step : PartialCircuit.hasDepth (k + 1) c.val = false := h_false (k + 1) (by omega)
          unfold PartialCircuit.hasDepth at h_step
          exact (Bool.or_eq_false_iff.mp h_step).2
        have h_exists_ref : ∃ ref ∈ c.val.refs, PartialCircuit.hasDepth k ref = false := by
          apply Decidable.byContradiction
          intro h_none
          simp at h_none
          have h_all_k_true : c.val.refs.all (PartialCircuit.hasDepth k) = true := by
            apply Array.all_eq_true_iff_forall_mem.mpr
            intro x hx
            cases h_eq : PartialCircuit.hasDepth k x
            · simp [h_none x hx] at h_eq
            · rfl
          rw [h_all_k_true] at h_all_k_false
          contradiction
        rcases h_exists_ref with ⟨ref, href_mem, href_false⟩
        rw [Array.mem_iff_getElem] at href_mem
        rcases href_mem with ⟨i, hi, h_ref_eq⟩
        have hi_sub : i < c.subcircuits.size := by
          have h_size : c.subcircuits.size = c.val.refs.size := by unfold Circuit.subcircuits; simp
          omega
        let ha := c.subcircuits[i]
        have ha_mem : ha ∈ c.subcircuits := Array.getElem_mem hi_sub
        have ha_val : ha.val = ref := by
          have h_val_eq : ha.val = c.val.refs[i] := by unfold ha Circuit.subcircuits; simp
          rw [h_val_eq, h_ref_eq]
        have ha_depth_lt : ha.depth < k + 1 := h_all_lt ha ha_mem
        have ha_depth_le : ha.depth ≤ k := by omega
        have ha_hasDepth_k := PartialCircuit.hasDepth_mono ha_depth_le (Circuit.depth_spec ha).1
        rw [ha_val] at ha_hasDepth_k
        rw [ha_hasDepth_k] at href_false
        contradiction

def evalStaged (st : State) : Array Bool := Id.run do
  let collect := Array.map fun idx =>
    if _ : idx < st.current.val then
      match st.gates[idx] with
      | .const val => val
      | _ => false
    else false
  if h_cur : st.gates.size = st.current then
    collect st.outputs
  else
    let mut newVal := false
    let mut newReplacer := st.replacer
    if hr : ¬st.replacer.isEmpty then
      let (val, tail) := st.replacer.next hr
      newVal := val
      newReplacer := tail
    else match hg : st.gates[st.current] with
    | .const val => newVal := val
    | .nand a b =>
      let vals := collect #[a, b]
      let aVal := vals[0]'(by simp [vals, collect])
      let bVal := vals[1]'(by simp [vals, collect])
      newVal := !(aVal && bVal)
    | .invoke cIdx args =>
      if _ : cIdx < st.circuits.size then
        let result := stageEval st.circuits[cIdx] (collect args) |> evalStaged |>.drain
        if hr : ¬ result.isEmpty then
          let (val, tail) := result.next hr
          newVal := val
          newReplacer := tail
    let gates := st.gates.set st.current (.const newVal)
    let next : Fin (gates.size + 1) := ⟨st.current.val + 1, by simp [gates]; omega⟩
    return evalStaged { st with gates := gates, current := next, replacer := newReplacer }
termination_by terminationMeasure st
decreasing_by
  all_goals
    refine Prod.lex_def.mpr ?_
    simp [terminationMeasure]
  · simp [stateDepth]
    omega
  · left
    simp only [stageEval_stateDepth]
    have h_mem : st.circuits[cIdx] ∈ st.circuits := Array.getElem_mem (by omega)
    have h_mem' : st.circuits[cIdx].depth + 1 ∈ st.circuits.map (fun c => c.depth + 1) :=
      Array.mem_map.mpr ⟨st.circuits[cIdx], h_mem, rfl⟩
    have hcne : st.circuits ≠ #[] := by
      intro h
      simp only [h, List.getElem_toArray, List.mem_toArray] at h_mem
      contradiction
    have hne : st.circuits.map (fun c => c.depth + 1) ≠ #[] := by
      simpa using hcne
    have h_le : st.circuits[cIdx].depth + 1 ≤ stateDepth st := by
      unfold stateDepth
      simp [Array.max?, hne]
      exact Array.le_max_of_mem h_mem'
    omega

def eval (c : Circuit) (inputs : Array Bool) : Array Bool :=
  c.stageEval inputs |> evalStaged

def mk' (refs : Array Circuit) (gates : Array Gate) (inputs : Array Nat) (outputs : Array Nat) : Circuit := by
  let p : PartialCircuit := ⟨refs.map Subtype.val, gates, inputs, outputs⟩
  refine ⟨p, ?_⟩
  have ⟨max_u, h_max_u⟩ : ∃ max_u, ∀ c ∈ refs, c.depth ≤ max_u := by
    cases refs
    rename_i refs_list
    induction refs_list with
    | nil =>
      refine ⟨0, ?_⟩
      intro c hc
      simp at hc
    | cons hd tl ih =>
      have ⟨m, hm⟩ := ih
      refine ⟨hd.depth + m, ?_⟩
      intro c hc
      simp at hc
      rcases hc with hl | hr
      · simp [hl]
      · have := hm c (by simp [hr])
        omega
  refine ⟨max_u + 1, ?_⟩
  unfold PartialCircuit.hasDepth
  apply Bool.or_eq_true_iff.mpr
  right
  apply Array.all_eq_true_iff_forall_mem.mpr
  intro v hv
  have ⟨c, hc_mem, hc_eq⟩ := Array.mem_map.mp hv
  rw [← hc_eq]
  exact PartialCircuit.hasDepth_mono (h_max_u c hc_mem) (Circuit.depth_spec c).1

instance : Inhabited Circuit where
  default := mk' #[] #[] #[] #[]

/--
Extracts the evaluated boolean value of a specific wire index.
-/
def wireValue (c : Circuit) (inputs : Array Bool) (idx : Nat) : Bool :=
  let probe := mk' c.subcircuits c.val.gates c.val.inputs #[idx]
  (probe.eval inputs)[0]? |>.getD false

/--
Extracts the entire execution trace.
-/
def evalTrace (c : Circuit) (inputs : Array Bool) : Array Bool :=
  -- Generate an array of all wire indices: #[0, 1, ..., gates.size - 1]
  let allWires := Array.range c.val.gates.size

  -- Evaluate a circuit whose outputs are ALL wires
  let traceCircuit := mk' c.subcircuits c.val.gates c.val.inputs allWires
  traceCircuit.eval inputs

/-- State managed by the CircuitBuilder monad -/
structure BuilderState where
  refs   : Array Circuit := #[]
  gates  : Array Gate    := #[]
  inputs : Array Nat     := #[]

abbrev BuilderM := StateM BuilderState

namespace BuilderM

/-- Appends a gate to the circuit and returns its wire index. -/
def addGate (g : Gate) : BuilderM Nat := modifyGet fun s =>
  (s.gates.size, { s with gates := s.gates.push g })

/-- Registers a new input wire. -/
def input : BuilderM Nat := do
  let idx ← addGate (.const false)
  modify fun s => { s with inputs := s.inputs.push idx }
  return idx

/-- Adds a NAND gate. -/
def nand (a b : Nat) : BuilderM Nat :=
  addGate (.nand a b)

/-- Registers a subcircuit and returns its reference index in the refs array. -/
def register (c : Circuit) : BuilderM Nat := modifyGet fun s =>
  (s.refs.size, { s with refs := s.refs.push c })

/--
Invokes a previously registered subcircuit by its index.
Automatically pads the gate array with the required dummy gates for multiple outputs.
-/
def invoke (cIdx : Nat) (args : Array Nat) : BuilderM (Array Nat) := do
  let s ← get
  let outCount := match s.refs[cIdx]? with
  | some c => c.val.outputs.size
  | none   => 0

  let startIdx ← addGate (.invoke cIdx args)

  let outIdxs ← Array.ofFnM
    fun idx : Fin outCount =>
      if idx = ⟨0, by have _ := idx.isLt; omega⟩ then
        pure startIdx
      else
        addGate (.const false)

  return outIdxs

/--
A builder action that generates constant gates for a given `BitVec`
and returns their wire indices.
-/
def constWires {w : Nat} (v : BitVec w) : BuilderM (Array Nat) := do
  let c0 ← addGate (.const false)
  let c1 ← addGate (.const true)
  return Array.ofFn fun i : Fin w =>
    if v.getLsb i then c1 else c0

end BuilderM

/-- Runs the builder and compiles it into a well-formed Circuit -/
def build (b : BuilderM (Array Nat)) : Circuit :=
  let (outputs, s) := b.run {}
  mk' s.refs s.gates s.inputs outputs

open Circuit.BuilderM

/--
A circuit representing an XOR gate built from NAND gates.
-/
def xor : Circuit := Circuit.build do
  let a ← input
  let b ← input

  let g2 ← nand a b
  let g3 ← nand a g2
  let g4 ← nand b g2
  let out ← nand g3 g4

  return #[out]

/--
A circuit representing a Half Adder.
-/
def halfAdder : Circuit := Circuit.build do
  let xorIdx ← register xor

  let a ← input
  let b ← input

  let sumIdxs ← invoke xorIdx #[a, b]
  let sum := sumIdxs[0]!

  let g3 ← nand a b
  let carry ← nand g3 g3

  return #[sum, carry]

/--
A Full Adder circuit.
-/
def fullAdder : Circuit := Circuit.build do
  let haIdx ← register halfAdder

  let a ← input
  let b ← input
  let cin ← input

  let ha1 ← invoke haIdx #[a, b]
  let sum1 := ha1[0]!
  let carry1 := ha1[1]!

  let ha2 ← invoke haIdx #[sum1, cin]
  let sum2 := ha2[0]!
  let carry2 := ha2[1]!

  let not_carry1 ← nand carry1 carry1
  let not_carry2 ← nand carry2 carry2
  let cout ← nand not_carry1 not_carry2

  return #[sum2, cout]

/--
An N-bit Ripple Carry Adder.
-/
def rippleAdder (n : Nat) : Circuit := Circuit.build do
  let faIdx ← register fullAdder

  let mut as ← Array.ofFnM fun _ : Fin n => input
  let mut bs ← Array.ofFnM fun _ : Fin n => input

  let mut cin ← input
  let mut sums := #[]

  for i in 0...n do
    let a := as[i]!
    let b := bs[i]!

    let fa ← invoke faIdx #[a, b, cin]
    sums := sums.push fa[0]!
    cin := fa[1]!

  return sums.push cin

/--
A `w`-bit circuit that evaluates whether the unsigned input is less than a constant `v`.
It uses a `w`-bit ripple carry adder to compute `A + (-v)` (which is equivalent to `A + 2^w - v`).
If the input `A` is less than `v`, the addition will not produce a carry out.
-/
def ltConst {w : Nat} (v : BitVec w) : Circuit := Circuit.build do
  let adderIdx ← register (rippleAdder w)

  let varArgs ← Array.ofFnM fun _ : Fin w => input

  let constArgs ← constWires (-v)

  let c0 ← addGate (.const false)
  let args := varArgs ++ constArgs ++ #[c0]
  let res ← invoke adderIdx args

  let cout := res[w]!
  let lt ← nand cout cout

  return #[lt]

/--
A `w`-bit less-than circuit.
Takes two `w`-bit inputs `A` and `B`.
Returns true if `A < B`, and false otherwise.
It computes `A + ~B + 1`. The carry out is 1 if `A >= B`.
Therefore, `A < B` is the negation of the carry out.
-/
def lt (w : Nat) : Circuit := Circuit.build do
  let adderIdx ← register (rippleAdder w)

  let arrA ← Array.ofFnM fun _ : Fin w => input
  let arrB ← Array.ofFnM fun _ : Fin w => input

  let notB ← Array.ofFnM fun i : Fin w => do
    let b := arrB[i.val]!
    nand b b

  let c1 ← addGate (.const true)
  let args := arrA ++ notB ++ #[c1]
  let res ← invoke adderIdx args

  let cout := res[w]!
  let out ← nand cout cout

  return #[out]

/--
A 1-bit conditional swap circuit.
If `s` is true, it outputs `(b, a)`. If `s` is false, it outputs `(a, b)`.
-/
def condSwap1 : Circuit := Circuit.build do
  let s ← input
  let a ← input
  let b ← input

  let not_s ← nand s s

  let a1 ← nand a not_s
  let a2 ← nand b s
  let a_out ← nand a1 a2

  let b1 ← nand b not_s
  let b2 ← nand a s
  let b_out ← nand b1 b2

  return #[a_out, b_out]

/--
A `w`-bit conditional swap circuit.
Takes a 1-bit condition `s` and two `w`-bit numbers.
Returns the two numbers, swapped if `s` is true, or in their original order if `s` is false.
-/
def condSwap (w : Nat) : Circuit := Circuit.build do
  let cs1Idx ← register condSwap1

  let s ← input
  let arrA ← Array.ofFnM fun _ : Fin w => input
  let arrB ← Array.ofFnM fun _ : Fin w => input

  let results ← Array.ofFnM fun i : Fin w => do
    let a := arrA[i.val]!
    let b := arrB[i.val]!
    invoke cs1Idx #[s, a, b]

  let outA := results.map (·[0]!)
  let outB := results.map (·[1]!)

  return outA ++ outB

/--
Recursively builds a bitonic merge circuit for 2^p items of W bits each,
sorting by a K-bit key occupying the top K bits of each item.
Returns the W-bit items followed by a flat transcript of swap decisions.
-/
def bitonicMerge (p : Nat) (K : Nat) (W : Nat) : Circuit := Circuit.build do
  if p = 0 then
    Array.ofFnM fun _ : Fin W => input
  else
    let half := 2^(p-1)
    let n := 2^p

    let ltKIdx ← register (lt K)
    let csWIdx ← register (condSwap W)
    let mergeHalfIdx ← register (bitonicMerge (p-1) K W)

    let items ← Array.ofFnM fun _ : Fin n => Array.ofFnM fun _ : Fin W => input

    let results ← Array.ofFnM fun i : Fin half => do
      let A := items[i.val]!
      let B := items[i.val + half]!
      let a_key := A.extract (W - K) W
      let b_key := B.extract (W - K) W

      let cmpArr ← invoke ltKIdx (b_key ++ a_key)
      let cmp := cmpArr[0]!

      let sw ← invoke csWIdx (#[cmp] ++ A ++ B)
      let A_out := sw.extract 0 W
      let B_out := sw.extract W (2 * W)

      return (cmp, A_out, B_out)

    let transcript := results.map (·.1)
    let afterSwapL := results.map (·.2.1)
    let afterSwapR := results.map (·.2.2)

    let leftRes ← invoke mergeHalfIdx afterSwapL.flatten
    let rightRes ← invoke mergeHalfIdx afterSwapR.flatten

    let leftItemsSize := W * half
    let rightItemsSize := W * half

    let finalItems := (leftRes.extract 0 leftItemsSize) ++ (rightRes.extract 0 rightItemsSize)
    let finalTranscript :=
      transcript ++ (leftRes.extract leftItemsSize leftRes.size) ++
        (rightRes.extract rightItemsSize rightRes.size)

    return finalItems ++ finalTranscript

/--
Recursively builds a bitonic sort circuit for 2^p items of W bits each,
sorting by a K-bit key occupying the top K bits of each item.
Outputs the sorted items and the collected transcript of swap decisions.
-/
def bitonicSort (p : Nat) (K : Nat) (W : Nat) : Circuit := Circuit.build do
  if p = 0 then
    Array.ofFnM fun _ : Fin W => input
  else
    let half := 2^(p-1)
    let n := 2^p
    let sortHalfIdx ← register (bitonicSort (p-1) K W)
    let mergeIdx ← register (bitonicMerge p K W)

    let items ← Array.ofFnM fun _ : Fin n => Array.ofFnM fun _ : Fin W => input

    let leftRes ← invoke sortHalfIdx (items.extract 0 half).flatten
    let rightRes ← invoke sortHalfIdx (items.extract half n).flatten

    let itemsSize := W * half

    let sortedLeft := Array.ofFn fun i : Fin half => leftRes.extract (i.val * W) (i.val * W + W)
    let sortedRight := Array.ofFn fun i : Fin half => rightRes.extract (i.val * W) (i.val * W + W)
    let rightRev := Array.ofFn fun i : Fin half => sortedRight[half - 1 - i.val]!

    let mergeRes ← invoke mergeIdx (sortedLeft.flatten ++ rightRev.flatten)

    let allT := (leftRes.extract itemsSize leftRes.size) ++ (rightRes.extract itemsSize rightRes.size)

    let mergeItemsSize := W * n
    let finalItems := mergeRes.extract 0 mergeItemsSize
    let allT := allT ++ (mergeRes.extract mergeItemsSize mergeRes.size)

    return finalItems ++ allT

/--
Number of swap-decision bits recorded by `bitonicMerge p K W` in its transcript.
This is independent of `K` and `W` — it only depends on the network's shape.
-/
def mergeTranscriptSize : Nat → Nat
| 0 => 0
| p + 1 => 2^p + 2 * mergeTranscriptSize p

/--
Number of swap-decision bits recorded by `bitonicSort p K W` in its transcript.
This is independent of `K` and `W`.
-/
def sortTranscriptSize : Nat → Nat
| 0 => 0
| p + 1 => 2 * sortTranscriptSize p + mergeTranscriptSize (p + 1)

/--
Inverse of `bitonicMerge`. Given the `2^p` sorted `W`-bit items produced by
`bitonicMerge p K W`, together with the `mergeTranscriptSize p` swap-decision
bits it recorded, reconstructs the original pre-merge items. Each stage simply
re-applies the same conditional swap with the same decision bit, which undoes it.
Inputs are `items (2^p * W bits) ++ transcript`, in the same layout that
`bitonicMerge` produces as its own output.
-/
def bitonicMergeUnsort (p : Nat) (W : Nat) : Circuit := Circuit.build do
  if p = 0 then
    Array.ofFnM fun _ : Fin W => input
  else
    let half := 2^(p-1)
    let n := 2^p
    let subT := mergeTranscriptSize (p-1)

    let csWIdx ← register (condSwap W)
    let unmergeHalfIdx ← register (bitonicMergeUnsort (p-1) W)

    let items ← Array.ofFnM fun _ : Fin n => Array.ofFnM fun _ : Fin W => input
    let topT ← Array.ofFnM fun _ : Fin half => input
    let leftSubT ← Array.ofFnM fun _ : Fin subT => input
    let rightSubT ← Array.ofFnM fun _ : Fin subT => input

    let sortedLeft := items.extract 0 half
    let sortedRight := items.extract half n

    let afterSwapL ← invoke unmergeHalfIdx (sortedLeft.flatten ++ leftSubT)
    let afterSwapR ← invoke unmergeHalfIdx (sortedRight.flatten ++ rightSubT)

    let results ← Array.ofFnM fun i : Fin half => do
      let s := topT[i.val]!
      let aOut := afterSwapL.extract (i.val * W) (i.val * W + W)
      let bOut := afterSwapR.extract (i.val * W) (i.val * W + W)
      let sw ← invoke csWIdx (#[s] ++ aOut ++ bOut)
      let a := sw.extract 0 W
      let b := sw.extract W (2 * W)
      return (a, b)

    let origLeft := results.map (·.1)
    let origRight := results.map (·.2)

    return origLeft.flatten ++ origRight.flatten

/--
Inverse of `bitonicSort`. Given the `2^p` sorted `W`-bit items produced by
`bitonicSort p K W`, together with the `sortTranscriptSize p` swap-decision
bits it recorded, reconstructs the original pre-sort items. Inputs are
`items (2^p * W bits) ++ transcript`, matching `bitonicSort`'s own output layout.
-/
def bitonicSortUnsort (p : Nat) (K : Nat) (W : Nat) : Circuit := Circuit.build do
  if p = 0 then
    Array.ofFnM fun _ : Fin W => input
  else
    let half := 2^(p-1)
    let n := 2^p
    let subS := sortTranscriptSize (p-1)
    let subM := mergeTranscriptSize p

    let unsortHalfIdx ← register (bitonicSortUnsort (p-1) K W)
    let unmergeIdx ← register (bitonicMergeUnsort p W)

    let items ← Array.ofFnM fun _ : Fin n => Array.ofFnM fun _ : Fin W => input
    let leftSubT ← Array.ofFnM fun _ : Fin subS => input
    let rightSubT ← Array.ofFnM fun _ : Fin subS => input
    let mergeT ← Array.ofFnM fun _ : Fin subM => input

    let preMerge ← invoke unmergeIdx (items.flatten ++ mergeT)

    let sortedLeftItems := Array.ofFn fun i : Fin half => preMerge.extract (i.val * W) (i.val * W + W)
    let rightRevItems := Array.ofFn fun i : Fin half => preMerge.extract ((half + i.val) * W) ((half + i.val) * W + W)
    let sortedRightItems := Array.ofFn fun i : Fin half => rightRevItems[half - 1 - i.val]!

    let origLeft ← invoke unsortHalfIdx (sortedLeftItems.flatten ++ leftSubT)
    let origRight ← invoke unsortHalfIdx (sortedRightItems.flatten ++ rightSubT)

    return origLeft ++ origRight

/--
Memory-pattern-secure (Mem-Sec) inverse rejection sampling encoder.

`n` : actual mask length (need **not** be a power of two — internally padded
      up to `2^p` with the constant `4095`, exactly like `repeat(4095)` in
      the Rust code; the padding is stripped back off before returning).
`D` : fixed number of data elements to embed, `1 ≤ D ≤ n`.
`stable` : when `true`, tags each item with `value ++ index_bits ++ invalid_bit`
      (the "index trick" — index bits only break ties within a validity class,
      so front-packing matches `encode_vector_pc_sec`'s left-to-right scan).
      When `false`, tags each item with just `value ++ invalid_bit` — cheaper,
      but front-packing order among equally-valid elements is unspecified.

Either way, the sort/unsort key's top bit is *always* the validity bit
(`¬(v < 3329)`) and nothing else — magnitude of `v` never participates in the
ordering, which is an essential property to avoid biasing the surviving values.
-/
def memSecEncode (stable : Bool) (n D : Nat) : Circuit := Circuit.build do
  let p := Nat.bitWidth n
  let padded := 2 ^ p
  let idxBits := if stable then p else 0
  let K := idxBits + 1
  let W := 12 + K

  let ltIdx ← register (@ltConst 12 (3329 : BitVec 12))
  let sortIdx ← register (bitonicSort p K W)
  let unsortIdx ← register (bitonicSortUnsort p K W)

  let maskItems ← Array.ofFnM fun _ : Fin n => Array.ofFnM fun _ : Fin 12 => input
  let dataItems ← Array.ofFnM fun _ : Fin D => Array.ofFnM fun _ : Fin 12 => input

  let padConst ←
    if padded > n then
      constWires (w := 12) (BitVec.ofNat 12 4095)
    else
      pure #[]

  let allItems : Array (Array Nat) :=
    maskItems ++ Array.ofFn fun _ : Fin (padded - n) => padConst

  let keyedItems ← Array.ofFnM fun i : Fin padded => do
    let v := allItems[i.val]!
    let ltRes ← invoke ltIdx v
    let validBit := ltRes[0]!
    let invalidBit ← nand validBit validBit
    if stable then
      let idxWires ← constWires (w := idxBits) (BitVec.ofNat idxBits i.val)
      return v ++ idxWires ++ #[invalidBit]
    else
      return v ++ #[invalidBit]

  let sortRes ← invoke sortIdx keyedItems.flatten
  let itemsSize := padded * W
  let sortedFlat := sortRes.extract 0 itemsSize
  let transcript := sortRes.extract itemsSize sortRes.size
  let sortedItems := Array.ofFn fun i : Fin padded =>
    sortedFlat.extract (i.val * W) (i.val * W + W)

  let successBit ←
    if D > 0 then
      let lastInvalid := (sortedItems[D - 1]!)[W - 1]!
      nand lastInvalid lastInvalid
    else
      addGate (.const true)

  let newItems := Array.ofFn fun i : Fin padded =>
    let item := sortedItems[i.val]!
    let key := item.extract 12 W
    if i.val < D then
      dataItems[i.val]! ++ key
    else
      item

  let unsortRes ← invoke unsortIdx (newItems.flatten ++ transcript)

  let outItems := Array.ofFn fun i : Fin n =>
    (unsortRes.extract (i.val * W) (i.val * W + W)).extract 0 12

  return outItems.flatten ++ #[successBit]

example : xor.cost = 6 := by native_decide
example : halfAdder.cost = 10 := by native_decide
example : fullAdder.cost = 28 := by native_decide
example : (rippleAdder 8).cost = 249 := by native_decide
example : (rippleAdder 16).cost = 497 := by native_decide
example : (@ltConst 12 3329).cost = 401 := by native_decide
example : (condSwap 13).cost = 170 := by native_decide
example : (lt 1).cost = 38 := by native_decide

end Circuit
