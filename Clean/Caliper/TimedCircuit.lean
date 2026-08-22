import Clean.Caliper.WitgenCost

/-!
# `TimedCircuit`: budgeted witness generation as a type

A `TimedCircuit` is a `FormalCircuit` that additionally **certifies its
witness-generation cost**: constructing one requires exhibiting, for every witness
generator of the circuit, compiled straight-line machine code (via the checked
witgen compiler `compile`, `Clean/Caliper/WitgenCompile.lean`) whose *syntactic*
static cost sums to a total below the circuit's `witgenBudget`.

The obligation is one boolean evaluation (`underBudget`), dischargeable by
`native_decide` — but the number it certifies is not just a number:

* `FlatOperation.witgenTime` folds `FlatOperation.witgenCost` over the circuit's flat
  operations, threading the offset exactly like `FlatOperation.localLength` and
  `computableChecks` (`WitgenComputable.lean`): each generator is priced — and its
  `envBound` checked by `compile` — at its own accumulated offset.
* `witgenTime_sound` extracts, from `witgenTime = some T`, a per-generator
  certificate (`WitnessCosts`): the checked compiler accepts every generator at its
  own offset, with a static time `tᵢ`, and `Σ tᵢ = T`.
* By the phase-2 cost theorems (`WitgenCost.lean`), each certified `tᵢ` is the
  **exact running time of every execution** of the compiled generator
  (`Exec.staticTime?_time_eq` / `compile_time_eq`), with live-memory peak `≤ tᵢ`
  in any per-word-charging cost model (`Exec.peak_le_time`); and by the simulation
  theorem (`compile_sim`, `WitgenSimIR.lean`) that execution computes the encoded
  reference output of the generator's IR semantics.

The type is *unattainable* for circuits with a bare `.native` witness closure —
`compile` rejects those, so `witgenTime` returns `none` and no budget check can
pass. A `.certified` witness (native closure + IR reimplementation + equivalence
proof, `Clean/Circuit/WitnessIR.lean`) restores the type: `compile` routes it
through its IR fields, so the cost certificate applies to the very closure the
prover runs.

**Input-genericity (design choice)**: the cost of a compiled generator depends on
the *syntactic shape* of the expressions it embeds, and a circuit's input variable
`Var Input F` is an arbitrary expression tree — instantiating `main` with compound
input expressions genuinely changes the instruction count of `<==`-style copy
generators. So a single number cannot be input-generic over all instantiations, and
the obligation is stated at the **canonical instantiation**: fresh input variables
`varFromOffset Input 0` (cells `0 .. size Input - 1`) with witnesses starting at
offset `size Input` — the standard top-level layout, the same instantiation the
`computableWitnesses` examples of `WitgenComputable.lean` certify (there at
`var ⟨0⟩` / offset 1). This is choice (b) of the design space; a structural
input-congruence lemma over variable-only instantiations is future work, as is
whole-circuit sequential composition of the per-generator executions (budgets sum
over composition by construction — `witgenTime` of an append is the sum — but the
machine-level composed run is not yet stated).
-/

namespace Caliper.WitgenCompile

open Witgen

variable {F : Type} [FiniteField F]

/-! ## Certified cost of flat operations -/

/-- The certified witness-generation cost of one flat operation at offset `n`: for a
witness operation, the static time of its compiled code — `some t` only when the
checked compiler accepts the generator at environment size `n`, priced by the honest
partial clock `Stmt.staticTime?` (which cannot quote a number for loopy code; on
`compile`'s straight-line output it always succeeds, `compile_straight`). Non-witness
operations cost 0. Certified native witnesses (`WitgenIR.certified`) need no special
handling: `compile` already routes them through their IR reimplementation. -/
def FlatOperation.witgenCost (C : CostModel) (n : ℕ) : FlatOperation F → Option ℕ
  | .witness _ ir => (compile n ir).bind (·.staticTime? C)
  | .assert _ | .lookup _ | .interact _ => some 0

/-- Total certified witgen time of a flat operation list starting at offset `n`.
The offset is threaded exactly like `FlatOperation.localLength` and
`computableChecks`: each operation advances it by its witness arity
(`FlatOperation.singleLocalLength`), so every generator is priced — and its
`envBound` checked by `compile` — at its own accumulated offset. `some T` means the
whole list is certified; one uncompilable generator (in particular any bare
`.native` closure) poisons the total to `none`. -/
def FlatOperation.witgenTime (C : CostModel) : ℕ → List (FlatOperation F) → Option ℕ
  | _, [] => some 0
  | n, op :: ops =>
    (FlatOperation.witgenCost C n op).bind fun t =>
      (FlatOperation.witgenTime C (FlatOperation.singleLocalLength op + n) ops).map (t + ·)

/-- Decidable budget check: the whole-list fold produces a certified total strictly
below `budget`. One boolean — `native_decide` discharges it at concrete circuits. -/
def underBudget (C : CostModel) (n budget : ℕ) (ops : List (FlatOperation F)) : Bool :=
  match FlatOperation.witgenTime C n ops with
  | some T => T < budget
  | none => false

theorem underBudget_iff {C : CostModel} {n budget : ℕ} {ops : List (FlatOperation F)} :
    underBudget C n budget ops = true ↔
      ∃ T, FlatOperation.witgenTime C n ops = some T ∧ T < budget := by
  unfold underBudget
  cases h : FlatOperation.witgenTime C n ops <;> simp

/-! ## The meaning theorem: the number is a per-generator certificate -/

/-- Per-generator cost certificate for a flat operation list starting at offset `n`,
with total `T`: every witness generator, **at its own accumulated offset**, is
accepted by the checked compiler with a static time, and the static times sum to
`T`. This is the fold `FlatOperation.witgenTime` computes, reified as a relation —
the shape the meaning theorems below are read off from. -/
inductive WitnessCosts (C : CostModel) : ℕ → List (FlatOperation F) → ℕ → Prop where
  | nil {n : ℕ} : WitnessCosts C n [] 0
  | witness {n m t T : ℕ} {ir : WitgenIR F m} {ops : List (FlatOperation F)}
      (code : Stmt 64) (hcompile : compile n ir = some code)
      (htime : code.staticTime? C = some t)
      (hrest : WitnessCosts C (m + n) ops T) :
      WitnessCosts C n (.witness m ir :: ops) (t + T)
  | assert {n T : ℕ} {e : Expression F} {ops : List (FlatOperation F)}
      (hrest : WitnessCosts C n ops T) : WitnessCosts C n (.assert e :: ops) T
  | lookup {n T : ℕ} {l : Lookup F} {ops : List (FlatOperation F)}
      (hrest : WitnessCosts C n ops T) : WitnessCosts C n (.lookup l :: ops) T
  | interact {n T : ℕ} {i : AbstractInteraction F} {ops : List (FlatOperation F)}
      (hrest : WitnessCosts C n ops T) : WitnessCosts C n (.interact i :: ops) T

/-- **The meaning of the number**: whenever the fold produces `some T`, every witness
generator in the list is individually certified at its own offset, and the certified
static times sum to exactly `T`. -/
theorem witgenTime_sound {C : CostModel} :
    ∀ (ops : List (FlatOperation F)) (n T : ℕ),
      FlatOperation.witgenTime C n ops = some T → WitnessCosts C n ops T
  | [], _, _, h => by
    simp only [FlatOperation.witgenTime, Option.some.injEq] at h
    exact h ▸ WitnessCosts.nil
  | .witness m ir :: ops, n, T, h => by
    simp only [FlatOperation.witgenTime, FlatOperation.witgenCost,
      FlatOperation.singleLocalLength] at h
    cases hc : compile n ir with
    | none => simp [hc] at h
    | some code =>
      cases ht : code.staticTime? C with
      | none => simp [hc, ht] at h
      | some t =>
        cases hrest : FlatOperation.witgenTime C (m + n) ops with
        | none => simp [hc, ht, hrest] at h
        | some rest =>
          simp only [hc, ht, hrest, Option.bind_some, Option.map_some,
            Option.some.injEq] at h
          exact h ▸ WitnessCosts.witness code hc ht (witgenTime_sound ops (m + n) rest hrest)
  | .assert e :: ops, n, T, h => by
    simp only [FlatOperation.witgenTime, FlatOperation.witgenCost,
      FlatOperation.singleLocalLength, Nat.zero_add, Option.bind_some] at h
    cases hrest : FlatOperation.witgenTime C n ops with
    | none => simp [hrest] at h
    | some rest =>
      simp only [hrest, Option.map_some, Option.some.injEq] at h
      exact h ▸ WitnessCosts.assert (witgenTime_sound ops n rest hrest)
  | .lookup l :: ops, n, T, h => by
    simp only [FlatOperation.witgenTime, FlatOperation.witgenCost,
      FlatOperation.singleLocalLength, Nat.zero_add, Option.bind_some] at h
    cases hrest : FlatOperation.witgenTime C n ops with
    | none => simp [hrest] at h
    | some rest =>
      simp only [hrest, Option.map_some, Option.some.injEq] at h
      exact h ▸ WitnessCosts.lookup (witgenTime_sound ops n rest hrest)
  | .interact i :: ops, n, T, h => by
    simp only [FlatOperation.witgenTime, FlatOperation.witgenCost,
      FlatOperation.singleLocalLength, Nat.zero_add, Option.bind_some] at h
    cases hrest : FlatOperation.witgenTime C n ops with
    | none => simp [hrest] at h
    | some rest =>
      simp only [hrest, Option.map_some, Option.some.injEq] at h
      exact h ▸ WitnessCosts.interact (witgenTime_sound ops n rest hrest)

/-- The per-generator ∀-statement extracted from a cost certificate, in the
codebase's offset-threaded `FlatOperation.forAll` form: every witness generator has
compiled code at its own offset, with a certified static time bounded by any bound
on the total. -/
theorem WitnessCosts.forAll_compile {C : CostModel} :
    ∀ {n T : ℕ} {ops : List (FlatOperation F)}, WitnessCosts C n ops T →
      ∀ {B : ℕ}, T ≤ B →
      FlatOperation.forAll n
        { witness n' _ ir := ∃ t code, compile n' ir = some code ∧
            code.staticTime? C = some t ∧ t ≤ B } ops
  | _, _, _, .nil, _, _ => trivial
  | _, _, _, .witness code hc ht hrest, _, hB =>
    ⟨⟨_, code, hc, ht, Nat.le_trans (Nat.le_add_right _ _) hB⟩,
      hrest.forAll_compile (Nat.le_trans (Nat.le_add_left _ _) hB)⟩
  | _, _, _, .assert hrest, _, hB => ⟨trivial, hrest.forAll_compile hB⟩
  | _, _, _, .lookup hrest, _, hB => ⟨trivial, hrest.forAll_compile hB⟩
  | _, _, _, .interact hrest, _, hB => ⟨trivial, hrest.forAll_compile hB⟩

/-- **The execution reading of a cost certificate**: in any per-word-charging cost
model (`1 ≤ C.allocPerWord` — true of both `CostModel.unit` and
`CostModel.cycles`), every witness generator's compiled code runs in **exactly** its
certified time `t ≤ B` on every input, with live-memory peak `≤ t`
(`Exec.staticTime?_time_eq`, `Exec.peak_le_time`). By the simulation theorem
`compile_sim` (`WitgenSimIR.lean`) — whose field-size side conditions are certified
by `compile` itself, leaving only primality — such an execution exists from every
environment-encoding start state and ends with the encoded reference output. -/
theorem WitnessCosts.forAll_exec {C : CostModel} (hC : 1 ≤ C.allocPerWord) :
    ∀ {n T : ℕ} {ops : List (FlatOperation F)}, WitnessCosts C n ops T →
      ∀ {B : ℕ}, T ≤ B →
      FlatOperation.forAll n
        { witness n' _ ir := ∃ t code, compile n' ir = some code ∧
            code.staticTime? C = some t ∧ t ≤ B ∧
            ∀ {s s' : State 64} {t' : ℕ} {d p : ℤ},
              Exec C code s s' t' d p → t' = t ∧ p ≤ (t : ℤ) } ops
  | _, _, _, .witness code hc ht hrest, _, hB =>
    ⟨⟨_, code, hc, ht, Nat.le_trans (Nat.le_add_right _ _) hB,
      fun hx =>
        have hte := hx.staticTime?_time_eq ht
        ⟨hte, hte ▸ hx.peak_le_time hC⟩⟩,
      hrest.forAll_exec hC (Nat.le_trans (Nat.le_add_left _ _) hB)⟩
  | _, _, _, .nil, _, _ => trivial
  | _, _, _, .assert hrest, _, hB => ⟨trivial, hrest.forAll_exec hC hB⟩
  | _, _, _, .lookup hrest, _, hB => ⟨trivial, hrest.forAll_exec hC hB⟩
  | _, _, _, .interact hrest, _, hB => ⟨trivial, hrest.forAll_exec hC hB⟩

/-- Weakening for witness-only `forAll` conditions (the assert/lookup/interact
fields are the trivial defaults on both sides). -/
theorem forAll_witness_mono {P Q : ℕ → (m : ℕ) → WitgenIR F m → Prop}
    (himp : ∀ n m ir, P n m ir → Q n m ir) :
    ∀ {n : ℕ} {ops : List (FlatOperation F)},
      FlatOperation.forAll n { witness := P } ops →
      FlatOperation.forAll n { witness := Q } ops
  | _, [], _ => trivial
  | n, .witness m ir :: _, h => ⟨himp n m ir h.1, forAll_witness_mono himp h.2⟩
  | _, .assert _ :: _, h => ⟨trivial, forAll_witness_mono himp h.2⟩
  | _, .lookup _ :: _, h => ⟨trivial, forAll_witness_mono himp h.2⟩
  | _, .interact _ :: _, h => ⟨trivial, forAll_witness_mono himp h.2⟩

/-! ## `TimedCircuit` -/

/-- A `TimedCircuit` is a `FormalCircuit` that **requires certified
witness-generation cost within a budget**: the checked witgen compiler must accept
every witness generator (at the canonical instantiation — fresh input variables
`varFromOffset Input 0`, witnesses from offset `size Input`; see the file docstring
for why the obligation is stated there), and the certified static times must sum to
a total strictly below `witgenBudget`.

The obligation is a single boolean evaluation, discharged by `native_decide` (the
default field tactic). A circuit with a bare `.native` witness closure cannot
inhabit this type; certifying the closure against an IR reimplementation
(`WitgenIR.certified`) restores it. -/
structure TimedCircuit (F : Type) [FiniteField F] (Input Output : TypeMap)
    [ProvableType Input] [ProvableType Output]
    extends circuit : FormalCircuit F Input Output where
  /-- The cost model witgen time is accounted in. -/
  costModel : CostModel := .unit
  /-- The budget: certified total witgen time must be strictly below this. -/
  witgenBudget : ℕ := 2 ^ 40
  /-- The certified cost obligation, at the canonical instantiation. -/
  witgen_bounded :
    underBudget costModel (size Input) witgenBudget
      ((circuit.main (varFromOffset Input 0)).operations (size Input)).toFlat = true := by
    native_decide

namespace TimedCircuit
variable {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]

/-- The flat operations of the canonical instantiation the budget is certified at:
fresh input variables at cells `0 .. size Input - 1`, witnesses from offset
`size Input`. -/
def canonicalOps (tc : TimedCircuit F Input Output) : List (FlatOperation F) :=
  ((tc.main (varFromOffset Input 0)).operations (size Input)).toFlat

/-- The obligation, read back: the canonical instantiation's total certified witgen
time exists and is strictly below the budget. -/
theorem witgenTime_lt_budget (tc : TimedCircuit F Input Output) :
    ∃ T, FlatOperation.witgenTime tc.costModel (size Input) tc.canonicalOps = some T ∧
      T < tc.witgenBudget :=
  underBudget_iff.mp tc.witgen_bounded

/-- The per-generator certificate behind a `TimedCircuit`'s budget. -/
theorem witnessCosts (tc : TimedCircuit F Input Output) :
    ∃ T, WitnessCosts tc.costModel (size Input) tc.canonicalOps T ∧
      T < tc.witgenBudget := by
  obtain ⟨T, hT, hlt⟩ := tc.witgenTime_lt_budget
  exact ⟨T, witgenTime_sound _ _ _ hT, hlt⟩

/-- **The `< budget` reading of the obligation**: in any per-word-charging cost
model, every witness generator of a `TimedCircuit` — at its offset in the canonical
instantiation — has compiled code with a certified static time `t < witgenBudget`,
and every execution of that code takes exactly `t` steps with live-memory peak
`≤ t` (via `compile_time_eq` / `Exec.staticTime?_time_eq` and `Exec.peak_le_time`;
`compile_sim` supplies the execution computing the encoded reference output). -/
theorem witgen_lt_budget (tc : TimedCircuit F Input Output)
    (hC : 1 ≤ tc.costModel.allocPerWord) :
    FlatOperation.forAll (size Input)
      { witness n _ ir := ∃ t code, compile n ir = some code ∧
          code.staticTime? tc.costModel = some t ∧ t < tc.witgenBudget ∧
          ∀ {s s' : State 64} {t' : ℕ} {d p : ℤ},
            Exec tc.costModel code s s' t' d p → t' = t ∧ p ≤ (t : ℤ) }
      tc.canonicalOps := by
  obtain ⟨T, hT, hlt⟩ := tc.witgenTime_lt_budget
  refine forAll_witness_mono ?_ ((witgenTime_sound _ _ _ hT).forAll_exec hC le_rfl)
  rintro n m ir ⟨t, code, hc, ht, hle, hexec⟩
  exact ⟨t, code, hc, ht, by omega, hexec⟩

/-- The `CostModel.Admissible` form of `witgen_lt_budget`: instead of the single
`1 ≤ allocPerWord` field, take the packaged "no table entry is free" predicate —
satisfied by both shipped tables (`CostModel.unit.admissible`,
`CostModel.cycles.admissible`), so for them the hypothesis is a named constant. -/
theorem witgen_lt_budget_admissible (tc : TimedCircuit F Input Output)
    (hC : tc.costModel.Admissible) :
    FlatOperation.forAll (size Input)
      { witness n _ ir := ∃ t code, compile n ir = some code ∧
          code.staticTime? tc.costModel = some t ∧ t < tc.witgenBudget ∧
          ∀ {s s' : State 64} {t' : ℕ} {d p : ℤ},
            Exec tc.costModel code s s' t' d p → t' = t ∧ p ≤ (t : ℤ) }
      tc.canonicalOps :=
  tc.witgen_lt_budget hC.allocPerWord

end TimedCircuit

/-! ## The demonstration: `IsZeroField` as a `TimedCircuit`

The circuit's two witness generators — `testIsZero` (the inverse witness, 139 unit
steps) and `isZeroCircuitCopyIR` (the `<==` copy, 18 unit steps) — sum to 157, far
below the default `2^40` budget. The obligation is one `native_decide`. -/

/- The pinned total for the instantiated `IsZeroField` circuit: `139 + 18 = 157`
unit steps for its complete witness generation (the same per-generator numbers as
`isZeroCompiled_staticTime_unit` / `isZeroCopyCompiled_staticTime_unit` in
`WitgenCost.lean`). -/
/-- info: some 157 -/
#guard_msgs in #eval FlatOperation.witgenTime CostModel.unit 1 isZeroCircuitOps

/-- **The goal shape**: the existing `FormalCircuit` upgraded to a `TimedCircuit`
by one `native_decide`, at the default budget `2^40` and unit cost model. -/
def isZeroTimed : TimedCircuit Fb field field :=
  { Gadgets.IsZeroField.circuit with witgen_bounded := by native_decide }

/-- The timed circuit's certified total, pinned: 157 unit steps. -/
theorem isZeroTimed_witgenTime :
    FlatOperation.witgenTime CostModel.unit (size field) isZeroTimed.canonicalOps
      = some 157 := by
  native_decide

/-- The exact-total reading for the demo, end to end: every witness generator of
the timed `IsZeroField` circuit has compiled code whose every execution takes
exactly its certified time `t ≤ 157`, with live-memory peak `≤ t`. -/
theorem isZeroTimed_witgen_le_159 :
    FlatOperation.forAll (size field)
      { witness n _ ir := ∃ t code, compile n ir = some code ∧
          code.staticTime? CostModel.unit = some t ∧ t ≤ 157 ∧
          ∀ {s s' : State 64} {t' : ℕ} {d p : ℤ},
            Exec CostModel.unit code s s' t' d p → t' = t ∧ p ≤ (t : ℤ) }
      isZeroTimed.canonicalOps :=
  (witgenTime_sound _ _ _ isZeroTimed_witgenTime).forAll_exec (by decide) le_rfl

/-- The `< 2^40` reading for the demo: the certified per-generator times `t ≤ 157`
of `isZeroTimed_witgen_le_159` are in particular strictly below the `2^40`
budget. -/
theorem isZeroTimed_witgen_lt_2_40 :
    FlatOperation.forAll (size field)
      { witness n _ ir := ∃ t code, compile n ir = some code ∧
          code.staticTime? CostModel.unit = some t ∧ t < 2 ^ 40 ∧
          ∀ {s s' : State 64} {t' : ℕ} {d p : ℤ},
            Exec CostModel.unit code s s' t' d p → t' = t ∧ p ≤ (t : ℤ) }
      isZeroTimed.canonicalOps := by
  refine forAll_witness_mono ?_ isZeroTimed_witgen_le_159
  rintro n m ir ⟨t, code, hc, ht, hle, hexec⟩
  exact ⟨t, code, hc, ht, by omega, hexec⟩

end Caliper.WitgenCompile
