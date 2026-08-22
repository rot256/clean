import Clean.Caliper.WitgenCompile
import Clean.Gadgets.Addition8.Addition8FullCarry

/-!
# The witgen compiler's checks imply Clean's computable-witnesses condition

The bridge between the witgen compiler's generation-time checks (`compilable`,
`envBound`) and the circuit layer's computability notion
(`ProverEnvironment.OnlyAccessedBelow`, `Operations.ComputableWitnesses`).

`ProverEnvironment.AgreesBelow N` constrains only `env.get` below `N`; `env.data` and
`env.hint` may differ arbitrarily. The constructors whose `eval` reads those fields
(`FExpr.dataGet`, `FExpr.hintGet`) and the closure escape hatch `WitgenIR.native` are
exactly the ones the checks reject, and every remaining access is an `env.get` below
`N`. So the checks imply `WitgenIR.eval` is invariant under `AgreesBelow N`
(`eval_congr`), i.e. `OnlyAccessedBelow N`. Certified witnesses pass the checks
through their IR reimplementation, and their equivalence proof extends `eval_congr`
to the closure their `eval` runs.

`Operations.ComputableWitnesses` is per-offset — the generator at offset `n` may only
access the environment below `n` — so the whole-circuit form threads the offset:
`computableChecks n ops` checks each generator's `envBound` at its own offset, and
`circuit_computableWitnesses_of_checks` turns one boolean evaluation into
`Circuit.ComputableWitnesses`.
-/

namespace Caliper.WitgenCompile

open Witgen

variable {F : Type} [FiniteField F]

/-! ## Evaluation congruence under `AgreesBelow`

Per sort: an environment-bounded expression evaluates equally in two environments that
agree below `N`, for any fixed locals and `mapRange` index. `envBound` alone suffices —
it already returns `false` on `listGet`/`dataGet`/`hintGet` and `native`, the
constructors excluded by `compilable`. -/

/-- Circuit expressions bounded by `N` only access `env.get` below `N`. -/
theorem Expression.eval_congr {N : ℕ} {env env' : ProverEnvironment F}
    (h : env.AgreesBelow N env') :
    ∀ (e : Expression F), Expression.envBound N e = true →
      e.eval env.toEnvironment = e.eval env'.toEnvironment
  | .var v, hb => by
    simp only [Expression.envBound, decide_eq_true_eq] at hb
    exact h v.index hb
  | .const _, _ => rfl
  | .add x y, hb => by
    simp only [Expression.envBound, Bool.and_eq_true] at hb
    simp only [Expression.eval, eval_congr h x hb.1, eval_congr h y hb.2]
  | .mul x y, hb => by
    simp only [Expression.envBound, Bool.and_eq_true] at hb
    simp only [Expression.eval, eval_congr h x hb.1, eval_congr h y hb.2]

mutual

/-- Environment-bounded field-sorted expressions only access `env.get` below `N`:
their evaluation agrees on environments that agree below `N` (with the same locals
and index). `dataGet`/`hintGet` — the constructors whose `eval` reads
`env.data`/`env.hint` — are excluded by `envBound` itself. -/
theorem FExpr.eval_congr {N : ℕ} {env env' : ProverEnvironment F}
    (h : env.AgreesBelow N env') (locals : Array (F ⊕ UInt64)) (idx : ℕ) :
    ∀ (e : FExpr F), FExpr.envBound N e = true →
      FExpr.eval { env := env, locals, idx } e = FExpr.eval { env := env', locals, idx } e
  | .expr e, hb => by
    simp only [FExpr.envBound] at hb
    simp only [FExpr.eval]
    exact Expression.eval_congr h e hb
  | .const _, _ => by simp only [FExpr.eval]
  | .localVar _, _ => by simp only [FExpr.eval]
  | .add x y, hb => by
    simp only [FExpr.envBound, Bool.and_eq_true] at hb
    simp only [FExpr.eval, FExpr.eval_congr h locals idx x hb.1,
      FExpr.eval_congr h locals idx y hb.2]
  | .mul x y, hb => by
    simp only [FExpr.envBound, Bool.and_eq_true] at hb
    simp only [FExpr.eval, FExpr.eval_congr h locals idx x hb.1,
      FExpr.eval_congr h locals idx y hb.2]
  | .inv x, hb => by
    simp only [FExpr.envBound] at hb
    simp only [FExpr.eval, FExpr.eval_congr h locals idx x hb]
  | .ofU64 n, hb => by
    simp only [FExpr.envBound] at hb
    simp only [FExpr.eval, U64Expr.eval_congr h locals idx n hb]
  | .ite c t e, hb => by
    simp only [FExpr.envBound, Bool.and_eq_true] at hb
    simp only [FExpr.eval, BExpr.eval_congr h locals idx c hb.1.1,
      FExpr.eval_congr h locals idx t hb.1.2, FExpr.eval_congr h locals idx e hb.2]
  | .listGet .., hb => by simp [FExpr.envBound] at hb
  | .dataGet .., hb => by simp [FExpr.envBound] at hb
  | .hintGet .., hb => by simp [FExpr.envBound] at hb

/-- Environment-bounded u64-sorted expressions only access `env.get` below `N`. -/
theorem U64Expr.eval_congr {N : ℕ} {env env' : ProverEnvironment F}
    (h : env.AgreesBelow N env') (locals : Array (F ⊕ UInt64)) (idx : ℕ) :
    ∀ (e : U64Expr F), U64Expr.envBound N e = true →
      U64Expr.eval { env := env, locals, idx } e
        = U64Expr.eval { env := env', locals, idx } e
  | .const _, _ => by simp only [U64Expr.eval]
  | .val x, hb => by
    simp only [U64Expr.envBound] at hb
    simp only [U64Expr.eval, FExpr.eval_congr h locals idx x hb]
  | .idx, _ => by simp only [U64Expr.eval]
  | .localVar _, _ => by simp only [U64Expr.eval]
  | .add x y, hb => by
    simp only [U64Expr.envBound, Bool.and_eq_true] at hb
    simp only [U64Expr.eval, U64Expr.eval_congr h locals idx x hb.1,
      U64Expr.eval_congr h locals idx y hb.2]
  | .mul x y, hb => by
    simp only [U64Expr.envBound, Bool.and_eq_true] at hb
    simp only [U64Expr.eval, U64Expr.eval_congr h locals idx x hb.1,
      U64Expr.eval_congr h locals idx y hb.2]
  | .div x y, hb => by
    simp only [U64Expr.envBound, Bool.and_eq_true] at hb
    simp only [U64Expr.eval, U64Expr.eval_congr h locals idx x hb.1,
      U64Expr.eval_congr h locals idx y hb.2]
  | .mod x y, hb => by
    simp only [U64Expr.envBound, Bool.and_eq_true] at hb
    simp only [U64Expr.eval, U64Expr.eval_congr h locals idx x hb.1,
      U64Expr.eval_congr h locals idx y hb.2]
  | .land x y, hb => by
    simp only [U64Expr.envBound, Bool.and_eq_true] at hb
    simp only [U64Expr.eval, U64Expr.eval_congr h locals idx x hb.1,
      U64Expr.eval_congr h locals idx y hb.2]
  | .lor x y, hb => by
    simp only [U64Expr.envBound, Bool.and_eq_true] at hb
    simp only [U64Expr.eval, U64Expr.eval_congr h locals idx x hb.1,
      U64Expr.eval_congr h locals idx y hb.2]
  | .lxor x y, hb => by
    simp only [U64Expr.envBound, Bool.and_eq_true] at hb
    simp only [U64Expr.eval, U64Expr.eval_congr h locals idx x hb.1,
      U64Expr.eval_congr h locals idx y hb.2]
  | .shiftL x y, hb => by
    simp only [U64Expr.envBound, Bool.and_eq_true] at hb
    simp only [U64Expr.eval, U64Expr.eval_congr h locals idx x hb.1,
      U64Expr.eval_congr h locals idx y hb.2]
  | .shiftR x y, hb => by
    simp only [U64Expr.envBound, Bool.and_eq_true] at hb
    simp only [U64Expr.eval, U64Expr.eval_congr h locals idx x hb.1,
      U64Expr.eval_congr h locals idx y hb.2]
  | .ite c t e, hb => by
    simp only [U64Expr.envBound, Bool.and_eq_true] at hb
    simp only [U64Expr.eval, BExpr.eval_congr h locals idx c hb.1.1,
      U64Expr.eval_congr h locals idx t hb.1.2, U64Expr.eval_congr h locals idx e hb.2]

/-- Environment-bounded conditions only access `env.get` below `N`. -/
theorem BExpr.eval_congr {N : ℕ} {env env' : ProverEnvironment F}
    (h : env.AgreesBelow N env') (locals : Array (F ⊕ UInt64)) (idx : ℕ) :
    ∀ (e : BExpr F), BExpr.envBound N e = true →
      BExpr.eval { env := env, locals, idx } e = BExpr.eval { env := env', locals, idx } e
  | .true, _ => by simp only [BExpr.eval]
  | .false, _ => by simp only [BExpr.eval]
  | .feq x y, hb => by
    simp only [BExpr.envBound, Bool.and_eq_true] at hb
    simp only [BExpr.eval, FExpr.eval_congr h locals idx x hb.1,
      FExpr.eval_congr h locals idx y hb.2]
  | .neq x y, hb => by
    simp only [BExpr.envBound, Bool.and_eq_true] at hb
    simp only [BExpr.eval, U64Expr.eval_congr h locals idx x hb.1,
      U64Expr.eval_congr h locals idx y hb.2]
  | .lt x y, hb => by
    simp only [BExpr.envBound, Bool.and_eq_true] at hb
    simp only [BExpr.eval, U64Expr.eval_congr h locals idx x hb.1,
      U64Expr.eval_congr h locals idx y hb.2]
  | .flt x y, hb => by
    simp only [BExpr.envBound, Bool.and_eq_true] at hb
    simp only [BExpr.eval, FExpr.eval_congr h locals idx x hb.1,
      FExpr.eval_congr h locals idx y hb.2]
  | .bit x _, hb => by
    simp only [BExpr.envBound] at hb
    simp only [BExpr.eval, FExpr.eval_congr h locals idx x hb]
  | .not b, hb => by
    simp only [BExpr.envBound] at hb
    simp only [BExpr.eval, BExpr.eval_congr h locals idx b hb]
  | .and x y, hb => by
    simp only [BExpr.envBound, Bool.and_eq_true] at hb
    simp only [BExpr.eval, BExpr.eval_congr h locals idx x hb.1,
      BExpr.eval_congr h locals idx y hb.2]

end

/-- Environment-bounded `let`-steps produce the same locals in two environments that
agree below `N`. -/
theorem evalSteps_congr {N : ℕ} {env env' : ProverEnvironment F}
    (h : env.AgreesBelow N env') :
    ∀ (steps : List (Step F)) (locals : Array (F ⊕ UInt64)),
      steps.all (Step.envBound N) = true →
      evalSteps env steps locals = evalSteps env' steps locals
  | [], _, _ => rfl
  | .letF e :: steps, locals, hb => by
    simp only [List.all_cons, Bool.and_eq_true, Step.envBound] at hb
    simp only [evalSteps]
    rw [FExpr.eval_congr h locals 0 e hb.1]
    exact evalSteps_congr h steps _ hb.2
  | .letU e :: steps, locals, hb => by
    simp only [List.all_cons, Bool.and_eq_true, Step.envBound] at hb
    simp only [evalSteps]
    rw [U64Expr.eval_congr h locals 0 e hb.1]
    exact evalSteps_congr h steps _ hb.2

/-- Environment-bounded vector outputs only access `env.get` below `N` (in
particular, `envRange offset` reads cells `offset .. offset + n - 1 < N`). -/
theorem VExpr.eval_congr {N : ℕ} {env env' : ProverEnvironment F}
    (h : env.AgreesBelow N env') (locals : Array (F ⊕ UInt64)) (idx : ℕ) :
    ∀ {n : ℕ} (v : VExpr F n), VExpr.envBound N v = true →
      VExpr.eval { env := env, locals, idx } v = VExpr.eval { env := env', locals, idx } v
  | _, .lit es, hb => by
    simp only [VExpr.envBound, List.all_eq_true] at hb
    simp only [VExpr.eval]
    ext i hi
    simp only [Vector.getElem_map]
    exact FExpr.eval_congr h locals idx es[i] (hb es[i] (by simp))
  | _, .mapRange n body, hb => by
    simp only [VExpr.envBound] at hb
    simp only [VExpr.eval]
    ext i hi
    simp only [Vector.getElem_mapRange]
    exact FExpr.eval_congr h locals i body hb
  | n, .envRange offset, hb => by
    simp only [VExpr.envBound, decide_eq_true_eq] at hb
    simp only [VExpr.eval]
    ext i hi
    simp only [Vector.getElem_mapRange]
    exact h (offset + i) (by omega)
  | n, .bitsOf x, hb => by
    simp only [VExpr.envBound] at hb
    simp only [VExpr.eval, FExpr.eval_congr h locals idx x hb]
  | _, .append a b, hb => by
    simp only [VExpr.envBound, Bool.and_eq_true] at hb
    simp only [VExpr.eval, VExpr.eval_congr h locals idx a hb.1,
      VExpr.eval_congr h locals idx b hb.2]

/-- Evaluation congruence for whole witness programs: an environment-bounded
witness program evaluates equally in two environments that agree below `N`.
`envBound` rejects `native` closures, so only structured programs — whose every
environment access is an `env.get` below `N` — remain. -/
theorem WitgenIR.eval_congr {m N : ℕ} {ir : WitgenIR F m}
    (hb : WitgenIR.envBound N ir = true) {env env' : ProverEnvironment F}
    (h : env.AgreesBelow N env') : ir.eval env = ir.eval env' := by
  cases ir with
  | native f => simp [WitgenIR.envBound] at hb
  | ir steps out =>
    simp only [WitgenIR.envBound, Bool.and_eq_true] at hb
    simp only [Witgen.WitgenIR.eval]
    rw [evalSteps_congr h steps #[] hb.1]
    exact VExpr.eval_congr h _ 0 out hb.2
  | certified f steps out hcert =>
    -- `eval` is the native closure `f`; the packed equivalence rewrites both sides
    -- to the IR reimplementation's evaluation, on which the per-sort congruence
    -- lemmas apply (`envBound` checks the IR fields, which is exactly what they
    -- need)
    show f env = f env'
    simp only [WitgenIR.envBound, Bool.and_eq_true] at hb
    rw [hcert env, hcert env']
    rw [evalSteps_congr h steps #[] hb.1]
    exact VExpr.eval_congr h _ 0 out hb.2

/-! ## The bridge -/

/-- A witness program passing `compilable` and `envBound N` only accesses the
environment below `N`. These are the checks `compile N` certifies
(`compile_checks`), so every program the compiler accepts discharges
`OnlyAccessedBelow`.

The `compilable` hypothesis is taken to match those checks, but `envBound` alone
carries the proof: it too returns `false` on every constructor whose evaluation reads
more than `env.get`. -/
theorem WitgenIR.onlyAccessedBelow_of_checks {m N : ℕ} {ir : WitgenIR F m}
    (_hc : WitgenIR.compilable ir = true) (hb : WitgenIR.envBound N ir = true) :
    ProverEnvironment.OnlyAccessedBelow N ir.eval := by
  intro _ _ h
  exact WitgenIR.eval_congr hb h

/-- Native-closure discharge: a certified IR implementation of a native witness
closure discharges the computability condition for the closure itself. If `f` agrees
with the evaluation of a checked IR program on every environment, then `f` only
accesses the environment below `N`. -/
theorem onlyAccessedBelow_of_ir_equiv {m N : ℕ} {f : ProverEnvironment F → Vector F m}
    {ir : WitgenIR F m} (_hc : WitgenIR.compilable ir = true)
    (hb : WitgenIR.envBound N ir = true) (h : ∀ env, f env = ir.eval env) :
    ProverEnvironment.OnlyAccessedBelow N f := by
  intro env env' hagree
  rw [h env, h env']
  exact WitgenIR.eval_congr hb hagree

/-- The `.certified` form of the native-closure discharge: a certified witness
program's checks (which run on its IR reimplementation) certify computability for
the native closure itself, the closure's fast evaluation path, not just the IR.
This is `onlyAccessedBelow_of_ir_equiv` with the equivalence read off the
constructor; equivalently, `WitgenIR.onlyAccessedBelow_of_checks` already covers
certified programs since `eval (certified f ..) = f`. -/
theorem onlyAccessedBelow_certified {m N : ℕ} {f : ProverEnvironment F → Vector F m}
    {steps : List (Step F)} {out : VExpr F m}
    {h : ∀ env, f env = (WitgenIR.ir steps out).eval env}
    (hc : WitgenIR.compilable (WitgenIR.certified f steps out h) = true)
    (hb : WitgenIR.envBound N (WitgenIR.certified f steps out h) = true) :
    ProverEnvironment.OnlyAccessedBelow N f :=
  onlyAccessedBelow_of_ir_equiv (ir := WitgenIR.ir steps out) hc hb h

/-! ## Whole-circuit discharge

`Operations.ComputableWitnesses` is per-offset: the generator at offset `n` must only
access the environment below `n`. `computableChecks` runs the compiler's checks on
every witness generator of a flat operation list *at that generator's own offset*, so
one boolean evaluation certifies the whole circuit. -/

/-- Decidable computability check for a flat operation list starting at offset `n`:
every witness generator passes `compilable` and `envBound` at its own offset.
Certified witness operations (`WitgenIR.certified`) are accepted: the two
checks run on their IR reimplementation, and `WitgenIR.eval_congr` transports the
conclusion to the native closure their `eval` runs. -/
def computableChecks (n : ℕ) : List (FlatOperation F) → Bool
  | [] => true
  | .witness m c :: ops =>
    WitgenIR.compilable c && WitgenIR.envBound n c && computableChecks (m + n) ops
  | .assert _ :: ops => computableChecks n ops
  | .lookup _ :: ops => computableChecks n ops
  | .interact _ :: ops => computableChecks n ops

/-- The flat-list form of the bridge: `computableChecks` implies the
computable-witnesses condition for every witness generator, at its offset. -/
theorem forAllComputable_of_checks (env env' : ProverEnvironment F) :
    ∀ (ops : List (FlatOperation F)) (n : ℕ), computableChecks n ops = true →
      FlatOperation.forAll n {
        witness n _ compute :=
          env.AgreesBelow n env' → compute.eval env = compute.eval env' } ops
  | [], _, _ => trivial
  | .witness m c :: ops, n, hchecks => by
    simp only [computableChecks, Bool.and_eq_true] at hchecks
    exact ⟨fun hA => WitgenIR.eval_congr hchecks.1.2 hA,
      forAllComputable_of_checks env env' ops (m + n) hchecks.2⟩
  | .assert _ :: ops, n, hchecks => by
    simp only [computableChecks] at hchecks
    exact ⟨trivial, forAllComputable_of_checks env env' ops n hchecks⟩
  | .lookup _ :: ops, n, hchecks => by
    simp only [computableChecks] at hchecks
    exact ⟨trivial, forAllComputable_of_checks env env' ops n hchecks⟩
  | .interact _ :: ops, n, hchecks => by
    simp only [computableChecks] at hchecks
    exact ⟨trivial, forAllComputable_of_checks env env' ops n hchecks⟩

/-- The `Operations` form of the bridge, via flattening. -/
theorem operations_computableWitnesses_of_checks {ops : Operations F} {n : ℕ}
    (h : computableChecks n ops.toFlat = true) (env env' : ProverEnvironment F) :
    ops.ComputableWitnesses n env env' := by
  simp only [Operations.ComputableWitnesses, ← Operations.forAll_toFlat_iff]
  exact forAllComputable_of_checks env env' ops.toFlat n h

/-- Whole-circuit discharge: one boolean evaluation of `computableChecks` over a
circuit's flat operations certifies `Circuit.ComputableWitnesses` — no manual trace
reasoning. The offset alignment is built in: the check runs each generator's
`envBound` at that generator's own offset. -/
theorem circuit_computableWitnesses_of_checks {α : Type} {circuit : Circuit F α}
    {n : ℕ} (h : computableChecks n ((circuit.operations n).toFlat) = true) :
    circuit.ComputableWitnesses n :=
  fun env env' => operations_computableWitnesses_of_checks h env env'

/-! ## The payoff, demonstrated

The `IsZeroField` circuit at input `var ⟨0⟩` and offset 1: its first generator sits at
offset 1 and reads only cell 0, the `<==` copy generator sits at offset 2 and reads
cells 0 and 1 — the per-offset alignment `ComputableWitnesses` demands. Both
obligations and the whole-circuit condition are discharged by the bridge plus
`native_decide`; the checks are well-founded mutual recursions, which `decide`'s
kernel reduction cannot evaluate. -/

/-- The circuit's first witness generator (offset 1, reads cell 0). -/
example : ProverEnvironment.OnlyAccessedBelow 1 (testIsZero.eval) :=
  WitgenIR.onlyAccessedBelow_of_checks (by native_decide) (by native_decide)

/-- The circuit's second witness generator, the `<==` copy for its output `b`
(offset 2, reads cells 0 and 1 — `envBound 1` would fail, `envBound 2` passes). -/
example : ProverEnvironment.OnlyAccessedBelow 2 (isZeroCircuitCopyIR.eval) :=
  WitgenIR.onlyAccessedBelow_of_checks (by native_decide) (by native_decide)

/-- Whole-circuit computability for the instantiated `IsZeroField` circuit, by one
boolean evaluation. -/
example : Circuit.ComputableWitnesses (F := Fb)
    (Gadgets.IsZeroField.circuit.main (var ⟨0⟩)) 1 :=
  circuit_computableWitnesses_of_checks (by native_decide)

/-- The same discharge pattern on `Addition8FullCarry` — the gadget whose
`LookupCircuit.computableWitnesses` field is proved by hand — instantiated at inputs
`var ⟨0⟩`/`var ⟨1⟩`/`var ⟨2⟩` and offset 3: the `z` generator (offset 3) and the
carry generator (offset 4) both read only the three input cells. -/
example : Circuit.ComputableWitnesses (F := Fb)
    (Gadgets.Addition8FullCarry.main ⟨var ⟨0⟩, var ⟨1⟩, var ⟨2⟩⟩) 3 :=
  circuit_computableWitnesses_of_checks (by native_decide)

/-! ### Certified native witnesses

The checks run on the IR reimplementation, yet certify `OnlyAccessedBelow` for the
bare closure `isZeroNative` — a statement about an arbitrary Lean function that no
syntactic check could establish directly. -/

/-- The bare closure only accesses the environment below 1 — via its certified IR
equivalent. -/
example : ProverEnvironment.OnlyAccessedBelow 1 isZeroNative :=
  onlyAccessedBelow_of_ir_equiv (ir := testIsZero) (by native_decide) (by native_decide)
    isZeroNative_eq_testIsZero

/-- The same fact through the generic checks-form on the certified program itself
(`eval isZeroCertified` *is* `isZeroNative`). -/
example : ProverEnvironment.OnlyAccessedBelow 1 (isZeroCertified.eval) :=
  WitgenIR.onlyAccessedBelow_of_checks (by native_decide) (by native_decide)

end Caliper.WitgenCompile
