import Clean.Gadgets.SHA256.AddMod32
import Clean.Gadgets.SHA256.Ch32

section
variable {p : ℕ} [Fact p.Prime] [h_large : Fact (p > 2^35)]

namespace Gadgets.SHA256

/-!
# Fused choice function + multi-operand 32-bit modular addition

Computes `(Σ_j ops_j + Ch(e, f, g) + cst) mod 2^32` in one gadget.  The SHA-256 round
consumes the choice word `Ch(e, f, g)` only as a summand of the e-add, so fusing the two
saves one witness and one constraint versus `Ch32` followed by `AddMod32`:

* the choice bits `0..30` are realised as witnessed products `m_i = e_i·(f_i − g_i)`
  (the choice bit itself is the affine combination `g_i + m_i`, never materialised), and
* the choice bit 31's product `e_31·(f_31 − g_31)` is inlined into the final sum
  constraint — an R1CS row may carry one product, and the sum row of a plain `AddMod32`
  carries none, so the row absorbs the product *and* the last witness for free.

R1CS structure (per call):
- 31 witnesses for the choice products `m[0..30]`, 32 witnesses for output bits
  `z[0..31]`, `cw` witnesses for carry bits `c[0..cw-1]`
- 31 product constraints `m_i = e_i·(f_i − g_i)`, 32 + `cw` boolean constraints
- 1 fused constraint:
  `Σ_j valueBits(op_j) + Σ_i 2^i·ch_i + cst = valueBits(z) + 2^32·Σ_i 2^i·c[i]`
  where `ch_i = g_i + m_i` for `i ≤ 30` and `ch_31 = g_31 + e_31·(f_31 − g_31)` inline.

Total: `63 + cw` witnesses and `64 + cw` constraints, versus `64 + cw` and `65 + cw` for
`Ch32` + `AddMod32`.

The carry width `cw` need only satisfy `(n+1)·(2^32 − 1) + cst < 2^(32+cw)` (the choice
word contributes at most `2^32 − 1`, like an extra operand).  Soundness needs `p > 2^35`
exactly as for `AddMod32`.
-/

variable {n cw cst : ℕ} [NeZero cw]
  [hb : Fact ((n + 1) * (2^32 - 1) + cst < 2^(32 + cw))] [hcw : Fact (cw ≤ 3)]

/-- ℕ value of the choice word `Ch(e,f,g)`, computed bitwise from the prover environment. -/
def chBitsNat (env : ProverEnvironment (F p)) (e f g : Var (fields 32) (F p)) : ℕ :=
  Finset.univ.sum fun (i : Fin 32) =>
    (env g[i] + env e[i] * (env f[i] - env g[i])).val * 2^i.val

/-- The choice-word bits as expressions: bits `0..30` use the witnessed products `m`,
bit 31 inlines its product (the only product of the fused constraint row). -/
def chBitsVar (e f g : Var (fields 32) (F p)) (m : Var (fields 31) (F p)) :
    Var (fields 32) (F p) :=
  Vector.ofFn fun (i : Fin 32) =>
    if h : i.val < 31 then g[i.val] + m[i.val] else g[31] + e[31] * (f[31] - g[31])

/-- Add `n` 32-bit words plus the choice word `Ch(e,f,g)` plus the constant `cst`
mod `2^32` (single reduction with a `cw`-bit carry, sum row fused with `Ch`'s bit 31). -/
def chAddMod32 (e f g : Var (fields 32) (F p))
    (ops : Vector (Var (fields 32) (F p)) n) :
    Circuit (F p) (Var (fields 32) (F p)) := do
  let m ← witnessVector 31 fun env =>
    Vector.ofFn fun (i : Fin 31) =>
      env e[i.val] * (env f[i.val] - env g[i.val])
  let z ← witnessVector 32 fun env =>
    let s := (sumBitsNat env ops + chBitsNat env e f g + cst) % 2^32
    Vector.ofFn fun (i : Fin 32) => ((s / 2^i.val % 2 : ℕ) : F p)
  let c ← witnessVector cw fun env =>
    let s := sumBitsNat env ops + chBitsNat env e f g + cst
    Vector.ofFn fun (i : Fin cw) => ((s / 2^32 / 2^i.val % 2 : ℕ) : F p)
  Circuit.forEach (Vector.finRange 31) fun i =>
    assertZero (m[i] - e[i.val] * (f[i.val] - g[i.val]))
  Circuit.forEach (Vector.finRange 32) fun i =>
    assertZero (z[i] * (z[i] - 1))
  Circuit.forEach (Vector.finRange cw) fun i =>
    assertZero (c[i] * (c[i] - 1))
  assertZero (sumExpr ops + fromBitsExpr (chBitsVar e f g m) + ((cst : F p) : Expression (F p))
    - fromBitsExpr z - (2^32 : F p) * carryExpr c)
  return z

namespace ChAddMod32

structure Inputs (n : ℕ) (F : Type) where
  e : fields 32 F
  f : fields 32 F
  g : fields 32 F
  ops : ProvableVector (fields 32) n F
deriving ProvableStruct

def main (input : Var (Inputs n) (F p)) : Circuit (F p) (Var (fields 32) (F p)) :=
  chAddMod32 (cw := cw) (cst := cst) input.e input.f input.g input.ops

-- `cw` and `cst` are not determined by the input/output types, so this is a plain `def`;
-- `circuit` below wires them in explicitly.
def elaborated : ElaboratedCircuit (F p) (Inputs n) (fields 32) where
  main := main (cw := cw) (cst := cst)
  localLength _ := 63 + cw
  output _ i0 := varFromOffset (fields 32) (i0 + 31)
  localLength_eq _ _ := by
    simp +arith only [circuit_norm, main, chAddMod32, Nat.mul_zero, Nat.add_zero]
  output_eq _ _ := rfl
  subcircuitsConsistent _ _ := by simp +arith only [circuit_norm, main, chAddMod32]
  channelsLawful := by intro x i; simp +arith only [circuit_norm, main, chAddMod32]

/-- The choice inputs and all summand operands are normalized. -/
def Assumptions (input : Inputs n (F p)) : Prop :=
  Normalized input.e ∧ Normalized input.f ∧ Normalized input.g ∧
    ∀ j : Fin n, Normalized input.ops[j]

/-- The output is `(Σ ops + Ch(e,f,g) + cst) mod 2^32`, and is normalized. -/
def Spec (input : Inputs n (F p)) (z : fields 32 (F p)) : Prop :=
  valueBits z = (opsValueSum input.ops +
    Specs.SHA256.Ch (valueBits input.e) (valueBits input.f) (valueBits input.g) + cst) % 2^32
  ∧ Normalized z

/-!
## Helper lemmas
-/

omit h_large hcw [NeZero cw] in
/-- The operand sum is at most `n` maximal words. -/
private lemma opsValueSum_le (ops : ProvableVector (fields 32) n (F p))
    (h : ∀ j : Fin n, Normalized ops[j]) :
    opsValueSum ops ≤ n * (2^32 - 1) := by
  have h_each_le : ∀ j : Fin n, valueBits ops[j] ≤ 2^32 - 1 := by
    intro j
    have hlt := AddMod32.valueBits_lt_two_pow ops[j] (h j)
    omega
  unfold opsValueSum
  calc
    ∑ j : Fin n, valueBits ops[j] ≤ ∑ _j : Fin n, (2^32 - 1) := by
      apply Finset.sum_le_sum
      intro j _
      exact h_each_le j
    _ = n * (2^32 - 1) := by simp

/-- The value-level choice word: bit `i` is `g_i + e_i·(f_i − g_i)`. -/
private def chWord (e f g : fields 32 (F p)) : fields 32 (F p) :=
  Vector.ofFn fun (i : Fin 32) => g[i] + e[i] * (f[i] - g[i])

omit h_large in
/-- The choice word satisfies `Ch32`'s spec: its value is `Ch` and it is normalized. -/
private lemma chWord_spec (e f g : fields 32 (F p))
    (he : Normalized e) (hf : Normalized f) (hg : Normalized g) :
    valueBits (chWord e f g) =
      Specs.SHA256.Ch (valueBits e) (valueBits f) (valueBits g) ∧
    Normalized (chWord e f g) := by
  apply Ch32.spec_of_constraint e f g (chWord e f g) he hf hg
  intro i
  simp [chWord, Vector.getElem_ofFn]

omit h_large in
/-- Evaluating `chBitsVar` under an environment where the product witnesses are correct
gives exactly the value-level choice word. -/
private lemma chBitsVar_eval (env : Environment (F p))
    (e_var f_var g_var : Var (fields 32) (F p)) (m_var : Var (fields 31) (F p))
    (e f g : fields 32 (F p))
    (h_e : ∀ (i : ℕ) (hi : i < 32), Expression.eval env (e_var[i]'hi) = e[i]'hi)
    (h_f : ∀ (i : ℕ) (hi : i < 32), Expression.eval env (f_var[i]'hi) = f[i]'hi)
    (h_g : ∀ (i : ℕ) (hi : i < 32), Expression.eval env (g_var[i]'hi) = g[i]'hi)
    (h_m : ∀ (i : ℕ) (hi : i < 31), Expression.eval env (m_var[i]'hi) =
      (e[i]'(by omega)) * ((f[i]'(by omega)) - (g[i]'(by omega)))) :
    Vector.map (Expression.eval env) (chBitsVar e_var f_var g_var m_var) = chWord e f g := by
  ext i hi
  simp only [chBitsVar, chWord, Vector.getElem_map, Vector.getElem_ofFn, Fin.getElem_fin]
  by_cases h31 : i < 31
  · simp only [dif_pos h31, circuit_norm]
    rw [h_g i hi, h_m i h31]
  · simp only [dif_neg h31, circuit_norm]
    have hi31 : i = 31 := by omega
    subst hi31
    rw [h_e 31 hi, h_f 31 hi, h_g 31 hi]
    ring

/-!
## Soundness
-/

theorem soundness : Soundness (Input := Inputs n) (Output := fields 32)
    (F p) (elaborated (n:=n) (cw:=cw) (cst:=cst)) (Assumptions (n:=n)) (Spec (n:=n) (cst:=cst)) := by
  circuit_proof_start [chAddMod32]
  obtain ⟨h_e_norm, h_f_norm, h_g_norm, h_ops_norm⟩ := h_assumptions
  have h_in_e : Vector.map (Expression.eval env) input_var.e = input.e :=
    congrArg Inputs.e h_input
  have h_in_f : Vector.map (Expression.eval env) input_var.f = input.f :=
    congrArg Inputs.f h_input
  have h_in_g : Vector.map (Expression.eval env) input_var.g = input.g :=
    congrArg Inputs.g h_input
  have h_in_ops : eval env input_var.ops = input.ops :=
    congrArg Inputs.ops h_input
  obtain ⟨h_m, h_z_bool, h_c_bool, h_lin⟩ := h_holds
  -- Pointwise evaluation of the three choice inputs.
  have h_ei : ∀ (i : ℕ) (hi : i < 32),
      Expression.eval env (input_var.e[i]'hi) = input.e[i]'hi := by
    intro i hi
    have := Vector.ext_iff.mp h_in_e i hi
    simp [Vector.getElem_map] at this
    exact this
  have h_fi : ∀ (i : ℕ) (hi : i < 32),
      Expression.eval env (input_var.f[i]'hi) = input.f[i]'hi := by
    intro i hi
    have := Vector.ext_iff.mp h_in_f i hi
    simp [Vector.getElem_map] at this
    exact this
  have h_gi : ∀ (i : ℕ) (hi : i < 32),
      Expression.eval env (input_var.g[i]'hi) = input.g[i]'hi := by
    intro i hi
    have := Vector.ext_iff.mp h_in_g i hi
    simp [Vector.getElem_map] at this
    exact this
  -- The product rows pin the choice products m[0..30].
  have h_m_val : ∀ (i : ℕ) (hi : i < 31), env.get (i₀ + i) =
      (input.e[i]'(by omega)) * ((input.f[i]'(by omega)) - (input.g[i]'(by omega))) := by
    intro i hi
    have h := h_m ⟨i, hi⟩
    rw [h_ei i (by omega), h_fi i (by omega), h_gi i (by omega)] at h
    have key : env.get (i₀ + i) -
        (input.e[i]'(by omega)) * ((input.f[i]'(by omega)) - (input.g[i]'(by omega))) = 0 := by
      ring_nf
      ring_nf at h
      exact h
    exact sub_eq_zero.mp key
  -- The boolean rows give normalization of z and c.
  have h_z_norm : Normalized (Vector.ofFn fun i : Fin 32 => env.get (i₀ + 31 + i.val)) :=
    AddMod32.normalized_of_bool_holds env (i₀ + 31) h_z_bool
  have h_c_norm : ∀ i : Fin cw,
      (Vector.ofFn fun j : Fin cw => env.get (i₀ + 31 + 32 + j.val))[i] = 0 ∨
      (Vector.ofFn fun j : Fin cw => env.get (i₀ + 31 + 32 + j.val))[i] = 1 :=
    AddMod32.bools_of_bool_holds env (i₀ + 31 + 32) h_c_bool
  -- The choice word: spec value and normalization.
  obtain ⟨h_ch_val, h_ch_norm⟩ := chWord_spec input.e input.f input.g h_e_norm h_f_norm h_g_norm
  -- Bounds for the ℕ-lift of the fused constraint.
  have h_p_large := h_large.elim
  have h_32cw_le : (2:ℕ)^(32 + cw) ≤ 2^35 := AddMod32.two_pow_32cw_le (cw := cw)
  have h_pow_split : (2:ℕ)^(32 + cw) = 2^32 * 2^cw := pow_add 2 32 cw
  have hp32 : (2:ℕ)^32 < p := by omega
  have hpc : (2:ℕ)^cw < p := by
    have h1 : (2:ℕ)^cw ≤ 2^(32 + cw) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  set z : fields 32 (F p) := Vector.ofFn fun i : Fin 32 => env.get (i₀ + 31 + i.val) with hz_def
  set c : fields cw (F p) :=
    Vector.ofFn fun i : Fin cw => env.get (i₀ + 31 + 32 + i.val) with hc_def
  set vz := valueBits z with hvz_def
  set vc := AddMod32.bitsValue c with hvc_def
  have h_chv_lt : valueBits (chWord input.e input.f input.g) < 2^32 :=
    AddMod32.valueBits_lt_two_pow _ h_ch_norm
  have h_total_bound : opsValueSum input.ops +
      valueBits (chWord input.e input.f input.g) + cst < 2^(32 + cw) := by
    have h1 := opsValueSum_le input.ops h_ops_norm
    have h2 : (n + 1) * (2^32 - 1) + cst < 2^(32 + cw) := hb.elim
    have h3 : (n + 1) * (2^32 - 1) = n * (2^32 - 1) + (2^32 - 1) := by ring
    omega
  have h_total_lt_p : opsValueSum input.ops +
      valueBits (chWord input.e input.f input.g) + cst < p := by omega
  have hvz_lt : vz < 2^32 := AddMod32.valueBits_lt_two_pow z (by simpa [z] using h_z_norm)
  have hvc_lt : vc < 2^cw := AddMod32.bitsValue_lt_two_pow c (by simpa [c] using h_c_norm)
  -- Evaluate each piece of the fused constraint.
  have h_sum_eval : Expression.eval env (sumExpr input_var.ops) =
      ((opsValueSum input.ops : ℕ) : F p) :=
    AddMod32.sumExpr_eval_eq env input_var.ops input.ops h_in_ops
  have h_mi : ∀ (i : ℕ) (hi : i < 31), Expression.eval env
      ((Vector.mapRange 31 fun i => (var {index := i₀ + i} : Expression (F p)))[i]'hi) =
      (input.e[i]'(by omega)) * ((input.f[i]'(by omega)) - (input.g[i]'(by omega))) := by
    intro i hi
    simp only [Vector.getElem_mapRange, Expression.eval]
    exact h_m_val i hi
  have h_ch_eval : Vector.map (Expression.eval env)
      (chBitsVar input_var.e input_var.f input_var.g
        (Vector.mapRange 31 fun i => (var {index := i₀ + i} : Expression (F p)))) =
      chWord input.e input.f input.g :=
    chBitsVar_eval env _ _ _ _ _ _ _ h_ei h_fi h_gi h_mi
  have h_ch_expr : Expression.eval env (fromBitsExpr
      (chBitsVar input_var.e input_var.f input_var.g
        (Vector.mapRange 31 fun i => (var {index := i₀ + i} : Expression (F p))))) =
      ((valueBits (chWord input.e input.f input.g) : ℕ) : F p) := by
    rw [AddMod32.fromBitsExpr_eval_bitsValue env _ _ h_ch_eval,
      AddMod32.bitsValue_eq_valueBits]
  have h_z_eval : Vector.map (Expression.eval env)
      (Vector.mapRange 32 fun i => (var {index := i₀ + 31 + i} : Expression (F p))) = z :=
    AddMod32.var_vector_eval env 32 (i₀ + 31)
  have h_fz : (Expression.eval env (fromBitsExpr
      (Vector.mapRange 32 fun i => (var {index := i₀ + 31 + i} : Expression (F p))))).val = vz :=
    AddMod32.fromBitsExpr_val_eq env _ z h_z_eval (by simpa [z] using h_z_norm) hp32
  have h_c_eval : Vector.map (Expression.eval env)
      (Vector.mapRange cw fun i => (var {index := i₀ + 31 + 32 + i} : Expression (F p))) = c :=
    AddMod32.var_vector_eval env cw (i₀ + 31 + 32)
  have h_fc : (Expression.eval env (carryExpr
      (Vector.mapRange cw fun i => (var {index := i₀ + 31 + 32 + i} : Expression (F p))))).val
      = vc :=
    AddMod32.carryExpr_val_eq env _ c h_c_eval (by simpa [c] using h_c_norm) hpc
  have h_pow32_val : (2^32 : F p).val = 2^32 := by
    have hcast : ((2^32 : ℕ) : F p) = (2^32 : F p) := by push_cast; ring
    rw [← hcast, ZMod.val_natCast_of_lt hp32]
  -- Rearranged fused constraint.
  have h_lin' : Expression.eval env (sumExpr input_var.ops) +
      Expression.eval env (fromBitsExpr
        (chBitsVar input_var.e input_var.f input_var.g
          (Vector.mapRange 31 fun i => (var {index := i₀ + i} : Expression (F p))))) +
      (cst : F p) =
      Expression.eval env (fromBitsExpr
        (Vector.mapRange 32 fun i => (var {index := i₀ + 31 + i} : Expression (F p)))) +
      (2^32 : F p) * Expression.eval env (carryExpr
        (Vector.mapRange cw fun i => (var {index := i₀ + 31 + 32 + i} : Expression (F p)))) := by
    rw [← sub_eq_zero]
    rw [show ∀ A B C D E : F p, A + B + C - (D + E) = A + B + C + -D + -E from by intros; ring]
    exact h_lin
  -- Lift to ℕ and conclude.
  have h_lhs_val : (Expression.eval env (sumExpr input_var.ops) +
      Expression.eval env (fromBitsExpr
        (chBitsVar input_var.e input_var.f input_var.g
          (Vector.mapRange 31 fun i => (var {index := i₀ + i} : Expression (F p))))) +
      (cst : F p)).val =
      opsValueSum input.ops + valueBits (chWord input.e input.f input.g) + cst := by
    have h_cast : Expression.eval env (sumExpr input_var.ops) +
        Expression.eval env (fromBitsExpr
          (chBitsVar input_var.e input_var.f input_var.g
            (Vector.mapRange 31 fun i => (var {index := i₀ + i} : Expression (F p))))) +
        (cst : F p) =
        ((opsValueSum input.ops + valueBits (chWord input.e input.f input.g) + cst : ℕ) : F p) := by
      rw [h_sum_eval, h_ch_expr]; push_cast; ring
    rw [h_cast]
    exact ZMod.val_natCast_of_lt h_total_lt_p
  have h_mul_lt : 2^32 * vc < p := by omega
  have h_rhs_lt : vz + 2^32 * vc < p := by omega
  have h_rhs_val : (Expression.eval env (fromBitsExpr
        (Vector.mapRange 32 fun i => (var {index := i₀ + 31 + i} : Expression (F p)))) +
      (2^32 : F p) * Expression.eval env (carryExpr
        (Vector.mapRange cw fun i =>
          (var {index := i₀ + 31 + 32 + i} : Expression (F p))))).val =
      vz + 2^32 * vc := by
    rw [ZMod.val_add, ZMod.val_mul, h_fz, h_pow32_val, h_fc]
    rw [Nat.mod_eq_of_lt h_mul_lt, Nat.mod_eq_of_lt h_rhs_lt]
  have h_nat_eq : opsValueSum input.ops + valueBits (chWord input.e input.f input.g) + cst =
      vz + 2^32 * vc := by
    have := congr_arg ZMod.val h_lin'
    rw [h_lhs_val, h_rhs_val] at this
    exact this
  rw [AddMod32.var_vector_eval env 32 (i₀ + 31)]
  refine ⟨?_, h_z_norm⟩
  show vz = (opsValueSum input.ops +
    Specs.SHA256.Ch (valueBits input.e) (valueBits input.f) (valueBits input.g) + cst) % 2^32
  rw [← h_ch_val, h_nat_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hvz_lt]

/-!
## Completeness
-/

omit hcw in
theorem completeness : Completeness (Input := Inputs n) (Output := fields 32)
    (F p) (elaborated (n:=n) (cw:=cw) (cst:=cst)) (Assumptions (n:=n)) := by
  circuit_proof_start [chAddMod32]
  obtain ⟨h_e_norm, h_f_norm, h_g_norm, h_ops_norm⟩ := h_assumptions
  have h_in_e : Vector.map (Expression.eval env.toEnvironment) input_var.e = input.e :=
    congrArg Inputs.e h_input
  have h_in_f : Vector.map (Expression.eval env.toEnvironment) input_var.f = input.f :=
    congrArg Inputs.f h_input
  have h_in_g : Vector.map (Expression.eval env.toEnvironment) input_var.g = input.g :=
    congrArg Inputs.g h_input
  have h_in_ops : eval env.toEnvironment input_var.ops = input.ops :=
    congrArg Inputs.ops h_input
  obtain ⟨h_env_m, h_env_z, h_env_c⟩ := h_env
  obtain ⟨h_env_c, -⟩ := h_env_c
  have h_ei : ∀ (i : ℕ) (hi : i < 32),
      Expression.eval env.toEnvironment (input_var.e[i]'hi) = input.e[i]'hi := by
    intro i hi
    have := Vector.ext_iff.mp h_in_e i hi
    simp [Vector.getElem_map] at this
    exact this
  have h_fi : ∀ (i : ℕ) (hi : i < 32),
      Expression.eval env.toEnvironment (input_var.f[i]'hi) = input.f[i]'hi := by
    intro i hi
    have := Vector.ext_iff.mp h_in_f i hi
    simp [Vector.getElem_map] at this
    exact this
  have h_gi : ∀ (i : ℕ) (hi : i < 32),
      Expression.eval env.toEnvironment (input_var.g[i]'hi) = input.g[i]'hi := by
    intro i hi
    have := Vector.ext_iff.mp h_in_g i hi
    simp [Vector.getElem_map] at this
    exact this
  set S := sumBitsNat env input_var.ops + chBitsNat env input_var.e input_var.f input_var.g + cst
    with hS_def
  have h_in_env : eval env.toEnvironment input_var.ops = input.ops := by
    simpa [CircuitType.eval_expression_prover] using h_in_ops
  -- The choice-word ℕ value agrees with the value-level choice word.
  have h_ch_nat : chBitsNat env input_var.e input_var.f input_var.g =
      valueBits (chWord input.e input.f input.g) := by
    unfold chBitsNat valueBits chWord
    apply Finset.sum_congr rfl
    intro i _
    simp only [Vector.getElem_ofFn, Fin.getElem_fin]
    congr 2
    show Expression.eval env.toEnvironment _ + Expression.eval env.toEnvironment _ *
      (Expression.eval env.toEnvironment _ - Expression.eval env.toEnvironment _) = _
    rw [h_ei i.val i.isLt, h_fi i.val i.isLt, h_gi i.val i.isLt]
  obtain ⟨h_ch_val, h_ch_norm⟩ := chWord_spec input.e input.f input.g h_e_norm h_f_norm h_g_norm
  have hS_eq : S = opsValueSum input.ops + valueBits (chWord input.e input.f input.g) + cst := by
    rw [hS_def, AddMod32.sumBitsNat_eq_opsValueSum env input_var.ops input.ops h_in_env,
      h_ch_nat]
  have h_p_large := h_large.elim
  have hp32 : (2:ℕ)^32 < p := by omega
  have hp2 : 2 < p := by omega
  have h_S_mod_lt : S % 2^32 < 2^32 := Nat.mod_lt _ (by norm_num)
  have h_div_lt : S / 2^32 < 2^cw := by
    have h1 := opsValueSum_le input.ops h_ops_norm
    have h2 : valueBits (chWord input.e input.f input.g) < 2^32 :=
      AddMod32.valueBits_lt_two_pow _ h_ch_norm
    have h3 : (n + 1) * (2^32 - 1) + cst < 2^(32 + cw) := hb.elim
    have h4 : (n + 1) * (2^32 - 1) = n * (2^32 - 1) + (2^32 - 1) := by ring
    apply (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2^32)).mpr
    have h5 : (2:ℕ)^(32 + cw) = 2^cw * 2^32 := by rw [pow_add]; ring
    omega
  have hS_decomp : S = S % 2^32 + 2^32 * (S / 2^32) :=
    (Nat.mod_add_div S (2^32)).symm.trans (by ring)
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, ?_⟩
  · -- product constraints m_i = e_i (f_i − g_i)
    have henv_i := h_env_m i
    simp only [Vector.getElem_ofFn] at henv_i
    rw [henv_i, h_ei i.val (by omega), h_fi i.val (by omega), h_gi i.val (by omega)]
    ring
  · -- booleanity of z
    have henv_i := h_env_z i
    simp only [Vector.getElem_ofFn] at henv_i
    rw [henv_i]
    rcases Nat.mod_two_eq_zero_or_one (S % 2^32 / 2^i.val) with h | h <;>
      rw [h] <;> push_cast <;> ring
  · -- booleanity of c
    have henv_i := h_env_c i
    simp only [Vector.getElem_ofFn] at henv_i
    rw [henv_i]
    rcases Nat.mod_two_eq_zero_or_one (S / 2^32 / 2^i.val) with h | h <;>
      rw [h] <;> push_cast <;> ring
  · -- the fused constraint row
    have h_sum_expr : Expression.eval env.toEnvironment (sumExpr input_var.ops) =
        ((opsValueSum input.ops : ℕ) : F p) :=
      AddMod32.sumExpr_eval_eq env.toEnvironment input_var.ops input.ops h_in_env
    have h_mi : ∀ (i : ℕ) (hi : i < 31), Expression.eval env.toEnvironment
        ((Vector.mapRange 31 fun i => (var {index := i₀ + i} : Expression (F p)))[i]'hi) =
        (input.e[i]'(by omega)) * ((input.f[i]'(by omega)) - (input.g[i]'(by omega))) := by
      intro i hi
      simp only [Vector.getElem_mapRange, Expression.eval]
      have henv_i := h_env_m ⟨i, hi⟩
      simp only [Vector.getElem_ofFn] at henv_i
      rw [henv_i, h_ei i (by omega), h_fi i (by omega), h_gi i (by omega)]
    have h_ch_eval : Vector.map (Expression.eval env.toEnvironment)
        (chBitsVar input_var.e input_var.f input_var.g
          (Vector.mapRange 31 fun i => (var {index := i₀ + i} : Expression (F p)))) =
        chWord input.e input.f input.g :=
      chBitsVar_eval env.toEnvironment _ _ _ _ _ _ _ h_ei h_fi h_gi h_mi
    have h_ch_expr : Expression.eval env.toEnvironment (fromBitsExpr
        (chBitsVar input_var.e input_var.f input_var.g
          (Vector.mapRange 31 fun i => (var {index := i₀ + i} : Expression (F p))))) =
        ((valueBits (chWord input.e input.f input.g) : ℕ) : F p) := by
      rw [AddMod32.fromBitsExpr_eval_bitsValue env.toEnvironment _ _ h_ch_eval,
        AddMod32.bitsValue_eq_valueBits]
    have h_z_eval : Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 32 fun i => (var {index := i₀ + 31 + i} : Expression (F p))) =
        Vector.ofFn fun i : Fin 32 => ((S % 2^32 / 2^i.val % 2 : ℕ) : F p) := by
      rw [AddMod32.var_vector_eval env.toEnvironment 32 (i₀ + 31)]
      ext i hi
      simp only [Vector.getElem_ofFn]
      have h := h_env_z ⟨i, hi⟩
      simp only [Vector.getElem_ofFn] at h
      exact h
    have h_fz : Expression.eval env.toEnvironment (fromBitsExpr
        (Vector.mapRange 32 fun i => (var {index := i₀ + 31 + i} : Expression (F p)))) =
        ((S % 2^32 : ℕ) : F p) := by
      change env.toEnvironment (Utils.Bits.fieldFromBitsExpr
        (Vector.mapRange 32 fun i => (var {index := i₀ + 31 + i} : Expression (F p)))) = _
      rw [Utils.Bits.fieldFromBits_eval, h_z_eval]
      exact AddMod32.fieldFromBits_bit_decomp 32 (S % 2^32) h_S_mod_lt hp2
    have h_c_eval : Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange cw fun i => (var {index := i₀ + 31 + 32 + i} : Expression (F p))) =
        Vector.ofFn fun i : Fin cw => ((S / 2^32 / 2^i.val % 2 : ℕ) : F p) := by
      rw [AddMod32.var_vector_eval env.toEnvironment cw (i₀ + 31 + 32)]
      ext i hi
      simp only [Vector.getElem_ofFn]
      have h := h_env_c ⟨i, hi⟩
      simp only [Vector.getElem_ofFn] at h
      exact h
    have h_fc : Expression.eval env.toEnvironment (carryExpr
        (Vector.mapRange cw fun i => (var {index := i₀ + 31 + 32 + i} : Expression (F p)))) =
        ((S / 2^32 : ℕ) : F p) := by
      rw [AddMod32.carryExpr_eval_bitsValue env.toEnvironment _ _ h_c_eval]
      rw [AddMod32.bitsValue_bit_decomp cw (S / 2^32) h_div_lt hp2]
    rw [h_sum_expr, h_ch_expr, h_fz, h_fc]
    have hnat : opsValueSum input.ops + valueBits (chWord input.e input.f input.g) + cst =
        S % 2^32 + 2^32 * (S / 2^32) := by
      rw [← hS_eq, ← hS_decomp]
    have hF : ((opsValueSum input.ops : ℕ) : F p) +
        ((valueBits (chWord input.e input.f input.g) : ℕ) : F p) + (cst : F p) =
        ((S % 2^32 : ℕ) : F p) + (2^32 : F p) * ((S / 2^32 : ℕ) : F p) := by
      have h := congr_arg (Nat.cast : ℕ → F p) hnat
      rw [Nat.cast_add, Nat.cast_add, Nat.cast_add, Nat.cast_mul] at h
      rw [show ((2^32 : ℕ) : F p) = (2^32 : F p) from by push_cast; ring] at h
      exact h
    have rearrange : ((opsValueSum input.ops : ℕ) : F p) +
        ((valueBits (chWord input.e input.f input.g) : ℕ) : F p) + (cst : F p) +
        -((S % 2^32 : ℕ) : F p) + -((2^32 : F p) * ((S / 2^32 : ℕ) : F p)) =
        (((opsValueSum input.ops : ℕ) : F p) +
          ((valueBits (chWord input.e input.f input.g) : ℕ) : F p) + (cst : F p)) -
        (((S % 2^32 : ℕ) : F p) + (2^32 : F p) * ((S / 2^32 : ℕ) : F p)) := by ring
    rw [rearrange, hF, sub_self]

def circuit : FormalCircuit (F p) (Inputs n) (fields 32) :=
  { elaborated (n:=n) (cw:=cw) (cst:=cst) with
    Assumptions := Assumptions
    Spec := Spec
    soundness := soundness
    completeness := completeness }

end ChAddMod32
end Gadgets.SHA256
end
