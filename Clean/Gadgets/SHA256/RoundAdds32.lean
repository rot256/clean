import Clean.Gadgets.SHA256.ChAddMod32
import Mathlib.Tactic.LinearCombination

section
variable {p : ℕ} [Fact p.Prime] [h_large : Fact (p > 2^110)]

namespace Gadgets.SHA256

/-!
# Both SHA-256 round additions in one gadget, sharing a single packed constraint row

Computes the round's two state updates together:

* `newE = (Σ eops + Ch(e, f, g)) mod 2^32` — the e-add with the fused choice word
  (`eops = [d, h, Σ₁, k, w]`), and
* `newA = (newE + Σ aops + 1) mod 2^32` — the a-add over `aops = [¬d, Σ₀, Maj]`
  (the `¬d + 1` realises `−d`, recovering `T1 = newE − d`).

The two addition equations are **packed into one R1CS row** at `2^36`-shifted lanes:

  `(Σ eops + Ch − newE − 2^32·ce) + 2^36·(newE + Σ aops + 1 − newA − 2^32·ca) = 0`.

Each lane value is a difference of two naturals below `2^36` (operand sums on one side,
result-plus-carry on the other), so over a field with `p > 2^110` the packed equation
lifts to `ℕ` and splits uniquely into its base-`2^36` digits — forcing both lane
equations individually.  An R1CS row may carry one product, and the row hosts exactly
one: `Ch`'s bit-31 product (the e-lane's fused choice bit).

R1CS structure (per call):
- 31 witnesses for the choice products `m[0..30]`, 32 + 3 witnesses for `newE` and its
  carry, 32 + 2 witnesses for `newA` and its carry (100 total)
- 31 product constraints, 69 boolean constraints, and 1 packed sum constraint
  (101 total) — versus 102 for `ChAddMod32` + `AddMod32`.

Soundness needs `p > 2^110` (with huge margin: the packed value is below `2^73`); this
gadget is intended for large fields such as the BN254 scalar field (≈ 2^253.6).  The
certified Mersenne prime `2^127 − 1` (`Utils.Primes.pM127`) serves as a stand-in for
field-independent cost evaluation.
-/

/-- Both round additions: `newE = (Σ eops + Ch(e,f,g)) mod 2^32` and
`newA = (newE + Σ aops + 1) mod 2^32`, with one packed sum row. -/
def roundAdds32 (e f g : Var (fields 32) (F p))
    (eops : Vector (Var (fields 32) (F p)) 5) (aops : Vector (Var (fields 32) (F p)) 3) :
    Circuit (F p) (Var (ProvableVector (fields 32) 2) (F p)) := do
  let m ← witnessVector 31 fun env =>
    Vector.ofFn fun (i : Fin 31) =>
      env e[i.val] * (env f[i.val] - env g[i.val])
  let ze ← witnessVector 32 fun env =>
    let t := (sumBitsNat env eops + chBitsNat env e f g) % 2^32
    Vector.ofFn fun (i : Fin 32) => ((t / 2^i.val % 2 : ℕ) : F p)
  let ce ← witnessVector 3 fun env =>
    let t := sumBitsNat env eops + chBitsNat env e f g
    Vector.ofFn fun (i : Fin 3) => ((t / 2^32 / 2^i.val % 2 : ℕ) : F p)
  let za ← witnessVector 32 fun env =>
    let t := ((sumBitsNat env eops + chBitsNat env e f g) % 2^32
      + sumBitsNat env aops + 1) % 2^32
    Vector.ofFn fun (i : Fin 32) => ((t / 2^i.val % 2 : ℕ) : F p)
  let ca ← witnessVector 2 fun env =>
    let t := (sumBitsNat env eops + chBitsNat env e f g) % 2^32
      + sumBitsNat env aops + 1
    Vector.ofFn fun (i : Fin 2) => ((t / 2^32 / 2^i.val % 2 : ℕ) : F p)
  Circuit.forEach (Vector.finRange 31) fun i =>
    assertZero (m[i] - e[i.val] * (f[i.val] - g[i.val]))
  Circuit.forEach (Vector.finRange 32) fun i =>
    assertZero (ze[i] * (ze[i] - 1))
  Circuit.forEach (Vector.finRange 3) fun i =>
    assertZero (ce[i] * (ce[i] - 1))
  Circuit.forEach (Vector.finRange 32) fun i =>
    assertZero (za[i] * (za[i] - 1))
  Circuit.forEach (Vector.finRange 2) fun i =>
    assertZero (ca[i] * (ca[i] - 1))
  -- Both addition equations in one row, at 2^36-shifted lanes; the only product is
  -- Ch's bit 31 inside `chBitsVar` (e-lane).
  assertZero (
    (sumExpr eops + fromBitsExpr (chBitsVar e f g m)
      - fromBitsExpr ze - (2^32 : F p) * carryExpr ce)
    + (2^36 : F p) * (fromBitsExpr ze + sumExpr aops + (1 : Expression (F p))
      - fromBitsExpr za - (2^32 : F p) * carryExpr ca))
  return #v[ze, za]

namespace RoundAdds32

structure Inputs (F : Type) where
  e : fields 32 F
  f : fields 32 F
  g : fields 32 F
  eops : ProvableVector (fields 32) 5 F
  aops : ProvableVector (fields 32) 3 F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var (ProvableVector (fields 32) 2) (F p)) :=
  roundAdds32 input.e input.f input.g input.eops input.aops

instance elaborated : ElaboratedCircuit (F p) Inputs (ProvableVector (fields 32) 2) where
  main := main
  localLength _ := 100
  output _ i0 := #v[varFromOffset (fields 32) (i0 + 31),
    varFromOffset (fields 32) (i0 + 31 + 32 + 3)]
  localLength_eq _ _ := by
    simp +arith only [circuit_norm, main, roundAdds32, Nat.mul_zero, Nat.add_zero]
  output_eq _ _ := rfl
  subcircuitsConsistent _ _ := by simp +arith only [circuit_norm, main, roundAdds32]
  channelsLawful := by intro x i; simp +arith only [circuit_norm, main, roundAdds32]

/-- The choice inputs and all summand operands are normalized. -/
def Assumptions (input : Inputs (F p)) : Prop :=
  Normalized input.e ∧ Normalized input.f ∧ Normalized input.g ∧
    (∀ j : Fin 5, Normalized input.eops[j]) ∧ ∀ j : Fin 3, Normalized input.aops[j]

/-- `newE = (Σ eops + Ch(e,f,g)) mod 2^32` and `newA = (newE + Σ aops + 1) mod 2^32`,
both normalized. -/
def Spec (input : Inputs (F p)) (out : ProvableVector (fields 32) 2 (F p)) : Prop :=
  valueBits out[0] = (opsValueSum input.eops +
    Specs.SHA256.Ch (valueBits input.e) (valueBits input.f) (valueBits input.g)) % 2^32
  ∧ valueBits out[1] = (valueBits out[0] + opsValueSum input.aops + 1) % 2^32
  ∧ Normalized out[0] ∧ Normalized out[1]

omit h_large in
/-- Componentwise evaluation of the two-word output vector. -/
lemma eval_pair_getElem (env : Environment (F p)) (a b : Var (fields 32) (F p)) :
    ((eval env (#v[a, b] : Var (ProvableVector (fields 32) 2) (F p)) :
      ProvableVector (fields 32) 2 (F p))[0] = Vector.map (Expression.eval env) a) ∧
    ((eval env (#v[a, b] : Var (ProvableVector (fields 32) 2) (F p)) :
      ProvableVector (fields 32) 2 (F p))[1] = Vector.map (Expression.eval env) b) := by
  constructor <;>
  · rw [← getElem_eval_vector]
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ]
    rw [CircuitType.eval_var_fields]

/-!
## Soundness
-/

theorem soundness : Soundness (Input := Inputs) (Output := ProvableVector (fields 32) 2)
    (F p) elaborated Assumptions Spec := by
  circuit_proof_start [roundAdds32]
  obtain ⟨h_e_norm, h_f_norm, h_g_norm, h_eops_norm, h_aops_norm⟩ := h_assumptions
  obtain ⟨h_in_e, h_in_f, h_in_g, h_in_eops, h_in_aops⟩ := h_input
  obtain ⟨h_m, h_ze_bool, h_ce_bool, h_za_bool, h_ca_bool, h_lin⟩ := h_holds
  -- Pointwise evaluation of the three choice inputs.
  have h_ei : ∀ (i : ℕ) (hi : i < 32),
      Expression.eval env (input_var_e[i]'hi) = input_e[i]'hi := by
    intro i hi
    have := Vector.ext_iff.mp h_in_e i hi
    simp [Vector.getElem_map] at this
    exact this
  have h_fi : ∀ (i : ℕ) (hi : i < 32),
      Expression.eval env (input_var_f[i]'hi) = input_f[i]'hi := by
    intro i hi
    have := Vector.ext_iff.mp h_in_f i hi
    simp [Vector.getElem_map] at this
    exact this
  have h_gi : ∀ (i : ℕ) (hi : i < 32),
      Expression.eval env (input_var_g[i]'hi) = input_g[i]'hi := by
    intro i hi
    have := Vector.ext_iff.mp h_in_g i hi
    simp [Vector.getElem_map] at this
    exact this
  -- The product rows pin the choice products m[0..30].
  have h_m_val : ∀ (i : ℕ) (hi : i < 31), env.get (i₀ + i) =
      (input_e[i]'(by omega)) * ((input_f[i]'(by omega)) - (input_g[i]'(by omega))) := by
    intro i hi
    have h := h_m ⟨i, hi⟩
    rw [h_ei i (by omega), h_fi i (by omega), h_gi i (by omega)] at h
    have key : env.get (i₀ + i) -
        (input_e[i]'(by omega)) * ((input_f[i]'(by omega)) - (input_g[i]'(by omega))) = 0 := by
      ring_nf
      ring_nf at h
      exact h
    exact sub_eq_zero.mp key
  -- The boolean rows give normalization of both outputs and carries.
  have h_ze_norm : Normalized (Vector.ofFn fun i : Fin 32 => env.get (i₀ + 31 + i.val)) :=
    AddMod32.normalized_of_bool_holds env (i₀ + 31) h_ze_bool
  have h_ce_norm : ∀ i : Fin 3,
      (Vector.ofFn fun j : Fin 3 => env.get (i₀ + 31 + 32 + j.val))[i] = 0 ∨
      (Vector.ofFn fun j : Fin 3 => env.get (i₀ + 31 + 32 + j.val))[i] = 1 :=
    AddMod32.bools_of_bool_holds env (i₀ + 31 + 32) h_ce_bool
  have h_za_norm : Normalized (Vector.ofFn fun i : Fin 32 => env.get (i₀ + 31 + 32 + 3 + i.val)) :=
    AddMod32.normalized_of_bool_holds env (i₀ + 31 + 32 + 3) h_za_bool
  have h_ca_norm : ∀ i : Fin 2,
      (Vector.ofFn fun j : Fin 2 => env.get (i₀ + 31 + 32 + 3 + 32 + j.val))[i] = 0 ∨
      (Vector.ofFn fun j : Fin 2 => env.get (i₀ + 31 + 32 + 3 + 32 + j.val))[i] = 1 :=
    AddMod32.bools_of_bool_holds env (i₀ + 31 + 32 + 3 + 32) h_ca_bool
  -- The choice word: spec value and normalization.
  obtain ⟨h_ch_val, h_ch_norm⟩ :=
    ChAddMod32.chWord_spec input_e input_f input_g h_e_norm h_f_norm h_g_norm
  -- Vector abbreviations for the two outputs and carries.
  set ze : fields 32 (F p) := Vector.ofFn fun i : Fin 32 => env.get (i₀ + 31 + i.val)
    with hze_def
  set ce : fields 3 (F p) := Vector.ofFn fun i : Fin 3 => env.get (i₀ + 31 + 32 + i.val)
    with hce_def
  set za : fields 32 (F p) := Vector.ofFn fun i : Fin 32 => env.get (i₀ + 31 + 32 + 3 + i.val)
    with hza_def
  set ca : fields 2 (F p) := Vector.ofFn fun i : Fin 2 => env.get (i₀ + 31 + 32 + 3 + 32 + i.val)
    with hca_def
  -- Bounds on the four lane sides.
  have h_p_large := h_large.elim
  have h_chv_lt : valueBits (ChAddMod32.chWord input_e input_f input_g) < 2^32 :=
    AddMod32.valueBits_lt_two_pow _ h_ch_norm
  have h_eops_le := ChAddMod32.opsValueSum_le input_eops h_eops_norm
  have h_aops_le := ChAddMod32.opsValueSum_le input_aops h_aops_norm
  have hvze_lt : valueBits ze < 2^32 :=
    AddMod32.valueBits_lt_two_pow ze (by simpa [ze] using h_ze_norm)
  have hvce_lt : AddMod32.bitsValue ce < 2^3 :=
    AddMod32.bitsValue_lt_two_pow ce (by simpa [ce] using h_ce_norm)
  have hvza_lt : valueBits za < 2^32 :=
    AddMod32.valueBits_lt_two_pow za (by simpa [za] using h_za_norm)
  have hvca_lt : AddMod32.bitsValue ca < 2^2 :=
    AddMod32.bitsValue_lt_two_pow ca (by simpa [ca] using h_ca_norm)
  -- Evaluate each piece of the packed constraint (in `Nat.cast` form).
  have h_sum_e : Expression.eval env (sumExpr input_var_eops) =
      ((opsValueSum input_eops : ℕ) : F p) :=
    AddMod32.sumExpr_eval_eq env input_var_eops input_eops h_in_eops
  have h_sum_a : Expression.eval env (sumExpr input_var_aops) =
      ((opsValueSum input_aops : ℕ) : F p) :=
    AddMod32.sumExpr_eval_eq env input_var_aops input_aops h_in_aops
  have h_mi : ∀ (i : ℕ) (hi : i < 31), Expression.eval env
      ((Vector.mapRange 31 fun i => (var {index := i₀ + i} : Expression (F p)))[i]'hi) =
      (input_e[i]'(by omega)) * ((input_f[i]'(by omega)) - (input_g[i]'(by omega))) := by
    intro i hi
    simp only [Vector.getElem_mapRange, Expression.eval]
    exact h_m_val i hi
  have h_ch_eval : Vector.map (Expression.eval env)
      (chBitsVar input_var_e input_var_f input_var_g
        (Vector.mapRange 31 fun i => (var {index := i₀ + i} : Expression (F p)))) =
      ChAddMod32.chWord input_e input_f input_g :=
    ChAddMod32.chBitsVar_eval env _ _ _ _ _ _ _ h_ei h_fi h_gi h_mi
  have h_ch_expr : Expression.eval env (fromBitsExpr
      (chBitsVar input_var_e input_var_f input_var_g
        (Vector.mapRange 31 fun i => (var {index := i₀ + i} : Expression (F p))))) =
      ((valueBits (ChAddMod32.chWord input_e input_f input_g) : ℕ) : F p) := by
    rw [AddMod32.fromBitsExpr_eval_bitsValue env _ _ h_ch_eval,
      AddMod32.bitsValue_eq_valueBits]
  have h_fze : Expression.eval env (fromBitsExpr
      (Vector.mapRange 32 fun i => (var {index := i₀ + 31 + i} : Expression (F p)))) =
      ((valueBits ze : ℕ) : F p) := by
    rw [AddMod32.fromBitsExpr_eval_bitsValue env _ ze (AddMod32.var_vector_eval env 32 (i₀ + 31)),
      AddMod32.bitsValue_eq_valueBits]
  have h_fce : Expression.eval env (carryExpr
      (Vector.mapRange 3 fun i => (var {index := i₀ + 31 + 32 + i} : Expression (F p)))) =
      ((AddMod32.bitsValue ce : ℕ) : F p) :=
    AddMod32.carryExpr_eval_bitsValue env _ ce (AddMod32.var_vector_eval env 3 (i₀ + 31 + 32))
  have h_fza : Expression.eval env (fromBitsExpr
      (Vector.mapRange 32 fun i =>
        (var {index := i₀ + 31 + 32 + 3 + i} : Expression (F p)))) =
      ((valueBits za : ℕ) : F p) := by
    rw [AddMod32.fromBitsExpr_eval_bitsValue env _ za
      (AddMod32.var_vector_eval env 32 (i₀ + 31 + 32 + 3)),
      AddMod32.bitsValue_eq_valueBits]
  have h_fca : Expression.eval env (carryExpr
      (Vector.mapRange 2 fun i =>
        (var {index := i₀ + 31 + 32 + 3 + 32 + i} : Expression (F p)))) =
      ((AddMod32.bitsValue ca : ℕ) : F p) :=
    AddMod32.carryExpr_eval_bitsValue env _ ca
      (AddMod32.var_vector_eval env 2 (i₀ + 31 + 32 + 3 + 32))
  -- The packed equation over `F p`, with all pieces in cast form.
  have hL_lt_p : opsValueSum input_eops +
      valueBits (ChAddMod32.chWord input_e input_f input_g) +
      2^36 * (valueBits ze + opsValueSum input_aops + 1) < p := by omega
  have hR_lt_p : (valueBits ze + 2^32 * AddMod32.bitsValue ce) +
      2^36 * (valueBits za + 2^32 * AddMod32.bitsValue ca) < p := by omega
  have h_cast : ((opsValueSum input_eops +
      valueBits (ChAddMod32.chWord input_e input_f input_g) +
      2^36 * (valueBits ze + opsValueSum input_aops + 1) : ℕ) : F p) =
      (((valueBits ze + 2^32 * AddMod32.bitsValue ce) +
      2^36 * (valueBits za + 2^32 * AddMod32.bitsValue ca) : ℕ) : F p) := by
    push_cast
    rw [← h_sum_e, ← h_sum_a, ← h_ch_expr, ← h_fze, ← h_fce, ← h_fza, ← h_fca]
    linear_combination h_lin
  have h_nat : opsValueSum input_eops +
      valueBits (ChAddMod32.chWord input_e input_f input_g) +
      2^36 * (valueBits ze + opsValueSum input_aops + 1) =
      (valueBits ze + 2^32 * AddMod32.bitsValue ce) +
      2^36 * (valueBits za + 2^32 * AddMod32.bitsValue ca) := by
    have h := congrArg ZMod.val h_cast
    rwa [ZMod.val_natCast_of_lt hL_lt_p, ZMod.val_natCast_of_lt hR_lt_p] at h
  -- Split the packed equation into its two base-2^36 digits: the low digits are equal
  -- mod 2^36 and both below 2^36, the high digits follow by cancellation.
  have h_lane_e : opsValueSum input_eops +
      valueBits (ChAddMod32.chWord input_e input_f input_g) =
      valueBits ze + 2^32 * AddMod32.bitsValue ce := by
    have h0 := congrArg (fun t => t % 2^36) h_nat
    simp only [Nat.add_mul_mod_self_left] at h0
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h0
  have h_lane_a : valueBits ze + opsValueSum input_aops + 1 =
      valueBits za + 2^32 * AddMod32.bitsValue ca := by
    omega
  -- Reduce the output getElems and conclude each conjunct.
  rw [(eval_pair_getElem env _ _).1, (eval_pair_getElem env _ _).2]
  rw [AddMod32.var_vector_eval env 32 (i₀ + 31),
    AddMod32.var_vector_eval env 32 (i₀ + 31 + 32 + 3), ← hze_def, ← hza_def]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← h_ch_val]
    omega
  · omega
  · exact h_ze_norm
  · exact h_za_norm

/-!
## Completeness
-/

theorem completeness : Completeness (Input := Inputs) (Output := ProvableVector (fields 32) 2)
    (F p) elaborated Assumptions := by
  circuit_proof_start [roundAdds32]
  obtain ⟨h_e_norm, h_f_norm, h_g_norm, h_eops_norm, h_aops_norm⟩ := h_assumptions
  obtain ⟨h_in_e, h_in_f, h_in_g, h_in_eops, h_in_aops⟩ := h_input
  obtain ⟨h_env_m, h_env_ze, h_env_ce, h_env_za, h_env_ca, -⟩ := h_env
  have h_ei : ∀ (i : ℕ) (hi : i < 32),
      Expression.eval env.toEnvironment (input_var_e[i]'hi) = input_e[i]'hi := by
    intro i hi
    have := Vector.ext_iff.mp h_in_e i hi
    simp [Vector.getElem_map] at this
    exact this
  have h_fi : ∀ (i : ℕ) (hi : i < 32),
      Expression.eval env.toEnvironment (input_var_f[i]'hi) = input_f[i]'hi := by
    intro i hi
    have := Vector.ext_iff.mp h_in_f i hi
    simp [Vector.getElem_map] at this
    exact this
  have h_gi : ∀ (i : ℕ) (hi : i < 32),
      Expression.eval env.toEnvironment (input_var_g[i]'hi) = input_g[i]'hi := by
    intro i hi
    have := Vector.ext_iff.mp h_in_g i hi
    simp [Vector.getElem_map] at this
    exact this
  set Se := sumBitsNat env input_var_eops + chBitsNat env input_var_e input_var_f input_var_g
    with hSe_def
  -- The choice-word ℕ value agrees with the value-level choice word.
  have h_ch_nat : chBitsNat env input_var_e input_var_f input_var_g =
      valueBits (ChAddMod32.chWord input_e input_f input_g) := by
    unfold chBitsNat valueBits ChAddMod32.chWord
    apply Finset.sum_congr rfl
    intro i _
    simp only [Vector.getElem_ofFn, Fin.getElem_fin]
    rw [h_ei i.val i.isLt, h_fi i.val i.isLt, h_gi i.val i.isLt]
  obtain ⟨h_ch_val, h_ch_norm⟩ :=
    ChAddMod32.chWord_spec input_e input_f input_g h_e_norm h_f_norm h_g_norm
  have hSe_eq : Se = opsValueSum input_eops +
      valueBits (ChAddMod32.chWord input_e input_f input_g) := by
    rw [hSe_def, AddMod32.sumBitsNat_eq_opsValueSum env input_var_eops input_eops h_in_eops,
      h_ch_nat]
  have h_p_large := h_large.elim
  have hp32 : (2:ℕ)^32 < p := by omega
  have hp2 : 2 < p := by omega
  have h_chv_lt : valueBits (ChAddMod32.chWord input_e input_f input_g) < 2^32 :=
    AddMod32.valueBits_lt_two_pow _ h_ch_norm
  have h_eops_le := ChAddMod32.opsValueSum_le input_eops h_eops_norm
  have h_aops_le := ChAddMod32.opsValueSum_le input_aops h_aops_norm
  have hSe_mod_lt : Se % 2^32 < 2^32 := Nat.mod_lt _ (by norm_num)
  have hSe_div_lt : Se / 2^32 < 2^3 := by
    apply (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2^32)).mpr
    omega
  set Sa := Se % 2^32 + sumBitsNat env input_var_aops + 1 with hSa_def
  have hSa_eq : Sa = Se % 2^32 + opsValueSum input_aops + 1 := by
    rw [hSa_def,
      AddMod32.sumBitsNat_eq_opsValueSum env input_var_aops input_aops h_in_aops]
  have hSa_mod_lt : Sa % 2^32 < 2^32 := Nat.mod_lt _ (by norm_num)
  have hSa_div_lt : Sa / 2^32 < 2^2 := by
    apply (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2^32)).mpr
    omega
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_, ?_⟩
  · -- product constraints m_i = e_i (f_i − g_i)
    have henv_i := h_env_m i
    simp only [Vector.getElem_ofFn] at henv_i
    rw [henv_i, h_ei i.val (by omega), h_fi i.val (by omega), h_gi i.val (by omega)]
    ring
  · -- booleanity of ze
    have henv_i := h_env_ze i
    simp only [Vector.getElem_ofFn] at henv_i
    rw [henv_i]
    rcases Nat.mod_two_eq_zero_or_one (Se % 2^32 / 2^i.val) with h | h <;>
      rw [h] <;> push_cast <;> ring
  · -- booleanity of ce
    have henv_i := h_env_ce i
    simp only [Vector.getElem_ofFn] at henv_i
    rw [henv_i]
    rcases Nat.mod_two_eq_zero_or_one (Se / 2^32 / 2^i.val) with h | h <;>
      rw [h] <;> push_cast <;> ring
  · -- booleanity of za
    have henv_i := h_env_za i
    simp only [Vector.getElem_ofFn] at henv_i
    rw [henv_i]
    rcases Nat.mod_two_eq_zero_or_one (Sa % 2^32 / 2^i.val) with h | h <;>
      rw [h] <;> push_cast <;> ring
  · -- booleanity of ca
    have henv_i := h_env_ca i
    simp only [Vector.getElem_ofFn] at henv_i
    rw [henv_i]
    rcases Nat.mod_two_eq_zero_or_one (Sa / 2^32 / 2^i.val) with h | h <;>
      rw [h] <;> push_cast <;> ring
  · -- the packed constraint row
    have h_sum_e : Expression.eval env.toEnvironment (sumExpr input_var_eops) =
        ((opsValueSum input_eops : ℕ) : F p) :=
      AddMod32.sumExpr_eval_eq env.toEnvironment input_var_eops input_eops h_in_eops
    have h_sum_a : Expression.eval env.toEnvironment (sumExpr input_var_aops) =
        ((opsValueSum input_aops : ℕ) : F p) :=
      AddMod32.sumExpr_eval_eq env.toEnvironment input_var_aops input_aops h_in_aops
    have h_mi : ∀ (i : ℕ) (hi : i < 31), Expression.eval env.toEnvironment
        ((Vector.mapRange 31 fun i => (var {index := i₀ + i} : Expression (F p)))[i]'hi) =
        (input_e[i]'(by omega)) * ((input_f[i]'(by omega)) - (input_g[i]'(by omega))) := by
      intro i hi
      simp only [Vector.getElem_mapRange, Expression.eval]
      have henv_i := h_env_m ⟨i, hi⟩
      simp only [Vector.getElem_ofFn] at henv_i
      rw [henv_i, h_ei i (by omega), h_fi i (by omega), h_gi i (by omega)]
    have h_ch_eval : Vector.map (Expression.eval env.toEnvironment)
        (chBitsVar input_var_e input_var_f input_var_g
          (Vector.mapRange 31 fun i => (var {index := i₀ + i} : Expression (F p)))) =
        ChAddMod32.chWord input_e input_f input_g :=
      ChAddMod32.chBitsVar_eval env.toEnvironment _ _ _ _ _ _ _ h_ei h_fi h_gi h_mi
    have h_ch_expr : Expression.eval env.toEnvironment (fromBitsExpr
        (chBitsVar input_var_e input_var_f input_var_g
          (Vector.mapRange 31 fun i => (var {index := i₀ + i} : Expression (F p))))) =
        ((valueBits (ChAddMod32.chWord input_e input_f input_g) : ℕ) : F p) := by
      rw [AddMod32.fromBitsExpr_eval_bitsValue env.toEnvironment _ _ h_ch_eval,
        AddMod32.bitsValue_eq_valueBits]
    have h_fze : Expression.eval env.toEnvironment (fromBitsExpr
        (Vector.mapRange 32 fun i => (var {index := i₀ + 31 + i} : Expression (F p)))) =
        ((Se % 2^32 : ℕ) : F p) := by
      change env.toEnvironment (Utils.Bits.fieldFromBitsExpr
        (Vector.mapRange 32 fun i => (var {index := i₀ + 31 + i} : Expression (F p)))) = _
      rw [Utils.Bits.fieldFromBits_eval]
      have h_map : Vector.map (Expression.eval env.toEnvironment)
          (Vector.mapRange 32 fun i => (var {index := i₀ + 31 + i} : Expression (F p))) =
          Vector.ofFn fun i : Fin 32 => ((Se % 2^32 / 2^i.val % 2 : ℕ) : F p) := by
        rw [AddMod32.var_vector_eval env.toEnvironment 32 (i₀ + 31)]
        ext i hi
        simp only [Vector.getElem_ofFn]
        have h := h_env_ze ⟨i, hi⟩
        simp only [Vector.getElem_ofFn] at h
        exact h
      rw [h_map]
      exact AddMod32.fieldFromBits_bit_decomp 32 (Se % 2^32) hSe_mod_lt hp2
    have h_fce : Expression.eval env.toEnvironment (carryExpr
        (Vector.mapRange 3 fun i => (var {index := i₀ + 31 + 32 + i} : Expression (F p)))) =
        ((Se / 2^32 : ℕ) : F p) := by
      have h_map : Vector.map (Expression.eval env.toEnvironment)
          (Vector.mapRange 3 fun i => (var {index := i₀ + 31 + 32 + i} : Expression (F p))) =
          Vector.ofFn fun i : Fin 3 => ((Se / 2^32 / 2^i.val % 2 : ℕ) : F p) := by
        rw [AddMod32.var_vector_eval env.toEnvironment 3 (i₀ + 31 + 32)]
        ext i hi
        simp only [Vector.getElem_ofFn]
        have h := h_env_ce ⟨i, hi⟩
        simp only [Vector.getElem_ofFn] at h
        exact h
      rw [AddMod32.carryExpr_eval_bitsValue env.toEnvironment _ _ h_map]
      rw [AddMod32.bitsValue_bit_decomp 3 (Se / 2^32) hSe_div_lt hp2]
    have h_fza : Expression.eval env.toEnvironment (fromBitsExpr
        (Vector.mapRange 32 fun i =>
          (var {index := i₀ + 31 + 32 + 3 + i} : Expression (F p)))) =
        ((Sa % 2^32 : ℕ) : F p) := by
      change env.toEnvironment (Utils.Bits.fieldFromBitsExpr
        (Vector.mapRange 32 fun i =>
          (var {index := i₀ + 31 + 32 + 3 + i} : Expression (F p)))) = _
      rw [Utils.Bits.fieldFromBits_eval]
      have h_map : Vector.map (Expression.eval env.toEnvironment)
          (Vector.mapRange 32 fun i =>
            (var {index := i₀ + 31 + 32 + 3 + i} : Expression (F p))) =
          Vector.ofFn fun i : Fin 32 => ((Sa % 2^32 / 2^i.val % 2 : ℕ) : F p) := by
        rw [AddMod32.var_vector_eval env.toEnvironment 32 (i₀ + 31 + 32 + 3)]
        ext i hi
        simp only [Vector.getElem_ofFn]
        have h := h_env_za ⟨i, hi⟩
        simp only [Vector.getElem_ofFn] at h
        exact h
      rw [h_map]
      exact AddMod32.fieldFromBits_bit_decomp 32 (Sa % 2^32) hSa_mod_lt hp2
    have h_fca : Expression.eval env.toEnvironment (carryExpr
        (Vector.mapRange 2 fun i =>
          (var {index := i₀ + 31 + 32 + 3 + 32 + i} : Expression (F p)))) =
        ((Sa / 2^32 : ℕ) : F p) := by
      have h_map : Vector.map (Expression.eval env.toEnvironment)
          (Vector.mapRange 2 fun i =>
            (var {index := i₀ + 31 + 32 + 3 + 32 + i} : Expression (F p))) =
          Vector.ofFn fun i : Fin 2 => ((Sa / 2^32 / 2^i.val % 2 : ℕ) : F p) := by
        rw [AddMod32.var_vector_eval env.toEnvironment 2 (i₀ + 31 + 32 + 3 + 32)]
        ext i hi
        simp only [Vector.getElem_ofFn]
        have h := h_env_ca ⟨i, hi⟩
        simp only [Vector.getElem_ofFn] at h
        exact h
      rw [AddMod32.carryExpr_eval_bitsValue env.toEnvironment _ _ h_map]
      rw [AddMod32.bitsValue_bit_decomp 2 (Sa / 2^32) hSa_div_lt hp2]
    rw [h_sum_e, h_sum_a, h_ch_expr, h_fze, h_fce, h_fza, h_fca]
    -- Both lane identities over ℕ, cast to the field.
    have hnat_e : opsValueSum input_eops +
        valueBits (ChAddMod32.chWord input_e input_f input_g) =
        Se % 2^32 + 2^32 * (Se / 2^32) := by
      rw [← hSe_eq]
      exact (Nat.mod_add_div Se (2^32)).symm.trans (by ring)
    have hnat_a : Se % 2^32 + opsValueSum input_aops + 1 =
        Sa % 2^32 + 2^32 * (Sa / 2^32) := by
      rw [← hSa_eq]
      exact (Nat.mod_add_div Sa (2^32)).symm.trans (by ring)
    have hF_e : ((opsValueSum input_eops : ℕ) : F p) +
        ((valueBits (ChAddMod32.chWord input_e input_f input_g) : ℕ) : F p) =
        ((Se % 2^32 : ℕ) : F p) + (2^32 : F p) * ((Se / 2^32 : ℕ) : F p) := by
      have h := congr_arg (Nat.cast : ℕ → F p) hnat_e
      push_cast at h
      linear_combination h
    have hF_a : ((Se % 2^32 : ℕ) : F p) + ((opsValueSum input_aops : ℕ) : F p) + 1 =
        ((Sa % 2^32 : ℕ) : F p) + (2^32 : F p) * ((Sa / 2^32 : ℕ) : F p) := by
      have h := congr_arg (Nat.cast : ℕ → F p) hnat_a
      push_cast at h
      linear_combination h
    linear_combination hF_e + (2^36 : F p) * hF_a

def circuit : FormalCircuit (F p) Inputs (ProvableVector (fields 32) 2) :=
  { elaborated with
    Assumptions := Assumptions
    Spec := Spec
    soundness := soundness
    completeness := completeness }

end RoundAdds32
end Gadgets.SHA256
end
