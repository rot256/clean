import Clean.Caliper.MultiLimb

/-!
# Multi-limb conversions, comparisons and bit access

The non-arithmetic half of the multi-limb field surface: moving between Montgomery
and canonical form, testing two `k`-limb values for equality and order, and reading
one bit of a canonical value. The witgen IR needs all four — `FExpr.const`,
`FExpr.ofU64` and environment reads enter Montgomery form, `U64Expr.val`,
`BExpr.flt`, `BExpr.bit` and the output buffer leave it, `BExpr.feq` compares.

Each follows the same frame convention as the arithmetic: the caller supplies a base
`w` above every value the gadget reads, the gadget owns a contiguous block from there,
and its result sits at a fixed offset. Costs are closed forms in `k`, so every one of
these is priced at every field.
-/

namespace Caliper.MultiLimb

open Caliper Caliper.Limbs

variable {C : CostModel}

/-! ## Montgomery conversion

Both directions are one Montgomery multiply by a generation-time constant: by
`R² mod p` to enter the representation, by `1` to leave it. The constant's limbs are
immediates, so the machine never computes it. -/

/-- `a * c * R⁻¹ mod p` for a generation-time constant `c`. -/
def montMulConst (k c a pReg pinv w : ℕ) : Stmt 64 :=
  immLimbs w c k ;; montMulSOS k a w pReg pinv (w + k)

/-- Where a constant-multiply based at `w` leaves its `k`-limb result. -/
def montMulConstOut (k w : ℕ) : ℕ := montOut k (w + k)

def montMulConstFrame (k : ℕ) : ℕ := k + montFrame k

/-- Canonical → Montgomery: multiply by `R² mod p`. -/
def toMont (k rsq a pReg pinv w : ℕ) : Stmt 64 := montMulConst k rsq a pReg pinv w

/-- Montgomery → canonical: multiply by `1`. -/
def fromMont (k a pReg pinv w : ℕ) : Stmt 64 := montMulConst k 1 a pReg pinv w

theorem montMulConst_staticTime_unit (k' c a pReg pinv w : ℕ) :
    (montMulConst (k' + 1) c a pReg pinv w).staticTime CostModel.unit
      = 16 * k' ^ 2 + 48 * k' + 41 := by
  show (immLimbs w c (k' + 1)).staticTime CostModel.unit
    + (montMulSOS (k' + 1) a w pReg pinv (w + (k' + 1))).staticTime CostModel.unit = _
  rw [immLimbs_staticTime, montMulSOS_staticTime_unit]
  simp [CostModel.unit]
  ring

theorem montMulConst_saf (k c a pReg pinv w : ℕ) : SAF (montMulConst k c a pReg pinv w) :=
  (immLimbs_saf _ _ _).seq (montMulSOS_saf _ _ _ _ _ _)

/-- The caller's obligation for a constant multiply: the frame starts above the
operand, the modulus and the constant. -/
structure ConstLayout (k a pReg pinv w : ℕ) : Prop where
  opA : a + k ≤ w
  modulus : pReg + (k + 1) ≤ w
  const : pinv < w

/-- **A multiply by a generation-time constant is correct.** With `c = 1` this leaves
Montgomery form; with `c = R² mod p` it enters it. -/
theorem montMulConst_exec {k' c a pReg pinv w : ℕ}
    (hl : ConstLayout (k' + 1) a pReg pinv w)
    {s : State 64} {p pv A : ℕ}
    (hp : 0 < p) (hpR : p < 2 ^ (64 * (k' + 1)))
    (hpinv : (p * pv + 1) % 2 ^ 64 = 0)
    (hA : A < p) (hc : c < p)
    (hpr : RegsEnc s pReg (k' + 2) p) (hcr : s.regs pinv = BitVec.ofNat 64 pv)
    (har : RegsEnc s a (k' + 1) A) :
    ∃ s' tt dd pp, Exec C (montMulConst (k' + 1) c a pReg pinv w) s s' tt dd pp ∧
      (∃ V, RegsEnc s' (montMulConstOut (k' + 1) w) (k' + 1) V ∧ V < p ∧
        V * 2 ^ (64 * (k' + 1)) ≡ A * c [MOD p]) ∧
      (∀ q, q < w → s'.regs q = s.regs q) ∧
      s'.bufs = s.bufs ∧ s'.caps = s.caps := by
  obtain ⟨hopA, hmodl, hconst⟩ := hl
  obtain ⟨s₁, t₁, d₁, p₁, hex₁, hcr₁, hlow₁, hhigh₁, hbuf₁, hcap₁⟩ :=
    immLimbs_exec (C := C) w c (s := s) (k' + 1)
  have har₁ : RegsEnc s₁ a (k' + 1) A := by
    intro j hj; rw [hlow₁ _ (by omega)]; exact har j hj
  have hpr₁ : RegsEnc s₁ pReg (k' + 2) p := by
    intro j hj; rw [hlow₁ _ (by omega)]; exact hpr j hj
  have hpinv₁ : s₁.regs pinv = BitVec.ofNat 64 pv := by
    rw [hlow₁ _ (by omega)]; exact hcr
  have hsos : SOSLayout (k' + 1) a w pReg pinv (w + (k' + 1)) :=
    ⟨by omega, by omega, by omega, by omega⟩
  obtain ⟨s₂, t₂, d₂, p₂, hex₂, hout, hpres₂, hbuf₂, hcap₂⟩ :=
    montMulSOS_exec (C := C) hsos hp hpR hpinv hA hc hpr₁ hpinv₁ har₁ hcr₁
  exact ⟨s₂, _, _, _, .seq hex₁ hex₂, hout,
    fun q hq => (hpres₂ q (by omega)).trans (hlow₁ q hq),
    hbuf₂.trans hbuf₁, hcap₂.trans hcap₁⟩

/-! ## Equality

`k` xors folded into one accumulator, then one `isZero`. Two instructions a limb. -/

def eqLoop (acc a b sc : ℕ) : ℕ → Stmt 64
  | 0 => .skip
  | n + 1 => eqLoop acc a b sc n ;; (.bin .xor sc (a + n) (b + n) ;; .bin .or acc acc sc)

/-- `w + 1 ← 1` if the `k`-limb values at `a` and `b` agree, else `0`. -/
def eqLimbs (k a b w : ℕ) : Stmt 64 :=
  .imm (w + 1) 0 ;; eqLoop (w + 1) a b w k ;; .un .isZero (w + 1) (w + 1)

def eqOut (w : ℕ) : ℕ := w + 1

def eqFrame : ℕ := 2

theorem eqLoop_staticTime (C : CostModel) (acc a b sc : ℕ) :
    ∀ n, (eqLoop acc a b sc n).staticTime C = n * (C.bin .xor + C.bin .or)
  | 0 => by simp [eqLoop, Stmt.staticTime]
  | n + 1 => by
    show (eqLoop acc a b sc n).staticTime C + _ = _
    rw [eqLoop_staticTime C acc a b sc n]; simp [Stmt.staticTime]; ring

/-- An equality test costs `2k + 2` unit steps. -/
theorem eqLimbs_staticTime_unit (k a b w : ℕ) :
    (eqLimbs k a b w).staticTime CostModel.unit = 2 * k + 2 := by
  show (Stmt.imm (w + 1) 0).staticTime CostModel.unit
    + ((eqLoop (w + 1) a b w k).staticTime CostModel.unit
      + (Stmt.un .isZero (w + 1) (w + 1)).staticTime CostModel.unit) = _
  rw [eqLoop_staticTime]
  simp [Stmt.staticTime, CostModel.unit]
  ring

theorem eqLoop_saf (acc a b sc : ℕ) : ∀ n, SAF (eqLoop acc a b sc n)
  | 0 => saf_skip
  | n + 1 => (eqLoop_saf acc a b sc n).seq ((saf_leaf_bin _ _ _ _).seq (saf_leaf_bin _ _ _ _))

theorem eqLimbs_saf (k a b w : ℕ) : SAF (eqLimbs k a b w) :=
  (saf_leaf_imm _ _).seq ((eqLoop_saf _ _ _ _ _).seq (saf_leaf_un _ _ _))

/-- A word is zero after an `or` exactly when both operands were. -/
theorem word_or_eq_zero (x y : Word 64) : x ||| y = 0 ↔ x = 0 ∧ y = 0 := by simp

/-- A word is zero after a `xor` exactly when the operands agreed. -/
theorem word_xor_eq_zero (x y : Word 64) : x ^^^ y = 0 ↔ x = y := by simp

theorem eqLoop_exec {k a b w : ℕ} (hopA : a + k ≤ w) (hopB : b + k ≤ w)
    {s : State 64} (hacc : s.regs (w + 1) = 0) :
    ∀ n ≤ k, ∃ s' t dd pp, Exec C (eqLoop (w + 1) a b w n) s s' t dd pp ∧
      (s'.regs (w + 1) = 0 ↔ ∀ j < n, s.regs (a + j) = s.regs (b + j)) ∧
      (∀ q, q < w → s'.regs q = s.regs q) ∧
      s'.bufs = s.bufs ∧ s'.caps = s.caps := by
  intro n
  induction n with
  | zero =>
    intro _
    exact ⟨s, 0, 0, 0, .skip, ⟨fun _ j hj => absurd hj (by omega), fun _ => hacc⟩,
      fun _ _ => rfl, rfl, rfl⟩
  | succ n ih =>
    intro hn
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hiff, hpres₁, hbuf₁, hcap₁⟩ := ih (by omega)
    refine ⟨_, _, _, _, .seq hex₁ (.seq .bin .bin), ?_, ?_, ?_, ?_⟩
    · rw [regs_setReg_self, regs_setReg_ne _ _ (show w + 1 ≠ w by omega),
        regs_setReg_self, hpres₁ (a + n) (by omega), hpres₁ (b + n) (by omega)]
      show ((s₁.regs (w + 1) ||| (s.regs (a + n) ^^^ s.regs (b + n)) : Word 64) = 0) ↔ _
      rw [word_or_eq_zero, hiff, word_xor_eq_zero]
      constructor
      · rintro ⟨h1, h2⟩ j hj
        rcases Nat.lt_or_ge j n with hlt | hge
        · exact h1 j hlt
        · have : j = n := by omega
          subst this; exact h2
      · intro h
        exact ⟨fun j hj => h j (by omega), h n (by omega)⟩
    · intro q hq
      rw [regs_setReg_ne _ _ (show q ≠ w + 1 by omega),
        regs_setReg_ne _ _ (show q ≠ w by omega), hpres₁ q hq]
    · simpa using hbuf₁
    · simpa using hcap₁

/-- **The equality test is correct.** -/
theorem eqLimbs_exec {k a b w : ℕ} (hopA : a + k ≤ w) (hopB : b + k ≤ w)
    {s : State 64} {A B : ℕ} (hA : A < 2 ^ (64 * k)) (hB : B < 2 ^ (64 * k))
    (har : RegsEnc s a k A) (hbr : RegsEnc s b k B) :
    ∃ s' tt dd pp, Exec C (eqLimbs k a b w) s s' tt dd pp ∧
      s'.regs (eqOut w) = BitVec.ofNat 64 (if A = B then 1 else 0) ∧
      (∀ q, q < w → s'.regs q = s.regs q) ∧
      s'.bufs = s.bufs ∧ s'.caps = s.caps := by
  have hacc : (s.setReg (w + 1) (0 : Word 64)).regs (w + 1) = 0 := by simp
  obtain ⟨s₁, t₁, d₁, p₁, hex₁, hiff, hpres₁, hbuf₁, hcap₁⟩ :=
    eqLoop_exec (C := C) hopA hopB hacc k le_rfl
  have hlimbs : (∀ j < k, (s.setReg (w + 1) (0 : Word 64)).regs (a + j)
      = (s.setReg (w + 1) (0 : Word 64)).regs (b + j)) ↔ A = B := by
    constructor
    · intro h
      refine eq_of_limbs hA hB fun j hj => ?_
      have := h j hj
      rw [regs_setReg_ne _ _ (show a + j ≠ w + 1 by omega),
        regs_setReg_ne _ _ (show b + j ≠ w + 1 by omega), har j hj, hbr j hj] at this
      have hnat := congrArg BitVec.toNat this
      have hAj := limb_lt 64 A j
      have hBj := limb_lt 64 B j
      simp only [BitVec.toNat_ofNat] at hnat
      omega
    · rintro rfl j hj
      rw [regs_setReg_ne _ _ (show a + j ≠ w + 1 by omega),
        regs_setReg_ne _ _ (show b + j ≠ w + 1 by omega), har j hj, hbr j hj]
  refine ⟨_, _, _, _, .seq .imm (.seq hex₁ .un), ?_, ?_, ?_, ?_⟩
  · rw [show eqOut w = w + 1 from rfl, regs_setReg_self]
    show (if s₁.regs (w + 1) = 0 then 1 else 0 : Word 64) = _
    by_cases hEq : A = B
    · rw [if_pos (hiff.mpr (hlimbs.mpr hEq)), if_pos hEq]; simp
    · rw [if_neg (fun h => hEq (hlimbs.mp (hiff.mp h))), if_neg hEq]; simp
  · intro q hq
    rw [regs_setReg_ne _ _ (show q ≠ w + 1 by omega), hpres₁ q hq,
      regs_setReg_ne _ _ (show q ≠ w + 1 by omega)]
  · simpa using hbuf₁
  · simpa using hcap₁

/-! ## Order

`subLimbs` already produces the bit that says `a ≥ b`; one `isZero` inverts it. The
difference itself is discarded, but it has to land somewhere, so the frame carries
`k` words for it. -/

/-- `ltOut k w ← 1` if the `k`-limb value at `a` is below the one at `b`. -/
def ltLimbs (k a b w : ℕ) : Stmt 64 :=
  subLimbs k (w + k + 4) a b w (w + k) ;; .un .isZero (w + 2 * k + 4) (w + k)

def ltOut (k w : ℕ) : ℕ := w + 2 * k + 4

def ltFrame (k : ℕ) : ℕ := 2 * k + 5

/-- An order test costs `6k + 2` unit steps. -/
theorem ltLimbs_staticTime_unit (k a b w : ℕ) :
    (ltLimbs k a b w).staticTime CostModel.unit = 6 * k + 2 := by
  show (subLimbs k (w + k + 4) a b w (w + k)).staticTime CostModel.unit
    + (Stmt.un .isZero (w + 2 * k + 4) (w + k)).staticTime CostModel.unit = _
  rw [subLimbs_staticTime]
  simp [Stmt.staticTime, addStepCost, CostModel.unit]
  ring

theorem ltLimbs_saf (k a b w : ℕ) : SAF (ltLimbs k a b w) :=
  (subLimbs_saf _ _ _ _ _ _).seq (saf_leaf_un _ _ _)

/-- The caller's obligation for an order test. -/
structure LtLayout (k a b w : ℕ) : Prop where
  opA : a + k ≤ w
  opB : b + k ≤ w

/-- **The order test is correct.** -/
theorem ltLimbs_exec {k a b w : ℕ} (hl : LtLayout k a b w)
    {s : State 64} {A B : ℕ} (hA : A < 2 ^ (64 * k)) (hB : B < 2 ^ (64 * k))
    (har : RegsEnc s a k A) (hbr : RegsEnc s b k B) :
    ∃ s' tt dd pp, Exec C (ltLimbs k a b w) s s' tt dd pp ∧
      s'.regs (ltOut k w) = BitVec.ofNat 64 (if A < B then 1 else 0) ∧
      (∀ q, q < w → s'.regs q = s.regs q) ∧
      s'.bufs = s.bufs ∧ s'.caps = s.caps := by
  obtain ⟨hopA, hopB⟩ := hl
  have hsub : SubLayout k (w + k + 4) a b w (w + k) :=
    ⟨by omega, by omega, by omega, by omega⟩
  obtain ⟨s₁, t₁, d₁, p₁, hex₁, _, hflag, hpres₁, hbuf₁, hcap₁⟩ :=
    subLimbs_exec (C := C) hsub hA hB har hbr
  have hflagv : (A + 2 ^ (64 * k) - B) / 2 ^ (64 * k) = if B ≤ A then 1 else 0 := by
    split_ifs with hle
    · exact Nat.div_eq_of_lt_le (by omega) (by omega)
    · exact Nat.div_eq_of_lt (by omega)
  refine ⟨_, _, _, _, .seq hex₁ .un, ?_, ?_, ?_, ?_⟩
  · have hv : s₁.regs (w + k) = BitVec.ofNat 64 (if B ≤ A then 1 else 0) := by
      rw [hflag, hflagv]
    rw [show ltOut k w = w + 2 * k + 4 from rfl, regs_setReg_self, hv]
    by_cases hle : B ≤ A
    · rw [if_pos hle, if_neg (show ¬ A < B by omega)]; simp
    · rw [if_neg hle, if_pos (show A < B by omega)]; simp
  · intro q hq
    rw [regs_setReg_ne _ _ (show q ≠ w + 2 * k + 4 by omega), hpres₁ q (by omega)]
  · simpa using hbuf₁
  · simpa using hcap₁

/-! ## Bit access

`i` is a generation-time index, so the limb it lives in and its offset inside that
limb are both constants: a shift and a mask, four instructions, or a single zero
immediate when the index is past the top limb. -/

/-- `w + 1 ← ` bit `i` of the `k`-limb value at `a`. -/
def bitLimb (k a i w : ℕ) : Stmt 64 :=
  if i / 64 < k then
    .imm w (BitVec.ofNat 64 (i % 64)) ;;
    .bin .shr (w + 1) (a + i / 64) w ;;
    .imm w 1 ;;
    .bin .and (w + 1) (w + 1) w
  else .imm (w + 1) 0

def bitOut (w : ℕ) : ℕ := w + 1

def bitFrame : ℕ := 2

/-- Reading a bit costs at most four unit steps, whatever the field. -/
theorem bitLimb_staticTime_unit_le (k a i w : ℕ) :
    (bitLimb k a i w).staticTime CostModel.unit ≤ 4 := by
  unfold bitLimb
  split <;> simp [Stmt.staticTime, CostModel.unit]

theorem bitLimb_saf (k a i w : ℕ) : SAF (bitLimb k a i w) := by
  unfold bitLimb
  split
  · exact (saf_leaf_imm _ _).seq ((saf_leaf_bin _ _ _ _).seq
      ((saf_leaf_imm _ _).seq (saf_leaf_bin _ _ _ _)))
  · exact saf_leaf_imm _ _

end Caliper.MultiLimb
