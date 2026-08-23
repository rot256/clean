import Clean.Caliper.MultiLimbIR
import Clean.Caliper.WitgenSim

/-!
# Encodings and leaf lemmas for the multi-limb compiler's correctness

The multi-limb counterpart of `WitgenSim.lean`. A field element is `k` registers (or
`k` buffer words) holding the limbs of its **Montgomery form** `x·R mod p`, so the
encoding layer has two jobs the single-word one did not:

* say what a block or a run of buffer words holds (`RegsEnc`, `encWords`), and
* pin down the Montgomery form as a *function* of the field element (`montVal`), so a
  gadget's "there exists `V < p` with `V·R ≡ A·B`" conclusion becomes an equation.

The bridge is `eq_montVal`: below `p`, a residue class determines its representative,
and `R` is invertible mod an odd `p`, so every gadget's congruence pins its output.

The rest of the file supplies the three gadget `Exec` lemmas the lowering needs and
`MultiLimb.lean` did not have — bit access, environment loads, and output pushes.
-/

namespace Caliper.MultiLimb

open Caliper Caliper.Limbs Witgen

variable {C : CostModel}

/-! ## Bit access -/

/-- Bit `j` of a limb is the corresponding bit of the value. -/
theorem testBit_limb (A i : ℕ) :
    (limb 64 A (i / 64)).testBit (i % 64) = A.testBit i := by
  simp only [limb, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
    Nat.mod_lt _ (by norm_num : 0 < 64), decide_true, Bool.true_and]
  congr 1
  omega

/-- The `{0, 1}` word a shift-and-mask leaves. -/
theorem word_shr_and_one {v n : ℕ} (hv : v < 2 ^ 64) (hn : n < 64) :
    (BitVec.ofNat 64 v >>> (BitVec.ofNat 64 n).toNat) &&& (1 : Word 64)
      = BitVec.ofNat 64 (if v.testBit n then 1 else 0) := by
  have hn' : (BitVec.ofNat 64 n).toNat = n := by
    simp only [BitVec.toNat_ofNat]; omega
  rw [hn']
  apply BitVec.eq_of_toNat_eq
  have h1 : (1 : Word 64).toNat = 1 := rfl
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, h1,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt hv]
  have hmod : v / 2 ^ n % 2 = if v.testBit n then 1 else 0 := by
    have h2 : v / 2 ^ n % 2 < 2 := Nat.mod_lt _ (by norm_num)
    by_cases h : v.testBit n
    · rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq] at h
      rw [if_pos (by simp [Nat.testBit_eq_decide_div_mod_eq, h])]
      exact h
    · rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq] at h
      rw [if_neg (by simp [Nat.testBit_eq_decide_div_mod_eq, h])]
      omega
  rw [Nat.and_one_is_mod, hmod]
  split <;> simp

/-- **Bit access is correct.** -/
theorem bitLimb_exec {k a i w : ℕ} (hopA : a + k ≤ w)
    {s : State 64} {A : ℕ} (hA : A < 2 ^ (64 * k)) (har : RegsEnc s a k A) :
    ∃ s' t dd pp, Exec C (bitLimb k a i w) s s' t dd pp ∧
      s'.regs (bitOut w) = BitVec.ofNat 64 (if A.testBit i then 1 else 0) ∧
      (∀ q, q < w → s'.regs q = s.regs q) ∧
      s'.bufs = s.bufs ∧ s'.caps = s.caps := by
  unfold bitLimb
  split
  · rename_i hik
    refine ⟨_, _, _, _, .seq .imm (.seq .bin (.seq .imm .bin)), ?_, ?_, ?_, ?_⟩
    · simp only [show bitOut w = w + 1 from rfl,
        regs_setReg_self, regs_setReg_ne _ _ (show w + 1 ≠ w by omega),
        regs_setReg_ne _ _ (show a + i / 64 ≠ w by omega), har (i / 64) hik]
      show (BitVec.ofNat 64 (limb 64 A (i / 64)) >>>
        (BitVec.ofNat 64 (i % 64)).toNat) &&& (1 : Word 64) = _
      rw [word_shr_and_one (limb_lt 64 A (i / 64)) (Nat.mod_lt _ (by norm_num)),
        testBit_limb]
    · intro q hq
      rw [regs_setReg_ne _ _ (show q ≠ w + 1 by omega),
        regs_setReg_ne _ _ (show q ≠ w by omega),
        regs_setReg_ne _ _ (show q ≠ w + 1 by omega),
        regs_setReg_ne _ _ (show q ≠ w by omega)]
    · rfl
    · rfl
  · rename_i hik
    refine ⟨_, _, _, _, .imm, ?_,
      fun q hq => regs_setReg_ne _ _ (show q ≠ w + 1 by omega), rfl, rfl⟩
    have hzero : A.testBit i = false := by
      exact Nat.testBit_lt_two_pow
        (lt_of_lt_of_le hA (Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [show bitOut w = w + 1 from rfl, regs_setReg_self, hzero]
    rfl

/-! ## Environment loads

`loadLimbs` walks a run of buffer-`0` cells into a register block, one index immediate
and one load a limb. The scratch register sits below the block. -/

/-- **A run of environment loads is correct.** -/
theorem loadLimbs_exec {base idx sc : ℕ} (hsc : sc < base) :
    ∀ (n : ℕ) {s : State 64}, idx + n ≤ 2 ^ 64 → idx + n ≤ (s.bufs 0).size →
      ∃ s' t dd pp, Exec C (loadLimbs base idx sc n) s s' t dd pp ∧
        (∀ j, j < n → s'.regs (base + j) = (s.bufs 0)[idx + j]!) ∧
        (∀ q, q < base → q ≠ sc → s'.regs q = s.regs q) ∧
        (∀ q, base + n ≤ q → s'.regs q = s.regs q) ∧
        s'.bufs = s.bufs ∧ s'.caps = s.caps
  | 0, s, _, _ => ⟨s, 0, 0, 0, .skip, fun _ h => absurd h (by omega),
      fun _ _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩
  | n + 1, s, hlt, hsz => by
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hval₁, hlow₁, hhigh₁, hbuf₁, hcap₁⟩ :=
      loadLimbs_exec hsc n (s := s) (show idx + n ≤ 2 ^ 64 by omega)
        (show idx + n ≤ (s.bufs 0).size by omega)
    have hidx : ((s₁.setReg sc (BitVec.ofNat 64 (idx + n))).regs sc).toNat = idx + n := by
      rw [regs_setReg_self]
      simp only [BitVec.toNat_ofNat]
      omega
    have hload : ((s₁.setReg sc (BitVec.ofNat 64 (idx + n))).regs sc).toNat
        < ((s₁.setReg sc (BitVec.ofNat 64 (idx + n))).bufs 0).size := by
      rw [hidx, bufs_setReg, hbuf₁]; omega
    refine ⟨_, _, _, _, .seq hex₁ (.seq .imm (.memLoad hload)), ?_, ?_, ?_, ?_, ?_⟩
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
      · rw [regs_setReg_ne _ _ (show base + j ≠ base + n by omega),
          regs_setReg_ne _ _ (show base + j ≠ sc by omega)]
        exact hval₁ j hj'
      · have harr : ((s₁.setReg sc (BitVec.ofNat 64 (idx + j))).bufs 0) = s.bufs 0 := by
          rw [bufs_setReg, hbuf₁]
        rw [regs_setReg_self,
          ← getElem!_pos (cont := Array (Word 64)) _ _ hload, harr, hidx]
    · intro q hq hqs
      rw [regs_setReg_ne _ _ (show q ≠ base + n by omega),
        regs_setReg_ne _ _ hqs]
      exact hlow₁ q hq hqs
    · intro q hq
      rw [regs_setReg_ne _ _ (show q ≠ base + n by omega),
        regs_setReg_ne _ _ (show q ≠ sc by omega)]
      exact hhigh₁ q (by omega)
    · simpa using hbuf₁
    · simpa using hcap₁

/-! ## Output pushes -/

/-- The `n` buffer words a value occupies, low limb first. -/
def encWords (n v : ℕ) : List (Word 64) :=
  (List.range n).map fun j => BitVec.ofNat 64 (limb 64 v j)

theorem encWords_succ (n v : ℕ) :
    encWords (n + 1) v = encWords n v ++ [BitVec.ofNat 64 (limb 64 v n)] := by
  simp [encWords, List.range_succ]

theorem encWords_length (n v : ℕ) : (encWords n v).length = n := by simp [encWords]

/-- Pushing onto an array extends the list still to be appended. -/
theorem push_append_toArray {α : Type} (arr : Array α) (l : List α) (v : α) :
    (arr ++ l.toArray).push v = arr ++ (l ++ [v]).toArray := by
  simp

/-- **A run of output pushes is correct.** -/
theorem pushLoop_exec {src : ℕ} :
    ∀ (n : ℕ) {s : State 64} {V : ℕ}, RegsEnc s src n V →
      (s.bufs 1).size + n ≤ s.caps 1 →
      ∃ s' t dd pp, Exec C (pushLoop src n) s s' t dd pp ∧
        s'.bufs 1 = s.bufs 1 ++ (encWords n V).toArray ∧
        (∀ b, b ≠ 1 → s'.bufs b = s.bufs b) ∧ s'.regs = s.regs ∧ s'.caps = s.caps
  | 0, s, V, _, _ => ⟨s, 0, 0, 0, .skip, by simp [encWords], fun _ _ => rfl, rfl, rfl⟩
  | n + 1, s, V, hsr, hcap => by
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hout₁, hother₁, hreg₁, hcap₁⟩ :=
      pushLoop_exec n (s := s) (V := V) (fun j hj => hsr j (by omega))
        (show (s.bufs 1).size + n ≤ s.caps 1 by omega)
    have hpush : (s₁.bufs 1).size < s₁.caps 1 := by
      rw [hout₁, hcap₁]
      have : (s.bufs 1 ++ (encWords n V).toArray).size = (s.bufs 1).size + n := by
        simp [encWords_length]
      omega
    refine ⟨_, _, _, _, .seq hex₁ (.memPush hpush), ?_, ?_, ?_, ?_⟩
    · rw [bufs_setBuf_self, hout₁, hreg₁, hsr n (by omega), encWords_succ]
      exact push_append_toArray _ _ _
    · intro b hb
      rw [bufs_setBuf_ne _ _ hb]
      exact hother₁ b hb
    · rw [regs_setBuf]; exact hreg₁
    · rw [caps_setBuf]; exact hcap₁

theorem pushLimbs_exec {k src : ℕ} {s : State 64} {V : ℕ} (hsr : RegsEnc s src k V)
    (hcap : (s.bufs 1).size + k ≤ s.caps 1) :
    ∃ s' t dd pp, Exec C (pushLimbs k src) s s' t dd pp ∧
      s'.bufs 1 = s.bufs 1 ++ (encWords k V).toArray ∧
      (∀ b, b ≠ 1 → s'.bufs b = s.bufs b) ∧ s'.regs = s.regs ∧ s'.caps = s.caps :=
  pushLoop_exec k hsr hcap

end Caliper.MultiLimb
