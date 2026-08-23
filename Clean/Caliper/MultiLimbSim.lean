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

/-! ## Montgomery encoding

A field element is stored as the limbs of `x·R mod p` with `R = 2 ^ (64k)`. The
gadgets state their results as congruences (`V·R ≡ A·B [MOD p]` with `V < p`); casting
into `F p`, where `R` is a unit, turns each of those into an equation between field
elements, and `V < p` turns that back into an equation between naturals. -/

section Mont

variable {p : ℕ} [Fact p.Prime]

/-- Montgomery form of a field element over `k` limbs. -/
def montVal (k : ℕ) (x : F p) : ℕ := x.val * 2 ^ (64 * k) % p

theorem montVal_lt (k : ℕ) (x : F p) : montVal k x < p :=
  Nat.mod_lt _ (Fact.out (p := p.Prime)).pos

/-- Two naturals below the modulus are equal as soon as they are equal in the field. -/
theorem eq_of_natCast {A B : ℕ} (hA : A < p) (hB : B < p)
    (h : (A : F p) = (B : F p)) : A = B := by
  have h' := congrArg ZMod.val h
  rwa [ZMod.val_cast_of_lt hA, ZMod.val_cast_of_lt hB] at h'

/-- Montgomery form, in the field: `x·R`. -/
theorem montVal_cast (k : ℕ) (x : F p) :
    ((montVal k x : ℕ) : F p) = x * (2 : F p) ^ (64 * k) := by
  rw [montVal, ZMod.natCast_mod]
  push_cast
  rw [ZMod.natCast_val, ZMod.cast_id]

/-- `R` is a unit: `2` is invertible in a field of odd characteristic. -/
theorem two_pow_ne_zero (hp2 : 2 < p) (n : ℕ) : (2 : F p) ^ n ≠ 0 := by
  refine pow_ne_zero n ?_
  intro h
  have hval : ((2 : ℕ) : F p) = 0 := by push_cast; exact h
  rw [ZMod.natCast_eq_zero_iff 2 p] at hval
  exact absurd (Nat.le_of_dvd (by norm_num) hval) (by omega)

/-- Below `p`, the field equation determines the natural. -/
theorem eq_montVal {k V : ℕ} {x : F p} (hV : V < p)
    (h : (V : F p) = x * (2 : F p) ^ (64 * k)) : V = montVal k x :=
  eq_of_natCast hV (montVal_lt k x) (by rw [h, montVal_cast])

/-- A gadget's `[MOD p]` conclusion, in the field. -/
theorem cast_modEq {A B : ℕ} (h : A ≡ B [MOD p]) : (A : F p) = (B : F p) :=
  (ZMod.natCast_eq_natCast_iff A B p).mpr h

end Mont

/-! ## The field gadgets, semantically

Each gadget's `Exec` lemma states its result as `V < p` together with a congruence;
these wrappers turn that into `montVal`, the form the compiler induction carries. -/

section FieldGadgets

variable {p : ℕ} [Fact p.Prime]

/-- **Addition of Montgomery forms.** -/
theorem montAdd_field {k a b pReg w : ℕ} (hl : FieldLayout k a b pReg w)
    {s : State 64} {x y : F p} (hpR : p < 2 ^ (64 * k))
    (hpr : RegsEnc s pReg k p)
    (har : RegsEnc s a k (montVal k x)) (hbr : RegsEnc s b k (montVal k y)) :
    ∃ s' tt dd pp, Exec C (montAdd k a b pReg w) s s' tt dd pp ∧
      RegsEnc s' (montAddOut k w) k (montVal k (x + y)) ∧
      (∀ q, q < w → s'.regs q = s.regs q) ∧
      s'.bufs = s.bufs ∧ s'.caps = s.caps := by
  have hp : 0 < p := (Fact.out (p := p.Prime)).pos
  obtain ⟨s', tt, dd, pp, hex, hout, hpres, hbuf, hcap⟩ :=
    montAdd_exec (C := C) hl hp hpR (montVal_lt k x) (montVal_lt k y) hpr har hbr
  refine ⟨s', tt, dd, pp, hex, ?_, hpres, hbuf, hcap⟩
  have hsum : (montVal k x + montVal k y) % p = montVal k (x + y) := by
    refine eq_montVal (Nat.mod_lt _ hp) ?_
    rw [ZMod.natCast_mod]
    push_cast
    rw [montVal_cast, montVal_cast]
    ring
  rwa [hsum] at hout

/-- **Multiplication of Montgomery forms.** -/
theorem montMulSOS_field {k' a b pReg pinv w : ℕ}
    (hl : SOSLayout (k' + 1) a b pReg pinv w)
    {s : State 64} {pv : ℕ} {x y : F p}
    (hp2 : 2 < p) (hpR : p < 2 ^ (64 * (k' + 1)))
    (hpinv : (p * pv + 1) % 2 ^ 64 = 0)
    (hpr : RegsEnc s pReg (k' + 2) p) (hcr : s.regs pinv = BitVec.ofNat 64 pv)
    (har : RegsEnc s a (k' + 1) (montVal (k' + 1) x))
    (hbr : RegsEnc s b (k' + 1) (montVal (k' + 1) y)) :
    ∃ s' tt dd pp, Exec C (montMulSOS (k' + 1) a b pReg pinv w) s s' tt dd pp ∧
      RegsEnc s' (montOut (k' + 1) w) (k' + 1) (montVal (k' + 1) (x * y)) ∧
      (∀ q, q < w → s'.regs q = s.regs q) ∧
      s'.bufs = s.bufs ∧ s'.caps = s.caps := by
  have hp : 0 < p := (Fact.out (p := p.Prime)).pos
  have hAB : montVal (k' + 1) x * montVal (k' + 1) y < p * 2 ^ (64 * (k' + 1)) :=
    Nat.mul_lt_mul'' (montVal_lt (k' + 1) x)
      (lt_trans (montVal_lt (k' + 1) y) hpR)
  obtain ⟨s', tt, dd, pp, hex, ⟨V, hV, hVlt, hVmod⟩, hpres, hbuf, hcap⟩ :=
    montMulSOS_exec (C := C) hl hp hpR hpinv
      (lt_trans (montVal_lt (k' + 1) x) hpR) (lt_trans (montVal_lt (k' + 1) y) hpR)
      hAB hpr hcr har hbr
  refine ⟨s', tt, dd, pp, hex, ?_, hpres, hbuf, hcap⟩
  have hval : V = montVal (k' + 1) (x * y) := by
    refine eq_montVal hVlt ?_
    have hc := cast_modEq hVmod
    push_cast at hc
    rw [montVal_cast, montVal_cast] at hc
    exact mul_right_cancel₀ (two_pow_ne_zero hp2 (64 * (k' + 1))) (hc.trans (by ring))
  rwa [hval] at hV

/-- **A multiply by a generation-time constant**, with the result named by its field
equation rather than a congruence. -/
theorem montMulConst_field {k' c a pReg pinv w : ℕ}
    (hl : ConstLayout (k' + 1) a pReg pinv w)
    {s : State 64} {pv A : ℕ}
    (hpR : p < 2 ^ (64 * (k' + 1))) (hpinv : (p * pv + 1) % 2 ^ 64 = 0)
    (hA : A < 2 ^ (64 * (k' + 1))) (hc : c < p)
    (hpr : RegsEnc s pReg (k' + 2) p) (hcr : s.regs pinv = BitVec.ofNat 64 pv)
    (har : RegsEnc s a (k' + 1) A) :
    ∃ s' tt dd pp V, Exec C (montMulConst (k' + 1) c a pReg pinv w) s s' tt dd pp ∧
      V < p ∧ (V : F p) * (2 : F p) ^ (64 * (k' + 1)) = (A : F p) * (c : F p) ∧
      RegsEnc s' (montMulConstOut (k' + 1) w) (k' + 1) V ∧
      (∀ q, q < w → s'.regs q = s.regs q) ∧
      s'.bufs = s.bufs ∧ s'.caps = s.caps := by
  have hp : 0 < p := (Fact.out (p := p.Prime)).pos
  obtain ⟨s', tt, dd, pp, hex, ⟨V, hV, hVlt, hVmod⟩, hpres, hbuf, hcap⟩ :=
    montMulConst_exec (C := C) hl hp hpR hpinv hA hc hpr hcr har
  refine ⟨s', tt, dd, pp, V, hex, hVlt, ?_, hV, hpres, hbuf, hcap⟩
  have hcst := cast_modEq hVmod
  push_cast at hcst
  exact hcst

/-! ### The conversions

`leaveMont` and `enterMont` are the same gadget at two generation-time constants,
and the inversion is the gcd followed by a third. -/

/-- What the prelude leaves in place and every field gadget reads. -/
structure PreludeEnc (p pv k : ℕ) (s : State 64) : Prop where
  modulus : RegsEnc s 0 (k + 1) p
  const : s.regs (k + 1) = BitVec.ofNat 64 pv

/-- A prime above two is odd. -/
theorem odd_of_two_lt (hp2 : 2 < p) : p % 2 = 1 := by
  rcases Nat.even_or_odd p with he | ho
  · exact absurd ((Nat.Prime.even_iff (Fact.out (p := p.Prime))).mp he) (by omega)
  · exact Nat.odd_iff.mp ho

/-- The cast of a power of two reduced by the modulus. -/
theorem cast_two_pow_mod (n : ℕ) :
    ((2 ^ n % p : ℕ) : F p) = (2 : F p) ^ n := by
  rw [ZMod.natCast_mod]; push_cast; ring

/-- **Leaving Montgomery form** gives the canonical value. -/
theorem leaveMont_field {k' a w : ℕ} {s : State 64} {pv : ℕ} {x : F p}
    (hw : k' + 3 ≤ w) (haw : a + (k' + 1) ≤ w)
    (hp2 : 2 < p) (hpR : p < 2 ^ (64 * (k' + 1)))
    (hpinv : (p * pv + 1) % 2 ^ 64 = 0) (hpre : PreludeEnc p pv (k' + 1) s)
    (har : RegsEnc s a (k' + 1) (montVal (k' + 1) x)) :
    ∃ s' tt dd pp, Exec C (leaveMont (k' + 1) a w) s s' tt dd pp ∧
      RegsEnc s' (montMulConstOut (k' + 1) w) (k' + 1) x.val ∧
      (∀ q, q < w → s'.regs q = s.regs q) ∧
      s'.bufs = s.bufs ∧ s'.caps = s.caps := by
  obtain ⟨s', tt, dd, pp, V, hex, hVlt, hVeq, hV, hpres, hbuf, hcap⟩ :=
    montMulConst_field (C := C) (c := 1)
      ⟨haw, by omega, by omega⟩ hpR hpinv
      (lt_trans (montVal_lt (k' + 1) x) hpR) (by omega) hpre.modulus hpre.const har
  refine ⟨s', tt, dd, pp, hex, ?_, hpres, hbuf, hcap⟩
  have hval : V = x.val := by
    refine eq_of_natCast hVlt (ZMod.val_lt x) ?_
    rw [ZMod.natCast_val, ZMod.cast_id]
    rw [montVal_cast, Nat.cast_one, mul_one] at hVeq
    exact mul_right_cancel₀ (two_pow_ne_zero hp2 (64 * (k' + 1))) hVeq
  rwa [hval] at hV

/-- **Entering Montgomery form** from a canonical value. -/
theorem enterMont_field {k' a w A : ℕ} {s : State 64} {pv : ℕ} {x : F p}
    (hw : k' + 3 ≤ w) (haw : a + (k' + 1) ≤ w)
    (hp2 : 2 < p) (hpR : p < 2 ^ (64 * (k' + 1)))
    (hpinv : (p * pv + 1) % 2 ^ 64 = 0) (hpre : PreludeEnc p pv (k' + 1) s)
    (hA : A < 2 ^ (64 * (k' + 1))) (hAx : (A : F p) = x)
    (har : RegsEnc s a (k' + 1) A) :
    ∃ s' tt dd pp,
      Exec C (enterMont (k' + 1) (2 ^ (2 * (64 * (k' + 1))) % p) a w) s s' tt dd pp ∧
      RegsEnc s' (montMulConstOut (k' + 1) w) (k' + 1) (montVal (k' + 1) x) ∧
      (∀ q, q < w → s'.regs q = s.regs q) ∧
      s'.bufs = s.bufs ∧ s'.caps = s.caps := by
  have hp : 0 < p := (Fact.out (p := p.Prime)).pos
  obtain ⟨s', tt, dd, pp, V, hex, hVlt, hVeq, hV, hpres, hbuf, hcap⟩ :=
    montMulConst_field (C := C) (c := 2 ^ (2 * (64 * (k' + 1))) % p)
      ⟨haw, by omega, by omega⟩ hpR hpinv hA (Nat.mod_lt _ hp)
      hpre.modulus hpre.const har
  refine ⟨s', tt, dd, pp, hex, ?_, hpres, hbuf, hcap⟩
  have hval : V = montVal (k' + 1) x := by
    refine eq_montVal hVlt ?_
    rw [cast_two_pow_mod, hAx] at hVeq
    refine mul_right_cancel₀ (two_pow_ne_zero hp2 (64 * (k' + 1))) (hVeq.trans ?_)
    rw [show 2 * (64 * (k' + 1)) = 64 * (k' + 1) + 64 * (k' + 1) by ring, pow_add]
    ring
  rwa [hval] at hV

/-- **The inversion.** The gcd inverts the Montgomery form itself, giving
`(x·R)⁻¹ = x⁻¹·R⁻¹`; one multiply by `R³` brings that back to `x⁻¹·R`. At `x = 0` the
gcd's input is zero, its loop does no rows, and the zero it started from is the
answer — which is what the IR's `0⁻¹ = 0` asks for. -/
theorem montInv_field {k' a w : ℕ} {s : State 64} {pv : ℕ} {x : F p}
    (hw : k' + 4 ≤ w) (haw : a + (k' + 1) ≤ w)
    (hp2 : 2 < p) (hpR : p < 2 ^ (64 * (k' + 1)))
    (hpinv : (p * pv + 1) % 2 ^ 64 = 0) (hk : 128 * (k' + 1) < 2 ^ 64)
    (hpre : PreludeEnc p pv (k' + 1) s)
    (har : RegsEnc s a (k' + 1) (montVal (k' + 1) x)) :
    ∃ s' tt dd pp,
      Exec C (invLimbs (k' + 1) a 0 w ;;
        montMulConst (k' + 1) (2 ^ (3 * (64 * (k' + 1))) % p) (invOut (k' + 1) w) 0
          (k' + 1 + 1) (w + 5 * (k' + 1) + 16)) s s' tt dd pp ∧
      RegsEnc s' (montMulConstOut (k' + 1) (w + 5 * (k' + 1) + 16)) (k' + 1)
        (montVal (k' + 1) x⁻¹) ∧
      (∀ q, q < w → s'.regs q = s.regs q) ∧
      s'.bufs = s.bufs ∧ s'.caps = s.caps := by
  have hp : 0 < p := (Fact.out (p := p.Prime)).pos
  have hRf : (2 : F p) ^ (64 * (k' + 1)) ≠ 0 := two_pow_ne_zero hp2 _
  obtain ⟨s₁, t₁, d₁, q₁, hex₁, ⟨S, hS, hSlt, hSzero, hSinv⟩, hpres₁, hbuf₁, hcap₁⟩ :=
    invLimbs_exec (C := C) (show 0 + (k' + 1) ≤ w by omega) haw hk
      (odd_of_two_lt hp2) hpR (by omega) (montVal_lt (k' + 1) x) har
      (fun j hj => hpre.modulus j (by omega))
  have hpre₁ : PreludeEnc p pv (k' + 1) s₁ :=
    ⟨fun j hj => by rw [hpres₁ _ (by omega)]; exact hpre.modulus j hj,
      by rw [hpres₁ _ (by omega)]; exact hpre.const⟩
  obtain ⟨s', tt, dd, pp, V, hex, hVlt, hVeq, hV, hpres, hbuf, hcap⟩ :=
    montMulConst_field (C := C) (c := 2 ^ (3 * (64 * (k' + 1))) % p)
      ⟨show invOut (k' + 1) w + (k' + 1) ≤ w + 5 * (k' + 1) + 16 by
        simp only [invOut]; omega, by omega, by omega⟩
      hpR hpinv (lt_trans hSlt hpR) (Nat.mod_lt _ hp) hpre₁.modulus hpre₁.const hS
  refine ⟨s', _, _, _, .seq hex₁ hex, ?_, ?_, hbuf.trans hbuf₁, hcap.trans hcap₁⟩
  · have hval : V = montVal (k' + 1) x⁻¹ := by
      refine eq_montVal hVlt ?_
      rw [cast_two_pow_mod] at hVeq
      -- `hVeq : (V : F p) * R = (S : F p) * 2 ^ (3 * (64 * (k' + 1)))`
      rw [show 3 * (64 * (k' + 1))
            = 64 * (k' + 1) + (64 * (k' + 1) + 64 * (k' + 1)) by ring,
        pow_add, pow_add] at hVeq
      refine mul_right_cancel₀ hRf (hVeq.trans ?_)
      by_cases hx : x = 0
      · subst hx
        have hA0 : montVal (k' + 1) (0 : F p) = 0 := by
          simp [montVal, ZMod.val_zero]
        rw [hSzero hA0]
        simp
      · have hcop : Nat.gcd (montVal (k' + 1) x) p = 1 := by
          have hA0 : montVal (k' + 1) x ≠ 0 := by
            intro h
            have := montVal_cast (k' + 1) x
            rw [h] at this
            exact hx (by
              have h0 : (0 : F p) = x * (2 : F p) ^ (64 * (k' + 1)) := by
                simpa using this
              exact (mul_eq_zero.mp h0.symm).resolve_right hRf)
          have hnd : ¬ p ∣ montVal (k' + 1) x := fun hd =>
            absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hA0) hd)
              (by have := montVal_lt (k' + 1) x; omega)
          exact Nat.Coprime.symm
            ((Nat.Prime.coprime_iff_not_dvd (Fact.out (p := p.Prime))).mpr hnd)
        have hSA := cast_modEq (hSinv hcop)
        push_cast at hSA
        rw [montVal_cast] at hSA
        -- `hSA : (S : F p) * (x * R) = 1`
        refine mul_right_cancel₀ hx ?_
        calc (S : F p) * ((2 : F p) ^ (64 * (k' + 1))
                * ((2 : F p) ^ (64 * (k' + 1)) * (2 : F p) ^ (64 * (k' + 1)))) * x
            = ((S : F p) * (x * (2 : F p) ^ (64 * (k' + 1))))
              * ((2 : F p) ^ (64 * (k' + 1)) * (2 : F p) ^ (64 * (k' + 1))) := by ring
          _ = (2 : F p) ^ (64 * (k' + 1)) * (2 : F p) ^ (64 * (k' + 1)) := by
              rw [hSA, one_mul]
          _ = x⁻¹ * (2 : F p) ^ (64 * (k' + 1))
              * (2 : F p) ^ (64 * (k' + 1)) * x := by
              rw [show x⁻¹ * (2 : F p) ^ (64 * (k' + 1))
                    * (2 : F p) ^ (64 * (k' + 1)) * x
                  = (x⁻¹ * x) * ((2 : F p) ^ (64 * (k' + 1))
                    * (2 : F p) ^ (64 * (k' + 1))) by ring,
                inv_mul_cancel₀ hx, one_mul]
    rwa [hval] at hV
  · intro q hq
    rw [hpres q (by omega), hpres₁ q hq]

end FieldGadgets

end Caliper.MultiLimb
