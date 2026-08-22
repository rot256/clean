import Clean.Caliper.Limbs
import Std.Tactic.BVDecide

/-!
# Multi-limb machine arithmetic, at the 64-bit surface

`Stmt`-level gadgets over values held in `k` consecutive registers, little-endian in
base `2 ^ 64` (`Clean/Caliper/Limbs.lean`), with their `Exec` specifications.

This is the arithmetic the witgen compiler needs to lower field operations over a
modulus too large for one word. `fieldOp`'s single `umod` is correct only for
`p * p ≤ 2 ^ 64`, i.e. `p ≤ 2 ^ 32`, which admits BabyBear and Mersenne31 and
excludes Goldilocks (a 64-bit prime) and every pairing-friendly field.

The word size stays 64 throughout, deliberately. Widening `w` would "fix" large
moduli by making one instruction an arbitrarily wide multiply, and Caliper prices an
instruction by its opcode, not its width: a 254-bit multiply would cost one unit
step, and the compilation contract that a DSL step is a constant number of CPU
instructions would be false. Large moduli are paid for in limb count, which shows up
honestly in the instruction count. The limb count `k` is a generation-time value, so
everything here unrolls to straight-line code and stays statically priced.

Values are unsigned naturals `< 2 ^ (64 * k)`; the field layer on top (Montgomery
form, reduction, inversion) is a separate module.

## Register discipline

A gadget takes register *bases*: `a` names the `k` registers `a, …, a + k - 1`. The
specs require the operand, destination and scratch ranges to be pairwise disjoint,
which the compiler's fresh-register threading provides at every call site.
-/

namespace Caliper.MultiLimb

open Caliper Caliper.Limbs

/-! ## Register encoding -/

/-- Registers `r, …, r + k - 1` of `s` hold the base-`2 ^ 64` limbs of `v`. -/
def RegsEnc (s : State 64) (r k v : ℕ) : Prop :=
  ∀ i < k, s.regs (r + i) = BitVec.ofNat 64 (limb 64 v i)

/-- Limbs below the `k`-th see only `v % 2 ^ (64 * k)`. -/
theorem limb_mod {k v i : ℕ} (hi : i < k) : limb 64 (v % 2 ^ (64 * k)) i = limb 64 v i := by
  have hsplit : (2:ℕ) ^ (64 * k) = 2 ^ (64 * i) * 2 ^ (64 * (k - i)) := by
    rw [← pow_add]; congr 1; omega
  unfold limb
  rw [hsplit, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd]
  exact pow_dvd_pow 2 (by omega)

/-- `RegsEnc` only constrains the value modulo `2 ^ (64 * k)`. -/
theorem RegsEnc.congr {s : State 64} {r k v v' : ℕ} (h : RegsEnc s r k v)
    (hv : v % 2 ^ (64 * k) = v' % 2 ^ (64 * k)) : RegsEnc s r k v' := by
  intro i hi
  rw [h i hi, ← limb_mod (v := v) hi, hv, limb_mod hi]

/-! ## Addition

Per limb: add the operands, detect the wrap with `ult`, add the incoming carry,
detect that wrap too, and add the two carry bits — `add` rather than `or` because they are never both set
(`(2 ^ 64 - 1) + (2 ^ 64 - 1) + 1 < 2 ^ 65`), and addition is the easier of the two
to reason about. Five instructions per limb, plus the `imm` clearing the initial
carry.

Scratch layout: `sc` is the running carry, `sc + 1` a temporary, `sc + 2` and
`sc + 3` the two wrap bits. -/

/-- The limb step at index `i`. -/
def addStep (d a b sc i : ℕ) : Stmt 64 :=
  .bin .add (sc + 1) (a + i) (b + i) ;;
  .bin .ult (sc + 2) (sc + 1) (a + i) ;;
  .bin .add (d + i) (sc + 1) sc ;;
  .bin .ult (sc + 3) (d + i) (sc + 1) ;;
  .bin .add sc (sc + 2) (sc + 3)

/-- The first `n` limb steps. -/
def addLoop (d a b sc : ℕ) : ℕ → Stmt 64
  | 0 => .skip
  | n + 1 => addLoop d a b sc n ;; addStep d a b sc n

/-- `d ← a + b + c0` over `k` limbs, carry-out in `sc`. `c0` is an immediate: `0` for
plain addition, `1` for the `A + ~B + 1` form of subtraction. -/
def addLimbsC (k d a b sc c0 : ℕ) : Stmt 64 :=
  .imm sc (BitVec.ofNat 64 c0) ;; addLoop d a b sc k

/-- `d ← a + b` over `k` limbs, leaving the carry-out in `sc`. -/
def addLimbs (k d a b sc : ℕ) : Stmt 64 := addLimbsC k d a b sc 0

/-- The low `n` limbs of both operands plus the initial carry: the quantity the first
`n` limb steps have consumed. `c0` is `0` for a plain addition and `1` for the
`A + ~B + 1` form of subtraction. -/
def partialSum (X Y c0 n : ℕ) : ℕ := X % 2 ^ (64 * n) + Y % 2 ^ (64 * n) + c0

/-- The arithmetic of one carry step, in `ℕ`: the wrapped sum plus the incoming carry
is the low word, and the two wrap bits sum to the carry-out. -/
theorem carry_step {x y c : ℕ} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (hc : c ≤ 1) :
    ((x + y) % 2 ^ 64 + c) % 2 ^ 64 = (x + y + c) % 2 ^ 64 ∧
      (if (x + y) % 2 ^ 64 < x then 1 else 0)
        + (if ((x + y) % 2 ^ 64 + c) % 2 ^ 64 < (x + y) % 2 ^ 64 then 1 else 0)
        = (x + y + c) / 2 ^ 64 := by
  split_ifs <;> omega

/-! ### Arithmetic of one limb position -/

/-- One more limb of each operand joins the running sum. -/
theorem partialSum_succ (X Y c0 n : ℕ) :
    partialSum X Y c0 (n + 1) = partialSum X Y c0 n + (limb 64 X n + limb 64 Y n) * 2 ^ (64 * n) := by
  have hsplit : ∀ v : ℕ, v % 2 ^ (64 * (n + 1))
      = v % 2 ^ (64 * n) + limb 64 v n * 2 ^ (64 * n) := by
    intro v
    have hpow : (2:ℕ) ^ (64 * (n + 1)) = 2 ^ (64 * n) * 2 ^ 64 := by
      rw [← pow_add]; ring_nf
    rw [hpow, mod_mul_split, limb]
    ring
  simp only [partialSum, hsplit]
  ring

/-- The running carry is a single bit. -/
theorem partialSum_div_le_one (X Y c0 n : ℕ) (hc0 : c0 ≤ 1) :
    partialSum X Y c0 n / 2 ^ (64 * n) ≤ 1 := by
  have hM : 0 < 2 ^ (64 * n) := Nat.two_pow_pos _
  have hlt : partialSum X Y c0 n < 2 * 2 ^ (64 * n) := by
    have hX := Nat.mod_lt X hM
    have hY := Nat.mod_lt Y hM
    simp only [partialSum]
    omega
  have := (Nat.div_lt_iff_lt_mul hM).mpr hlt
  omega

section Shift

variable {low T n : ℕ}

/-- Limbs below the shift see only the low part. -/
theorem limb_add_shift_lt {i : ℕ} (hi : i < n) :
    limb 64 (low + T * 2 ^ (64 * n)) i = limb 64 low i := by
  have hmod : (low + T * 2 ^ (64 * n)) % 2 ^ (64 * (i + 1)) = low % 2 ^ (64 * (i + 1)) := by
    obtain ⟨c, hc⟩ := pow_dvd_pow 2 (show 64 * (i + 1) ≤ 64 * n by omega)
    rw [hc, show T * (2 ^ (64 * (i + 1)) * c) = T * c * 2 ^ (64 * (i + 1)) by ring,
      Nat.add_mul_mod_self_right]
  rw [← limb_mod (k := i + 1) (by omega), ← limb_mod (v := low) (k := i + 1) (by omega), hmod]

/-- The limb at the shift is the low word of the shifted quantity. -/
theorem limb_add_shift_eq (hlow : low < 2 ^ (64 * n)) :
    limb 64 (low + T * 2 ^ (64 * n)) n = T % 2 ^ 64 := by
  rw [limb, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hlow, Nat.zero_add]

/-- Everything above the shift is the shifted quantity's carry. -/
theorem div_add_shift (hlow : low < 2 ^ (64 * n)) :
    (low + T * 2 ^ (64 * n)) / 2 ^ (64 * (n + 1)) = T / 2 ^ 64 := by
  have hpow : (2:ℕ) ^ (64 * (n + 1)) = 2 ^ (64 * n) * 2 ^ 64 := by
    rw [← pow_add]; ring_nf
  rw [hpow, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt hlow, Nat.zero_add]

end Shift

/-- Re-associating a quotient/remainder split across an added multiple. -/
theorem split_of_div_mod (P M x y : ℕ) :
    P + (x + y) * M = P % M + (P / M + x + y) * M := by
  have h1 : M * (P / M) + P % M = P := Nat.div_add_mod _ _
  calc P + (x + y) * M = M * (P / M) + P % M + (x + y) * M := by rw [h1]
    _ = P % M + (P / M + x + y) * M := by ring

/-! ### Correctness of one limb step -/

variable {C : CostModel}

/-- One limb step: from the two operand limbs and the incoming carry, the destination
limb holds the low word of their sum and the scratch register the carry-out. Only the
scratch block and `d + n` are written. -/
theorem addStep_exec {d a b sc n : ℕ} (hA : a + n < sc) (hD : sc + 4 ≤ d)
    {s : State 64} {x y c : ℕ} (hxlt : x < 2 ^ 64) (hylt : y < 2 ^ 64) (hc : c ≤ 1)
    (hax : s.regs (a + n) = BitVec.ofNat 64 x)
    (hby : s.regs (b + n) = BitVec.ofNat 64 y)
    (hsc : s.regs sc = BitVec.ofNat 64 c) :
    ∃ s' t dd pp, Exec C (addStep d a b sc n) s s' t dd pp ∧
      s'.regs (d + n) = BitVec.ofNat 64 ((x + y + c) % 2 ^ 64) ∧
      s'.regs sc = BitVec.ofNat 64 ((x + y + c) / 2 ^ 64) ∧
      (∀ q, q ≠ sc → q ≠ sc + 1 → q ≠ sc + 2 → q ≠ sc + 3 → q ≠ d + n →
        s'.regs q = s.regs q) ∧
      s'.bufs = s.bufs ∧ s'.caps = s.caps := by
  obtain ⟨hword, hcarry⟩ := carry_step hxlt hylt hc
  refine ⟨_, _, _, _,
    .seq .bin (.seq .bin (.seq .bin (.seq .bin .bin))), ?_, ?_, ?_, rfl, rfl⟩
  · simp only [regs_setReg_self, BinOp.eval,
      regs_setReg_ne _ _ (show a + n ≠ sc + 1 by omega),
      regs_setReg_ne _ _ (show sc + 1 ≠ sc + 2 by omega),
      regs_setReg_ne _ _ (show sc ≠ sc + 2 by omega),
      regs_setReg_ne _ _ (show sc ≠ sc + 1 by omega),
      regs_setReg_ne _ _ (show sc + 1 ≠ d + n by omega),
      regs_setReg_ne _ _ (show sc + 2 ≠ sc + 3 by omega),
      regs_setReg_ne _ _ (show sc + 2 ≠ d + n by omega),
      regs_setReg_ne _ _ (show d + n ≠ sc by omega),
      regs_setReg_ne _ _ (show d + n ≠ sc + 3 by omega),
      hax, hby, hsc]
    apply BitVec.eq_of_toNat_eq
    simp [Nat.add_mod]
  · simp only [regs_setReg_self, BinOp.eval,
      regs_setReg_ne _ _ (show a + n ≠ sc + 1 by omega),
      regs_setReg_ne _ _ (show sc + 1 ≠ sc + 2 by omega),
      regs_setReg_ne _ _ (show sc ≠ sc + 2 by omega),
      regs_setReg_ne _ _ (show sc ≠ sc + 1 by omega),
      regs_setReg_ne _ _ (show sc + 1 ≠ d + n by omega),
      regs_setReg_ne _ _ (show sc + 2 ≠ sc + 3 by omega),
      regs_setReg_ne _ _ (show sc + 2 ≠ d + n by omega),
      hax, hby, hsc]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hxlt,
      Nat.mod_eq_of_lt hylt, Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega)]
    rw [← hcarry]
    split_ifs <;> rfl
  · intro q h1 h2 h3 h4 h5
    rw [regs_setReg_ne _ _ h1, regs_setReg_ne _ _ h4, regs_setReg_ne _ _ h5,
      regs_setReg_ne _ _ h3, regs_setReg_ne _ _ h2]

/-! ### Correctness of the addition loop -/

/-- The register layout the addition gadget assumes, matching how the compiler
allocates: both operand ranges strictly below the scratch base, the destination range
above the scratch block. -/
structure AddLayout (k d a b sc : ℕ) : Prop where
  opA : a + k ≤ sc
  opB : b + k ≤ sc
  dest : sc + 4 ≤ d

/-- After `n` limb steps the destination holds the low `n` limbs of `X + Y` and the
scratch register holds the carry out of limb `n - 1`. Induction on `n`, with the
start state fixed and its carry register cleared. -/
theorem addLoop_exec {k d a b sc c0 : ℕ} (hl : AddLayout k d a b sc) (hc0 : c0 ≤ 1)
    {s : State 64} {X Y : ℕ} (ha : RegsEnc s a k X) (hb : RegsEnc s b k Y)
    (hsc : s.regs sc = BitVec.ofNat 64 c0) :
    ∀ n ≤ k, ∃ s' t dd pp, Exec C (addLoop d a b sc n) s s' t dd pp ∧
      RegsEnc s' d n (partialSum X Y c0 n) ∧
      s'.regs sc = BitVec.ofNat 64 (partialSum X Y c0 n / 2 ^ (64 * n)) ∧
      (∀ q, q < sc → s'.regs q = s.regs q) ∧
      s'.bufs = s.bufs ∧ s'.caps = s.caps := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨s, 0, 0, 0, .skip, ?_, ?_, fun _ _ => rfl, rfl, rfl⟩
    · intro i hi; omega
    · simpa [partialSum, Nat.mod_one, Nat.div_one] using hsc
  | succ n ih =>
    intro hn
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hd₁, hc₁, hpres₁, hbuf₁, hcap₁⟩ := ih (by omega)
    have hxlt : limb 64 X n < 2 ^ 64 := limb_lt _ _ _
    have hylt : limb 64 Y n < 2 ^ 64 := limb_lt _ _ _
    have hclt : partialSum X Y c0 n / 2 ^ (64 * n) ≤ 1 := partialSum_div_le_one X Y c0 n hc0
    -- the operands are below the scratch base, so `n` steps have not touched them
    have hA := hl.opA
    have hB := hl.opB
    have hD := hl.dest
    have hax : s₁.regs (a + n) = BitVec.ofNat 64 (limb 64 X n) := by
      rw [hpres₁ _ (by omega)]; exact ha n (by omega)
    have hby : s₁.regs (b + n) = BitVec.ofNat 64 (limb 64 Y n) := by
      rw [hpres₁ _ (by omega)]; exact hb n (by omega)
    -- the running sum, split at the limb boundary
    have hlow : partialSum X Y c0 n % 2 ^ (64 * n) < 2 ^ (64 * n) :=
      Nat.mod_lt _ (Nat.two_pow_pos _)
    have hsplit : partialSum X Y c0 (n + 1)
        = partialSum X Y c0 n % 2 ^ (64 * n)
          + (partialSum X Y c0 n / 2 ^ (64 * n) + limb 64 X n + limb 64 Y n) * 2 ^ (64 * n) := by
      rw [partialSum_succ]; exact split_of_div_mod _ _ _ _
    have hPsplit : partialSum X Y c0 n
        = partialSum X Y c0 n % 2 ^ (64 * n)
          + partialSum X Y c0 n / 2 ^ (64 * n) * 2 ^ (64 * n) := by
      have h1 : 2 ^ (64 * n) * (partialSum X Y c0 n / 2 ^ (64 * n))
          + partialSum X Y c0 n % 2 ^ (64 * n) = partialSum X Y c0 n := Nat.div_add_mod _ _
      calc partialSum X Y c0 n
          = 2 ^ (64 * n) * (partialSum X Y c0 n / 2 ^ (64 * n))
            + partialSum X Y c0 n % 2 ^ (64 * n) := h1.symm
        _ = partialSum X Y c0 n % 2 ^ (64 * n)
            + partialSum X Y c0 n / 2 ^ (64 * n) * 2 ^ (64 * n) := by ring
    obtain ⟨hword, hcarry⟩ := carry_step (x := limb 64 X n) (y := limb 64 Y n)
      (c := partialSum X Y c0 n / 2 ^ (64 * n)) hxlt hylt hclt
    have hT : limb 64 X n + limb 64 Y n + partialSum X Y c0 n / 2 ^ (64 * n)
        = partialSum X Y c0 n / 2 ^ (64 * n) + limb 64 X n + limb 64 Y n := by ring
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hdn, hsc₂, hpres₂, hbuf₂, hcap₂⟩ :=
      addStep_exec (C := C) (n := n) (by omega) (by omega) hxlt hylt hclt hax hby hc₁
    refine ⟨s₂, _, _, _, .seq hex₁ hex₂, ?_, ?_, ?_, hbuf₂.trans hbuf₁, hcap₂.trans hcap₁⟩
    · intro i hi
      rcases Nat.lt_or_ge i n with hlt | hge
      · have hL : limb 64 (partialSum X Y c0 n) i
            = limb 64 (partialSum X Y c0 n % 2 ^ (64 * n)) i := by
          conv_lhs => rw [hPsplit]
          exact limb_add_shift_lt hlt
        have hR : limb 64 (partialSum X Y c0 (n + 1)) i
            = limb 64 (partialSum X Y c0 n % 2 ^ (64 * n)) i := by
          rw [hsplit]; exact limb_add_shift_lt hlt
        rw [hpres₂ _ (by omega) (by omega) (by omega) (by omega) (by omega), hd₁ i hlt,
          hL, hR]
      · have : i = n := by omega
        subst this
        rw [hdn, hsplit, limb_add_shift_eq hlow, hT]
    · rw [hsc₂, hsplit, div_add_shift hlow, hT]
    · intro q hq
      rw [hpres₂ _ (by omega) (by omega) (by omega) (by omega) (by omega), hpres₁ q hq]

/-- `addLimbsC`: from `k`-limb operands and an initial carry, the destination holds
the `k`-limb sum and the scratch register the carry out of the top limb, so `sc`
together with `d` is the exact `k + 1`-limb value of `X + Y + c0`. -/
theorem addLimbsC_exec {k d a b sc c0 : ℕ} (hl : AddLayout k d a b sc) (hc0 : c0 ≤ 1)
    {s : State 64} {X Y : ℕ} (hX : X < 2 ^ (64 * k)) (hY : Y < 2 ^ (64 * k))
    (ha : RegsEnc s a k X) (hb : RegsEnc s b k Y) :
    ∃ s' t dd pp, Exec C (addLimbsC k d a b sc c0) s s' t dd pp ∧
      RegsEnc s' d k (X + Y + c0) ∧
      s'.regs sc = BitVec.ofNat 64 ((X + Y + c0) / 2 ^ (64 * k)) ∧
      (∀ q, q < sc → s'.regs q = s.regs q) ∧
      s'.bufs = s.bufs ∧ s'.caps = s.caps := by
  have hA := hl.opA
  have hB := hl.opB
  have hsum : partialSum X Y c0 k = X + Y + c0 := by
    simp only [partialSum, Nat.mod_eq_of_lt hX, Nat.mod_eq_of_lt hY]
  have ha' : RegsEnc (s.setReg sc (BitVec.ofNat 64 c0)) a k X := by
    intro i hi; rw [regs_setReg_ne _ _ (show a + i ≠ sc by omega)]; exact ha i hi
  have hb' : RegsEnc (s.setReg sc (BitVec.ofNat 64 c0)) b k Y := by
    intro i hi; rw [regs_setReg_ne _ _ (show b + i ≠ sc by omega)]; exact hb i hi
  have hsc' : (s.setReg sc (BitVec.ofNat 64 c0)).regs sc = BitVec.ofNat 64 c0 := by simp
  obtain ⟨s', t', d', p', hex, hd, hc, hpres, hbuf, hcap⟩ :=
    addLoop_exec (C := C) hl hc0 ha' hb' hsc' k le_rfl
  refine ⟨s', _, _, _, .seq .imm hex, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hsum]; exact hd
  · rw [hc, hsum]
  · intro q hq
    rw [hpres q hq, regs_setReg_ne _ _ (show q ≠ sc by omega)]
  · simpa using hbuf
  · simpa using hcap

/-- Plain addition: `addLimbsC` at initial carry `0`. -/
theorem addLimbs_exec {k d a b sc : ℕ} (hl : AddLayout k d a b sc)
    {s : State 64} {X Y : ℕ} (hX : X < 2 ^ (64 * k)) (hY : Y < 2 ^ (64 * k))
    (ha : RegsEnc s a k X) (hb : RegsEnc s b k Y) :
    ∃ s' t dd pp, Exec C (addLimbs k d a b sc) s s' t dd pp ∧
      RegsEnc s' d k (X + Y) ∧
      s'.regs sc = BitVec.ofNat 64 ((X + Y) / 2 ^ (64 * k)) ∧
      (∀ q, q < sc → s'.regs q = s.regs q) ∧
      s'.bufs = s.bufs ∧ s'.caps = s.caps := by
  obtain ⟨s', t', d', p', hex, hd, hc, hpres, hbuf, hcap⟩ :=
    addLimbsC_exec (C := C) (c0 := 0) hl (by omega) hX hY ha hb
  refine ⟨s', t', d', p', hex, ?_, ?_, hpres, hbuf, hcap⟩
  · simpa using hd
  · simpa using hc

/-! ## Multiply-accumulate

`acc += x * y` with `x` a `k`-limb value and `y` a single word. This is the inner
loop of *both* halves of a CIOS Montgomery multiplication — the product half
accumulates `a * b[i]`, the reduction half accumulates `m * p` — so proving it once
is what keeps the field layer tractable.

Per limb: the `2 ^ 64`-wide product via `mul`/`mulhi`, then a three-way add of
`acc[j] + lo + carry` whose two wrap bits join the product's high word to form the
outgoing carry. Eight instructions per limb.

The outgoing carry cannot overflow: `acc[j] + x[j] * y + c ≤ (2^64 - 1) +
(2^64 - 1)^2 + (2^64 - 1) = 2^128 - 1`, so the quotient stays below `2 ^ 64`. -/

/-- The three-way accumulate step, in `ℕ`. `P` is the full product `x[j] * y`, kept
abstract so the statement is linear and `omega` can close it. No bound on `P` is
needed for the identity itself; `mac_carry_lt` is what keeps the carry in a
register. -/
theorem mac_carry {aj P c : ℕ} (haj : aj < 2 ^ 64) (hc : c < 2 ^ 64) :
    ((aj + P % 2 ^ 64) % 2 ^ 64 + c) % 2 ^ 64 = (aj + P + c) % 2 ^ 64 ∧
      P / 2 ^ 64 + (if (aj + P % 2 ^ 64) % 2 ^ 64 < P % 2 ^ 64 then 1 else 0)
          + (if ((aj + P % 2 ^ 64) % 2 ^ 64 + c) % 2 ^ 64 < (aj + P % 2 ^ 64) % 2 ^ 64
              then 1 else 0)
        = (aj + P + c) / 2 ^ 64 := by
  split_ifs <;> omega

/-- The outgoing carry fits in a register: with `x[j]`, `y`, `acc[j]` and the incoming
carry all below `2 ^ 64`, the accumulated quantity is at most `2 ^ 128 - 1`. -/
theorem mac_carry_lt {aj xj y c : ℕ} (haj : aj < 2 ^ 64) (hxj : xj < 2 ^ 64)
    (hy : y < 2 ^ 64) (hc : c < 2 ^ 64) : (aj + xj * y + c) / 2 ^ 64 < 2 ^ 64 := by
  have hmul : xj * y ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  norm_num at hmul
  omega

/-- One multiply-accumulate limb step: `acc[j] += x[j] * y + carry`, low word back
into `acc + j`, carry-out into `sc`. Scratch: `sc + 1` the product's low word,
`sc + 2` its high word, `sc + 3` the partial sum, `sc + 4` and `sc + 5` the wrap
bits. -/
def macStep (acc x y sc j : ℕ) : Stmt 64 :=
  .bin .mul (sc + 1) (x + j) y ;;
  .bin .mulhi (sc + 2) (x + j) y ;;
  .bin .add (sc + 3) (acc + j) (sc + 1) ;;
  .bin .ult (sc + 4) (sc + 3) (sc + 1) ;;
  .bin .add (acc + j) (sc + 3) sc ;;
  .bin .ult (sc + 5) (acc + j) (sc + 3) ;;
  .bin .add (sc + 2) (sc + 2) (sc + 4) ;;
  .bin .add sc (sc + 2) (sc + 5)

theorem macStep_exec {acc x y sc j : ℕ}
    (hx : x + j < sc) (hy : y < sc) (hacc : sc + 6 ≤ acc)
    {s : State 64} {aj xj yv c : ℕ}
    (haj : aj < 2 ^ 64) (hxj : xj < 2 ^ 64) (hyv : yv < 2 ^ 64) (hc : c < 2 ^ 64)
    (hsx : s.regs (x + j) = BitVec.ofNat 64 xj)
    (hsy : s.regs y = BitVec.ofNat 64 yv)
    (hsa : s.regs (acc + j) = BitVec.ofNat 64 aj)
    (hsc : s.regs sc = BitVec.ofNat 64 c) :
    ∃ s' t dd pp, Exec C (macStep acc x y sc j) s s' t dd pp ∧
      s'.regs (acc + j) = BitVec.ofNat 64 ((aj + xj * yv + c) % 2 ^ 64) ∧
      s'.regs sc = BitVec.ofNat 64 ((aj + xj * yv + c) / 2 ^ 64) ∧
      (∀ q, q ≠ sc → q ≠ sc + 1 → q ≠ sc + 2 → q ≠ sc + 3 → q ≠ sc + 4 → q ≠ sc + 5 →
        q ≠ acc + j → s'.regs q = s.regs q) ∧
      s'.bufs = s.bufs ∧ s'.caps = s.caps := by
  obtain ⟨hword, hcarry⟩ := mac_carry (P := xj * yv) haj hc
  have hfit := mac_carry_lt haj hxj hyv hc
  refine ⟨_, _, _, _,
    .seq .bin (.seq .bin (.seq .bin (.seq .bin (.seq .bin (.seq .bin (.seq .bin .bin)))))),
    ?_, ?_, ?_, rfl, rfl⟩
  · simp only [regs_setReg_self, BinOp.eval,
      regs_setReg_ne _ _ (show acc + j ≠ sc by omega),
      regs_setReg_ne _ _ (show acc + j ≠ sc + 1 by omega),
      regs_setReg_ne _ _ (show acc + j ≠ sc + 2 by omega),
      regs_setReg_ne _ _ (show acc + j ≠ sc + 5 by omega),
      regs_setReg_ne _ _ (show sc ≠ sc + 1 by omega),
      regs_setReg_ne _ _ (show sc ≠ sc + 2 by omega),
      regs_setReg_ne _ _ (show sc ≠ sc + 3 by omega),
      regs_setReg_ne _ _ (show sc ≠ sc + 4 by omega),
      regs_setReg_ne _ _ (show sc + 1 ≠ sc + 2 by omega),
      regs_setReg_ne _ _ (show sc + 1 ≠ sc + 3 by omega),
      regs_setReg_ne _ _ (show sc + 2 ≠ sc + 3 by omega),
      regs_setReg_ne _ _ (show sc + 2 ≠ sc + 4 by omega),
      regs_setReg_ne _ _ (show sc + 2 ≠ sc + 5 by omega),
      regs_setReg_ne _ _ (show sc + 2 ≠ acc + j by omega),
      regs_setReg_ne _ _ (show sc + 3 ≠ sc + 4 by omega),
      regs_setReg_ne _ _ (show sc + 3 ≠ acc + j by omega),
      regs_setReg_ne _ _ (show sc + 4 ≠ sc + 5 by omega),
      regs_setReg_ne _ _ (show sc + 4 ≠ acc + j by omega),
      regs_setReg_ne _ _ (show sc + 5 ≠ sc + 2 by omega),
      hsx, hsy, hsa, hsc]
    apply BitVec.eq_of_toNat_eq
    simp [Nat.add_mod, Nat.mul_mod]
  · simp only [regs_setReg_self, BinOp.eval,
      regs_setReg_ne _ _ (show x + j ≠ sc + 1 by omega),
      regs_setReg_ne _ _ (show y ≠ sc + 1 by omega),
      regs_setReg_ne _ _ (show acc + j ≠ sc + 1 by omega),
      regs_setReg_ne _ _ (show acc + j ≠ sc + 2 by omega),
      regs_setReg_ne _ _ (show sc ≠ sc + 1 by omega),
      regs_setReg_ne _ _ (show sc ≠ sc + 2 by omega),
      regs_setReg_ne _ _ (show sc ≠ sc + 3 by omega),
      regs_setReg_ne _ _ (show sc ≠ sc + 4 by omega),
      regs_setReg_ne _ _ (show sc + 1 ≠ sc + 2 by omega),
      regs_setReg_ne _ _ (show sc + 1 ≠ sc + 3 by omega),
      regs_setReg_ne _ _ (show sc + 2 ≠ sc + 3 by omega),
      regs_setReg_ne _ _ (show sc + 2 ≠ sc + 4 by omega),
      regs_setReg_ne _ _ (show sc + 2 ≠ sc + 5 by omega),
      regs_setReg_ne _ _ (show sc + 2 ≠ acc + j by omega),
      regs_setReg_ne _ _ (show sc + 3 ≠ sc + 4 by omega),
      regs_setReg_ne _ _ (show sc + 3 ≠ acc + j by omega),
      regs_setReg_ne _ _ (show sc + 4 ≠ sc + 5 by omega),
      regs_setReg_ne _ _ (show sc + 4 ≠ acc + j by omega),
      regs_setReg_ne _ _ (show sc + 5 ≠ sc + 2 by omega),
      hsx, hsy, hsa, hsc]
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt haj, Nat.mod_eq_of_lt hxj, Nat.mod_eq_of_lt hyv, Nat.mod_eq_of_lt hc]
    rw [← hcarry]
    apply BitVec.eq_of_toNat_eq
    split_ifs <;> simp
  · intro q h0 h1 h2 h3 h4 h5 h6
    rw [regs_setReg_ne _ _ h0, regs_setReg_ne _ _ h2, regs_setReg_ne _ _ h5,
      regs_setReg_ne _ _ h6, regs_setReg_ne _ _ h4, regs_setReg_ne _ _ h3,
      regs_setReg_ne _ _ h2, regs_setReg_ne _ _ h1]

/-! ### The multiply-accumulate loop -/

/-- The quantity the first `n` limb steps of a multiply-accumulate have consumed:
the low `n` limbs of the accumulator plus the low `n` limbs of `x` times `y`. -/
def macSum (A X y n : ℕ) : ℕ := A % 2 ^ (64 * n) + (X % 2 ^ (64 * n)) * y

theorem macSum_succ (A X y n : ℕ) :
    macSum A X y (n + 1)
      = macSum A X y n + (limb 64 A n + limb 64 X n * y) * 2 ^ (64 * n) := by
  have hsplit : ∀ v : ℕ, v % 2 ^ (64 * (n + 1))
      = v % 2 ^ (64 * n) + limb 64 v n * 2 ^ (64 * n) := by
    intro v
    have hpow : (2:ℕ) ^ (64 * (n + 1)) = 2 ^ (64 * n) * 2 ^ 64 := by
      rw [← pow_add]; ring_nf
    rw [hpow, mod_mul_split, limb]
    ring
  simp only [macSum, hsplit]
  ring

/-- The running carry of a multiply-accumulate fits in a register. -/
theorem macSum_div_lt (A X y n : ℕ) (hy : y < 2 ^ 64) :
    macSum A X y n / 2 ^ (64 * n) < 2 ^ 64 := by
  have hM : 0 < 2 ^ (64 * n) := Nat.two_pow_pos _
  have hA := Nat.mod_lt A hM
  have hX := Nat.mod_lt X hM
  have hlt : macSum A X y n < 2 ^ (64 * n) * 2 ^ 64 := by
    simp only [macSum]
    nlinarith [hA, hX, hy]
  exact (Nat.div_lt_iff_lt_mul hM).mpr (by rw [mul_comm] at hlt; exact hlt)

/-- The first `n` multiply-accumulate limb steps. -/
def macLoop (acc x y sc : ℕ) : ℕ → Stmt 64
  | 0 => .skip
  | n + 1 => macLoop acc x y sc n ;; macStep acc x y sc n

/-- `acc += x * y` over `k` limbs, carry-out in `sc`. -/
def macLimbs (k acc x y sc : ℕ) : Stmt 64 := .imm sc 0 ;; macLoop acc x y sc k

/-- The register layout of a multiply-accumulate: multiplicand and scalar below the
scratch block, accumulator above it. -/
structure MacLayout (k acc x y sc : ℕ) : Prop where
  opX : x + k ≤ sc
  opY : y < sc
  dest : sc + 6 ≤ acc

/-- After `n` multiply-accumulate steps the accumulator's low `n` limbs hold
`macSum`'s low part and the scratch register its carry. The accumulator's limbs from
`n` up are untouched, which is what lets the next step read `A`'s limb `n`. -/
theorem macLoop_exec {k acc x y sc : ℕ} (hl : MacLayout k acc x y sc)
    {s : State 64} {A X yv : ℕ} (hyv : yv < 2 ^ 64)
    (hxr : RegsEnc s x k X) (haccr : RegsEnc s acc (k + 1) A)
    (hsy : s.regs y = BitVec.ofNat 64 yv)
    (hsc : s.regs sc = BitVec.ofNat 64 0) :
    ∀ n ≤ k, ∃ s' t dd pp, Exec C (macLoop acc x y sc n) s s' t dd pp ∧
      (∀ i < n, s'.regs (acc + i) = BitVec.ofNat 64 (limb 64 (macSum A X yv n) i)) ∧
      s'.regs sc = BitVec.ofNat 64 (macSum A X yv n / 2 ^ (64 * n)) ∧
      (∀ q, q < sc → s'.regs q = s.regs q) ∧
      (∀ i, n ≤ i → s'.regs (acc + i) = s.regs (acc + i)) ∧
      s'.bufs = s.bufs ∧ s'.caps = s.caps := by
  have hX := hl.opX
  have hY := hl.opY
  have hD := hl.dest
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨s, 0, 0, 0, .skip, ?_, ?_, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩
    · intro i hi; omega
    · simpa [macSum, Nat.mod_one, Nat.div_one] using hsc
  | succ n ih =>
    intro hn
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hd₁, hc₁, hpres₁, hhigh₁, hbuf₁, hcap₁⟩ := ih (by omega)
    have hcfit : macSum A X yv n / 2 ^ (64 * n) < 2 ^ 64 := macSum_div_lt A X yv n hyv
    have hxn : s₁.regs (x + n) = BitVec.ofNat 64 (limb 64 X n) := by
      rw [hpres₁ _ (by omega)]; exact hxr n (by omega)
    have hyn : s₁.regs y = BitVec.ofNat 64 yv := by rw [hpres₁ _ (by omega)]; exact hsy
    have han : s₁.regs (acc + n) = BitVec.ofNat 64 (limb 64 A n) := by
      rw [hhigh₁ n le_rfl]; exact haccr n (by omega)
    have hlow : macSum A X yv n % 2 ^ (64 * n) < 2 ^ (64 * n) :=
      Nat.mod_lt _ (Nat.two_pow_pos _)
    have hsplit : macSum A X yv (n + 1)
        = macSum A X yv n % 2 ^ (64 * n)
          + (macSum A X yv n / 2 ^ (64 * n) + limb 64 A n + limb 64 X n * yv)
            * 2 ^ (64 * n) := by
      rw [macSum_succ]; exact split_of_div_mod _ _ _ _
    have hPsplit : macSum A X yv n
        = macSum A X yv n % 2 ^ (64 * n)
          + macSum A X yv n / 2 ^ (64 * n) * 2 ^ (64 * n) := by
      have h1 : 2 ^ (64 * n) * (macSum A X yv n / 2 ^ (64 * n))
          + macSum A X yv n % 2 ^ (64 * n) = macSum A X yv n := Nat.div_add_mod _ _
      calc macSum A X yv n
          = 2 ^ (64 * n) * (macSum A X yv n / 2 ^ (64 * n))
            + macSum A X yv n % 2 ^ (64 * n) := h1.symm
        _ = macSum A X yv n % 2 ^ (64 * n)
            + macSum A X yv n / 2 ^ (64 * n) * 2 ^ (64 * n) := by ring
    have hT : limb 64 A n + limb 64 X n * yv + macSum A X yv n / 2 ^ (64 * n)
        = macSum A X yv n / 2 ^ (64 * n) + limb 64 A n + limb 64 X n * yv := by ring
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hdn, hsc₂, hpres₂, hbuf₂, hcap₂⟩ :=
      macStep_exec (C := C) (by omega) (by omega) (by omega)
        (limb_lt 64 A n) (limb_lt 64 X n) hyv hcfit hxn hyn han hc₁
    refine ⟨s₂, _, _, _, .seq hex₁ hex₂, ?_, ?_, ?_, ?_,
      hbuf₂.trans hbuf₁, hcap₂.trans hcap₁⟩
    · intro i hi
      rcases Nat.lt_or_ge i n with hlt | hge
      · have hL : limb 64 (macSum A X yv n) i
            = limb 64 (macSum A X yv n % 2 ^ (64 * n)) i := by
          conv_lhs => rw [hPsplit]
          exact limb_add_shift_lt hlt
        have hR : limb 64 (macSum A X yv (n + 1)) i
            = limb 64 (macSum A X yv n % 2 ^ (64 * n)) i := by
          rw [hsplit]; exact limb_add_shift_lt hlt
        rw [hpres₂ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega), hd₁ i hlt, hL, hR]
      · have : i = n := by omega
        subst this
        rw [hdn, hsplit, limb_add_shift_eq hlow, hT]
    · rw [hsc₂, hsplit, div_add_shift hlow, hT]
    · intro q hq
      rw [hpres₂ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega), hpres₁ q hq]
    · intro i hi
      rw [hpres₂ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega), hhigh₁ i (by omega)]

/-- `macLimbs`: `acc[0..k-1]` together with the carry in `sc` hold the exact
`k + 1`-word value of `A mod 2^(64k) + X * y`. The accumulator's limb `k` is left
untouched, so a CIOS driver can fold the carry into it. -/
theorem macLimbs_exec {k acc x y sc : ℕ} (hl : MacLayout k acc x y sc)
    {s : State 64} {A X yv : ℕ} (hyv : yv < 2 ^ 64) (hXlt : X < 2 ^ (64 * k))
    (hxr : RegsEnc s x k X) (haccr : RegsEnc s acc (k + 1) A)
    (hsy : s.regs y = BitVec.ofNat 64 yv) :
    ∃ s' t dd pp, Exec C (macLimbs k acc x y sc) s s' t dd pp ∧
      (∀ i < k, s'.regs (acc + i)
        = BitVec.ofNat 64 (limb 64 (A % 2 ^ (64 * k) + X * yv) i)) ∧
      s'.regs sc = BitVec.ofNat 64 ((A % 2 ^ (64 * k) + X * yv) / 2 ^ (64 * k)) ∧
      (∀ q, q < sc → s'.regs q = s.regs q) ∧
      (∀ i, k ≤ i → s'.regs (acc + i) = s.regs (acc + i)) ∧
      s'.bufs = s.bufs ∧ s'.caps = s.caps := by
  have hX := hl.opX
  have hY := hl.opY
  have hD := hl.dest
  have hsum : macSum A X yv k = A % 2 ^ (64 * k) + X * yv := by
    simp only [macSum, Nat.mod_eq_of_lt hXlt]
  have hxr' : RegsEnc (s.setReg sc 0) x k X := by
    intro i hi; rw [regs_setReg_ne _ _ (show x + i ≠ sc by omega)]; exact hxr i hi
  have haccr' : RegsEnc (s.setReg sc 0) acc (k + 1) A := by
    intro i hi; rw [regs_setReg_ne _ _ (show acc + i ≠ sc by omega)]; exact haccr i hi
  have hsy' : (s.setReg sc (0 : Word 64)).regs y = BitVec.ofNat 64 yv := by
    rw [regs_setReg_ne _ _ (show y ≠ sc by omega)]; exact hsy
  have hsc' : (s.setReg sc (0 : Word 64)).regs sc = BitVec.ofNat 64 0 := by simp
  obtain ⟨s', t', d', p', hex, hd, hc, hpres, hhigh, hbuf, hcap⟩ :=
    macLoop_exec (C := C) hl hyv hxr' haccr' hsy' hsc' k le_rfl
  refine ⟨s', _, _, _, .seq .imm hex, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; rw [hd i hi, hsum]
  · rw [hc, hsum]
  · intro q hq
    rw [hpres q hq, regs_setReg_ne _ _ (show q ≠ sc by omega)]
  · intro i hi
    rw [hhigh i hi, regs_setReg_ne _ _ (show acc + i ≠ sc by omega)]
  · simpa using hbuf
  · simpa using hcap

/-! ## Subtraction

The mirror of addition, with a borrow chain. Stated subtraction-free: the machine's
wrapping difference `t = (x + 2^64 - y) % 2^64` and the two borrow bits satisfy
`x + 2^64 * borrowOut = result + y + borrowIn`, an identity in `ℕ` with no truncating
subtraction anywhere, which is what makes `omega` able to close it. -/

theorem borrow_step {x y bw : ℕ} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (hbw : bw ≤ 1) :
    x + 2 ^ 64 * ((if x < y then 1 else 0)
        + (if (x + 2 ^ 64 - y) % 2 ^ 64 < bw then 1 else 0))
      = ((x + 2 ^ 64 - y) % 2 ^ 64 + 2 ^ 64 - bw) % 2 ^ 64 + y + bw := by
  split_ifs <;> omega

/-! ### Complement, and subtraction as `A + ~B + 1`

Rather than a second carry chain, subtraction complements `b` limb-wise and reuses
the adder at initial carry `1`: `A + ~B + 1 = A + 2 ^ (64k) - B`. The carry-out is
then the complement of the borrow — `1` means no borrow, i.e. `A ≥ B` — which is
exactly the bit a conditional subtract wants. Six instructions per limb. -/

/-- Limbs are unique below `k`: a limb function bounded by `2 ^ 64` that reconstructs
a value *is* that value's limb function. -/
theorem limb_ofLimbs {f : ℕ → ℕ} (hf : ∀ j, f j < 2 ^ 64) :
    ∀ k, ∀ i < k, limb 64 (ofLimbs 64 f k) i = f i
  | 0, _, hi => absurd hi (Nat.not_lt_zero _)
  | k + 1, i, hi => by
    have hlt : ofLimbs 64 f k < 2 ^ (64 * k) := ofLimbs_lt hf k
    rw [ofLimbs_succ]
    rcases Nat.lt_or_ge i k with h | h
    · rw [limb_add_shift_lt h]; exact limb_ofLimbs hf k i h
    · have : i = k := by omega
      subst this
      rw [limb_add_shift_eq hlt, Nat.mod_eq_of_lt (hf i)]

/-- Limb-wise complement of a value. -/
def complLimb (B i : ℕ) : ℕ := 2 ^ 64 - 1 - limb 64 B i

theorem complLimb_lt (B j : ℕ) : complLimb B j < 2 ^ 64 := by
  have := limb_lt 64 B j; simp only [complLimb]; omega

/-- The recursion step of `ofLimbs_compl`, with the modulus abstract so that `omega`
sees only linear atoms. -/
private theorem compl_step {L r b M : ℕ} (hM : 1 ≤ M) (hb : b < 2 ^ 64)
    (ih : L + r = M - 1) : L + (2 ^ 64 - 1 - b) * M + (r + b * M) = M * 2 ^ 64 - 1 := by
  have hcomb : (2 ^ 64 - 1 - b) * M + b * M = (2 ^ 64 - 1) * M := by
    rw [← Nat.add_mul]; congr 1; omega
  have hmul : (2 ^ 64 - 1) * M = M * 2 ^ 64 - M := by
    rw [Nat.sub_one_mul]; ring_nf
  omega

/-- The complement's limbs and the value's limbs sum to all-ones. -/
theorem ofLimbs_compl (B : ℕ) : ∀ n,
    ofLimbs 64 (complLimb B) n + B % 2 ^ (64 * n) = 2 ^ (64 * n) - 1
  | 0 => by simp [ofLimbs, Nat.mod_one]
  | n + 1 => by
    have ih := ofLimbs_compl B n
    have hpow : (2:ℕ) ^ (64 * (n + 1)) = 2 ^ (64 * n) * 2 ^ 64 := by
      rw [← pow_add]; ring_nf
    have hsplit : B % 2 ^ (64 * (n + 1))
        = B % 2 ^ (64 * n) + limb 64 B n * 2 ^ (64 * n) := by
      rw [hpow, mod_mul_split, limb]; ring
    rw [ofLimbs_succ, hsplit, hpow, complLimb]
    exact compl_step Nat.one_le_two_pow (limb_lt 64 B n) ih

/-- The complement of a `k`-limb value has the complemented limbs. -/
theorem limb_compl {k B : ℕ} (hB : B < 2 ^ (64 * k)) {i : ℕ} (hi : i < k) :
    limb 64 (2 ^ (64 * k) - 1 - B) i = complLimb B i := by
  have hval : ofLimbs 64 (complLimb B) k = 2 ^ (64 * k) - 1 - B := by
    have h := ofLimbs_compl B k
    rw [Nat.mod_eq_of_lt hB] at h
    omega
  rw [← hval]
  exact limb_ofLimbs (complLimb_lt B) k i hi

/-- Limb-wise complement of `b` into `nb`, first `n` limbs. -/
def notLoop (nb b : ℕ) : ℕ → Stmt 64
  | 0 => .skip
  | n + 1 => notLoop nb b n ;; .un .not (nb + n) (b + n)

/-- The register layout of a subtraction: the operands below the complement buffer,
the complement below the scratch block, the destination above it. -/
structure SubLayout (k d a b nb sc : ℕ) : Prop where
  opB : b + k ≤ nb
  opA : a + k ≤ nb
  cmpl : nb + k ≤ sc
  dest : sc + 4 ≤ d

/-- `d ← a - b` over `k` limbs, as `a + ~b + 1`. The carry-out in `sc` is `1` exactly
when `a ≥ b`, i.e. it is the complement of the borrow. -/
def subLimbs (k d a b nb sc : ℕ) : Stmt 64 :=
  notLoop nb b k ;; addLimbsC k d a nb sc 1

theorem notLoop_exec {k nb b : ℕ} (hlay : b + k ≤ nb)
    {s : State 64} {B : ℕ} (hbr : RegsEnc s b k B) :
    ∀ n ≤ k, ∃ s' t dd pp, Exec C (notLoop nb b n) s s' t dd pp ∧
      (∀ i < n, s'.regs (nb + i) = BitVec.ofNat 64 (complLimb B i)) ∧
      (∀ q, q < nb → s'.regs q = s.regs q) ∧
      s'.bufs = s.bufs ∧ s'.caps = s.caps := by
  intro n
  induction n with
  | zero =>
    intro _
    exact ⟨s, 0, 0, 0, .skip, fun i hi => absurd hi (Nat.not_lt_zero _),
      fun _ _ => rfl, rfl, rfl⟩
  | succ n ih =>
    intro hn
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hd₁, hpres₁, hbuf₁, hcap₁⟩ := ih (by omega)
    have hbn : s₁.regs (b + n) = BitVec.ofNat 64 (limb 64 B n) := by
      rw [hpres₁ _ (by omega)]; exact hbr n (by omega)
    refine ⟨_, _, _, _, .seq hex₁ .un, ?_, ?_, ?_, ?_⟩
    · intro i hi
      rcases Nat.lt_or_ge i n with hlt | hge
      · rw [regs_setReg_ne _ _ (show nb + i ≠ nb + n by omega)]; exact hd₁ i hlt
      · have hin : i = n := by omega
        rw [hin, regs_setReg_self, UnOp.eval, hbn]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_not, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (limb_lt 64 B n), Nat.mod_eq_of_lt (complLimb_lt B n)]
        rfl
    · intro q hq
      rw [regs_setReg_ne _ _ (show q ≠ nb + n by omega), hpres₁ q hq]
    · simpa using hbuf₁
    · simpa using hcap₁

/-- `subLimbs`: the destination holds the low `k` limbs of `a + 2 ^ (64k) - b`, and
`sc` holds `1` exactly when `a ≥ b`. -/
theorem subLimbs_exec {k d a b nb sc : ℕ} (hl : SubLayout k d a b nb sc)
    {s : State 64} {A B : ℕ} (hA : A < 2 ^ (64 * k)) (hB : B < 2 ^ (64 * k))
    (har : RegsEnc s a k A) (hbr : RegsEnc s b k B) :
    ∃ s' t dd pp, Exec C (subLimbs k d a b nb sc) s s' t dd pp ∧
      RegsEnc s' d k (A + 2 ^ (64 * k) - B) ∧
      s'.regs sc = BitVec.ofNat 64 ((A + 2 ^ (64 * k) - B) / 2 ^ (64 * k)) ∧
      (∀ q, q < nb → s'.regs q = s.regs q) ∧
      s'.bufs = s.bufs ∧ s'.caps = s.caps := by
  have hB' := hl.opB
  have hA' := hl.opA
  have hC := hl.cmpl
  have hD := hl.dest
  obtain ⟨s₁, t₁, d₁, p₁, hex₁, hnb, hpres₁, hbuf₁, hcap₁⟩ :=
    notLoop_exec (C := C) hB' hbr k le_rfl
  have hClt : 2 ^ (64 * k) - 1 - B < 2 ^ (64 * k) := by
    have : (1:ℕ) ≤ 2 ^ (64 * k) := Nat.one_le_two_pow
    omega
  have hnbr : RegsEnc s₁ nb k (2 ^ (64 * k) - 1 - B) := by
    intro i hi; rw [hnb i hi, limb_compl hB hi]
  have har₁ : RegsEnc s₁ a k A := by
    intro i hi; rw [hpres₁ _ (by omega)]; exact har i hi
  have hlay : AddLayout k d a nb sc := ⟨by omega, by omega, by omega⟩
  obtain ⟨s₂, t₂, d₂, p₂, hex₂, hd₂, hsc₂, hpres₂, hbuf₂, hcap₂⟩ :=
    addLimbsC_exec (C := C) (c0 := 1) hlay (by omega) hA hClt har₁ hnbr
  have hval : A + (2 ^ (64 * k) - 1 - B) + 1 = A + 2 ^ (64 * k) - B := by
    have : (1:ℕ) ≤ 2 ^ (64 * k) := Nat.one_le_two_pow
    omega
  refine ⟨s₂, _, _, _, .seq hex₁ hex₂, ?_, ?_, ?_,
    hbuf₂.trans hbuf₁, hcap₂.trans hcap₁⟩
  · rw [← hval]; exact hd₂
  · rw [hsc₂, hval]
  · intro q hq
    rw [hpres₂ q (by omega), hpres₁ q hq]

/-! ## Branch-free select

`d ← if f then a else b`, limb by limb, with `f` a `{0, 1}` word. Not a mask: in
wrapping arithmetic `b + f * (a - b)` already selects, which is three instructions per
limb with a *single* scratch register, where the mask formulation needs a two-
instruction preamble and four. No `ifNZ`, so the code stays straight-line. -/

theorem select_word {flag : ℕ} (hf : flag ≤ 1) (x y : Word 64) :
    y + BitVec.ofNat 64 flag * (x - y) = if flag = 1 then x else y := by
  have h : flag = 0 ∨ flag = 1 := by omega
  have hcancel : ∀ u v : Word 64, v + (u - v) = u := by
    intro u v
    apply BitVec.eq_of_toNat_eq
    have hu := u.isLt
    have hv := v.isLt
    simp only [BitVec.toNat_add, BitVec.toNat_sub]
    omega
  rcases h with h | h <;> subst h <;> simp [hcancel]

/-- The select step at limb `i`. -/
def selectStep (d a b f sc i : ℕ) : Stmt 64 :=
  .bin .sub sc (a + i) (b + i) ;;
  .bin .mul sc f sc ;;
  .bin .add (d + i) (b + i) sc

def selectLoop (d a b f sc : ℕ) : ℕ → Stmt 64
  | 0 => .skip
  | n + 1 => selectLoop d a b f sc n ;; selectStep d a b f sc n

/-- `d ← if f then a else b` over `k` limbs. -/
def selectLimbs (k d a b f sc : ℕ) : Stmt 64 := selectLoop d a b f sc k

/-- The register layout of a select: operands and flag below the scratch register,
destination above it. -/
structure SelLayout (k d a b f sc : ℕ) : Prop where
  opA : a + k ≤ sc
  opB : b + k ≤ sc
  flag : f < sc
  dest : sc + 1 ≤ d

theorem selectLoop_exec {k d a b f sc : ℕ} (hl : SelLayout k d a b f sc)
    {s : State 64} {A B flag : ℕ} (hflag : flag ≤ 1)
    (har : RegsEnc s a k A) (hbr : RegsEnc s b k B)
    (hsf : s.regs f = BitVec.ofNat 64 flag) :
    ∀ n ≤ k, ∃ s' t dd pp, Exec C (selectLoop d a b f sc n) s s' t dd pp ∧
      (∀ i < n, s'.regs (d + i)
        = BitVec.ofNat 64 (limb 64 (if flag = 1 then A else B) i)) ∧
      (∀ q, q < sc → s'.regs q = s.regs q) ∧
      s'.bufs = s.bufs ∧ s'.caps = s.caps := by
  have hA' := hl.opA
  have hB' := hl.opB
  have hF := hl.flag
  have hD := hl.dest
  intro n
  induction n with
  | zero =>
    intro _
    exact ⟨s, 0, 0, 0, .skip, fun i hi => absurd hi (Nat.not_lt_zero _),
      fun _ _ => rfl, rfl, rfl⟩
  | succ n ih =>
    intro hn
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hd₁, hpres₁, hbuf₁, hcap₁⟩ := ih (by omega)
    have han : s₁.regs (a + n) = BitVec.ofNat 64 (limb 64 A n) := by
      rw [hpres₁ _ (by omega)]; exact har n (by omega)
    have hbn : s₁.regs (b + n) = BitVec.ofNat 64 (limb 64 B n) := by
      rw [hpres₁ _ (by omega)]; exact hbr n (by omega)
    have hfn : s₁.regs f = BitVec.ofNat 64 flag := by
      rw [hpres₁ _ (by omega)]; exact hsf
    refine ⟨_, _, _, _, .seq hex₁ (.seq .bin (.seq .bin .bin)), ?_, ?_, ?_, ?_⟩
    · intro i hi
      rcases Nat.lt_or_ge i n with hlt | hge
      · rw [regs_setReg_ne _ _ (show d + i ≠ d + n by omega),
          regs_setReg_ne _ _ (show d + i ≠ sc by omega),
          regs_setReg_ne _ _ (show d + i ≠ sc by omega)]
        exact hd₁ i hlt
      · have hin : i = n := by omega
        rw [hin, regs_setReg_self]
        simp only [BinOp.eval, regs_setReg_self,
          regs_setReg_ne _ _ (show b + n ≠ sc by omega),
          regs_setReg_ne _ _ (show f ≠ sc by omega),
          han, hbn, hfn]
        rw [select_word hflag]
        by_cases hf1 : flag = 1 <;> simp [hf1]
    · intro q hq
      rw [regs_setReg_ne _ _ (show q ≠ d + n by omega),
        regs_setReg_ne _ _ (show q ≠ sc by omega),
        regs_setReg_ne _ _ (show q ≠ sc by omega), hpres₁ q hq]
    · simpa using hbuf₁
    · simpa using hcap₁

/-- `selectLimbs`: the destination holds `A` or `B` according to the flag. -/
theorem selectLimbs_exec {k d a b f sc : ℕ} (hl : SelLayout k d a b f sc)
    {s : State 64} {A B flag : ℕ} (hflag : flag ≤ 1)
    (har : RegsEnc s a k A) (hbr : RegsEnc s b k B)
    (hsf : s.regs f = BitVec.ofNat 64 flag) :
    ∃ s' t dd pp, Exec C (selectLimbs k d a b f sc) s s' t dd pp ∧
      RegsEnc s' d k (if flag = 1 then A else B) ∧
      (∀ q, q < sc → s'.regs q = s.regs q) ∧
      s'.bufs = s.bufs ∧ s'.caps = s.caps :=
  selectLoop_exec (C := C) hl hflag har hbr hsf k le_rfl

/-! ## CIOS Montgomery multiplication (code shape)

The driver: `k` rows, each accumulating `a * b[i]` into the running total, then
`m * p` with `m = t[0] * p'` chosen to zero the low limb, then shifting the total
down one limb. Both accumulations are `macLimbs`, which is why that primitive was
worth proving once.

Only the code is given here — the correctness proof is the next step. It is enough to
*measure*, which is what settles the representation question below. -/

/-- Fold a carry word in `sc` into the accumulator's top two limbs. -/
def foldCarry (acc sc k : ℕ) : Stmt 64 :=
  .bin .add (acc + k) (acc + k) sc ;;
  .bin .ult sc (acc + k) sc ;;
  .bin .add (acc + k + 1) (acc + k + 1) sc

/-- Shift the accumulator down by one limb. -/
def shiftDown (acc : ℕ) : ℕ → Stmt 64
  | 0 => .skip
  | n + 1 => shiftDown acc n ;; .mov (acc + n) (acc + n + 1)

/-- One CIOS row. -/
def ciosRow (k acc a b p pinv sc m i : ℕ) : Stmt 64 :=
  macLimbs k acc a (b + i) sc ;;
  foldCarry acc sc k ;;
  .bin .mul m acc pinv ;;
  macLimbs k acc p m sc ;;
  foldCarry acc sc k ;;
  shiftDown acc (k + 1)

def ciosRows (k acc a b p pinv sc m : ℕ) : ℕ → Stmt 64
  | 0 => .skip
  | n + 1 => ciosRows k acc a b p pinv sc m n ;; ciosRow k acc a b p pinv sc m n

/-- Montgomery multiplication, CIOS. Accumulator zeroing is the caller's job. -/
def montMulCIOS (k acc a b p pinv sc m : ℕ) : Stmt 64 :=
  ciosRows k acc a b p pinv sc m k

/-! ### Shift-free CIOS

The `shiftDown` in `ciosRow` costs `k + 1` instructions a row, `k (k + 1)` overall,
purely to move the accumulator back to a fixed base. Since rows are unrolled at
generation time, the base can instead advance with the row: row `i` works at
`acc + i`, and the shift disappears. The accumulator then spans `2k + 2` register
names rather than `k + 2`, but the limbs below the current base are dead, so the
inferred live peak absorbs it. -/

/-- One CIOS row, working at the row's own accumulator base. -/
def ciosRowAt (k acc a b p pinv sc m i : ℕ) : Stmt 64 :=
  macLimbs k (acc + i) a (b + i) sc ;;
  foldCarry (acc + i) sc k ;;
  .bin .mul m (acc + i) pinv ;;
  macLimbs k (acc + i) p m sc ;;
  foldCarry (acc + i) sc k

def ciosRowsAt (k acc a b p pinv sc m : ℕ) : ℕ → Stmt 64
  | 0 => .skip
  | n + 1 => ciosRowsAt k acc a b p pinv sc m n ;; ciosRowAt k acc a b p pinv sc m n

/-- Shift-free CIOS Montgomery multiplication. -/
def montMul (k acc a b p pinv sc m : ℕ) : Stmt 64 :=
  ciosRowsAt k acc a b p pinv sc m k

/-! ### Row zero writes rather than accumulates

The first CIOS row accumulates `a * b[0]` into an accumulator that is still zero, so
both its accumulator reads and the pass that zeroed it are wasted work. A *set*
variant drops the `acc[j] +` term: five instructions a limb instead of eight, and the
`k + 2` zeroing immediates disappear with it. -/

/-- Multiply-set limb step: `acc[j] ← x[j] * y + carry`, no accumulator read. -/
def macSetStep (acc x y sc j : ℕ) : Stmt 64 :=
  .bin .mul (sc + 1) (x + j) y ;;
  .bin .mulhi (sc + 2) (x + j) y ;;
  .bin .add (acc + j) (sc + 1) sc ;;
  .bin .ult (sc + 3) (acc + j) (sc + 1) ;;
  .bin .add sc (sc + 2) (sc + 3)

def macSetLoop (acc x y sc : ℕ) : ℕ → Stmt 64
  | 0 => .skip
  | n + 1 => macSetLoop acc x y sc n ;; macSetStep acc x y sc n

/-- `acc ← x * y` over `k` limbs, carry-out in `sc`. -/
def macSetLimbs (k acc x y sc : ℕ) : Stmt 64 := .imm sc 0 ;; macSetLoop acc x y sc k

/-- CIOS row zero: multiply-set instead of multiply-accumulate, and the accumulator's
top limb is written rather than folded into. -/
def ciosRow0 (k acc a b p pinv sc m : ℕ) : Stmt 64 :=
  macSetLimbs k acc a b sc ;;
  .mov (acc + k) sc ;;
  .imm (acc + k + 1) 0 ;;
  .bin .mul m acc pinv ;;
  macLimbs k acc p m sc ;;
  foldCarry acc sc k

/-- Rows `1 .. n` of a shift-free CIOS. -/
def ciosRowsFrom (k acc a b p pinv sc m : ℕ) : ℕ → Stmt 64
  | 0 => .skip
  | n + 1 => ciosRowsFrom k acc a b p pinv sc m n ;;
      ciosRowAt k acc a b p pinv sc m (n + 1)

/-- Shift-free CIOS with a specialised first row. -/
def montMulOpt (k acc a b p pinv sc m : ℕ) : Stmt 64 :=
  match k with
  | 0 => .skip
  | k' + 1 => ciosRow0 (k' + 1) acc a b p pinv sc m ;;
      ciosRowsFrom (k' + 1) acc a b p pinv sc m k'

/-! ## Cost, as closed forms

Every gadget's running time as a function of the limb count, proved for all `k` and
generic in the cost model — not evaluated at a few instantiations. These are worth
more than pins: compiled witgen code is straight-line, so `Exec.straight_time_eq`
makes `staticTime` the *exact* running time of every execution, and a closed form in
`k` therefore bounds the gadget at every field, including ones nobody has run. -/

/-- Per-limb cost of an addition step: three adds and two unsigned compares. -/
def addStepCost (C : CostModel) : ℕ := 3 * C.bin .add + 2 * C.bin .ult

/-- Per-limb cost of a multiply-accumulate step. -/
def macStepCost (C : CostModel) : ℕ :=
  C.bin .mul + C.bin .mulhi + 4 * C.bin .add + 2 * C.bin .ult

/-- Per-limb cost of a multiply-set step: no accumulator read, so two fewer adds and
one fewer compare. -/
def macSetStepCost (C : CostModel) : ℕ :=
  C.bin .mul + C.bin .mulhi + 2 * C.bin .add + C.bin .ult

/-- Per-limb cost of a select step. -/
def selStepCost (C : CostModel) : ℕ := C.bin .sub + C.bin .mul + C.bin .add

/-- Cost of folding a carry into the accumulator's top limbs. -/
def foldCarryCost (C : CostModel) : ℕ := 2 * C.bin .add + C.bin .ult

theorem addLoop_staticTime (C : CostModel) (d a b sc : ℕ) :
    ∀ n, (addLoop d a b sc n).staticTime C = n * addStepCost C
  | 0 => by simp [addLoop, Stmt.staticTime]
  | n + 1 => by
    show (addLoop d a b sc n).staticTime C + (addStep d a b sc n).staticTime C = _
    rw [addLoop_staticTime C d a b sc n]
    simp [addStep, Stmt.staticTime, addStepCost]
    ring

theorem addLimbsC_staticTime (C : CostModel) (k d a b sc c0 : ℕ) :
    (addLimbsC k d a b sc c0).staticTime C = C.imm + k * addStepCost C := by
  show C.imm + (addLoop d a b sc k).staticTime C = _
  rw [addLoop_staticTime]

theorem notLoop_staticTime (C : CostModel) (nb b : ℕ) :
    ∀ n, (notLoop nb b n).staticTime C = n * C.un .not
  | 0 => by simp [notLoop, Stmt.staticTime]
  | n + 1 => by
    show (notLoop nb b n).staticTime C + _ = _
    rw [notLoop_staticTime C nb b n]; simp [Stmt.staticTime]; ring

theorem subLimbs_staticTime (C : CostModel) (k d a b nb sc : ℕ) :
    (subLimbs k d a b nb sc).staticTime C
      = k * C.un .not + (C.imm + k * addStepCost C) := by
  show (notLoop nb b k).staticTime C + (addLimbsC k d a nb sc 1).staticTime C = _
  rw [notLoop_staticTime, addLimbsC_staticTime]

theorem macLoop_staticTime (C : CostModel) (acc x y sc : ℕ) :
    ∀ n, (macLoop acc x y sc n).staticTime C = n * macStepCost C
  | 0 => by simp [macLoop, Stmt.staticTime]
  | n + 1 => by
    show (macLoop acc x y sc n).staticTime C + (macStep acc x y sc n).staticTime C = _
    rw [macLoop_staticTime C acc x y sc n]
    simp [macStep, Stmt.staticTime, macStepCost]
    ring

theorem macLimbs_staticTime (C : CostModel) (k acc x y sc : ℕ) :
    (macLimbs k acc x y sc).staticTime C = C.imm + k * macStepCost C := by
  show C.imm + (macLoop acc x y sc k).staticTime C = _
  rw [macLoop_staticTime]

theorem macSetLoop_staticTime (C : CostModel) (acc x y sc : ℕ) :
    ∀ n, (macSetLoop acc x y sc n).staticTime C = n * macSetStepCost C
  | 0 => by simp [macSetLoop, Stmt.staticTime]
  | n + 1 => by
    show (macSetLoop acc x y sc n).staticTime C
      + (macSetStep acc x y sc n).staticTime C = _
    rw [macSetLoop_staticTime C acc x y sc n]
    simp [macSetStep, Stmt.staticTime, macSetStepCost]
    ring

theorem macSetLimbs_staticTime (C : CostModel) (k acc x y sc : ℕ) :
    (macSetLimbs k acc x y sc).staticTime C = C.imm + k * macSetStepCost C := by
  show C.imm + (macSetLoop acc x y sc k).staticTime C = _
  rw [macSetLoop_staticTime]

theorem selectLoop_staticTime (C : CostModel) (d a b f sc : ℕ) :
    ∀ n, (selectLoop d a b f sc n).staticTime C = n * selStepCost C
  | 0 => by simp [selectLoop, Stmt.staticTime]
  | n + 1 => by
    show (selectLoop d a b f sc n).staticTime C
      + (selectStep d a b f sc n).staticTime C = _
    rw [selectLoop_staticTime C d a b f sc n]
    simp [selectStep, Stmt.staticTime, selStepCost]
    ring

theorem selectLimbs_staticTime (C : CostModel) (k d a b f sc : ℕ) :
    (selectLimbs k d a b f sc).staticTime C = k * selStepCost C :=
  selectLoop_staticTime C d a b f sc k

/-! ### Cost of the Montgomery multiply

The quadratic ones. `ciosRowCost` is linear in `k`, and there are `k` rows. -/

/-- Cost of one shift-free CIOS row: two multiply-accumulates, two carry folds and
the multiplication choosing the reduction multiplier. -/
def ciosRowCost (C : CostModel) (k : ℕ) : ℕ :=
  2 * (C.imm + k * macStepCost C) + 2 * foldCarryCost C + C.bin .mul

/-- Cost of the specialised first row: a multiply-*set* in place of the first
multiply-accumulate, and a written top limb in place of a carry fold. -/
def ciosRow0Cost (C : CostModel) (k : ℕ) : ℕ :=
  (C.imm + k * macSetStepCost C) + C.mov + C.imm + C.bin .mul
    + (C.imm + k * macStepCost C) + foldCarryCost C

theorem foldCarry_staticTime (C : CostModel) (acc sc k : ℕ) :
    (foldCarry acc sc k).staticTime C = foldCarryCost C := by
  simp [foldCarry, Stmt.staticTime, foldCarryCost]; ring

theorem ciosRowAt_staticTime (C : CostModel) (k acc a b p pinv sc m i : ℕ) :
    (ciosRowAt k acc a b p pinv sc m i).staticTime C = ciosRowCost C k := by
  show (macLimbs k (acc + i) a (b + i) sc).staticTime C
      + ((foldCarry (acc + i) sc k).staticTime C
        + ((Stmt.bin .mul m (acc + i) pinv).staticTime C
          + ((macLimbs k (acc + i) p m sc).staticTime C
            + (foldCarry (acc + i) sc k).staticTime C))) = _
  rw [macLimbs_staticTime, macLimbs_staticTime, foldCarry_staticTime]
  simp [Stmt.staticTime, ciosRowCost]
  ring

theorem ciosRowsFrom_staticTime (C : CostModel) (k acc a b p pinv sc m : ℕ) :
    ∀ n, (ciosRowsFrom k acc a b p pinv sc m n).staticTime C = n * ciosRowCost C k
  | 0 => by simp [ciosRowsFrom, Stmt.staticTime]
  | n + 1 => by
    show (ciosRowsFrom k acc a b p pinv sc m n).staticTime C
      + (ciosRowAt k acc a b p pinv sc m (n + 1)).staticTime C = _
    rw [ciosRowsFrom_staticTime C k acc a b p pinv sc m n, ciosRowAt_staticTime]
    ring

theorem ciosRow0_staticTime (C : CostModel) (k acc a b p pinv sc m : ℕ) :
    (ciosRow0 k acc a b p pinv sc m).staticTime C = ciosRow0Cost C k := by
  show (macSetLimbs k acc a b sc).staticTime C
      + ((Stmt.mov (acc + k) sc).staticTime C
        + ((Stmt.imm (acc + k + 1) 0).staticTime C
          + ((Stmt.bin .mul m acc pinv).staticTime C
            + ((macLimbs k acc p m sc).staticTime C
              + (foldCarry acc sc k).staticTime C)))) = _
  rw [macSetLimbs_staticTime, macLimbs_staticTime, foldCarry_staticTime]
  simp [Stmt.staticTime, ciosRow0Cost]
  ring

/-- **The cost of a Montgomery multiplication, for every limb count.** One
specialised first row plus `k'` ordinary rows. -/
theorem montMulOpt_staticTime (C : CostModel) (k' acc a b p pinv sc m : ℕ) :
    (montMulOpt (k' + 1) acc a b p pinv sc m).staticTime C
      = ciosRow0Cost C (k' + 1) + k' * ciosRowCost C (k' + 1) := by
  show (ciosRow0 (k' + 1) acc a b p pinv sc m).staticTime C
    + (ciosRowsFrom (k' + 1) acc a b p pinv sc m k').staticTime C = _
  rw [ciosRow0_staticTime, ciosRowsFrom_staticTime]

/-- The same under the uniform model, as an explicit polynomial: a Montgomery
multiplication over a `k`-limb modulus costs exactly `16k² + 6k - 1` steps, written
subtraction-free at `k = k' + 1`. -/
theorem montMulOpt_staticTime_unit (k' acc a b p pinv sc m : ℕ) :
    (montMulOpt (k' + 1) acc a b p pinv sc m).staticTime CostModel.unit
      = 16 * k' ^ 2 + 38 * k' + 21 := by
  rw [montMulOpt_staticTime]
  simp [ciosRow0Cost, ciosRowCost, macStepCost, macSetStepCost, foldCarryCost,
    CostModel.unit]
  ring

/-! ### Loops and upper bounds

Everything above is straight-line, so its cost is an *equality*: `staticTime` is the
running time of every execution. GCD-based inversion will not be, by decision: it is
emitted as a `whileNZ` with a measure rather than unrolled to a worst-case divstep
count, so its code stays small and it exits early, at the price of a `≤` instead of an
`=`.

`Caliper.Triple.whileNZ_measure` is the rule — an invariant indexed by a remaining-
iterations budget, a guard triple, and a body triple that decrements the budget,
yielding `(k + 1) * (Tg + C.branch) + k * Tb`. For a binary extended GCD over an
`n`-bit modulus the budget is `2n`, a generation-time constant, so the bound is still
a number the compiler computes without running anything.

What this costs the pipeline, and what has to change with it: a program containing a
loop is not `Stmt.Straight`, so `compile_time_eq` and `staticTime?` no longer apply to
it, and `TimedCircuit.underBudget` — which is built on `staticTime?` — cannot quote a
number. The replacement is to carry the bound with the code: the compiler returns a
proved `TimeTriple` rather than leaning on `staticTime`, and `compile_time_eq` becomes
`compile_time_le`. Data-independence of the time counter is genuinely lost for
inverting programs; that was never a side-channel guarantee here, and
`witgen < 2 ^ 40` is an upper-bound claim to begin with. -/

/-! ## Straight-line, and hence real runtime bounds

The cost formulas above are functions of the syntax. They become statements about
*executions* through `Exec.straight_time_eq`, which needs the code straight-line —
true of every gadget here, since none emits `ifNZ`, `whileNZ` or a dynamic
`memAlloc`. `AllocFree` comes along in the same induction and gives the memory side.

This is what makes the bounds hold *for every field*: `k` is a parameter, so
`montMulOpt_time` prices a Montgomery multiplication over a modulus of any size. -/

/-- Straight-line and allocation-free, the pair every gadget here satisfies. -/
def SAF (c : Stmt 64) : Prop := c.Straight ∧ c.AllocFree

theorem SAF.seq {c₁ c₂ : Stmt 64} (h₁ : SAF c₁) (h₂ : SAF c₂) : SAF (c₁ ;; c₂) :=
  ⟨⟨h₁.1, h₂.1⟩, ⟨h₁.2, h₂.2⟩⟩

theorem saf_leaf_bin (op : BinOp) (d a b : Reg) : SAF (.bin op d a b) := ⟨trivial, trivial⟩
theorem saf_leaf_un (op : UnOp) (d a : Reg) : SAF (.un op d a) := ⟨trivial, trivial⟩
theorem saf_leaf_imm (d : Reg) (v : Word 64) : SAF (.imm d v) := ⟨trivial, trivial⟩
theorem saf_leaf_mov (d a : Reg) : SAF (.mov d a) := ⟨trivial, trivial⟩
theorem saf_skip : SAF (.skip : Stmt 64) := ⟨trivial, trivial⟩

theorem addStep_saf (d a b sc i : ℕ) : SAF (addStep d a b sc i) := by
  simp [addStep, SAF, Stmt.Straight, Stmt.AllocFree]

theorem addLoop_saf (d a b sc : ℕ) : ∀ n, SAF (addLoop d a b sc n)
  | 0 => saf_skip
  | n + 1 => (addLoop_saf d a b sc n).seq (addStep_saf d a b sc n)

theorem addLimbsC_saf (k d a b sc c0 : ℕ) : SAF (addLimbsC k d a b sc c0) :=
  (saf_leaf_imm _ _).seq (addLoop_saf d a b sc k)

theorem notLoop_saf (nb b : ℕ) : ∀ n, SAF (notLoop nb b n)
  | 0 => saf_skip
  | n + 1 => (notLoop_saf nb b n).seq (saf_leaf_un _ _ _)

theorem subLimbs_saf (k d a b nb sc : ℕ) : SAF (subLimbs k d a b nb sc) :=
  (notLoop_saf nb b k).seq (addLimbsC_saf k d a nb sc 1)

theorem macStep_saf (acc x y sc j : ℕ) : SAF (macStep acc x y sc j) := by
  simp [macStep, SAF, Stmt.Straight, Stmt.AllocFree]

theorem macLoop_saf (acc x y sc : ℕ) : ∀ n, SAF (macLoop acc x y sc n)
  | 0 => saf_skip
  | n + 1 => (macLoop_saf acc x y sc n).seq (macStep_saf acc x y sc n)

theorem macLimbs_saf (k acc x y sc : ℕ) : SAF (macLimbs k acc x y sc) :=
  (saf_leaf_imm _ _).seq (macLoop_saf acc x y sc k)

theorem macSetStep_saf (acc x y sc j : ℕ) : SAF (macSetStep acc x y sc j) := by
  simp [macSetStep, SAF, Stmt.Straight, Stmt.AllocFree]

theorem macSetLoop_saf (acc x y sc : ℕ) : ∀ n, SAF (macSetLoop acc x y sc n)
  | 0 => saf_skip
  | n + 1 => (macSetLoop_saf acc x y sc n).seq (macSetStep_saf acc x y sc n)

theorem macSetLimbs_saf (k acc x y sc : ℕ) : SAF (macSetLimbs k acc x y sc) :=
  (saf_leaf_imm _ _).seq (macSetLoop_saf acc x y sc k)

theorem selectStep_saf (d a b f sc i : ℕ) : SAF (selectStep d a b f sc i) := by
  simp [selectStep, SAF, Stmt.Straight, Stmt.AllocFree]

theorem selectLoop_saf (d a b f sc : ℕ) : ∀ n, SAF (selectLoop d a b f sc n)
  | 0 => saf_skip
  | n + 1 => (selectLoop_saf d a b f sc n).seq (selectStep_saf d a b f sc n)

theorem selectLimbs_saf (k d a b f sc : ℕ) : SAF (selectLimbs k d a b f sc) :=
  selectLoop_saf d a b f sc k

theorem foldCarry_saf (acc sc k : ℕ) : SAF (foldCarry acc sc k) := by
  simp [foldCarry, SAF, Stmt.Straight, Stmt.AllocFree]

theorem ciosRowAt_saf (k acc a b p pinv sc m i : ℕ) :
    SAF (ciosRowAt k acc a b p pinv sc m i) :=
  (macLimbs_saf _ _ _ _ _).seq ((foldCarry_saf _ _ _).seq ((saf_leaf_bin _ _ _ _).seq
    ((macLimbs_saf _ _ _ _ _).seq (foldCarry_saf _ _ _))))

theorem ciosRowsFrom_saf (k acc a b p pinv sc m : ℕ) :
    ∀ n, SAF (ciosRowsFrom k acc a b p pinv sc m n)
  | 0 => saf_skip
  | n + 1 => (ciosRowsFrom_saf k acc a b p pinv sc m n).seq
      (ciosRowAt_saf _ _ _ _ _ _ _ _ _)

theorem ciosRow0_saf (k acc a b p pinv sc m : ℕ) :
    SAF (ciosRow0 k acc a b p pinv sc m) :=
  (macSetLimbs_saf _ _ _ _ _).seq ((saf_leaf_mov _ _).seq ((saf_leaf_imm _ _).seq
    ((saf_leaf_bin _ _ _ _).seq ((macLimbs_saf _ _ _ _ _).seq (foldCarry_saf _ _ _)))))

theorem montMulOpt_saf (k acc a b p pinv sc m : ℕ) :
    SAF (montMulOpt k acc a b p pinv sc m) := by
  cases k with
  | zero => exact saf_skip
  | succ k' =>
    exact (ciosRow0_saf _ _ _ _ _ _ _ _).seq (ciosRowsFrom_saf _ _ _ _ _ _ _ _ _)

/-- **Worst-case running time of a Montgomery multiplication, at every field.** Over a
`k`-limb modulus — `k = ⌈bits p / 64⌉`, so any prime whatsoever — every execution
takes exactly `16k² + 6k - 1` unit steps, written subtraction-free at `k = k' + 1`.
Exact rather than merely bounded, because the code is straight-line. -/
theorem montMulOpt_time {k' acc a b p pinv sc m : ℕ} {s s' : State 64} {t : ℕ}
    {d pp : ℤ}
    (h : Exec CostModel.unit (montMulOpt (k' + 1) acc a b p pinv sc m) s s' t d pp) :
    t = 16 * k' ^ 2 + 38 * k' + 21 :=
  (h.straight_time_eq (montMulOpt_saf _ _ _ _ _ _ _ _).1).trans
    (montMulOpt_staticTime_unit _ _ _ _ _ _ _ _)

/-! ## Modular arithmetic, and the cost of a field operation at any modulus

`limbCount p` is how many 64-bit words a modulus needs; every operation below is
parameterised by it, so the bounds hold at every field. Reduction is a conditional
subtract done branch-free: subtract the modulus, then select on the borrow bit, which
is exactly the flag `subLimbs` already produces.

For a *small* modulus the compiler should not use these: the existing single-word
`fieldOp` reduces with one `umod` and costs 3 instructions where `montAdd` costs
`14k + 3`, which at `k = 1` is 17. The dispatch is per-operation, since the
single-word path needs `2p ≤ 2^64` for addition but `p² ≤ 2^64` for multiplication —
Goldilocks can use it for one and not the other. -/

/-- Number of 64-bit limbs a modulus needs. -/
def limbCount (p : ℕ) : ℕ := (Nat.size p + 63) / 64

/-- The single-word `fieldOp` reduction is sound for addition when `2p ≤ 2 ^ 64`. -/
def addFitsWord (p : ℕ) : Prop := 2 * p ≤ 2 ^ 64

/-- …and for multiplication only when `p² ≤ 2 ^ 64`. -/
def mulFitsWord (p : ℕ) : Prop := p * p ≤ 2 ^ 64

/-- `d ← (a + b) mod p`. Add, subtract the modulus, and select on "the sum reached the
modulus", which is the addition's carry-out or the subtraction's no-borrow bit. -/
def montAdd (k d a b pReg t u nb sc flag : ℕ) : Stmt 64 :=
  addLimbs k t a b sc ;;
  subLimbs k u t pReg nb flag ;;
  .bin .or flag sc flag ;;
  selectLimbs k d u t flag sc

/-- `d ← (a - b) mod p`. Subtract, add the modulus back, and select on the borrow. -/
def montSub (k d a b pReg t u nb sc flag : ℕ) : Stmt 64 :=
  subLimbs k t a b nb flag ;;
  addLimbs k u t pReg sc ;;
  selectLimbs k d t u flag sc

/-- Montgomery multiplication followed by the conditional subtract that brings the
result below the modulus. -/
def montMulRed (k d acc a b pReg pinv m t nb sc : ℕ) : Stmt 64 :=
  montMulOpt k acc a b pReg pinv sc m ;;
  subLimbs k t (acc + k) pReg nb sc ;;
  selectLimbs k d t (acc + k) sc nb

/-! ### Cost -/

def montAddCost (C : CostModel) (k : ℕ) : ℕ :=
  (C.imm + k * addStepCost C) + (k * C.un .not + (C.imm + k * addStepCost C))
    + C.bin .or + k * selStepCost C

def montSubCost (C : CostModel) (k : ℕ) : ℕ :=
  (k * C.un .not + (C.imm + k * addStepCost C)) + (C.imm + k * addStepCost C)
    + k * selStepCost C

theorem montAdd_staticTime (C : CostModel) (k d a b pReg t u nb sc flag : ℕ) :
    (montAdd k d a b pReg t u nb sc flag).staticTime C = montAddCost C k := by
  show (addLimbs k t a b sc).staticTime C
    + ((subLimbs k u t pReg nb flag).staticTime C
      + ((Stmt.bin .or flag sc flag).staticTime C
        + (selectLimbs k d u t flag sc).staticTime C)) = _
  rw [show addLimbs k t a b sc = addLimbsC k t a b sc 0 from rfl, addLimbsC_staticTime,
    subLimbs_staticTime, selectLimbs_staticTime]
  simp [Stmt.staticTime, montAddCost]
  ring

theorem montSub_staticTime (C : CostModel) (k d a b pReg t u nb sc flag : ℕ) :
    (montSub k d a b pReg t u nb sc flag).staticTime C = montSubCost C k := by
  show (subLimbs k t a b nb flag).staticTime C
    + ((addLimbs k u t pReg sc).staticTime C
      + (selectLimbs k d t u flag sc).staticTime C) = _
  rw [subLimbs_staticTime, show addLimbs k u t pReg sc = addLimbsC k u t pReg sc 0 from rfl,
    addLimbsC_staticTime, selectLimbs_staticTime]
  simp [montSubCost]
  ring

/-- A modular addition over a `k`-limb modulus costs exactly `14k + 3` unit steps. -/
theorem montAdd_staticTime_unit (k d a b pReg t u nb sc flag : ℕ) :
    (montAdd k d a b pReg t u nb sc flag).staticTime CostModel.unit = 14 * k + 3 := by
  rw [montAdd_staticTime]
  simp [montAddCost, addStepCost, selStepCost, CostModel.unit]
  ring

/-- A modular subtraction costs exactly `14k + 2`. -/
theorem montSub_staticTime_unit (k d a b pReg t u nb sc flag : ℕ) :
    (montSub k d a b pReg t u nb sc flag).staticTime CostModel.unit = 14 * k + 2 := by
  rw [montSub_staticTime]
  simp [montSubCost, addStepCost, selStepCost, CostModel.unit]
  ring

/-- A reduced Montgomery multiplication costs exactly `16k² + 15k` unit steps,
subtraction-free at `k = k' + 1`. -/
theorem montMulRed_staticTime_unit (k' d acc a b pReg pinv m t nb sc : ℕ) :
    (montMulRed (k' + 1) d acc a b pReg pinv m t nb sc).staticTime CostModel.unit
      = 16 * k' ^ 2 + 47 * k' + 31 := by
  show (montMulOpt (k' + 1) acc a b pReg pinv sc m).staticTime CostModel.unit
    + ((subLimbs (k' + 1) t (acc + (k' + 1)) pReg nb sc).staticTime CostModel.unit
      + (selectLimbs (k' + 1) d t (acc + (k' + 1)) sc nb).staticTime CostModel.unit) = _
  rw [montMulOpt_staticTime_unit, subLimbs_staticTime, selectLimbs_staticTime]
  simp [addStepCost, selStepCost, CostModel.unit]
  ring

/-! ### Straightness -/

theorem montAdd_saf (k d a b pReg t u nb sc flag : ℕ) :
    SAF (montAdd k d a b pReg t u nb sc flag) :=
  (addLimbsC_saf _ _ _ _ _ _).seq ((subLimbs_saf _ _ _ _ _ _).seq
    ((saf_leaf_bin _ _ _ _).seq (selectLimbs_saf _ _ _ _ _ _)))

theorem montSub_saf (k d a b pReg t u nb sc flag : ℕ) :
    SAF (montSub k d a b pReg t u nb sc flag) :=
  (subLimbs_saf _ _ _ _ _ _).seq ((addLimbsC_saf _ _ _ _ _ _).seq
    (selectLimbs_saf _ _ _ _ _ _))

theorem montMulRed_saf (k d acc a b pReg pinv m t nb sc : ℕ) :
    SAF (montMulRed k d acc a b pReg pinv m t nb sc) :=
  (montMulOpt_saf _ _ _ _ _ _ _ _).seq ((subLimbs_saf _ _ _ _ _ _).seq
    (selectLimbs_saf _ _ _ _ _ _))

/-! ### Worst-case runtime, at every field

The three theorems the goal asks for: a field operation over a modulus of *any* size
runs in exactly the stated number of steps, on every input. -/

theorem montAdd_time {k d a b pReg t u nb sc flag : ℕ} {s s' : State 64} {tm : ℕ}
    {dd pp : ℤ}
    (h : Exec CostModel.unit (montAdd k d a b pReg t u nb sc flag) s s' tm dd pp) :
    tm = 14 * k + 3 :=
  (h.straight_time_eq (montAdd_saf _ _ _ _ _ _ _ _ _ _).1).trans
    (montAdd_staticTime_unit _ _ _ _ _ _ _ _ _ _)

theorem montSub_time {k d a b pReg t u nb sc flag : ℕ} {s s' : State 64} {tm : ℕ}
    {dd pp : ℤ}
    (h : Exec CostModel.unit (montSub k d a b pReg t u nb sc flag) s s' tm dd pp) :
    tm = 14 * k + 2 :=
  (h.straight_time_eq (montSub_saf _ _ _ _ _ _ _ _ _ _).1).trans
    (montSub_staticTime_unit _ _ _ _ _ _ _ _ _ _)

theorem montMulRed_time {k' d acc a b pReg pinv m t nb sc : ℕ} {s s' : State 64}
    {tm : ℕ} {dd pp : ℤ}
    (h : Exec CostModel.unit (montMulRed (k' + 1) d acc a b pReg pinv m t nb sc)
      s s' tm dd pp) :
    tm = 16 * k' ^ 2 + 47 * k' + 31 :=
  (h.straight_time_eq (montMulRed_saf _ _ _ _ _ _ _ _ _ _ _).1).trans
    (montMulRed_staticTime_unit _ _ _ _ _ _ _ _ _ _ _)

/-! ## Loading and materialising limbs

Two leaf emitters the IR lowering needs: `k` immediates for a constant, and `k`
environment loads for a variable. The environment buffer is taken to hold field
elements *already in Montgomery form*, `k` words apiece — the encoding is ours to
pick, and picking it this way removes a Montgomery conversion (`16k² + 15k` steps)
from every single variable read. -/

/-- `k` immediates writing the limbs of `v` into `base ..`. -/
def immLimbs (base v : ℕ) : ℕ → Stmt 64
  | 0 => .skip
  | n + 1 => immLimbs base v n ;; .imm (base + n) (BitVec.ofNat 64 (limb 64 v n))

/-- `k` loads of buffer `0` at `idx * k ..`, into `base ..`. Two instructions a limb:
the index immediate and the load. -/
def loadLimbs (base idx sc : ℕ) : ℕ → Stmt 64
  | 0 => .skip
  | n + 1 => loadLimbs base idx sc n ;;
      (.imm sc (BitVec.ofNat 64 (idx + n)) ;; .memLoad (base + n) 0 sc)

theorem immLimbs_staticTime (C : CostModel) (base v : ℕ) :
    ∀ n, (immLimbs base v n).staticTime C = n * C.imm
  | 0 => by simp [immLimbs, Stmt.staticTime]
  | n + 1 => by
    show (immLimbs base v n).staticTime C + _ = _
    rw [immLimbs_staticTime C base v n]; simp [Stmt.staticTime]; ring

theorem loadLimbs_staticTime (C : CostModel) (base idx sc : ℕ) :
    ∀ n, (loadLimbs base idx sc n).staticTime C = n * (C.imm + C.memLoad)
  | 0 => by simp [loadLimbs, Stmt.staticTime]
  | n + 1 => by
    show (loadLimbs base idx sc n).staticTime C + _ = _
    rw [loadLimbs_staticTime C base idx sc n]; simp [Stmt.staticTime]; ring

theorem immLimbs_saf (base v : ℕ) : ∀ n, SAF (immLimbs base v n)
  | 0 => saf_skip
  | n + 1 => (immLimbs_saf base v n).seq (saf_leaf_imm _ _)

theorem loadLimbs_saf (base idx sc : ℕ) : ∀ n, SAF (loadLimbs base idx sc n)
  | 0 => saf_skip
  | n + 1 => (loadLimbs_saf base idx sc n).seq
      ((saf_leaf_imm _ _).seq ⟨trivial, trivial⟩)

/-! ## Schoolbook multiply (SOS)

`acc ← a * b` over `2k` limbs. Row `i` accumulates `a * b[i]` at limb offset `i`, its
carry landing in the top limb that row is the first to touch — so no zeroing pass is
needed if row 0 *writes* rather than accumulates.

This is the first phase of a Separated Operand Scanning Montgomery multiply. Two
reasons to prefer it to the CIOS driver above: its spec is `= a * b`, with no modular
arithmetic to reason about, and it is *cheaper* here — CIOS folds a carry twice a row,
which SOS does not. It costs `k` more accumulator words. -/

/-- Row `i`: accumulate `a * b[i]` at offset `i`, carry into the fresh top limb. -/
def mulRow (k acc a b sc i : ℕ) : Stmt 64 :=
  macLimbs k (acc + i) a (b + i) sc ;; .mov (acc + i + k) sc

/-- Row `0` writes instead of accumulating, so the accumulator needs no zeroing. -/
def mulRow0 (k acc a b sc : ℕ) : Stmt 64 :=
  macSetLimbs k acc a b sc ;; .mov (acc + k) sc

def mulRowsFrom (k acc a b sc : ℕ) : ℕ → Stmt 64
  | 0 => .skip
  | n + 1 => mulRowsFrom k acc a b sc n ;; mulRow k acc a b sc (n + 1)

/-- `acc ← a * b`, a `2k`-limb product in `acc .. acc + 2k - 1`. -/
def mulLimbs (k acc a b sc : ℕ) : Stmt 64 :=
  match k with
  | 0 => .skip
  | k' + 1 => mulRow0 (k' + 1) acc a b sc ;; mulRowsFrom (k' + 1) acc a b sc k'

theorem mulRow_staticTime (C : CostModel) (k acc a b sc i : ℕ) :
    (mulRow k acc a b sc i).staticTime C = (C.imm + k * macStepCost C) + C.mov := by
  show (macLimbs k (acc + i) a (b + i) sc).staticTime C + _ = _
  rw [macLimbs_staticTime]; simp [Stmt.staticTime]

theorem mulRow0_staticTime (C : CostModel) (k acc a b sc : ℕ) :
    (mulRow0 k acc a b sc).staticTime C = (C.imm + k * macSetStepCost C) + C.mov := by
  show (macSetLimbs k acc a b sc).staticTime C + _ = _
  rw [macSetLimbs_staticTime]; simp [Stmt.staticTime]

theorem mulRowsFrom_staticTime (C : CostModel) (k acc a b sc : ℕ) :
    ∀ n, (mulRowsFrom k acc a b sc n).staticTime C
      = n * ((C.imm + k * macStepCost C) + C.mov)
  | 0 => by simp [mulRowsFrom, Stmt.staticTime]
  | n + 1 => by
    show (mulRowsFrom k acc a b sc n).staticTime C
      + (mulRow k acc a b sc (n + 1)).staticTime C = _
    rw [mulRowsFrom_staticTime C k acc a b sc n, mulRow_staticTime]
    ring

/-- A `k`-limb schoolbook multiply costs exactly `8k² - k` unit steps,
subtraction-free at `k = k' + 1`. Cheaper than the CIOS driver's `16k² + 6k - 1`
half — the reduction phase makes up the rest. -/
theorem mulLimbs_staticTime_unit (k' acc a b sc : ℕ) :
    (mulLimbs (k' + 1) acc a b sc).staticTime CostModel.unit
      = 8 * k' ^ 2 + 15 * k' + 7 := by
  show (mulRow0 (k' + 1) acc a b sc).staticTime CostModel.unit
    + (mulRowsFrom (k' + 1) acc a b sc k').staticTime CostModel.unit = _
  rw [mulRow0_staticTime, mulRowsFrom_staticTime]
  simp [macStepCost, macSetStepCost, CostModel.unit]
  ring

theorem mulRow_saf (k acc a b sc i : ℕ) : SAF (mulRow k acc a b sc i) :=
  (macLimbs_saf _ _ _ _ _).seq (saf_leaf_mov _ _)

theorem mulRow0_saf (k acc a b sc : ℕ) : SAF (mulRow0 k acc a b sc) :=
  (macSetLimbs_saf _ _ _ _ _).seq (saf_leaf_mov _ _)

theorem mulRowsFrom_saf (k acc a b sc : ℕ) : ∀ n, SAF (mulRowsFrom k acc a b sc n)
  | 0 => saf_skip
  | n + 1 => (mulRowsFrom_saf k acc a b sc n).seq (mulRow_saf _ _ _ _ _ _)

theorem mulLimbs_saf (k acc a b sc : ℕ) : SAF (mulLimbs k acc a b sc) := by
  cases k with
  | zero => exact saf_skip
  | succ k' => exact (mulRow0_saf _ _ _ _ _).seq (mulRowsFrom_saf _ _ _ _ _ _)

/-- Worst-case runtime of a schoolbook multiply, at every field. -/
theorem mulLimbs_time {k' acc a b sc : ℕ} {s s' : State 64} {t : ℕ} {d pp : ℤ}
    (h : Exec CostModel.unit (mulLimbs (k' + 1) acc a b sc) s s' t d pp) :
    t = 8 * k' ^ 2 + 15 * k' + 7 :=
  (h.straight_time_eq (mulLimbs_saf _ _ _ _ _).1).trans
    (mulLimbs_staticTime_unit _ _ _ _ _)

/-! ### Toward correctness of the schoolbook multiply

`limb_window` relates the limbs of a value seen from an offset to the limbs of the
shifted value — the lemma the row induction needs to connect a row's `k + 1`-limb
window to the whole `2k`-limb accumulator. -/

/-- The limbs of `V` from `i` up are the limbs of `V / 2 ^ (64 i)`. -/
theorem limb_window (V i j : ℕ) : limb 64 V (i + j) = limb 64 (V / 2 ^ (64 * i)) j := by
  have hpow : (2:ℕ) ^ (64 * (i + j)) = 2 ^ (64 * i) * 2 ^ (64 * j) := by
    rw [← pow_add]; ring_nf
  simp only [limb, hpow, ← Nat.div_div_eq_div_mul]

/-- The carry identity for a multiply-*set* step: the accumulate step at accumulator
limb `0`, where the first wrap bit is identically zero — which is exactly why the set
variant may drop it and cost three instructions less. -/
theorem macSet_carry {P c : ℕ} (hc : c < 2 ^ 64) :
    (P % 2 ^ 64 + c) % 2 ^ 64 = (P + c) % 2 ^ 64 ∧
      P / 2 ^ 64 + (if (P % 2 ^ 64 + c) % 2 ^ 64 < P % 2 ^ 64 then 1 else 0)
        = (P + c) / 2 ^ 64 := by
  split_ifs <;> omega

theorem macSetStep_exec {acc x y sc j : ℕ}
    (hx : x + j < sc) (hy : y < sc) (hacc : sc + 4 ≤ acc)
    {s : State 64} {xj yv c : ℕ} (hxj : xj < 2 ^ 64) (hyv : yv < 2 ^ 64)
    (hc : c < 2 ^ 64)
    (hsx : s.regs (x + j) = BitVec.ofNat 64 xj)
    (hsy : s.regs y = BitVec.ofNat 64 yv)
    (hsc : s.regs sc = BitVec.ofNat 64 c) :
    ∃ s' t dd pp, Exec C (macSetStep acc x y sc j) s s' t dd pp ∧
      s'.regs (acc + j) = BitVec.ofNat 64 ((xj * yv + c) % 2 ^ 64) ∧
      s'.regs sc = BitVec.ofNat 64 ((xj * yv + c) / 2 ^ 64) ∧
      (∀ q, q ≠ sc → q ≠ sc + 1 → q ≠ sc + 2 → q ≠ sc + 3 → q ≠ acc + j →
        s'.regs q = s.regs q) ∧
      s'.bufs = s.bufs ∧ s'.caps = s.caps := by
  obtain ⟨hword, hcarry⟩ := macSet_carry (P := xj * yv) hc
  refine ⟨_, _, _, _,
    .seq .bin (.seq .bin (.seq .bin (.seq .bin .bin))), ?_, ?_, ?_, rfl, rfl⟩
  · simp only [regs_setReg_self, BinOp.eval,
      regs_setReg_ne _ _ (show acc + j ≠ sc by omega),
      regs_setReg_ne _ _ (show acc + j ≠ sc + 3 by omega),
      regs_setReg_ne _ _ (show sc ≠ sc + 1 by omega),
      regs_setReg_ne _ _ (show sc ≠ sc + 2 by omega),
      regs_setReg_ne _ _ (show sc + 1 ≠ sc + 2 by omega),
      regs_setReg_ne _ _ (show x + j ≠ sc + 1 by omega),
      regs_setReg_ne _ _ (show y ≠ sc + 1 by omega),
      hsx, hsy, hsc]
    apply BitVec.eq_of_toNat_eq
    simp [Nat.add_mod, Nat.mul_mod]
  · simp only [regs_setReg_self, BinOp.eval,
      regs_setReg_ne _ _ (show sc ≠ sc + 1 by omega),
      regs_setReg_ne _ _ (show sc ≠ sc + 2 by omega),
      regs_setReg_ne _ _ (show sc + 1 ≠ sc + 2 by omega),
      regs_setReg_ne _ _ (show sc + 1 ≠ acc + j by omega),
      regs_setReg_ne _ _ (show sc + 2 ≠ sc + 3 by omega),
      regs_setReg_ne _ _ (show sc + 2 ≠ acc + j by omega),
      regs_setReg_ne _ _ (show x + j ≠ sc + 1 by omega),
      regs_setReg_ne _ _ (show y ≠ sc + 1 by omega),
      hsx, hsy, hsc]
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hxj, Nat.mod_eq_of_lt hyv, Nat.mod_eq_of_lt hc]
    rw [← hcarry]
    apply BitVec.eq_of_toNat_eq
    split_ifs <;> simp
  · intro q h0 h1 h2 h3 h4
    rw [regs_setReg_ne _ _ h0, regs_setReg_ne _ _ h3, regs_setReg_ne _ _ h4,
      regs_setReg_ne _ _ h2, regs_setReg_ne _ _ h1]

@[simp] theorem limb_zero (i : ℕ) : limb 64 0 i = 0 := by simp [limb]

/-- The multiply-set loop is the multiply-accumulate loop at accumulator `0`, so it
shares `macSum`'s algebra: after `n` steps the destination's low `n` limbs hold
`(X mod 2^(64n)) * y` and `sc` its carry. -/
theorem macSetLoop_exec {k acc x y sc : ℕ} (hl : MacLayout k acc x y sc)
    {s : State 64} {X yv : ℕ} (hyv : yv < 2 ^ 64)
    (hxr : RegsEnc s x k X)
    (hsy : s.regs y = BitVec.ofNat 64 yv)
    (hsc : s.regs sc = BitVec.ofNat 64 0) :
    ∀ n ≤ k, ∃ s' t dd pp, Exec C (macSetLoop acc x y sc n) s s' t dd pp ∧
      (∀ i < n, s'.regs (acc + i) = BitVec.ofNat 64 (limb 64 (macSum 0 X yv n) i)) ∧
      s'.regs sc = BitVec.ofNat 64 (macSum 0 X yv n / 2 ^ (64 * n)) ∧
      (∀ q, q < sc → s'.regs q = s.regs q) ∧
      (∀ i, n ≤ i → s'.regs (acc + i) = s.regs (acc + i)) ∧
      s'.bufs = s.bufs ∧ s'.caps = s.caps := by
  have hX := hl.opX
  have hY := hl.opY
  have hD := hl.dest
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨s, 0, 0, 0, .skip, ?_, ?_, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩
    · intro i hi; omega
    · simpa [macSum, Nat.mod_one, Nat.div_one] using hsc
  | succ n ih =>
    intro hn
    obtain ⟨s₁, t₁, d₁, p₁, hex₁, hd₁, hc₁, hpres₁, hhigh₁, hbuf₁, hcap₁⟩ := ih (by omega)
    have hcfit : macSum 0 X yv n / 2 ^ (64 * n) < 2 ^ 64 := macSum_div_lt 0 X yv n hyv
    have hxn : s₁.regs (x + n) = BitVec.ofNat 64 (limb 64 X n) := by
      rw [hpres₁ _ (by omega)]; exact hxr n (by omega)
    have hyn : s₁.regs y = BitVec.ofNat 64 yv := by rw [hpres₁ _ (by omega)]; exact hsy
    have hlow : macSum 0 X yv n % 2 ^ (64 * n) < 2 ^ (64 * n) :=
      Nat.mod_lt _ (Nat.two_pow_pos _)
    have hsplit : macSum 0 X yv (n + 1)
        = macSum 0 X yv n % 2 ^ (64 * n)
          + (macSum 0 X yv n / 2 ^ (64 * n) + 0 + limb 64 X n * yv) * 2 ^ (64 * n) := by
      rw [macSum_succ, limb_zero]; exact split_of_div_mod _ _ _ _
    have hPsplit : macSum 0 X yv n
        = macSum 0 X yv n % 2 ^ (64 * n)
          + macSum 0 X yv n / 2 ^ (64 * n) * 2 ^ (64 * n) := by
      have h1 : 2 ^ (64 * n) * (macSum 0 X yv n / 2 ^ (64 * n))
          + macSum 0 X yv n % 2 ^ (64 * n) = macSum 0 X yv n := Nat.div_add_mod _ _
      calc macSum 0 X yv n
          = 2 ^ (64 * n) * (macSum 0 X yv n / 2 ^ (64 * n))
            + macSum 0 X yv n % 2 ^ (64 * n) := h1.symm
        _ = macSum 0 X yv n % 2 ^ (64 * n)
            + macSum 0 X yv n / 2 ^ (64 * n) * 2 ^ (64 * n) := by ring
    have hT : limb 64 X n * yv + macSum 0 X yv n / 2 ^ (64 * n)
        = macSum 0 X yv n / 2 ^ (64 * n) + 0 + limb 64 X n * yv := by ring
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hdn, hsc₂, hpres₂, hbuf₂, hcap₂⟩ :=
      macSetStep_exec (C := C) (acc := acc) (by omega) (by omega) (by omega)
        (limb_lt 64 X n) hyv hcfit hxn hyn hc₁
    refine ⟨s₂, _, _, _, .seq hex₁ hex₂, ?_, ?_, ?_, ?_,
      hbuf₂.trans hbuf₁, hcap₂.trans hcap₁⟩
    · intro i hi
      rcases Nat.lt_or_ge i n with hlt | hge
      · have hL : limb 64 (macSum 0 X yv n) i
            = limb 64 (macSum 0 X yv n % 2 ^ (64 * n)) i := by
          conv_lhs => rw [hPsplit]
          exact limb_add_shift_lt hlt
        have hR : limb 64 (macSum 0 X yv (n + 1)) i
            = limb 64 (macSum 0 X yv n % 2 ^ (64 * n)) i := by
          rw [hsplit]; exact limb_add_shift_lt hlt
        rw [hpres₂ _ (by omega) (by omega) (by omega) (by omega) (by omega),
          hd₁ i hlt, hL, hR]
      · have hin : i = n := by omega
        rw [hin, hdn, hsplit, limb_add_shift_eq hlow, hT]
    · rw [hsc₂, hsplit, div_add_shift hlow, hT]
    · intro q hq
      rw [hpres₂ _ (by omega) (by omega) (by omega) (by omega) (by omega), hpres₁ q hq]
    · intro i hi
      rw [hpres₂ _ (by omega) (by omega) (by omega) (by omega) (by omega),
        hhigh₁ i (by omega)]

/-- `macSetLimbs`: the destination's `k` limbs and the carry in `sc` are the exact
`k + 1`-word value of `X * y`. -/
theorem macSetLimbs_exec {k acc x y sc : ℕ} (hl : MacLayout k acc x y sc)
    {s : State 64} {X yv : ℕ} (hyv : yv < 2 ^ 64) (hXlt : X < 2 ^ (64 * k))
    (hxr : RegsEnc s x k X) (hsy : s.regs y = BitVec.ofNat 64 yv) :
    ∃ s' t dd pp, Exec C (macSetLimbs k acc x y sc) s s' t dd pp ∧
      (∀ i < k, s'.regs (acc + i) = BitVec.ofNat 64 (limb 64 (X * yv) i)) ∧
      s'.regs sc = BitVec.ofNat 64 (X * yv / 2 ^ (64 * k)) ∧
      (∀ q, q < sc → s'.regs q = s.regs q) ∧
      (∀ i, k ≤ i → s'.regs (acc + i) = s.regs (acc + i)) ∧
      s'.bufs = s.bufs ∧ s'.caps = s.caps := by
  have hX := hl.opX
  have hY := hl.opY
  have hD := hl.dest
  have hsum : macSum 0 X yv k = X * yv := by
    simp only [macSum, Nat.mod_eq_of_lt hXlt, Nat.zero_mod, Nat.zero_add]
  have hxr' : RegsEnc (s.setReg sc 0) x k X := by
    intro i hi; rw [regs_setReg_ne _ _ (show x + i ≠ sc by omega)]; exact hxr i hi
  have hsy' : (s.setReg sc (0 : Word 64)).regs y = BitVec.ofNat 64 yv := by
    rw [regs_setReg_ne _ _ (show y ≠ sc by omega)]; exact hsy
  have hsc' : (s.setReg sc (0 : Word 64)).regs sc = BitVec.ofNat 64 0 := by simp
  obtain ⟨s', t', d', p', hex, hd, hc, hpres, hhigh, hbuf, hcap⟩ :=
    macSetLoop_exec (C := C) hl hyv hxr' hsy' hsc' k le_rfl
  refine ⟨s', _, _, _, .seq .imm hex, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; rw [hd i hi, hsum]
  · rw [hc, hsum]
  · intro q hq
    rw [hpres q hq, regs_setReg_ne _ _ (show q ≠ sc by omega)]
  · intro i hi
    rw [hhigh i hi, regs_setReg_ne _ _ (show acc + i ≠ sc by omega)]
  · simpa using hbuf
  · simpa using hcap

end Caliper.MultiLimb
