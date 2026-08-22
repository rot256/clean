import Clean.Caliper.Limbs

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

/-- `d ← a + b` over `k` limbs, leaving the carry-out in `sc`. -/
def addLimbs (k d a b sc : ℕ) : Stmt 64 := .imm sc 0 ;; addLoop d a b sc k

/-- The low `n` limbs of both operands, the quantity the first `n` limb steps have
consumed. -/
def partialSum (X Y n : ℕ) : ℕ := X % 2 ^ (64 * n) + Y % 2 ^ (64 * n)

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
theorem partialSum_succ (X Y n : ℕ) :
    partialSum X Y (n + 1) = partialSum X Y n + (limb 64 X n + limb 64 Y n) * 2 ^ (64 * n) := by
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
theorem partialSum_div_le_one (X Y n : ℕ) : partialSum X Y n / 2 ^ (64 * n) ≤ 1 := by
  have hM : 0 < 2 ^ (64 * n) := Nat.two_pow_pos _
  have hlt : partialSum X Y n < 2 * 2 ^ (64 * n) := by
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
theorem addLoop_exec {k d a b sc : ℕ} (hl : AddLayout k d a b sc)
    {s : State 64} {X Y : ℕ} (ha : RegsEnc s a k X) (hb : RegsEnc s b k Y)
    (hsc : s.regs sc = BitVec.ofNat 64 0) :
    ∀ n ≤ k, ∃ s' t dd pp, Exec C (addLoop d a b sc n) s s' t dd pp ∧
      RegsEnc s' d n (partialSum X Y n) ∧
      s'.regs sc = BitVec.ofNat 64 (partialSum X Y n / 2 ^ (64 * n)) ∧
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
    have hclt : partialSum X Y n / 2 ^ (64 * n) ≤ 1 := partialSum_div_le_one X Y n
    -- the operands are below the scratch base, so `n` steps have not touched them
    have hA := hl.opA
    have hB := hl.opB
    have hD := hl.dest
    have hax : s₁.regs (a + n) = BitVec.ofNat 64 (limb 64 X n) := by
      rw [hpres₁ _ (by omega)]; exact ha n (by omega)
    have hby : s₁.regs (b + n) = BitVec.ofNat 64 (limb 64 Y n) := by
      rw [hpres₁ _ (by omega)]; exact hb n (by omega)
    -- the running sum, split at the limb boundary
    have hlow : partialSum X Y n % 2 ^ (64 * n) < 2 ^ (64 * n) :=
      Nat.mod_lt _ (Nat.two_pow_pos _)
    have hsplit : partialSum X Y (n + 1)
        = partialSum X Y n % 2 ^ (64 * n)
          + (partialSum X Y n / 2 ^ (64 * n) + limb 64 X n + limb 64 Y n) * 2 ^ (64 * n) := by
      rw [partialSum_succ]; exact split_of_div_mod _ _ _ _
    have hPsplit : partialSum X Y n
        = partialSum X Y n % 2 ^ (64 * n)
          + partialSum X Y n / 2 ^ (64 * n) * 2 ^ (64 * n) := by
      have h1 : 2 ^ (64 * n) * (partialSum X Y n / 2 ^ (64 * n))
          + partialSum X Y n % 2 ^ (64 * n) = partialSum X Y n := Nat.div_add_mod _ _
      calc partialSum X Y n
          = 2 ^ (64 * n) * (partialSum X Y n / 2 ^ (64 * n))
            + partialSum X Y n % 2 ^ (64 * n) := h1.symm
        _ = partialSum X Y n % 2 ^ (64 * n)
            + partialSum X Y n / 2 ^ (64 * n) * 2 ^ (64 * n) := by ring
    obtain ⟨hword, hcarry⟩ := carry_step (x := limb 64 X n) (y := limb 64 Y n)
      (c := partialSum X Y n / 2 ^ (64 * n)) hxlt hylt hclt
    have hT : limb 64 X n + limb 64 Y n + partialSum X Y n / 2 ^ (64 * n)
        = partialSum X Y n / 2 ^ (64 * n) + limb 64 X n + limb 64 Y n := by ring
    obtain ⟨s₂, t₂, d₂, p₂, hex₂, hdn, hsc₂, hpres₂, hbuf₂, hcap₂⟩ :=
      addStep_exec (C := C) (n := n) (by omega) (by omega) hxlt hylt hclt hax hby hc₁
    refine ⟨s₂, _, _, _, .seq hex₁ hex₂, ?_, ?_, ?_, hbuf₂.trans hbuf₁, hcap₂.trans hcap₁⟩
    · intro i hi
      rcases Nat.lt_or_ge i n with hlt | hge
      · have hL : limb 64 (partialSum X Y n) i
            = limb 64 (partialSum X Y n % 2 ^ (64 * n)) i := by
          conv_lhs => rw [hPsplit]
          exact limb_add_shift_lt hlt
        have hR : limb 64 (partialSum X Y (n + 1)) i
            = limb 64 (partialSum X Y n % 2 ^ (64 * n)) i := by
          rw [hsplit]; exact limb_add_shift_lt hlt
        rw [hpres₂ _ (by omega) (by omega) (by omega) (by omega) (by omega), hd₁ i hlt,
          hL, hR]
      · have : i = n := by omega
        subst this
        rw [hdn, hsplit, limb_add_shift_eq hlow, hT]
    · rw [hsc₂, hsplit, div_add_shift hlow, hT]
    · intro q hq
      rw [hpres₂ _ (by omega) (by omega) (by omega) (by omega) (by omega), hpres₁ q hq]

/-- `addLimbs`: from `k`-limb operands, the destination holds the `k`-limb sum and
the scratch register the carry out of the top limb, so `sc` together with `d` is the
exact `k + 1`-limb value of `X + Y`. -/
theorem addLimbs_exec {k d a b sc : ℕ} (hl : AddLayout k d a b sc)
    {s : State 64} {X Y : ℕ} (hX : X < 2 ^ (64 * k)) (hY : Y < 2 ^ (64 * k))
    (ha : RegsEnc s a k X) (hb : RegsEnc s b k Y) :
    ∃ s' t dd pp, Exec C (addLimbs k d a b sc) s s' t dd pp ∧
      RegsEnc s' d k (X + Y) ∧
      s'.regs sc = BitVec.ofNat 64 ((X + Y) / 2 ^ (64 * k)) ∧
      (∀ q, q < sc → s'.regs q = s.regs q) ∧
      s'.bufs = s.bufs ∧ s'.caps = s.caps := by
  have hA := hl.opA
  have hB := hl.opB
  have hsum : partialSum X Y k = X + Y := by
    simp only [partialSum, Nat.mod_eq_of_lt hX, Nat.mod_eq_of_lt hY]
  have ha' : RegsEnc (s.setReg sc 0) a k X := by
    intro i hi; rw [regs_setReg_ne _ _ (show a + i ≠ sc by omega)]; exact ha i hi
  have hb' : RegsEnc (s.setReg sc 0) b k Y := by
    intro i hi; rw [regs_setReg_ne _ _ (show b + i ≠ sc by omega)]; exact hb i hi
  have hsc' : (s.setReg sc (0 : Word 64)).regs sc = BitVec.ofNat 64 0 := by simp
  obtain ⟨s', t', d', p', hex, hd, hc, hpres, hbuf, hcap⟩ :=
    addLoop_exec (C := C) hl ha' hb' hsc' k le_rfl
  refine ⟨s', _, _, _, .seq .imm hex, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hsum]; exact hd
  · rw [hc, hsum]
  · intro q hq
    rw [hpres q hq, regs_setReg_ne _ _ (show q ≠ sc by omega)]
  · simpa using hbuf
  · simpa using hcap

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

end Caliper.MultiLimb
