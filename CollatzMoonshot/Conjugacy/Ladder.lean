/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Obstructions.ParityWordGenericity

/-!
# The conjugacy ladder: the 3x+1 conjugacy as a triangular map on binary digits

Terras's bijection reads the shortcut map `tstep` on the 2-adic integers through the parity
word: `Q(x)_j = tstep^[j] x mod 2` is a bijection of `ℤ₂` onto `{0,1}^ℕ` conjugating `tstep`
to the shift.  This module freezes that conjugacy as a **computable triangular map on binary
digits**, on `ℕ`, with no `ℤ_[2]` in sight.

* **The lift identity** (`tstep_iterate_add_mul_two_pow`): adding `c · 2^j` to the start adds
  exactly `c · 3^a` to the `j`-th iterate, `a` the number of odd steps taken.  Its parity
  corollaries say the `j`-th letter flips under `+2^j` (`accWord_add_two_pow`) and depends only
  on the residue mod `2^(j+1)` (`accWord_congr_mod`): this is Terras's bijection, digit by
  digit.
* **The residue reading** (`tstep_iterate_lt_three_pow`, `tstep_iterate_modEq`,
  `tstep_iterate_eq_of_modEq`): for a `j`-bit start `N`, the `j`-th iterate is the unique
  `y < 3^a` with `2^j · y ≡ numer(v) (mod 3^a)`, `v` the parity word, i.e. the least nonnegative
  residue of `numer(v) · 2^(-j)` mod `3^a`.
* **The triangular form** (`Qword_eq_xor`): `Qword ε j = ε j ^^ feedback ε j`, where
  `feedback ε j` is the parity of `tstep^[j]` of the `j`-bit truncation of `ε`.  The map is the
  identity plus a strictly lower-triangular feedback term, so it has an inverse built digit by
  digit (`prefixInt`, `Qinv`), and the pair is a bijection of `ℕ → Bool` (`Qword_Qinv`,
  `Qinv_Qword`, `Qword_bijective`).  The first feedback terms are explicit
  (`feedback_zero`, `feedback_one`, `feedback_two`): the parity of `tstep x` is bit `1` of `x`.
* **The bias** (`bias`): `bias j / 2^j = 2 · P(Q_j = ε_j) − 1` is the correlation between the
  `j`-th letter and the `j`-th digit, over uniform digits.  Small values are kernel-checked
  (`bias_one` … `bias_eight`); the conjectures `BiasDecays`, `BiasSqrtLaw`, `BiasPositive`
  are frozen from the numerics of 2026-10-21.

## The ladder

| rung | digits `ε` | word `Qword ε` |
|---|---|---|
| integer | finite support, `natDigits n` | `accWord n` (`Qword_natDigits`).  Eventually periodic iff the orbit does not diverge; `IntegerRung` is the "no divergent orbit" half of Collatz (`not_diverges_of_integerRung`) |
| rational | eventually periodic | Lagarias's periodicity conjecture `RationalRung`: the word is eventually periodic too.  Implies the integer rung (`integerRung_of_rationalRung`) |
| Maze | a divergent integer | never normal: `Obstructions.ParityWord.accWord_not_normal_of_diverges` (the Maze row "normality of a divergent orbit's parity word") |
| generic | normal | not normal in general (`QNotNormalityPreserving`, `QinvNotNormalityPreserving`); which `ε` survive is the question |
| explicit | Thue–Morse, Fibonacci | `ThueMorseCollatzGeneric`, `SturmianCollatzGeneric`: the Collatz orbit of an automatic or Sturmian 2-adic integer is equidistributed |

The top rungs are the new objects: Collatz on `ℤ₂` has long been known to be conjugate to a
shift (Terras, Lagarias, Bernstein), but the *digit-level* behaviour of the conjugacy on
specific non-rational 2-adics is, as far as this repo knows, not in print.

## Complexity

`Qword` and `Qinv` preserve the Kolmogorov complexity of prefixes up to `O(log j)`: the
`j`-bit prefix of `Qword ε` is a computable function of the `j`-bit prefix of `ε` and
conversely (`bitsToNat`, `prefixInt` are computable bijections at each length), so each
prefix is describable from the other with a constant-size program plus `j` in binary.  In
particular the conjugacy cannot create or destroy incompressibility; what it can do
(`QNotNormalityPreserving`) is reshuffle statistics without touching complexity.  Prose only,
no theorem.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord

/-! ## Odd-step count and the lift identity -/

/-- The number of odd terms among `tstep^[i] r`, `i < j`: `ones` of the parity trace. -/
def oddCount (r j : ℕ) : ℕ := ones (traceWord r j)

theorem oddCount_zero (r : ℕ) : oddCount r 0 = 0 := rfl

theorem oddCount_succ (r j : ℕ) :
    oddCount r (j + 1) = oddCount (tstep r) j + (if r % 2 = 1 then 1 else 0) :=
  FrontA.ones_traceWord_succ r j

/-- The back-recursion: the `(j+1)`-st count adds the parity of the `j`-th iterate. -/
theorem oddCount_succ' (r : ℕ) : ∀ j, oddCount r (j + 1) =
    oddCount r j + (if tstep^[j] r % 2 = 1 then 1 else 0) := by
  suffices h : ∀ j r, oddCount r (j + 1) = oddCount r j + (if tstep^[j] r % 2 = 1 then 1 else 0)
    from fun j => h j r
  intro j
  induction j with
  | zero =>
    intro r
    simp only [oddCount_succ, oddCount_zero, Function.iterate_zero_apply]
    rfl
  | succ k ih =>
    intro r
    rw [oddCount_succ, ih, oddCount_succ r k, Function.iterate_succ_apply]
    ring

/-- `oddCount` is what its docstring says: the number of `true` letters of `accWord r` below
`j`. -/
theorem oddCount_eq_sum (r j : ℕ) :
    oddCount r j = ∑ i ∈ Finset.range j, (if accWord r i then 1 else 0) := by
  induction j with
  | zero => simp [oddCount_zero]
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih, oddCount_succ']
    simp [accWord]

/-- One accelerated step commutes with adding an even number, up to the factor `3` on an odd
start. -/
theorem tstep_add_two_mul (r m : ℕ) :
    tstep (r + 2 * m) = tstep r + (if r % 2 = 1 then 3 else 1) * m := by
  unfold tstep
  split_ifs <;> omega

/-- **The lift identity.**  Adding `c · 2^j` to the start adds exactly `c · 3^a` to the `j`-th
iterate, where `a = oddCount r j` is the number of odd steps the base orbit takes. -/
theorem tstep_iterate_add_mul_two_pow (j : ℕ) : ∀ r c : ℕ,
    tstep^[j] (r + c * 2 ^ j) = tstep^[j] r + c * 3 ^ oddCount r j := by
  induction j with
  | zero => intro r c; simp [oddCount_zero]
  | succ k ih =>
    intro r c
    have e : r + c * 2 ^ (k + 1) = r + 2 * (c * 2 ^ k) := by ring
    rw [e, Function.iterate_succ_apply, Function.iterate_succ_apply, tstep_add_two_mul,
      ← mul_assoc, ih, oddCount_succ]
    split_ifs <;> ring

/-- **L1.**  `tstep^[j] (r + 2^j) = tstep^[j] r + 3^(oddCount r j)`. -/
theorem tstep_iterate_add_two_pow (j r : ℕ) :
    tstep^[j] (r + 2 ^ j) = tstep^[j] r + 3 ^ oddCount r j := by
  simpa using tstep_iterate_add_mul_two_pow j r 1

theorem three_pow_mod_two (a : ℕ) : 3 ^ a % 2 = 1 := by
  rw [Nat.pow_mod]; simp

/-- Adding `2^j` flips the `j`-th parity letter (because `3^a` is odd). -/
theorem accWord_add_two_pow (r j : ℕ) : accWord (r + 2 ^ j) j = !(accWord r j) := by
  have h3 := three_pow_mod_two (oddCount r j)
  simp only [accWord, tstep_iterate_add_two_pow]
  rcases Nat.mod_two_eq_zero_or_one (tstep^[j] r) with h | h
  · have : (tstep^[j] r + 3 ^ oddCount r j) % 2 = 1 := by omega
    simp [h, this]
  · have : (tstep^[j] r + 3 ^ oddCount r j) % 2 = 0 := by omega
    simp [h, this]

/-- Adding a multiple of `2^(j+1)` leaves the `j`-th parity letter alone. -/
theorem accWord_add_mul_two_pow_succ (r c j : ℕ) :
    accWord (r + c * 2 ^ (j + 1)) j = accWord r j := by
  have e : r + c * 2 ^ (j + 1) = r + (2 * c) * 2 ^ j := by ring
  simp only [accWord, e, tstep_iterate_add_mul_two_pow]
  rw [decide_eq_decide, mul_assoc]
  omega

theorem accWord_add_two_pow_succ (r j : ℕ) : accWord (r + 2 ^ (j + 1)) j = accWord r j := by
  simpa using accWord_add_mul_two_pow_succ r 1 j

/-- **Terras, digit by digit.**  The `j`-th parity letter depends only on `r mod 2^(j+1)`. -/
theorem accWord_mod_two_pow_succ (r j : ℕ) : accWord (r % 2 ^ (j + 1)) j = accWord r j := by
  conv_rhs => rw [← Nat.mod_add_div r (2 ^ (j + 1)), mul_comm]
  exact (accWord_add_mul_two_pow_succ _ _ _).symm

theorem accWord_congr_mod {r s : ℕ} (j : ℕ) (h : r % 2 ^ (j + 1) = s % 2 ^ (j + 1)) :
    accWord r j = accWord s j := by
  rw [← accWord_mod_two_pow_succ r, h, accWord_mod_two_pow_succ]

/-! ## The residue reading of a `j`-bit start -/

/-- **L2.**  The `j`-th iterate of a `j`-bit start is below `3^a`
(`FrontA.tstep_iterate_lt_pow_ones`, restated through `oddCount`). -/
theorem tstep_iterate_lt_three_pow {j r : ℕ} (hr : r < 2 ^ j) :
    tstep^[j] r < 3 ^ oddCount r j :=
  FrontA.tstep_iterate_lt_pow_ones hr

/-- `2^j · tstep^[j] r ≡ numer(v) (mod 3^a)`, `v` the parity trace: the iterate identity
`tstep_iterate_identity` read modulo `3^a`. -/
theorem tstep_iterate_modEq (j r : ℕ) :
    2 ^ j * tstep^[j] r ≡ numer (traceWord r j) [MOD 3 ^ oddCount r j] := by
  show (2 ^ j * tstep^[j] r) % 3 ^ oddCount r j = numer (traceWord r j) % 3 ^ oddCount r j
  rw [tstep_iterate_identity]
  exact Nat.mul_add_mod _ _ _

/-- **The residue reading.**  For a `j`-bit start `r`, `tstep^[j] r` is the unique `y < 3^a`
with `2^j · y ≡ numer(v) (mod 3^a)`: the least nonnegative residue of `numer(v) · 2^(-j)`
modulo `3^a`.  (The start `r` itself enters only through `v`, since `3^a · r ≡ 0`.) -/
theorem tstep_iterate_eq_of_modEq {j r y : ℕ} (hr : r < 2 ^ j) (hy : y < 3 ^ oddCount r j)
    (hmod : 2 ^ j * y ≡ numer (traceWord r j) [MOD 3 ^ oddCount r j]) :
    tstep^[j] r = y := by
  have h : 2 ^ j * tstep^[j] r ≡ 2 ^ j * y [MOD 3 ^ oddCount r j] :=
    (tstep_iterate_modEq j r).trans hmod.symm
  have hcop : Nat.gcd (3 ^ oddCount r j) (2 ^ j) = 1 :=
    Nat.Coprime.pow _ _ (by decide : Nat.Coprime 3 2)
  exact (Nat.ModEq.cancel_left_of_coprime hcop h).eq_of_lt_of_lt
    (tstep_iterate_lt_three_pow hr) hy

/-! ## Digits, truncations, and the conjugacy -/

/-- The `j`-bit truncation of a digit sequence: `∑ i < j, ε i · 2^i`. -/
def bitsToNat (ε : ℕ → Bool) (j : ℕ) : ℕ := ∑ i ∈ Finset.range j, (if ε i then 2 ^ i else 0)

@[simp] theorem bitsToNat_zero (ε : ℕ → Bool) : bitsToNat ε 0 = 0 := by simp [bitsToNat]

theorem bitsToNat_succ (ε : ℕ → Bool) (j : ℕ) :
    bitsToNat ε (j + 1) = bitsToNat ε j + (if ε j then 2 ^ j else 0) :=
  Finset.sum_range_succ _ _

theorem bitsToNat_lt (ε : ℕ → Bool) (j : ℕ) : bitsToNat ε j < 2 ^ j := by
  induction j with
  | zero => simp
  | succ k ih => rw [bitsToNat_succ, pow_succ]; split_ifs <;> omega

/-- Reading the top bit back off a `(j+1)`-bit number whose low part is below `2^j`. -/
theorem add_ite_two_pow_div {b j : ℕ} (hb : b < 2 ^ j) (c : Bool) :
    (b + if c then 2 ^ j else 0) / 2 ^ j = if c then 1 else 0 := by
  have hpos : 0 < 2 ^ j := by positivity
  cases c
  · simp [Nat.div_eq_of_lt hb]
  · simp [Nat.add_div_right _ hpos, Nat.div_eq_of_lt hb]

/-- **The conjugacy on digits.**  `Qword ε j` is the `j`-th parity letter of the 2-adic integer
with binary digits `ε`; by `accWord_congr_mod` it is determined by the `(j+1)`-bit truncation. -/
def Qword (ε : ℕ → Bool) : ℕ → Bool := fun j => accWord (bitsToNat ε (j + 1)) j

/-- The parity of `tstep^[j]` of the `j`-bit truncation: the feedback term of the triangular
form `Qword_eq_xor`. -/
def feedback (ε : ℕ → Bool) (j : ℕ) : Bool := accWord (bitsToNat ε j) j

/-- The `j`-bit integer whose parity word agrees with `w` below `j`, built digit by digit: bit
`j` is set exactly when the current prefix gets the `j`-th letter wrong. -/
def prefixInt (w : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | j + 1 => prefixInt w j + (if (w j != accWord (prefixInt w j) j) then 2 ^ j else 0)

/-- **The inverse conjugacy.**  `Qinv w` is the digit sequence of the 2-adic integer with parity
word `w`: bit `j` of `prefixInt w (j+1)`. -/
def Qinv (w : ℕ → Bool) : ℕ → Bool := fun j => decide (prefixInt w (j + 1) / 2 ^ j % 2 = 1)

theorem prefixInt_zero (w : ℕ → Bool) : prefixInt w 0 = 0 := rfl

theorem prefixInt_succ (w : ℕ → Bool) (j : ℕ) :
    prefixInt w (j + 1) =
      prefixInt w j + (if (w j != accWord (prefixInt w j) j) then 2 ^ j else 0) := rfl

theorem prefixInt_lt (w : ℕ → Bool) (j : ℕ) : prefixInt w j < 2 ^ j := by
  induction j with
  | zero => simp [prefixInt_zero]
  | succ k ih => rw [prefixInt_succ, pow_succ]; split_ifs <;> omega

theorem Qinv_eq (w : ℕ → Bool) (j : ℕ) : Qinv w j = (w j != accWord (prefixInt w j) j) := by
  unfold Qinv
  rw [prefixInt_succ, add_ite_two_pow_div (prefixInt_lt w j)]
  cases h : (w j != accWord (prefixInt w j) j) <;> simp

/-- The truncations of `Qinv w` are the `prefixInt`s. -/
theorem bitsToNat_Qinv (w : ℕ → Bool) (j : ℕ) : bitsToNat (Qinv w) j = prefixInt w j := by
  induction j with
  | zero => simp [prefixInt_zero]
  | succ k ih => rw [bitsToNat_succ, ih, Qinv_eq, prefixInt_succ]

/-- **L3 (right inverse).**  `Qword (Qinv w) = w`. -/
theorem Qword_Qinv (w : ℕ → Bool) : Qword (Qinv w) = w := by
  funext j
  simp only [Qword]
  rw [bitsToNat_Qinv, prefixInt_succ]
  cases w j <;> cases ha : accWord (prefixInt w j) j <;>
    simp [ha, accWord_add_two_pow]

/-- The `prefixInt`s of `Qword ε` are the truncations of `ε`. -/
theorem prefixInt_Qword (ε : ℕ → Bool) (j : ℕ) : prefixInt (Qword ε) j = bitsToNat ε j := by
  induction j with
  | zero => simp [prefixInt_zero]
  | succ k ih =>
    rw [prefixInt_succ, ih, bitsToNat_succ]
    congr 1
    simp only [Qword, bitsToNat_succ]
    cases ε k <;> cases ha : accWord (bitsToNat ε k) k <;>
      simp [ha, accWord_add_two_pow]

/-- **L3 (left inverse).**  `Qinv (Qword ε) = ε`. -/
theorem Qinv_Qword (ε : ℕ → Bool) : Qinv (Qword ε) = ε := by
  funext j
  simp only [Qinv]
  rw [prefixInt_Qword, bitsToNat_succ, add_ite_two_pow_div (bitsToNat_lt ε j)]
  cases ε j <;> simp

theorem Qword_bijective : Function.Bijective Qword :=
  Function.bijective_iff_has_inverse.mpr ⟨Qinv, Qinv_Qword, Qword_Qinv⟩

theorem Qinv_bijective : Function.Bijective Qinv :=
  Function.bijective_iff_has_inverse.mpr ⟨Qword, Qword_Qinv, Qinv_Qword⟩

/-- The conjugacy as an equivalence of digit space with itself. -/
def QwordEquiv : (ℕ → Bool) ≃ (ℕ → Bool) where
  toFun := Qword
  invFun := Qinv
  left_inv := Qinv_Qword
  right_inv := Qword_Qinv

/-! ## The triangular form -/

/-- **L4 (the triangular form).**  `Qword ε j = ε j ^^ feedback ε j`: the `j`-th letter is the
`j`-th digit, flipped by a term that depends only on the digits below `j`. -/
theorem Qword_eq_xor (ε : ℕ → Bool) (j : ℕ) : Qword ε j = (ε j ^^ feedback ε j) := by
  simp only [Qword, feedback, bitsToNat_succ]
  cases ε j <;> simp [accWord_add_two_pow]

/-- **L5.**  No feedback at digit `0`: the first letter is the parity of `x`. -/
theorem feedback_zero (ε : ℕ → Bool) : feedback ε 0 = false := by
  simp [feedback, accWord]

/-- **L5.**  No feedback at digit `1`: the parity of `tstep x` is bit `1` of `x`. -/
theorem feedback_one (ε : ℕ → Bool) : feedback ε 1 = false := by
  simp only [feedback, bitsToNat_succ, bitsToNat_zero]
  cases ε 0 <;> decide

/-- **L5.**  The first genuine feedback: the parity of `tstep^[2] x` is bit `2` of `x` flipped
exactly when `x ≡ 1 (mod 4)`. -/
theorem feedback_two (ε : ℕ → Bool) : feedback ε 2 = (ε 0 && !ε 1) := by
  simp only [feedback, bitsToNat_succ, bitsToNat_zero]
  cases ε 0 <;> cases ε 1 <;> decide

theorem Qword_zero (ε : ℕ → Bool) : Qword ε 0 = ε 0 := by
  rw [Qword_eq_xor, feedback_zero, Bool.xor_false]

theorem Qword_one (ε : ℕ → Bool) : Qword ε 1 = ε 1 := by
  rw [Qword_eq_xor, feedback_one, Bool.xor_false]

theorem Qword_two (ε : ℕ → Bool) : Qword ε 2 = (ε 2 ^^ (ε 0 && !ε 1)) := by
  rw [Qword_eq_xor, feedback_two]

/-! ## The integer and rational rungs -/

/-- The binary digits of a natural number, as a digit sequence of finite support. -/
def natDigits (n : ℕ) : ℕ → Bool := fun i => decide (n / 2 ^ i % 2 = 1)

theorem bitsToNat_natDigits (n j : ℕ) : bitsToNat (natDigits n) j = n % 2 ^ j := by
  induction j with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    rw [bitsToNat_succ, ih, Nat.mod_pow_succ]
    congr 1
    simp only [natDigits]
    rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ k) with h | h <;> simp [h]

/-- **The integer rung.**  On the digits of an integer, `Qword` is the shortcut parity word. -/
theorem Qword_natDigits (n : ℕ) : Qword (natDigits n) = accWord n := by
  funext j
  simp only [Qword, bitsToNat_natDigits]
  exact accWord_mod_two_pow_succ n j

theorem natDigits_eventuallyPeriodic (n : ℕ) : EventuallyPeriodic (natDigits n) := by
  refine ⟨n, 1, le_rfl, fun k hk => ?_⟩
  have h1 : n / 2 ^ k = 0 :=
    Nat.div_eq_of_lt (lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) hk))
  have h2 : n / 2 ^ (k + 1) = 0 :=
    Nat.div_eq_of_lt
      (lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (by omega)))
  simp [natDigits, h1, h2]

/-- **The integer rung as a node.**  Every integer's parity word is eventually periodic.  This is
the "no divergent orbit" half of the Collatz conjecture: an eventually periodic shortcut parity
forces a cycle (`FrontA.not_diverges_of_eventually_periodic_parity`), and conversely a bounded
orbit repeats.  Open. -/
def IntegerRung : Prop := ∀ n, 1 ≤ n → EventuallyPeriodic (Qword (natDigits n))

theorem not_diverges_of_integerRung (h : IntegerRung) {n : ℕ} (hn : 1 ≤ n) : ¬ Diverges n :=
  fun hdiv => accWord_not_eventuallyPeriodic hn hdiv (by rw [← Qword_natDigits]; exact h n hn)

/-- **The rational rung (Lagarias's periodicity conjecture).**  Eventually periodic digits are
the 2-adic expansions of the rationals with odd denominator, and Lagarias (1985, *The 3x+1
problem and its generalizations*, Conjecture "Periodicity") asks that `Q` map them onto the
eventually periodic words.  The inclusion `Q⁻¹(periodic) ⊆ periodic` is Bernstein's explicit
inverse (1994); this `Prop` is the open inclusion.  Confidence that the transcription is
faithful: 90% (the 2-adic digits of a negative rational are eventually all ones, and those
are included). -/
def RationalRung : Prop := ∀ ε, EventuallyPeriodic ε → EventuallyPeriodic (Qword ε)

theorem integerRung_of_rationalRung (h : RationalRung) : IntegerRung :=
  fun n _ => h _ (natDigits_eventuallyPeriodic n)

/-! ## The bias -/

/-- `bias j = #{r < 2^j : tstep^[j] r even} − #{r < 2^j : tstep^[j] r odd}`.  For `r < 2^j`
the `j`-th digit is `0`, so `Qword_eq_xor` reads this as `∑_ε (−1)^(feedback ε j)` over the
`2^j` digit prefixes: `bias j / 2^j = 2 · P(Q_j = ε_j) − 1`, the correlation between the
`j`-th letter and the `j`-th digit under uniform digits.  `bias 0 = 1`, `bias 1 = 2`
(`feedback_one`), `bias 2 = 2` (`feedback_two`). -/
def bias (j : ℕ) : ℤ := ∑ r ∈ Finset.range (2 ^ j), (if tstep^[j] r % 2 = 0 then 1 else -1)

/-! **L6.**  The teeth test of the definitions: kernel-checked values. -/

theorem bias_zero : bias 0 = 1 := by decide
theorem bias_one : bias 1 = 2 := by decide
theorem bias_two : bias 2 = 2 := by decide
theorem bias_three : bias 3 = 6 := by decide
theorem bias_four : bias 4 = 6 := by decide
theorem bias_five : bias 5 = 14 := by decide
theorem bias_six : bias 6 = 18 := by decide
theorem bias_seven : bias 7 = 34 := by decide +kernel
theorem bias_eight : bias 8 = 34 := by decide +kernel

/-- **Conjecture C1 (bias decay).**  The `j`-th parity letter decorrelates from the `j`-th
binary digit.  Numerics (2026-10-21, `j ≤ 24`): `bias j / 2^j ≈ 2^(−j/2)`.  Confidence 85%.
Mechanism: none proved; the feedback term is the parity of a `j`-step orbit of a uniform
`j`-bit start, and `tstep_iterate_eq_of_modEq` reads it as a residue mod `3^a`, which is
where an equidistribution argument would start. -/
def BiasDecays : Prop := Tendsto (fun j => (bias j : ℝ) / 2 ^ j) atTop (𝓝 0)

/-- **Conjecture C2a (square-root law).**  `|bias j| ≤ C · 2^(j/2)`.  Numerics `j ≤ 24`.
Confidence 60%: the exponent `1/2` is read off a log-log slope over a short range. -/
def BiasSqrtLaw : Prop := ∃ C : ℝ, 0 < C ∧ ∀ j, |(bias j : ℝ)| ≤ C * Real.sqrt 2 ^ j

/-- **Conjecture C2b (positivity).**  `0 < bias j` for `j ≥ 1`: the `j`-th letter agrees with
the `j`-th digit more often than not.  True for `j ≤ 24` (numerics, 2026-10-21) and for
`j ≤ 8` by the kernel checks above.  Confidence 60%. -/
def BiasPositive : Prop := ∀ j, 1 ≤ j → 0 < bias j

/-! ## The top rungs: normality under the conjugacy -/

/-- **Conjecture C3a.**  `Qword` does not preserve normality.  Numerics (2026-10-21): the
parity word of a biased-coin digit sequence looks iid, so, by the bijection, some normal
digit sequence maps to a biased word.  Confidence 80%. -/
def QNotNormalityPreserving : Prop := ∃ ε, Normal ε ∧ ¬ Normal (Qword ε)

/-- **Conjecture C3b.**  `Qinv` does not preserve normality.  Numerics (2026-10-21): `Qinv` of
a golden-mean word (no `11`) has iid-looking binary digits, so some normal word has a
non-normal preimage.  Confidence 80%. -/
def QinvNotNormalityPreserving : Prop := ∃ w, Normal w ∧ ¬ Normal (Qinv w)

/-- The Thue–Morse sequence: `true` when the binary digit sum of `n` is odd. -/
def thueMorse (n : ℕ) : Bool := decide ((Nat.digits 2 n).sum % 2 = 1)

/-- **Conjecture C4a.**  The Collatz orbit of the Thue–Morse 2-adic integer is equidistributed:
its parity word is normal.  Thue–Morse itself is not normal (it is automatic, of linear
complexity), so this would be the conjugacy manufacturing randomness from an automatic
input.  Numerics 2026-10-21.  Confidence 70%. -/
def ThueMorseCollatzGeneric : Prop := Normal (Qword thueMorse)

/-- The Fibonacci word `0100101001001…`, the characteristic Sturmian word of slope `2 − φ`:
`true` at `n` exactly when `⌊(n+2)φ⌋ − ⌊(n+1)φ⌋ = 1` (the difference is `1` or `2` since
`1 < φ < 2`). -/
noncomputable def fibonacciWord (n : ℕ) : Bool :=
  decide (⌊((n : ℝ) + 2) * Real.goldenRatio⌋ - ⌊((n : ℝ) + 1) * Real.goldenRatio⌋ = 1)

/-- **Conjecture C4b.**  The Collatz orbit of the Fibonacci 2-adic integer is equidistributed.
Confidence 65%: the Sturmian input has the lowest possible complexity, so this is the
sharpest form of "the conjugacy manufactures randomness". -/
def SturmianCollatzGeneric : Prop := Normal (Qword fibonacciWord)

end CollatzMoonshot.Conjugacy
