/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.FrontB.Words

/-!
# The one-circuit (base of the ladder): a canonical 1-circuit cycle is trivial

The circuit ladder that closes Front B (`Threads.lean`, `LadderCompletes` /
`hercher_min_circuit_count`) has its base case at `circuits v = 1`.  Up to
rotation every one-circuit word is `trueᵃ falseᵇ` (`a` odd steps then `b`
halvings).  This file pins the **arithmetic core** of the base case, with no
transcendence input, purely from the `Words.lean` definitions.

## Closed forms (proved)

For `w = trueᵃ ++ falseᵇ`:
* `ones w = a`, `w.length = a + b`;
* `numer w = 3ᵃ − 2ᵃ` — **independent of `b`** (the trailing halvings contribute
  nothing to the numerator: `numer (false :: t) = 2 · numer t` and
  `numer (falseᵇ) = 0`, while each prepended `true` adds `3^(ones tail)`);
* `den w = 2^(a+b) − 3ᵃ`.

## The Diophantine base case

`oneCircuitCanonical_trivial`: for `a, b ≥ 1`, if `0 < den w` and `den w ∣ numer w`
then `a = 1 ∧ b = 1` (the trivial cycle `{1,2}`, member `1`).  Verified by
`experiments`: the sole solution through `a ≤ 8` is `(1,1)`.

Reduction (proved, transcendence-free): `numer w + den w = 2ᵃ (2ᵇ − 1)` and
`den w` is odd, so `den w ∣ numer w ↔ den w ∣ 2ᵇ − 1`.  The `a = 1` slice is then
closed elementarily here.

**The `a ≥ 2` slice is NOT elementary — it is Steiner's theorem (1977).**  After
the reduction it asks: can `den w = 2^(a+b) − 3ᵃ` divide `2ᵇ − 1` with `a ≥ 2`?
`den ∣ 2ᵇ−1` gives `den ≤ 2ᵇ−1`, which with `den > 0` pins `2ᵇ` to the interval
`(3ᵃ/2ᵃ, 3ᵃ/(2ᵃ−1))` — width-ratio `2ᵃ/(2ᵃ−1) → 1`.  "No power of `2` in that
interval for `a ≥ 2`" is exactly the statement `‖a·log₂3‖ ≳ 2^{−a}`, an **effective
irrationality-measure / Baker** lower bound (Steiner used transcendence to close the
one-circuit / one-cycle case; cf. `FRONT-B-ROUTES.md` §filter).  It is therefore
**not** an `omega` argument (correcting the earlier `PENDING_WORK.md` "path 1"
claim), and it is **off the ladder's critical path**: `hercher_min_circuit_count`
(no-transcendence, in `Threads.lean`) already gives triviality for every circuit
count `≤ 91`, this rung included.

We therefore keep the file **transcendence-free** by isolating that single input as
an explicit hypothesis `SteinerOneCircuit` (a `def`, in the style of the board's
`Compression`/`LadderCompletes` open targets), NOT as a `sorry` and NOT as a new
axiom.  The elementary reduction below is complete and sorry-free.
-/

namespace CollatzMoonshot.FrontB

/-- The canonical one-circuit word: `a` odd steps then `b` halvings. -/
def oneCircuitWord (a b : ℕ) : List Bool :=
  List.replicate a true ++ List.replicate b false

theorem ones_append (l1 l2 : List Bool) : ones (l1 ++ l2) = ones l1 + ones l2 := by
  induction l1 with
  | nil => simp [ones]
  | cons b t ih => cases b <;> simp [ones, ih] <;> omega

@[simp] theorem ones_replicate_true (n : ℕ) : ones (List.replicate n true) = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, ones]; omega

@[simp] theorem ones_replicate_false (n : ℕ) : ones (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, ones]; exact ih

@[simp] theorem numer_replicate_false (n : ℕ) : numer (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, numer, ih]

@[simp] theorem ones_oneCircuitWord (a b : ℕ) : ones (oneCircuitWord a b) = a := by
  unfold oneCircuitWord; rw [ones_append]; simp

@[simp] theorem length_oneCircuitWord (a b : ℕ) :
    (oneCircuitWord a b).length = a + b := by
  simp [oneCircuitWord]

/-- **Closed form for the numerator**, independent of `b`: `numer (trueᵃ falseᵇ) = 3ᵃ − 2ᵃ`. -/
theorem numer_oneCircuitWord (a b : ℕ) :
    numer (oneCircuitWord a b) = 3 ^ a - 2 ^ a := by
  unfold oneCircuitWord
  induction a with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, numer, ih, ones_append,
      ones_replicate_true, ones_replicate_false]
    have h2 : 2 ^ n ≤ 3 ^ n := Nat.pow_le_pow_left (by norm_num) n
    rw [pow_succ 2 n, pow_succ 3 n, Nat.add_zero]
    omega

/-- Closed form for the denominator. -/
theorem den_oneCircuitWord (a b : ℕ) :
    den (oneCircuitWord a b) = 2 ^ (a + b) - 3 ^ a := by
  unfold den
  rw [length_oneCircuitWord, ones_oneCircuitWord]

/-- `numer w + den w = 2ᵃ (2ᵇ − 1)` (as integers), the identity behind the
`den ∣ numer ↔ den ∣ 2ᵇ − 1` reduction. -/
theorem numer_add_den_oneCircuitWord (a b : ℕ) (hpos : 0 < den (oneCircuitWord a b)) :
    (numer (oneCircuitWord a b) : ℤ) + den (oneCircuitWord a b)
      = 2 ^ a * (2 ^ b - 1) := by
  have hden : den (oneCircuitWord a b) = 2 ^ (a + b) - 3 ^ a := den_oneCircuitWord a b
  have hnum : numer (oneCircuitWord a b) = 3 ^ a - 2 ^ a := numer_oneCircuitWord a b
  have h2 : (2 : ℕ) ^ a ≤ 3 ^ a := Nat.pow_le_pow_left (by norm_num) a
  have hnumZ : (numer (oneCircuitWord a b) : ℤ) = (3 : ℤ) ^ a - 2 ^ a := by
    rw [hnum]; push_cast [h2]; ring
  rw [hnumZ, hden]
  have : (2 : ℤ) ^ (a + b) = 2 ^ a * 2 ^ b := by rw [pow_add]
  rw [this]; ring

/-- **The single transcendence input for the one-circuit base rung** (Steiner 1977).
Isolated as an explicit hypothesis — a `def`, exactly as the board states its open
targets `Compression`/`LadderCompletes` — so that `OneCircuit.lean` stays
sorry-free and axiom-free while naming precisely what is not elementary.

Content: for `a ≥ 2` there is no canonical one-circuit integer cycle, i.e. the odd
denominator `den (trueᵃfalseᵇ) = 2^(a+b) − 3ᵃ` (when positive) never divides
`2ᵇ − 1`.  Equivalently (via `den ∣ 2ᵇ−1 ⇒ den ≤ 2ᵇ−1`) the interval
`(3ᵃ/2ᵃ, 3ᵃ/(2ᵃ−1))` contains no power of `2` — an effective irrationality-measure
lower bound `‖a·log₂3‖ ≳ 2^{−a}` (Baker/Rhin). -/
def SteinerOneCircuit : Prop :=
  ∀ a b : ℕ, 2 ≤ a → 1 ≤ b → 0 < den (oneCircuitWord a b) →
    ¬ (den (oneCircuitWord a b) ∣ (2 ^ b - 1 : ℤ))

/-- **Base of the circuit ladder (arithmetic core).**  A canonical one-circuit
integer cycle is the trivial one.

Transcendence-free modulo the single explicit input `SteinerOneCircuit`: the `a = 1`
slice is proved elementarily; the `a ≥ 2` slice is Steiner's theorem, discharged by
the hypothesis (see its docstring and `PENDING_WORK.md`). -/
theorem oneCircuitCanonical_trivial (hSteiner : SteinerOneCircuit)
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hpos : 0 < den (oneCircuitWord a b))
    (hdvd : den (oneCircuitWord a b) ∣ (numer (oneCircuitWord a b) : ℤ)) :
    a = 1 ∧ b = 1 := by
  -- reduction: den is odd and den ∣ numer + den = 2ᵃ(2ᵇ−1), so den ∣ 2ᵇ − 1.
  have hne : oneCircuitWord a b ≠ [] := by
    intro h; have := length_oneCircuitWord a b; rw [h] at this; simp at this; omega
  have hodd : ¬ (2 : ℤ) ∣ den (oneCircuitWord a b) := not_two_dvd_den hne
  have hsum := numer_add_den_oneCircuitWord a b hpos
  have hdvd_sum : den (oneCircuitWord a b) ∣ 2 ^ a * (2 ^ b - 1) := by
    rw [← hsum]; exact dvd_add hdvd dvd_rfl
  have hcop : IsCoprime (den (oneCircuitWord a b)) ((2 : ℤ) ^ a) := by
    have : IsCoprime (den (oneCircuitWord a b)) (2 : ℤ) :=
      (Int.prime_two.coprime_iff_not_dvd.mpr hodd).symm
    exact this.pow_right
  have hdvd_pow : den (oneCircuitWord a b) ∣ (2 ^ b - 1) :=
    hcop.dvd_of_dvd_mul_left hdvd_sum
  -- from here: the classical bound forcing a = 1.
  rcases Nat.lt_or_ge a 2 with haa | haa
  · -- a = 1
    have ha1 : a = 1 := by omega
    subst ha1
    -- den = 2^(1+b) - 3, numer = 3 - 2 = 1, so den ∣ 1 hence den = 1, giving b = 1.
    have hnum1 : (numer (oneCircuitWord 1 b) : ℤ) = 1 := by
      rw [numer_oneCircuitWord]; norm_num
    have hden1 : den (oneCircuitWord 1 b) = 2 ^ (1 + b) - 3 := by
      rw [den_oneCircuitWord]; norm_num
    have hdvd1 : den (oneCircuitWord 1 b) ∣ (1 : ℤ) := by rw [← hnum1]; exact hdvd
    have hle : den (oneCircuitWord 1 b) = 1 := by
      have := Int.le_of_dvd (by norm_num) hdvd1
      omega
    rw [hden1] at hle
    -- 2^(1+b) - 3 = 1 → 2^(1+b) = 4 → 1+b = 2 → b = 1
    have h4 : (2 : ℤ) ^ (1 + b) = 4 := by omega
    have hn4 : (2 : ℕ) ^ (1 + b) = 2 ^ 2 := by
      have h : (2 : ℕ) ^ (1 + b) = 4 := by exact_mod_cast h4
      omega
    have hb1 : 1 + b = 2 := Nat.pow_right_injective (by norm_num) hn4
    exact ⟨rfl, by omega⟩
  · -- a ≥ 2: no canonical one-circuit integer cycle exists (Steiner 1977).
    -- hpos (0 < 2^(a+b)−3^a), hdvd_pow (den ∣ 2^b−1), and haa (2 ≤ a) are jointly
    -- contradictory — this is exactly the isolated transcendence input.
    exact absurd hdvd_pow (hSteiner a b haa hb hpos)

end CollatzMoonshot.FrontB
