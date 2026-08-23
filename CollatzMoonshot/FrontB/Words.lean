/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Parity words and the rotation identity

The word formalism for Front B.  A cycle is encoded by its **parity word**: a list of
`Bool`, `true` at an odd step, `false` at a halving.  Following Halbeisen-Hungerbühler and
Knight, a word `v` of length `k` with `x` ones determines exactly one rational cycle whose
members are `numer v' / den v` over the rotations `v'`, with

`numer v = Σᵢ 3^(x−1−i) · 2^(dᵢ)`   and   `den v = 2^k − 3^x`.

The cycle consists of **integers** iff `den v ∣ numer v`.

## The payoff: the rotation identity

`numer` satisfies an exact two-case identity under rotation (`two_mul_numer_rot`), from
which `dvd_numer_rot_iff` follows: **the divisibility condition is rotation-invariant.**
That is the formal content of the "Route 1 collapse" recorded in `FRONT-B-ROUTES.md` -
gcd-ing over all rotations of the word carries no information the single condition
`den v ∣ numer v` does not already carry, because every rotation's numerator is a unit
multiple of every other's modulo `den v`.

It also explains why Knight's high-cycle proof needs a *difference* of two members rather
than the members themselves: differences of unit multiples are not unit multiples.
-/

namespace CollatzMoonshot.FrontB

/-- Number of odd steps (ones) in a parity word. -/
def ones : List Bool → ℕ
  | [] => 0
  | true :: t => ones t + 1
  | false :: t => ones t

/-- The numerator attached to a parity word.  Prepending a letter shifts every one up by a
position, doubling the value; a leading one is the *first* one, so it carries `3 ^ (ones of
the tail)`. -/
def numer : List Bool → ℕ
  | [] => 0
  | false :: t => 2 * numer t
  | true :: t => 2 * numer t + 3 ^ ones t

/-- The denominator `2^k − 3^x`.  Positive words give positive cycles; `den < 0` is the
negative-integer regime, where nontrivial cycles genuinely exist (see `FrontB/Negative.lean`). -/
def den (v : List Bool) : ℤ := 2 ^ v.length - 3 ^ ones v

/-- Rotate a word one step: the cycle's members are the rotations' numerators. -/
def rot : List Bool → List Bool
  | [] => []
  | b :: t => t ++ [b]

@[simp] theorem ones_nil : ones [] = 0 := rfl
@[simp] theorem numer_nil : numer [] = 0 := rfl

@[simp] theorem ones_append_false (t : List Bool) : ones (t ++ [false]) = ones t := by
  induction t with
  | nil => rfl
  | cons b s ih => cases b <;> simp [ones, ih]

@[simp] theorem ones_append_true (t : List Bool) : ones (t ++ [true]) = ones t + 1 := by
  induction t with
  | nil => rfl
  | cons b s ih => cases b <;> simp [ones, ih] <;> omega

theorem numer_append_false (t : List Bool) : numer (t ++ [false]) = numer t := by
  induction t with
  | nil => rfl
  | cons b s ih => cases b <;> simp [numer, ih]

theorem numer_append_true (t : List Bool) :
    numer (t ++ [true]) = 3 * numer t + 2 ^ t.length := by
  induction t with
  | nil => simp [numer]
  | cons b s ih =>
    cases b <;> simp only [List.cons_append, numer, ih, List.length_cons, ones_append_true]
    · ring
    · rw [pow_succ, pow_succ]; ring

@[simp] theorem ones_rot (v : List Bool) : ones (rot v) = ones v := by
  cases v with
  | nil => rfl
  | cons b t => cases b <;> simp [rot, ones]

@[simp] theorem length_rot (v : List Bool) : (rot v).length = v.length := by
  cases v with
  | nil => rfl
  | cons b t => simp [rot]

@[simp] theorem den_rot (v : List Bool) : den (rot v) = den v := by
  simp [den]

/-- **The rotation identity.**  Rotating multiplies the numerator by `2⁻¹` after an even
step, and by `3 · 2⁻¹` (plus a multiple of the denominator) after an odd step.  Both cases
in one statement: `2 · numer (rot v) = numer v` when the head is `false`, and
`2 · numer (rot v) = 3 · numer v + den v` when the head is `true`. -/
theorem two_mul_numer_rot_false (t : List Bool) :
    2 * numer (rot (false :: t)) = numer (false :: t) := by
  simp [rot, numer, numer_append_false]

theorem two_mul_numer_rot_true (t : List Bool) :
    (2 : ℤ) * numer (rot (true :: t)) = 3 * numer (true :: t) + den (true :: t) := by
  simp only [rot, numer, den, numer_append_true, List.length_cons, ones]
  push_cast
  ring

/-- The denominator is odd: `2^k` is even for a nonempty word and `3^x` is odd. -/
theorem not_two_dvd_den {v : List Bool} (hv : v ≠ []) : ¬ (2 : ℤ) ∣ den v := by
  intro h
  have hlen : v.length ≠ 0 := by
    have := List.length_pos_iff_ne_nil.mpr hv
    omega
  have h2 : (2:ℤ) ∣ 2 ^ v.length := dvd_pow_self 2 hlen
  have h3 : (2:ℤ) ∣ 3 ^ ones v := by
    have hd := dvd_sub h2 h
    simpa [den] using hd
  have := Int.prime_two.dvd_of_dvd_pow h3
  norm_num at this

/-- The denominator is coprime to `3` whenever the word has an odd step. -/
theorem not_three_dvd_den {v : List Bool} (hx : 1 ≤ ones v) : ¬ (3 : ℤ) ∣ den v := by
  intro h
  have hp3 : Prime (3:ℤ) := by norm_num
  have h3 : (3:ℤ) ∣ 3 ^ ones v := dvd_pow_self 3 (by omega)
  have h2 : (3:ℤ) ∣ 2 ^ v.length := by
    have hd := dvd_add h h3
    simpa [den] using hd
  have := hp3.dvd_of_dvd_pow h2
  norm_num at this

/-- **The Route-1 collapse.**  Integrality is rotation-invariant: `den v ∣ numer v` holds
for one rotation iff it holds for every rotation.  So gcd-ing the numerators over all
rotations returns exactly the information the single condition already carries, and any
attack hoping to harvest extra divisibility from the other cycle members is vacuous.

This is why Knight's high-cycle proof must use a *difference* of two members: differences
of unit multiples are not unit multiples.  Recorded as a killed route in
`FRONT-B-ROUTES.md`. -/
theorem dvd_numer_rot_iff {v : List Bool} (hv : v ≠ []) (hx : 1 ≤ ones v) :
    den v ∣ (numer v : ℤ) ↔ den v ∣ (numer (rot v) : ℤ) := by
  have hp3 : Prime (3:ℤ) := by norm_num
  have c2 : IsCoprime (den v) (2:ℤ) :=
    (Int.prime_two.coprime_iff_not_dvd.mpr (not_two_dvd_den hv)).symm
  have c3 : IsCoprime (den v) (3:ℤ) :=
    (hp3.coprime_iff_not_dvd.mpr (not_three_dvd_den hx)).symm
  obtain ⟨b, t, rfl⟩ : ∃ b t, v = b :: t := by
    cases v with
    | nil => exact absurd rfl hv
    | cons b t => exact ⟨b, t, rfl⟩
  cases b
  · -- even step: rotation exactly halves the numerator
    have key : (2:ℤ) * (numer (rot (false :: t)) : ℤ) = (numer (false :: t) : ℤ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) (two_mul_numer_rot_false t)
    constructor
    · intro hd
      refine c2.dvd_of_dvd_mul_left ?_
      rw [key]; exact hd
    · intro hd
      rw [← key]
      exact Dvd.dvd.mul_left hd 2
  · -- odd step: rotation triples it, modulo the denominator
    have key := two_mul_numer_rot_true t
    constructor
    · intro hd
      refine c2.dvd_of_dvd_mul_left ?_
      rw [key]
      exact dvd_add (Dvd.dvd.mul_left hd 3) dvd_rfl
    · intro hd
      have h2 : den (true :: t) ∣ (2:ℤ) * (numer (rot (true :: t)) : ℤ) :=
        Dvd.dvd.mul_left hd 2
      rw [key] at h2
      have h3 : den (true :: t) ∣ 3 * (numer (true :: t) : ℤ) := by
        have := dvd_sub h2 (dvd_refl (den (true :: t)))
        simpa using this
      exact c3.dvd_of_dvd_mul_left h3

/-! ## Cycle vocabulary

The three definitions the Front B board (`Threads.lean`) states its threads with.  They
live here so that `Powers.lean` can prove transfer lemmas about them without importing
the board. -/

/-- Maximal cyclic runs of odd steps, counted by their trailing edges.  (An all-`true` word
has zero edges and one circuit; it is excluded by `0 < den` anyway.) -/
def circuits (v : List Bool) : ℕ := (v.zip (rot v)).countP (fun p => p.1 && !p.2)

/-- The word encodes a cycle of positive **integers**. -/
def IntegerCycle (v : List Bool) : Prop :=
  v ≠ [] ∧ 1 ≤ ones v ∧ 0 < den v ∧ den v ∣ (numer v : ℤ)

/-- The word encodes the trivial cycle `{1, 2}` (or a rotation/repetition of it): its
member `numer v / den v` is `1` or `2`.  Both residues are needed: the trace of the
trivial accelerated cycle rooted at `2` is `[false, true]` with `numer = 2`, `den = 1`,
a perfectly good `IntegerCycle` whose member is `2`, not `1`.  (With the member-is-`1`
definition `FrontB` would be *refutably false* on that very word, and the dictionary
`noNontrivialCycle_iff_frontB` would be false with it.) -/
def IsTrivial (v : List Bool) : Prop :=
  (numer v : ℤ) = den v ∨ (numer v : ℤ) = 2 * den v

end CollatzMoonshot.FrontB
