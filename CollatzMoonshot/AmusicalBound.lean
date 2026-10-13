/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalWindow

/-!
# Orbit minima of the amusical permutation have upper density below `1/20`

`windowMinDensity 200` bounds the upper density of orbit minima by `δ₂₀₀ = fwdSurv 200 *
bwdSurv 200 = 0.0498876…`, just under `1/20` (the conjectured density is `0.049780`).  The
pattern sums have `2^200` terms, so `windowDensity_two_hundred_lt` needs a dynamic-programming
form of `fwdSurv` and `bwdSurv` (state: step and number of marked steps) proved equal to the
definitions, then an exact rational evaluation.  Plan: `KICKOFF-2026-10-13-amusical-bound.md`.
-/

namespace CollatzMoonshot.Amusical

open Classical in
/-- Split a sum over words by the last letter.  Unlike direct reduction of a
`Fintype` of functions, this identity scales inductively and is the entry point
for connecting the word sums to the lattice rows. -/
theorem sum_bool_snoc {n : ℕ} (f : (Fin (n + 1) → Bool) → ℚ) :
    ∑ w, f w = ∑ b : Bool, ∑ u : Fin n → Bool, f (Fin.snoc u b) := by
  refine ((Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (n + 1) => Bool))
    (fun x => f (Fin.snoc x.2 x.1)) f (fun _ => rfl)).symm).trans ?_
  exact Fintype.sum_prod_type _

/-! ## A linear-size lattice computation

The rows below store integer numerators.  At time `t`, entry `o` is the total
weight of surviving prefixes with exactly `o` marked letters.  Forward letters
both have weight one (the common denominator is `2^t`); backward unmarked and
marked letters have weights one and two (common denominator `3^t`).  Passing
the preceding entry explicitly makes one row step linear rather than rebuilding
the preceding row at every output coordinate during kernel reduction. -/

def fwdLatticeStep (t o prev : ℕ) : List ℕ → List ℕ
  | [] => []
  | x :: xs =>
      (if 2 ^ (t + 1 + o) < 3 ^ (t + 1) then x + prev else 0) ::
        fwdLatticeStep t (o + 1) x xs

def bwdLatticeStep (t o prev : ℕ) : List ℕ → List ℕ
  | [] => []
  | x :: xs =>
      (if 3 ^ (t + 1) < 2 ^ (t + 1 + o) then x + 2 * prev else 0) ::
        bwdLatticeStep t (o + 1) x xs

def fwdLatticeRow : ℕ → List ℕ
  | 0 => [1]
  | t + 1 => fwdLatticeStep t 0 0 (fwdLatticeRow t ++ [0])

def bwdLatticeRow : ℕ → List ℕ
  | 0 => [1]
  | t + 1 => bwdLatticeStep t 0 0 (bwdLatticeRow t ++ [0])

def fwdLatticeNum (L : ℕ) : ℕ := (fwdLatticeRow L).sum
def bwdLatticeNum (L : ℕ) : ℕ := (bwdLatticeRow L).sum

theorem fwdLatticeStep_length (t o prev : ℕ) (xs : List ℕ) :
    (fwdLatticeStep t o prev xs).length = xs.length := by
  induction xs generalizing o prev with
  | nil => rfl
  | cons x xs ih => simp [fwdLatticeStep, ih]

theorem bwdLatticeStep_length (t o prev : ℕ) (xs : List ℕ) :
    (bwdLatticeStep t o prev xs).length = xs.length := by
  induction xs generalizing o prev with
  | nil => rfl
  | cons x xs ih => simp [bwdLatticeStep, ih]

/-- A coordinate of a forward lattice step only uses the two adjacent
coordinates of the preceding row.  The explicit `prev` argument is the
coordinate immediately to the left of the input list. -/
theorem fwdLatticeStep_getD (t o prev k : ℕ) (xs : List ℕ) (hk : k < xs.length) :
    (fwdLatticeStep t o prev xs).getD k 0 =
      if 2 ^ (t + 1 + (o + k)) < 3 ^ (t + 1) then
        xs.getD k 0 + if k = 0 then prev else xs.getD (k - 1) 0
      else 0 := by
  induction xs generalizing o prev k with
  | nil => simp at hk
  | cons x xs ih =>
      cases k with
      | zero => simp [fwdLatticeStep]
      | succ k =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at hk
          rw [fwdLatticeStep, List.getD_cons_succ, ih (o := o + 1) (prev := x) k hk]
          cases k <;> simp [Nat.add_left_comm, Nat.add_comm]

/-- Backward lattice coordinates satisfy the analogous adjacent-coordinate
recurrence, with weight two on a newly marked letter. -/
theorem bwdLatticeStep_getD (t o prev k : ℕ) (xs : List ℕ) (hk : k < xs.length) :
    (bwdLatticeStep t o prev xs).getD k 0 =
      if 3 ^ (t + 1) < 2 ^ (t + 1 + (o + k)) then
        xs.getD k 0 + 2 * (if k = 0 then prev else xs.getD (k - 1) 0)
      else 0 := by
  induction xs generalizing o prev k with
  | nil => simp at hk
  | cons x xs ih =>
      cases k with
      | zero => simp [bwdLatticeStep]
      | succ k =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at hk
          rw [bwdLatticeStep, List.getD_cons_succ, ih (o := o + 1) (prev := x) k hk]
          cases k <;> simp [Nat.add_left_comm, Nat.add_comm]

private theorem getD_append_zero (xs : List ℕ) (k : ℕ) (hk : k ≤ xs.length) :
    (xs ++ [0]).getD k 0 = xs.getD k 0 := by
  rcases hk.lt_or_eq with hk | rfl
  · exact List.getD_append xs [0] 0 k hk
  · simp

/-- Each computed row has exactly one coordinate for every possible mark count. -/
theorem fwdLatticeRow_length (t : ℕ) : (fwdLatticeRow t).length = t + 1 := by
  induction t with
  | zero => rfl
  | succ t ih => simp [fwdLatticeRow, fwdLatticeStep_length, ih]

/-- Each computed row has exactly one coordinate for every possible mark count. -/
theorem bwdLatticeRow_length (t : ℕ) : (bwdLatticeRow t).length = t + 1 := by
  induction t with
  | zero => rfl
  | succ t ih => simp [bwdLatticeRow, bwdLatticeStep_length, ih]

/-- Coordinate form of the forward row recurrence. -/
theorem fwdLatticeRow_succ_getD (t o : ℕ) (ho : o ≤ t + 1) :
    (fwdLatticeRow (t + 1)).getD o 0 =
      if 2 ^ (t + 1 + o) < 3 ^ (t + 1) then
        (fwdLatticeRow t).getD o 0 +
          if o = 0 then 0 else (fwdLatticeRow t).getD (o - 1) 0
      else 0 := by
  rw [fwdLatticeRow, fwdLatticeStep_getD]
  · rw [getD_append_zero _ o]
    · by_cases h : o = 0
      · simp [h]
      · have hp : o - 1 ≤ (fwdLatticeRow t).length := by
          rw [fwdLatticeRow_length]
          omega
        rw [getD_append_zero _ _ hp]
        simp
    · simpa [fwdLatticeRow_length] using ho
  · simpa [fwdLatticeRow_length] using Nat.lt_succ_of_le ho

/-- Coordinate form of the backward row recurrence. -/
theorem bwdLatticeRow_succ_getD (t o : ℕ) (ho : o ≤ t + 1) :
    (bwdLatticeRow (t + 1)).getD o 0 =
      if 3 ^ (t + 1) < 2 ^ (t + 1 + o) then
        (bwdLatticeRow t).getD o 0 +
          2 * (if o = 0 then 0 else (bwdLatticeRow t).getD (o - 1) 0)
      else 0 := by
  rw [bwdLatticeRow, bwdLatticeStep_getD]
  · rw [getD_append_zero _ o]
    · by_cases h : o = 0
      · simp [h]
      · have hp : o - 1 ≤ (bwdLatticeRow t).length := by
          rw [bwdLatticeRow_length]
          omega
        rw [getD_append_zero _ _ hp]
        simp
    · simpa [bwdLatticeRow_length] using ho
  · simpa [bwdLatticeRow_length] using Nat.lt_succ_of_le ho

/-- The lattice recurrence reproduces the four small window-density controls. -/
theorem latticeDensity_values :
    fwdLatticeNum 1 * bwdLatticeNum 1 * 3 = 2 ^ 1 * 3 ^ 1 ∧
      fwdLatticeNum 2 * bwdLatticeNum 2 * 9 = 2 * (2 ^ 2 * 3 ^ 2) ∧
      fwdLatticeNum 3 * bwdLatticeNum 3 * 6 = 2 ^ 3 * 3 ^ 3 ∧
      fwdLatticeNum 4 * bwdLatticeNum 4 * 27 = 4 * (2 ^ 4 * 3 ^ 4) := by
  decide +kernel

/-- Exact kernel evaluation of the 200-step lattice, still separated from the
word-sum definitions by the combinatorial bridge below. -/
theorem latticeDensity_two_hundred_lt :
    20 * fwdLatticeNum 200 * bwdLatticeNum 200 < 2 ^ 200 * 3 ^ 200 := by
  decide +kernel

/-- **Target (treadmill).**  `δ₂₀₀ < 1/20`.  Exact value `0.04988761510…`
(`scripts/amusical/window.py`-style lattice computation, 2026-10-13). -/
theorem windowDensity_two_hundred_lt : fwdSurv 200 * bwdSurv 200 < 1 / 20 := by
  sorry

open Classical in
/-- **Orbit minima have upper density below `1/20`**: eventually fewer than `X/20` of
`0, …, X-1` are orbit minima. -/
theorem orbitMin_density_lt_one_twentieth : ∀ᶠ X : ℕ in Filter.atTop,
    (((Finset.range X).filter fun m : ℕ => IsOrbitMin m).card : ℝ) / X < 1 / 20 := by
  set δ : ℝ := ((fwdSurv 200 * bwdSurv 200 : ℚ) : ℝ)
  have hδ : δ < 1 / 20 := by
    have h := windowDensity_two_hundred_lt
    have : ((fwdSurv 200 * bwdSurv 200 : ℚ) : ℝ) < ((1 / 20 : ℚ) : ℝ) := Rat.cast_lt.2 h
    simpa [δ] using this
  filter_upwards [orbitMin_density_le 200 (by linarith : (0 : ℝ) < (1 / 20 - δ) / 2)] with X hX
  linarith

end CollatzMoonshot.Amusical
