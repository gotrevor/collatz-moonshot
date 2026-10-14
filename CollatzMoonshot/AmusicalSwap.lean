/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Amusical

/-!
# Block-swap maps keep every proved invariant (Conjecture G′, research §45)

The 2026-10-14 "gprime" agent built a family `F_L` of bounded-offset permutations that share
`U`'s even branch, hence `U`'s `E`-runs (MR II), and differ only in how each block's odd points are
matched to the block's non-multiples of 3.  `U` is the member with increasing block transitions.

**`ampSwap` (the family `F_1`).**  `U` with the targets of `4n + 1` and `4n + 3` optionally
swapped.  Every swap pattern is a permutation of `ℕ` (`ampSwap_bijective`), with `U`'s even
branch (`ampSwap_even`), offset `|4π(x) − 3x| ≤ 5` on odd `x` (`ampSwap_offset`), and no swaps
is `U` (`ampSwap_false`).

**`nc_iff_pse_parent` (CT1).**  On an injective sequence, "the first re-entry into `[0, x_s + D]`
lands above `x_s`" iff some later point within `D` above `x_s` is reached before anything smaller
than it: near-cycle starts are short edges of the Cartesian tree.

**`next_survivor_le`.**  A forward survivor `s'` below every later point of `s` satisfies
`2s' ≤ 3s + E` when `2π(s) ≤ 3s + E`.
-/

namespace CollatzMoonshot.Amusical

/-- `F_1`: `U` with the targets of `4n + 1` and `4n + 3` swapped when `c n = true`. -/
def ampSwap (c : ℕ → Bool) (x : ℕ) : ℕ :=
  if x % 2 = 0 then 3 * (x / 2)
  else if x % 4 = 1 then 3 * (x / 4) + (if c (x / 4) then 2 else 1)
  else 3 * (x / 4) + (if c (x / 4) then 1 else 2)

/-- **Target.**  Every swap pattern gives a permutation of `ℕ`. -/
theorem ampSwap_bijective (c : ℕ → Bool) : Function.Bijective (ampSwap c) := by
  have e0 : ∀ m, ampSwap c (2 * m) = 3 * m := fun m => by
    unfold ampSwap; rw [if_pos (by omega)]; omega
  have e1 : ∀ n, ampSwap c (4 * n + 1) = 3 * n + (if c n then 2 else 1) := fun n => by
    unfold ampSwap; rw [if_neg (by omega), if_pos (by omega), show (4 * n + 1) / 4 = n by omega]
  have e3 : ∀ n, ampSwap c (4 * n + 3) = 3 * n + (if c n then 1 else 2) := fun n => by
    unfold ampSwap; rw [if_neg (by omega), if_neg (by omega), show (4 * n + 3) / 4 = n by omega]
  let g : ℕ → ℕ := fun m =>
    if m % 3 = 0 then 2 * (m / 3)
    else if m % 3 = 1 then (if c (m / 3) then 4 * (m / 3) + 3 else 4 * (m / 3) + 1)
    else (if c (m / 3) then 4 * (m / 3) + 1 else 4 * (m / 3) + 3)
  have g0 : ∀ m, g (3 * m) = 2 * m := fun m => by
    simp only [g]; rw [if_pos (by omega)]; omega
  have g1 : ∀ n, g (3 * n + 1) = if c n then 4 * n + 3 else 4 * n + 1 := fun n => by
    simp only [g]; rw [if_neg (by omega), if_pos (by omega), show (3 * n + 1) / 3 = n by omega]
  have g2 : ∀ n, g (3 * n + 2) = if c n then 4 * n + 1 else 4 * n + 3 := fun n => by
    simp only [g]; rw [if_neg (by omega), if_neg (by omega), show (3 * n + 2) / 3 = n by omega]
  refine Function.bijective_iff_has_inverse.mpr ⟨g, fun x => ?_, fun m => ?_⟩
  · rcases (by omega : x % 2 = 0 ∨ x % 4 = 1 ∨ x % 4 = 3) with h | h | h
    · obtain ⟨m, rfl⟩ : ∃ m, x = 2 * m := ⟨x / 2, by omega⟩
      rw [e0, g0]
    · obtain ⟨n, rfl⟩ : ∃ n, x = 4 * n + 1 := ⟨x / 4, by omega⟩
      rw [e1]; cases h : c n <;> simp only [Bool.false_eq_true, if_false, if_true]
      · rw [g1, h]; rfl
      · rw [g2, h]; rfl
    · obtain ⟨n, rfl⟩ : ∃ n, x = 4 * n + 3 := ⟨x / 4, by omega⟩
      rw [e3]; cases h : c n <;> simp only [Bool.false_eq_true, if_false, if_true]
      · rw [g2, h]; rfl
      · rw [g1, h]; rfl
  · rcases (by omega : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2) with h | h | h
    · obtain ⟨k, rfl⟩ : ∃ k, m = 3 * k := ⟨m / 3, by omega⟩
      rw [g0, e0]
    · obtain ⟨n, rfl⟩ : ∃ n, m = 3 * n + 1 := ⟨m / 3, by omega⟩
      rw [g1]; cases h : c n <;> simp only [Bool.false_eq_true, if_false, if_true]
      · rw [e1, h]; rfl
      · rw [e3, h]; rfl
    · obtain ⟨n, rfl⟩ : ∃ n, m = 3 * n + 2 := ⟨m / 3, by omega⟩
      rw [g2]; cases h : c n <;> simp only [Bool.false_eq_true, if_false, if_true]
      · rw [e3, h]; rfl
      · rw [e1, h]; rfl

/-- **Target.**  The even branch is `U`'s. -/
theorem ampSwap_even (c : ℕ → Bool) (m : ℕ) : ampSwap c (2 * m) = 3 * m := by
  unfold ampSwap; rw [if_pos (by omega)]; omega

/-- **Target.**  Bounded offset on odd points. -/
theorem ampSwap_offset (c : ℕ → Bool) (x : ℕ) (hx : x % 2 = 1) :
    |4 * (ampSwap c x : ℤ) - 3 * x| ≤ 5 := by
  unfold ampSwap
  rw [abs_le]
  cases c (x / 4) <;> split_ifs <;> push_cast <;> constructor <;> omega

/-- **Target.**  No swaps is `U`. -/
theorem ampSwap_false (x : ℕ) : (ampSwap (fun _ => false) x : ℤ) = amusical (x : ℤ) := by
  unfold ampSwap amusical
  simp only [Bool.false_eq_true, if_false]
  split_ifs <;> push_cast <;> omega

/-- **Target (CT1).**  Near-cycle starts are the previous-smaller parents of points within `D`. -/
theorem nc_iff_pse_parent {x : ℤ → ℕ} (hx : Function.Injective x) (s : ℤ) (D : ℕ) :
    (∃ t, s < t ∧ x s < x t ∧ x t ≤ x s + D ∧ ∀ u, s < u → u < t → x s + D < x u) ↔
      (∃ t, s < t ∧ x s < x t ∧ x t ≤ x s + D ∧ ∀ u, s < u → u < t → x t < x u) := by
  have _ := hx
  constructor
  · rintro ⟨t, hst, h1, h2, h3⟩
    exact ⟨t, hst, h1, h2, fun u hsu hut => lt_of_le_of_lt h2 (h3 u hsu hut)⟩
  · rintro ⟨t, hst, h1, h2, h3⟩
    have hex : ∃ k : ℕ, 1 ≤ k ∧ x (s + k) ≤ x s + D :=
      ⟨(t - s).toNat, by omega, by rw [show s + ((t - s).toNat : ℤ) = t by omega]; exact h2⟩
    classical
    let k := Nat.find hex
    have hk : 1 ≤ k ∧ x (s + k) ≤ x s + D := Nat.find_spec hex
    have hkt : s + k ≤ t := by
      have := Nat.find_min' hex (m := (t - s).toNat)
        ⟨by omega, by rw [show s + ((t - s).toNat : ℤ) = t by omega]; exact h2⟩
      omega
    refine ⟨s + k, by omega, ?_, hk.2, fun u hsu hut => ?_⟩
    · rcases eq_or_lt_of_le hkt with heq | hlt
      · rw [heq]; exact h1
      · exact lt_trans h1 (h3 _ (by omega) hlt)
    · by_contra hu
      have := Nat.find_min hex (m := (u - s).toNat) (by omega)
      exact this ⟨by omega, by rw [show s + ((u - s).toNat : ℤ) = u by omega]; omega⟩

/-- **Target.**  The spine bound. -/
theorem next_survivor_le {π : ℕ → ℕ} {E s s' : ℕ} (hA : 2 * π s ≤ 3 * s + E)
    (hfut : ∀ k ≥ 1, s' ≤ π^[k] s) : 2 * s' ≤ 3 * s + E := by
  have := hfut 1 le_rfl
  rw [Function.iterate_one] at this
  omega

end CollatzMoonshot.Amusical
