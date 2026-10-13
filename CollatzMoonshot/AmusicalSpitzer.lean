/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalConstant
import CollatzMoonshot.CycleDiophantine

/-!
# The window densities converge to `minimaConstant` (Sparre Andersen)

Target for a treadmill (`KICKOFF-2026-10-13-amusical-spitzer.md`): `windowDensityLimit`, after
which `orbitMin_density_le_minimaConstant` is unconditional.  The duality half is a termwise
identity: forward survival at time `k` and backward non-survival use the same binomial index set
`{o : 2^(k+o) < 3^k}`, with weights `C(k,o) 2^-k · 2^(k+o) 3^-k = C(k,o) 2^o 3^-k` on both sides.
The real content is Sparre Andersen's theorem for the two multiplicative walks.
-/

namespace CollatzMoonshot.Amusical

/-! ## Haar duality at one fixed time -/

/-- The probability that the forward multiplicative walk is at or below its start after `k`
steps.  There are `choose k o` words with `o` steps of type `×3/4`, each of mass `2⁻ᵏ`. -/
noncomputable def fwdNonposTerm (k : ℕ) : ℝ :=
  ∑ o ∈ Finset.range (k + 1),
    if 3 ^ k < 2 ^ (k + o) then (Nat.choose k o : ℝ) / 2 ^ k else 0

/-- The probability that the backward multiplicative walk is at or below its start after `k`
steps.  Haar tilting changes the forward mass `choose k o / 2^k` into
`choose k o * 2^o / 3^k` on the complementary side of the no-tie cut. -/
noncomputable def bwdNonposTerm (k : ℕ) : ℝ :=
  ∑ o ∈ Finset.range (k + 1),
    if 2 ^ (k + o) < 3 ^ k then (Nat.choose k o : ℝ) * 2 ^ o / 3 ^ k else 0

/-- The forward probability of finishing strictly above the start after `k` steps. -/
noncomputable def fwdPosTerm (k : ℕ) : ℝ :=
  ∑ o ∈ Finset.range (k + 1),
    if 2 ^ (k + o) < 3 ^ k then (Nat.choose k o : ℝ) / 2 ^ k else 0

/-- The backward probability of finishing strictly above the start after `k` steps. -/
noncomputable def bwdPosTerm (k : ℕ) : ℝ :=
  ∑ o ∈ Finset.range (k + 1),
    if 3 ^ k < 2 ^ (k + o) then (Nat.choose k o : ℝ) * 2 ^ o / 3 ^ k else 0

/-- No endpoint of either multiplicative walk is tied with its start at positive time. -/
theorem walk_endpoint_ne (k o : ℕ) (hk : 0 < k) :
    (2 : ℕ) ^ (k + o) ≠ 3 ^ k := by
  exact Ne.symm (three_pow_ne_two_pow (a := k) (b := k + o) hk)

/-- **Haar duality, termwise form.**  At each positive time, the Spitzer contribution splits
exactly into the forward and backward probabilities of finishing at or below the start. -/
theorem spitzerTerm_eq_fwdNonposTerm_add_bwdNonposTerm (k : ℕ) (hk : 0 < k) :
    spitzerTerm k = fwdNonposTerm k + bwdNonposTerm k := by
  rw [spitzerTerm, fwdNonposTerm, bwdNonposTerm, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro o ho
  have hone : (0 : ℝ) < 2 ^ k := by positivity
  have hthree : (0 : ℝ) < 3 ^ k := by positivity
  have hneNat : (2 : ℕ) ^ (k + o) ≠ 3 ^ k := walk_endpoint_ne k o hk
  rcases lt_or_gt_of_ne hneNat with hlt | hgt
  · rw [if_neg (by exact_mod_cast (not_lt_of_ge hlt.le)), if_pos (by exact_mod_cast hlt)]
    rw [min_eq_right (by
      apply (div_le_one hthree).2
      exact_mod_cast hlt.le)]
    field_simp
    ring
  · rw [if_pos (by exact_mod_cast hgt), if_neg (by exact_mod_cast (not_lt_of_ge hgt.le))]
    rw [min_eq_left (by
      apply (one_le_div hthree).2
      exact_mod_cast hgt.le)]
    ring

/-- At positive time, the forward endpoint is either strictly positive or nonpositive, and the
two binomial masses sum to one. -/
theorem fwdNonposTerm_add_fwdPosTerm (k : ℕ) (hk : 0 < k) :
    fwdNonposTerm k + fwdPosTerm k = 1 := by
  rw [fwdNonposTerm, fwdPosTerm, ← Finset.sum_add_distrib]
  calc
    _ = ∑ o ∈ Finset.range (k + 1), (Nat.choose k o : ℝ) / 2 ^ k := by
      apply Finset.sum_congr rfl
      intro o ho
      have hne : (2 : ℕ) ^ (k + o) ≠ 3 ^ k := walk_endpoint_ne k o hk
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [if_neg (by exact_mod_cast (not_lt_of_ge hlt.le)), if_pos (by exact_mod_cast hlt)]
        ring
      · rw [if_pos (by exact_mod_cast hgt), if_neg (by exact_mod_cast (not_lt_of_ge hgt.le))]
        ring
    _ = (∑ o ∈ Finset.range (k + 1), (Nat.choose k o : ℝ)) / 2 ^ k := by
      rw [Finset.sum_div]
    _ = 1 := by
      rw [← Nat.cast_sum, Nat.sum_range_choose]
      norm_num

/-- At positive time, the backward endpoint is either strictly positive or nonpositive, and the
two tilted binomial masses sum to one. -/
theorem bwdNonposTerm_add_bwdPosTerm (k : ℕ) (hk : 0 < k) :
    bwdNonposTerm k + bwdPosTerm k = 1 := by
  rw [bwdNonposTerm, bwdPosTerm, ← Finset.sum_add_distrib]
  calc
    _ = ∑ o ∈ Finset.range (k + 1), (Nat.choose k o : ℝ) * 2 ^ o / 3 ^ k := by
      apply Finset.sum_congr rfl
      intro o ho
      have hne : (2 : ℕ) ^ (k + o) ≠ 3 ^ k := walk_endpoint_ne k o hk
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [if_pos (by exact_mod_cast hlt), if_neg (by exact_mod_cast (not_lt_of_ge hlt.le))]
        ring
      · rw [if_neg (by exact_mod_cast (not_lt_of_ge hgt.le)), if_pos (by exact_mod_cast hgt)]
        ring
    _ = (∑ o ∈ Finset.range (k + 1), (Nat.choose k o : ℝ) * 2 ^ o) / 3 ^ k := by
      rw [Finset.sum_div]
    _ = 1 := by
      have hbinom := add_pow (2 : ℝ) 1 k
      simp only [one_pow, mul_one] at hbinom
      rw [add_comm] at hbinom
      have htotal : (3 : ℝ) ^ k =
          ∑ o ∈ Finset.range (k + 1), (Nat.choose k o : ℝ) * 2 ^ o := by
        norm_num [mul_comm] at hbinom ⊢
        exact hbinom
      rw [← htotal]
      norm_num

/-- **Target (treadmill).**  `fwdSurv L * bwdSurv L → minimaConstant`. -/
theorem windowDensityLimit : WindowDensityLimit := by
  sorry

open Classical in
/-- Orbit minima have upper density at most `minimaConstant ≈ 0.049780`. -/
theorem orbitMin_density_le_minimaConstant' {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in Filter.atTop,
      (((Finset.range X).filter fun m : ℕ => IsOrbitMin m).card : ℝ) / X ≤ minimaConstant + ε :=
  orbitMin_density_le_minimaConstant windowDensityLimit hε

end CollatzMoonshot.Amusical
