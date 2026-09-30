/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Obstructions.ArithmeticLifts

/-!
# The positive approximate-fixed-vector family: exact coefficient theorem

This module discharges `PositiveApproximationFamily`, the coefficient half of
section 3 of `RESEARCH-2026-09-27-arithmetic-lifts-followup.md`.  The frozen
statement and all coefficient definitions live in `ArithmeticLifts`; nothing
there is edited.

The paper proof, made precise.  Write `napx K j = 3^j * 2^(K-j) - 1` for
`j ≤ K`, so `napx K 0 = 2^K - 1` is the odd base of the dyadic ray and
`napx K K = 3^K - 1` is the defect point.  Then:

* `napx` is strictly increasing on `[0, K]` (`napx_lt`);
* `napx K j` is odd for `j < K` (`napx_odd`) and `≡ 2 [MOD 3]` for `1 ≤ j`
  (`napx_mod_three`);
* the shortcut map sends `napx K j` to `napx K (j+1)` for `j < K`
  (`napx_step`).

So the support of `approxCoeff K` is the disjoint union of the dyadic ray
through `napx K 0` and the finite odd chain `napx K 1, …, napx K (K-1)`
(disjoint by parity), and the `transfer` preimage count at `n` is
`ray(n) + #{1 ≤ i ≤ K : n = napx K i}`, one term longer than `approxCoeff`
itself.  The difference is exactly the indicator of `n = napx K K = 3^K - 1`.

No norm, topology, or asymptotics is used.  The `List.range (n+1)` cutoff in
`rayCoeff` is shown to be lossless (`ray_any_iff`): `n = 2^j * base` with
`0 < base` forces `j < 2^j ≤ n`.
-/

namespace CollatzMoonshot.Obstructions.ArithmeticLifts

/-! ## The exponent chain `napx` -/

/-- The `j`-th point of the family: `napx K 0 = 2^K - 1` is the odd base and
`napx K K = 3^K - 1` is the single defect point. -/
def napx (K j : ℕ) : ℕ := 3 ^ j * 2 ^ (K - j) - 1

lemma napx_zero (K : ℕ) : napx K 0 = 2 ^ K - 1 := by simp [napx]

lemma napx_top (K : ℕ) : napx K K = 3 ^ K - 1 := by simp [napx]

lemma one_le_g (K j : ℕ) : 1 ≤ 3 ^ j * 2 ^ (K - j) :=
  Nat.one_le_iff_ne_zero.2 (by positivity)

/-- `g j * 2^j = 2^K * 3^j`, the identity that makes `g` easy to compare. -/
lemma g_mul_pow (K j : ℕ) (hj : j ≤ K) :
    (3 ^ j * 2 ^ (K - j)) * 2 ^ j = 2 ^ K * 3 ^ j := by
  have : 2 ^ (K - j) * 2 ^ j = 2 ^ K := by
    rw [← pow_add]
    congr 1
    omega
  calc (3 ^ j * 2 ^ (K - j)) * 2 ^ j = 3 ^ j * (2 ^ (K - j) * 2 ^ j) := by ring
    _ = 3 ^ j * 2 ^ K := by rw [this]
    _ = 2 ^ K * 3 ^ j := by ring

lemma g_lt (K i j : ℕ) (hij : j < i) (hi : i ≤ K) :
    3 ^ j * 2 ^ (K - j) < 3 ^ i * 2 ^ (K - i) := by
  have hj : j ≤ K := le_of_lt (lt_of_lt_of_le hij hi)
  have key : 3 ^ j * 2 ^ i < 3 ^ i * 2 ^ j := by
    have e1 : (3:ℕ) ^ j * 2 ^ i = (3 ^ j * 2 ^ j) * 2 ^ (i - j) := by
      rw [mul_assoc, ← pow_add]
      congr 2
      omega
    have e2 : (3:ℕ) ^ i * 2 ^ j = (3 ^ j * 2 ^ j) * 3 ^ (i - j) := by
      have : (3:ℕ) ^ i = 3 ^ j * 3 ^ (i - j) := by
        rw [← pow_add]; congr 1; omega
      rw [this]; ring
    have hlt : (2:ℕ) ^ (i - j) < 3 ^ (i - j) :=
      Nat.pow_lt_pow_left (by norm_num) (by omega)
    rw [e1, e2]
    exact mul_lt_mul_of_pos_left hlt (by positivity)
  have h1 : (3 ^ j * 2 ^ (K - j)) * (2 ^ j * 2 ^ i) = 2 ^ K * (3 ^ j * 2 ^ i) := by
    calc (3 ^ j * 2 ^ (K - j)) * (2 ^ j * 2 ^ i)
        = ((3 ^ j * 2 ^ (K - j)) * 2 ^ j) * 2 ^ i := by ring
      _ = (2 ^ K * 3 ^ j) * 2 ^ i := by rw [g_mul_pow K j hj]
      _ = 2 ^ K * (3 ^ j * 2 ^ i) := by ring
  have h2 : (3 ^ i * 2 ^ (K - i)) * (2 ^ j * 2 ^ i) = 2 ^ K * (3 ^ i * 2 ^ j) := by
    calc (3 ^ i * 2 ^ (K - i)) * (2 ^ j * 2 ^ i)
        = ((3 ^ i * 2 ^ (K - i)) * 2 ^ i) * 2 ^ j := by ring
      _ = (2 ^ K * 3 ^ i) * 2 ^ j := by rw [g_mul_pow K i hi]
      _ = 2 ^ K * (3 ^ i * 2 ^ j) := by ring
  have hpos : 0 < (2:ℕ) ^ j * 2 ^ i := by positivity
  refine Nat.lt_of_mul_lt_mul_right (a := 2 ^ j * 2 ^ i) ?_
  rw [h1, h2]
  exact mul_lt_mul_of_pos_left key (by positivity)

lemma napx_lt (K i j : ℕ) (hij : j < i) (hi : i ≤ K) : napx K j < napx K i := by
  have h := g_lt K i j hij hi
  have := one_le_g K j
  simp only [napx]
  omega

lemma napx_inj (K i j : ℕ) (hi : i ≤ K) (hj : j ≤ K) (h : napx K i = napx K j) :
    i = j := by
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact absurd h (Nat.ne_of_lt (napx_lt K j i hlt hj))
  · exact heq
  · exact absurd h.symm (Nat.ne_of_lt (napx_lt K i j hgt hi))

lemma napx_odd (K j : ℕ) (hj : j < K) : napx K j % 2 = 1 := by
  obtain ⟨t, ht⟩ : ∃ t, K - j = t + 1 := ⟨K - j - 1, by omega⟩
  have hg : 3 ^ j * 2 ^ (K - j) = 2 * (3 ^ j * 2 ^ t) := by
    rw [ht, pow_succ]; ring
  have hpos : 0 < 3 ^ j * 2 ^ t := by positivity
  simp only [napx, hg]
  omega

lemma napx_mod_three (K j : ℕ) (hj : 1 ≤ j) : napx K j % 3 = 2 := by
  obtain ⟨t, ht⟩ : ∃ t, j = t + 1 := ⟨j - 1, by omega⟩
  have hg : 3 ^ j * 2 ^ (K - j) = 3 * (3 ^ t * 2 ^ (K - j)) := by
    rw [ht, pow_succ]; ring
  have hpos : 0 < 3 ^ t * 2 ^ (K - j) := by positivity
  simp only [napx, hg]
  omega

/-- The shortcut step along the chain: `(3 * napx K j + 1)/2 = napx K (j+1)`. -/
lemma napx_step (K j : ℕ) (hj : j < K) : 3 * napx K j + 1 = 2 * napx K (j + 1) := by
  have ht : K - j = (K - (j + 1)) + 1 := by omega
  have hg : 3 ^ j * 2 ^ (K - j) = 2 * (3 ^ j * 2 ^ (K - (j + 1))) := by
    rw [ht, pow_succ]; ring
  have hg' : 3 ^ (j + 1) * 2 ^ (K - (j + 1)) = 3 * (3 ^ j * 2 ^ (K - (j + 1))) := by
    rw [pow_succ]; ring
  have hpos : 0 < 3 ^ j * 2 ^ (K - (j + 1)) := by positivity
  simp only [napx, hg, hg']
  omega


lemma two_pow_mul_even {i b : ℕ} (hi : i ≠ 0) : (2 ^ i * b) % 2 = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have h : (2:ℕ) ^ (k + 1) * b = 2 * (2 ^ k * b) := by rw [pow_succ]; ring
  rw [h]; omega

lemma half_of_two_pow_mul {i b n : ℕ} (hi : i ≠ 0) (h : 2 * n = 2 ^ i * b) :
    n = 2 ^ (i - 1) * b := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have h' : 2 * n = 2 * (2 ^ k * b) := by rw [h, pow_succ]; ring
  simp only [Nat.add_sub_cancel]
  omega

/-! ## Support predicates -/

/-- `n` lies on the dyadic ray through the odd base `2^K - 1`. -/
def RayAt (K n : ℕ) : Prop := ∃ j, n = 2 ^ j * (2 ^ K - 1)

/-- `n` is one of the interior chain points `napx K 1, …, napx K (K-1)`. -/
def FinAt (K n : ℕ) : Prop := ∃ j, 1 ≤ j ∧ j < K ∧ n = napx K j

/-- `n` is one of `napx K 1, …, napx K K`: the image chain, one point longer. -/
def FinAt' (K n : ℕ) : Prop := ∃ j, 1 ≤ j ∧ j ≤ K ∧ n = napx K j

lemma base_pos {K : ℕ} (hK : 1 ≤ K) : 0 < 2 ^ K - 1 := by
  have : (2:ℕ) ^ 1 ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hK
  simp at this; omega

lemma base_odd {K : ℕ} (hK : 1 ≤ K) : (2 ^ K - 1) % 2 = 1 := by
  have := napx_odd K 0 hK
  rwa [napx_zero] at this

/-! ## The `rayCoeff` cutoff is lossless -/

lemma ray_any_iff (base n : ℕ) (hb : 0 < base) :
    ((List.range (n + 1)).any (fun j => n == 2 ^ j * base)) = true ↔
      ∃ j, n = 2 ^ j * base := by
  simp only [List.any_eq_true, List.mem_range, beq_iff_eq]
  constructor
  · rintro ⟨j, -, hj⟩; exact ⟨j, hj⟩
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_, hj⟩
    have h1 : j < 2 ^ j := Nat.lt_two_pow_self
    have h2 : 2 ^ j ≤ n := by
      rw [hj]; exact Nat.le_mul_of_pos_right _ hb
    omega

lemma rayCoeff_eq_one {base n : ℕ} (hb : 0 < base) (h : ∃ j, n = 2 ^ j * base) :
    rayCoeff base n = 1 := by
  unfold rayCoeff
  rw [if_pos ((ray_any_iff base n hb).2 h)]

lemma rayCoeff_eq_zero {base n : ℕ} (h : ¬ ∃ j, n = 2 ^ j * base) :
    rayCoeff base n = 0 := by
  unfold rayCoeff
  rw [if_neg]
  intro hh
  simp only [List.any_eq_true, List.mem_range, beq_iff_eq] at hh
  obtain ⟨j, -, hj⟩ := hh
  exact h ⟨j, hj⟩

/-! ## The finite part of `approxCoeff` -/

lemma sumFin_eq_one {K n : ℕ} (h : FinAt K n) :
    (∑ j ∈ Finset.Ico 1 K, if n = 3 ^ j * 2 ^ (K - j) - 1 then 1 else 0) = (1 : ℚ) := by
  obtain ⟨j, hj1, hjK, hn⟩ := h
  simp only [napx] at hn
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_Ico.2 ⟨hj1, hjK⟩)]
  · rw [if_pos hn]
  · intro i hi hij
    rw [Finset.mem_Ico] at hi
    rw [if_neg]
    intro hni
    exact hij (napx_inj K i j (le_of_lt hi.2) (le_of_lt hjK) (by
      simp only [napx]; rw [← hni, ← hn]))

lemma sumFin_eq_zero {K n : ℕ} (h : ¬ FinAt K n) :
    (∑ j ∈ Finset.Ico 1 K, if n = 3 ^ j * 2 ^ (K - j) - 1 then 1 else 0) = (0 : ℚ) := by
  refine Finset.sum_eq_zero ?_
  intro i hi
  rw [Finset.mem_Ico] at hi
  rw [if_neg]
  intro hni
  exact h ⟨i, hi.1, hi.2, hni⟩

/-! ## `approxCoeff` as a disjoint indicator -/

lemma ray_finAt_disjoint {K n : ℕ} (_hK : 1 ≤ K) (hr : RayAt K n) (hf : FinAt K n) :
    False := by
  obtain ⟨j, hj1, hjK, hn⟩ := hf
  obtain ⟨i, hi⟩ := hr
  have hodd : n % 2 = 1 := by rw [hn]; exact napx_odd K j hjK
  have hi0 : i = 0 := by
    by_contra h
    have : n % 2 = 0 := by rw [hi]; exact two_pow_mul_even h
    omega
  rw [hi0, pow_zero, one_mul, ← napx_zero K] at hi
  have := napx_lt K j 0 hj1 (le_of_lt hjK)
  omega

lemma approxCoeff_eq_one_of_ray {K n : ℕ} (hK : 1 ≤ K) (hr : RayAt K n) :
    approxCoeff K n = 1 := by
  have hf : ¬ FinAt K n := fun h => ray_finAt_disjoint hK hr h
  unfold approxCoeff
  rw [rayCoeff_eq_one (base_pos hK) hr, sumFin_eq_zero hf]
  ring

lemma approxCoeff_eq_one_of_fin {K n : ℕ} (hK : 1 ≤ K) (hf : FinAt K n) :
    approxCoeff K n = 1 := by
  have hr : ¬ RayAt K n := fun h => ray_finAt_disjoint hK h hf
  unfold approxCoeff
  rw [rayCoeff_eq_zero hr, sumFin_eq_one hf]
  ring

lemma approxCoeff_eq_zero {K n : ℕ} (hr : ¬ RayAt K n) (hf : ¬ FinAt K n) :
    approxCoeff K n = 0 := by
  unfold approxCoeff
  rw [rayCoeff_eq_zero hr, sumFin_eq_zero hf]
  ring

/-! ## Behaviour of the support under the two shortcut preimages -/

lemma rayAt_two_mul {K n : ℕ} (hK : 1 ≤ K) : RayAt K (2 * n) ↔ RayAt K n := by
  constructor
  · rintro ⟨i, hi⟩
    have hbodd := base_odd hK
    have hi0 : i ≠ 0 := by
      rintro rfl
      rw [pow_zero, one_mul] at hi
      omega
    exact ⟨i - 1, half_of_two_pow_mul hi0 hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i + 1, by rw [hi, pow_succ]; ring⟩

lemma not_finAt_two_mul {K n : ℕ} : ¬ FinAt K (2 * n) := by
  rintro ⟨j, hj1, hjK, hn⟩
  have := napx_odd K j hjK
  omega

/-- The even preimage contributes exactly the ray indicator. -/
lemma approxCoeff_two_mul_eq_one {K n : ℕ} (hK : 1 ≤ K) (hr : RayAt K n) :
    approxCoeff K (2 * n) = 1 :=
  approxCoeff_eq_one_of_ray hK ((rayAt_two_mul hK).2 hr)

lemma approxCoeff_two_mul_eq_zero {K n : ℕ} (hK : 1 ≤ K) (hr : ¬ RayAt K n) :
    approxCoeff K (2 * n) = 0 :=
  approxCoeff_eq_zero (fun h => hr ((rayAt_two_mul hK).1 h)) not_finAt_two_mul

/-- Every point of the image chain is `2 mod 3`, so the odd preimage exists. -/
lemma finAt'_mod_three {K n : ℕ} (h : FinAt' K n) : n % 3 = 2 := by
  obtain ⟨j, hj1, -, hn⟩ := h
  rw [hn]; exact napx_mod_three K j hj1

/-- Odd preimage of `n` when `n % 3 = 2`. -/
lemma odd_preimage_spec {n : ℕ} (hn : 0 < n) (h3 : n % 3 = 2) :
    3 * ((2 * n - 1) / 3) = 2 * n - 1 ∧ 3 * ((2 * n - 1) / 3) + 1 = 2 * n := by
  have hdvd : 3 ∣ 2 * n - 1 := by omega
  obtain ⟨c, hc⟩ := hdvd
  rw [hc, Nat.mul_div_cancel_left _ (by norm_num)]
  omega

/-- The odd preimage carries the *image* chain `napx K 1, …, napx K K`. -/
lemma approxCoeff_odd_preimage_eq_one {K n : ℕ} (hK : 1 ≤ K) (hn : 0 < n)
    (h : FinAt' K n) : approxCoeff K ((2 * n - 1) / 3) = 1 := by
  obtain ⟨j, hj1, hjK, hnj⟩ := h
  set m := (2 * n - 1) / 3 with hm
  have h3 := finAt'_mod_three ⟨j, hj1, hjK, hnj⟩
  obtain ⟨-, hmspec⟩ := odd_preimage_spec hn h3
  rcases Nat.lt_or_ge 1 j with hj | hj
  · -- interior: predecessor is `napx K (j-1)` with `1 ≤ j-1 < K`
    have hstep : 3 * napx K (j - 1) + 1 = 2 * napx K j := by
      have := napx_step K (j - 1) (by omega)
      rwa [show j - 1 + 1 = j by omega] at this
    have : m = napx K (j - 1) := by omega
    exact approxCoeff_eq_one_of_fin hK ⟨j - 1, by omega, by omega, this⟩
  · -- j = 1: predecessor is the odd base of the ray
    have hj' : j = 1 := by omega
    subst hj'
    have hstep : 3 * napx K 0 + 1 = 2 * napx K 1 := napx_step K 0 hK
    have hmb : m = 2 ^ K - 1 := by rw [← napx_zero K]; omega
    exact approxCoeff_eq_one_of_ray hK ⟨0, by rw [hmb, pow_zero, one_mul]⟩

lemma approxCoeff_odd_preimage_eq_zero {K n : ℕ} (hK : 1 ≤ K) (hn : 0 < n)
    (h3 : n % 3 = 2) (h : ¬ FinAt' K n) : approxCoeff K ((2 * n - 1) / 3) = 0 := by
  set m := (2 * n - 1) / 3 with hm
  obtain ⟨-, hmspec⟩ := odd_preimage_spec hn h3
  refine approxCoeff_eq_zero ?_ ?_
  · rintro ⟨i, hi⟩
    -- `m` is odd, so `i = 0` and `m` is the base; then `n = napx K 1`
    have hmodd : m % 2 = 1 := by omega
    have hi0 : i = 0 := by
      by_contra hne
      have : m % 2 = 0 := by rw [hi]; exact two_pow_mul_even hne
      omega
    rw [hi0, pow_zero, one_mul, ← napx_zero K] at hi
    have hstep : 3 * napx K 0 + 1 = 2 * napx K 1 := napx_step K 0 hK
    exact h ⟨1, le_refl 1, hK, by omega⟩
  · rintro ⟨j, hj1, hjK, hmj⟩
    have hstep : 3 * napx K j + 1 = 2 * napx K (j + 1) := napx_step K j hjK
    exact h ⟨j + 1, by omega, by omega, by omega⟩

/-! ## Splitting the image chain off its last point -/

lemma finAt'_iff {K n : ℕ} (hK : 1 ≤ K) : FinAt' K n ↔ FinAt K n ∨ n = napx K K := by
  constructor
  · rintro ⟨j, hj1, hjK, hn⟩
    rcases Nat.lt_or_ge j K with h | h
    · exact Or.inl ⟨j, hj1, h, hn⟩
    · right; rw [hn, show j = K by omega]
  · rintro (⟨j, hj1, hjK, hn⟩ | hn)
    · exact ⟨j, hj1, le_of_lt hjK, hn⟩
    · exact ⟨K, hK, le_refl K, hn⟩

lemma finAt_ne_top {K n : ℕ} (_hK : 1 ≤ K) (h : FinAt K n) : n ≠ napx K K := by
  obtain ⟨j, hj1, hjK, hn⟩ := h
  have := napx_lt K K j hjK (le_refl K)
  omega

/-! ## The headline -/

/-- The explicit positive connected sparse family has exactly one coefficient
of transfer defect, at the endpoint of its growing odd prefix. -/
theorem positiveApproximationFamily : PositiveApproximationFamily := by
  intro K hK
  have hK1 : 1 ≤ K := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- coefficients are 0 or 1
    intro n
    by_cases hr : RayAt K n
    · exact Or.inr (approxCoeff_eq_one_of_ray hK1 hr)
    by_cases hf : FinAt K n
    · exact Or.inr (approxCoeff_eq_one_of_fin hK1 hf)
    · exact Or.inl (approxCoeff_eq_zero hr hf)
  · -- value one at the base
    exact approxCoeff_eq_one_of_ray hK1 ⟨0, by rw [pow_zero, one_mul]⟩
  · -- vanishing below the base
    intro n hn
    refine approxCoeff_eq_zero ?_ ?_
    · rintro ⟨i, hi⟩
      have : 2 ^ K - 1 ≤ 2 ^ i * (2 ^ K - 1) :=
        Nat.le_mul_of_pos_left _ (by positivity)
      omega
    · rintro ⟨j, hj1, hjK, hnj⟩
      have := napx_lt K j 0 hj1 (le_of_lt hjK)
      rw [napx_zero] at this
      omega
  · -- the one-point defect
    intro n hn
    have hnapxK : napx K K = 3 ^ K - 1 := napx_top K
    unfold transfer
    by_cases hf' : FinAt' K n
    · -- the odd preimage fires
      have h3 : n % 3 = 2 := finAt'_mod_three hf'
      rw [if_pos h3, approxCoeff_odd_preimage_eq_one hK1 hn hf']
      rcases (finAt'_iff hK1).1 hf' with hf | htop
      · -- interior chain point: no defect
        have hne : n ≠ 3 ^ K - 1 := by
          rw [← hnapxK]; exact finAt_ne_top hK1 hf
        rw [if_neg hne, approxCoeff_eq_one_of_fin hK1 hf]
        by_cases hr : RayAt K n
        · exact absurd hf (fun h => ray_finAt_disjoint hK1 hr h)
        · rw [approxCoeff_two_mul_eq_zero hK1 hr]; ring
      · -- the endpoint: defect one
        have heq : n = 3 ^ K - 1 := by rw [htop, hnapxK]
        rw [if_pos heq]
        have hfn : ¬ FinAt K n := fun h => finAt_ne_top hK1 h htop
        by_cases hr : RayAt K n
        · rw [approxCoeff_two_mul_eq_one hK1 hr, approxCoeff_eq_one_of_ray hK1 hr]
          ring
        · rw [approxCoeff_two_mul_eq_zero hK1 hr, approxCoeff_eq_zero hr hfn]
          ring
    · -- the odd preimage contributes nothing
      have hfn : ¬ FinAt K n := fun h => hf' ((finAt'_iff hK1).2 (Or.inl h))
      have hne : n ≠ 3 ^ K - 1 := by
        rw [← hnapxK]
        intro h
        exact hf' ((finAt'_iff hK1).2 (Or.inr h))
      rw [if_neg hne]
      have hsecond : (if n % 3 = 2 then approxCoeff K ((2 * n - 1) / 3) else 0) = 0 := by
        by_cases h3 : n % 3 = 2
        · rw [if_pos h3, approxCoeff_odd_preimage_eq_zero hK1 hn h3 hf']
        · rw [if_neg h3]
      rw [hsecond]
      by_cases hr : RayAt K n
      · rw [approxCoeff_two_mul_eq_one hK1 hr, approxCoeff_eq_one_of_ray hK1 hr]; ring
      · rw [approxCoeff_two_mul_eq_zero hK1 hr, approxCoeff_eq_zero hr hfn]; ring

-- Trust-base audit for the headline: no `sorry`, no new axiom.
/-- info: 'CollatzMoonshot.Obstructions.ArithmeticLifts.positiveApproximationFamily' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms positiveApproximationFamily

end CollatzMoonshot.Obstructions.ArithmeticLifts
