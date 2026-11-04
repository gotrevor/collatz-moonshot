/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.SliceFourierGeneral

/-!
# Fourier weights of a residue indicator on `ℤ/3^a` (2026-11-04)

The observable behind `BeyondWords.lean` is the centred indicator
`resInd K c y = 1[y ≡ c (mod 2^K)] − 2^{−K}`, read on least residues `y < 3^a`.  Its Fourier
coefficient at `ξ ≠ 0` is `3^{−a} e(−ξc/3^a)` times a geometric sum of ratio `e(−2^K ξ/3^a)`, so
`‖f̂ ξ‖ ≤ 3^{−a} / |sin(π (2^K ξ)/3^a)|`; at `ξ = 0` it is `T/3^a − 2^{−K}` with `T` the number of
`y < 3^a` in the class, within `3^{−a}` of zero.  Multiplication by the unit `2^K` permutes `ℤ/3^a`
and preserves divisibility by `3^k`, and `Σ_{u<N} 1/|sin(πu/N)| ≤ N·H_N`, so the layered weights
are `≤ 3^{−k} · 4(a+1)`: `layeredWeight_resInd`, uniformly in `K` and `c`.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB

/-! ## Sine harmonic bounds -/

/-- Half-angle factorisation `1 − e^{−2ix} = 2i sin x · e^{−ix}`. -/
theorem one_sub_exp_neg_two_mul_I (x : ℝ) :
    1 - Complex.exp (-(2 * x * Complex.I)) =
      (2 * Real.sin x : ℂ) * Complex.I * Complex.exp (-(x * Complex.I)) := by
  rw [show -(2 * x * Complex.I) = ((-2 * x : ℝ) : ℂ) * Complex.I by
    push_cast
    ring]
  rw [show -(x * Complex.I) = ((-x : ℝ) : ℂ) * Complex.I by
    push_cast
    ring]
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  simp_rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [show -2 * x = -(2 * x) by ring]
  simp only [Real.cos_neg, Real.sin_neg]
  rw [Real.cos_two_mul, Real.sin_two_mul]
  have hs := Complex.sin_sq_add_cos_sq (x : ℂ)
  push_cast
  linear_combination (-2 : ℂ) * hs + 2 * Complex.sin (x : ℂ) ^ 2 * Complex.I_sq

/-- The geometric-sum denominator `‖1 − e(−η/3^a)‖ = 2|sin(π η/3^a)|`. -/
theorem norm_one_sub_stdAddChar (a : ℕ) (η : ZMod (3 ^ a)) :
    ‖1 - ZMod.stdAddChar (-η)‖ =
      2 * |Real.sin (Real.pi * η.val / 3 ^ a)| := by
  rw [stdAddChar_neg_eq_exp]
  let x : ℝ := Real.pi * η.val / 3 ^ a
  have he : -(2 * Real.pi * Complex.I * (η.val : ℂ) / (3 ^ a : ℂ)) =
      -(2 * x * Complex.I) := by
    dsimp [x]
    push_cast
    ring
  rw [he, one_sub_exp_neg_two_mul_I]
  rw [norm_mul, norm_mul, Complex.norm_I, mul_one]
  rw [show (2 : ℂ) * (Real.sin x : ℂ) = ((2 * Real.sin x : ℝ) : ℂ) by norm_num]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
  have hn : ‖Complex.exp (-(x * Complex.I))‖ = 1 := by
    rw [show -(x * Complex.I) = ((-x : ℝ) : ℂ) * Complex.I by
      push_cast
      ring]
    exact Complex.norm_exp_ofReal_mul_I (-x)
  rw [hn, mul_one]
  simp [x]

/-- Jordan at the nearer endpoint: `1/|sin(πu/N)| ≤ (N/2)(1/u + 1/(N−u))` for `u < N`
(both sides read with `1/0 = 0`). -/
theorem inv_abs_sin_le (N u : ℕ) (hu : u < N) :
    1 / |Real.sin (Real.pi * u / N)| ≤
      (N : ℝ) / 2 * (1 / (u : ℝ) + 1 / ((N - u : ℕ) : ℝ)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNu : 0 < N - u := by omega
  have hNuR : (0 : ℝ) < ((N - u : ℕ) : ℝ) := by exact_mod_cast hNu
  rcases Nat.eq_zero_or_pos u with rfl | hupos
  · simp only [Nat.cast_zero, mul_zero, zero_div, Real.sin_zero, abs_zero, div_zero, zero_add]
    positivity
  have huR : (0 : ℝ) < u := by exact_mod_cast hupos
  have hsub : ((N - u : ℕ) : ℝ) = (N : ℝ) - u := by
    rw [Nat.cast_sub hu.le]
  -- the Jordan bound at whichever of `u`, `N - u` is the smaller
  have key : ∀ v : ℕ, 0 < v → 2 * v ≤ N →
      |Real.sin (Real.pi * v / N)| ≥ 2 * v / N := by
    intro v hv hvN
    have hvR : (0 : ℝ) < v := by exact_mod_cast hv
    have hvNR : 2 * (v : ℝ) ≤ N := by exact_mod_cast hvN
    have hx0 : 0 ≤ Real.pi * v / N := by positivity
    have hx1 : Real.pi * v / N ≤ Real.pi / 2 := by
      rw [div_le_div_iff₀ hNpos (by norm_num)]
      nlinarith [Real.pi_pos]
    have hj := Real.mul_le_sin hx0 hx1
    have hsinpos : 0 ≤ Real.sin (Real.pi * v / N) := le_trans (by positivity) hj
    rw [abs_of_nonneg hsinpos]
    calc 2 * (v : ℝ) / N = 2 / Real.pi * (Real.pi * v / N) := by
          field_simp
      _ ≤ _ := hj
  by_cases h2 : 2 * u ≤ N
  · have hk := key u hupos h2
    have hpos : 0 < 2 * (u : ℝ) / N := by positivity
    calc 1 / |Real.sin (Real.pi * u / N)| ≤ 1 / (2 * (u : ℝ) / N) :=
          one_div_le_one_div_of_le hpos hk
      _ = (N : ℝ) / 2 * (1 / (u : ℝ)) := by field_simp
      _ ≤ _ := by
          gcongr
          exact le_add_of_nonneg_right (by positivity)
  · have h2' : 2 * (N - u) ≤ N := by omega
    have hk := key (N - u) hNu h2'
    have hrefl : Real.sin (Real.pi * ((N - u : ℕ) : ℝ) / N) = Real.sin (Real.pi * u / N) := by
      rw [hsub, ← Real.sin_pi_sub]
      congr 1
      field_simp
      ring
    rw [hrefl] at hk
    have hpos : 0 < 2 * ((N - u : ℕ) : ℝ) / N := by positivity
    calc 1 / |Real.sin (Real.pi * u / N)| ≤ 1 / (2 * ((N - u : ℕ) : ℝ) / N) :=
          one_div_le_one_div_of_le hpos hk
      _ = (N : ℝ) / 2 * (1 / ((N - u : ℕ) : ℝ)) := by field_simp
      _ ≤ _ := by
          gcongr
          exact le_add_of_nonneg_left (by positivity)

/-- `Σ_{u<N} 1/u ≤ H_N`, the `u = 0` term being `1/0 = 0`. -/
theorem sum_range_inv_le_harmonic (N : ℕ) :
    ∑ u ∈ Finset.range N, (1 : ℝ) / u ≤ (harmonic N : ℝ) := by
  rcases N with _ | n
  · simp
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, div_zero, add_zero]
  have hh : (harmonic n : ℝ) ≤ harmonic (n + 1) := by
    rw [harmonic_succ]
    push_cast
    linarith [show (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹ by positivity]
  refine le_trans (le_of_eq ?_) hh
  simp [harmonic, Nat.cast_add, Nat.cast_one, div_eq_mul_inv]

/-- `Σ_{u<N} 1/(N−u) = H_N` by reflection. -/
theorem sum_range_inv_sub_eq_harmonic (N : ℕ) :
    ∑ u ∈ Finset.range N, (1 : ℝ) / ((N - u : ℕ) : ℝ) = (harmonic N : ℝ) := by
  rw [← Finset.sum_range_reflect]
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  apply Finset.sum_congr rfl
  intro u hu
  have hu' := Finset.mem_range.mp hu
  rw [show N - (N - 1 - u) = u + 1 by omega]
  simp

/-- **Sine harmonic bound.**  `Σ_{u<N} 1/|sin(πu/N)| ≤ N · H_N`. -/
theorem sum_inv_abs_sin_le (N : ℕ) :
    ∑ u ∈ Finset.range N, 1 / |Real.sin (Real.pi * u / N)| ≤ N * (harmonic N : ℝ) := by
  calc ∑ u ∈ Finset.range N, 1 / |Real.sin (Real.pi * u / N)| ≤
        ∑ u ∈ Finset.range N, (N : ℝ) / 2 * (1 / (u : ℝ) + 1 / ((N - u : ℕ) : ℝ)) :=
        Finset.sum_le_sum fun u hu => inv_abs_sin_le N u (Finset.mem_range.mp hu)
    _ = (N : ℝ) / 2 * (∑ u ∈ Finset.range N, (1 : ℝ) / u +
          ∑ u ∈ Finset.range N, (1 : ℝ) / ((N - u : ℕ) : ℝ)) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (N : ℝ) / 2 * ((harmonic N : ℝ) + harmonic N) := by
        rw [sum_range_inv_sub_eq_harmonic]
        gcongr
        exact sum_range_inv_le_harmonic N
    _ = N * (harmonic N : ℝ) := by ring

end CollatzMoonshot.Conjugacy
