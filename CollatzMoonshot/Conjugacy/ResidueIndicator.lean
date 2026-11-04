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

/-! ## The centred residue indicator -/

/-- Standard additive characters take values on the unit circle. -/
theorem norm_stdAddChar {N : ℕ} [NeZero N] (x : ZMod N) : ‖ZMod.stdAddChar x‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

/-- The centred residue indicator `1[y ≡ c (mod 2^K)] − 2^{−K}`, read on least residues. -/
noncomputable def resInd (K c : ℕ) (y : ℕ) : ℂ :=
  (if y % 2 ^ K = c then 1 else 0) - ((2 : ℂ) ^ K)⁻¹

/-- The number of `y < 3^a` with `y % 2^K = c` (for `c < 2^K`): `⌈(3^a − c)/2^K⌉`. -/
def resCount (a K c : ℕ) : ℕ := (3 ^ a + 2 ^ K - 1 - c) / 2 ^ K

/-- `t` indexes a member `c + 2^K t` of the class below `3^a` iff `t < resCount a K c`. -/
theorem lt_resCount_iff {a K c t : ℕ} (hc : c < 2 ^ K) :
    t < resCount a K c ↔ c + 2 ^ K * t < 3 ^ a := by
  have hQ : 0 < 2 ^ K := by positivity
  unfold resCount
  rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hQ,
    show (t + 1) * 2 ^ K = 2 ^ K * t + 2 ^ K by ring]
  generalize 2 ^ K * t = m
  omega

/-- The class `{n < 3^a : n ≡ c (2^K)}` is the arithmetic progression `c + 2^K t`,
`t < resCount a K c`. -/
theorem sum_filter_mod_eq {a K c : ℕ} (hc : c < 2 ^ K) (f : ℕ → ℂ) :
    ∑ n ∈ (Finset.range (3 ^ a)).filter (fun n => n % 2 ^ K = c), f n =
      ∑ t ∈ Finset.range (resCount a K c), f (c + 2 ^ K * t) := by
  have hQ : 0 < 2 ^ K := by positivity
  symm
  apply Finset.sum_nbij' (fun t => c + 2 ^ K * t) (fun n => n / 2 ^ K)
  · intro t ht
    have ht' : t < resCount a K c := Finset.mem_range.mp ht
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ((lt_resCount_iff hc).mp ht'), ?_⟩
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
  · intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hlt := Finset.mem_range.mp hn'.1
    refine Finset.mem_range.mpr ((lt_resCount_iff hc).mpr ?_)
    have := Nat.mod_add_div n (2 ^ K)
    rw [hn'.2] at this
    omega
  · intro t ht
    rw [Nat.add_mul_div_left c t hQ, Nat.div_eq_of_lt hc, zero_add]
  · intro n hn
    have hn' := Finset.mem_filter.mp hn
    have := Nat.mod_add_div n (2 ^ K)
    rw [hn'.2] at this
    exact this
  · intro t ht
    rfl

/-- `e(−ξn/3^a)` is the `n`-th power of `e(−ξ/3^a)`. -/
theorem stdAddChar_neg_mul_natCast (a n : ℕ) (ξ : ZMod (3 ^ a)) :
    ZMod.stdAddChar (-(ξ * (n : ZMod (3 ^ a)))) = ZMod.stdAddChar (-ξ) ^ n := by
  rw [show -(ξ * (n : ZMod (3 ^ a))) = n • (-ξ) by
    simp only [nsmul_eq_mul]
    ring]
  rw [AddChar.map_nsmul_eq_pow]

/-- The indicator transform is a sum along the progression of the class. -/
theorem sum_ind_mul_stdAddChar {a K c : ℕ} (hc : c < 2 ^ K) (ξ : ZMod (3 ^ a)) :
    ∑ y : ZMod (3 ^ a), (if y.val % 2 ^ K = c then (1 : ℂ) else 0) *
        ZMod.stdAddChar (-(ξ * y)) =
      ∑ t ∈ Finset.range (resCount a K c), ZMod.stdAddChar (-ξ) ^ (c + 2 ^ K * t) := by
  rw [sum_zmod_eq_sum_range]
  rw [← sum_filter_mod_eq hc, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  rw [ZMod.val_natCast_of_lt (Finset.mem_range.mp hn), stdAddChar_neg_mul_natCast]
  split_ifs <;> simp

/-- Orthogonality: the complete character sum vanishes off `ξ = 0`. -/
theorem sum_stdAddChar_neg_mul (a : ℕ) (ξ : ZMod (3 ^ a)) :
    ∑ y : ZMod (3 ^ a), ZMod.stdAddChar (-(ξ * y)) =
      if ξ = 0 then ((3 ^ a : ℕ) : ℂ) else 0 := by
  have h := AddChar.sum_mulShift (-ξ) (ZMod.isPrimitive_stdAddChar (3 ^ a))
  simp_rw [show ∀ y : ZMod (3 ^ a), -(ξ * y) = y * -ξ from fun y => by ring]
  rw [h]
  simp [ZMod.card]

/-- Closed form of the Fourier coefficient of the centred indicator. -/
theorem resFourier_resInd {a K c : ℕ} (hc : c < 2 ^ K) (ξ : ZMod (3 ^ a)) :
    resFourier a (resInd K c) ξ = ((3 ^ a : ℕ) : ℂ)⁻¹ *
      ((∑ t ∈ Finset.range (resCount a K c), ZMod.stdAddChar (-ξ) ^ (c + 2 ^ K * t)) -
        ((2 : ℂ) ^ K)⁻¹ * if ξ = 0 then ((3 ^ a : ℕ) : ℂ) else 0) := by
  unfold resFourier resInd
  congr 1
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  rw [sum_ind_mul_stdAddChar hc, ← Finset.mul_sum, sum_stdAddChar_neg_mul]

/-- The class has `resCount ≈ 3^a/2^K` members: `|2^K · resCount − 3^a| ≤ 2^K`. -/
theorem resCount_bounds {a K c : ℕ} (hc : c < 2 ^ K) :
    3 ^ a ≤ c + 2 ^ K * resCount a K c ∧ 2 ^ K * resCount a K c ≤ 3 ^ a + 2 ^ K := by
  constructor
  · by_contra h
    exact lt_irrefl _ ((lt_resCount_iff (t := resCount a K c) hc).mpr (by omega))
  · rcases Nat.eq_zero_or_eq_succ_pred (resCount a K c) with h | h
    · rw [h, mul_zero]
      exact Nat.zero_le _
    · have hs := (lt_resCount_iff (a := a) (t := (resCount a K c).pred) hc).mp (by omega)
      rw [h, show 2 ^ K * ((resCount a K c).pred + 1) =
        2 ^ K * (resCount a K c).pred + 2 ^ K by ring]
      omega

/-- At the zero frequency the centring leaves at most `3^{−a}`. -/
theorem norm_resFourier_resInd_zero {a K c : ℕ} (hc : c < 2 ^ K) :
    ‖resFourier a (resInd K c) 0‖ ≤ ((3 : ℝ) ^ a)⁻¹ := by
  rw [resFourier_resInd hc, if_pos rfl]
  simp only [neg_zero, AddChar.map_zero_eq_one, one_pow, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one]
  obtain ⟨h1, h2⟩ := resCount_bounds (a := a) hc
  set T := resCount a K c
  have h1R : ((3 : ℝ) ^ a) ≤ c + (2 : ℝ) ^ K * T := by exact_mod_cast h1
  have h2R : (2 : ℝ) ^ K * T ≤ 3 ^ a + 2 ^ K := by exact_mod_cast h2
  have hcR : (c : ℝ) < 2 ^ K := by exact_mod_cast hc
  have hQ : (0 : ℝ) < 2 ^ K := by positivity
  have heq : ((((3 ^ a : ℕ) : ℂ))⁻¹ * ((T : ℂ) - ((2 : ℂ) ^ K)⁻¹ * ((3 ^ a : ℕ) : ℂ))) =
      ((((3 : ℝ) ^ a)⁻¹ * (((2 : ℝ) ^ K)⁻¹ * ((2 : ℝ) ^ K * T - 3 ^ a)) : ℝ) : ℂ) := by
    push_cast
    field_simp
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity),
    abs_mul, abs_of_pos (by positivity)]
  apply mul_le_of_le_one_right (by positivity)
  rw [inv_mul_le_iff₀ hQ, mul_one, abs_le]
  constructor <;> linarith

/-- `2^K` is a unit mod `3^a`, so it preserves nonzero frequencies. -/
theorem natCast_two_pow_mul_ne_zero {a K : ℕ} {ξ : ZMod (3 ^ a)} (hξ : ξ ≠ 0) :
    ((2 ^ K : ℕ) : ZMod (3 ^ a)) * ξ ≠ 0 := by
  have hcop : Nat.Coprime (2 ^ K) (3 ^ a) := Nat.Coprime.pow K a (by decide)
  have hu : IsUnit ((2 ^ K : ℕ) : ZMod (3 ^ a)) := by
    rw [← ZMod.coe_unitOfCoprime (2 ^ K) hcop]
    exact Units.isUnit _
  rwa [Ne, hu.mul_right_eq_zero]

/-- At `ξ ≠ 0` the coefficient is a geometric sum of ratio `e(−2^K ξ/3^a)`:
`‖f̂ ξ‖ ≤ 3^{−a}/|sin(π (2^K ξ)/3^a)|`. -/
theorem norm_resFourier_resInd_ne_zero {a K c : ℕ} (hc : c < 2 ^ K) {ξ : ZMod (3 ^ a)}
    (hξ : ξ ≠ 0) :
    ‖resFourier a (resInd K c) ξ‖ ≤ ((3 : ℝ) ^ a)⁻¹ *
      (1 / |Real.sin (Real.pi * (((2 ^ K : ℕ) : ZMod (3 ^ a)) * ξ).val / 3 ^ a)|) := by
  rw [resFourier_resInd hc, if_neg hξ, mul_zero, sub_zero]
  set η := ((2 ^ K : ℕ) : ZMod (3 ^ a)) * ξ with hηdef
  have hη : η ≠ 0 := natCast_two_pow_mul_ne_zero hξ
  set ω := ZMod.stdAddChar (-η)
  set ψ := ZMod.stdAddChar (-ξ)
  have hpow (t : ℕ) : ψ ^ (c + 2 ^ K * t) = ψ ^ c * ω ^ t := by
    rw [pow_add, pow_mul]
    congr 2
    rw [← stdAddChar_neg_mul_natCast a (2 ^ K) ξ, mul_comm]
  simp_rw [hpow]
  rw [← Finset.mul_sum]
  have hvpos : 0 < η.val := Nat.pos_of_ne_zero (fun h => hη ((ZMod.val_eq_zero η).mp h))
  have hvlt : η.val < 3 ^ a := ZMod.val_lt η
  have hvltR : (η.val : ℝ) < 3 ^ a := by exact_mod_cast hvlt
  have hsinpos : 0 < Real.sin (Real.pi * η.val / 3 ^ a) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · have : (0 : ℝ) < η.val := by exact_mod_cast hvpos
      positivity
    · rw [div_lt_iff₀ (by positivity)]
      nlinarith [Real.pi_pos]
  have hden : ‖1 - ω‖ = 2 * |Real.sin (Real.pi * η.val / 3 ^ a)| :=
    norm_one_sub_stdAddChar a η
  have hω1 : ω ≠ 1 := by
    intro h
    rw [h, sub_self, norm_zero] at hden
    rw [abs_of_pos hsinpos] at hden
    linarith
  have hgeom : ‖∑ t ∈ Finset.range (resCount a K c), ω ^ t‖ ≤ 2 / ‖1 - ω‖ := by
    rw [geom_sum_eq hω1, norm_div, norm_sub_rev ω 1]
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    calc ‖ω ^ resCount a K c - 1‖ ≤ ‖ω ^ resCount a K c‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, norm_stdAddChar, one_pow, norm_one]; norm_num
  rw [norm_mul, norm_mul, norm_pow, norm_stdAddChar, one_pow, one_mul]
  have hM : ‖(((3 ^ a : ℕ) : ℂ))⁻¹‖ = ((3 : ℝ) ^ a)⁻¹ := by
    rw [norm_inv]
    norm_num
  rw [hM]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc ‖∑ t ∈ Finset.range (resCount a K c), ω ^ t‖ ≤ 2 / ‖1 - ω‖ := hgeom
    _ = 1 / |Real.sin (Real.pi * η.val / 3 ^ a)| := by
      rw [hden]
      field_simp

/-- The pointwise weight bound, valid at every frequency (`1/0 = 0` at `ξ = 0`). -/
theorem norm_resFourier_resInd_le {a K c : ℕ} (hc : c < 2 ^ K) (ξ : ZMod (3 ^ a)) :
    ‖resFourier a (resInd K c) ξ‖ ≤ ((3 : ℝ) ^ a)⁻¹ *
      (1 / |Real.sin (Real.pi * (((2 ^ K : ℕ) : ZMod (3 ^ a)) * ξ).val / 3 ^ a)| + 1) := by
  have hx : 0 ≤ 1 / |Real.sin (Real.pi * (((2 ^ K : ℕ) : ZMod (3 ^ a)) * ξ).val / 3 ^ a)| := by
    positivity
  by_cases hξ : ξ = 0
  · subst hξ
    calc _ ≤ ((3 : ℝ) ^ a)⁻¹ := norm_resFourier_resInd_zero hc
      _ ≤ _ := le_mul_of_one_le_right (by positivity) (by linarith)
  · calc _ ≤ _ := norm_resFourier_resInd_ne_zero hc hξ
      _ ≤ _ := by gcongr; linarith

/-- `H_{3^b} ≤ 1 + 2b`. -/
theorem harmonic_three_pow_le (b : ℕ) : (harmonic (3 ^ b) : ℝ) ≤ 1 + 2 * b := by
  have hh := harmonic_le_one_add_log (3 ^ b)
  have hlog3 : Real.log (3 : ℝ) ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
    norm_num at this ⊢
    exact this
  have hlogpow : Real.log ((3 ^ b : ℕ) : ℝ) ≤ 2 * b := by
    rw [show (((3 ^ b : ℕ) : ℝ)) = (3 : ℝ) ^ b by norm_num, Real.log_pow]
    have hb : (0 : ℝ) ≤ b := by positivity
    nlinarith
  linarith

/-- Multiplication by `2^K` preserves divisibility of the least residue by `3^k`, `k ≤ a`. -/
theorem dvd_val_two_pow_mul_iff {a K k : ℕ} (hk : k ≤ a) (ξ : ZMod (3 ^ a)) :
    3 ^ k ∣ (((2 ^ K : ℕ) : ZMod (3 ^ a)) * ξ).val ↔ 3 ^ k ∣ ξ.val := by
  rw [ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod,
    Nat.dvd_mod_iff (Nat.pow_dvd_pow 3 hk)]
  exact (Nat.Coprime.pow k K (by decide : Nat.Coprime 3 2)).dvd_mul_left

/-- The sine weights on frequencies divisible by `3^k`, plus one per frequency, total at most
`3^{a−k}(H_{3^{a−k}} + 1)`. -/
theorem sum_dvd_inv_abs_sin_le (a k : ℕ) (hk : k ≤ a) :
    (∑ η : ZMod (3 ^ a), if 3 ^ k ∣ η.val then
        (1 / |Real.sin (Real.pi * η.val / 3 ^ a)| + 1) else 0) ≤
      ((3 ^ (a - k) : ℕ) : ℝ) * ((harmonic (3 ^ (a - k)) : ℝ) + 1) := by
  let d := 3 ^ k
  let N := 3 ^ (a - k)
  have hd : 0 < d := by positivity
  have hpow : 3 ^ a = d * N := by
    dsimp [d, N]
    rw [← pow_add, Nat.add_sub_of_le hk]
  have hpowR : (3 : ℝ) ^ a = (d : ℝ) * N := by exact_mod_cast hpow
  rw [sum_zmod_eq_sum_range]
  rw [show (∑ n ∈ Finset.range (3 ^ a), if 3 ^ k ∣ (n : ZMod (3 ^ a)).val then
        (1 / |Real.sin (Real.pi * ((n : ZMod (3 ^ a)).val : ℕ) / 3 ^ a)| + 1) else 0) =
      ∑ n ∈ Finset.range (3 ^ a), if d ∣ n then
        (1 / |Real.sin (Real.pi * (n : ℝ) / 3 ^ a)| + 1) else 0 by
    apply Finset.sum_congr rfl
    intro n hn
    rw [ZMod.val_natCast_of_lt (Finset.mem_range.mp hn)]]
  rw [← Finset.sum_filter, hpow, sum_filter_range_dvd_eq _ d N hd]
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have harg (u : ℕ) : Real.pi * ((d * u : ℕ) : ℝ) / 3 ^ a = Real.pi * u / N := by
    rw [hpowR]
    push_cast
    field_simp
  simp_rw [harg]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hs := sum_inv_abs_sin_le N
  show _ ≤ (N : ℝ) * ((harmonic N : ℝ) + 1)
  linarith

/-- **Layered weight of the residue indicator.**  For every `K` and `c < 2^K`, the centred
indicator has layered weight `4(a+1)` — the same as parity, uniformly in `K` and `c`. -/
theorem layeredWeight_resInd {K c : ℕ} (hc : c < 2 ^ K) (a : ℕ) :
    LayeredWeight a (resInd K c) (1 * (4 * (a + 1))) := by
  intro k hk
  have hcop : Nat.Coprime (2 ^ K) (3 ^ a) := Nat.Coprime.pow K a (by decide)
  let u := ZMod.unitOfCoprime (2 ^ K) hcop
  let G : ZMod (3 ^ a) → ℝ := fun η => if 3 ^ k ∣ η.val then
    ((3 : ℝ) ^ a)⁻¹ * (1 / |Real.sin (Real.pi * η.val / 3 ^ a)| + 1) else 0
  have hstep1 : (∑ ξ : ZMod (3 ^ a),
      if 3 ^ k ∣ ξ.val then ‖resFourier a (resInd K c) ξ‖ else 0) ≤
      ∑ ξ : ZMod (3 ^ a), G ((Units.mulLeft u) ξ) := by
    apply Finset.sum_le_sum
    intro ξ _
    simp only [G, Units.mulLeft_apply, u, ZMod.coe_unitOfCoprime, dvd_val_two_pow_mul_iff hk]
    split_ifs
    · exact norm_resFourier_resInd_le hc ξ
    · exact le_rfl
  have hstep2 : (∑ ξ : ZMod (3 ^ a), G ((Units.mulLeft u) ξ)) = ∑ η : ZMod (3 ^ a), G η :=
    Equiv.sum_comp (Units.mulLeft u) G
  have hstep3 : (∑ η : ZMod (3 ^ a), G η) = ((3 : ℝ) ^ a)⁻¹ *
      ∑ η : ZMod (3 ^ a), if 3 ^ k ∣ η.val then
        (1 / |Real.sin (Real.pi * η.val / 3 ^ a)| + 1) else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro η _
    simp only [G]
    split_ifs <;> simp
  have hH := harmonic_three_pow_le (a - k)
  have hsub : ((a - k : ℕ) : ℝ) ≤ a := by exact_mod_cast Nat.sub_le a k
  have hpowR : (3 : ℝ) ^ a = (3 : ℝ) ^ k * 3 ^ (a - k) := by
    rw [← pow_add, Nat.add_sub_of_le hk]
  calc _ ≤ _ := hstep1
    _ = _ := hstep2
    _ = _ := hstep3
    _ ≤ ((3 : ℝ) ^ a)⁻¹ *
          (((3 ^ (a - k) : ℕ) : ℝ) * ((harmonic (3 ^ (a - k)) : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (sum_dvd_inv_abs_sin_le a k hk) (by positivity)
    _ = ((3 : ℝ) ^ k)⁻¹ * ((harmonic (3 ^ (a - k)) : ℝ) + 1) := by
        rw [hpowR]
        push_cast
        field_simp
    _ ≤ ((3 : ℝ) ^ k)⁻¹ * (1 * (4 * (a + 1))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith

end CollatzMoonshot.Conjugacy
