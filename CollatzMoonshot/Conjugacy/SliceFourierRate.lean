/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.SliceFourierGeneral

/-!
# The slice-Fourier pipeline with its rate kept (2026-11-04)

`SliceFourier.lean` runs the C1 pipeline with the exponent `A = 2` of `SliceCharDecay` hard-wired
(`exists_norm_sliceChar_pow_le`), which is all a fixed observable needs.  To sum the central-slice
bound over a polynomially growing family of observables (the `2^K ≤ j^N` residues of
`BeyondWordsLinear.lean`) the rate must be kept: this file is the same argument at an arbitrary
natural exponent `n`.

* `exists_norm_sliceChar_pow_le_rate`: low-valuation frequencies decay like `2^n C j^{−n}` plus
  the geometric sub-slice tail.
* `exists_norm_levelSum_le_rate`: the generic central-slice bound, at exponent `n`.
* `logMajorant`, `tendsto_logMajorant`: the central-slice majorant at exponent `N + 2`, multiplied
  by `j^N`, still tends to `0`.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB

/-- **Low-valuation slice characters at exponent `n`.**  The sibling of
`exists_norm_sliceChar_pow_le` with `SliceCharDecay` used at `A = n` instead of `A = 2`. -/
theorem exists_norm_sliceChar_pow_le_rate (h : SliceCharDecay) (n : ℕ) (hn : 1 ≤ n) :
    ∃ C > (0 : ℝ), ∀ j a k u : ℕ, 128 ≤ j → j ≤ 4 * a → a ≤ 11 * j / 20 →
      4096 * k ≤ j → ¬3 ∣ u →
      ‖sliceChar j a (3 ^ k * u)‖ ≤
        (2 ^ n * C / (j : ℝ) ^ n +
          (j : ℝ) * ((7 : ℝ) / 8) ^ (j / 16 - j / 32)) * j.choose a := by
  obtain ⟨C, hCpos, hC⟩ := h n (by exact_mod_cast hn)
  have hrpow (x : ℕ) (hx : 0 < x) : ((x : ℝ)) ^ (-(n : ℝ)) = ((x : ℝ) ^ n)⁻¹ := by
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
  refine ⟨C, hCpos, fun j a k u hj hja haj hjk hu => ?_⟩
  have hjpos : 0 < j := by omega
  have hjRpos : (0 : ℝ) < j := by exact_mod_cast hjpos
  by_cases hkzero : k = 0
  · subst k
    simp only [pow_zero, one_mul]
    have hd := hC j a u (by omega) (by omega) (by omega) hu
    rw [card_levelSet_eq_choose, hrpow j hjpos] at hd
    have h2n : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    have hjn : (0 : ℝ) < (j : ℝ) ^ n := by positivity
    calc
      ‖sliceChar j a u‖ ≤ C * ((j : ℝ) ^ n)⁻¹ * j.choose a := hd
      _ ≤ (2 ^ n * C / (j : ℝ) ^ n) * j.choose a := by
        rw [div_eq_mul_inv]
        gcongr
        nlinarith
      _ ≤ (2 ^ n * C / (j : ℝ) ^ n +
            (j : ℝ) * ((7 : ℝ) / 8) ^ (j / 16 - j / 32)) * j.choose a := by
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (by positivity)
  · have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hkzero
    have hka : k ≤ a := by omega
    have hE : 0 ≤ 2 ^ n * C / (j : ℝ) ^ n := by positivity
    have hgood (t : ℕ) (ht : t ∈ Finset.range j) (htm : t < j / 16) :
        ‖sliceChar (j - 1 - t) (a - k) u‖ ≤
          (2 ^ n * C / (j : ℝ) ^ n) * (levelSet (j - 1 - t) (a - k)).card := by
      have htj : t < j := Finset.mem_range.mp ht
      have hj' : 1 ≤ j - 1 - t := by omega
      have hlower : j - 1 - t ≤ 5 * (a - k) := by omega
      have hupper : 5 * (a - k) ≤ 3 * (j - 1 - t) := by omega
      have hd := hC (j - 1 - t) (a - k) u hj' hlower hupper hu
      rw [hrpow _ (by omega)] at hd
      have hhalfNat : j ≤ 2 * (j - 1 - t) := by omega
      have hhalf : (j : ℝ) / 2 ≤ (j - 1 - t : ℕ) := by
        exact (div_le_iff₀' (by norm_num : (0 : ℝ) < 2)).2 (by exact_mod_cast hhalfNat)
      have hpow : ((j : ℝ) / 2) ^ n ≤ ((j - 1 - t : ℕ) : ℝ) ^ n :=
        pow_le_pow_left₀ (by positivity) hhalf n
      have hinv : (((j - 1 - t : ℕ) : ℝ) ^ n)⁻¹ ≤ 2 ^ n / (j : ℝ) ^ n := by
        calc
          (((j - 1 - t : ℕ) : ℝ) ^ n)⁻¹ ≤ (((j : ℝ) / 2) ^ n)⁻¹ :=
            (inv_le_inv₀ (by positivity) (by positivity)).2 hpow
          _ = 2 ^ n / (j : ℝ) ^ n := by
            rw [div_pow]
            field_simp
      have hcard : (0 : ℝ) ≤ (levelSet (j - 1 - t) (a - k)).card := by positivity
      calc
        ‖sliceChar (j - 1 - t) (a - k) u‖ ≤
            C * (((j - 1 - t : ℕ) : ℝ) ^ n)⁻¹ * (levelSet (j - 1 - t) (a - k)).card := hd
        _ ≤ C * (2 ^ n / (j : ℝ) ^ n) * (levelSet (j - 1 - t) (a - k)).card := by
          gcongr
        _ = (2 ^ n * C / (j : ℝ) ^ n) * (levelSet (j - 1 - t) (a - k)).card := by ring
    have hmain := norm_sliceChar_pow_le_good_add_tail j a k u (j / 16)
      (2 ^ n * C / (j : ℝ) ^ n) hE hk hka hgood
    have htail := subslice_tail_real_le j a k (by omega) hjk hja hk hka
    calc
      ‖sliceChar j a (3 ^ k * u)‖ ≤
          (2 ^ n * C / (j : ℝ) ^ n) * j.choose a +
            subsliceTail j a k (j / 16) := hmain
      _ ≤ (2 ^ n * C / (j : ℝ) ^ n) * j.choose a +
            ((j : ℝ) * ((7 : ℝ) / 8) ^ (j / 16 - j / 32)) * j.choose a := by
        gcongr
      _ = (2 ^ n * C / (j : ℝ) ^ n +
            (j : ℝ) * ((7 : ℝ) / 8) ^ (j / 16 - j / 32)) * j.choose a := by ring

/-- **Generic central-slice bound at exponent `n`.**  The sibling of `exists_norm_levelSum_le`
with the low-frequency rate `2^n C j^{−n}` of `exists_norm_sliceChar_pow_le_rate`. -/
theorem exists_norm_levelSum_le_rate (h : SliceCharDecay) (n : ℕ) (hn : 1 ≤ n) :
    ∃ C > (0 : ℝ), ∀ j a : ℕ, 4096 ≤ j → j ≤ 4 * a → a ≤ 11 * j / 20 →
      ∀ (f : ℕ → ℂ) (B : ℝ), LayeredWeight a f (B * (4 * (a + 1))) →
      ‖∑ r ∈ levelSet j a, f (tstep^[j] r)‖ ≤
        B * (((2 ^ n * C / (j : ℝ) ^ n +
            (j : ℝ) * ((7 : ℝ) / 8) ^ (j / 16 - j / 32)) * (4 * (a + 1)) +
          ((3 : ℝ) ^ (j / 4096))⁻¹ * (4 * (a + 1))) * (levelSet j a).card) := by
  obtain ⟨C, hCpos, hlow⟩ := exists_norm_sliceChar_pow_le_rate h n hn
  refine ⟨C, hCpos, fun j a hj hja haj f B hf => ?_⟩
  let K := j / 4096
  let E := 2 ^ n * C / (j : ℝ) ^ n +
    (j : ℝ) * ((7 : ℝ) / 8) ^ (j / 16 - j / 32)
  let g := resFourier a f
  have hKa : K ≤ a := by dsimp [K]; omega
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hlowξ (ξ : ZMod (3 ^ a)) (hξ : ¬3 ^ K ∣ ξ.val) :
      ‖sliceChar j a ξ.val‖ ≤ E * (levelSet j a).card := by
    have hξ0 : ξ.val ≠ 0 := by
      intro hz
      apply hξ
      rw [hz]
      exact dvd_zero _
    let k := padicValNat 3 ξ.val
    let u := ξ.val.divMaxPow 3
    have hku : 3 ^ k * u = ξ.val := by
      exact Nat.pow_padicValNat_mul_divMaxPow 3 ξ.val
    have hu : ¬3 ∣ u := by
      exact Nat.not_dvd_divMaxPow (by norm_num) hξ0
    have hkK : k < K := by
      by_contra hnot
      apply hξ
      exact (Nat.pow_dvd_pow 3 (Nat.le_of_not_gt hnot)).trans pow_padicValNat_dvd
    have hjk : 4096 * k ≤ j := by
      dsimp [K] at hkK
      omega
    have hb := hlow j a k u (by omega) hja haj hjk hu
    rw [hku] at hb
    rw [card_levelSet_eq_choose]
    simpa [E] using hb
  have hpoint (ξ : ZMod (3 ^ a)) :
      ‖g ξ * sliceChar j a ξ.val‖ ≤
        E * (levelSet j a).card * ‖g ξ‖ +
          if 3 ^ K ∣ ξ.val then (levelSet j a).card * ‖g ξ‖ else 0 := by
    rw [norm_mul]
    by_cases hξ : 3 ^ K ∣ ξ.val
    · rw [if_pos hξ]
      have ht := norm_sliceChar_le_card j a ξ.val
      have hg : 0 ≤ ‖g ξ‖ := norm_nonneg _
      have hc : (0 : ℝ) ≤ (levelSet j a).card := by positivity
      have hmain : ‖g ξ‖ * ‖sliceChar j a ξ.val‖ ≤
          ‖g ξ‖ * (levelSet j a).card :=
        mul_le_mul_of_nonneg_left ht hg
      nlinarith [mul_nonneg hE (mul_nonneg hc hg)]
    · rw [if_neg hξ]
      have hb := hlowξ ξ hξ
      calc
        ‖g ξ‖ * ‖sliceChar j a ξ.val‖ ≤
            ‖g ξ‖ * (E * (levelSet j a).card) :=
          mul_le_mul_of_nonneg_left hb (norm_nonneg _)
        _ = E * (levelSet j a).card * ‖g ξ‖ + 0 := by ring
  have hsum :
      ‖∑ r ∈ levelSet j a, f (tstep^[j] r)‖ ≤
        E * (levelSet j a).card * (∑ ξ : ZMod (3 ^ a), ‖g ξ‖) +
          (levelSet j a).card *
            (∑ ξ : ZMod (3 ^ a), if 3 ^ K ∣ ξ.val then ‖g ξ‖ else 0) := by
    calc
      ‖∑ r ∈ levelSet j a, f (tstep^[j] r)‖ =
          ‖∑ ξ : ZMod (3 ^ a), g ξ * sliceChar j a ξ.val‖ := by
        rw [sum_levelSet_eq_fourier_slice]
      _ ≤ ∑ ξ : ZMod (3 ^ a), ‖g ξ * sliceChar j a ξ.val‖ :=
        norm_sum_le _ _
      _ ≤ ∑ ξ : ZMod (3 ^ a),
          (E * (levelSet j a).card * ‖g ξ‖ +
            if 3 ^ K ∣ ξ.val then (levelSet j a).card * ‖g ξ‖ else 0) := by
        exact Finset.sum_le_sum fun ξ _ => hpoint ξ
      _ = E * (levelSet j a).card * (∑ ξ : ZMod (3 ^ a), ‖g ξ‖) +
          (levelSet j a).card *
            (∑ ξ : ZMod (3 ^ a), if 3 ^ K ∣ ξ.val then ‖g ξ‖ else 0) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro ξ hξ
        split_ifs <;> ring
  have hall : (∑ ξ : ZMod (3 ^ a), ‖g ξ‖) ≤ B * (4 * (a + 1)) := by
    have h0 := hf 0 (Nat.zero_le a)
    simpa using h0
  have hhigh := hf K hKa
  have hcard : (0 : ℝ) ≤ (levelSet j a).card := by positivity
  calc
    ‖∑ r ∈ levelSet j a, f (tstep^[j] r)‖ ≤
        E * (levelSet j a).card * (∑ ξ : ZMod (3 ^ a), ‖g ξ‖) +
          (levelSet j a).card *
            (∑ ξ : ZMod (3 ^ a), if 3 ^ K ∣ ξ.val then ‖g ξ‖ else 0) := hsum
    _ ≤ E * (levelSet j a).card * (B * (4 * (a + 1))) +
          (levelSet j a).card * (((3 : ℝ) ^ K)⁻¹ * (B * (4 * (a + 1)))) := by
      gcongr
    _ = B * ((E * (4 * (a + 1)) + ((3 : ℝ) ^ K)⁻¹ * (4 * (a + 1))) *
          (levelSet j a).card) := by ring

/-- The central-slice majorant at exponent `N + 2`, inflated by the polynomial factor `j^N`. -/
noncomputable def logMajorant (C : ℝ) (N j : ℕ) : ℝ :=
  (j : ℝ) ^ N * ((2 ^ (N + 2) * C / (j : ℝ) ^ (N + 2) +
      (j : ℝ) * ((7 : ℝ) / 8) ^ (j / 16 - j / 32)) * (4 * (j + 1)) +
    ((3 : ℝ) ^ (j / 4096))⁻¹ * (4 * (j + 1)))

/-- **The inflated majorant still vanishes.**  The rational part loses `j^N` against `j^{N+2}`;
the two geometric parts absorb any polynomial. -/
theorem tendsto_logMajorant (C : ℝ) (N : ℕ) :
    Tendsto (logMajorant C N) atTop (𝓝 0) := by
  let r : ℕ → ℕ := fun j => j / 16 - j / 32
  let K : ℕ → ℕ := fun j => j / 4096
  have hr : Tendsto r atTop atTop := by
    rw [tendsto_atTop]
    intro b
    rw [eventually_atTop]
    refine ⟨64 * b + 64, fun j hj => ?_⟩
    dsimp [r]
    omega
  have hK : Tendsto K atTop atTop := by
    rw [tendsto_atTop]
    intro b
    rw [eventually_atTop]
    refine ⟨4096 * b + 4096, fun j hj => ?_⟩
    dsimp [K]
    omega
  have hone : Tendsto (fun j : ℕ => (1 : ℝ) / j) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hrat : Tendsto
      (fun j : ℕ => (j : ℝ) ^ N * ((2 ^ (N + 2) * C / (j : ℝ) ^ (N + 2)) * (4 * (j + 1 : ℕ))))
      atTop (𝓝 0) := by
    have ht := (hone.add (hone.pow 2)).const_mul (2 ^ (N + 2) * 4 * C)
    have ht0 : Tendsto (fun j : ℕ => 2 ^ (N + 2) * 4 * C * ((1 : ℝ) / j + ((1 : ℝ) / j) ^ 2))
        atTop (𝓝 0) := by simpa using ht
    apply ht0.congr'
    filter_upwards [eventually_ge_atTop 1] with j hj
    have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hj)
    push_cast
    field_simp
    ring
  have hrpow : Tendsto
      (fun j : ℕ => ((r j : ℝ) ^ (N + 2)) * ((7 : ℝ) / 8) ^ r j) atTop (𝓝 0) := by
    have ht := (tendsto_pow_const_mul_const_pow_of_lt_one (N + 2)
      (by norm_num : (0 : ℝ) ≤ 7 / 8) (by norm_num : (7 : ℝ) / 8 < 1)).comp hr
    simpa [Function.comp_def] using ht
  have htail : Tendsto
      (fun j : ℕ => (j : ℝ) ^ N * (((j : ℝ) * ((7 : ℝ) / 8) ^ r j) * (4 * (j + 1 : ℕ))))
      atTop (𝓝 0) := by
    have hu : Tendsto
        (fun j : ℕ => (4 * 64 ^ (N + 1) * 128 : ℝ) * ((r j : ℝ) ^ (N + 2) * ((7 : ℝ) / 8) ^ r j))
        atTop (𝓝 0) := by simpa using hrpow.const_mul (4 * 64 ^ (N + 1) * 128 : ℝ)
    apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) _ hu
    filter_upwards [eventually_ge_atTop 64] with j hj
    have hjr : j ≤ 64 * r j := by dsimp [r]; omega
    have hj1r : j + 1 ≤ 128 * r j := by dsimp [r]; omega
    have hjrR : (j : ℝ) ≤ 64 * r j := by exact_mod_cast hjr
    have hj1rR : ((j + 1 : ℕ) : ℝ) ≤ 128 * r j := by exact_mod_cast hj1r
    have hpowle : (j : ℝ) ^ (N + 1) ≤ (64 * r j : ℝ) ^ (N + 1) :=
      pow_le_pow_left₀ (by positivity) hjrR _
    have hq : (0 : ℝ) ≤ ((7 : ℝ) / 8) ^ r j := by positivity
    calc
      (j : ℝ) ^ N * (((j : ℝ) * ((7 : ℝ) / 8) ^ r j) * (4 * (j + 1 : ℕ))) =
          4 * ((j : ℝ) ^ (N + 1) * ((j + 1 : ℕ) : ℝ)) * ((7 : ℝ) / 8) ^ r j := by ring
      _ ≤ 4 * ((64 * r j : ℝ) ^ (N + 1) * (128 * r j)) * ((7 : ℝ) / 8) ^ r j := by
        gcongr
      _ = (4 * 64 ^ (N + 1) * 128 : ℝ) * ((r j : ℝ) ^ (N + 2) * ((7 : ℝ) / 8) ^ r j) := by
        ring
  have hKpow : Tendsto
      (fun j : ℕ => (K j : ℝ) ^ (N + 1) * ((1 : ℝ) / 3) ^ K j) atTop (𝓝 0) := by
    have ht := (tendsto_pow_const_mul_const_pow_of_lt_one (N + 1)
      (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (1 : ℝ) / 3 < 1)).comp hK
    simpa [Function.comp_def] using ht
  have hhigh : Tendsto
      (fun j : ℕ => (j : ℝ) ^ N * (((3 : ℝ) ^ K j)⁻¹ * (4 * (j + 1 : ℕ)))) atTop (𝓝 0) := by
    have hu : Tendsto
        (fun j : ℕ => (4 * 8192 ^ (N + 1) : ℝ) * ((K j : ℝ) ^ (N + 1) * ((1 : ℝ) / 3) ^ K j))
        atTop (𝓝 0) := by simpa using hKpow.const_mul (4 * 8192 ^ (N + 1) : ℝ)
    apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) _ hu
    filter_upwards [eventually_ge_atTop 4096] with j hj
    have hjK : j ≤ 8192 * K j := by dsimp [K]; omega
    have hj1K : j + 1 ≤ 8192 * K j := by dsimp [K]; omega
    have hjKR : (j : ℝ) ≤ 8192 * K j := by exact_mod_cast hjK
    have hj1KR : ((j + 1 : ℕ) : ℝ) ≤ 8192 * K j := by exact_mod_cast hj1K
    have hpowle : (j : ℝ) ^ N ≤ (8192 * K j : ℝ) ^ N :=
      pow_le_pow_left₀ (by positivity) hjKR _
    have heq : ((3 : ℝ) ^ K j)⁻¹ = ((1 : ℝ) / 3) ^ K j := by
      rw [one_div, inv_pow]
    rw [heq]
    have hq : (0 : ℝ) ≤ ((1 : ℝ) / 3) ^ K j := by positivity
    calc
      (j : ℝ) ^ N * (((1 : ℝ) / 3) ^ K j * (4 * (j + 1 : ℕ))) =
          4 * ((j : ℝ) ^ N * ((j + 1 : ℕ) : ℝ)) * ((1 : ℝ) / 3) ^ K j := by ring
      _ ≤ 4 * ((8192 * K j : ℝ) ^ N * (8192 * K j)) * ((1 : ℝ) / 3) ^ K j := by
        gcongr
      _ = (4 * 8192 ^ (N + 1) : ℝ) * ((K j : ℝ) ^ (N + 1) * ((1 : ℝ) / 3) ^ K j) := by
        ring
  have hsum := (hrat.add htail).add hhigh
  have hsum0 : Tendsto
      (fun j : ℕ =>
        (j : ℝ) ^ N * ((2 ^ (N + 2) * C / (j : ℝ) ^ (N + 2)) * (4 * (j + 1 : ℕ))) +
          (j : ℝ) ^ N * (((j : ℝ) * ((7 : ℝ) / 8) ^ r j) * (4 * (j + 1 : ℕ))) +
          (j : ℝ) ^ N * (((3 : ℝ) ^ K j)⁻¹ * (4 * (j + 1 : ℕ)))) atTop (𝓝 0) := by
    simpa using hsum
  apply hsum0.congr'
  filter_upwards with j
  simp only [logMajorant, r, K]
  push_cast
  ring

end CollatzMoonshot.Conjugacy
