/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Conjugacy.BeyondWordsLinear

/-!
# The linear-depth edge at its natural limit: every `κ < (log₂ 3)/2`

`beyondWordsUniformLinear_of_sliceOscDecay` reaches depth `K ≤ j/8` from the node `SliceOscDecay`
with the fixed choice `m = ⌊a/2⌋` on the band `j ≤ 4a ≤ 11j/5`.  The per-slice bound
`sum_norm_levelSum_resInd_le` is general in `m`: on a slice `a` the residue sums are
`≤ 2 levelOsc j a m + 2^K 3^{m−a} card` for every `m ≤ a`.  Taking the band `|a − j/2| ≤ δ j`
(Chebyshev, `sum_oddDeviation_sq_real`: the complement has `≤ 2^j/(4 δ² j)` starts) and
`m = a − ⌈ρ j⌉` with `κ log₃ 2 < ρ < 1/2 − δ`, the second term is `2^K 3^{−⌈ρ j⌉} → 0`
exponentially and `m ≥ j(1/2 − δ − ρ) − 1 → ∞`, so the node (exponent `A = 1`) kills the first
term.  Hence uniformity to every linear depth `κ j` with `κ < (log₂ 3)/2 ≈ 0.792`.

Ensemble statement over all `j`-bit starts; nothing about any individual orbit.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB

/-! ## Total variation from slices on an arbitrary band -/

/-- The slices of a band partition the starts whose odd-step count lies in the band. -/
theorem sum_levelSet_card_filter (j : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ∑ a ∈ (Finset.range (j + 1)).filter P, (levelSet j a).card =
      ((Finset.range (2 ^ j)).filter (fun r => P (oddCount r j))).card := by
  unfold levelSet
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  congr 1
  ext r
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨h1, _, h3⟩
    exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩
    exact ⟨h1, Nat.lt_succ_of_le (oddCount_le r j), h3⟩

/-- **Total variation from the slices of a band.**  `beyondTV_le_of_slice` with the fixed band
`j ≤ 4a ≤ 11j/5` replaced by an arbitrary band `P`: if every slice in the band has residue sums
totalling at most `M · #slice`, then `beyondTV j K` is at most `M` plus twice the share of the
starts outside the band (charged once in total, `sum_norm_resInd_le`). -/
theorem beyondTV_le_of_band (j K : ℕ) (P : ℕ → Prop) [DecidablePred P] {M : ℝ} (hM : 0 ≤ M)
    (hslice : ∀ a, P a →
      ∑ c ∈ Finset.range (2 ^ K), ‖∑ r ∈ levelSet j a, resInd K c (tstep^[j] r)‖ ≤
        M * (levelSet j a).card) :
    beyondTV j K ≤
      M + 2 * (((Finset.range (2 ^ j)).filter (fun r => ¬ P (oddCount r j))).card : ℝ) /
        2 ^ j := by
  set E := ((Finset.range (2 ^ j)).filter (fun r => ¬ P (oddCount r j))).card with hE
  let I := Finset.range (j + 1)
  let L := I.filter P
  let H := I.filter (fun a => ¬ P a)
  let S : ℕ → ℕ → ℂ := fun c a => ∑ r ∈ levelSet j a, resInd K c (tstep^[j] r)
  have hpowpos : (0 : ℝ) < 2 ^ j := by positivity
  have hterm (c : ℕ) : |(beyondCount j K c : ℝ) / 2 ^ j - 1 / 2 ^ K| =
      ‖∑ r ∈ Finset.range (2 ^ j), resInd K c (tstep^[j] r)‖ / 2 ^ j := by
    rw [sum_resInd_eq]
    have hr := Complex.norm_real ((beyondCount j K c : ℝ) - 2 ^ j * ((2 : ℝ) ^ K)⁻¹)
    push_cast at hr
    rw [hr, Real.norm_eq_abs]
    have heq : (beyondCount j K c : ℝ) / 2 ^ j - 1 / 2 ^ K =
        ((beyondCount j K c : ℝ) - 2 ^ j * ((2 : ℝ) ^ K)⁻¹) / 2 ^ j := by
      field_simp
    rw [heq, abs_div, abs_of_pos hpowpos]
  have hpartition (c : ℕ) : ∑ r ∈ Finset.range (2 ^ j), resInd K c (tstep^[j] r) =
      (∑ a ∈ L, S c a) + ∑ a ∈ H, S c a := by
    rw [sum_range_eq_sum_levelSet j (fun r => resInd K c (tstep^[j] r))]
    exact (Finset.sum_filter_add_sum_filter_not I P (S c)).symm
  have hHnorm (c : ℕ) : ‖∑ a ∈ H, S c a‖ ≤
      ∑ a ∈ H, ∑ r ∈ levelSet j a, ‖resInd K c (tstep^[j] r)‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
  have hLcard : ∑ a ∈ L, ((levelSet j a).card : ℝ) ≤ 2 ^ j := by
    calc
      ∑ a ∈ L, ((levelSet j a).card : ℝ) ≤
          ∑ a ∈ I, ((levelSet j a).card : ℝ) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => by positivity)
      _ = 2 ^ j := by
        exact_mod_cast sum_levelSet_card j
  have hHcard : ∑ a ∈ H, ((levelSet j a).card : ℝ) = E := by
    exact_mod_cast sum_levelSet_card_filter j (fun a => ¬ P a)
  have hLsum : ∑ c ∈ Finset.range (2 ^ K), ∑ a ∈ L, ‖S c a‖ ≤ M * 2 ^ j := by
    rw [Finset.sum_comm]
    calc
      ∑ a ∈ L, ∑ c ∈ Finset.range (2 ^ K), ‖S c a‖ ≤
          ∑ a ∈ L, M * ((levelSet j a).card : ℝ) :=
        Finset.sum_le_sum fun a ha => hslice a (Finset.mem_filter.mp ha).2
      _ = M * ∑ a ∈ L, ((levelSet j a).card : ℝ) := by rw [Finset.mul_sum]
      _ ≤ M * 2 ^ j := mul_le_mul_of_nonneg_left hLcard hM
  have hHsum : ∑ c ∈ Finset.range (2 ^ K),
      ∑ a ∈ H, ∑ r ∈ levelSet j a, ‖resInd K c (tstep^[j] r)‖ ≤ 2 * (E : ℝ) := by
    rw [Finset.sum_comm]
    calc
      ∑ a ∈ H, ∑ c ∈ Finset.range (2 ^ K), ∑ r ∈ levelSet j a, ‖resInd K c (tstep^[j] r)‖ =
          ∑ a ∈ H, ∑ r ∈ levelSet j a,
            ∑ c ∈ Finset.range (2 ^ K), ‖resInd K c (tstep^[j] r)‖ := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_comm]
      _ ≤ ∑ a ∈ H, ∑ _r ∈ levelSet j a, (2 : ℝ) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun r _ => sum_norm_resInd_le K _
      _ = 2 * ∑ a ∈ H, ((levelSet j a).card : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
      _ = 2 * (E : ℝ) := by rw [hHcard]
  unfold beyondTV
  calc
    ∑ c ∈ Finset.range (2 ^ K), |(beyondCount j K c : ℝ) / 2 ^ j - 1 / 2 ^ K| =
        (∑ c ∈ Finset.range (2 ^ K),
          ‖∑ r ∈ Finset.range (2 ^ j), resInd K c (tstep^[j] r)‖) / 2 ^ j := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun c _ => hterm c
    _ ≤ (∑ c ∈ Finset.range (2 ^ K), ((∑ a ∈ L, ‖S c a‖) +
          ∑ a ∈ H, ∑ r ∈ levelSet j a, ‖resInd K c (tstep^[j] r)‖)) / 2 ^ j := by
      gcongr with c hc
      rw [hpartition c]
      exact (norm_add_le _ _).trans (add_le_add (norm_sum_le _ _) (hHnorm c))
    _ ≤ (M * 2 ^ j + 2 * (E : ℝ)) / 2 ^ j := by
      gcongr
      rw [Finset.sum_add_distrib]
      exact add_le_add hLsum hHsum
    _ = M + 2 * (E : ℝ) / 2 ^ j := by
      field_simp

/-! ## The Chebyshev tail of the band `|a − j/2| ≤ δ j` -/

/-- **Band Chebyshev.**  The starts `r < 2^j` whose odd-step count is more than `δ j` from `j/2`
number at most `2^j / (4 δ² j)`, in division-free form (`sum_oddDeviation_sq_real`). -/
theorem card_offBand_mul_le (j : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (((Finset.range (2 ^ j)).filter
        (fun r => ¬ |(oddCount r j : ℝ) - j / 2| ≤ δ * j)).card : ℝ) *
      (4 * δ ^ 2 * (j : ℝ) ^ 2) ≤ (j : ℝ) * 2 ^ j := by
  set F := (Finset.range (2 ^ j)).filter (fun r => ¬ |(oddCount r j : ℝ) - j / 2| ≤ δ * j)
  have hlarge (r : ℕ) (hr : r ∈ F) :
      4 * δ ^ 2 * (j : ℝ) ^ 2 ≤ (oddDeviation r j : ℝ) ^ 2 := by
    have hlt : δ * j < |(oddCount r j : ℝ) - j / 2| := lt_of_not_ge (Finset.mem_filter.1 hr).2
    have h0 : 0 ≤ δ * j := by positivity
    have hsq : (δ * j) ^ 2 ≤ ((oddCount r j : ℝ) - j / 2) ^ 2 := by
      rw [← sq_abs ((oddCount r j : ℝ) - j / 2)]
      exact pow_le_pow_left₀ h0 hlt.le 2
    have hdev : (oddDeviation r j : ℝ) = 2 * ((oddCount r j : ℝ) - j / 2) := by
      unfold oddDeviation
      push_cast
      ring
    rw [hdev]
    nlinarith
  calc
    (F.card : ℝ) * (4 * δ ^ 2 * (j : ℝ) ^ 2) = ∑ _r ∈ F, 4 * δ ^ 2 * (j : ℝ) ^ 2 := by simp
    _ ≤ ∑ r ∈ F, (oddDeviation r j : ℝ) ^ 2 := Finset.sum_le_sum fun r hr => hlarge r hr
    _ ≤ ∑ r ∈ Finset.range (2 ^ j), (oddDeviation r j : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => by positivity)
    _ = (j : ℝ) * 2 ^ j := sum_oddDeviation_sq_real j

/-- The Chebyshev tail as a share: twice the off-band starts over `2^j` is `≤ 1/(2 δ² j)`. -/
theorem two_mul_card_offBand_div_le (j : ℕ) (hj : 0 < j) {δ : ℝ} (hδ : 0 < δ) :
    2 * (((Finset.range (2 ^ j)).filter
        (fun r => ¬ |(oddCount r j : ℝ) - j / 2| ≤ δ * j)).card : ℝ) / 2 ^ j ≤
      1 / (2 * δ ^ 2) / j := by
  have h := card_offBand_mul_le j hδ.le
  set E := (((Finset.range (2 ^ j)).filter
        (fun r => ¬ |(oddCount r j : ℝ) - j / 2| ≤ δ * j)).card : ℝ)
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have hp : (0 : ℝ) < 2 ^ j := by positivity
  have hd : 0 < δ ^ 2 := by positivity
  rw [div_le_div_iff₀ hp hjR, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith

/-! ## The geometric term `2^K 3^{−s}` -/

/-- `2^K / 3^s ≤ exp(−η)^j` once `K ≤ k j` and `s ≥ ρ j` with `ρ log 3 − k log 2 = η`. -/
theorem two_pow_div_three_pow_le (j K s : ℕ) {k ρ η : ℝ}
    (hK : (K : ℝ) ≤ k * j) (hs : ρ * j ≤ s) (hη : ρ * Real.log 3 - k * Real.log 2 = η) :
    (2 : ℝ) ^ K / 3 ^ s ≤ Real.exp (-η) ^ j := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have e2 : (2 : ℝ) ^ K = Real.exp (K * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have e3 : (3 : ℝ) ^ s = Real.exp (s * Real.log 3) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [e2, e3, ← Real.exp_sub, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.2
  have h1 : (K : ℝ) * Real.log 2 ≤ k * j * Real.log 2 := mul_le_mul_of_nonneg_right hK hl2.le
  have h2 : ρ * j * Real.log 3 ≤ s * Real.log 3 := mul_le_mul_of_nonneg_right hs hl3.le
  have : (j : ℝ) * -η = -(ρ * j * Real.log 3) + k * j * Real.log 2 := by
    rw [← hη]
    ring
  linarith

/-- **Frozen (2026-11-04).**  From the sliced Proposition 1.14 node, beyond-Terras uniformity
holds to every linear depth `K ≤ κ j` with `κ < (log₂ 3)/2`.

Proof: band `|a − j/2| ≤ δ j` (Chebyshev tail `≤ 1/(2δ²j)`), scale `m = a − ⌈ρ j⌉` with
`κ⁺ log₃ 2 < ρ < 1/2 − δ`; the fibre term is `2^K 3^{−⌈ρ j⌉} ≤ exp(−η j)` and `m ≥ (g/3) j − 1`
with `g = 1/2 − κ⁺ log₃ 2`, so the node with `A = 1` kills the oscillation term. -/
theorem beyondWordsUniformLinear_of_sliceOscDecay_sharp (h : SliceOscDecay) (κ : ℝ)
    (hκ : κ < Real.logb 2 3 / 2) : BeyondWordsUniformLinear κ := by
  classical
  intro ε hε
  obtain ⟨C, hCpos, hC⟩ := h 1 one_pos
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set k := max κ 0 with hkdef
  have hk0 : 0 ≤ k := le_max_right _ _
  have hκk : κ ≤ k := le_max_left _ _
  set t := k * Real.log 2 / Real.log 3 with htdef
  have ht0 : 0 ≤ t := by positivity
  have htl : t * Real.log 3 = k * Real.log 2 := by
    rw [htdef]
    field_simp
  have ht : t < 1 / 2 := by
    have hκ' : κ * Real.log 2 < Real.log 3 / 2 := by
      rw [Real.logb] at hκ
      have := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).1 hκ
      rw [lt_div_iff₀ hl2] at this
      linarith
    have hk' : k * Real.log 2 < Real.log 3 / 2 := by
      rcases le_total κ 0 with h0 | h0
      · rw [hkdef, max_eq_right h0]
        linarith
      · rw [hkdef, max_eq_left h0]
        exact hκ'
    rw [htdef, div_lt_iff₀ hl3]
    linarith
  set g := 1 / 2 - t with hgdef
  have hg : 0 < g := by linarith
  set δ := min (1 / 10 : ℝ) (g / 3) with hδdef
  have hδpos : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ10 : δ ≤ 1 / 10 := min_le_left _ _
  have hδg : δ ≤ g / 3 := min_le_right _ _
  set ρ := t + g / 3 with hρdef
  set η := g / 3 * Real.log 3 with hηdef
  have hη : 0 < η := by positivity
  have hηeq : ρ * Real.log 3 - k * Real.log 2 = η := by
    rw [hρdef, hηdef, ← htl]
    ring
  -- the three eventual thresholds
  have hgeo := (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos (-η)).le
    (Real.exp_lt_one_iff.2 (by linarith))).eventually (gt_mem_nhds (by positivity : 0 < ε / 4))
  have htail := (tendsto_const_div_atTop_nhds_zero_nat (1 / (2 * δ ^ 2))).eventually
    (gt_mem_nhds (by positivity : 0 < ε / 2))
  obtain ⟨N, hN⟩ := exists_nat_gt ((3 / g) * (2 + 8 * C / ε))
  filter_upwards [hgeo, htail, eventually_ge_atTop (N + 1)] with j hjgeo hjtail hjN
  intro K hK
  have hjpos : 0 < j := by omega
  have hjR : (0 : ℝ) < j := by exact_mod_cast hjpos
  have hKk : (K : ℝ) ≤ k * j := hK.trans (mul_le_mul_of_nonneg_right hκk hjR.le)
  have hjN' : (3 / g) * (2 + 8 * C / ε) < j := by
    have : (N : ℝ) + 1 ≤ j := by exact_mod_cast hjN
    linarith
  have hjbig : 2 + 8 * C / ε < g / 3 * j := by
    rw [div_mul_eq_mul_div, lt_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
    rw [div_mul_eq_mul_div, div_lt_iff₀ hg] at hjN'
    linarith
  set s := ⌈ρ * j⌉₊ with hsdef
  have hs1 : ρ * j ≤ s := Nat.le_ceil _
  have hs2 : (s : ℝ) < ρ * j + 1 := Nat.ceil_lt_add_one (by positivity)
  set P : ℕ → Prop := fun a => |(a : ℝ) - j / 2| ≤ δ * j with hPdef
  have hper : ∀ a, P a →
      ∑ c ∈ Finset.range (2 ^ K), ‖∑ r ∈ levelSet j a, resInd K c (tstep^[j] r)‖ ≤
        (ε / 2) * (levelSet j a).card := by
    intro a ha
    have ha' := abs_le.1 ha
    have haR1 : (1 / 2 - δ) * j ≤ a := by linarith [ha'.1]
    have haR2 : (a : ℝ) ≤ (1 / 2 + δ) * j := by linarith [ha'.2]
    -- the scale `m = a − s`
    have hgap : (g / 3) * j - 1 ≤ (a : ℝ) - s := by
      have h1 : ρ + g / 3 ≤ 1 / 2 - δ := by linarith
      have : (ρ + g / 3) * j ≤ (1 / 2 - δ) * j := mul_le_mul_of_nonneg_right h1 hjR.le
      linarith
    have hsa : s ≤ a := by
      have : (s : ℝ) ≤ a := by
        have : 0 ≤ 8 * C / ε := by positivity
        linarith
      exact_mod_cast this
    set m := a - s with hmdef
    have hmR : (m : ℝ) = a - s := by rw [hmdef, Nat.cast_sub hsa]
    have hm8 : 8 * C / ε ≤ m := by
      rw [hmR]
      linarith
    have hm1 : 1 ≤ m := by
      have : (1 : ℝ) ≤ m := by
        have : 0 ≤ 8 * C / ε := by positivity
        rw [hmR]
        linarith
      exact_mod_cast this
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
    have hδj : δ * j ≤ 1 / 10 * j := mul_le_mul_of_nonneg_right hδ10 hjR.le
    have hw1 : j ≤ 5 * a := by
      have : (j : ℝ) ≤ 5 * a := by linarith
      exact_mod_cast this
    have hw2 : 5 * a ≤ 3 * j := by
      have : (5 * a : ℝ) ≤ 3 * j := by linarith
      exact_mod_cast this
    have hb := sum_norm_levelSum_resInd_le j a m K (Nat.sub_le a s)
    have hosc := hC j a m hm1 (Nat.sub_le a s) hw1 hw2
    rw [Real.rpow_neg_one] at hosc
    have hcard : (0 : ℝ) ≤ (levelSet j a).card := by positivity
    have hCm : C * (m : ℝ)⁻¹ ≤ ε / 8 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hmpos]
      rw [div_le_iff₀ hε] at hm8
      linarith
    have hoscε : 2 * levelOsc j a m ≤ ε / 4 * (levelSet j a).card := by
      have : C * (m : ℝ)⁻¹ * (levelSet j a).card ≤ ε / 8 * (levelSet j a).card := by gcongr
      linarith
    have hgeoε : (2 : ℝ) ^ K * ((3 : ℝ) ^ m / 3 ^ a) ≤ ε / 4 := by
      have hpow : (3 : ℝ) ^ a = 3 ^ m * 3 ^ s := by
        rw [← pow_add, hmdef, Nat.sub_add_cancel hsa]
      have h1 : (2 : ℝ) ^ K * ((3 : ℝ) ^ m / 3 ^ a) = 2 ^ K / 3 ^ s := by
        rw [hpow]
        field_simp
      rw [h1]
      exact (two_pow_div_three_pow_le j K s hKk hs1 hηeq).trans hjgeo.le
    calc
      ∑ c ∈ Finset.range (2 ^ K), ‖∑ r ∈ levelSet j a, resInd K c (tstep^[j] r)‖ ≤
          2 * levelOsc j a m + 2 ^ K * ((3 : ℝ) ^ m / 3 ^ a) * (levelSet j a).card := hb
      _ ≤ ε / 4 * (levelSet j a).card + ε / 4 * (levelSet j a).card := by
        gcongr
      _ = (ε / 2) * (levelSet j a).card := by ring
  have hTV := beyondTV_le_of_band j K P (by positivity) hper
  have hoff := two_mul_card_offBand_div_le j hjpos hδpos
  have hjtail' : 1 / (2 * δ ^ 2) / j < ε / 2 := hjtail
  simp only [hPdef] at hTV
  linarith

end CollatzMoonshot.Conjugacy
