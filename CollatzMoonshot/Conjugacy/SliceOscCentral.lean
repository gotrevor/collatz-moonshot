/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Conjugacy.BeyondWordsLinearSharp
import CollatzMoonshot.Conjugacy.SliceDecay
import CollatzMoonshot.Conjugacy.SliceOscBridge
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# The central-band slice oscillation node, and why Tao §6 only reaches the centre

`SliceOscDecay` asks for oscillation decay on every slice of the window `1/5 ≤ a/j ≤ 3/5`.
Tao's §6 conditioning, read for slices (`SEC6S-PLAN.md`), needs two budgets on the low-digit
tail of `p` odd steps spanning `t` positions:

* **entropy**: each tail configuration has slice probability `≈ e^{−t H(ρ)}`, `ρ = a/j`, and
  this must be `≲ 3^{−a}` (Tao's single-point mass `2^{−l}`), so `a log 3 ≤ t H(ρ)`;
* **injectivity**: the tail integer `Σ_{k ≤ p} 3^{k−1} 2^{t−T_k}` must stay below `3^a`
  (Tao's `fnat < 3^n`), and its leading term is `≈ 2^t`, so `t log 2 ≤ a log 3`.

Off the centre `H(ρ) < log 2` (`Real.binEntropy_lt_log_two`) and the two are incompatible
(`tail_budgets_incompatible`); with Tao's `C_A² log a` slack they are compatible only for
`|ρ − 1/2| ≲ √(log a / a)`.  At `ρ = 1/2` they coincide, which is Tao's case.

The consumers need only the centre.  `SliceOscDecayCentral` is the node on the CLT band
`|2a − j| ≤ K √j` (every `K`), and `beyondWordsUniformLinear_of_sliceOscDecayCentral` proves the
linear-depth consumer from it at the same depth `κ < (log₂ 3)/2` (Chebyshev share `≤ 1/K²`).
`sliceOscDecayCentral_of_sliceOscDecay` shows the central node is implied by the window node.
The campaign targets are the two edges `sliceOscStep_of_sliceCharDecay` (the §6 conditioning at
one scale step) and `sliceOscDecayCentral_of_sliceOscStep` (the §6.1 telescope through the slice
mixture identity), both frozen with `sorry`.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB

/-! ## The obstruction kernel -/

/-- **The two tail budgets are incompatible off the centre.**  For `ρ ≠ 1/2` no tail span
`t > 0` satisfies both the entropy budget `a log 3 ≤ t H(ρ)` and the injectivity budget
`t log 2 ≤ a log 3`, because `H(ρ) < log 2`.  (The heuristic identification of the two budgets
with Tao's (6.10)–(6.15) is in the module docstring and `SEC6S-PLAN.md` §3.) -/
theorem tail_budgets_incompatible {ρ t a : ℝ} (hρ : ρ ≠ 2⁻¹) (ht : 0 < t) :
    ¬ (a * Real.log 3 ≤ t * Real.binEntropy ρ ∧ t * Real.log 2 ≤ a * Real.log 3) := by
  rintro ⟨h1, h2⟩
  have hH := Real.binEntropy_lt_log_two.2 hρ
  have : t * Real.binEntropy ρ < t * Real.log 2 := mul_lt_mul_of_pos_left hH ht
  linarith

/-! ## The central node and its consumer -/

/-- **Node (central band): the sliced Proposition 1.14 on the CLT band.**  For every `A` and
every band width `K`, the oscillation above scale `m` of a slice with `|2a − j| ≤ K √j` is a
`C m^{−A}` fraction of the slice.  Implied by `SliceOscDecay`
(`sliceOscDecayCentral_of_sliceOscDecay`); the probe `experiments/conjugacy/levelosc_table.c`
measures exactly this band (`a = j/2 ± 1`).  Confidence 75% true. -/
def SliceOscDecayCentral : Prop :=
  ∀ A > (0 : ℝ), ∀ K : ℝ, ∃ C > (0 : ℝ), ∀ j a m : ℕ, 1 ≤ m → m ≤ a →
    |2 * (a : ℝ) - j| ≤ K * Real.sqrt j →
      levelOsc j a m ≤ C * (m : ℝ) ^ (-A) * (levelSet j a).card

/-- **The window node implies the central node.**  For `j ≥ 25 K²` the band `|2a − j| ≤ K √j`
lies in the window `j ≤ 5a ≤ 3j`; below that, `m ≤ a ≤ j` is bounded and `levelOsc ≤ 2 · card`
(`levelOsc_le_two_mul_card`) is absorbed into the constant. -/
theorem sliceOscDecayCentral_of_sliceOscDecay (h : SliceOscDecay) : SliceOscDecayCentral := by
  intro A hA K
  obtain ⟨C, hC, hCb⟩ := h A hA
  set K' := max K 0 with hK'def
  have hK'0 : 0 ≤ K' := le_max_right _ _
  obtain ⟨J, hJ⟩ := exists_nat_gt ((5 * K') ^ 2)
  refine ⟨max C (2 * (J : ℝ) ^ A), lt_max_of_lt_left hC, ?_⟩
  intro j a m hm1 hma hband
  have hle2 := levelOsc_le_two_mul_card j a m hma
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  have hmpow : 0 ≤ (m : ℝ) ^ (-A) := Real.rpow_nonneg hmpos.le _
  by_cases hjJ : J ≤ j
  · have hband' : |2 * (a : ℝ) - j| ≤ K' * Real.sqrt j :=
      hband.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))
    have hsq : 5 * K' ≤ Real.sqrt j := by
      apply Real.le_sqrt_of_sq_le
      have : (J : ℝ) ≤ j := by exact_mod_cast hjJ
      linarith
    have hsj : Real.sqrt j * Real.sqrt j = j := Real.mul_self_sqrt (Nat.cast_nonneg _)
    have hKs : 5 * (K' * Real.sqrt j) ≤ j := by
      have := mul_le_mul_of_nonneg_right hsq (Real.sqrt_nonneg (j : ℝ))
      rw [hsj] at this
      linarith
    have ha := abs_le.1 hband'
    have hw1 : j ≤ 5 * a := by
      have : (j : ℝ) ≤ 5 * a := by linarith
      exact_mod_cast this
    have hw2 : 5 * a ≤ 3 * j := by
      have : (5 * a : ℝ) ≤ 3 * j := by linarith
      exact_mod_cast this
    calc
      levelOsc j a m ≤ C * (m : ℝ) ^ (-A) * (levelSet j a).card := hCb j a m hm1 hma hw1 hw2
      _ ≤ max C (2 * (J : ℝ) ^ A) * (m : ℝ) ^ (-A) * (levelSet j a).card := by
        gcongr
        exact le_max_left _ _
  · replace hjJ : j < J := not_le.1 hjJ
    rcases Nat.eq_zero_or_pos (levelSet j a).card with h0 | hpos
    · have h0' : ((levelSet j a).card : ℝ) = 0 := by exact_mod_cast h0
      rw [h0'] at hle2 ⊢
      simp only [mul_zero] at hle2 ⊢
      exact hle2
    · obtain ⟨r, hr⟩ := Finset.card_pos.1 hpos
      have haj : a ≤ j := by
        have := (Finset.mem_filter.1 hr).2
        rw [← this]
        exact oddCount_le r j
      have hmJ : (m : ℝ) ≤ J := by exact_mod_cast (by omega : m ≤ J)
      have hmA : 0 < (m : ℝ) ^ A := Real.rpow_pos_of_pos hmpos A
      have hJm : (m : ℝ) ^ A ≤ (J : ℝ) ^ A := Real.rpow_le_rpow hmpos.le hmJ hA.le
      have h2 : 2 ≤ 2 * (J : ℝ) ^ A * (m : ℝ) ^ (-A) := by
        rw [Real.rpow_neg hmpos.le, mul_assoc, ← div_eq_mul_inv]
        have : 1 ≤ (J : ℝ) ^ A / (m : ℝ) ^ A := (one_le_div hmA).2 hJm
        linarith
      have hcard : (0 : ℝ) ≤ (levelSet j a).card := by positivity
      calc
        levelOsc j a m ≤ 2 * (levelSet j a).card := hle2
        _ ≤ 2 * (J : ℝ) ^ A * (m : ℝ) ^ (-A) * (levelSet j a).card := by gcongr
        _ ≤ max C (2 * (J : ℝ) ^ A) * (m : ℝ) ^ (-A) * (levelSet j a).card := by
          gcongr
          exact le_max_right _ _

/-- **CLT-band Chebyshev.**  The starts whose odd-step count deviates from `j/2` by more than
`K √j / 2` number at most `2^j / K²`, in division-free form. -/
theorem card_offCentral_mul_le (j : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    (((Finset.range (2 ^ j)).filter
        (fun r => ¬ |2 * (oddCount r j : ℝ) - j| ≤ K * Real.sqrt j)).card : ℝ) *
      (K ^ 2 * j) ≤ (j : ℝ) * 2 ^ j := by
  set F := (Finset.range (2 ^ j)).filter
    (fun r => ¬ |2 * (oddCount r j : ℝ) - j| ≤ K * Real.sqrt j)
  have hlarge (r : ℕ) (hr : r ∈ F) : K ^ 2 * j ≤ (oddDeviation r j : ℝ) ^ 2 := by
    have hlt : K * Real.sqrt j < |2 * (oddCount r j : ℝ) - j| :=
      lt_of_not_ge (Finset.mem_filter.1 hr).2
    have h0 : 0 ≤ K * Real.sqrt j := by positivity
    have hsq : (K * Real.sqrt j) ^ 2 ≤ (2 * (oddCount r j : ℝ) - j) ^ 2 := by
      rw [← sq_abs (2 * (oddCount r j : ℝ) - j)]
      exact pow_le_pow_left₀ h0 hlt.le 2
    have hdev : (oddDeviation r j : ℝ) = 2 * (oddCount r j : ℝ) - j := by
      unfold oddDeviation
      push_cast
      ring
    rw [hdev]
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)] at hsq
    exact hsq
  calc
    (F.card : ℝ) * (K ^ 2 * j) = ∑ _r ∈ F, K ^ 2 * (j : ℝ) := by simp
    _ ≤ ∑ r ∈ F, (oddDeviation r j : ℝ) ^ 2 := Finset.sum_le_sum fun r hr => hlarge r hr
    _ ≤ ∑ r ∈ Finset.range (2 ^ j), (oddDeviation r j : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => by positivity)
    _ = (j : ℝ) * 2 ^ j := sum_oddDeviation_sq_real j

/-- **The linear edge from the central node.**  `SliceOscDecayCentral` gives beyond-Terras
uniformity to every linear depth `K ≤ κ j`, `κ < (log₂ 3)/2`, exactly as
`beyondWordsUniformLinear_of_sliceOscDecay_sharp` does from the window node: band
`|2a − j| ≤ K_ε √j` with `K_ε² = 8/ε` (off-band share `≤ ε/8`), scale `m = a − ⌈ρ j⌉`. -/
theorem beyondWordsUniformLinear_of_sliceOscDecayCentral (h : SliceOscDecayCentral) (κ : ℝ)
    (hκ : κ < Real.logb 2 3 / 2) : BeyondWordsUniformLinear κ := by
  classical
  intro ε hε
  set Kb : ℝ := Real.sqrt (8 / ε) with hKbdef
  have hKb0 : 0 ≤ Kb := Real.sqrt_nonneg _
  have hKb2 : Kb ^ 2 = 8 / ε := Real.sq_sqrt (by positivity)
  obtain ⟨C, hCpos, hC⟩ := h 1 one_pos Kb
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
  set ρ := t + g / 3 with hρdef
  set η := g / 3 * Real.log 3 with hηdef
  have hη : 0 < η := by positivity
  have hηeq : ρ * Real.log 3 - k * Real.log 2 = η := by
    rw [hρdef, hηdef, ← htl]
    ring
  have hgeo := (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos (-η)).le
    (Real.exp_lt_one_iff.2 (by linarith))).eventually (gt_mem_nhds (by positivity : 0 < ε / 4))
  obtain ⟨N, hN⟩ := exists_nat_gt ((3 / g) * (2 + 8 * C / ε))
  obtain ⟨N2, hN2⟩ := exists_nat_gt ((3 * Kb / (2 * g)) ^ 2)
  filter_upwards [hgeo, eventually_ge_atTop (N + 1), eventually_ge_atTop N2]
    with j hjgeo hjN hjN2
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
  -- the band half-width `Kb √j / 2` is at most `(g/3) j`
  have hsj : Real.sqrt j * Real.sqrt j = j := Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hsqrt : 3 * Kb / (2 * g) ≤ Real.sqrt j := by
    apply Real.le_sqrt_of_sq_le
    have : (N2 : ℝ) ≤ j := by exact_mod_cast hjN2
    linarith
  have hbandw : Kb * Real.sqrt j / 2 ≤ g / 3 * j := by
    have h1 : 3 * Kb / (2 * g) * Real.sqrt j ≤ j := by
      have := mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg (j : ℝ))
      rwa [hsj] at this
    have h2 : Kb * Real.sqrt j / 2 = g / 3 * (3 * Kb / (2 * g) * Real.sqrt j) := by
      field_simp
    rw [h2]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have hρj : ρ * j = 1 / 2 * j - 2 * g / 3 * j := by
    rw [hρdef, hgdef]
    ring
  set s := ⌈ρ * j⌉₊ with hsdef
  have hs1 : ρ * j ≤ s := Nat.le_ceil _
  have hs2 : (s : ℝ) < ρ * j + 1 := Nat.ceil_lt_add_one (by positivity)
  set P : ℕ → Prop := fun a => |2 * (a : ℝ) - j| ≤ Kb * Real.sqrt j with hPdef
  have hper : ∀ a, P a →
      ∑ c ∈ Finset.range (2 ^ K), ‖∑ r ∈ levelSet j a, resInd K c (tstep^[j] r)‖ ≤
        (ε / 2) * (levelSet j a).card := by
    intro a ha
    have ha' := abs_le.1 ha
    have haR1 : (j : ℝ) / 2 - Kb * Real.sqrt j / 2 ≤ a := by linarith [ha'.1]
    have hgap : (g / 3) * j - 1 ≤ (a : ℝ) - s := by linarith
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
    have hb := sum_norm_levelSum_resInd_le j a m K (Nat.sub_le a s)
    have hosc := hC j a m hm1 (Nat.sub_le a s) ha
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
  have hE := card_offCentral_mul_le j hKb0
  set E := (((Finset.range (2 ^ j)).filter
      (fun r => ¬ |2 * (oddCount r j : ℝ) - j| ≤ Kb * Real.sqrt j)).card : ℝ) with hEdef
  have hp : (0 : ℝ) < 2 ^ j := by positivity
  have hE8 : E * 8 ≤ ε * 2 ^ j := by
    rw [hKb2] at hE
    have h1 : E * 8 / ε * j ≤ 2 ^ j * j := by
      calc E * 8 / ε * j = E * (8 / ε * j) := by ring
        _ ≤ j * 2 ^ j := hE
        _ = 2 ^ j * j := by ring
    have h2 := le_of_mul_le_mul_right h1 hjR
    rwa [div_le_iff₀ hε, mul_comm (2 ^ j : ℝ) ε] at h2
  have hoff : 2 * E / 2 ^ j ≤ ε / 4 := by
    rw [div_le_iff₀ hp]
    linarith
  have hTV' : beyondTV j K ≤ ε / 2 + 2 * E / 2 ^ j := hTV
  linarith

/-! ## The campaign targets (frozen; `SEC6S-PLAN.md`) -/

/-- **Node: one scale step on the logarithmic band.**  The oscillation of a slice above scale
`a − 1` (one 3-adic digit) is `O_A(a^{−A})` of the slice, on every band
`|2a − j| ≤ K √(j log j)`.  This is the sliced (6.2)–(6.10): Tao's telescope (6.1) only ever
calls the high regime at `m = n − 1` (`TaoCollatz.osc_syracZ_regime_telescope_at` applies its
hypothesis at `(k + 1, k)`), so one step suffices.  The `√(log j)` widening pays for the slice
mixture's fluctuations in the telescope.  Confidence 65% true. -/
def SliceOscStep : Prop :=
  ∀ A > (0 : ℝ), ∀ K : ℝ, ∃ C > (0 : ℝ), ∀ j a : ℕ, 2 ≤ a →
    |2 * (a : ℝ) - j| ≤ K * Real.sqrt (j * Real.log j) →
      levelOsc j a (a - 1) ≤ C * (a : ℝ) ^ (-A) * (levelSet j a).card

/-- **Campaign target 1 (Tao §6 conditioning for slices).**  Frozen 2026-11-04.  Condition on
`T_{p+1} = t`: the slice splits into a tail slice `(t − 1, p)` (low digits) and a head slice
`(j − t, a − p − 1)` (high digits, scaled by `3^{p+1} 2^{−t}`), independent and uniform, so the
character sum factors exactly (the slice `cond_char_factor`).  Head: `SliceCharDecay` at a unit
frequency.  Tail: Rényi-2 mass `≤ 3^{−a} a^{O(C_A²)}` by injectivity on the window
(`fnat_lt_of_suffix_window`), possible only on the central band (`tail_budgets_incompatible`).
Confidence 55%; `sorry` is the campaign. -/
theorem sliceOscStep_of_sliceCharDecay (h : SliceCharDecay) : SliceOscStep := by
  sorry

/-- **Campaign target 2 (the §6.1 telescope for slices).**  Frozen 2026-11-04.  Levels
triangle (`TaoCollatz.osc_syracZ_levels_triangle`, generic in the density) plus the slice
mixture identity `levelClass j a (a−1) c = Σ_{t ≤ j} levelMass (t − 1) (a − 1) c` (reducing a
slice mod `3^{a−1}` is the sum of the sub-slices, checked by `experiments/conjugacy/mixture.py`)
plus subadditivity (`TaoCollatz.osc_sum_le`) unroll `osc_{m,a}` into one-step oscillations of
sub-slices; sub-slices outside the logarithmic band carry `O(a^{−A})` of the mass (hypergeometric
tails).  Confidence 80%; `sorry` is the campaign. -/
theorem sliceOscDecayCentral_of_sliceOscStep (h : SliceOscStep) : SliceOscDecayCentral := by
  sorry

end CollatzMoonshot.Conjugacy
