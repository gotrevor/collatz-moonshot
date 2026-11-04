/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.BeyondWords

/-!
# Beyond-Terras words over a fixed dyadic block

`BeyondWordsUniform` takes `n < 2^b`.  Here `n` runs over a block `[α 2^b, (α + 1) 2^b)` for fixed
`α`.  Then `T^b (r + α 2^b) = T^b r + α 3^s`, `s` the odd count of `r`
(`tstep_iterate_add_mul_two_pow`), and on the slice `s = a` the shift is a constant.  So the residue
test on the block is a residue test on the slice, at the shifted residue `shiftRes K c α a`.  The
slice bound `eventually_norm_levelSum_le` is uniform over observables of the given weight, and
`layeredWeight_resInd` is uniform in the residue, so the slices sum as in `BeyondWordsUniform`.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB

/-- The starts in block `α` (`n = r + α 2^b`, `r < 2^b`) whose `b`-th iterate is `c mod 2^K`. -/
def blockCount (b α K c : ℕ) : ℕ :=
  ((Finset.range (2 ^ b)).filter fun r => tstep^[b] (r + α * 2 ^ b) % 2 ^ K = c).card

/-- **Node.**  Over each fixed block, `T^b n mod 2^K` is uniform as `b → ∞`.  At `α = 0` this is
`BeyondWordsUniform`. -/
def BlockWordsUniform : Prop :=
  ∀ α K c : ℕ, c < 2 ^ K →
    Tendsto (fun b : ℕ => (blockCount b α K c : ℝ) / 2 ^ b) atTop (𝓝 (1 / 2 ^ K))

/-- The residue `y` must have mod `2^K` for `y + α 3^a` to be `c`: `(2^K − 1) s ≡ −s`. -/
def shiftRes (K c α a : ℕ) : ℕ := (c + (2 ^ K - 1) * (α * 3 ^ a)) % 2 ^ K

theorem shiftRes_lt (K c α a : ℕ) : shiftRes K c α a < 2 ^ K :=
  Nat.mod_lt _ (by positivity)

/-- Subtracting `s` mod `M` is adding `(M − 1) s`: the arithmetic behind `shiftRes`. -/
theorem add_mod_eq_iff_mod_eq_shift (M y s c : ℕ) (hM : 0 < M) (hc : c < M) :
    (y + s) % M = c ↔ y % M = (c + (M - 1) * s) % M := by
  have hs : (M - 1) * s + s = M * s := by
    obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  constructor
  · intro h
    have h1 : y + s ≡ c [MOD M] := by
      show (y + s) % M = c % M
      rw [h, Nat.mod_eq_of_lt hc]
    have h2 : y + (M * s) ≡ c + (M - 1) * s [MOD M] := by
      rw [← hs, show y + ((M - 1) * s + s) = y + s + (M - 1) * s by ring]
      exact h1.add_right _
    have h3 : y + M * s ≡ y [MOD M] := by simp [Nat.ModEq]
    exact h3.symm.trans h2
  · intro h
    have h1 : y + s ≡ c + (M - 1) * s + s [MOD M] := Nat.ModEq.add_right s h
    have h2 : c + (M - 1) * s + s ≡ c [MOD M] := by
      rw [add_assoc, hs]
      simp [Nat.ModEq]
    have h3 := h1.trans h2
    have h4 : (y + s) % M = c % M := h3
    rwa [Nat.mod_eq_of_lt hc] at h4

/-- On the slice `a`, the block's residue test is the shifted residue test on `T^b r`. -/
theorem block_test_iff (b α K c a r : ℕ) (hc : c < 2 ^ K) (hr : r ∈ levelSet b a) :
    tstep^[b] (r + α * 2 ^ b) % 2 ^ K = c ↔ tstep^[b] r % 2 ^ K = shiftRes K c α a := by
  have ha : oddCount r b = a := (Finset.mem_filter.mp hr).2
  rw [tstep_iterate_add_mul_two_pow, ha]
  exact add_mod_eq_iff_mod_eq_shift (2 ^ K) _ _ c (by positivity) hc

/-- The centred block count is a sum over slices of centred residue indicators. -/
theorem sum_block_eq (b α K c : ℕ) (hc : c < 2 ^ K) :
    (blockCount b α K c : ℂ) - 2 ^ b * ((2 : ℂ) ^ K)⁻¹ =
      ∑ a ∈ Finset.range (b + 1), ∑ r ∈ levelSet b a,
        resInd K (shiftRes K c α a) (tstep^[b] r) := by
  have h1 : (blockCount b α K c : ℂ) - 2 ^ b * ((2 : ℂ) ^ K)⁻¹ =
      ∑ r ∈ Finset.range (2 ^ b),
        ((if tstep^[b] (r + α * 2 ^ b) % 2 ^ K = c then (1 : ℂ) else 0) - ((2 : ℂ) ^ K)⁻¹) := by
    unfold blockCount
    rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    push_cast
    ring
  rw [h1, sum_range_eq_sum_levelSet b (fun r =>
    (if tstep^[b] (r + α * 2 ^ b) % 2 ^ K = c then (1 : ℂ) else 0) - ((2 : ℂ) ^ K)⁻¹)]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun r hr => ?_
  unfold resInd
  simp only [block_test_iff b α K c a r hc hr]

/-- Central slices by the hypothesis, the others by their cardinality.  The observable may vary with
the slice, unlike in `norm_sum_range_le_of_levelSum`. -/
theorem norm_sum_slices_le (j : ℕ) (f : ℕ → ℕ → ℂ) (hf1 : ∀ a y, ‖f a y‖ ≤ 1) {ε : ℝ} (hε : 0 ≤ ε)
    (hslice : ∀ a, j ≤ 4 * a → a ≤ 11 * j / 20 →
      ‖∑ r ∈ levelSet j a, f a (tstep^[j] r)‖ ≤ ε * (levelSet j a).card) :
    ‖∑ a ∈ Finset.range (j + 1), ∑ r ∈ levelSet j a, f a (tstep^[j] r)‖ ≤
      ε * 2 ^ j + (outOddSet j).card := by
  let I := Finset.range (j + 1)
  let L := I.filter (fun a => j ≤ 4 * a ∧ a ≤ 11 * j / 20)
  let H := I.filter (fun a => 4 * a < j ∨ 11 * j / 20 < a)
  let S : ℕ → ℂ := fun a => ∑ r ∈ levelSet j a, f a (tstep^[j] r)
  have hLcard : ∑ a ∈ L, ((levelSet j a).card : ℝ) ≤ 2 ^ j := by
    calc
      ∑ a ∈ L, ((levelSet j a).card : ℝ) ≤
          ∑ a ∈ I, ((levelSet j a).card : ℝ) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => by positivity)
      _ = 2 ^ j := by
        exact_mod_cast sum_levelSet_card j
  have hlow : ‖∑ a ∈ L, S a‖ ≤ ε * 2 ^ j := by
    calc
      ‖∑ a ∈ L, S a‖ ≤ ∑ a ∈ L, ‖S a‖ := norm_sum_le _ _
      _ ≤ ∑ a ∈ L, ε * (levelSet j a).card := by
        exact Finset.sum_le_sum fun a ha => hslice a
          (Finset.mem_filter.mp ha).2.1 (Finset.mem_filter.mp ha).2.2
      _ = ε * ∑ a ∈ L, ((levelSet j a).card : ℝ) := by rw [Finset.mul_sum]
      _ ≤ ε * 2 ^ j := mul_le_mul_of_nonneg_left hLcard hε
  have hHcard : ∑ a ∈ H, ((levelSet j a).card : ℝ) = (outOddSet j).card := by
    exact_mod_cast sum_out_levelSet_card j
  have hcardS (a : ℕ) : ‖S a‖ ≤ (levelSet j a).card := by
    calc
      ‖S a‖ ≤ ∑ r ∈ levelSet j a, ‖f a (tstep^[j] r)‖ := norm_sum_le _ _
      _ ≤ ∑ _r ∈ levelSet j a, (1 : ℝ) := Finset.sum_le_sum fun r _ => hf1 _ _
      _ = (levelSet j a).card := by simp
  have hhigh : ‖∑ a ∈ H, S a‖ ≤ (outOddSet j).card := by
    calc
      ‖∑ a ∈ H, S a‖ ≤ ∑ a ∈ H, ‖S a‖ := norm_sum_le _ _
      _ ≤ ∑ a ∈ H, ((levelSet j a).card : ℝ) :=
        Finset.sum_le_sum fun a _ => hcardS a
      _ = (outOddSet j).card := hHcard
  have hpartition : ∑ a ∈ I, S a = (∑ a ∈ L, S a) + ∑ a ∈ H, S a := by
    have hs := Finset.sum_filter_add_sum_filter_not I
      (fun a => j ≤ 4 * a ∧ a ≤ 11 * j / 20) S
    rw [show I.filter (fun a => ¬(j ≤ 4 * a ∧ a ≤ 11 * j / 20)) = H by
      ext a
      simp [H]
      omega] at hs
    exact hs.symm
  change ‖∑ a ∈ I, S a‖ ≤ _
  rw [hpartition]
  exact (norm_add_le _ _).trans (add_le_add hlow hhigh)

/-- **Block words are uniform**, from slice character decay. -/
theorem blockWordsUniform_of_sliceCharDecay (h : SliceCharDecay) : BlockWordsUniform := by
  intro α K c hc
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hslices := eventually_norm_levelSum_le h 1 zero_le_one (ε / 2) (by positivity)
  rw [Filter.eventually_atTop] at hslices
  obtain ⟨J, hJ⟩ := hslices
  obtain ⟨M, hM⟩ := exists_nat_gt (200 / ε)
  refine ⟨max J (M + 1), fun j hj => ?_⟩
  have hjJ : J ≤ j := le_trans (le_max_left _ _) hj
  have hMj : M + 1 ≤ j := le_trans (le_max_right _ _) hj
  have hjpos : 0 < j := by omega
  have hjreal : 200 / ε < (j : ℝ) := by
    exact hM.trans_le (by exact_mod_cast (show M ≤ j by omega))
  have htailSmall : 100 / (j : ℝ) < ε / 2 := by
    have hcross : (200 : ℝ) < ε * j := by
      rwa [div_lt_iff₀' hε] at hjreal
    have hjrealpos : (0 : ℝ) < j := by exact_mod_cast hjpos
    rw [div_lt_iff₀ hjrealpos]
    nlinarith
  have hsum : ‖∑ a ∈ Finset.range (j + 1), ∑ r ∈ levelSet j a,
      resInd K (shiftRes K c α a) (tstep^[j] r)‖ ≤ ε / 2 * 2 ^ j + (outOddSet j).card :=
    norm_sum_slices_le j (fun a => resInd K (shiftRes K c α a))
      (fun a y => norm_resInd_le_one K _ y) (show 0 ≤ ε / 2 by positivity)
      (fun a ha1 ha2 => hJ j hjJ a ha1 ha2 _ (layeredWeight_resInd (shiftRes_lt K c α a) a))
  rw [← sum_block_eq j α K c hc] at hsum
  have hnormeq : ‖(blockCount j α K c : ℂ) - 2 ^ j * ((2 : ℂ) ^ K)⁻¹‖ =
      |(blockCount j α K c : ℝ) - 2 ^ j * ((2 : ℝ) ^ K)⁻¹| := by
    have hr := Complex.norm_real ((blockCount j α K c : ℝ) - 2 ^ j * ((2 : ℝ) ^ K)⁻¹)
    push_cast at hr
    rw [hr, Real.norm_eq_abs]
  rw [hnormeq] at hsum
  have hpowpos : (0 : ℝ) < 2 ^ j := by positivity
  have htail := outOddSet_ratio_le j hjpos
  have hdist : dist ((blockCount j α K c : ℝ) / 2 ^ j) (1 / 2 ^ K) =
      |(blockCount j α K c : ℝ) - 2 ^ j * ((2 : ℝ) ^ K)⁻¹| / 2 ^ j := by
    rw [Real.dist_eq, ← abs_of_pos hpowpos, ← abs_div, abs_of_pos hpowpos]
    congr 1
    field_simp
  rw [hdist]
  have hnorm :
      |(blockCount j α K c : ℝ) - 2 ^ j * ((2 : ℝ) ^ K)⁻¹| / 2 ^ j ≤
        ε / 2 + ((outOddSet j).card : ℝ) / 2 ^ j := by
    apply (div_le_iff₀ hpowpos).2
    calc
      _ ≤ (ε / 2) * 2 ^ j + ((outOddSet j).card : ℝ) := hsum
      _ = (ε / 2 + ((outOddSet j).card : ℝ) / 2 ^ j) * 2 ^ j := by
        field_simp
  linarith

/-- Unconditional, through the Sec7P node. -/
theorem blockWordsUniform : BlockWordsUniform :=
  blockWordsUniform_of_sliceCharDecay (sliceCharDecay_of_pascalDampingDecay pascalDampingDecay)

end CollatzMoonshot.Conjugacy
