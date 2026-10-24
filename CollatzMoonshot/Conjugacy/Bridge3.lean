/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.Bridge3Aux

/-!
# The 3-adic bridge for `BiasDecays` (research note §11, 2026-10-24)

§10.6 of the research note closed the bridge to Tao on the 2-adic mirror side.  This file opens
it on the 3-adic side.  The beyond-Terras sign `(−1)^{T^j r}` is a function of the Syracuse
value.  For `r < 2^j` with `a = oddCount r j`, `tstep_iterate_lt_three_pow` gives
`T^j r < 3^a`, and `tstep_iterate_eq_of_modEq` pins `T^j r` as a residue mod `3^a`.  That
residue is `Σ_k 3^{k−1} 2^{−T_k}`, with `T_k` the odd-step times counted back from `j`, and the
`T_k` form a uniform `a`-subset of `[1, j]` (Terras).  So the level-`a` slice of the bias is the
parity of the least residue of a truncated Syracuse variable.

* `levelSign j a`: the signed count of the slice.  Summing over `a` gives `bias j`
  (`bias_eq_sum_levelSign`).
* `levelOsc j a m`: Tao's oscillation `osc_{m,a}` of the slice, in counts.
* **Edge, proof owed** (`abs_levelSign_le`): `|levelSign j a| ≤ levelOsc j a m + #slice · 3^{m−a}`.
  Within each class mod `3^m`, the `3^{a−m}` lifts of a least residue alternate in parity
  (`3^m` is odd), so the uniform lift has signed mass at most `3^{m−a}` per unit.  Exact numerics
  (`experiments/conjugacy/fsm_bridge.py`) confirm it at every `j ≤ 20`, `a`, `m`.
* **Node** `TruncatedSyracMixing`: fine-scale mixing of the slices, uniformly for
  `j/4 ≤ a ≤ 11j/20`.  Above `≈ 0.609 j` (where `H(a/j) = (a/j)·log₂ 3`) the slice has about `3^a` atoms or fewer and cannot mix;
  below, small `a` cannot mix at all (at `a = 0` the scale condition `3^m ≤ ε·3^a` is `1 ≤ ε`).
  Both excluded ranges have binomially small mass.  Confidence 80% true.  The Tao-type input that should give it, the
  characteristic-function decay twisted by `e(θ T_n)` uniformly in `θ`, is measured in
  `experiments/conjugacy/twisted_charfn.py` (prose node `TwistedSyracCharDecay`, note §11).
* **Edge, proof owed** (`biasDecays_of_truncatedSyracMixing`): mixing plus the binomial tail
  `Σ_{a > 11j/20} C(j,a)/2^j → 0` gives `BiasDecays`.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB

/-- The starts `r < 2^j` with exactly `a` odd steps among the first `j`. -/
def levelSet (j a : ℕ) : Finset ℕ := (Finset.range (2 ^ j)).filter (fun r => oddCount r j = a)

/-- The signed count of the level-`a` slice: `Σ_{r ∈ levelSet j a} (−1)^{T^j r}`. -/
def levelSign (j a : ℕ) : ℤ :=
  ∑ r ∈ levelSet j a, (if tstep^[j] r % 2 = 0 then 1 else -1)

/-- The number of starts in the slice landing on `y` after `j` steps. -/
def levelMass (j a y : ℕ) : ℕ := ((levelSet j a).filter (fun r => tstep^[j] r = y)).card

/-- The number of starts in the slice whose `j`-th iterate is `≡ c (mod 3^m)`. -/
def levelClass (j a m c : ℕ) : ℕ :=
  ((levelSet j a).filter (fun r => tstep^[j] r % 3 ^ m = c)).card

/-- Tao's oscillation `osc_{m,a}` of the slice law on `ℤ/3^a`, in counts:
`Σ_{y < 3^a} |mass(y) − 3^{m−a} · mass(y mod 3^m)|`. -/
noncomputable def levelOsc (j a m : ℕ) : ℝ :=
  ∑ y ∈ Finset.range (3 ^ a),
    |(levelMass j a y : ℝ) - (3 : ℝ) ^ m / 3 ^ a * levelClass j a m (y % 3 ^ m)|

private theorem levelSign_cast_eq_sum_mass (j a : ℕ) :
    (levelSign j a : ℝ) =
      ∑ y ∈ Finset.range (3 ^ a), (levelMass j a y : ℝ) * paritySign y := by
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := levelSet j a) (t := Finset.range (3 ^ a)) (g := fun r => tstep^[j] r)
    (fun r hr => Finset.mem_range.2 (by
      have hlt := tstep_iterate_lt_three_pow
        (Finset.mem_range.1 (Finset.mem_filter.1 hr).1)
      simpa [(Finset.mem_filter.1 hr).2] using hlt))
    (fun r => paritySign (tstep^[j] r))
  calc
    (levelSign j a : ℝ) = ∑ r ∈ levelSet j a, paritySign (tstep^[j] r) := by
      simp [levelSign, paritySign_eq_ite]
    _ = ∑ y ∈ Finset.range (3 ^ a),
        ∑ r ∈ (levelSet j a).filter (fun r => tstep^[j] r = y),
          paritySign (tstep^[j] r) := hfiber.symm
    _ = ∑ y ∈ Finset.range (3 ^ a), (levelMass j a y : ℝ) * paritySign y := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [levelMass]
      calc
        ∑ r ∈ (levelSet j a).filter (fun r => tstep^[j] r = y), paritySign (tstep^[j] r) =
            ∑ _r ∈ (levelSet j a).filter (fun r => tstep^[j] r = y), paritySign y := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [(Finset.mem_filter.1 hr).2]
        _ = (((levelSet j a).filter (fun r => tstep^[j] r = y)).card : ℝ) * paritySign y := by
          simp

private theorem sum_levelClass (j a m : ℕ) :
    ∑ c ∈ Finset.range (3 ^ m), (levelClass j a m c : ℝ) = (levelSet j a).card := by
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := levelSet j a) (t := Finset.range (3 ^ m))
    (g := fun r => tstep^[j] r % 3 ^ m)
    (fun r _ => Finset.mem_range.2 (Nat.mod_lt _ (pow_pos (by omega) _)))
    (fun _ => (1 : ℝ))
  calc
    ∑ c ∈ Finset.range (3 ^ m), (levelClass j a m c : ℝ) =
        ∑ c ∈ Finset.range (3 ^ m),
          ∑ r ∈ (levelSet j a).filter (fun r => tstep^[j] r % 3 ^ m = c), (1 : ℝ) := by
      simp [levelClass]
    _ = ∑ _r ∈ levelSet j a, (1 : ℝ) := hfiber
    _ = (levelSet j a).card := by simp

private theorem abs_sum_levelClass_paritySign_le (j a m : ℕ) (hma : m ≤ a) :
    |∑ y ∈ Finset.range (3 ^ a),
        (levelClass j a m (y % 3 ^ m) : ℝ) * paritySign y| ≤ (levelSet j a).card := by
  have halt := sum_mod_three_pow_mul_paritySign
    (fun c => (levelClass j a m c : ℝ)) m (a - m)
  have hpow : 3 ^ a = 3 ^ m * 3 ^ (a - m) := by
    rw [← pow_add, Nat.add_sub_of_le hma]
  rw [hpow, halt]
  calc
    |∑ c ∈ Finset.range (3 ^ m), (levelClass j a m c : ℝ) * paritySign c| ≤
        ∑ c ∈ Finset.range (3 ^ m),
          |(levelClass j a m c : ℝ) * paritySign c| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ c ∈ Finset.range (3 ^ m), (levelClass j a m c : ℝ) := by
      apply Finset.sum_congr rfl
      intro c hc
      simp [abs_mul, abs_paritySign]
    _ = (levelSet j a).card := sum_levelClass j a m

/-! **Teeth test.**  Kernel-checked slice values.  The slices of `bias 4 = 6` are `1, 0, 4, 0, 1`,
and those of `bias 5 = 14` are `1, 1, 4, 4, 3, 1`.  The slice sizes are `C(j, a)` (Terras). -/

theorem levelSign_four : (List.range 5).map (levelSign 4) = [1, 0, 4, 0, 1] := by decide +kernel
theorem levelSign_five : (List.range 6).map (levelSign 5) = [1, 1, 4, 4, 3, 1] := by decide +kernel
theorem levelSet_card_five : (List.range 6).map (fun a => (levelSet 5 a).card) = [1, 5, 10, 10, 5, 1] := by
  decide +kernel

/-- The bias splits over the odd-step count.  (Proof owed: `Finset.sum_fiberwise` over
`oddCount r j ∈ range (j+1)`.) -/
theorem bias_eq_sum_levelSign (j : ℕ) :
    bias j = ∑ a ∈ Finset.range (j + 1), levelSign j a := by
  exact (sum_biasBand j).symm

/-- **Edge (the reduction).**  The slice's signed count is at most its oscillation at any
coarser scale, plus the lift term.  Proof owed.  Sketch: compare with the uniform lift
`λ(y) = 3^{m−a}·mass(y mod 3^m)`; a class `c < 3^m` lifts to `c + 3^m t`, `t < 3^{a−m}`, whose
parities alternate, so `|Σ_y λ(y)(−1)^y| ≤ 3^{m−a}·#slice`; and
`|Σ_y (mass − λ)(y)(−1)^y| ≤ levelOsc`.  Uses `tstep_iterate_lt_three_pow` (support in
`range (3^a)`).  Verified numerically at every `j ≤ 20`, `a`, `m`. -/
theorem abs_levelSign_le (j a m : ℕ) (hma : m ≤ a) :
    |(levelSign j a : ℝ)| ≤ levelOsc j a m + (levelSet j a).card * ((3 : ℝ) ^ m / 3 ^ a) := by
  let q : ℝ := (3 : ℝ) ^ m / 3 ^ a
  let D : ℝ := ∑ y ∈ Finset.range (3 ^ a),
    ((levelMass j a y : ℝ) - q * levelClass j a m (y % 3 ^ m)) * paritySign y
  let U : ℝ := ∑ y ∈ Finset.range (3 ^ a),
    (levelClass j a m (y % 3 ^ m) : ℝ) * paritySign y
  have hq : 0 ≤ q := div_nonneg (by positivity) (by positivity)
  have hdecomp :
      ∑ y ∈ Finset.range (3 ^ a), (levelMass j a y : ℝ) * paritySign y = D + q * U := by
    dsimp [D, U]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y hy
    ring
  have hD : |D| ≤ levelOsc j a m := by
    calc
      |D| ≤ ∑ y ∈ Finset.range (3 ^ a),
          |((levelMass j a y : ℝ) - q * levelClass j a m (y % 3 ^ m)) * paritySign y| := by
        exact Finset.abs_sum_le_sum_abs _ _
      _ = levelOsc j a m := by
        rw [levelOsc]
        apply Finset.sum_congr rfl
        intro y hy
        simp [q, abs_mul, abs_paritySign]
  have hU : |U| ≤ (levelSet j a).card := by
    exact abs_sum_levelClass_paritySign_le j a m hma
  have hqU : |q * U| ≤ (levelSet j a).card * q := by
    rw [abs_mul, abs_of_nonneg hq]
    nlinarith
  calc
    |(levelSign j a : ℝ)| =
        |∑ y ∈ Finset.range (3 ^ a), (levelMass j a y : ℝ) * paritySign y| := by
      rw [levelSign_cast_eq_sum_mass]
    _ = |D + q * U| := by rw [hdecomp]
    _ ≤ |D| + |q * U| := abs_add_le _ _
    _ ≤ levelOsc j a m + (levelSet j a).card * q := add_le_add hD hqU
    _ = levelOsc j a m + (levelSet j a).card * ((3 : ℝ) ^ m / 3 ^ a) := rfl

private theorem abs_levelSign_le_card (j a : ℕ) :
    |(levelSign j a : ℝ)| ≤ (levelSet j a).card := by
  calc
    |(levelSign j a : ℝ)| =
        |∑ r ∈ levelSet j a, paritySign (tstep^[j] r)| := by
      congr 1
      simp [levelSign, paritySign_eq_ite]
    _ ≤ ∑ r ∈ levelSet j a, |paritySign (tstep^[j] r)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = (levelSet j a).card := by simp [abs_paritySign]

private theorem sum_out_levelSet_card (j : ℕ) :
    ∑ a ∈ (Finset.range (j + 1)).filter
        (fun a => 4 * a < j ∨ 11 * j / 20 < a),
      (levelSet j a).card = (outOddSet j).card := by
  unfold levelSet
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  congr 1
  ext r
  simp [outOddSet, oddCount_le]

private theorem sum_levelSet_card (j : ℕ) :
    ∑ a ∈ Finset.range (j + 1), (levelSet j a).card = 2 ^ j := by
  unfold levelSet
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  have heq : (Finset.range (2 ^ j)).filter (fun r => oddCount r j ∈ Finset.range (j + 1)) =
      Finset.range (2 ^ j) := by
    ext r
    simp [oddCount_le]
  rw [heq, Finset.card_range]

private theorem outOddSet_ratio_le (j : ℕ) (hj : 0 < j) :
    ((outOddSet j).card : ℝ) / 2 ^ j ≤ 100 / (j : ℝ) := by
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ j) (by exact_mod_cast hj)).2
  have hm := outOddSet_card_mul_sq_le j
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  nlinarith

/-- **Node: truncated fine-scale mixing.**  Uniformly over slices with `j/4 ≤ a ≤ 11j/20`, the
oscillation at some scale `m` with `3^{a−m}` large is a vanishing fraction of the slice.  The
analogue of Tao 2019 Prop 1.14 for the uniform-subset law, which is the geometric-gap law
sliced at `T_a ≤ j < T_{a+1}`.  Below the entropy threshold `a/j ≈ 0.609` the slice has more
than `3^a` atoms; the cutoff `11/20` leaves margin.  Confidence 80% true, 30% provable by
adapting Tao's §5-7.  Refutation probe: `experiments/conjugacy/fsm_bridge.py` (the bound at
`a ≈ j/2` falls `0.375 → 0.291` from `j = 16` to `20`).  The lower cutoff `j ≤ 4a` is needed:
without it the node is false at `a = 0` (fixed 2026-10-24; the first version was refuted there,
which made the edge below vacuous). -/
def TruncatedSyracMixing : Prop :=
  ∀ ε > (0 : ℝ), ∀ᶠ j in atTop, ∀ a, j ≤ 4 * a → a ≤ 11 * j / 20 → ∃ m ≤ a,
    levelOsc j a m ≤ ε * (levelSet j a).card ∧ (3 : ℝ) ^ m ≤ ε * 3 ^ a

private theorem abs_bias_le_of_levelMixing (j : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (hmix : ∀ a, j ≤ 4 * a → a ≤ 11 * j / 20 → ∃ m ≤ a,
      levelOsc j a m ≤ ε * (levelSet j a).card ∧ (3 : ℝ) ^ m ≤ ε * 3 ^ a) :
    |(bias j : ℝ)| ≤ 2 * ε * 2 ^ j + (outOddSet j).card := by
  let I := Finset.range (j + 1)
  let L := I.filter (fun a => j ≤ 4 * a ∧ a ≤ 11 * j / 20)
  let H := I.filter (fun a => 4 * a < j ∨ 11 * j / 20 < a)
  have hslice (a : ℕ) (ha : j ≤ 4 * a ∧ a ≤ 11 * j / 20) :
      |(levelSign j a : ℝ)| ≤ 2 * ε * (levelSet j a).card := by
    obtain ⟨m, hma, hosc, hpow⟩ := hmix a ha.1 ha.2
    have hratio : (3 : ℝ) ^ m / 3 ^ a ≤ ε := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 3 ^ a)).2
      simpa [mul_comm] using hpow
    have hred := abs_levelSign_le j a m hma
    have hcard : (0 : ℝ) ≤ (levelSet j a).card := by positivity
    nlinarith
  have hLcard : ∑ a ∈ L, ((levelSet j a).card : ℝ) ≤ 2 ^ j := by
    calc
      ∑ a ∈ L, ((levelSet j a).card : ℝ) ≤
          ∑ a ∈ I, ((levelSet j a).card : ℝ) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => by positivity)
      _ = 2 ^ j := by
        exact_mod_cast sum_levelSet_card j
  have hlow : |∑ a ∈ L, (levelSign j a : ℝ)| ≤ 2 * ε * 2 ^ j := by
    calc
      |∑ a ∈ L, (levelSign j a : ℝ)| ≤
          ∑ a ∈ L, |(levelSign j a : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ L, 2 * ε * (levelSet j a).card := by
        exact Finset.sum_le_sum fun a ha => hslice a (Finset.mem_filter.1 ha).2
      _ = 2 * ε * ∑ a ∈ L, ((levelSet j a).card : ℝ) := by
        rw [Finset.mul_sum]
      _ ≤ 2 * ε * 2 ^ j := mul_le_mul_of_nonneg_left hLcard (by positivity)
  have hHcard : ∑ a ∈ H, ((levelSet j a).card : ℝ) = (outOddSet j).card := by
    exact_mod_cast sum_out_levelSet_card j
  have hhigh : |∑ a ∈ H, (levelSign j a : ℝ)| ≤ (outOddSet j).card := by
    calc
      |∑ a ∈ H, (levelSign j a : ℝ)| ≤
          ∑ a ∈ H, |(levelSign j a : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ H, ((levelSet j a).card : ℝ) := by
        exact Finset.sum_le_sum fun a _ => abs_levelSign_le_card j a
      _ = (outOddSet j).card := hHcard
  have hpartition :
      ∑ a ∈ I, (levelSign j a : ℝ) =
        (∑ a ∈ L, (levelSign j a : ℝ)) +
          ∑ a ∈ H, (levelSign j a : ℝ) := by
    have hs := Finset.sum_filter_add_sum_filter_not I
      (fun a => j ≤ 4 * a ∧ a ≤ 11 * j / 20) (fun a => (levelSign j a : ℝ))
    rw [show I.filter (fun a => ¬(j ≤ 4 * a ∧ a ≤ 11 * j / 20)) = H by
      ext a
      simp [H]
      omega] at hs
    exact hs.symm
  have hbias : (bias j : ℝ) = ∑ a ∈ I, (levelSign j a : ℝ) := by
    have hb := congrArg (fun z : ℤ => (z : ℝ)) (bias_eq_sum_levelSign j)
    simpa [I] using hb
  rw [hbias, hpartition]
  exact (abs_add_le _ _).trans (add_le_add hlow hhigh)

/-- **Edge: truncated mixing gives C1.**  Proof owed: split `bias j` by `bias_eq_sum_levelSign`,
bound slices with `j/4 ≤ a ≤ 11j/20` by `abs_levelSign_le` and the node (total `≤ 2ε·2^j`), and
the rest by the two binomial tails, `#{r : 4·oddCount r j < j ∨ 11j/20 < oddCount r j} ≤ 100·2^j/j`
(Chebyshev on `oddDeviation`).  Commit aadd4d6 proved the version for the old one-sided node. -/
theorem biasDecays_of_truncatedSyracMixing (h : TruncatedSyracMixing) : BiasDecays := by
  rw [BiasDecays, Metric.tendsto_atTop]
  intro ε hε
  have hmix := h (ε / 4) (by positivity)
  rw [Filter.eventually_atTop] at hmix
  obtain ⟨J, hJ⟩ := hmix
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
  have habs := abs_bias_le_of_levelMixing j (show 0 ≤ ε / 4 by positivity) (hJ j hjJ)
  have hpowpos : (0 : ℝ) < 2 ^ j := by positivity
  have hnorm :
      |(bias j : ℝ)| / 2 ^ j ≤ ε / 2 + ((outOddSet j).card : ℝ) / 2 ^ j := by
    apply (div_le_iff₀ hpowpos).2
    calc
      |(bias j : ℝ)| ≤
          2 * (ε / 4) * 2 ^ j + ((outOddSet j).card : ℝ) := habs
      _ = (ε / 2 + ((outOddSet j).card : ℝ) / 2 ^ j) * 2 ^ j := by
        field_simp
        <;> ring
  have htail := outOddSet_ratio_le j hjpos
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hpowpos]
  linarith

end CollatzMoonshot.Conjugacy
