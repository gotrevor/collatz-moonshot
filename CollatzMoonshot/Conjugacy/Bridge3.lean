/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.Ladder

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
* **Node** `TruncatedSyracMixing`: fine-scale mixing of the slices, uniformly for `a ≤ 11j/20`.
  Above `≈ 0.63 j` the slice has about `3^a` atoms or fewer and cannot mix, and that range has
  binomially small mass.  Confidence 80% true.  The Tao-type input that should give it, the
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
  sorry

/-- **Edge (the reduction).**  The slice's signed count is at most its oscillation at any
coarser scale, plus the lift term.  Proof owed.  Sketch: compare with the uniform lift
`λ(y) = 3^{m−a}·mass(y mod 3^m)`; a class `c < 3^m` lifts to `c + 3^m t`, `t < 3^{a−m}`, whose
parities alternate, so `|Σ_y λ(y)(−1)^y| ≤ 3^{m−a}·#slice`; and
`|Σ_y (mass − λ)(y)(−1)^y| ≤ levelOsc`.  Uses `tstep_iterate_lt_three_pow` (support in
`range (3^a)`).  Verified numerically at every `j ≤ 20`, `a`, `m`. -/
theorem abs_levelSign_le (j a m : ℕ) (hma : m ≤ a) :
    |(levelSign j a : ℝ)| ≤ levelOsc j a m + (levelSet j a).card * ((3 : ℝ) ^ m / 3 ^ a) := by
  sorry

/-- **Node: truncated fine-scale mixing.**  Uniformly over slices with `a ≤ 11j/20`, the
oscillation at some scale `m` with `3^{a−m}` large is a vanishing fraction of the slice.  The
analogue of Tao 2019 Prop 1.14 for the uniform-subset law, which is the geometric-gap law
sliced at `T_a ≤ j < T_{a+1}`.  Below the entropy threshold `a/j ≈ 0.63` the slice has more
than `3^a` atoms; the cutoff `11/20` leaves margin.  Confidence 80% true, 30% provable by
adapting Tao's §5-7.  Refutation probe: `experiments/conjugacy/fsm_bridge.py` (the bound at
`a ≈ j/2` falls `0.375 → 0.291` from `j = 16` to `20`). -/
def TruncatedSyracMixing : Prop :=
  ∀ ε > (0 : ℝ), ∀ᶠ j in atTop, ∀ a ≤ 11 * j / 20, ∃ m ≤ a,
    levelOsc j a m ≤ ε * (levelSet j a).card ∧ (3 : ℝ) ^ m ≤ ε * 3 ^ a

/-- **Edge: truncated mixing gives C1.**  Proof owed: split `bias j` by `bias_eq_sum_levelSign`,
bound slices with `a ≤ 11j/20` by `abs_levelSign_le` and the node (total `≤ 2ε·2^j`), and the
rest by the binomial tail `Σ_{a > 11j/20} C(j,a) = o(2^j)`, using
`#levelSet j a = C(j,a)` (Terras). -/
theorem biasDecays_of_truncatedSyracMixing (h : TruncatedSyracMixing) : BiasDecays := by
  sorry

end CollatzMoonshot.Conjugacy
