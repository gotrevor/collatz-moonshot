/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.Bridge3

/-!
# Character decay of the slice laws (research note §11, 2026-10-24)

`Bridge3.lean` reduces `BiasDecays` to `TruncatedSyracMixing`, fine-scale mixing of the slice
laws.  The slice law at `(j, a)` is the law of `T^j r` over `r ∈ levelSet j a`: on `ℤ/3^a` it is
`Σ_k 3^{k−1} 2^{−T_k}` with `T_1 < … < T_a` a uniform `a`-subset of `[1, j]`.  This file states
the Tao-type input (the analogue of Tao 2019 Prop 1.17) and the edge from it.

**Why it should hold (Tao §7 transfers).**  Tao's proof of 1.17 conditions on the pair sums
`b_i = a_{2i−1} + a_{2i}` and bounds the character sum by `E_b ∏_i |f(x_i, b_i)|`
(`TaoCollatz.cexpect_pairing`).  Two facts carry this to slices.
* Given the pair sums, each pair of gaps of a uniform `a`-subset is uniform over its
  `b_i − 1` splits.  That is the same conditional law as under iid geometric gaps, for any gap
  parameter `p`.  So the slice character sum is bounded by `E_slice[∏ |f|]`.
* `∏ |f| ≥ 0` depends only on `b`, so `E_slice[∏ |f|] ≤ E_{Pascal(p)}[∏ |f|] / P(slice)`.  At
  `p = a/j`, `P(slice) ≍ j^{−1/2}`, a polynomial loss against Tao's `n^{−A}` for every `A`.

The remaining input is Tao's white-encounter bound (Prop 7.3, `renewal_white_encounters`) at
pair-sum law `Pascal(p)` in place of `Pascal(1/2)`, for `p ≤ 3/5`.  Heuristically, the walk
`(i, Σ b)` has drift `1/p` per step against the black-triangle slope `log₂ 3`, so the condition is
`p < 1/log₂ 3 ≈ 0.631`.  That is close to, but above, the slice entropy cutoff `a/j ≈ 0.609`
(`H(ρ) = ρ log₂ 3`), so the two need not coincide.  That heuristic is
unproved.  The same pairing argument shows the `θ`-twisted 1.17 (`TwistedSyracCharDecay`, note
§11) is a corollary of Tao's bound itself, because `e(θ T_n)` is `b`-measurable of modulus 1.

**Measured** (`experiments/conjugacy/slice_charfn.py`, an exact DP checked against brute-force
iterates for every `j ≤ 12` and every `a`): `sup_{3 ∤ ξ} |slice char| / #slice` along rays
`a/j = ρ`.  At `ρ = 1/2` it falls `0.031, 0.018, 0.0078, 0.0066` at `j = 16, 20, 24, 28`; at
`ρ = 0.6`, `0.37 → 0.055` from `j = 8` to `24`.  The control `ρ = 0.75` does not decay (`0.36`
to `0.66`).
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB

/-- The unnormalized characteristic function of the slice law at frequency `ξ`:
`Σ_{r ∈ levelSet j a} e(ξ · T^j r / 3^a)`. -/
noncomputable def sliceChar (j a ξ : ℕ) : ℂ :=
  ∑ r ∈ levelSet j a,
    Complex.exp (2 * Real.pi * Complex.I * ((ξ * tstep^[j] r : ℕ) : ℂ) / (3 ^ a : ℂ))

/-- **Node: slice character decay** (the sliced Tao 1.17).  For slices with `1/5 ≤ a/j ≤ 3/5`
and `ξ` coprime to `3`, the normalized slice character sum is `O_A(j^{−A})` for every `A`.  The
window is wider than `TruncatedSyracMixing`'s `[1/4, 11/20]`, so the sub-slices met in the §6
head/tail conditioning stay inside it with overwhelming probability.  Confidence 70% true, 35%
provable by redoing Tao §7 at `Pascal(p)` (the heuristic above).  Refutation probe:
`experiments/conjugacy/slice_charfn.py`. -/
def SliceCharDecay : Prop :=
  ∀ A > (0 : ℝ), ∃ C > (0 : ℝ), ∀ j a ξ : ℕ, j ≤ 5 * a → 5 * a ≤ 3 * j → ¬ 3 ∣ ξ →
    ‖sliceChar j a ξ‖ ≤ C * (j : ℝ) ^ (-A) * (levelSet j a).card

/-- **Edge: the sliced Tao 1.17 ⇒ 1.14.**  Proof owed (moonshot edge, not a treadmill target).
Tao §6 needs two structural facts about his family of laws, and both hold for slices.
* **Telescope across scales.**  Reducing a slice mod `3^k` gives a mixture of slices, because
  given `T_{k+1} = t` the first `k` elements are a uniform `k`-subset of `[1, t−1]`.  Oscillation
  is subadditive over mixtures (`TaoCollatz.osc_sum_le`).
* **Head/tail conditioning.**  Given the tail elements, the head is again a uniform subset of a
  shorter interval, so the conditioned character sum factors into slice character sums, as in
  `TaoCollatz.cond_char_factor`.
The slice recursion `μ_{n,s} = Σ_g C(s−g−1,n−2)/C(s−1,n−1) · (x ↦ 2^{−g}(1+3x))_* μ_{n−1,s−g}`
is checked exactly in `experiments/conjugacy/slice_recursion.py`. -/
theorem truncatedSyracMixing_of_sliceCharDecay (h : SliceCharDecay) : TruncatedSyracMixing := by
  sorry

end CollatzMoonshot.Conjugacy
