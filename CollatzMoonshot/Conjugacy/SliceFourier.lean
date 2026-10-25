/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.SliceDecay

/-!
# C1 directly from slice character decay (2026-10-25)

A shortcut past `TruncatedSyracMixing` and Tao's §6.  For `r ∈ levelSet j a`, `y = T^j r < 3^a` is a
least residue mod `M = 3^a`, so the slice's signed count is `Σ_y mass(y)·g(y)`, with `g(y) = (−1)^y`
on `[0, M)`.  Expand `g` in additive characters of `ℤ/M`:
`ĝ(ξ) = (1/M)·2/(1 + e(−ξ/M))`, so `|ĝ(ξ)| = 1/(M·|cos(πξ/M)|)`, because `M` is odd.

* **Weights.**  `Σ_ξ |ĝ(ξ)| = O(log M) = O(a)`.  The frequencies with `v₃(ξ) = k` carry weight
  `O(3^{−k}·(a − k + 1))`.
* **Frequencies `ξ = 3^k u`, `3 ∤ u`.**  Here `F(ξ) = Σ_r e(u·T^j r / 3^{a−k})` is the character sum of
  the slice reduced mod `3^{a−k}`.  Given the `(a−k+1)`-th odd time `t`, that is the slice `(t−1, a−k)`.
  So `F(ξ)` is a mixture of `sliceChar (t−1) (a−k) u`.  The sub-slice ratios concentrate at `a/j`, and
  the exceptional `t` have binomially small mass.
* **Bound.**  `|levelSign j a|/#slice ≤ 3^{−a} + O(a)·sup_{k ≤ K} C·j^{−A} + O(a·3^{−K})`.  Take
  `K = ⌈2 log₃ j⌉` and `A = 2`.  The slices with `a/j` outside `[1/4, 11/20]` are the binomial tails
  already bounded in `Bridge3.lean` (`outOddSet`).
* **Checked** (`experiments/conjugacy/fourier_bias_check.py`):
  - the identity `levelSign = Σ_ξ conj(ĝ(ξ))·F(ξ)` is exact against brute-force Collatz at
    `(j,a) = (8,3), (10,5), (12,6), (12,7)`;
  - `Σ|ĝ| ≈ (2/π) ln M + 1`;
  - the level-`k` weights fall by about `3×` per level.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB

/-- **Edge: slice character decay gives C1 directly** (no fine-scale mixing, no Tao §6).  Proof owed,
plan in the module docstring.  With `sliceCharDecay_of_pascalDampingDecay` (SliceSeven.lean) this
makes `BiasDecays` follow from `PascalDampingDecay` alone.  Confidence 75%. -/
theorem biasDecays_of_sliceCharDecay (h : SliceCharDecay) : BiasDecays := by
  sorry

end CollatzMoonshot.Conjugacy
