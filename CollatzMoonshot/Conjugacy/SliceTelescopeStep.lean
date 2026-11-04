/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.SliceTelescope

/-!
# SEC6S lap 1 (second half): the one-step telescope for slice oscillations

Tao's (6.1) for the sliced laws (`SEC6S-PLAN.md` §2(b)): for `m ≤ a`,

    levelOsc j (a+1) m ≤ levelOsc j (a+1) a + Σ_{t=1}^{j} levelOsc (t − 1) a m.

Proof: for `y < 3^{a+1}` put `ȳ = y % 3^a`; then `y % 3^m = ȳ % 3^m` and
`3^m/3^{a+1} = (1/3)·(3^m/3^a)`, so the pointwise triangle inequality gives
`|mass y − 3^m/3^{a+1}·class_m (y % 3^m)| ≤ |mass y − 3^a/3^{a+1}·class_a ȳ| + (1/3)|class_a ȳ − 3^m/3^a·class_m (ȳ % 3^m)|`
with `mass = levelMass j (a+1)`, `class_k = levelClass j (a+1) k`.  Summing over `y < 3^{a+1}`:
the first sum is `levelOsc j (a+1) a`; in the second each `ȳ < 3^a` has exactly three lifts
`ȳ + i·3^a`, `i < 3`, which cancels the `1/3`.  Now `class_a ȳ = Σ_t levelMass (t−1) a ȳ`
(`levelClass_eq_sum_levelMass` at `a' = a`, weights `C(j−t, 0) = 1`) and
`class_m c = Σ_t levelClass (t−1) a m c` (the same Pascal induction, `levelClass_succ_pascal`,
on the class counts), so the remaining sum is `Σ_ȳ |Σ_t (levelMass (t−1) a ȳ − 3^m/3^a·levelClass (t−1) a m (ȳ % 3^m))|`,
which is `≤ Σ_t levelOsc (t−1) a m` by `|Σ| ≤ Σ|·|` and swapping the sums.  Exact check:
`experiments/conjugacy/telescope.py` (364 triples, `j ≤ 12`, 0 violations; dropping the first
term fails 332/364; the bound is attained).
-/

namespace CollatzMoonshot.Conjugacy

open Finset CollatzMoonshot.FrontB

/-- **Frozen.**  One-step telescope for the slice oscillations (Tao's (6.1) for slices): for
`m ≤ a`, `osc_{m,a+1}` of the slice `(j, a+1)` is at most its last-scale oscillation `osc_{a,a+1}`
plus the sum of the `osc_{m,a}` of the shorter slices `(t − 1, a)`, `1 ≤ t ≤ j`. -/
theorem levelOsc_succ_le_telescope (j a m : ℕ) (hm : m ≤ a) :
    levelOsc j (a + 1) m ≤
      levelOsc j (a + 1) a + ∑ t ∈ Finset.Icc 1 j, levelOsc (t - 1) a m := by
  sorry

end CollatzMoonshot.Conjugacy
