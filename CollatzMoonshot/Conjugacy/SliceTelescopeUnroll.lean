/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.SliceTelescopeStep

/-!
# SEC6S lap 1 (third part): the unrolled multi-scale telescope

Iterating the one-step telescope `levelOsc_succ_le_telescope` from scale `a` down to `m`
(`SEC6S-PLAN.md` §2(b), Tao's unrolled (6.1)): for `m < a`,

    levelOsc j a m ≤ levelOsc j a (a−1)
                     + Σ_{k=m+1}^{a−1} Σ_{j' < j} C(j − j' − 1, a − k − 1) · levelOsc j' k (k−1).

The weight `C(j − j' − 1, s − 1)` counts the chains `j > ℓ₁ > ⋯ > ℓ_{s−1} > j'` of slice lengths
produced by `s = a − k` applications of the one-step rule (each step replaces a length `ℓ` by some
`t − 1 < ℓ`).  Proof: induction on `a` from `a = m + 1` (where the sum is empty and the bound is an
equality); the step applies `levelOsc_succ_le_telescope j a m`, then the hypothesis at each
`(t − 1, a, m)`, and sums: the `levelOsc (t−1) a (a−1)` terms are the new `k = a` layer (weight
`C(j − j' − 1, 0) = 1`), and the inner layers collapse by the hockey stick
`Σ_{u ≤ n} C(u, r) = C(n + 1, r + 1)` applied to `Σ_{t = j'+2}^{j} C(t − 2 − j', a − k − 1) = C(j − j' − 1, a − k)`.
Exact check: `experiments/conjugacy/unroll.py` (286 triples, `j ≤ 11`, 0 violations; dropping the
first term fails 112/286; the weight `C(j − j' − 1, a − k)` fails 100/286; the bound is attained).
-/

namespace CollatzMoonshot.Conjugacy

open Finset CollatzMoonshot.FrontB

/-- **Frozen.**  The unrolled multi-scale telescope for the slice oscillations: for `m < a`,
`osc_{m,a}` of the slice `(j, a)` is at most its top-scale oscillation plus the binomially weighted
top-scale oscillations of the shorter slices at every intermediate scale. -/
theorem levelOsc_le_unrolled (j a m : ℕ) (hm : m < a) :
    levelOsc j a m ≤ levelOsc j a (a - 1) +
      ∑ k ∈ Finset.Ico (m + 1) a, ∑ j' ∈ Finset.range j,
        ((j - j' - 1).choose (a - k - 1) : ℝ) * levelOsc j' k (k - 1) := by
  sorry

end CollatzMoonshot.Conjugacy
