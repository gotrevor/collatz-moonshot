/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.SliceDecay

/-!
# Tao 2019 §7 at the pair-sum law `Pascal(p)`: the input for `SliceCharDecay`

`SliceDecay.lean` (personal-c5) reduces `BiasDecays` to `SliceCharDecay`, the sliced Tao 1.17.
Two facts carry Tao's §7 pairing to slices: given the pair sums, each pair of gaps of a uniform
`a`-subset is uniform over its splits (the same conditional law as under iid `Geom(p)` gaps, for
every `p`), and conditioning on the slice event `T_a ≤ j < T_{a+1}` reweights each gap vector by
`(1−p)^{j − T_a} ≤ 1`.  So the normalised slice character sum is at most
`damping a p ξ / P_p(slice)`, and at `p = a/j` the slice probability is `≍ j^{−1/2}`.  What is
needed is therefore Tao's (7.5) damping bound at `Pascal(p)`, **uniformly in `p`** on the window.

**Tao's proof transfers at the paper level** (read from Tao 2019 §7, research note §12–§11 and
`experiments/conjugacy/BRIDGE3-SLICE-RECURSION.md`).  The deterministic half (the field
`θ(j, l)`, Lemma 7.4's triangles, the white points) does not involve `p`.  The pair factor
`|f(x, 3)| = |cos πθ|` (Lemma 7.2) does not involve `p`.  The holding time becomes
`Hold = (1, 3) + Σ_{i < K−1} (1, b′_i)` with `K ~ Geom(q)`, `q = P(b = 3) = 2p²(1−p)`, and `b′`
the pair sum conditioned `≠ 3`; so `E Hold = (1/q)·(1, 2/p)` (Tao's `(4, 16)` at `p = 1/2`), with
the same support, hence the same aperiodicity, and exponential tails.  Lemma 7.7's first-passage
location is `j ≈ s·p/2` instead of `s/4`.  Every slope-sensitive step (Case 2 after (7.50),
"`¼ log 9 < log 2`"; Case 3 after (7.52), "`0.8 > ¼ log 9/log 2`"; the line after (7.64)) reduces
to the single condition `p log₂ 3 < 1` (personal-c5: it is slice contraction `3^a < 2^j`), with
Tao's `0.8, 0.9` replaced by thresholds strictly between `p log₂ 3` and `1`.  At `p = 3/5`,
`p log₂ 3 = 0.951`.  The constants depend continuously on `p`, hence are uniform on `[1/5, 3/5]`.

**Measured** (`experiments/conjugacy/pascal_damping.py`, personal-c5, exact DP checked against
brute force): `sup_ξ damping` at `n = 4, 8, 12, 14` is `0.655, 0.546, 0.478, 0.452` at `p = 0.6`
and `0.310 … 0.071` at `p = 0.35`, with a steady per-2-step ratio for `p ≤ 0.65` (`0.945` at
`p = 0.6`), drifting toward `1` at `p = 0.7, 0.8`.  The refutation probe for the node below.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology

/-- `e(−x/3^n)` for `x ∈ ℤ/3^n`. -/
noncomputable def charZ (n : ℕ) (x : ZMod (3 ^ n)) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I * ((x.val : ℕ) : ℂ) / 3 ^ n))

/-- Tao's pair factor (7.4): `f(x, b) = (b−1)⁻¹ Σ_{a=1}^{b−1} e(−x(2^a + 3)/3^n)`, the conditional
expectation of the pair's character given its sum `b` (uniform over the `b − 1` splits, for any
gap law `Geom(p)`). -/
noncomputable def fPair (n : ℕ) (x : ZMod (3 ^ n)) (b : ℕ) : ℂ :=
  ((b : ℂ) - 1)⁻¹ * ∑ a ∈ Finset.Icc 1 (b - 1), charZ n (x * (2 ^ a + 3))

/-- The argument `x_j = ξ · 3^{2j} · 2^{−s}` at prefix pair-sum `s` (0-indexed `j`). -/
noncomputable def xArg (n ξ j s : ℕ) : ZMod (3 ^ n) :=
  (ξ : ZMod (3 ^ n)) * 3 ^ (2 * j) * (2 : ZMod (3 ^ n))⁻¹ ^ s

/-- The pair-sum law `Pascal(p)`: the sum of two iid `Geom(p)` gaps on `{1, 2, …}`,
`P(b) = (b−1) p² (1−p)^{b−2}` for `b ≥ 2`. -/
noncomputable def pascalWeight (p : ℝ) (b : ℕ) : ℝ :=
  if 2 ≤ b then ((b : ℝ) - 1) * p ^ 2 * (1 - p) ^ (b - 2) else 0

/-- **Tao's (7.5) damping at `Pascal(p)`**:
`E_{b ~ Pascal(p)^{⌊n/2⌋}} ∏_j |f(x_j, b_j)|` with `x_j = ξ 3^{2j} 2^{−(b_0 + ⋯ + b_j)}`.
At `p = 1/2` this is the quantity Tao bounds by `n^{−A}` (his Props 7.1, 7.3). -/
noncomputable def pascalDamping (n : ℕ) (p : ℝ) (ξ : ℕ) : ℝ :=
  ∑' b : Fin (n / 2) → ℕ, (∏ j, pascalWeight p (b j)) *
    ∏ j : Fin (n / 2),
      ‖fPair n (xArg n ξ j (∑ i ∈ Finset.univ.filter (fun i : Fin (n / 2) => i ≤ j), b i)) (b j)‖

/-- **Node: Tao's damping bound at `Pascal(p)`, uniformly on `p ∈ [1/5, 3/5]`.**  The analogue of
Tao 2019 Prop 7.1 (via 7.3) with the pair-sum law tilted.  Evidence: the paper-level transfer in
the module docstring (every `p`-sensitive step reduces to `p log₂ 3 < 1`), and the measured decay.
Confidence 80% true; 60% that the `tao-collatz` §7 Lean proof generalises by re-parametrising its
probabilistic half (`HoldBasics`, `HoldLocal`, `Holding`, `FpLocation`, `BlackEdge`, `Case3`,
`ManyTriangles`, `Monotone`, `Unroll`, `Reduction`, `Bridge`) with the deterministic half
(`Setup`, `Triangles`, `White`) unchanged. -/
def PascalDampingDecay : Prop :=
  ∀ A > (0 : ℝ), ∃ C > (0 : ℝ), ∀ p : ℝ, 1 / 5 ≤ p → p ≤ 3 / 5 → ∀ n ξ : ℕ, 1 ≤ n → ¬ 3 ∣ ξ →
    pascalDamping n p ξ ≤ C * (n : ℝ) ^ (-A)

/-- **Edge: the uniform damping bound gives slice character decay.**  Sketch (personal-c5's two
facts, `SliceDecay.lean`): write the slice law at `(j, a)` as `Σ_k 3^{k−1} 2^{−T_k} mod 3^a` with
`T` the partial sums of a uniform `a`-subset of `[1, j]`; that is iid `Geom(p)` gaps conditioned
on `T_a ≤ j < T_{a+1}`, for any `p`; pair the gaps, condition on the pair sums (uniform splits,
Tao 7.4–7.5), and bound the slice expectation of `∏|f| ≥ 0` by
`pascalDamping a p ξ / P_p(T_a ≤ j < T_{a+1})`; take `p = a/j ∈ [1/5, 3/5]`, where a local limit
theorem gives `P_p(slice) ≥ c j^{−1/2}` uniformly.  So `|sliceChar| / #slice ≤ C' j^{1/2} a^{−A}`,
and `a ≥ j/5`.  Confidence 85%. -/
theorem sliceCharDecay_of_pascalDampingDecay (h : PascalDampingDecay) : SliceCharDecay := by
  sorry

end CollatzMoonshot.Conjugacy
