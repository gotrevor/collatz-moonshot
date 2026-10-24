/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.Fourier

/-!
# The Fourier coefficient at one frequency is a lattice sum

The mirror recursion `fourierCoeff_succ` sends a frequency `f` only to `f` and `f/3`.  So the
coefficient `G_j(ξ)` at one odd frequency involves only the frequencies `ξ · 3^{−m}`, `m ≤ j`,
at each level: a lattice of size `~ j²`, not the `2^{j+1}`-term sum.  Since
`1 − 4u ≡ −3⁻¹`, the phase on the step from level `n + 1` to `n` at orbit position `m` is
`e(−⟨ξ · 3^{−(m+1)}⟩_{n+2})`, where `⟨x⟩_k = (x mod 2^k)/2^k` reads the top bits of the
`k`-bit truncation of the `2`-adic number `x`.  Unrolled: `G_j(ξ)` is the expectation, over a
uniform random subset `S = {s₁ > s₂ > ⋯}` of `{0, …, j−1}`, of `e(−Σ_t ⟨ξ · 3^{−t}⟩_{s_t + 2})`,
a multiplicative functional of a simple random walk in the space-time environment of the
`2`-adic digits of `ξ · 3^{−t}`.  So `LowFreqDecay` is a weighted equidistribution statement
about binary digits of powers of `3`.

Evidence with control (`experiments/conjugacy/latticedp.py`): the lattice recursion reproduces
the FFT coefficients at every `j ≤ 18` for ten frequencies each, maximum error `2.6e-16`;
**teeth**: with the phase deleted the error is `1.23`.  The recursion makes the coefficients
cheap: `latticerun.py` measures them to `j = 4000`.
-/

namespace CollatzMoonshot.Conjugacy

/-- The phase on the lattice step from level `n + 1` to level `n` at orbit position `m`:
`e(−⟨ξ · 3^{−(m+1)}⟩_{n+2})`. -/
noncomputable def latticePhase (ξ n m : ℕ) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I *
    ((((3 : ZMod (2 ^ (n + 2)))⁻¹ ^ (m + 1) * ξ).val : ℕ) : ℂ) / 2 ^ (n + 2)))

/-- The lattice values: `latticeCoeff ξ n m = G_n(ξ · 3^{−m})` (`fourierCoeff_eq_latticeCoeff`). -/
noncomputable def latticeCoeff (ξ : ℕ) : ℕ → ℕ → ℂ
  | 0, _ => 1
  | n + 1, m => (1 / 2 : ℂ) * latticeCoeff ξ n m +
      (1 / 2 : ℂ) * latticePhase ξ n m * latticeCoeff ξ n (m + 1)

/-- **The lattice formula.**  For odd `ξ`, the coefficient at the frequency `ξ · 3^{−m}` (read
mod `2^(n+1)`) is the lattice value.

Proof sketch.  Induction on `n`.  At `n = 0`, `G_0 = 1` at every odd frequency, and
`ξ · 3^{−m}` is odd.  The step is `fourierCoeff_succ` with `u = 3⁻¹`, using
`u · (ξ 3^{−m}) = ξ 3^{−(m+1)}`, `ξ 3^{−m} (1 − 4u) ≡ −ξ 3^{−(m+1)} (mod 2^(n+2))` (because
`3 (1 − 4u) ≡ −1`), `1`-periodicity of `e`, and periodicity of `fourierCoeff n` in the
frequency mod `2^(n+1)`.  Confidence 97% (the numerics above match it to `2.6e-16`). -/
theorem fourierCoeff_eq_latticeCoeff (ξ n m : ℕ) (hξ : Odd ξ) :
    fourierCoeff n (((3 : ZMod (2 ^ (n + 1)))⁻¹ ^ m * ξ).val) = latticeCoeff ξ n m := by
  sorry

/-- **Corollary at `m = 0`.**  `G_j(ξ) = latticeCoeff ξ j 0` for odd `ξ`. -/
theorem fourierCoeff_eq_latticeCoeff_zero (ξ j : ℕ) (hξ : Odd ξ) :
    fourierCoeff j ξ = latticeCoeff ξ j 0 := by
  sorry

end CollatzMoonshot.Conjugacy
