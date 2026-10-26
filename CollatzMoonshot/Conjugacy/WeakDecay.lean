/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Conjugacy.C1

/-!
# C1⁺: decay at every 3-adic scale (`WeakDecayOnZ3`), via over-precision slice sums

`WeakDecayOnZ3` (`Recursion.lean`) asks that every residue class of the *start* mod `3^k` carry
`o(2^m)` of the signed mass `Σ_{y < 2^m} (−1)^{T^m y}`.  Its `k = 0` case is C1 (`biasDecays`).

**The reduction (exact).**  Expand the class indicator in characters `e(η r / 3^k)` of `ℤ/3^k`.
`η = 0` is `bias / 3^k`, handled by C1.  For `η ≠ 0` split the starts into slices
`levelSet j a`.  On a slice, the iterate identity gives `3^a r = 2^j y − N_r` with
`y = T^j r < 3^a` and `N_r = 2^j T^j r − 3^a r`, so `e(η r / 3^k) = e(η (2^j y − N_r) / 3^{a+k})`
exactly.  Expand `g_η(y) = (−1)^y e(η 2^j y / 3^{a+k})` on `[0, 3^a)` in characters of `ℤ/3^a`;
as in `SliceFourier.lean`, `Σ_ξ |ĝ_η(ξ)| ≤ (2/π) ln 3^a + 1 = O(a)`.  Since `y ≡ 2^{−j} N_r`
(mod `3^a`), each frequency becomes `e(ζ N_r / 3^{a+k})` with `ζ = 3^k ξ 2^{−j} − η`.  Its
3-adic valuation is `v₃(η) < k` whatever `ξ` is.  So every term is an **over-precision** slice
sum `overPrecChar j a k' ζ'` with `k' = k − v₃(η) ≥ 1` and `3 ∤ ζ'`, on the *same* slice.  No
sub-slices appear.  Checked exactly against brute-force Collatz starts
(`experiments/conjugacy/c1plus_twistcheck.py`, six `(j, a, k, η)`, error `< 1e−10`).

**Why the over-precision sums decay (Sec7P absorbs it).**  In Tao's ordering,
`N_r · 2^{−j} mod 3^{a+k}` is the Syracuse sum at level `n = a + k` with only its first `a`
terms.  After Tao's pairing that is the `(7.5)` product at level `n` with the top `⌈k/2⌉` pair
factors deleted.  Each factor has modulus at most `1`, and `prod_fCond_le_dampingP` bounds the
full product by `exp(−ε³ · #white)`.  Whiteness at pair `q` depends only on the prefix
`pre b (q+1)`.  So padding `b` with `⌈k/2⌉` independent `Pascal(p)` coordinates costs at most a
factor `exp(ε³ ⌈k/2⌉)` against `renewal_white_encountersP`, which is a constant for fixed `k`.
The slice-to-Pascal step is `norm_sliceChar_le_mode_damping` (`SliceSeven.lean`) at level
`a + k` instead of `a`.

**Measured** (`experiments/conjugacy/overprec_charfn.py`, an exact DP over odd times; control equals brute
force): `max_{ζ ∈ {1,2,5,7,11}} |overPrecChar| / #slice` at `a/j = 0.45` is
`6.9e−7, 5.8e−12, 1.3e−18, 1.2e−33` for `k = 0` and `1.2e−4, 2.2e−8, 9.6e−16, 1.1e−30` for
`k = 3`, at `j = 40, 80, 160, 320`.  The rate is the same, and the constant is worse by about
`10^k`.  The rays `a/j = 0.3, 0.55` behave the same way.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB

/-- The over-precision slice character sum: `Σ_{r ∈ levelSet j a} e(ξ · N_r / 3^{a+k})`, where
`N_r = 2^j T^j r − 3^a r` is the numerator of the parity word (`tstep_iterate_identity`;
the natural subtraction is exact).  At `k = 0` it is the slice character sum at frequency
`ξ 2^j`. -/
noncomputable def overPrecChar (j a k ξ : ℕ) : ℂ :=
  ∑ r ∈ levelSet j a,
    Complex.exp (2 * Real.pi * Complex.I *
      ((ξ * (2 ^ j * tstep^[j] r - 3 ^ a * r) : ℕ) : ℂ) / (3 ^ (a + k) : ℂ))

/-- **Node: over-precision slice character decay.**  For each fixed extra precision `k`, on
the window `1/5 ≤ a/j ≤ 3/5` and for `ξ` coprime to `3`, the normalized sum is `O_{k,A}(j^{−A})`.
Its `k = 0` case is `SliceCharDecay` (up to the unit `2^j`).  Confidence 85% true, 70% that
it follows from Sec7P as sketched in the module docstring. -/
def OverPrecSliceCharDecay : Prop :=
  ∀ k : ℕ, ∀ A > (0 : ℝ), ∃ C > (0 : ℝ), ∀ j a ξ : ℕ, 1 ≤ j → j ≤ 5 * a → 5 * a ≤ 3 * j →
    ¬ 3 ∣ ξ → ‖overPrecChar j a k ξ‖ ≤ C * (j : ℝ) ^ (-A) * (levelSet j a).card

/-- **Edge: over-precision decay gives C1⁺.**  The reduction in the module docstring: characters
of the start class mod `3^k`, the `η = 0` term by `biasDecays`, slices outside
`[1/4, 11/20]` by the binomial tails (`outOddSet`, `Bridge3Aux.lean`), and on each main slice
the `O(a)` Fourier weight of `g_η` times `OverPrecSliceCharDecay` at `A = 3`. -/
theorem weakDecayOnZ3_of_overPrecSliceCharDecay (h : OverPrecSliceCharDecay) :
    WeakDecayOnZ3 := by
  sorry

/-- **Edge: Sec7P gives over-precision decay.**  The level-`(a + k)` version of
`norm_sliceChar_le_mode_damping`, with the top `⌈k/2⌉` pair factors bounded by `1`, then
`prod_fCond_le_dampingP` and `renewal_white_encountersP` (tao-collatz `Sec7P`) with
`⌈k/2⌉` padding coordinates, at a cost of `exp(ε³ ⌈k/2⌉)`. -/
theorem overPrecSliceCharDecay : OverPrecSliceCharDecay := by
  sorry

/-- **C1⁺ holds**: every residue class of the start mod `3^k` carries `o(2^m)` signed mass. -/
theorem weakDecayOnZ3 : WeakDecayOnZ3 :=
  weakDecayOnZ3_of_overPrecSliceCharDecay overPrecSliceCharDecay

end CollatzMoonshot.Conjugacy
