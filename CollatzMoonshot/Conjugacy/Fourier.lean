/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.Ladder

/-!
# The beyond-Terras sign on the Fourier side: decay of fixed frequencies suffices

The beyond-Terras sign `g_j(r) = (−1)^{tstep^[j] r}` depends only on `r mod 2^(j+1)` and is
`2^j`-antiperiodic, so its Fourier coefficients
`G_j(ξ) = 2^{−(j+1)} Σ_{r < 2^(j+1)} g_j(r) e(ξ r / 2^(j+1))` (`fourierCoeff`) live on odd `ξ`.
The research note (§10.6) gave a weighted sufficient condition for `BiasDecays`; this module
replaces it by a weaker, pointwise one and records the recursion it lives on.

* **The reduction** (`bias_div_le_lowFreq_add_tail`): for every `K ≥ 1`,
  `|bias j| / 2^j ≤ Σ_{odd ξ ≤ K} 2‖G_j(ξ)‖/ξ + √(2/K)`.  Parseval (`Σ_ξ ‖G_j(ξ)‖² = 1`,
  `sum_norm_sq_fourierCoeff`) controls every frequency above `K` at once.
* **Pointwise decay suffices** (`LowFreqDecay`, `biasDecays_of_lowFreqDecay`): if each fixed odd
  frequency's coefficient tends to `0`, then `BiasDecays`.  The node needs no uniformity in `ξ`,
  which matters: on the chain `ξ = 3^k` the coefficients rise before they fall (§10.6's
  resonance), so a uniform statement is false at the scale `1/j`.
* **The mirror recursion** (`fourierCoeff_succ`): `G_{j+1}(ξ) = ½ G_j(ξ) + ½ e(ξ(1−4u)/2^{j+2})
  G_j(uξ)` with `3u ≡ 1 (mod 2^(j+1))`, the parity split `g_{j+1}(2s) = g_j(s)`,
  `g_{j+1}(2s+1) = g_j(3s+2)`.
* **Magnitudes alone prove nothing.**  The recursion bounds `‖G_{j+1}(ξ)‖` by the average of
  `‖G_j(ξ)‖` and `‖G_j(uξ)‖`; starting from `‖G_0‖ = 1` on its one odd class this gives only
  `‖G_j‖ ≤ 1`.  So a proof of `LowFreqDecay` must use the phases: it is an exponential-sum
  statement, not a positivity one.  (Measured, `experiments/conjugacy/wbranch.py`: one level of
  the triangle inequality does contract the weighted sum, by `0.88–0.96` for `j ≥ 11`, but only
  because the actual `‖G_j‖` already carries earlier cancellation.)
* **Closure under `ξ ↦ ξ/3`** (`TwoAdicFreqDecay`, `lowFreqDecay_of_twoAdicFreqDecay`):
  unrolling the first branch, `‖G_j(ξ)‖ ≤ Σ_m 2^{−m} ‖G_{j−m}(ξ/3)‖ + 2^{−j}` with `ξ/3` read in
  `ℤ₂`, so the natural node is decay at every fixed odd 2-adic frequency, a family closed under
  division by `3` that contains the integer frequencies.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord

/-- The beyond-Terras sign `(−1)^{tstep^[j] r}` as a real number. -/
def beyondSign (j r : ℕ) : ℝ := if tstep^[j] r % 2 = 0 then 1 else -1

/-- The Fourier coefficient `G_j(ξ) = 2^{−(j+1)} Σ_{r < 2^(j+1)} g_j(r) e(ξ r / 2^(j+1))` of the
beyond-Terras sign on `ℤ / 2^(j+1)`. -/
noncomputable def fourierCoeff (j ξ : ℕ) : ℂ :=
  ((2 : ℂ) ^ (j + 1))⁻¹ * ∑ r ∈ Finset.range (2 ^ (j + 1)),
    (beyondSign j r : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ξ * r / 2 ^ (j + 1))

/-- The Fourier coefficient at level `j` is periodic in the frequency with period `2^(j+1)`. -/
theorem fourierCoeff_add_period (j ξ k : ℕ) :
    fourierCoeff j (ξ + 2 ^ (j + 1) * k) = fourierCoeff j ξ := by
  unfold fourierCoeff
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  push_cast
  rw [show
      2 * Real.pi * Complex.I * (ξ + 2 ^ (j + 1) * k) * r / 2 ^ (j + 1) =
        2 * Real.pi * Complex.I * ξ * r / 2 ^ (j + 1) +
          ((k * r : ℕ) : ℂ) * (2 * Real.pi * Complex.I) by
    push_cast
    field_simp]
  rw [Complex.exp_add, Complex.exp_periodic.nat_mul_eq]
  simp

/-- **Parseval.**  The sign has unit modulus, so the squared Fourier coefficients over one period
sum to `1`.  Orthogonality of the characters `r ↦ e(ξ r / 2^(j+1))` on `ℤ / 2^(j+1)`. -/
theorem sum_norm_sq_fourierCoeff (j : ℕ) :
    ∑ ξ ∈ Finset.range (2 ^ (j + 1)), ‖fourierCoeff j ξ‖ ^ 2 = 1 := by
  sorry

/-- **The reduction.**  For every `K ≥ 1`,
`|bias j| / 2^j ≤ Σ_{odd ξ ≤ K} 2 ‖G_j(ξ)‖ / ξ + √(2/K)`.

Proof.  Write `n = 2^(j+1)`.  The window `[0, 2^j)` is half a period, so by Parseval
`bias j = n Σ_ξ G_j(ξ) · conj(H(ξ))` with `H` the Fourier coefficient of the window's indicator;
`|H(ξ)| = n⁻¹ / |sin(π ξ / n)|` at odd `ξ`, and `G_j` vanishes at even `ξ` by antiperiodicity.
So `|bias j| / 2^j ≤ 2^{−j} Σ_{odd ξ} ‖G_j(ξ)‖ / |sin(π ξ / n)|`.  Take signed representatives
`ξ ∈ (−n/2, n/2]`; Jordan's inequality gives `2^{−j} / |sin(π ξ / n)| ≤ 1/|ξ|`.  The frequencies
with `|ξ| ≤ K` contribute at most `Σ_{odd ξ ≤ K} (‖G_j(ξ)‖ + ‖G_j(−ξ)‖)/ξ`, and
`‖G_j(−ξ)‖ = ‖G_j(ξ)‖` because the sign is real.  The rest is at most
`2^{−j} (Σ ‖G_j‖²)^{1/2} (Σ_{|ξ| > K} (n / 2|ξ|)²)^{1/2} ≤ 2^{−j} · 1 · n / √(2K) = √(2/K)`
by Cauchy–Schwarz, Parseval and `Σ_{m > K} m⁻² ≤ 1/K`.

Evidence with control (`experiments/conjugacy/lowfreq.py`, `j ≤ 24`, `K` up to `729`): the
inequality holds with positive slack at every `(j, K)`, and with the `√(2/K)` term deleted it
fails from `j = 13` on, so the tail term is load-bearing.  Confidence 97%. -/
theorem bias_div_le_lowFreq_add_tail (j K : ℕ) (hK : 1 ≤ K) :
    |(bias j : ℝ)| / 2 ^ j ≤
      (∑ ξ ∈ (Finset.range (K + 1)).filter Odd, 2 * ‖fourierCoeff j ξ‖ / ξ) +
        Real.sqrt (2 / K) := by
  sorry

/-- **Node: decay of every fixed odd frequency.**  For each fixed odd `ξ`, the Fourier coefficient
`G_j(ξ)` of the beyond-Terras sign tends to `0` as `j → ∞`.

Evidence with control (`experiments/conjugacy/lowfreq.py`, `j ≤ 24`): off the powers of `3`,
`‖G_j(ξ)‖ · 2^{j/2}` stays in `[0.04, 2.8]` for `ξ = 1, 3, 5, 7, 15`, i.e. square-root
cancellation.  On the chain `ξ = 3^k` the normalised value rises and then falls (`ξ = 27` peaks
at `7.8` at `j = 13`, `ξ = 81` at `16.9` at `j = 22`), still decaying for each fixed `ξ`.  The
probe's control is §10.6's weighted sum `W_j`, reproduced to three figures at
`j = 8, 10, …, 22` by `wbranch.py` from the same coefficients.  Implies `BiasDecays`
(`biasDecays_of_lowFreqDecay`).  Confidence 85%. -/
def LowFreqDecay : Prop :=
  ∀ ξ : ℕ, Odd ξ → Tendsto (fun j => ‖fourierCoeff j ξ‖) atTop (𝓝 0)

/-- **Edge: pointwise decay of the fixed frequencies implies `BiasDecays`.**  Given `ε > 0`,
choose `K` with `√(2/K) < ε/2`; the finitely many odd `ξ ≤ K` have `2 ‖G_j(ξ)‖ / ξ → 0`, so
their sum is eventually below `ε/2`; conclude by `bias_div_le_lowFreq_add_tail`.  Confidence
99% given the reduction. -/
theorem biasDecays_of_lowFreqDecay (h : LowFreqDecay) : BiasDecays := by
  sorry

/-- **The mirror recursion.**  With `3u ≡ 1 (mod 2^(j+1))`,
`G_{j+1}(ξ) = ½ G_j(ξ) + ½ e(ξ (1 − 4u) / 2^(j+2)) G_j(u ξ)`.

Proof.  Split `r < 2^(j+2)` by parity.  `tstep (2s) = s`, so the even half is
`½ G_j(ξ)` (with `e(ξ · 2s / 2^(j+2)) = e(ξ s / 2^(j+1))`).  `tstep (2s+1) = 3s + 2`; put
`t = 3s + 2 mod 2^(j+1)`, so `s ≡ u(t − 2)` and `2s + 1 ≡ 2ut − 4u + 1 (mod 2^(j+2))`, and the
odd half is `½ e(ξ(1 − 4u)/2^(j+2)) G_j(uξ)`.  Uses that `beyondSign j` depends only on
`r mod 2^(j+1)` (`accWord_congr_mod`, Ladder.lean) and that `fourierCoeff j` is periodic in `ξ`
mod `2^(j+1)`.

Evidence with control (`experiments/conjugacy/recurcheck.py`, `j ≤ 17`, every `ξ < 2^(j+2)`):
maximum error `1.8e-11`; with the phase deleted the error is `0.65`.  Confidence 97%. -/
theorem fourierCoeff_succ (j ξ u : ℕ) (hu : 3 * u % 2 ^ (j + 1) = 1) :
    fourierCoeff (j + 1) ξ =
      (1 / 2 : ℂ) * fourierCoeff j ξ +
        (1 / 2 : ℂ) *
            Complex.exp (2 * Real.pi * Complex.I * ξ * (1 - 4 * (u : ℂ)) / 2 ^ (j + 2)) *
          fourierCoeff j (u * ξ) := by
  sorry

/-- **Node: decay at every fixed odd 2-adic frequency.**  For each `2`-adic unit `η`, the
coefficient at its truncation `η mod 2^(j+1)` tends to `0`.  Unrolling the first branch of
`fourierCoeff_succ` gives `‖G_j(ξ)‖ ≤ Σ_m 2^{−m} ‖G_{j−m}(ξ/3 mod 2^{j−m+1})‖ + 2^{−j}`, so decay at
an integer frequency is fed by decay at the 2-adic frequency `ξ/3` (the "third points", where
`ξ/3 mod 2^(j+1)` sits near `2^(j+1)/3` or `2^(j+2)/3`).  This family is closed under `η ↦ η/3`
and contains the integer frequencies (`lowFreqDecay_of_twoAdicFreqDecay`).

Evidence with control (`experiments/conjugacy/twoadicfreq.py`, `j ≤ 24`): for
`η = 1/3, −1/3, 1/9, 5/7, 1/27` and a random 64-bit unit, `‖G_j(η)‖ · 2^{j/2}` stays in
`[0.14, 1.6]`; the pair `±1/3` agrees to every digit, as conjugate symmetry requires.
Confidence 80%. -/
def TwoAdicFreqDecay : Prop :=
  ∀ η : ℤ_[2], IsUnit η →
    Tendsto (fun j => ‖fourierCoeff j (PadicInt.appr η (j + 1))‖) atTop (𝓝 0)

/-- The canonical natural approximant to an embedded natural is its remainder modulo `2^n`. -/
theorem padicInt_appr_natCast (ξ n : ℕ) :
    PadicInt.appr (ξ : ℤ_[2]) n = ξ % 2 ^ n := by
  have hz :
      ((PadicInt.appr (ξ : ℤ_[2]) n : ℕ) : ZMod (2 ^ n)) =
        (ξ : ZMod (2 ^ n)) := by
    change PadicInt.toZModPow n (ξ : ℤ_[2]) = (ξ : ZMod (2 ^ n))
    simp
  have hm := (ZMod.natCast_eq_natCast_iff _ _ _).mp hz
  rw [Nat.ModEq, Nat.mod_eq_of_lt (PadicInt.appr_lt _ _)] at hm
  exact hm

/-- **Edge: the 2-adic node contains the integer one.**  For odd `ξ : ℕ`, `(ξ : ℤ_[2])` is a unit
and its approximant mod `2^(j+1)` is `ξ mod 2^(j+1)`; `fourierCoeff j` is periodic in the
frequency mod `2^(j+1)`.  Confidence 99%. -/
theorem lowFreqDecay_of_twoAdicFreqDecay (h : TwoAdicFreqDecay) : LowFreqDecay := by
  intro ξ hξ
  have hunit : IsUnit (ξ : ℤ_[2]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff,
      Nat.prime_two.coprime_iff_not_dvd]
    intro hdvd
    rw [Nat.dvd_iff_mod_eq_zero] at hdvd
    rw [Nat.odd_iff] at hξ
    omega
  apply (h (ξ : ℤ_[2]) hunit).congr'
  filter_upwards [] with j
  congr 1
  rw [padicInt_appr_natCast]
  symm
  conv_lhs => rw [← Nat.mod_add_div ξ (2 ^ (j + 1))]
  exact fourierCoeff_add_period j _ _

end CollatzMoonshot.Conjugacy
