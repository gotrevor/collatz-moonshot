/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.Fourier

/-!
# Uniform decay of the beyond-Terras Fourier coefficients

`Fourier.lean` reduces `BiasDecays` to decay of each fixed odd frequency (`LowFreqDecay`), and that
to decay at each fixed odd 2-adic frequency (`TwoAdicFreqDecay`).  This module records the
uniform version, which the measurements suggest is also true.

* **Where the sup sits** (`experiments/conjugacy/supfreq.py`, full FFT, `j ≤ 24`): for every
  `j` from `8` to `24` the maximum of `‖G_j(ξ)‖` over odd `ξ` is attained at `±3^k`.
* **How it decays** (`experiments/conjugacy/chainsup.py`, chunked direct sum on the chain,
  `j ≤ 33`; control: reproduces the FFT values at `j = 22, 24` to every printed digit):
  `sup_ξ ‖G_j(ξ)‖ = 0.104, 0.075, 0.065, 0.058, 0.0525, 0.0515` at `j = 14, 20, 24, 28, 32, 33`.
  `sup · √j` falls slowly (`0.388 → 0.296`) and `sup · j` rises (`1.45 → 1.70`), so the uniform
  rate on this range lies between `1/j` and `1/√j`.  The maximising exponent drifts up,
  `k/j = 0.33` at `j = 24` to `0.42` at `j = 33`.
* **A heuristic for the rate** (research note §12): unrolling the mirror recursion from `3^k`,
  the frequency is carried down to `1` almost in phase, arriving at a level `L ≈ j − 2k` with
  spread `√j`, after which `G_L(1) ≈ 2^{−L/2}`; averaging over `L` gives `≍ j^{−1/2}` with
  `k/j → 1/2`.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology

/-- **Node: uniform decay over all odd frequencies.**  `sup_{odd ξ} ‖G_j(ξ)‖ → 0`.

Evidence with control: see the module docstring (`supfreq.py`, `chainsup.py`, `j ≤ 33`).  The
sup is attained on the resonant chain `±3^k`, so this node is exactly the statement that the
resonance is transient uniformly in `k`.  The lattice DP (`FourierLattice.lean`,
`latticerun.py`) extends the chain to `N = 4096`: `sup · √N = 0.2352, 0.2306, 0.2284, 0.2272,
0.2267` at `N = 256, …, 4096`, maximiser `k/N = 0.488 → 0.499`.  Confidence 80%. -/
def SupFreqDecay : Prop :=
  ∀ ε > (0 : ℝ), ∀ᶠ j in atTop, ∀ ξ : ℕ, Odd ξ → ‖fourierCoeff j ξ‖ ≤ ε

/-- **Node: the `j^{−1/2}` rate.**  Some constant bounds `‖G_j(ξ)‖ · √j` for every `j ≥ 1` and odd
`ξ`.

Evidence: measured `sup · √j ≤ 0.92` for `2 ≤ j ≤ 33` (FFT and direct sum), and on the chain
`|k| ≤ N` by the lattice DP, `sup · √N` settling at `0.2267` by `N = 4096` with the maximiser at
`k/N → 1/2`, as the transport heuristic predicts.  What would refute it: `sup · √N` turning
upward, or the sup leaving the window `|k| ≤ N` (checked only by FFT, `N ≤ 24`).
Confidence 75%. -/
def SupFreqSqrtBound : Prop :=
  ∃ C : ℝ, ∀ j ≥ 1, ∀ ξ : ℕ, Odd ξ → ‖fourierCoeff j ξ‖ ≤ C / Real.sqrt j

/-- **Node: fixed integer frequencies decay exponentially, beyond square-root cancellation.**

Evidence with control (`experiments/conjugacy/latticerun.py seqs`, lattice DP;
`latticemp.py` reruns it at 60 digits and agrees to relative `2.5e-13` at `j = 1000`):
`log₂‖G_j(ξ)‖ / j ∈ [−0.530, −0.520]` for `j = 1000, …, 1600` at `ξ = 1, 5, 7, 27`, and the same
at the `2`-adic frequencies `1/3`, `5/7` and a random 64-bit unit.  The exponent `≈ 0.526` is
not identified.  Not uniform over `2`-adic units: `η = 3^a` with `a ∈ ℤ₂` super-sparse in
binary sits at chain position `k ≈ j/2` along a subsequence of levels, where the coefficient is
`≈ 0.22/√j` (research note §12).  So the integer form is frozen, not the `2`-adic one.
Confidence 55%. -/
def FixedFreqExpDecay : Prop :=
  ∃ δ > (0 : ℝ), ∀ ξ : ℕ, Odd ξ → ∃ C : ℝ, ∀ j : ℕ,
    ‖fourierCoeff j ξ‖ ≤ C * (2 : ℝ) ^ (-((1 / 2 + δ) * j))

/-- **Edge: the exponential rate implies `LowFreqDecay`.**  `C · 2^{−(1/2+δ) j} → 0`.
Confidence 99%. -/
theorem lowFreqDecay_of_fixedFreqExpDecay (h : FixedFreqExpDecay) : LowFreqDecay := by
  obtain ⟨δ, hδ, h⟩ := h
  intro ξ hξ
  obtain ⟨C, hC⟩ := h ξ hξ
  have hbase_nonneg : 0 ≤ (2 : ℝ) ^ (-(1 / 2 + δ)) := Real.rpow_nonneg (by norm_num) _
  have hbase_lt : (2 : ℝ) ^ (-(1 / 2 + δ)) < 1 := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num) (by linarith))
  have hbound : Tendsto
      (fun j : ℕ => C * (2 : ℝ) ^ (-((1 / 2 + δ) * j))) atTop (nhds 0) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hbase_nonneg hbase_lt
    convert hp.const_mul C using 1
    · ext j
      rw [show -((1 / 2 + δ) * (j : ℝ)) = (-(1 / 2 + δ)) * j by ring,
        Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
    · simp
  exact squeeze_zero (fun j => norm_nonneg _) hC hbound

/-- **Edge: the rate implies uniform decay.**  `C / √j → 0`.  Confidence 99%. -/
theorem supFreqDecay_of_sqrtBound (h : SupFreqSqrtBound) : SupFreqDecay := by
  obtain ⟨C, hC⟩ := h
  intro ε hε
  have hbound : Tendsto (fun j : ℕ => C / Real.sqrt (j : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hevent : ∀ᶠ j : ℕ in atTop, C / Real.sqrt (j : ℝ) < ε :=
    (tendsto_order.1 hbound).2 ε hε
  filter_upwards [hevent, eventually_ge_atTop 1] with j hj hj1
  intro ξ hξ
  exact (lt_of_le_of_lt (hC j hj1 ξ hξ) hj).le

/-- **Edge: uniform decay implies decay at every fixed 2-adic unit.**  The approximant of a
`2`-adic unit modulo `2^(j+1)` is odd (its residue mod `2` is the unit's, which is nonzero), so
the uniform bound applies to it.  Confidence 99%. -/
theorem twoAdicFreqDecay_of_supFreqDecay (h : SupFreqDecay) : TwoAdicFreqDecay := by
  intro η hη
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨J, hJ⟩ := (h (ε / 2) (by linarith)).exists_forall_of_atTop
  refine ⟨J, fun j hj => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  apply lt_of_le_of_lt (hJ j hj _ ?_) (by linarith)
  rw [← Nat.not_even_iff_odd]
  intro heven
  apply (show ¬(2 : ℤ_[2]) ∣ η by
    intro hdvd
    have hlt := (PadicInt.norm_lt_one_iff_dvd η).2 hdvd
    rw [PadicInt.isUnit_iff] at hη
    linarith)
  have hpow : (2 : ℤ_[2]) ^ (j + 1) ∣ η - PadicInt.appr η (j + 1) := by
    have hs := PadicInt.appr_spec (j + 1) η
    rw [Ideal.mem_span_singleton] at hs
    norm_num at hs ⊢
    exact hs
  have hdiff : (2 : ℤ_[2]) ∣ η - PadicInt.appr η (j + 1) :=
    (dvd_pow_self (2 : ℤ_[2]) (by omega)).trans hpow
  have happr : (2 : ℤ_[2]) ∣ (PadicInt.appr η (j + 1) : ℤ_[2]) := by
    obtain ⟨k, hk⟩ := even_iff_two_dvd.mp heven
    refine ⟨(k : ℤ_[2]), ?_⟩
    exact_mod_cast hk
  rw [← sub_add_cancel η (PadicInt.appr η (j + 1) : ℤ_[2])]
  exact dvd_add hdiff happr

end CollatzMoonshot.Conjugacy
