/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.ChampernowneOne

/-!
# The second moment over offsets meets coalescence

Averaged mixing asks for a sum over `n` of `∑_t s(n, t)`, with `s = (−1)^letter`.  Van der Corput in
`n` bounds its square by the average over `h ≤ H` of the pair correlations `pairCorr C k h`, so the
route needs `PairCorrelationsAverageOut`.

Two things stand in its way.

* **The correlations do not decay in `k`.**  Orbits of nearby starts merge in phase at bounded times:
  `T^3 (8j + 4) = T^3 (8j + 5)` (`tstep_iterate_three_merge`), so on `1/8` of `n` the letters of `n`
  and `n + 1` agree at every `t ≥ 3` (`accWord_eq_of_merge`).  Measured
  (`experiments/conjugacy/pair_correlation.py`, exhaustive, `C = 2`): `pairCorr` at
  `h = 1, 2, 64, 1023` is `0.407, 0.286, 0.055, 0.004` at `k = 18`, and `0.424, 0.309, 0.078, 0.011`
  at `k = 22`, against `0.0001` for independent bits.  So `H` must grow, and the proof must control the
  merge density as a function of `h`.
* **The unmerged pairs keep the sparsity.**  Both `n` and `n + h` are functions of the same `k` bits,
  so at `t − k ≍ k` a pair has no more free randomness than a single orbit.  The reduction trades one
  letter's balance for a two-orbit balance over the same sparse set.  This is a judgment, not a
  theorem (75%).
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord

/-- Consecutive starts `8j + 4`, `8j + 5` merge in phase after three steps. -/
theorem tstep_iterate_three_merge (j : ℕ) : tstep^[3] (8 * j + 4) = tstep^[3] (8 * j + 5) := by
  have h4 : tstep (8 * j + 4) = 4 * j + 2 := by simp only [tstep]; split_ifs <;> omega
  have h2 : tstep (4 * j + 2) = 2 * j + 1 := by simp only [tstep]; split_ifs <;> omega
  have h1 : tstep (2 * j + 1) = 3 * j + 2 := by simp only [tstep]; split_ifs <;> omega
  have h5 : tstep (8 * j + 5) = 12 * j + 8 := by simp only [tstep]; split_ifs <;> omega
  have h8 : tstep (12 * j + 8) = 6 * j + 4 := by simp only [tstep]; split_ifs <;> omega
  have h6 : tstep (6 * j + 4) = 3 * j + 2 := by simp only [tstep]; split_ifs <;> omega
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id, h4, h2, h1, h5, h8, h6]

/-- So their letters agree from then on. -/
theorem accWord_eq_of_merge (j t : ℕ) (ht : 3 ≤ t) :
    accWord (8 * j + 4) t = accWord (8 * j + 5) t := by
  obtain ⟨e, rfl⟩ : ∃ e, t = e + 3 := ⟨t - 3, by omega⟩
  simp only [accWord, Function.iterate_add_apply, tstep_iterate_three_merge]

/-- The sign of a letter. -/
def pairSign (n t : ℕ) : ℝ := if accWord n t then -1 else 1

/-- The correlation of the letters of `n` and `n + h`, over stage `k` and offsets `t ∈ [k, C k)`. -/
noncomputable def pairCorr (C k h : ℕ) : ℝ :=
  (∑ t ∈ Finset.Ico k (C * k), ∑ n ∈ Finset.Ico (2 ^ (k - 1)) (2 ^ k),
      pairSign n t * pairSign (n + h) t) / (((C - 1) * k : ℕ) * 2 ^ (k - 1))

/-- **Node.**  The hypothesis the van der Corput route needs: the pair correlations average out over
`h ≤ H` for large `H`, uniformly for large `k`.  What the route would have to prove.  The measurement
in the module docstring is consistent with it (at `k = 22`, roughly `h^(−1/2)`), and it does not by
itself supply a mechanism. -/
def PairCorrelationsAverageOut (C : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ H : ℕ, 1 ≤ H ∧ ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
    (∑ h ∈ Finset.Icc 1 H, |pairCorr C k h|) / H ≤ ε

end CollatzMoonshot.Conjugacy
