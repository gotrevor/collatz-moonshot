/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import TaoCollatz.Sec5.Stabilization
import CollatzMoonshot.Conjugacy.ChampernowneLog
import CollatzMoonshot.Conjugacy.OrbitWordLawDensity

/-!
# The orbit word law, from Tao's stabilisation

For `C ≤ 4`, almost every start in logarithmic density has the right frequency of every word among
its first `C log₂ n` parity letters (`orbitWordLaw_of_le_four`), so `𝒞_C` is normal in logarithmic
density (`logNormal_of_le_four`).  The proof chains Tao 2019 Proposition 1.11 (`stabilization_atCX`)
over scales `x_(j+1) = x_j^(1/α)`, down to `N^(1/10)`.  Research note §16.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord

/-- **Frozen target.  Believed, 85%, given (1.20), which `stabilization_atCX` proves.** -/
theorem orbitWordLaw_of_le_four (C : ℕ) (hC : 1 ≤ C) (hC4 : C ≤ 4) : OrbitWordLaw C := by
  rw [orbitWordLaw_iff]
  intro u δ hδ
  obtain ⟨s₀, hs₀⟩ := not_badStart_of_goodOdd hC4 u hδ
  set ε : ℝ := min (1 / 15) (δ / 8) with hεdef
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have h1 : LogDens0 (fun n => ε * Nat.size (TaoCollatz.oddPart n) < padicValNat 2 n) :=
    logDens0_of_summable (summable_large_twoAdic hε)
  have h2 : LogDens0 (fun n => n ≤ 2 ^ (2 * s₀)) := logDens0_of_bdd (fun n h => h)
  have h3 : LogDens0 (fun n => ¬ GoodOdd u (δ / 2) (TaoCollatz.oddPart n)) :=
    logDens0_oddPart (fun m => ¬ GoodOdd u (δ / 2) m)
      (logDens0_of_window (fun m => ¬ GoodOdd u (δ / 2) m) (goodOdd_whp u (by positivity)))
  refine ((h1.or h2).or h3).mono fun n hn => ?_
  by_contra hcon
  simp only [not_or, not_lt, not_le, not_not] at hcon
  obtain ⟨⟨ha, hn2⟩, hgood⟩ := hcon
  have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hn2
  obtain ⟨a, ha_def⟩ : ∃ a, a = padicValNat 2 n := ⟨_, rfl⟩
  obtain ⟨m, hm_def⟩ : ∃ m, m = TaoCollatz.oddPart n := ⟨_, rfl⟩
  rw [← ha_def, ← hm_def] at ha
  rw [← hm_def] at hgood
  have hm : m % 2 = 1 := hm_def ▸ TaoCollatz.oddPart_odd hn0
  have hnm : 2 ^ a * m = n := by rw [ha_def, hm_def]; exact TaoCollatz.two_pow_mul_oddPart n
  have haε : (a : ℝ) ≤ ε * Nat.size m := ha
  have ha15 : 15 * (a : ℝ) ≤ Nat.size m := by
    have : ε ≤ 1 / 15 := min_le_left _ _
    have hs : (0 : ℝ) ≤ Nat.size m := Nat.cast_nonneg _
    nlinarith
  have ha8 : 8 * (a : ℝ) ≤ δ * Nat.size m := by
    have : ε ≤ δ / 8 := min_le_right _ _
    have hs : (0 : ℝ) ≤ Nat.size m := Nat.cast_nonneg _
    nlinarith
  have ha15' : 15 * a ≤ Nat.size m := by exact_mod_cast ha15
  have hsize : s₀ ≤ Nat.size m := by
    by_contra hlt
    push Not at hlt
    have hm2 : m < 2 ^ s₀ := lt_of_lt_of_le (Nat.lt_size_self m) (Nat.pow_le_pow_right (by norm_num)
      hlt.le)
    have ha2 : 2 ^ a ≤ 2 ^ s₀ := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : n < 2 ^ (2 * s₀) := by
      rw [← hnm, two_mul, pow_add]
      exact Nat.mul_lt_mul_of_le_of_lt ha2 hm2 (by positivity)
    omega
  rw [← hnm] at hn
  exact hs₀ a m hm hsize ha15' ha8 hgood hn

/-- **Below the threshold, `𝒞_C` is normal in logarithmic density.** -/
theorem logNormal_of_le_four (C : ℕ) (hC : 1 ≤ C) (hC4 : C ≤ 4) :
    LogNormal (collatzChampernowne C) :=
  logNormal_of_orbitWordLaw C hC (orbitWordLaw_of_le_four C hC hC4)

end CollatzMoonshot.Conjugacy
