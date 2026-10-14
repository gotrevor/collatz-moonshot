/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalNearCycleRuns.Growth

/-!
# Run-bounded near-cycles (Theorem MR)

The 2026-10-14 "ncbaker" agent (research §38) carried the Steiner / Simons–de Weger cycle method
over to near-cycles.  For a near-cycle start `p` with return time `g`, write `m` for the number of
`E`-runs of its excursion and `Λ = g log 3 − a log 2` (`a` = bits consumed).

**`nearCycleAt_linearForm` (MR I).**  `−m < p Λ < D + m`.  The carry is bounded run by run: along
an odd run `z ↦ z'` has `z − 1 ≥ (4/3)(z' − 1)`, so a run ending at `X` contributes `< 1/(X − 1)`,
and every run ends above `p`.

**`nearCycleAt_numE_le`, `nearCycleAt_numE_ge` (MR II).**  An `E`-run at a local minimum `x_j`
has length `≤ log₂ x_j` (`2^{a_j} ∣ x_j`, the one integrality input), so its peak is `≤ x_j^θ`
and `#E ≤ log₂ p · (θ^m − 1)/(θ − 1)`.  Conversely (I) gives `#E > (2 − θ) g − 1` once `p > 1.5 m`.

**`nearCycleAt_le_of_eRuns_le` (MR-P).**  With Rhin's linear-forms bound as a hypothesis `Prop`,
near-cycle starts with at most `m` runs satisfy `p ≤ C_m · D · (log D + 1)^13.3`: the location
clause of Conjecture LIN (§37) holds on every run stratum.

The agent also proves the linear law `#NC_D^(≤m) = κ_{≤m} D + O(D^{θ/2+ε})` on every stratum
(`κ₁ = 2.736…`; exhaustive count `179 332` at `D = 2¹⁶` against `179 329.5`), and that LIN's density
clause is equivalent to run tightness.  The 1-near-cycle starts with at most 32 runs are exactly
`2, 4, 6, 10, 88, 112` (exhaustive computation).  Those are recorded in research §38.
-/

namespace CollatzMoonshot.Amusical

/-- **Literature input (Rhin 1987, as used in Simons 2022, Lemma 10), a hypothesis `Prop`.** -/
def RhinBound : Prop :=
  ∀ a g : ℕ, 2 ≤ max a g →
    ((max a g : ℝ) ^ (-(13.3 : ℝ))) ≤ |a * Real.log 2 - g * Real.log 3|

/-- The number of `E`-steps among the first `g` steps of the orbit of `p`. -/
def numE (p g : ℕ) : ℕ :=
  ((Finset.range g).filter fun t => Even (amusical^[t] (p : ℤ))).card

/-- The number of maximal `E`-runs among the first `g` steps of the orbit of `p`. -/
def eRuns (p g : ℕ) : ℕ :=
  ((Finset.range g).filter fun t =>
    Even (amusical^[t] (p : ℤ)) ∧ (t = 0 ∨ Odd (amusical^[t - 1] (p : ℤ)))).card

/-- The bits consumed by the first `g` steps: `#E + 2 #O`. -/
def excursionWeight (p g : ℕ) : ℕ := 2 * g - numE p g

/-- **Target (MR I).**  The carry bound: `−m < p Λ < D + m`. -/
theorem nearCycleAt_linearForm {D p g : ℕ} (h : NearCycleAt D p g) (hp : 2 ≤ p) :
    -(eRuns p g : ℝ) < p * ((g : ℝ) * Real.log 3 - excursionWeight p g * Real.log 2) ∧
      p * ((g : ℝ) * Real.log 3 - excursionWeight p g * Real.log 2) < D + eRuns p g := by
  obtain ⟨s, hs, hps⟩ := NearCycleRuns.carry_bound (fun t => amusical^[t] (p : ℤ))
    (NearCycleRuns.iterate_even_step _) (NearCycleRuns.iterate_odd_step _) h.1
    (NearCycleRuns.nearCycleAt_even h) (by simp only [Function.iterate_zero, id_eq]; omega)
    (NearCycleRuns.nearCycleAt_big h)
  have hW : (excursionWeight p g : ℝ) = 2 * g - numE p g := by
    have : numE p g ≤ g := NearCycleRuns.cntE_le _ g
    unfold excursionWeight
    rw [Nat.cast_sub (by omega)]
    push_cast; ring
  simp only [Function.iterate_zero, id_eq, Int.cast_natCast] at hs hps
  change |_ - _ - (_ - (2 * (g : ℝ) - (numE p g : ℝ)) * _)| ≤ s at hs
  change _ ≤ (eRuns p g : ℝ) at hps
  obtain ⟨-, h1, h2, -⟩ := h
  set X : ℝ := ((amusical^[g] (p : ℤ) : ℤ) : ℝ) with hX
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hXp : (p : ℝ) < X := by rw [hX]; exact_mod_cast h1
  have hXD : X ≤ p + D := by rw [hX]; exact_mod_cast h2
  have hL : Real.log X - Real.log p = Real.log (X / p) := (Real.log_div (by linarith) hp0.ne').symm
  have hL0 : 0 < Real.log (X / p) := Real.log_pos (by rw [one_lt_div hp0]; exact hXp)
  have hL1 : p * Real.log (X / p) < D := by
    have := Real.log_lt_sub_one_of_pos (x := X / p) (div_pos (by linarith) hp0)
      (by rw [ne_eq, div_eq_one_iff_eq hp0.ne']; exact hXp.ne')
    rw [div_sub_one hp0.ne', lt_div_iff₀ hp0] at this
    linarith
  rw [hW]
  rw [abs_le] at hs
  constructor <;> nlinarith

/-- **Target (MR II, upper half).**  Few runs force few `E`-steps. -/
theorem nearCycleAt_numE_le {D p g : ℕ} (h : NearCycleAt D p g) (hp : 2 ≤ p) :
    (numE p g : ℝ) ≤
      Real.logb 2 p * (Real.logb 2 3 ^ eRuns p g - 1) / (Real.logb 2 3 - 1) := by
  have h2 : ∀ k ≤ g, 2 ≤ amusical^[k] (p : ℤ) := fun k hk => by
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp only [Function.iterate_zero, id_eq]; omega
    · have := NearCycleRuns.nearCycleAt_big h k hk0 hk; omega
  have := NearCycleRuns.cntE_le_of_runs (fun t => amusical^[t] (p : ℤ))
    (NearCycleRuns.iterate_even_step _) (NearCycleRuns.iterate_odd_step _) h.1 h2
  simp only [Function.iterate_zero, id_eq, Int.cast_natCast] at this
  exact this

/-- **Target (MR II, lower half).** -/
theorem nearCycleAt_numE_ge {D p g : ℕ} (h : NearCycleAt D p g)
    (hp : 3 * eRuns p g < 2 * p) :
    (2 - Real.logb 2 3) * g - 1 < numE p g := by
  have hp2 := NearCycleRuns.nearCycleAt_two_le h
  have h1 := (nearCycleAt_linearForm h hp2).1
  have hW : (excursionWeight p g : ℝ) = 2 * g - numE p g := by
    have : numE p g ≤ g := NearCycleRuns.cntE_le _ g
    unfold excursionWeight
    rw [Nat.cast_sub (by omega)]
    push_cast; ring
  rw [hW] at h1
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hm : 3 * (eRuns p g : ℝ) < 2 * p := by exact_mod_cast hp
  have hl2 := Real.log_two_gt_d9
  have hl2' : 0 < Real.log 2 := by linarith
  set Λ := (g : ℝ) * Real.log 3 - (2 * g - numE p g) * Real.log 2 with hΛ
  have hΛ0 : -(2 / 3 : ℝ) < Λ := by
    by_contra hc
    push Not at hc
    nlinarith
  rw [Real.logb, show (2 - Real.log 3 / Real.log 2) * g - 1 =
    ((2 * Real.log 2 - Real.log 3) * g - Real.log 2) / Real.log 2 by field_simp,
    div_lt_iff₀ hl2']
  linarith

/-- **Target (MR-P).**  Run-bounded near-cycle starts are polynomially bounded in `D`. -/
theorem nearCycleAt_le_of_eRuns_le (hR : RhinBound) :
    ∃ C : ℕ → ℝ, ∀ {D p g m : ℕ}, NearCycleAt D p g → eRuns p g ≤ m → 1 ≤ D →
      (p : ℝ) ≤ C m * D * (Real.log D + 1) ^ (13.3 : ℝ) := by
  sorry

end CollatzMoonshot.Amusical
