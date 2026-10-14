/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalNearCycleRuns.Bootstrap

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
  have hb := fun m : ℕ => NearCycleRuns.rpow_bootstrap (NearCycleRuns.one_le_growthConst m)
    (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)] : (1 : ℝ) ≤ m + 1)
  choose Cb hCb using hb
  refine ⟨fun m => max (3 * m / 2 + 2) (Cb m), ?_⟩
  intro D p g m h hm hD
  have hp2 := NearCycleRuns.nearCycleAt_two_le h
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hX : 1 ≤ (Real.log D + 1) ^ (13.3 : ℝ) :=
    Real.one_le_rpow (by linarith [Real.log_nonneg hD1]) (by norm_num)
  have hW : (D : ℝ) ≤ D * (Real.log D + 1) ^ (13.3 : ℝ) := le_mul_of_one_le_right (by linarith) hX
  have hm' : (eRuns p g : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  set C := max (3 * (m : ℝ) / 2 + 2) (Cb m) with hC
  have hC1 : 3 * (m : ℝ) / 2 + 2 ≤ C := le_max_left _ _
  rw [mul_assoc]
  by_cases hA : 3 * eRuns p g < 2 * p
  swap
  · -- `p ≤ 1.5 m`
    have : 2 * (p : ℝ) ≤ 3 * eRuns p g := by exact_mod_cast (by omega : 2 * p ≤ 3 * eRuns p g)
    nlinarith
  rcases (by have := h.1; omega : g = 1 ∨ 2 ≤ g) with rfl | hg2
  · -- `g = 1`: `3p/2 ≤ p + D`
    have h2 := NearCycleRuns.two_mul_amusical_of_even (NearCycleRuns.nearCycleAt_even h)
    have h3 := h.2.2.1
    simp only [Function.iterate_one] at h3
    have : (p : ℝ) ≤ 2 * D := by exact_mod_cast (by omega : p ≤ 2 * D)
    nlinarith
  -- the main case
  have h1 := nearCycleAt_linearForm h hp2
  have hg := NearCycleRuns.two_mul_le_growthConst (by omega : 1 ≤ p) hm
    (nearCycleAt_numE_ge h hA) (nearCycleAt_numE_le h hp2)
  have hN : numE p g ≤ g := NearCycleRuns.cntE_le _ g
  have ha : g ≤ excursionWeight p g := by unfold excursionWeight; omega
  have ha2 : excursionWeight p g ≤ 2 * g := by unfold excursionWeight; omega
  have hRh := hR (excursionWeight p g) g (by omega)
  set a := excursionWeight p g with hadef
  have haR : (g : ℝ) ≤ a := by exact_mod_cast ha
  have ha2R : (a : ℝ) ≤ 2 * g := by exact_mod_cast ha2
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg2
  rw [max_eq_left haR, abs_sub_comm] at hRh
  set Λ := (g : ℝ) * Real.log 3 - a * Real.log 2 with hΛ
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hpΛ : p * |Λ| < D + m := by
    rw [← abs_of_pos hp0, ← abs_mul, abs_lt]
    constructor <;> linarith
  have h2g : ((2 * g : ℝ)) ^ (-(13.3 : ℝ)) ≤ (a : ℝ) ^ (-(13.3 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) ha2R (by norm_num)
  have hG0 : 0 < ((2 * g : ℝ)) ^ (13.3 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hpg : (p : ℝ) < (D + m) * (2 * g) ^ (13.3 : ℝ) := by
    rw [Real.rpow_neg (by linarith)] at h2g
    have : (p : ℝ) * ((2 * g : ℝ) ^ (13.3 : ℝ))⁻¹ < D + m := by
      calc _ ≤ (p : ℝ) * |Λ| := mul_le_mul_of_nonneg_left (h2g.trans hRh) hp0.le
        _ < D + m := hpΛ
    rwa [← div_eq_mul_inv, div_lt_iff₀ hG0] at this
  have hpow : ((2 * g : ℝ)) ^ (13.3 : ℝ) ≤
      (NearCycleRuns.growthConst m * (Real.log p + 1)) ^ (13.3 : ℝ) :=
    Real.rpow_le_rpow (by linarith) hg (by norm_num)
  have hDm : (D : ℝ) + m ≤ (m + 1) * D := by nlinarith
  have hfin := hCb m p D (by exact_mod_cast (by omega : 1 ≤ p)) hD1 (by
    calc (p : ℝ) ≤ (D + m) * (2 * g) ^ (13.3 : ℝ) := hpg.le
      _ ≤ ((m + 1) * D) * (NearCycleRuns.growthConst m * (Real.log p + 1)) ^ (13.3 : ℝ) :=
          mul_le_mul hDm hpow hG0.le (by positivity)
      _ = _ := by ring)
  have hCb' : Cb m ≤ C := le_max_right _ _
  rw [mul_assoc] at hfin
  exact hfin.trans (mul_le_mul_of_nonneg_right hCb' (by positivity))

end CollatzMoonshot.Amusical
