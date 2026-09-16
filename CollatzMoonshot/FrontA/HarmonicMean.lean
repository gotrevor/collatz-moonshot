/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.FrontA.TrunkBound

/-!
# The harmonic-mean trunk bound: the hard half of Rozier–Terracol Theorem 4.2

`TrunkBound.lean` formalizes the **easy (min-term) half** of Rozier–Terracol Theorem 4.2:
a strictly climbing subcritical segment has one odd-step value below `a/(3Λ)`.  This file
is the **hard (all-terms, harmonic-mean) half**: the same bound holds for the *harmonic
mean* of all `a` odd-step values, which is `≥ x_min` — a strictly stronger statement.
No novelty is claimed; this is RT Theorem 4.2 in the repository's `tstep` notation.

Write `x_i = tstep^[i] n`, `I = oddSteps n m`, `a = |I|`, `H = ∑_{i∈I} 1/x_i` (`harmSum`),
so the harmonic mean is `h = a/H` (`harmonicMean`).

1. `prod_le_pow_harmonic` : `∏_{i∈I} (1 + 1/(3x_i)) ≤ (1 + H/(3a))^a`, weighted AM–GM
   (`Real.geom_mean_le_arith_mean_weighted`) with equal weights `1/a`.
2. `harmonic_mean_inequality` : `n < x_m → (2:ℝ)^m < (3 + H/a)^a`, from
   `tstep_iterate_prod_identity` with the product bound of (1) in place of the min-term
   bound.  This is RT 4.2's `log 2 / log(3 + 1/h) ≤ a/m`.
3. `harmonicMean_lt_of_subcritical` : under `3^a < 2^m`, `h < a/(3Λ)` with
   `Λ = m log 2 − a log 3 > 0`, via `2^(m/a) − 3 = 3(exp(Λ/a) − 1) ≥ 3Λ/a` in the form
   `Λ ≤ a·log(1 + H/(3a)) ≤ H/3`.
4. `segMin_le_harmonicMean` : the trivial comparison `x_min ≤ h`, which exhibits (3) as
   strictly stronger than `TrunkBound`'s `segMin_lt_of_subcritical`.

Trust ledger: everything here is standard trust triple
(`propext, Classical.choice, Quot.sound`); no Rhin-lite native certificate is inherited.

Kernel control on `(7, 8)`: `H = 1/7 + 1/11 + 1/17 + 1/13 + 1/5`, `a = 5`, `m = 8`
(`harmonicMean_control_seven_eight`).
-/

namespace CollatzMoonshot.FrontA

open CollatzMoonshot CollatzMoonshot.FrontB Finset

/-- `H = ∑_{i∈I} 1/x_i`, the reciprocal sum of the odd-step values of the first `m`
shortcut steps from `n`. -/
noncomputable def harmSum (n m : ℕ) : ℝ := ∑ i ∈ oddSteps n m, (1 : ℝ) / (tstep^[i] n : ℝ)

/-- `h = a/H`, the harmonic mean of the odd-step values (`0` when there are none). -/
noncomputable def harmonicMean (n m : ℕ) : ℝ := ((oddSteps n m).card : ℝ) / harmSum n m

theorem harmSum_nonneg (n m : ℕ) : 0 ≤ harmSum n m :=
  Finset.sum_nonneg fun i _ => by positivity

theorem harmSum_pos {n m : ℕ} (h : (oddSteps n m).Nonempty) : 0 < harmSum n m := by
  obtain ⟨i, hi⟩ := h
  refine Finset.sum_pos' (fun j _ => by positivity) ⟨i, hi, ?_⟩
  have : 1 ≤ tstep^[i] n := one_le_of_mem_oddSteps hi
  have : (1 : ℝ) ≤ (tstep^[i] n : ℝ) := by exact_mod_cast this
  positivity

/-- **Weighted AM–GM on the excess factors.**  With `a = |I| ≥ 1`,
`∏_{i∈I} (1 + 1/(3x_i)) ≤ (1 + H/(3a))^a`. -/
theorem prod_le_pow_harmonic (n m : ℕ) (hne : (oddSteps n m).Nonempty) :
    (∏ i ∈ oddSteps n m, (1 + 1 / (3 * (tstep^[i] n : ℝ)))) ≤
      (1 + harmSum n m / (3 * ((oddSteps n m).card : ℝ))) ^ (oddSteps n m).card := by
  set I := oddSteps n m with hI
  set a : ℕ := I.card with ha
  have ha1 : 1 ≤ a := Finset.card_pos.mpr hne
  have haR : (0 : ℝ) < a := by exact_mod_cast ha1
  set z : ℕ → ℝ := fun i => 1 + 1 / (3 * (tstep^[i] n : ℝ)) with hz
  have hzpos : ∀ i ∈ I, 0 ≤ z i := by
    intro i hi
    have : 1 ≤ tstep^[i] n := one_le_of_mem_oddSteps (hI ▸ hi)
    have : (1 : ℝ) ≤ (tstep^[i] n : ℝ) := by exact_mod_cast this
    simp only [hz]
    positivity
  -- weighted AM–GM with equal weights `1/a`
  have hw : ∑ _i ∈ I, (1 : ℝ) / a = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, ← ha]
    field_simp
  have hAM := Real.geom_mean_le_arith_mean_weighted I (fun _ => (1 : ℝ) / a) z
    (fun _ _ => by positivity) hw hzpos
  -- the arithmetic side is `1 + H/(3a)`
  have hsum : ∑ i ∈ I, (1 : ℝ) / a * z i = 1 + harmSum n m / (3 * a) := by
    simp only [hz, mul_add, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
      ← Finset.mul_sum, ← ha]
    have hH : ∑ i ∈ I, (1 : ℝ) / (3 * (tstep^[i] n : ℝ)) = harmSum n m / 3 := by
      rw [harmSum, Finset.sum_div, ← hI]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hH]
    field_simp
  rw [hsum] at hAM
  -- the geometric side is `(∏ z)^(1/a)`
  have hgeo : ∏ i ∈ I, z i ^ ((1 : ℝ) / a) = (∏ i ∈ I, z i) ^ ((1 : ℝ) / a) :=
    Real.finsetProd_rpow I z hzpos _
  rw [hgeo] at hAM
  have hPnn : 0 ≤ ∏ i ∈ I, z i := Finset.prod_nonneg hzpos
  have hApos : (0 : ℝ) ≤ 1 + harmSum n m / (3 * a) := by
    have := harmSum_nonneg n m
    positivity
  have := Real.rpow_le_rpow (by positivity) hAM (le_of_lt haR)
  rwa [← Real.rpow_mul hPnn, one_div, inv_mul_cancel₀ (ne_of_gt haR), Real.rpow_one,
    Real.rpow_natCast] at this

theorem tstep_iterate_zero (m : ℕ) : tstep^[m] 0 = 0 := by
  induction m with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih]; decide

/-- **RT Theorem 4.2, all-terms form.**  A strictly climbing segment satisfies
`2^m < (3 + H/a)^a`, i.e. `log 2 / log(3 + 1/h) ≤ a/m` for the harmonic mean `h = a/H`. -/
theorem harmonic_mean_inequality (n m : ℕ) (hend : n < tstep^[m] n) :
    (2 : ℝ) ^ m < (3 + harmSum n m / ((oddSteps n m).card : ℝ)) ^ (oddSteps n m).card := by
  have hne : (oddSteps n m).Nonempty := oddSteps_nonempty_of_lt n m hend
  set I := oddSteps n m with hI
  set a : ℕ := I.card with ha
  have ha1 : 1 ≤ a := Finset.card_pos.mpr hne
  have haR : (0 : ℝ) < a := by exact_mod_cast ha1
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · rw [tstep_iterate_zero m] at hend; omega
    · exact h
  -- the product identity, cast to ℝ
  have hid := tstep_iterate_prod_identity n m
  have hxpos : ∀ i ∈ I, (1 : ℝ) ≤ (tstep^[i] n : ℝ) := by
    intro i hi
    have := one_le_of_mem_oddSteps (hI ▸ hi)
    exact_mod_cast this
  have hPpos : (0 : ℝ) < ∏ i ∈ I, (3 * (tstep^[i] n : ℝ)) :=
    Finset.prod_pos fun i hi => by have := hxpos i hi; linarith
  have hidR : (2 : ℝ) ^ m * (tstep^[m] n : ℝ) * ∏ i ∈ I, (3 * (tstep^[i] n : ℝ)) =
      3 ^ ones (traceWord n m) * (n : ℝ) * ∏ i ∈ I, (3 * (tstep^[i] n : ℝ) + 1) := by
    have := congrArg (fun k : ℕ => (k : ℝ)) hid
    push_cast at this
    simpa [hI] using this
  -- `∏ (3x+1) = (∏ 3x) * ∏ (1 + 1/(3x))`
  have hsplit : ∏ i ∈ I, (3 * (tstep^[i] n : ℝ) + 1) =
      (∏ i ∈ I, (3 * (tstep^[i] n : ℝ))) * ∏ i ∈ I, (1 + 1 / (3 * (tstep^[i] n : ℝ))) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i hi => ?_
    have := hxpos i hi
    field_simp
  have hcard : ones (traceWord n m) = a := by rw [ha, hI, card_oddSteps]
  rw [hsplit, hcard] at hidR
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hendR : (n : ℝ) < (tstep^[m] n : ℝ) := by exact_mod_cast hend
  -- cancel `n` and `∏ 3x`
  have hkey : (2 : ℝ) ^ m < 3 ^ a * ∏ i ∈ I, (1 + 1 / (3 * (tstep^[i] n : ℝ))) := by
    have h1 : (2 : ℝ) ^ m * (n : ℝ) * ∏ i ∈ I, (3 * (tstep^[i] n : ℝ)) <
        3 ^ a * (n : ℝ) * ((∏ i ∈ I, (3 * (tstep^[i] n : ℝ))) *
          ∏ i ∈ I, (1 + 1 / (3 * (tstep^[i] n : ℝ)))) := by
      rw [← hidR]
      have h2 : (0 : ℝ) < (2 : ℝ) ^ m * ∏ i ∈ I, (3 * (tstep^[i] n : ℝ)) := by positivity
      nlinarith
    have hnpos : (0 : ℝ) < n := by linarith
    have hprod : (0 : ℝ) < (n : ℝ) * ∏ i ∈ I, (3 * (tstep^[i] n : ℝ)) := by positivity
    refine lt_of_mul_lt_mul_right ?_ (le_of_lt hprod)
    calc (2 : ℝ) ^ m * ((n : ℝ) * ∏ i ∈ I, (3 * (tstep^[i] n : ℝ)))
        = 2 ^ m * (n : ℝ) * ∏ i ∈ I, (3 * (tstep^[i] n : ℝ)) := by ring
      _ < 3 ^ a * (n : ℝ) * ((∏ i ∈ I, (3 * (tstep^[i] n : ℝ))) *
            ∏ i ∈ I, (1 + 1 / (3 * (tstep^[i] n : ℝ)))) := h1
      _ = (3 ^ a * ∏ i ∈ I, (1 + 1 / (3 * (tstep^[i] n : ℝ)))) *
            ((n : ℝ) * ∏ i ∈ I, (3 * (tstep^[i] n : ℝ))) := by ring
  refine lt_of_lt_of_le hkey ?_
  have hAMGM := prod_le_pow_harmonic n m hne
  rw [← hI, ← ha] at hAMGM
  have h3 : (3 : ℝ) ^ a * (1 + harmSum n m / (3 * a)) ^ a =
      (3 + harmSum n m / a) ^ a := by
    rw [← mul_pow]
    congr 1
    field_simp
  calc (3 : ℝ) ^ a * ∏ i ∈ I, (1 + 1 / (3 * (tstep^[i] n : ℝ)))
      ≤ 3 ^ a * (1 + harmSum n m / (3 * a)) ^ a := by
        have : (0 : ℝ) < 3 ^ a := by positivity
        nlinarith
    _ = (3 + harmSum n m / a) ^ a := h3

/-- **The harmonic-mean trunk bound.**  A strictly climbing subcritical segment has
`3Λ < H`, i.e. the harmonic mean `h = a/H` of *all* its odd-step values satisfies
`h < a/(3Λ)` — the bound `TrunkBound` proves for `x_min` alone. -/
theorem three_mul_log_lt_harmSum (n m : ℕ) (hend : n < tstep^[m] n)
    (hsub : 3 ^ ones (traceWord n m) < 2 ^ m) :
    3 * ((m : ℝ) * Real.log 2 - (ones (traceWord n m) : ℝ) * Real.log 3) < harmSum n m := by
  have hne : (oddSteps n m).Nonempty := oddSteps_nonempty_of_lt n m hend
  have hcard : ones (traceWord n m) = (oddSteps n m).card := (card_oddSteps n m).symm
  set a : ℕ := (oddSteps n m).card with ha
  have ha1 : 1 ≤ a := Finset.card_pos.mpr hne
  have haR : (0 : ℝ) < a := by exact_mod_cast ha1
  have hHpos : 0 < harmSum n m := harmSum_pos hne
  have hineq := harmonic_mean_inequality n m hend
  rw [← ha] at hineq
  -- take logs
  have hbase : (0 : ℝ) < 3 + harmSum n m / a := by positivity
  have hlog := Real.log_lt_log (by positivity) hineq
  rw [Real.log_pow, Real.log_pow] at hlog
  -- `log(3 + H/a) − log 3 = log(1 + H/(3a)) ≤ H/(3a)`
  have hsplit : Real.log (3 + harmSum n m / a) - Real.log 3 ≤ harmSum n m / (3 * a) := by
    rw [← Real.log_div (ne_of_gt hbase) (by norm_num)]
    have h1 : (3 + harmSum n m / a) / 3 = 1 + harmSum n m / (3 * a) := by
      field_simp
    rw [h1]
    have := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < 1 + harmSum n m / (3 * a) by positivity)
    linarith
  rw [hcard]
  have := mul_le_mul_of_nonneg_left hsplit (le_of_lt haR)
  have hcancel : (a : ℝ) * (harmSum n m / (3 * a)) = harmSum n m / 3 := by
    field_simp
  rw [hcancel] at this
  linarith

/-- The harmonic-mean bound in the shape of RT Theorem 4.2: `h < a/(3Λ)`. -/
theorem harmonicMean_lt_of_subcritical (n m : ℕ) (hend : n < tstep^[m] n)
    (hsub : 3 ^ ones (traceWord n m) < 2 ^ m) :
    harmonicMean n m < (ones (traceWord n m) : ℝ) /
      (3 * ((m : ℝ) * Real.log 2 - (ones (traceWord n m) : ℝ) * Real.log 3)) := by
  have hne : (oddSteps n m).Nonempty := oddSteps_nonempty_of_lt n m hend
  have hHpos : 0 < harmSum n m := harmSum_pos hne
  have hkey := three_mul_log_lt_harmSum n m hend hsub
  set Λ : ℝ := (m : ℝ) * Real.log 2 - (ones (traceWord n m) : ℝ) * Real.log 3 with hΛ
  have hΛpos : 0 < Λ := by
    have hlogs : 0 < Real.log ((3 : ℝ) ^ ones (traceWord n m)) →
        True := fun _ => trivial
    have h := Real.log_lt_log (by positivity)
      (show ((3 : ℕ) ^ ones (traceWord n m) : ℝ) < (2 : ℕ) ^ m by exact_mod_cast hsub)
    push_cast at h
    rw [Real.log_pow, Real.log_pow] at h
    rw [hΛ]; linarith
  have haR : (0 : ℝ) < (ones (traceWord n m) : ℝ) := by
    have : 1 ≤ ones (traceWord n m) := one_le_ones_of_lt n m hend
    exact_mod_cast this
  rw [harmonicMean, card_oddSteps, div_lt_div_iff₀ hHpos (by positivity)]
  nlinarith

/-- **The comparison that makes the above the stronger half**: `x_min ≤ h`. -/
theorem segMin_le_harmonicMean (n m : ℕ) (hne : (oddSteps n m).Nonempty) :
    (segMin n m : ℝ) ≤ harmonicMean n m := by
  have hmin1 : 1 ≤ segMin n m := one_le_segMin hne
  have hminR : (1 : ℝ) ≤ (segMin n m : ℝ) := by exact_mod_cast hmin1
  have hHpos : 0 < harmSum n m := harmSum_pos hne
  have hH : harmSum n m ≤ ((oddSteps n m).card : ℝ) / (segMin n m : ℝ) := by
    have h1 : harmSum n m ≤ ∑ _i ∈ oddSteps n m, (1 : ℝ) / (segMin n m : ℝ) := by
      rw [harmSum]
      refine Finset.sum_le_sum fun i hi => ?_
      have h2 : (segMin n m : ℝ) ≤ (tstep^[i] n : ℝ) := by exact_mod_cast segMin_le hi
      exact one_div_le_one_div_of_le (by linarith) h2
    rw [Finset.sum_const, nsmul_eq_mul] at h1
    calc harmSum n m ≤ ((oddSteps n m).card : ℝ) * (1 / (segMin n m : ℝ)) := h1
      _ = ((oddSteps n m).card : ℝ) / (segMin n m : ℝ) := by ring
  rw [harmonicMean, le_div_iff₀ hHpos]
  have hcard : (0 : ℝ) ≤ ((oddSteps n m).card : ℝ) := by positivity
  calc (segMin n m : ℝ) * harmSum n m
      ≤ (segMin n m : ℝ) * (((oddSteps n m).card : ℝ) / (segMin n m : ℝ)) := by
        apply mul_le_mul_of_nonneg_left hH (by linarith)
    _ = ((oddSteps n m).card : ℝ) := by field_simp

/-- **On every acyclic paradoxical segment**, the harmonic mean of the odd-step values is
below `a/(3Λ)`.  Hard half of Rozier–Terracol Theorem 4.2 (harmonic-mean form); no novelty
claimed. -/
theorem acyclicParadoxical_harmonicMean_lt (n m : ℕ) (h : AcyclicParadoxical n m) :
    harmonicMean n m < (ones (traceWord n m) : ℝ) /
      (3 * ((m : ℝ) * Real.log 2 - (ones (traceWord n m) : ℝ) * Real.log 3)) :=
  harmonicMean_lt_of_subcritical n m h.2.2.2 h.2.2.1

/-! ### Kernel control on `(7, 8)` -/

/-- **Kernel control.**  On `AcyclicParadoxical 7 8` the odd-step values are `7,11,17,13,5`,
so `H = 1/7 + 1/11 + 1/17 + 1/13 + 1/5`, `a = 5`, and `2^8 < (3 + H/5)^5`. -/
theorem harmonicMean_control_seven_eight :
    harmSum 7 8 = 1/7 + 1/11 + 1/17 + 1/13 + 1/5 ∧
    (oddSteps 7 8).card = 5 ∧
    (2 : ℝ) ^ 8 < (3 + harmSum 7 8 / 5) ^ 5 := by
  have hI : oddSteps 7 8 = {0, 1, 2, 4, 7} := trunkBound_control_seven_eight.1
  have hH : harmSum 7 8 = 1/7 + 1/11 + 1/17 + 1/13 + 1/5 := by
    rw [harmSum, hI]
    norm_num [tstep]
  refine ⟨hH, by rw [hI]; decide, ?_⟩
  rw [hH]
  norm_num

end CollatzMoonshot.FrontA
