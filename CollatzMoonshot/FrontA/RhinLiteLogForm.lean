/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.FrontA.RhinLiteEven
import CollatzMoonshot.FrontA.Legendre
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Exact integer log forms for the Rhin-lite remainder integrals

Objective 3 of `FRONT-A-RHIN-LITE-NEXT.md`.  The remainder integral
`∫_a^b H_N(x) / x^{N+1} dx` (with `(a,b) = (2,3)` or `(3,4)`, `H_N` the degree-`2N` integer
polynomial) expands monomial by monomial: the `x^N` term contributes the central coefficient
times `log(b/a)`, and every other term `x^j` (`j ≠ N`) contributes the rational value
`(b^{j-N} - a^{j-N})/(j-N)`.

This module begins with the elementary single-monomial integral identity, the arithmetic core
from which the two cleared integer log forms `A₁ + B·log(3/2)`, `A₂ + B·log(4/3)` (common `B`,
explicit clearing factor `D_N`) will be assembled.
-/

namespace CollatzMoonshot.FrontA

open MeasureTheory intervalIntegral Polynomial Finset

/-- **Single-monomial integral identity.**  For `0 < a ≤ b`, the integral of `x^j / x^{N+1}`
over `[a,b]` is the log term `log(b/a)` when `j = N`, and the rational value
`(b^{j-N} - a^{j-N})/(j-N)` otherwise. -/
theorem integral_monomial_div_pow {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (j N : ℕ) :
    (∫ x in a..b, x ^ j / x ^ (N + 1)) =
      if j = N then Real.log (b / a)
      else (b ^ ((j : ℤ) - N) - a ^ ((j : ℤ) - N)) / ((j : ℤ) - N) := by
  have h0 : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    simp only [Set.mem_Icc, not_and, not_le]
    intro h; linarith
  have hcongr : (∫ x in a..b, x ^ j / x ^ (N + 1)) =
      ∫ x in a..b, x ^ ((j : ℤ) - ((N + 1 : ℕ) : ℤ)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hxpos : 0 < x := lt_of_lt_of_le ha hx.1
    show x ^ j / x ^ (N + 1) = x ^ ((j : ℤ) - ((N + 1 : ℕ) : ℤ))
    rw [zpow_sub₀ (ne_of_gt hxpos), zpow_natCast, zpow_natCast]
  rw [hcongr]
  by_cases hjN : j = N
  · subst hjN
    rw [if_pos rfl]
    simp only [show ((j : ℤ) - ((j + 1 : ℕ) : ℤ)) = (-1 : ℤ) by push_cast; ring, zpow_neg_one]
    exact integral_inv h0
  · rw [if_neg hjN, integral_zpow (Or.inr ⟨by
        intro hcon
        apply hjN
        have : (j : ℤ) = N := by push_cast at hcon ⊢; linarith [hcon]
        exact_mod_cast this, h0⟩),
      show ((j : ℤ) - ((N + 1 : ℕ) : ℤ) + 1) = (j : ℤ) - N by push_cast; ring]
    congr 1
    push_cast
    ring

/-- Interval-integrability of a single monomial-over-power term on `[a,b]` with `0 < a`. -/
theorem intervalIntegrable_monomial_div_pow {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (j N : ℕ) :
    IntervalIntegrable (fun x => x ^ j / x ^ (N + 1)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div (continuous_pow j).continuousOn (continuous_pow (N + 1)).continuousOn
  intro x hx
  rw [Set.uIcc_of_le hab] at hx
  exact pow_ne_zero _ (by linarith [hx.1] : x ≠ 0)

/-- **Full remainder-integral expansion.**  For any real polynomial `p` and `0 < a ≤ b`,
`∫_a^b p(x)/x^{N+1} dx` expands as the coefficient sum in which the `x^N` term carries
`log(b/a)` and every other term is rational. -/
theorem integral_poly_div_pow {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (p : ℝ[X]) (N : ℕ) :
    (∫ x in a..b, p.eval x / x ^ (N + 1)) =
      ∑ j ∈ range (p.natDegree + 1),
        p.coeff j * (if j = N then Real.log (b / a)
          else (b ^ ((j : ℤ) - N) - a ^ ((j : ℤ) - N)) / ((j : ℤ) - N)) := by
  have hcongr : (∫ x in a..b, p.eval x / x ^ (N + 1)) =
      ∫ x in a..b, ∑ j ∈ range (p.natDegree + 1), p.coeff j * (x ^ j / x ^ (N + 1)) := by
    apply intervalIntegral.integral_congr
    intro x _
    show p.eval x / x ^ (N + 1) = ∑ j ∈ range (p.natDegree + 1), p.coeff j * (x ^ j / x ^ (N + 1))
    rw [eval_eq_sum_range, Finset.sum_div]
    exact Finset.sum_congr rfl (fun j _ => mul_div_assoc _ _ _)
  rw [hcongr, intervalIntegral.integral_finsetSum
    (fun j _ => (intervalIntegrable_monomial_div_pow ha hab j N).const_mul _)]
  exact Finset.sum_congr rfl (fun j _ => by
    rw [intervalIntegral.integral_const_mul, integral_monomial_div_pow ha hab])

/-- **Log term split out.**  When `N ≤ deg p`, the remainder integral is the single log term
`coeff_N · log(b/a)` plus a rational tail summed over the other indices. -/
theorem integral_poly_div_pow_split {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (p : ℝ[X]) (N : ℕ)
    (hN : N ≤ p.natDegree) :
    (∫ x in a..b, p.eval x / x ^ (N + 1)) =
      p.coeff N * Real.log (b / a) +
        ∑ j ∈ (range (p.natDegree + 1)).erase N,
          p.coeff j * ((b ^ ((j : ℤ) - N) - a ^ ((j : ℤ) - N)) / ((j : ℤ) - N)) := by
  rw [integral_poly_div_pow ha hab,
    ← Finset.add_sum_erase _ _ (mem_range.mpr (by omega : N < p.natDegree + 1))]
  congr 1
  · rw [if_pos rfl]
  · exact Finset.sum_congr rfl (fun j hj => by rw [if_neg (Finset.ne_of_mem_erase hj)])

/-! ## Denominator-clearing arithmetic for the rational tail -/

/-- Each tail denominator `j - N` (with `j ≤ 2N`, `j ≠ N`, so `1 ≤ |j-N| ≤ N`) divides
`lcmUpto N`. -/
theorem sub_natCast_dvd_lcmUpto {j N : ℕ} (hj : j ≤ 2 * N) (hjN : j ≠ N) :
    ((j : ℤ) - N) ∣ (Nat.lcmUpto N : ℤ) := by
  rw [← Int.natAbs_dvd]
  have h1 : 1 ≤ ((j : ℤ) - N).natAbs := by omega
  have h2 : ((j : ℤ) - N).natAbs ≤ N := by omega
  exact_mod_cast dvd_lcmUpto h1 h2

/-- An endpoint `e ∈ {2,3,4}` raised to a power `≤ N` divides `12^N` (since `e ∣ 12`). -/
theorem endpoint_pow_dvd_twelve_pow {e : ℤ} (he : e ∣ 12) {m N : ℕ} (hm : m ≤ N) :
    e ^ m ∣ (12 : ℤ) ^ N := by
  calc e ^ m ∣ (12 : ℤ) ^ m := pow_dvd_pow_of_dvd he m
    _ ∣ (12 : ℤ) ^ N := pow_dvd_pow 12 hm

/-- For a positive endpoint `e ∣ 12` and any exponent `k ≥ -N`, the real number
`12^N · e^k` is an integer (negative powers are cleared by `12^N`). -/
theorem twelve_pow_mul_zpow_isInt {e : ℤ} (he : e ∣ 12) (hepos : 0 < e) {k : ℤ} {N : ℕ}
    (hk : -(N : ℤ) ≤ k) : ∃ z : ℤ, (12 : ℝ) ^ N * (e : ℝ) ^ k = (z : ℝ) := by
  have hepos' : (0 : ℝ) < (e : ℝ) := by exact_mod_cast hepos
  rcases le_total 0 k with hk0 | hk0
  · refine ⟨12 ^ N * e ^ k.toNat, ?_⟩
    push_cast
    rw [← zpow_natCast (e : ℝ) k.toNat, Int.toNat_of_nonneg hk0]
  · set m := (-k).toNat with hm_def
    have hmk : (m : ℤ) = -k := Int.toNat_of_nonneg (by omega)
    have hmN : m ≤ N := by omega
    obtain ⟨w, hw⟩ := endpoint_pow_dvd_twelve_pow he hmN
    refine ⟨w, ?_⟩
    have hem : (e : ℝ) ^ m ≠ 0 := by positivity
    have hk' : (e : ℝ) ^ k = ((e : ℝ) ^ m)⁻¹ := by
      rw [show k = -(m : ℤ) by omega, zpow_neg, zpow_natCast]
    have hwR : (12 : ℝ) ^ N = (e : ℝ) ^ m * (w : ℝ) := by
      have := congrArg (fun n : ℤ => (n : ℝ)) hw
      push_cast at this
      rw [this]
    rw [hk', hwR]
    field_simp

/-- **Single tail term is cleared to an integer** by `D_N = lcmUpto N · 12^N`.  Endpoints
`ea, eb ∈ {2,3,4}` (positive divisors of `12`); `c` is the integer coefficient. -/
theorem tail_term_cleared {ea eb : ℤ} (hea : ea ∣ 12) (heb : eb ∣ 12)
    (heap : 0 < ea) (hebp : 0 < eb) (c : ℤ) {j N : ℕ} (hj : j ≤ 2 * N) (hjN : j ≠ N) :
    ∃ m : ℤ, (Nat.lcmUpto N : ℝ) * 12 ^ N *
        ((c : ℝ) * (((eb : ℝ) ^ ((j : ℤ) - N) - (ea : ℝ) ^ ((j : ℤ) - N)) /
          ((j : ℤ) - N))) = (m : ℝ) := by
  set k : ℤ := (j : ℤ) - N with hk_def
  have hkz : k ≠ 0 := by rw [hk_def]; intro h; apply hjN; omega
  have hkne : (k : ℝ) ≠ 0 := by exact_mod_cast hkz
  have hkbound : -(N : ℤ) ≤ k := by rw [hk_def]; omega
  obtain ⟨zb, hzb⟩ := twelve_pow_mul_zpow_isInt heb hebp (k := k) (N := N) hkbound
  obtain ⟨za, hza⟩ := twelve_pow_mul_zpow_isInt hea heap (k := k) (N := N) hkbound
  obtain ⟨q, hq⟩ := sub_natCast_dvd_lcmUpto hj hjN
  refine ⟨c * q * (zb - za), ?_⟩
  have hqR : (Nat.lcmUpto N : ℝ) = (k : ℝ) * (q : ℝ) := by rw [hk_def]; exact_mod_cast hq
  have hdiv : (Nat.lcmUpto N : ℝ) / (k : ℝ) = (q : ℝ) := by
    rw [hqR, mul_comm, mul_div_assoc, div_self hkne, mul_one]
  rw [show ((j : ℤ) : ℝ) - (N : ℝ) = (k : ℝ) by rw [hk_def]; push_cast; ring]
  calc (Nat.lcmUpto N : ℝ) * 12 ^ N *
          ((c : ℝ) * (((eb : ℝ) ^ k - (ea : ℝ) ^ k) / k))
      = 12 ^ N * (c : ℝ) * ((Nat.lcmUpto N : ℝ) / (k : ℝ)) * ((eb : ℝ) ^ k - (ea : ℝ) ^ k) := by
        ring
    _ = (c : ℝ) * q * (12 ^ N * (eb : ℝ) ^ k) - (c : ℝ) * q * (12 ^ N * (ea : ℝ) ^ k) := by
        rw [hdiv]; ring
    _ = (c : ℝ) * q * (zb : ℝ) - (c : ℝ) * q * (za : ℝ) := by rw [hzb, hza]
    _ = ((c * q * (zb - za) : ℤ) : ℝ) := by push_cast; ring

/-- A finite sum of integer-valued reals is integer-valued. -/
theorem isInt_finset_sum {α : Type*} (s : Finset α) (g : α → ℝ)
    (h : ∀ a ∈ s, ∃ m : ℤ, g a = (m : ℝ)) : ∃ M : ℤ, ∑ a ∈ s, g a = (M : ℝ) := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨0, by simp⟩
  | @insert a t ha ih =>
      obtain ⟨m, hm⟩ := h a (Finset.mem_insert_self a t)
      obtain ⟨M, hM⟩ := ih (fun b hb => h b (Finset.mem_insert_of_mem hb))
      exact ⟨m + M, by rw [Finset.sum_insert ha, hm, hM]; push_cast; ring⟩

/-- **The `D_N`-cleared integer log form.**  For an integer polynomial `P` of degree `≤ 2N`
(and `≥ N`), positive endpoints `ea ≤ eb` dividing `12`, there is an integer `A` with

`D_N · ∫_{ea}^{eb} P(x)/x^{N+1} dx = A + B · log(eb/ea)`,

where `D_N = lcmUpto N · 12^N` and `B = D_N · P.coeff N` is an explicit integer. -/
theorem lcm_cleared_log_form (P : ℤ[X]) {ea eb : ℤ} (hea : ea ∣ 12) (heb : eb ∣ 12)
    (heap : 0 < ea) (hebp : 0 < eb) (hab : ea ≤ eb) (N : ℕ)
    (hdeg : (P.map (Int.castRingHom ℝ)).natDegree ≤ 2 * N)
    (hN : N ≤ (P.map (Int.castRingHom ℝ)).natDegree) :
    ∃ A : ℤ, (Nat.lcmUpto N : ℝ) * 12 ^ N *
        (∫ x in (ea : ℝ)..(eb : ℝ),
          (P.map (Int.castRingHom ℝ)).eval x / x ^ (N + 1))
      = (A : ℝ) + ((Nat.lcmUpto N * 12 ^ N * P.coeff N : ℤ) : ℝ) *
          Real.log ((eb : ℝ) / (ea : ℝ)) := by
  classical
  set p := P.map (Int.castRingHom ℝ) with hp
  have ha : (0 : ℝ) < (ea : ℝ) := by exact_mod_cast heap
  have hab' : (ea : ℝ) ≤ (eb : ℝ) := by exact_mod_cast hab
  have hcoeff : ∀ j : ℕ, p.coeff j = ((P.coeff j : ℤ) : ℝ) := by
    intro j; rw [hp, coeff_map]; simp
  obtain ⟨A, hA⟩ := isInt_finset_sum ((range (p.natDegree + 1)).erase N)
    (fun j => (Nat.lcmUpto N : ℝ) * 12 ^ N *
      (p.coeff j * (((eb : ℝ) ^ ((j : ℤ) - N) - (ea : ℝ) ^ ((j : ℤ) - N)) / ((j : ℤ) - N))))
    (by
      intro j hj
      have hjN : j ≠ N := (Finset.mem_erase.mp hj).1
      have hjr : j < p.natDegree + 1 := Finset.mem_range.mp (Finset.mem_erase.mp hj).2
      have hj2 : j ≤ 2 * N := by omega
      rw [hcoeff j]
      exact tail_term_cleared hea heb heap hebp (P.coeff j) hj2 hjN)
  refine ⟨A, ?_⟩
  rw [integral_poly_div_pow_split ha hab' p N hN, mul_add, Finset.mul_sum, hA, add_comm]
  congr 1
  rw [hcoeff N]
  push_cast
  ring

/-! ## The integer even polynomial `H_N` and the two concrete log forms -/

/-- The signed six-factor polynomial at `N = 2000t`, over `ℤ` (the same object as
`rhinLiteEvenPolynomial` but with integer coefficients). -/
noncomputable def rhinLiteEvenPolynomialZ (t : ℕ) : ℤ[X] :=
  rhinLiteQ1 ^ (2 * rhinLiteW1 * t) * rhinLiteQ2 ^ (2 * rhinLiteW2 * t) *
    rhinLiteQ3 ^ (2 * rhinLiteW3 * t) * rhinLiteQ4 ^ (2 * rhinLiteW4 * t) *
    rhinLiteQ5 ^ (2 * rhinLiteW5 * t) * rhinLiteQ6 ^ (2 * rhinLiteW6 * t)

/-- `H_N` casts to the rational even polynomial. -/
theorem rhinLiteEvenPolynomialZ_map_rat (t : ℕ) :
    (rhinLiteEvenPolynomialZ t).map (Int.castRingHom ℚ) = rhinLiteEvenPolynomial t := by
  simp only [rhinLiteEvenPolynomialZ, rhinLiteEvenPolynomial, Polynomial.map_mul,
    Polynomial.map_pow, rhinLiteQ1, rhinLiteQ2, rhinLiteQ3, rhinLiteQ4, rhinLiteQ5, rhinLiteQ6,
    Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, map_X, map_C,
    map_ofNat]
  norm_num

/-- `H_N` has exact degree `2N`. -/
theorem rhinLiteEvenPolynomialZ_natDegree (t : ℕ) :
    (rhinLiteEvenPolynomialZ t).natDegree = 2 * rhinLiteEvenIndex t := by
  rw [rhinLiteEvenPolynomialZ, rhinLiteEvenIndex, rhinLiteQ1, rhinLiteQ2, rhinLiteQ3,
    rhinLiteQ4, rhinLiteQ5, rhinLiteQ6]
  compute_degree!
  all_goals simp only [rhinLiteScale, rhinLiteW1, rhinLiteW2, rhinLiteW3, rhinLiteW4,
    rhinLiteW5, rhinLiteW6]
  all_goals omega

/-- The real cast of `H_N` also has degree `2N`. -/
theorem rhinLiteEvenPolynomialZ_map_real_natDegree (t : ℕ) :
    ((rhinLiteEvenPolynomialZ t).map (Int.castRingHom ℝ)).natDegree =
      2 * rhinLiteEvenIndex t := by
  rw [natDegree_map_eq_of_injective (by exact_mod_cast Int.cast_injective),
    rhinLiteEvenPolynomialZ_natDegree]

/-- `H_N`'s central integer coefficient lies in the promised `[17^N, 18^N]` band. -/
theorem rhinLiteEvenPolynomialZ_centralCoeff_bounds (t : ℕ) :
    (17 : ℤ) ^ rhinLiteEvenIndex t ≤
        (rhinLiteEvenPolynomialZ t).coeff (rhinLiteEvenIndex t) ∧
      (rhinLiteEvenPolynomialZ t).coeff (rhinLiteEvenIndex t) ≤
        (18 : ℤ) ^ rhinLiteEvenIndex t := by
  have hmap : ((rhinLiteEvenPolynomialZ t).coeff (rhinLiteEvenIndex t) : ℚ) =
      (rhinLiteEvenPolynomial t).coeff (rhinLiteEvenIndex t) := by
    rw [← rhinLiteEvenPolynomialZ_map_rat, coeff_map]; simp
  obtain ⟨hlo, hhi⟩ := rhinLiteEvenPolynomial_centralCoeff_bounds t
  refine ⟨?_, ?_⟩
  · have : (17 : ℚ) ^ rhinLiteEvenIndex t ≤
        ((rhinLiteEvenPolynomialZ t).coeff (rhinLiteEvenIndex t) : ℚ) := by rw [hmap]; exact hlo
    exact_mod_cast this
  · have : ((rhinLiteEvenPolynomialZ t).coeff (rhinLiteEvenIndex t) : ℚ) ≤
        (18 : ℚ) ^ rhinLiteEvenIndex t := by rw [hmap]; exact hhi
    exact_mod_cast this

/-- **The two `D_N`-cleared integer log forms with a common `B`.**  With
`N = rhinLiteEvenIndex t`, `D_N = lcmUpto N · 12^N`, and `p` the real cast of `H_N`, there are
integers `A₁, A₂, B` such that

`D_N·∫_2^3 p/x^{N+1} = A₁ + B·log(3/2)`,  `D_N·∫_3^4 p/x^{N+1} = A₂ + B·log(4/3)`,

the same `B`, with `D_N·17^N ≤ B ≤ D_N·18^N`. -/
theorem rhinLiteEven_two_log_forms (t : ℕ) :
    ∃ A₁ A₂ B : ℤ,
      ((Nat.lcmUpto (rhinLiteEvenIndex t) : ℝ) * 12 ^ rhinLiteEvenIndex t *
          (∫ x in (2 : ℝ)..3,
            ((rhinLiteEvenPolynomialZ t).map (Int.castRingHom ℝ)).eval x /
              x ^ (rhinLiteEvenIndex t + 1))
        = (A₁ : ℝ) + (B : ℝ) * Real.log (3 / 2)) ∧
      ((Nat.lcmUpto (rhinLiteEvenIndex t) : ℝ) * 12 ^ rhinLiteEvenIndex t *
          (∫ x in (3 : ℝ)..4,
            ((rhinLiteEvenPolynomialZ t).map (Int.castRingHom ℝ)).eval x /
              x ^ (rhinLiteEvenIndex t + 1))
        = (A₂ : ℝ) + (B : ℝ) * Real.log (4 / 3)) ∧
      (Nat.lcmUpto (rhinLiteEvenIndex t) : ℤ) * 12 ^ rhinLiteEvenIndex t *
          17 ^ rhinLiteEvenIndex t ≤ B ∧
      B ≤ (Nat.lcmUpto (rhinLiteEvenIndex t) : ℤ) * 12 ^ rhinLiteEvenIndex t *
          18 ^ rhinLiteEvenIndex t := by
  have hdeg : ((rhinLiteEvenPolynomialZ t).map (Int.castRingHom ℝ)).natDegree ≤
      2 * rhinLiteEvenIndex t := le_of_eq (rhinLiteEvenPolynomialZ_map_real_natDegree t)
  have hN : rhinLiteEvenIndex t ≤
      ((rhinLiteEvenPolynomialZ t).map (Int.castRingHom ℝ)).natDegree := by
    rw [rhinLiteEvenPolynomialZ_map_real_natDegree]; omega
  obtain ⟨A₁, h₁⟩ := lcm_cleared_log_form (rhinLiteEvenPolynomialZ t) (ea := 2) (eb := 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (rhinLiteEvenIndex t) hdeg hN
  obtain ⟨A₂, h₂⟩ := lcm_cleared_log_form (rhinLiteEvenPolynomialZ t) (ea := 3) (eb := 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (rhinLiteEvenIndex t) hdeg hN
  refine ⟨A₁, A₂,
    (Nat.lcmUpto (rhinLiteEvenIndex t) : ℤ) * 12 ^ rhinLiteEvenIndex t *
      (rhinLiteEvenPolynomialZ t).coeff (rhinLiteEvenIndex t), ?_, ?_, ?_, ?_⟩
  · simpa using h₁
  · simpa using h₂
  · obtain ⟨hlo, _⟩ := rhinLiteEvenPolynomialZ_centralCoeff_bounds t
    have hD : (0 : ℤ) ≤ (Nat.lcmUpto (rhinLiteEvenIndex t) : ℤ) * 12 ^ rhinLiteEvenIndex t := by
      positivity
    calc (Nat.lcmUpto (rhinLiteEvenIndex t) : ℤ) * 12 ^ rhinLiteEvenIndex t *
            17 ^ rhinLiteEvenIndex t
        ≤ (Nat.lcmUpto (rhinLiteEvenIndex t) : ℤ) * 12 ^ rhinLiteEvenIndex t *
            (rhinLiteEvenPolynomialZ t).coeff (rhinLiteEvenIndex t) :=
          mul_le_mul_of_nonneg_left hlo hD
      _ = _ := by ring
  · obtain ⟨_, hhi⟩ := rhinLiteEvenPolynomialZ_centralCoeff_bounds t
    have hD : (0 : ℤ) ≤ (Nat.lcmUpto (rhinLiteEvenIndex t) : ℤ) * 12 ^ rhinLiteEvenIndex t := by
      positivity
    exact mul_le_mul_of_nonneg_left hhi hD

end CollatzMoonshot.FrontA
