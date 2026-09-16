/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license.
-/
import CollatzMoonshot.FrontB.Eliahou
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Eliahou's cycle-length method at the repository's own `2^68` frontier

`CollatzMoonshot.FrontB.Eliahou` formalises Eliahou's 1993 argument and runs it through the
Farey pair `16785921/10590737 < log₂ 3 < 301994/190537`, reproducing his published
`27 869 189`.  That pair is far from optimal once the verification frontier is `2^68`: the
interval `(log₂ 3, log₂ (3 + 2^{-68}))` has width `≈ 1.63·10^{-21}`, so the Farey neighbours
that straddle *it* have much larger denominators, namely

    c₁ = 103768467013 / 65470613321  <  log₂ 3  <  log₂ (3 + 2^{-68})  <  10439860591 / 6586818670 = c₂

(`65470613321 · 10439860591 − 103768467013 · 6586818670 = 1`).  The denominator sum is
`72 057 431 991`, which is therefore a lower bound on the number of odd members of any
nontrivial cycle, and the corresponding shortcut length is `114 208 327 604`; total period
at least `186 265 759 595`.

This is **Eliahou's method**, not Hercher 2023 Cor. 29: Hercher's `1.375·10¹¹` odd members
needs his residue-class computation on top of the continued fraction, and the pure Farey step
at his frontier `X₀ = 2075·2^60` gives the same `72 057 431 991`.  So
`Assumed.hercher_odd_members_bound` remains a citation axiom.  Cite Eliahou §3.

At this size the node-3 style `native_decide` certificates `2^p < 3^q` are infeasible
(`q ≈ 6.5·10^10`, i.e. numerals of `~10^11` bits).  They are replaced by **certified rational
bounds on `log 2` and `log (3/2)` to 30 decimal places**, obtained from
`Real.abs_log_sub_add_sum_range_le` with `90` resp. `58` Taylor terms; the finite rational
sums are evaluated by `norm_num`.  Consequently this module mints **no** `native_decide`
axiom, and the results stand on `Assumed.collatz_verified_up_to_two_pow_68` plus the
classical trio.
-/

namespace CollatzMoonshot.FrontB.EliahouFrontier

open CollatzMoonshot.FrontB.Eliahou

/-! ### Certified bounds on `log 2` and `log (3/2)` -/

private theorem sum2_lower :
    (693147180559945309417232120641 / 10 ^ 30 : ℝ) + (1 / 2) ^ 90
      < ∑ i ∈ Finset.range 90, ((1:ℝ) / 2) ^ (i + 1) / (i + 1) := by
  norm_num [Finset.sum_range_succ]

private theorem sum2_upper :
    (∑ i ∈ Finset.range 90, ((1:ℝ) / 2) ^ (i + 1) / (i + 1)) + (1 / 2) ^ 90
      < 693147180559945309417232122258 / 10 ^ 30 := by
  norm_num [Finset.sum_range_succ]

private theorem sum3_lower :
    (405465108108164381978013115356 / 10 ^ 30 : ℝ) + (3 / 2) * (1 / 3) ^ 59
      < ∑ i ∈ Finset.range 58, ((1:ℝ) / 3) ^ (i + 1) / (i + 1) := by
  norm_num [Finset.sum_range_succ]

private theorem sum3_upper :
    (∑ i ∈ Finset.range 58, ((1:ℝ) / 3) ^ (i + 1) / (i + 1)) + (3 / 2) * (1 / 3) ^ 59
      < 405465108108164381978013115569 / 10 ^ 30 := by
  norm_num [Finset.sum_range_succ]

/-- `log 2` to 30 decimals, from the first `90` Taylor terms of `−log(1 − x)` at `x = 1/2`
(truncation error `≤ 2^{-90} < 10^{-27}`). -/
theorem log_two_bounds_26 :
    (693147180559945309417232120641 / 10 ^ 30 : ℝ) < Real.log 2 ∧
      Real.log 2 < 693147180559945309417232122258 / 10 ^ 30 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (1 / 2 : ℝ)) (by norm_num) 90
  have hx : (1 : ℝ) - 1 / 2 = 2⁻¹ := by norm_num
  rw [hx, Real.log_inv] at h
  have hr : |(1 / 2 : ℝ)| ^ (90 + 1) / (1 - |(1 / 2 : ℝ)|) = (1 / 2 : ℝ) ^ 90 := by
    rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2), div_eq_iff (by norm_num)]
    ring
  rw [hr, abs_le] at h
  exact ⟨by linarith [h.2, sum2_lower], by linarith [h.1, sum2_upper]⟩

/-- `log (3/2)` to 30 decimals, from the first `58` Taylor terms at `x = 1/3`
(truncation error `≤ (3/2)·3^{-59} < 10^{-27}`). -/
theorem log_three_halves_bounds_26 :
    (405465108108164381978013115356 / 10 ^ 30 : ℝ) < Real.log (3 / 2) ∧
      Real.log (3 / 2) < 405465108108164381978013115569 / 10 ^ 30 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (1 / 3 : ℝ)) (by norm_num) 58
  have hx : (1 : ℝ) - 1 / 3 = (3 / 2)⁻¹ := by norm_num
  rw [hx, Real.log_inv] at h
  have hr : |(1 / 3 : ℝ)| ^ (58 + 1) / (1 - |(1 / 3 : ℝ)|) = (3 / 2) * (1 / 3 : ℝ) ^ 59 := by
    rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/3), div_eq_iff (by norm_num)]
    ring
  rw [hr, abs_le] at h
  exact ⟨by linarith [h.2, sum3_lower], by linarith [h.1, sum3_upper]⟩

theorem log_three_eq : Real.log 3 = Real.log 2 + Real.log (3 / 2) := by
  rw [← Real.log_mul (by norm_num) (by norm_num)]
  norm_num

/-- `c₁ = 103768467013/65470613321 < log₂ 3`, in cleared form. -/
theorem key_lower : (103768467013 : ℝ) * Real.log 2 < 65470613321 * Real.log 3 := by
  rw [log_three_eq]
  have h2 := log_two_bounds_26.2
  have h3 := log_three_halves_bounds_26.1
  nlinarith [h2, h3]

/-- `log₂ (3 + 2^{-68}) < c₂ = 10439860591/6586818670`, in cleared form. -/
theorem key_upper :
    (6586818670 : ℝ) * Real.log (3 + 1 / 2 ^ 68) < 10439860591 * Real.log 2 := by
  have hsplit : (3 : ℝ) + 1 / 2 ^ 68 = 3 * (1 + 1 / (3 * 2 ^ 68)) := by ring
  have hpos : (0 : ℝ) < 1 + 1 / (3 * 2 ^ 68) := by positivity
  have hle : Real.log (1 + 1 / (3 * 2 ^ 68)) ≤ 1 / (3 * 2 ^ 68) := by
    have := Real.log_le_sub_one_of_pos hpos
    linarith
  have hlog : Real.log (3 + 1 / 2 ^ 68)
      ≤ Real.log 2 + Real.log (3 / 2) + 1 / (3 * 2 ^ 68) := by
    rw [hsplit, Real.log_mul (by norm_num) (ne_of_gt hpos), ← log_three_eq]
    linarith [hle]
  have h2 := log_two_bounds_26.1
  have h3 := log_three_halves_bounds_26.2
  nlinarith [hlog, h2, h3]

/-! ### The two rational inequalities on a cycle -/

theorem log_two_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)

/-- From `3^a < 2^e` and `c₁ < log₂ 3`: `c₁ < e/a` in cleared form. -/
theorem lower_ineq {a e : ℕ} (ha : 0 < a) (hA : 3 ^ a < 2 ^ e) :
    103768467013 * a < e * 65470613321 := by
  have hR : ((3 : ℝ)) ^ a < 2 ^ e := by exact_mod_cast hA
  have hlog : (a : ℝ) * Real.log 3 < e * Real.log 2 := by
    have := Real.log_lt_log (by positivity) hR
    rwa [Real.log_pow, Real.log_pow] at this
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have : (103768467013 : ℝ) * a * Real.log 2 < (e : ℝ) * 65470613321 * Real.log 2 := by
    nlinarith [key_lower, hlog, haR, log_two_pos]
  have := lt_of_mul_lt_mul_right (by linarith [this] : (103768467013 : ℝ) * a * Real.log 2
      < (e : ℝ) * 65470613321 * Real.log 2) log_two_pos.le
  exact_mod_cast this

/-- From `2^e (2^68)^a ≤ (3·2^68+1)^a` and `log₂ (3 + 2^{-68}) < c₂`: `e/a < c₂`. -/
theorem upper_ineq {a e : ℕ} (ha : 0 < a)
    (hB : 2 ^ e * (2 ^ 68 : ℕ) ^ a ≤ (3 * 2 ^ 68 + 1) ^ a) :
    e * 6586818670 < 10439860591 * a := by
  have hR : ((2 : ℝ)) ^ e * ((2 : ℝ) ^ 68) ^ a ≤ ((3 * 2 ^ 68 + 1 : ℝ)) ^ a := by
    exact_mod_cast hB
  have hone : ((3 : ℝ) * 2 ^ 68 + 1) = 2 ^ 68 * (3 + 1 / 2 ^ 68) := by ring
  have hlhs : Real.log ((2:ℝ) ^ e * ((2:ℝ) ^ 68) ^ a) = ((e : ℝ) + 68 * a) * Real.log 2 := by
    rw [Real.log_mul (by positivity) (by positivity), ← pow_mul, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hrhs : Real.log (((3:ℝ) * 2 ^ 68 + 1) ^ a)
      = (a : ℝ) * (68 * Real.log 2 + Real.log (3 + 1 / 2 ^ 68)) := by
    rw [Real.log_pow, hone, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    ring
  have hlog : (e : ℝ) * Real.log 2 ≤ a * Real.log (3 + 1 / 2 ^ 68) := by
    have hL := Real.log_le_log (by positivity) hR
    rw [hlhs, hrhs] at hL
    nlinarith [hL]
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hmain : (e : ℝ) * 6586818670 * Real.log 2 < 10439860591 * (a : ℝ) * Real.log 2 := by
    nlinarith [key_upper, hlog, haR, log_two_pos]
  have := lt_of_mul_lt_mul_right hmain log_two_pos.le
  exact_mod_cast this

/-! ### The arithmetic core at the frontier -/

/-- From the two cycle inequalities, the Farey step at the `2^68` frontier gives
`a ≥ 72 057 431 991` odd members and `e ≥ 114 208 327 604` even members. -/
theorem frontier_counts {a e : ℕ} (ha1 : 1 ≤ a)
    (hA : 3 ^ a < 2 ^ e)
    (hB : 2 ^ e * (2 ^ 68 : ℕ) ^ a ≤ (3 * 2 ^ 68 + 1) ^ a) :
    72057431991 ≤ a ∧ 114208327604 ≤ e := by
  have h₁ := lower_ineq (a := a) (e := e) ha1 hA
  have h₂ := upper_ineq (a := a) (e := e) ha1 hB
  have hfar : 65470613321 + 6586818670 ≤ a :=
    farey_denominator_bound (p₁ := 103768467013) (q₁ := 65470613321)
      (p₂ := 10439860591) (q₂ := 6586818670) (by norm_num) h₁ h₂
  refine ⟨by omega, by omega⟩

/-- The three hypotheses `frontier_counts` needs, extracted from a nontrivial cycle. -/
theorem cycle_inputs {n m : ℕ} (hn : 1 ≤ n) (hm : 0 < m) (hcyc : step^[m] n = n)
    (hnt : ¬(n = 1 ∨ n = 2 ∨ n = 4)) :
    1 ≤ (oddS n m).card ∧ 3 ^ (oddS n m).card < 2 ^ (evenS n m).card ∧
      2 ^ (evenS n m).card * (2 ^ 68 : ℕ) ^ (oddS n m).card
        ≤ (3 * 2 ^ 68 + 1) ^ (oddS n m).card := by
  have hx : ∀ i ∈ oddS n m, (2 : ℕ) ^ 68 ≤ step^[i] n :=
    fun i _ => (two_pow_68_lt_orbit hn hm hcyc hnt i).le
  have hne : (oddS n m).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h0
    have hid := cycle_prod_identity hn hcyc
    rw [h0] at hid
    simp only [Finset.prod_empty, mul_one] at hid
    have hcard : (evenS n m).card = m := by
      have h1 : (oddS n m).card = 0 := by rw [h0]; simp
      have := card_oddS_add_card_evenS n m
      omega
    rw [hcard] at hid
    have h2 : (1 : ℕ) < 2 ^ m := Nat.one_lt_pow (by omega) (by omega)
    omega
  exact ⟨Finset.card_pos.mpr hne, three_pow_lt_two_pow hn hcyc hne,
    two_pow_mul_pow_le hn hcyc hx⟩

/-! ### The frontier bounds -/

/-- **Odd members at the `2^68` frontier.**  Any `step`-cycle outside `{1,2,4}` visits at
least `72 057 431 991` odd values. -/
theorem odd_members_ge_of_two_pow_68 :
    ∀ n m : ℕ, 1 ≤ n → 0 < m → step^[m] n = n →
      (n = 1 ∨ n = 2 ∨ n = 4) ∨
        72057431991 ≤ ((Finset.range m).filter (fun i => step^[i] n % 2 = 1)).card := by
  intro n m hn hm hcyc
  by_cases hnt : n = 1 ∨ n = 2 ∨ n = 4
  · exact Or.inl hnt
  refine Or.inr ?_
  obtain ⟨ha1, hA, hB⟩ := cycle_inputs hn hm hcyc hnt
  show 72057431991 ≤ (oddS n m).card
  exact (frontier_counts ha1 hA hB).1

/-- **Eliahou's method at the `2^68` frontier.**  Any `step`-cycle outside `{1,2,4}` has
period at least `186 265 759 595 = 114 208 327 604 + 72 057 431 991`. -/
theorem min_cycle_length_two_pow_68 :
    ∀ n m : ℕ, 1 ≤ n → 0 < m → step^[m] n = n →
      (n = 1 ∨ n = 2 ∨ n = 4) ∨ 186265759595 ≤ m := by
  intro n m hn hm hcyc
  by_cases hnt : n = 1 ∨ n = 2 ∨ n = 4
  · exact Or.inl hnt
  refine Or.inr ?_
  obtain ⟨ha1, hA, hB⟩ := cycle_inputs hn hm hcyc hnt
  have hsum : (oddS n m).card + (evenS n m).card = m := card_oddS_add_card_evenS n m
  have := frontier_counts ha1 hA hB
  omega

end CollatzMoonshot.FrontB.EliahouFrontier
