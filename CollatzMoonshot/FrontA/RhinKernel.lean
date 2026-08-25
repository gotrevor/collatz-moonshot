/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Rhin's six-factor kernel: exact floor and arithmetic balances

This file records the elementary arithmetic skeleton of the auxiliary polynomial used for
Rhin's asymptotic linear-independence measure of `{1, log 2, log 3}`.  The six printed decimal
weights are treated as exact rationals with denominator `10^6`.

Three weighted identities are load-bearing:

* the polynomial degrees sum to `2n` before floor losses;
* the 2-adic contents of `Qᵢ(12x)` sum to `2n` before floor losses;
* the 3-adic contents of `Qᵢ(12x)` sum to `n` before floor losses.

The factor contents after `x ↦ 12x` are

```text
              Q₁       Q₂       Q₃       Q₄       Q₅          Q₆
content       3        2        4        12       72          144
(v₂,v₃)      (0,1)    (1,0)    (2,0)    (2,1)    (3,2)       (4,2).
```

Consequently Rhin's constant prefactor `12^7` absorbs every floor loss and leaves a scalar
divisible by `12^n`.  This is the arithmetic condition that clears the endpoint powers in the
integrals over `[2,3]` and `[3,4]`.

Source warning: Wu 2003, Theorem 2 prints `Δ = gcd(a₁,...,aₘ)`, but the displayed termwise
integrality argument for negative powers requires a common *multiple* of the endpoints.  In this
specialization the operative scale is `lcm(2,3,4) = 12`; the exact balances below independently
confirm that reading.  No transcendence or analytic estimate is asserted here.
-/

namespace CollatzMoonshot.FrontA

def rhinScale : ℕ := 1000000

def rhinE1 (n : ℕ) : ℕ := 704324 * n / rhinScale
def rhinE2 (n : ℕ) : ℕ := 552418 * n / rhinScale
def rhinE3 (n : ℕ) : ℕ := 447582 * n / rhinScale
def rhinE4 (n : ℕ) : ℕ := 109072 * n / rhinScale
def rhinE5 (n : ℕ) : ℕ := 38934 * n / rhinScale
def rhinE6 (n : ℕ) : ℕ := 54368 * n / rhinScale

/-- Degree of the product of Rhin's six factors (the constant `12^7` is omitted). -/
def rhinDegree (n : ℕ) : ℕ :=
  rhinE1 n + rhinE2 n + rhinE3 n + rhinE4 n + 2 * rhinE5 n + 2 * rhinE6 n

/-- 2-adic valuation supplied by the contents of `12^7 · ∏ Qᵢ(12x)^⌊bᵢn⌋`. -/
def rhinContentV2 (n : ℕ) : ℕ :=
  14 + rhinE2 n + 2 * rhinE3 n + 2 * rhinE4 n + 3 * rhinE5 n + 4 * rhinE6 n

/-- 3-adic valuation supplied by the contents of `12^7 · ∏ Qᵢ(12x)^⌊bᵢn⌋`. -/
def rhinContentV3 (n : ℕ) : ℕ :=
  7 + rhinE1 n + rhinE4 n + 2 * rhinE5 n + 2 * rhinE6 n

/-- The scalar content isolated from `12^7 · ∏ Qᵢ(12x)^⌊bᵢn⌋`. -/
def rhinContent (n : ℕ) : ℕ := 2 ^ rhinContentV2 n * 3 ^ rhinContentV3 n

/-- The six exact weights have total polynomial degree `2`. -/
theorem rhin_degree_weight_balance :
    704324 + 552418 + 447582 + 109072 + 2 * 38934 + 2 * 54368 = 2 * rhinScale := by
  norm_num [rhinScale]

/-- Their `Qᵢ(12x)` contents have total 2-adic valuation `2`. -/
theorem rhin_v2_weight_balance :
    552418 + 2 * 447582 + 2 * 109072 + 3 * 38934 + 4 * 54368 = 2 * rhinScale := by
  norm_num [rhinScale]

/-- Their `Qᵢ(12x)` contents have total 3-adic valuation `1`. -/
theorem rhin_v3_weight_balance :
    704324 + 109072 + 2 * 38934 + 2 * 54368 = rhinScale := by
  norm_num [rhinScale]

private theorem floor_lt_succ_mul (a n : ℕ) :
    a * n < (a * n / 1000000 + 1) * 1000000 := by
  exact (Nat.div_lt_iff_lt_mul (by norm_num)).mp (Nat.lt_succ_self _)

/-- Floor losses can only lower the degree: `deg Hₙ ≤ 2n`. -/
theorem rhinDegree_le (n : ℕ) : rhinDegree n ≤ 2 * n := by
  have h1 := Nat.mul_div_le (704324 * n) rhinScale
  have h2 := Nat.mul_div_le (552418 * n) rhinScale
  have h3 := Nat.mul_div_le (447582 * n) rhinScale
  have h4 := Nat.mul_div_le (109072 * n) rhinScale
  have h5 := Nat.mul_div_le (38934 * n) rhinScale
  have h6 := Nat.mul_div_le (54368 * n) rhinScale
  dsimp [rhinDegree, rhinE1, rhinE2, rhinE3, rhinE4, rhinE5, rhinE6, rhinScale] at *
  omega

/-- The central coefficient `[xⁿ]Hₙ` is within the degree range for every `n ≥ 2`. -/
theorem le_rhinDegree (n : ℕ) (hn : 2 ≤ n) : n ≤ rhinDegree n := by
  by_cases hn8 : 8 ≤ n
  · have h1 := floor_lt_succ_mul 704324 n
    have h2 := floor_lt_succ_mul 552418 n
    have h3 := floor_lt_succ_mul 447582 n
    have h4 := floor_lt_succ_mul 109072 n
    have h5 := floor_lt_succ_mul 38934 n
    have h6 := floor_lt_succ_mul 54368 n
    dsimp [rhinDegree, rhinE1, rhinE2, rhinE3, rhinE4, rhinE5, rhinE6, rhinScale] at *
    omega
  · interval_cases n <;> native_decide

/-- Rhin's `12^7` prefactor covers all 2-adic floor losses. -/
theorem two_mul_le_rhinContentV2 (n : ℕ) : 2 * n ≤ rhinContentV2 n := by
  have h2 := floor_lt_succ_mul 552418 n
  have h3 := floor_lt_succ_mul 447582 n
  have h4 := floor_lt_succ_mul 109072 n
  have h5 := floor_lt_succ_mul 38934 n
  have h6 := floor_lt_succ_mul 54368 n
  dsimp [rhinContentV2, rhinE2, rhinE3, rhinE4, rhinE5, rhinE6, rhinScale] at *
  omega

/-- Rhin's `12^7` prefactor covers all 3-adic floor losses. -/
theorem le_rhinContentV3 (n : ℕ) : n ≤ rhinContentV3 n := by
  have h1 := floor_lt_succ_mul 704324 n
  have h4 := floor_lt_succ_mul 109072 n
  have h5 := floor_lt_succ_mul 38934 n
  have h6 := floor_lt_succ_mul 54368 n
  dsimp [rhinContentV3, rhinE1, rhinE4, rhinE5, rhinE6, rhinScale] at *
  omega

/-- **Exact arithmetic payoff:** the isolated scalar content is divisible by `12ⁿ`.

After the elementary factorizations of `Qᵢ(12x)` listed in the module docstring, this is precisely
the coefficient divisibility needed to put the scaled Rhin polynomial in the ideal `(12,x)^n` and
clear the negative endpoint powers in both logarithmic integrals. -/
theorem twelve_pow_dvd_rhinContent (n : ℕ) : 12 ^ n ∣ rhinContent n := by
  have h2 : 2 ^ (2 * n) ∣ 2 ^ rhinContentV2 n :=
    pow_dvd_pow 2 (two_mul_le_rhinContentV2 n)
  have h3 : 3 ^ n ∣ 3 ^ rhinContentV3 n := pow_dvd_pow 3 (le_rhinContentV3 n)
  have h := Nat.mul_dvd_mul h2 h3
  have heq : 2 ^ (2 * n) = 4 ^ n := by rw [show (4 : ℕ) = 2 ^ 2 by norm_num, pow_mul]
  rw [show (12 : ℕ) = 4 * 3 by norm_num, mul_pow, ← heq]
  exact h

end CollatzMoonshot.FrontA
