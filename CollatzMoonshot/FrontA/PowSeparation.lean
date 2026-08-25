/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Effective separation of powers of 2 and 3, and the two-block `b + d ≤ 5` reduction

This module isolates the sole deep input behind the interior two-block exclusion
(`le_two_blocks_not_acyclicParadoxical` in `Paradoxical.lean`): after the elementary squeeze,
`window_unique_m`, and the near-critical bracket, the crux is the single inequality `b + d ≤ 5`.

That inequality is **Baker-grade** — a review lap proved that the real relaxation of the
governing constraints is feasible at unbounded `b + d`, so no `nlinarith`/polynomial certificate
can exist (`experiments/two_block_relaxation.py`).  The *only* genuinely arithmetic (integrality)
input needed is a **weak** effective separation between powers of 2 and 3, isolated here as
`sep_two_three`.  Everything else — the reduction to `b + d ≤ 5`, a growth lemma, and a finite
`native_decide` check — is machine-checked in this file.

`sep_two_three` is the exponent-`β = 1/3` form `3 ^ (3k) ≤ (2^m − 3^k)^3 · 2^k` for the
near-critical `m` (`3^k < 2^m < 2·3^k`), i.e. `|2^m − 3^k| ≥ 3^k · 2^(−k/3)`.  It is **true**
for every near-critical `k ≥ 6` (verified exactly to `k < 500`, `experiments/two_block_separation.py`;
`β = 1/3` sits in the feasible window `[0.319, 0.387)`).  It is far weaker than full Baker and is
the target to discharge via mathlib's continued-fraction convergent bounds for `log₂ 3`
(`Mathlib/Algebra/ContinuedFractions/`).  It is left as the single disclosed obligation.
-/

namespace CollatzMoonshot.FrontA

/-- **Disclosed effective input (weak power separation, `β = 1/3`).**  For the near-critical power
`2 ^ m` just above `3 ^ k` (i.e. `3 ^ k < 2 ^ m < 2 · 3 ^ k`) with `k ≥ 6`,
`3 ^ (3k) ≤ (2^m − 3^k)^3 · 2^k`, equivalently `2^m − 3^k ≥ 3^k · 2^(−k/3)`.

TRUE for all near-critical `k ≥ 6` (checked exactly to `k < 500`).  This is the *only* deep
(effective-irrationality-of-`log₂3`) obligation behind the two-block exclusion; to be discharged
from the continued fraction of `log₂ 3`.  Everything downstream is machine-checked. -/
theorem sep_two_three (k m : ℕ) (hk : 6 ≤ k) (h1 : 3 ^ k < 2 ^ m) (h2 : 2 ^ m < 2 * 3 ^ k) :
    3 ^ (3 * k) ≤ (2 ^ m - 3 ^ k) ^ 3 * 2 ^ k := by
  sorry

/-- **Irrationality of `log₂ 3`** (mathlib lacks it).  The unavoidable first prerequisite of any
continued-fraction / effective-measure attack on `linear_form_lower_log23`: a rational value
`log₂ 3 = a/b` would force `2^a = 3^b` with `a, b ≥ 1`, contradicting `2 ∤ 3^b`. -/
theorem irrational_logb_two_three : Irrational (Real.logb 2 3) := by
  rintro ⟨q, hq⟩
  -- `2 ^ (q:ℝ) = 3`
  have h23 : (2 : ℝ) ^ (q : ℝ) = 3 := by
    rw [hq]; exact Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)
  set n := q.num with hn
  set d := q.den with hd
  have hdpos : 0 < d := q.pos
  -- raise to the `d`-th power: `2^(n:ℝ) = 3^(d:ℝ)`
  have hqd : (q : ℝ) * (d : ℝ) = (n : ℝ) := by
    have : (q : ℝ) = (n : ℝ) / (d : ℝ) := by
      rw [hn, hd]; exact_mod_cast (Rat.num_div_den q).symm
    rw [this]; field_simp
  have hpow : (2 : ℝ) ^ (n : ℝ) = (3 : ℝ) ^ (d : ℝ) := by
    have e : ((2 : ℝ) ^ (q : ℝ)) ^ (d : ℝ) = (3 : ℝ) ^ (d : ℝ) := by rw [h23]
    rwa [← Real.rpow_mul (by norm_num), hqd] at e
  -- `n > 0`
  have h3d : (1 : ℝ) < (3 : ℝ) ^ (d : ℝ) := by
    apply Real.one_lt_rpow_iff_of_pos (by norm_num) |>.mpr
    exact Or.inl ⟨by norm_num, by exact_mod_cast hdpos⟩
  have hnpos : 0 < n := by
    by_contra hnn
    push_neg at hnn
    have : (2 : ℝ) ^ (n : ℝ) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      exact_mod_cast hnn
    linarith [hpow ▸ this]
  -- descend to ℕ: `2 ^ n.toNat = 3 ^ d`
  lift n to ℕ using hnpos.le with N hN
  have hNpos : 0 < N := by exact_mod_cast hnpos
  have hnat : (2 : ℕ) ^ N = 3 ^ d := by
    have : ((2 ^ N : ℕ) : ℝ) = ((3 ^ d : ℕ) : ℝ) := by
      push_cast
      rw [← Real.rpow_natCast (2:ℝ) N, ← Real.rpow_natCast (3:ℝ) d]
      exact_mod_cast hpow
    exact_mod_cast this
  -- contradiction: `2 ∣ 2^N = 3^d`, but `2 ∤ 3^d`
  have hdvd : (2 : ℕ) ∣ 3 ^ d := hnat ▸ dvd_pow_self 2 hNpos.ne'
  have : (2 : ℕ) ∣ 3 := (Nat.prime_two).dvd_of_dvd_pow hdvd
  norm_num at this

/-- **Integer ⇄ real bridge for `θ = log₂ 3` (workhorse of the continued-fraction route).**
A rational lower bound `a/b < log₂ 3` is *equivalent* to the decidable integer fact `2^a < 3^b`.
This lets every continued-fraction convergent / semiconvergent inequality for `log₂ 3` be
discharged by `decide`/`norm_num` on naturals, with no real-analysis in the loop. -/
theorem lt_logb_two_three_iff (a b : ℕ) (hb : 0 < b) :
    (a : ℝ) / b < Real.logb 2 3 ↔ 2 ^ a < 3 ^ b := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb
  rw [Real.logb, div_lt_div_iff₀ hbpos hlog2, mul_comm (Real.log 3) (b : ℝ),
      ← Real.log_pow, ← Real.log_pow, Real.log_lt_log_iff (by positivity) (by positivity)]
  exact_mod_cast Iff.rfl

/-- Companion: `log₂ 3 < a/b ↔ 3^b < 2^a`. -/
theorem logb_two_three_lt_iff (a b : ℕ) (hb : 0 < b) :
    Real.logb 2 3 < (a : ℝ) / b ↔ 3 ^ b < 2 ^ a := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb
  rw [Real.logb, div_lt_div_iff₀ hlog2 hbpos, mul_comm (Real.log 3) (b : ℝ),
      ← Real.log_pow, ← Real.log_pow, Real.log_lt_log_iff (by positivity) (by positivity)]
  exact_mod_cast Iff.rfl

/-- **Unimodular best-approximation core (pure integers).**  If `a/b < p/k < c/d` and the pair
`a/b, c/d` is unimodular (`b·c = a·d + 1`), then `k ≥ b + d`.  This is the denominator gap behind
the classical best-approximation lower bound `‖kθ‖ ≥ ‖q_n θ‖`, formalized with no continued-fraction
theory (absent from mathlib) via the identity `k = (b·p − a·k)·d + (c·k − p·d)·b`.  Combined with the
integer bridge `lt_logb_two_three_iff`, it will drive an effective lower bound on `‖k·log₂3‖`. -/
theorem denom_ge_of_between (a b c d p k : ℕ) (hb : 0 < b) (hd : 0 < d)
    (huni : b * c = a * d + 1) (h1 : a * k < b * p) (h2 : p * d < c * k) : b + d ≤ k := by
  have huniZ : (b : ℤ) * c = a * d + 1 := by exact_mod_cast huni
  have key : (k : ℤ) = ((b : ℤ) * p - a * k) * d + ((c : ℤ) * k - p * d) * b := by
    linear_combination (-(k : ℤ)) * huniZ
  have hbp : (1 : ℤ) ≤ (b : ℤ) * p - a * k := by
    have h : (a : ℤ) * k < b * p := by exact_mod_cast h1
    omega
  have hck : (1 : ℤ) ≤ (c : ℤ) * k - p * d := by
    have h : (p : ℤ) * d < c * k := by exact_mod_cast h2
    omega
  have hbZ : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have hdZ : (1 : ℤ) ≤ d := by exact_mod_cast hd
  have : (b : ℤ) + d ≤ k := by rw [key]; nlinarith [hbp, hck, hbZ, hdZ]
  exact_mod_cast this

/-- **Best-approximation lower bound for a unimodular bracket.**  If `a/b < θ < c/d` is unimodular
(`b·c = a·d + 1`), then every fraction `p/k` with denominator `1 ≤ k < b + d` stays at least the
bracket-endpoint gap `min(θ − a/b, c/d − θ)` away from `θ`.  (No `p/k` can slip strictly inside the
bracket, by `denom_ge_of_between`.)  This is the classical `‖kθ‖ ≥ ‖qₙθ‖` engine; iterating it over
the convergent brackets of `log₂3` will yield the effective measure. -/
theorem theta_dist_lower (a b c d : ℕ) (θ : ℝ) (hb : 0 < b) (hd : 0 < d)
    (huni : b * c = a * d + 1) (hlo : (a : ℝ) / b < θ) (hhi : θ < (c : ℝ) / d)
    (k p : ℕ) (hk : 0 < k) (hklt : k < b + d) :
    min (θ - (a : ℝ) / b) ((c : ℝ) / d - θ) ≤ |θ - (p : ℝ) / k| := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  rcases lt_or_ge ((a : ℝ) / b) ((p : ℝ) / k) with hx | hx
  · rcases lt_or_ge ((p : ℝ) / k) ((c : ℝ) / d) with hx2 | hx2
    · exfalso
      have h1 : a * k < b * p := by
        have hr := (div_lt_div_iff₀ hbR hkR).mp hx
        have : (a : ℝ) * k < b * p := by rw [mul_comm (b : ℝ) p]; exact hr
        exact_mod_cast this
      have h2 : p * d < c * k := by
        have hr := (div_lt_div_iff₀ hkR hdR).mp hx2
        exact_mod_cast hr
      have := denom_ge_of_between a b c d p k hb hd huni h1 h2
      omega
    · have habs : |θ - (p : ℝ) / k| = (p : ℝ) / k - θ := by
        rw [abs_sub_comm, abs_of_pos (by linarith)]
      rw [habs]; exact le_trans (min_le_right _ _) (by linarith)
  · have habs : |θ - (p : ℝ) / k| = θ - (p : ℝ) / k := by
        rw [abs_of_pos (by linarith)]
    rw [habs]; exact le_trans (min_le_left _ _) (by linarith)

/-- **Analytic bridge to the textbook Baker linear form (no new axioms).**  The weak separation
`sep_two_three` reduces to the *standard* linear-forms-in-logarithms lower bound
`Λ = m·log 2 − k·log 3 ≥ 2^(−k/3)` on the near-critical window, via nothing but the elementary
convexity inequality `e^Λ − 1 ≥ Λ` and `2^k = e^{k log 2}`.

This pins the sole deep obligation behind the two-block exclusion to exactly the classical
effective-irrationality object `Λ = |m·log 2 − k·log 3|` (linear forms in logs / Baker), and
machine-checks — sorry-free, axiom-free beyond the trust base — that *everything* between that
bound and `sep_two_three` is elementary.  The residual disclosed target is therefore:

> `linear_form_lower_log23`:  for near-critical `k ≥ 6`,
> `Real.exp (−(k/3)·log 2) ≤ (m:ℝ)·log 2 − (k:ℝ)·log 3`,

i.e. `|m·log 2 − k·log 3| ≥ 2^(−k/3)`, the β = 1/3 effective bound. -/
theorem sep_of_linear_form (k m : ℕ) (h1 : 3 ^ k < 2 ^ m)
    (hΛ : Real.exp (-(k : ℝ) / 3 * Real.log 2)
            ≤ (m : ℝ) * Real.log 2 - (k : ℝ) * Real.log 3) :
    3 ^ (3 * k) ≤ (2 ^ m - 3 ^ k) ^ 3 * 2 ^ k := by
  set Λ : ℝ := (m : ℝ) * Real.log 2 - (k : ℝ) * Real.log 3 with hΛdef
  -- powers as exponentials
  have e2 : (2 : ℝ) ^ m = Real.exp ((m : ℝ) * Real.log 2) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  have e3 : (3 : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log 3) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  have e2k : (2 : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log 2) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  -- factor the real deficit
  have hprod : (3 : ℝ) ^ k * Real.exp Λ = (2 : ℝ) ^ m := by
    rw [e3, ← Real.exp_add, e2]; congr 1; rw [hΛdef]; ring
  have hDfac : (3 : ℝ) ^ k * (Real.exp Λ - 1) = (2 : ℝ) ^ m - (3 : ℝ) ^ k := by
    rw [mul_sub, mul_one, hprod]
  -- lower bound the deficit by 3^k · Λ, then by 3^k · exp(−k/3 log2)
  have hL : (3 : ℝ) ^ k * Real.exp (-(k : ℝ) / 3 * Real.log 2) ≤ (2 : ℝ) ^ m - (3 : ℝ) ^ k := by
    rw [← hDfac]
    refine le_trans (mul_le_mul_of_nonneg_left hΛ (by positivity)) ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have := Real.add_one_le_exp Λ; linarith
  have hLnn : (0 : ℝ) ≤ (3 : ℝ) ^ k * Real.exp (-(k : ℝ) / 3 * Real.log 2) := by positivity
  -- cube and multiply by 2^k: the LHS collapses to 3^(3k)
  have hcollapse :
      ((3 : ℝ) ^ k * Real.exp (-(k : ℝ) / 3 * Real.log 2)) ^ 3 * (2 : ℝ) ^ k = (3 : ℝ) ^ (3 * k) := by
    have h3 : ((3 : ℝ) ^ k) ^ 3 = (3 : ℝ) ^ (3 * k) := by rw [← pow_mul, Nat.mul_comm]
    rw [mul_pow, h3, ← Real.exp_nat_mul, e2k, mul_assoc, ← Real.exp_add]
    rw [show (↑(3 : ℕ) : ℝ) * (-(k : ℝ) / 3 * Real.log 2) + (k : ℝ) * Real.log 2 = 0 by
          push_cast; ring]
    simp
  -- combine
  have hcube : ((3 : ℝ) ^ k * Real.exp (-(k : ℝ) / 3 * Real.log 2)) ^ 3
      ≤ ((2 : ℝ) ^ m - (3 : ℝ) ^ k) ^ 3 := by
    exact pow_le_pow_left₀ hLnn hL 3
  have hreal : (3 : ℝ) ^ (3 * k) ≤ ((2 : ℝ) ^ m - (3 : ℝ) ^ k) ^ 3 * (2 : ℝ) ^ k := by
    calc (3 : ℝ) ^ (3 * k)
        = ((3 : ℝ) ^ k * Real.exp (-(k : ℝ) / 3 * Real.log 2)) ^ 3 * (2 : ℝ) ^ k := hcollapse.symm
      _ ≤ ((2 : ℝ) ^ m - (3 : ℝ) ^ k) ^ 3 * (2 : ℝ) ^ k := by
          apply mul_le_mul_of_nonneg_right hcube (by positivity)
  -- descend to ℕ
  have hcast : (((2 ^ m - 3 ^ k) ^ 3 * 2 ^ k : ℕ) : ℝ)
      = ((2 : ℝ) ^ m - (3 : ℝ) ^ k) ^ 3 * (2 : ℝ) ^ k := by
    push_cast [Nat.cast_sub (le_of_lt h1)]; ring
  have : ((3 ^ (3 * k) : ℕ) : ℝ) ≤ (((2 ^ m - 3 ^ k) ^ 3 * 2 ^ k : ℕ) : ℝ) := by
    rw [hcast]; push_cast; exact hreal
  exact_mod_cast this

/-- **Pure-ℕ narrowing to the integer irrationality measure (no reals, fully general in `C`).**
`sep_two_three` follows from *any* polynomial integer lower bound on the deficit
`D = 2^m − 3^k`, namely `3^k ≤ D · k^C` (the standard effective-irrationality-measure form,
`|log₂3 − m/k| ≥ c/k^{C+1}`), together with the elementary growth fact `k^(3C) ≤ 2^k`.

Proof is a one-line cube: `3^(3k) = (3^k)^3 ≤ (D·k^C)^3 = D^3·k^(3C) ≤ D^3·2^k`.  This isolates
the sole deep obligation as the classical Diophantine statement (finite irrationality measure of
`log₂3`), completely elementarily, with no real-analysis bridge and no committed constant `C`. -/
theorem sep_of_measure (k m C : ℕ) (hmeas : 3 ^ k ≤ (2 ^ m - 3 ^ k) * k ^ C)
    (hgrow : k ^ (3 * C) ≤ 2 ^ k) :
    3 ^ (3 * k) ≤ (2 ^ m - 3 ^ k) ^ 3 * 2 ^ k := by
  set D := 2 ^ m - 3 ^ k with hD
  calc 3 ^ (3 * k) = (3 ^ k) ^ 3 := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ (D * k ^ C) ^ 3 := Nat.pow_le_pow_left hmeas 3
    _ = D ^ 3 * k ^ (3 * C) := by rw [mul_pow, ← pow_mul, Nat.mul_comm C 3]
    _ ≤ D ^ 3 * 2 ^ k := by gcongr

/-- **Scaled best-approximation bound (linear-form form).**  Multiplying `theta_dist_lower` by `k`:
the linear form `|k·θ − p|` is at least `k·min(θ−a/b, c/d−θ)` for every `p`, when `1 ≤ k < b + d`.
This is the `‖k·θ‖`-shaped quantity the crux pipeline consumes (`m − k·θ = |k·θ − m|` near-critical). -/
theorem linForm_dist_lower (a b c d : ℕ) (θ : ℝ) (hb : 0 < b) (hd : 0 < d)
    (huni : b * c = a * d + 1) (hlo : (a : ℝ) / b < θ) (hhi : θ < (c : ℝ) / d)
    (k p : ℕ) (hk : 0 < k) (hklt : k < b + d) :
    (k : ℝ) * min (θ - (a : ℝ) / b) ((c : ℝ) / d - θ) ≤ |(k : ℝ) * θ - p| := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hbase := theta_dist_lower a b c d θ hb hd huni hlo hhi k p hk hklt
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkR
  have heq : (k : ℝ) * θ - p = k * (θ - (p : ℝ) / k) := by field_simp
  have hrw : |(k : ℝ) * θ - p| = (k : ℝ) * |θ - (p : ℝ) / k| := by
    rw [heq, abs_mul, abs_of_pos hkR]
  rw [hrw]
  exact mul_le_mul_of_nonneg_left hbase (le_of_lt hkR)

/-- **Connector: the linear form `Λ` in terms of `θ = log₂3`.**  `Λ = m·log2 − k·log3` equals
`log2·(m − k·log₂3)`, i.e. `log2` times the signed distance `m − k·θ`.  This ties the output of the
best-approximation engine `theta_dist_lower` (distances from `m/k` to `θ`) directly to the input of
`sep_of_linear_form` (the linear form). -/
theorem linear_form_eq_logb (k m : ℕ) :
    (m : ℝ) * Real.log 2 - k * Real.log 3
      = Real.log 2 * ((m : ℝ) - k * Real.logb 2 3) := by
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  rw [Real.logb]; field_simp

/-- **Pipeline endpoint (no new axioms).**  `sep_two_three` follows from a lower bound on the signed
distance `m − k·log₂3` alone: if `log2·(m − k·θ) ≥ 2^(−k/3)` then `3^(3k) ≤ (2^m−3^k)^3·2^k`.  This is
exactly `sep_of_linear_form` re-expressed through `θ = log₂3`, so the remaining obligation is now a
pure statement about how close `m/k` can be to `log₂3` — the object `theta_dist_lower` bounds. -/
theorem sep_of_logb_gap (k m : ℕ) (h1 : 3 ^ k < 2 ^ m)
    (hgap : Real.exp (-(k : ℝ) / 3 * Real.log 2)
              ≤ Real.log 2 * ((m : ℝ) - k * Real.logb 2 3)) :
    3 ^ (3 * k) ≤ (2 ^ m - 3 ^ k) ^ 3 * 2 ^ k := by
  apply sep_of_linear_form k m h1
  rw [linear_form_eq_logb]; exact hgap

/-- Elementary growth lemma: for `k ≥ 15`, `3 ^ (k + 2) ≤ 2 ^ (2k − 3)`. -/
theorem grow_two_three (k : ℕ) (hk : 15 ≤ k) : 3 ^ (k + 2) ≤ 2 ^ (2 * k - 3) := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have e2 : 2 * (n + 1) - 3 = (2 * n - 3) + 2 := by omega
      calc 3 ^ (n + 1 + 2) = 3 ^ (n + 2) * 3 := by
              rw [show n + 1 + 2 = (n + 2) + 1 by ring, pow_succ]
        _ ≤ 2 ^ (2 * n - 3) * 3 := by gcongr
        _ ≤ 2 ^ (2 * n - 3) * 2 ^ 2 := by gcongr <;> norm_num
        _ = 2 ^ (2 * (n + 1) - 3) := by rw [e2, pow_add]

/-- Finite check (`native_decide`): for `6 ≤ k ≤ 14`, no near-critical configuration survives the
two block-window inequalities `(W)`, `(A)`. -/
theorem finite_two_block_check :
    ∀ k ∈ Finset.range 15, ∀ m ∈ Finset.range 24, ∀ d ∈ Finset.range 15,
      ¬ (6 ≤ k ∧ 1 ≤ d ∧ d < k ∧ 3 ^ k < 2 ^ m ∧ 2 ^ m < 2 * 3 ^ k ∧
         2 ^ d * (2 ^ m - 3 ^ k) < 2 ^ m ∧ (2 ^ m - 3 ^ k) * 2 ^ k ≤ 2 ^ m * 3 ^ d) := by
  native_decide

/-- **The reduction (machine-checked modulo `sep_two_three`).**  Given the near-critical window
`3^k < 2^m < 2·3^k` and the two block inequalities
  `(W) : 2^d·(2^m − 3^k) < 2^m`  and  `(A) : (2^m − 3^k)·2^k ≤ 2^m·3^d`,
with `1 ≤ d < k`, the separation forces `k ≤ 5`.  (β=1/3 gives the elementary bound `k ≤ 14` via
`grow_two_three`; the residue `6 ≤ k ≤ 14` is cleared by `finite_two_block_check`.) -/
theorem bd_reduction (k m d : ℕ) (hk1 : 1 ≤ d) (hdk : d < k)
    (h1 : 3 ^ k < 2 ^ m) (h2 : 2 ^ m < 2 * 3 ^ k)
    (hW : 2 ^ d * (2 ^ m - 3 ^ k) < 2 ^ m)
    (hA : (2 ^ m - 3 ^ k) * 2 ^ k ≤ 2 ^ m * 3 ^ d) :
    k ≤ 5 := by
  by_contra hcon
  have hk6 : 6 ≤ k := by omega
  set D := 2 ^ m - 3 ^ k with hD
  have hDpos : 0 < D := by rw [hD]; omega
  have hS : 3 ^ (3 * k) ≤ D ^ 3 * 2 ^ k := sep_two_three k m hk6 h1 h2
  have hD3 : 0 < D ^ 3 := by positivity
  -- (ii'): 3d < k+3
  have hii : 3 * d < k + 3 := by
    have hWc : (2 ^ d * D) ^ 3 < (2 * 3 ^ k) ^ 3 := by
      apply Nat.pow_lt_pow_left _ (by norm_num)
      calc 2 ^ d * D < 2 ^ m := hW
        _ < 2 * 3 ^ k := h2
    have key : D ^ 3 * (2 ^ d) ^ 3 < D ^ 3 * 2 ^ (k + 3) := by
      calc D ^ 3 * (2 ^ d) ^ 3 = (2 ^ d * D) ^ 3 := by ring
        _ < (2 * 3 ^ k) ^ 3 := hWc
        _ = 8 * 3 ^ (3 * k) := by rw [mul_pow, ← pow_mul, Nat.mul_comm k 3]; norm_num
        _ ≤ 8 * (D ^ 3 * 2 ^ k) := by gcongr
        _ = D ^ 3 * 2 ^ (k + 3) := by rw [pow_add]; ring
    have hpow : (2 ^ d) ^ 3 < 2 ^ (k + 3) := Nat.lt_of_mul_lt_mul_left key
    rw [← pow_mul] at hpow
    have := (Nat.pow_lt_pow_iff_right (a := 2) (by norm_num)).mp hpow
    omega
  -- (iii'): 2^(2k-3) < 3^(3d)
  have hiii : 2 ^ (2 * k - 3) < 3 ^ (3 * d) := by
    have hAstrict : D * 2 ^ k < 2 * 3 ^ (k + d) := by
      calc D * 2 ^ k ≤ 2 ^ m * 3 ^ d := hA
        _ < 2 * 3 ^ k * 3 ^ d := by gcongr
        _ = 2 * 3 ^ (k + d) := by rw [pow_add]; ring
    have hAc : (D * 2 ^ k) ^ 3 < (2 * 3 ^ (k + d)) ^ 3 :=
      Nat.pow_lt_pow_left hAstrict (by norm_num)
    have hlow : 3 ^ (3 * k) * 2 ^ (2 * k) ≤ (D * 2 ^ k) ^ 3 := by
      calc 3 ^ (3 * k) * 2 ^ (2 * k) ≤ (D ^ 3 * 2 ^ k) * 2 ^ (2 * k) := by gcongr
        _ = D ^ 3 * 2 ^ (3 * k) := by
              rw [mul_assoc, ← pow_add, show k + 2 * k = 3 * k by ring]
        _ = (D * 2 ^ k) ^ 3 := by rw [mul_pow, ← pow_mul, Nat.mul_comm k 3]
    have hchain : 3 ^ (3 * k) * 2 ^ (2 * k) < (2 * 3 ^ (k + d)) ^ 3 := lt_of_le_of_lt hlow hAc
    have hRHS : (2 * 3 ^ (k + d)) ^ 3 = 3 ^ (3 * k) * (8 * 3 ^ (3 * d)) := by
      rw [mul_pow, ← pow_mul, show (k + d) * 3 = 3 * k + 3 * d by ring, pow_add]; ring
    rw [hRHS] at hchain
    have hcancel : 2 ^ (2 * k) < 8 * 3 ^ (3 * d) := Nat.lt_of_mul_lt_mul_left hchain
    have hsplit : 2 ^ (2 * k) = 2 ^ (2 * k - 3) * 8 := by
      rw [show (8:ℕ) = 2 ^ 3 by norm_num, ← pow_add]; congr 1; omega
    rw [hsplit] at hcancel
    have hmul : 2 ^ (2 * k - 3) * 8 < 3 ^ (3 * d) * 8 := by omega
    exact Nat.lt_of_mul_lt_mul_right hmul
  -- combine (ii') + (iii'): 2^(2k-3) < 3^(k+2)
  have hd3 : 3 * d ≤ k + 2 := by omega
  have h3dle : 3 ^ (3 * d) ≤ 3 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) hd3
  have hiv : 2 ^ (2 * k - 3) < 3 ^ (k + 2) := lt_of_lt_of_le hiii h3dle
  by_cases hk15 : 15 ≤ k
  · exact absurd (grow_two_three k hk15) (by omega)
  · have hkle : k ≤ 14 := by omega
    have hmlt : m < 24 := by
      have hlt : 2 ^ m < 2 ^ 24 := by
        calc 2 ^ m < 2 * 3 ^ k := h2
          _ ≤ 2 * 3 ^ 14 := by gcongr <;> norm_num
          _ < 2 ^ 24 := by norm_num
      exact (Nat.pow_lt_pow_iff_right (a := 2) (by norm_num)).mp hlt
    exact finite_two_block_check k (Finset.mem_range.mpr (by omega)) m
      (Finset.mem_range.mpr hmlt) d (Finset.mem_range.mpr (by omega))
      ⟨hk6, hk1, hdk, h1, h2, hW, hA⟩

end CollatzMoonshot.FrontA
