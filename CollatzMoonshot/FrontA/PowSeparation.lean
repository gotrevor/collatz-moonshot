/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CollatzMoonshot.Assumed.Rhin1987

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

/-- **Sharp best-approximation lower bound.**  For a unimodular bracket `a/b < θ < c/d`
(`b·c = a·d + 1`) and `1 ≤ k < b + d`, every `p` satisfies `|kθ − p| ≥ min(bθ − a, c − dθ)`.
This is a factor `b` (resp. `d`) sharper than `theta_dist_lower`'s `min(θ−a/b, c/d−θ)`, and is the
tight `‖q_nθ‖`-quality bound (at `k = b`, `p = a` it is exactly `bθ − a = ‖bθ‖`).  Key identity
(pure `ring` given unimodularity): `kθ − p = (kc − pd)(bθ − a) + (ka − pb)(c − dθ)`. -/
theorem theta_dist_lower_sharp (a b c d : ℕ) (θ : ℝ) (hb : 0 < b) (hd : 0 < d)
    (huni : b * c = a * d + 1) (hlo : (a : ℝ) / b < θ) (hhi : θ < (c : ℝ) / d)
    (k p : ℕ) (hk : 0 < k) (hklt : k < b + d) :
    min ((b : ℝ) * θ - a) ((c : ℝ) - d * θ) ≤ |(k : ℝ) * θ - p| := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hbθa : 0 < (b : ℝ) * θ - a := by rw [div_lt_iff₀ hbR] at hlo; linarith
  have hcdθ : 0 < (c : ℝ) - d * θ := by rw [lt_div_iff₀ hdR] at hhi; linarith
  have huniR : (b : ℝ) * c - a * d = 1 := by
    have : (b * c : ℝ) = (a * d : ℝ) + 1 := by exact_mod_cast huni
    push_cast at this ⊢; linarith
  have hid : (k : ℝ) * θ - p
      = ((k : ℝ) * c - p * d) * ((b : ℝ) * θ - a) + ((k : ℝ) * a - p * b) * ((c : ℝ) - d * θ) := by
    have hpure : ((k : ℝ) * c - p * d) * ((b : ℝ) * θ - a)
          + ((k : ℝ) * a - p * b) * ((c : ℝ) - d * θ)
        = ((b : ℝ) * c - a * d) * ((k : ℝ) * θ - p) := by ring
    rw [hpure, huniR, one_mul]
  rcases lt_or_ge ((a : ℝ) / b) ((p : ℝ) / k) with hx | hx
  · rcases lt_or_ge ((p : ℝ) / k) ((c : ℝ) / d) with hx2 | hx2
    · -- strictly between → contradiction via denom_ge_of_between
      exfalso
      have h1 : a * k < b * p := by
        have hr := (div_lt_div_iff₀ hbR hkR).mp hx
        have : (a : ℝ) * k < b * p := by rw [mul_comm (b : ℝ) p]; exact hr
        exact_mod_cast this
      have h2 : p * d < c * k := by exact_mod_cast (div_lt_div_iff₀ hkR hdR).mp hx2
      have := denom_ge_of_between a b c d p k hb hd huni h1 h2
      omega
    · -- p/k ≥ c/d: |kθ−p| = p − kθ ≥ c − dθ.  Here u = ka−pb ≤ 0, v = kc−pd ≤ 0.
      have hck : (c : ℝ) * k ≤ p * d := (div_le_div_iff₀ hdR hkR).mp hx2
      have hv : (k : ℝ) * c - p * d ≤ 0 := by nlinarith [hck]
      have hu : (k : ℝ) * a - p * b ≤ -1 := by
        have hac : (a : ℝ) / b < (c : ℝ) / d := lt_trans hlo hhi
        have hlt : (a : ℝ) / b < (p : ℝ) / k := lt_of_lt_of_le hac hx2
        have hr := (div_lt_div_iff₀ hbR hkR).mp hlt
        have hnat : a * k < p * b := by exact_mod_cast hr
        have : (a : ℝ) * k + 1 ≤ p * b := by exact_mod_cast hnat
        nlinarith [this]
      have hlow : (c : ℝ) - d * θ ≤ (p : ℝ) - k * θ := by
        nlinarith [hbθa, hcdθ, hv, hu, hid]
      rw [abs_of_nonpos (by nlinarith [hlow, hcdθ])]
      calc min ((b : ℝ) * θ - a) ((c : ℝ) - d * θ) ≤ (c : ℝ) - d * θ := min_le_right _ _
        _ ≤ (p : ℝ) - k * θ := hlow
        _ = -((k : ℝ) * θ - p) := by ring
  · -- p/k ≤ a/b: |kθ−p| = kθ − p ≥ bθ − a.  Here u = ka−pb ≥ 0, v = kc−pd ≥ 1.
    have hu : 0 ≤ (k : ℝ) * a - p * b := by
      have hpb : (p : ℝ) * b ≤ a * k := (div_le_div_iff₀ hkR hbR).mp hx
      nlinarith [hpb]
    have hv : (1 : ℝ) ≤ (k : ℝ) * c - p * d := by
      have hac : (a : ℝ) / b < (c : ℝ) / d := lt_trans hlo hhi
      have hlt : (p : ℝ) / k < (c : ℝ) / d := lt_of_le_of_lt hx hac
      have hr := (div_lt_div_iff₀ hkR hdR).mp hlt
      have hnat : p * d < c * k := by exact_mod_cast hr
      have : p * d + 1 ≤ c * k := hnat
      have : (p : ℝ) * d + 1 ≤ c * k := by exact_mod_cast this
      nlinarith [this]
    have hlow : (b : ℝ) * θ - a ≤ (k : ℝ) * θ - p := by rw [hid]; nlinarith [hbθa, hcdθ, hu, hv]
    rw [abs_of_nonneg (by nlinarith [hlow, hbθa])]
    exact le_trans (min_le_left _ _) hlow

/-- **Determinant preservation for the convergent recurrence (pure ℤ).**  Consecutive convergents
`p₋/q₋, p/q` with determinant `p·q₋ − p₋·q = e` produce the next convergent
`p₊ = a·p + p₋, q₊ = a·q + q₋` with determinant `p₊·q − p·q₊ = p₋·q − p·q₋` (the sign of the
`p·q₋ − p₋·q` determinant flips each step, so `|det|` is preserved).  This is the algebraic engine
that propagates unimodularity (`|det| = 1`) along the continued-fraction chain of `log₂3`, so every
convergent bracket fed to `theta_dist_lower` stays unimodular. -/
theorem convergent_det_step (p' q' p q a : ℤ) :
    (a * p + p') * q - p * (a * q + q') = p' * q - p * q' := by ring

/-- The convergent denominators grow: `q₊ = a·q + q₋ ≥ q + q₋` for `a ≥ 1`, so the straddling
range `[q, q₊)` of `theta_dist_lower` strictly advances each step. -/
theorem convergent_denom_grow (q' q a : ℕ) (ha : 1 ≤ a) : q + q' ≤ a * q + q' := by
  have : q ≤ a * q := by nlinarith [ha]
  omega

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

/-- **Elementary growth: every fixed polynomial is eventually dominated by `2^k` (pure ℕ).**
For each exponent `C` there is a threshold `K` with `k ^ C ≤ 2 ^ k` for all `k ≥ K`.  This is the
missing connective that turns a *uniform* irrationality-measure input (`3^k ≤ (2^m−3^k)·k^C`) into
the cube-and-clear step of `sep_of_measure` (which needs `k^(3C) ≤ 2^k`).  Proved from mathlib's
`n^C / 2^n → 0`. -/
theorem poly_le_two_pow (C : ℕ) : ∃ K : ℕ, ∀ k : ℕ, K ≤ k → k ^ C ≤ 2 ^ k := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt C (r := 2) (by norm_num)
  have hev : ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ C / 2 ^ n < 1 :=
    h.eventually (Iio_mem_nhds (by norm_num))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨K, hK⟩ := hev
  refine ⟨K, fun k hk => ?_⟩
  have hlt := hK k hk
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  rw [div_lt_one h2] at hlt
  have hcast : ((k ^ C : ℕ) : ℝ) < ((2 ^ k : ℕ) : ℝ) := by push_cast; exact hlt
  exact le_of_lt (by exact_mod_cast hcast)

/-- **Uniform-measure reduction: the whole crux `sep_two_three` from ONE Gelfond-style bound.**
The classical effective lower bound on the distance between powers of 2 and 3 (Gelfond 1935; Baker;
explicit in Bennett–Bugeaud, *Acta Arith.* 155 (2012) and Bugeaud's monograph §3.1) provides, for
`log₂3`, a *polynomial* irrationality measure — far stronger than the exponential `2^(−k/3)` this
crux needs.  In the near-critical window it takes the pure-ℕ form `3^k ≤ (2^m−3^k)·k^C` for a fixed
`C` and all large `k`.

This theorem machine-checks (sorry-free, trust base only) that such a uniform measure `hmeas`
(for `k ≥ K`), together with the elementary crossover `hK` (dischargeable by `poly_le_two_pow`) and a
finite check `hfin` on the residual `6 ≤ k < K`, yields `sep_two_three` for **every** near-critical
`k ≥ 6`.  So *everything* between the standard Gelfond object and the crux is elementary: the sole
open input is the uniform measure `hmeas` (the Gelfond bound) — a well-defined, classical,
🟡 project-scale target (explicit hypergeometric/interpolation constructions; no mathlib support yet),
NOT a generational wall. -/
theorem sep_of_uniform_measure (C K : ℕ)
    (hK : ∀ k : ℕ, K ≤ k → k ^ (3 * C) ≤ 2 ^ k)
    (hmeas : ∀ k m : ℕ, K ≤ k → 3 ^ k < 2 ^ m → 2 ^ m < 2 * 3 ^ k →
        3 ^ k ≤ (2 ^ m - 3 ^ k) * k ^ C)
    (hfin : ∀ k m : ℕ, 6 ≤ k → k < K → 3 ^ k < 2 ^ m → 2 ^ m < 2 * 3 ^ k →
        3 ^ (3 * k) ≤ (2 ^ m - 3 ^ k) ^ 3 * 2 ^ k)
    (k m : ℕ) (hk : 6 ≤ k) (h1 : 3 ^ k < 2 ^ m) (h2 : 2 ^ m < 2 * 3 ^ k) :
    3 ^ (3 * k) ≤ (2 ^ m - 3 ^ k) ^ 3 * 2 ^ k := by
  by_cases hkK : K ≤ k
  · exact sep_of_measure k m C (hmeas k m hkK h1 h2) (hK k hkK)
  · exact hfin k m hk (by omega) h1 h2

/-- **Finite check for the residual `6 ≤ k < 130` (`native_decide`).**  For every near-critical
`(k, m)` with `k < 130`, the separation `3^(3k) ≤ (2^m−3^k)^3·2^k` holds outright.  The `m`-range is
bounded (`2^m < 2·3^k ≤ 2·3^129 < 2^208`), so the claim is a finite decidable table. -/
theorem sep_two_three_finite_check :
    ∀ k ∈ Finset.range 130, ∀ m ∈ Finset.range 208,
      ¬ (6 ≤ k ∧ 3 ^ k < 2 ^ m ∧ 2 ^ m < 2 * 3 ^ k) ∨
        3 ^ (3 * k) ≤ (2 ^ m - 3 ^ k) ^ 3 * 2 ^ k := by
  native_decide

/-- **Discharged small-`k` case of `sep_two_three` (sorry-free).**  For near-critical `6 ≤ k < 130`
the separation holds unconditionally.  This is exactly the `hfin` input of `sep_of_uniform_measure`
for threshold `K = 130` (which pairs with any measure exponent `C ≤ 6`, since then the crossover
`k^(3C) ≤ k^18 ≤ 2^k` holds for `k ≥ 130`).  So the ENTIRE residual of `sep_two_three` beyond the
elementary/finite parts is the single uniform Gelfond measure `3^k ≤ (2^m−3^k)·k^C` for `k ≥ 130`. -/
theorem sep_two_three_small (k m : ℕ) (hk : 6 ≤ k) (hklt : k < 130)
    (h1 : 3 ^ k < 2 ^ m) (h2 : 2 ^ m < 2 * 3 ^ k) :
    3 ^ (3 * k) ≤ (2 ^ m - 3 ^ k) ^ 3 * 2 ^ k := by
  have hmlt : m < 208 := by
    have hlt : 2 ^ m < 2 ^ 208 := by
      calc 2 ^ m < 2 * 3 ^ k := h2
        _ ≤ 2 * 3 ^ 129 := by
              have hk129 : k ≤ 129 := by omega
              gcongr
              norm_num
        _ < 2 ^ 208 := by norm_num
    exact (Nat.pow_lt_pow_iff_right (a := 2) (by norm_num)).mp hlt
  rcases sep_two_three_finite_check k (Finset.mem_range.mpr hklt) m (Finset.mem_range.mpr hmlt)
    with h | h
  · exact absurd ⟨hk, h1, h2⟩ h
  · exact h

/-- **Concrete crossover `k^18 ≤ 2^k` for `k ≥ 130` (the `C = 6` threshold).**  `poly_le_two_pow`
only gives a *non-explicit* threshold; this pins it to `130`, exactly matching `sep_two_three_small`'s
finite range.  Induction: base `130^18 ≤ 2^130` (`native_decide`); step uses the tight real ratio
bound `((k+1)/k)^18 ≤ (131/130)^18 ≤ 2` (so `(k+1)^18 ≤ 2·k^18 ≤ 2·2^k = 2^(k+1)`). -/
theorem crossover_130 (k : ℕ) (hk : 130 ≤ k) : k ^ 18 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => native_decide
  | succ n hn ih =>
      have hstep : (n + 1) ^ 18 ≤ 2 * n ^ 18 := by
        have hnR : (130 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
        have h1 : ((n : ℝ) + 1) / n ≤ 131 / 130 := by
          rw [div_le_div_iff₀ hn0 (by norm_num)]; nlinarith [hnR]
        have h0 : (0 : ℝ) ≤ ((n : ℝ) + 1) / n := by positivity
        have h2 : (((n : ℝ) + 1) / n) ^ 18 ≤ (131 / 130 : ℝ) ^ 18 := pow_le_pow_left₀ h0 h1 18
        have h3 : ((131 : ℝ) / 130) ^ 18 ≤ 2 := by norm_num
        have hn18 : (0 : ℝ) < (n : ℝ) ^ 18 := by positivity
        have h4 : ((n : ℝ) + 1) ^ 18 ≤ 2 * (n : ℝ) ^ 18 := by
          have hdiv : ((n : ℝ) + 1) ^ 18 / (n : ℝ) ^ 18 ≤ 2 := by
            rw [← div_pow]; exact le_trans h2 h3
          rw [div_le_iff₀ hn18] at hdiv; linarith [hdiv]
        have hcast : ((n : ℝ) + 1) ^ 18 = (((n + 1) ^ 18 : ℕ) : ℝ) := by push_cast; ring
        have hcast2 : 2 * (n : ℝ) ^ 18 = ((2 * n ^ 18 : ℕ) : ℝ) := by push_cast; ring
        rw [hcast, hcast2] at h4; exact_mod_cast h4
      calc (n + 1) ^ 18 ≤ 2 * n ^ 18 := hstep
        _ ≤ 2 * 2 ^ n := by gcongr
        _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

/-- **End-to-end reduction: the crux `sep_two_three` from ONE concrete uniform Gelfond measure
(fully machine-checked, no existential thresholds).**  Given the single classical input
`hmeas : ∀ near-critical k ≥ 130, 3^k ≤ (2^m − 3^k)·k^6` — the **Gelfond 1935 / Bennett–Bugeaud**
effective measure of `log₂3` at exponent `C = 6` (a *polynomial* bound, far weaker than proven) —
`sep_two_three` holds for **every** near-critical `k ≥ 6`.  Large `k` (`≥ 130`): `sep_of_measure` with
the concrete crossover `crossover_130`.  Small `k`: the finite check `sep_two_three_small`.  So the
entire content of the crux is exactly this one hypothesis; everything else is elementary + finite. -/
theorem sep_two_three_of_gelfond_measure
    (hmeas : ∀ k m : ℕ, 130 ≤ k → 3 ^ k < 2 ^ m → 2 ^ m < 2 * 3 ^ k →
        3 ^ k ≤ (2 ^ m - 3 ^ k) * k ^ 6)
    (k m : ℕ) (hk : 6 ≤ k) (h1 : 3 ^ k < 2 ^ m) (h2 : 2 ^ m < 2 * 3 ^ k) :
    3 ^ (3 * k) ≤ (2 ^ m - 3 ^ k) ^ 3 * 2 ^ k := by
  by_cases hbig : 130 ≤ k
  · refine sep_of_measure k m 6 (hmeas k m hbig h1 h2) ?_
    have := crossover_130 k hbig; norm_num; exact this
  · exact sep_two_three_small k m hk (by omega) h1 h2

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

/-- **Per-`k` interface: `sep` from a single straddling unimodular bracket (no new axioms).**
For near-critical `(k, m)`, given *any* unimodular bracket `a/b < θ < c/d` (`θ = log₂3`) that
straddles `k` (`k < b + d`) and whose scaled gap clears the threshold
`2^(−k/3) ≤ log2 · k · min(θ−a/b, c/d−θ)`, the separation `3^(3k) ≤ (2^m−3^k)^3·2^k` holds.

This packages the whole elementary engine (`linForm_dist_lower` + `sep_of_logb_gap`) into one
statement.  The **sole** remaining obligation is therefore: for every near-critical `k`, produce a
convergent bracket of `log₂3` straddling `k` whose gap clears the threshold — i.e. the effective
separation *at convergent denominators*, which is the irreducible Baker content. -/
theorem sep_of_bracket (k m a b c d : ℕ) (hk : 0 < k)
    (h1 : 3 ^ k < 2 ^ m) (hb : 0 < b) (hd : 0 < d) (huni : b * c = a * d + 1)
    (hlo : (a : ℝ) / b < Real.logb 2 3) (hhi : Real.logb 2 3 < (c : ℝ) / d)
    (hklt : k < b + d)
    (hgap : Real.exp (-(k : ℝ) / 3 * Real.log 2)
              ≤ Real.log 2 * ((k : ℝ) *
                  min (Real.logb 2 3 - (a : ℝ) / b) ((c : ℝ) / d - Real.logb 2 3))) :
    3 ^ (3 * k) ≤ (2 ^ m - 3 ^ k) ^ 3 * 2 ^ k := by
  set θ := Real.logb 2 3 with hθ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- k·θ < m, since 3^k < 2^m
  have hkθ : (k : ℝ) * θ < m := by
    have e1 : (k : ℝ) * θ = Real.logb 2 ((3 : ℝ) ^ k) := by rw [hθ, Real.logb_pow]
    have e2 : (m : ℝ) = Real.logb 2 ((2 : ℝ) ^ m) := by
      rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]; ring
    rw [e1, e2]
    apply Real.logb_lt_logb (by norm_num) (by positivity)
    exact_mod_cast h1
  -- the best-approximation bound, specialised to p = m
  have hdist := linForm_dist_lower a b c d θ hb hd huni hlo hhi k m hk hklt
  have habs : |(k : ℝ) * θ - m| = (m : ℝ) - k * θ := by
    rw [abs_of_neg (by linarith)]; ring
  rw [habs] at hdist
  -- chain: exp(..) ≤ log2·k·ming ≤ log2·(m − kθ)
  apply sep_of_logb_gap k m h1
  refine le_trans hgap ?_
  rw [← hθ]
  exact mul_le_mul_of_nonneg_left hdist (le_of_lt hlog2)

/-- **Sharp per-`k` interface (uses `theta_dist_lower_sharp`).**  Same as `sep_of_bracket` but with
the tight bound, so the gap hypothesis has NO spurious factor of `k`: for near-critical `(k,m)` and a
straddling unimodular bracket `a/b < θ < c/d` (`θ = log₂3`, `k < b+d`) with
`2^(−k/3) ≤ log2 · min(bθ−a, c−dθ)`, the separation holds.  This is the interface the large-`k`
convergent argument feeds: for `k ≈ q_{n+1}`, `min(bθ−a, c−dθ) ≈ 1/q_{n+2}`, so the hypothesis is
`q_{n+2} ≲ 2^{k/3}` — the sub-exponential partial-quotient (Baker) bound. -/
theorem sep_of_bracket_sharp (k m a b c d : ℕ) (hk : 0 < k)
    (h1 : 3 ^ k < 2 ^ m) (hb : 0 < b) (hd : 0 < d) (huni : b * c = a * d + 1)
    (hlo : (a : ℝ) / b < Real.logb 2 3) (hhi : Real.logb 2 3 < (c : ℝ) / d)
    (hklt : k < b + d)
    (hgap : Real.exp (-(k : ℝ) / 3 * Real.log 2)
              ≤ Real.log 2 * min ((b : ℝ) * Real.logb 2 3 - a) ((c : ℝ) - d * Real.logb 2 3)) :
    3 ^ (3 * k) ≤ (2 ^ m - 3 ^ k) ^ 3 * 2 ^ k := by
  set θ := Real.logb 2 3 with hθ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hkθ : (k : ℝ) * θ < m := by
    have e1 : (k : ℝ) * θ = Real.logb 2 ((3 : ℝ) ^ k) := by rw [hθ, Real.logb_pow]
    have e2 : (m : ℝ) = Real.logb 2 ((2 : ℝ) ^ m) := by
      rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]; ring
    rw [e1, e2]; apply Real.logb_lt_logb (by norm_num) (by positivity); exact_mod_cast h1
  have hdist := theta_dist_lower_sharp a b c d θ hb hd huni hlo hhi k m hk hklt
  have habs : |(k : ℝ) * θ - m| = (m : ℝ) - k * θ := by rw [abs_of_neg (by linarith)]; ring
  rw [habs] at hdist
  apply sep_of_logb_gap k m h1
  refine le_trans hgap ?_
  rw [← hθ]
  exact mul_le_mul_of_nonneg_left hdist (le_of_lt hlog2)

/-- Concrete verified convergent bracket of `log₂3`: the consecutive principal convergents
`19/12 < log₂3 < 65/41` (unimodular `12·65 = 19·41 − 1`, i.e. `det = −1`), straddling every
`k < 12 + 41 = 53`.  Both bounds are decided by the integer bridge (`2^19 < 3^12`, `3^41 < 2^65`).
A base data point for the `log₂3` convergent chain (item (i) of the finished-proof structure). -/
theorem logb_bracket_19_12_65_41 :
    (19 : ℝ) / 12 < Real.logb 2 3 ∧ Real.logb 2 3 < (65 : ℝ) / 41 ∧ 12 * 65 = 19 * 41 + 1 := by
  refine ⟨?_, ?_, by norm_num⟩
  · have h := (lt_logb_two_three_iff 19 12 (by norm_num)).mpr (by norm_num)
    push_cast at h; linarith
  · have h := (logb_two_three_lt_iff 65 41 (by norm_num)).mpr (by norm_num)
    push_cast at h; linarith

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

/-- **General-base poly ≤ exp (over ℝ).**  For any base `b > 1` and exponent `C`, `k^C ≤ b^k` for all
large `k`.  The real-valued generalization of `poly_le_two_pow` (used to discharge the crossover of
`sep_of_linear_form_poly`, whose base is `2^(1/3)`). -/
theorem poly_le_pow (b : ℝ) (hb : 1 < b) (C : ℕ) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → (k : ℝ) ^ C ≤ b ^ k := by
  have hb0 : (0 : ℝ) < b := by linarith
  have h := tendsto_pow_const_div_const_pow_of_one_lt C hb
  have hev : ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ C / b ^ n < 1 :=
    h.eventually (Iio_mem_nhds (by norm_num))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨K, hK⟩ := hev
  refine ⟨K, fun k hk => ?_⟩
  have hbpos : (0 : ℝ) < b ^ k := pow_pos hb0 k
  have hlt := hK k hk
  rw [div_lt_one hbpos] at hlt
  exact hlt.le

/-- **Literature-standard interface: `sep_two_three` from Gelfond's linear-forms lower bound.**
The Gelfond 1935 / Baker theorem on the distance between powers of 2 and 3 is stated as a *linear
form in two logarithms*: `|m·log 2 − k·log 3| ≥ c·k^(−κ)` for explicit `c > 0, κ`.  This is the exact
shape a formalized Baker/Gelfond theorem produces (κ free — no pre-digestion to a fixed measure
exponent).  Given that bound (`hLF`, for near-critical `k ≥ 130`) and the elementary crossover
`hcross : k^κ ≤ c·2^(k/3)` (dischargeable by `poly_le_pow` at base `2^(1/3)`), `sep_two_three` holds
for every near-critical `k ≥ 6` — large `k` via `sep_of_linear_form`, small `k` via the finite check
`sep_two_three_small`.  Complements `sep_two_three_of_gelfond_measure` (which takes the digested
integer measure `3^k ≤ (2^m−3^k)·k^6`); together they let the source's bound plug in in whichever of
its two standard forms is more convenient. -/
theorem sep_of_linear_form_poly (c : ℝ) (κ : ℕ)
    (hLF : ∀ k m : ℕ, 130 ≤ k → 3 ^ k < 2 ^ m → 2 ^ m < 2 * 3 ^ k →
             c / (k : ℝ) ^ κ ≤ (m : ℝ) * Real.log 2 - (k : ℝ) * Real.log 3)
    (hcross : ∀ k : ℕ, 130 ≤ k →
             (k : ℝ) ^ κ ≤ c * Real.exp ((k : ℝ) / 3 * Real.log 2))
    (k m : ℕ) (hk : 6 ≤ k) (h1 : 3 ^ k < 2 ^ m) (h2 : 2 ^ m < 2 * 3 ^ k) :
    3 ^ (3 * k) ≤ (2 ^ m - 3 ^ k) ^ 3 * 2 ^ k := by
  by_cases hbig : 130 ≤ k
  · apply sep_of_linear_form k m h1
    have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hkpos : (0 : ℝ) < (k : ℝ) ^ κ := pow_pos hkR κ
    have hexppos : (0 : ℝ) < Real.exp ((k : ℝ) / 3 * Real.log 2) := Real.exp_pos _
    have hc2 := hcross k hbig
    have key : Real.exp (-(k : ℝ) / 3 * Real.log 2) ≤ c / (k : ℝ) ^ κ := by
      rw [show -(k : ℝ) / 3 * Real.log 2 = -((k : ℝ) / 3 * Real.log 2) by ring, Real.exp_neg,
          le_div_iff₀ hkpos]
      calc (Real.exp ((k : ℝ) / 3 * Real.log 2))⁻¹ * (k : ℝ) ^ κ
          ≤ (Real.exp ((k : ℝ) / 3 * Real.log 2))⁻¹
              * (c * Real.exp ((k : ℝ) / 3 * Real.log 2)) :=
            mul_le_mul_of_nonneg_left hc2 (by positivity)
        _ = c := by
            rw [mul_comm c, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hexppos), one_mul]
    exact le_trans key (hLF k m hbig h1 h2)
  · exact sep_two_three_small k m hk (by omega) h1 h2

/-- **`exp(1/2) < 2`** (auxiliary for the general crossover step). -/
theorem exp_half_lt_two : Real.exp (1 / 2) < 2 := by
  have h : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_pos (1 / 2 : ℝ), Real.exp_one_lt_d9, h]

/-- **`C^2 ≤ 2^C` for `C ≥ 4`** (pure ℕ induction).  Base for the general crossover. -/
theorem nat_sq_le_two_pow (C : ℕ) (hC : 4 ≤ C) : C ^ 2 ≤ 2 ^ C := by
  induction C, hC using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have hstep : (n + 1) ^ 2 ≤ 2 * n ^ 2 := by nlinarith [hn]
      calc (n + 1) ^ 2 ≤ 2 * n ^ 2 := hstep
        _ ≤ 2 * 2 ^ n := by gcongr
        _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

/-- **General explicit crossover `k^C ≤ 2^k` for `C ≥ 4` and `k ≥ C^2`.**  Removes the
non-explicit threshold of `poly_le_two_pow`: whatever measure exponent the source's effective
Gelfond bound yields, the crossover feeding `sep_of_measure` (`k^(3C) ≤ 2^k`) holds from the
*explicit* point `k ≥ (3C)^2` — so `sep_of_uniform_measure` becomes fully concrete at any exponent
(only the finite residual `6 ≤ k < (3C)^2` remains for a per-`C` `native_decide` table).  Base
`(C^2)^C ≤ 2^(C^2)` via `nat_sq_le_two_pow`; inductive step via `(1 + 1/k)^C ≤ exp(1/2) < 2`
(from `k ≥ C^2 ≥ 2C`, using `Real.add_one_le_exp`). -/
theorem pow_le_two_pow_gen (C k : ℕ) (hC : 4 ≤ C) (hk : C ^ 2 ≤ k) : k ^ C ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base =>
      have hb : (2 ^ C) ^ C = 2 ^ (C ^ 2) := by rw [← pow_mul, pow_two]
      calc (C ^ 2) ^ C ≤ (2 ^ C) ^ C := Nat.pow_le_pow_left (nat_sq_le_two_pow C hC) C
        _ = 2 ^ (C ^ 2) := hb
  | succ n hn ih =>
      -- `n ≥ C^2 ≥ 2C`, so `C/n ≤ 1/2`
      have h2C : 2 * C ≤ C ^ 2 := by nlinarith [hC]
      have hn2C : 2 * C ≤ n := le_trans h2C hn
      have hnpos : 0 < n := by nlinarith [hC, hn]
      have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
      have hstep : (n + 1) ^ C ≤ 2 * n ^ C := by
        have hbase : (1 + 1 / (n : ℝ)) ≤ Real.exp (1 / (n : ℝ)) := by
          have := Real.add_one_le_exp (1 / (n : ℝ)); linarith
        have h0 : (0 : ℝ) ≤ 1 + 1 / (n : ℝ) := by positivity
        have hpow : (1 + 1 / (n : ℝ)) ^ C ≤ (Real.exp (1 / (n : ℝ))) ^ C :=
          pow_le_pow_left₀ h0 hbase C
        have hexp : (Real.exp (1 / (n : ℝ))) ^ C = Real.exp ((C : ℝ) / n) := by
          rw [← Real.exp_nat_mul]; congr 1; field_simp
        have hCn : (C : ℝ) / n ≤ 1 / 2 := by
          rw [div_le_div_iff₀ hnR (by norm_num)]
          have : (2 * C : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2C
          linarith
        have hexple : Real.exp ((C : ℝ) / n) ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr hCn
        have hlt2 : (1 + 1 / (n : ℝ)) ^ C ≤ 2 := by
          calc (1 + 1 / (n : ℝ)) ^ C ≤ Real.exp ((C : ℝ) / n) := by rw [← hexp]; exact hpow
            _ ≤ Real.exp (1 / 2) := hexple
            _ ≤ 2 := le_of_lt exp_half_lt_two
        have hratio : ((n : ℝ) + 1) / n = 1 + 1 / n := by field_simp
        have hdiv : (((n : ℝ) + 1) / n) ^ C ≤ 2 := by rw [hratio]; exact hlt2
        rw [div_pow, div_le_iff₀ (by positivity)] at hdiv
        have hcast : ((n : ℝ) + 1) ^ C = (((n + 1) ^ C : ℕ) : ℝ) := by push_cast; ring
        have hcast2 : 2 * (n : ℝ) ^ C = ((2 * n ^ C : ℕ) : ℝ) := by push_cast; ring
        rw [hcast, hcast2] at hdiv
        exact_mod_cast hdiv
      calc (n + 1) ^ C ≤ 2 * n ^ C := hstep
        _ ≤ 2 * 2 ^ n := by gcongr
        _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

/-- **Threshold-parametric linear-form reduction.**  Identical to `sep_of_linear_form_poly` but with
the crossover threshold `K` a free parameter (rather than hard-coded `130`) and the residual small
range `6 ≤ k < K` discharged by a supplied finite check `hfin`.  This is what lets a *large* measure
exponent `κ` (whose crossover point sits well above `130`) still close `sep_two_three`: pick `K`
past the crossover and `native_decide` the finite table below it.  Large `k` (`≥ K`) goes through
`sep_of_linear_form`; small `k` through `hfin`. -/
theorem sep_of_linear_form_poly_threshold (c : ℝ) (κ K : ℕ)
    (hLF : ∀ k m : ℕ, K ≤ k → 3 ^ k < 2 ^ m → 2 ^ m < 2 * 3 ^ k →
             c / (k : ℝ) ^ κ ≤ (m : ℝ) * Real.log 2 - (k : ℝ) * Real.log 3)
    (hcross : ∀ k : ℕ, K ≤ k →
             (k : ℝ) ^ κ ≤ c * Real.exp ((k : ℝ) / 3 * Real.log 2))
    (hfin : ∀ k m : ℕ, 6 ≤ k → k < K → 3 ^ k < 2 ^ m → 2 ^ m < 2 * 3 ^ k →
             3 ^ (3 * k) ≤ (2 ^ m - 3 ^ k) ^ 3 * 2 ^ k)
    (k m : ℕ) (hk : 6 ≤ k) (h1 : 3 ^ k < 2 ^ m) (h2 : 2 ^ m < 2 * 3 ^ k) :
    3 ^ (3 * k) ≤ (2 ^ m - 3 ^ k) ^ 3 * 2 ^ k := by
  by_cases hbig : K ≤ k
  · apply sep_of_linear_form k m h1
    have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hkpos : (0 : ℝ) < (k : ℝ) ^ κ := pow_pos hkR κ
    have hexppos : (0 : ℝ) < Real.exp ((k : ℝ) / 3 * Real.log 2) := Real.exp_pos _
    have hc2 := hcross k hbig
    have key : Real.exp (-(k : ℝ) / 3 * Real.log 2) ≤ c / (k : ℝ) ^ κ := by
      rw [show -(k : ℝ) / 3 * Real.log 2 = -((k : ℝ) / 3 * Real.log 2) by ring, Real.exp_neg,
          le_div_iff₀ hkpos]
      calc (Real.exp ((k : ℝ) / 3 * Real.log 2))⁻¹ * (k : ℝ) ^ κ
          ≤ (Real.exp ((k : ℝ) / 3 * Real.log 2))⁻¹
              * (c * Real.exp ((k : ℝ) / 3 * Real.log 2)) :=
            mul_le_mul_of_nonneg_left hc2 (by positivity)
        _ = c := by
            rw [mul_comm c, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hexppos), one_mul]
    exact le_trans key (hLF k m hbig h1 h2)
  · exact hfin k m hk (by omega) h1 h2

/-- **Concrete crossover for the Rhin/κ=14 measure: `3^14·k^14 ≤ exp((k/3)·log2)` for `k ≥ 450`.**
The crossover point of the `κ = 14`, `c = 1/3^14` effective measure sits near `k ≈ 435`; `450` is a
clean divisible-by-3 threshold past it.  Base `3^14·450^14 = 1350^14 ≤ 2^150` (`native_decide`);
step uses `((n+1)/n)^14 ≤ exp(14/n) ≤ exp((1/3)log2)` for `n ≥ 450` (since `14/450 < (log2)/3`). -/
theorem crossover_exp_450 (k : ℕ) (hk : 450 ≤ k) :
    (3 : ℝ) ^ 14 * (k : ℝ) ^ 14 ≤ Real.exp ((k : ℝ) / 3 * Real.log 2) := by
  induction k, hk using Nat.le_induction with
  | base =>
      have he : Real.exp (((450 : ℕ) : ℝ) / 3 * Real.log 2) = (2 : ℝ) ^ 150 := by
        have hlg : ((450 : ℕ) : ℝ) / 3 * Real.log 2 = Real.log ((2 : ℝ) ^ 150) := by
          rw [Real.log_pow]; push_cast; ring
        rw [hlg, Real.exp_log (by positivity)]
      rw [he]
      have hnat : (3 : ℕ) ^ 14 * 450 ^ 14 ≤ 2 ^ 150 := by native_decide
      calc (3 : ℝ) ^ 14 * ((450 : ℕ) : ℝ) ^ 14
            = (((3 ^ 14 * 450 ^ 14 : ℕ)) : ℝ) := by push_cast; ring
        _ ≤ (((2 ^ 150 : ℕ)) : ℝ) := by exact_mod_cast hnat
        _ = (2 : ℝ) ^ 150 := by push_cast; ring
  | succ n hn ih =>
      have hnpos : 0 < n := by omega
      have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
      -- ratio bound: ((n+1)/n)^14 ≤ exp((1/3)·log2)
      have hbase : (1 + 1 / (n : ℝ)) ≤ Real.exp (1 / (n : ℝ)) := by
        have := Real.add_one_le_exp (1 / (n : ℝ)); linarith
      have h0 : (0 : ℝ) ≤ 1 + 1 / (n : ℝ) := by positivity
      have hpow : (1 + 1 / (n : ℝ)) ^ 14 ≤ (Real.exp (1 / (n : ℝ))) ^ 14 :=
        pow_le_pow_left₀ h0 hbase 14
      have hexp : (Real.exp (1 / (n : ℝ))) ^ 14 = Real.exp ((14 : ℝ) / n) := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      have hCn : (14 : ℝ) / n ≤ (1 / 3) * Real.log 2 := by
        have hnge : (450 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have hlog : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
        rw [div_le_iff₀ hnR]
        nlinarith [hlog, hnge]
      have hexple : Real.exp ((14 : ℝ) / n) ≤ Real.exp ((1 / 3) * Real.log 2) :=
        Real.exp_le_exp.mpr hCn
      have hratiobound : (1 + 1 / (n : ℝ)) ^ 14 ≤ Real.exp ((1 / 3) * Real.log 2) := by
        calc (1 + 1 / (n : ℝ)) ^ 14 ≤ Real.exp ((14 : ℝ) / n) := by rw [← hexp]; exact hpow
          _ ≤ Real.exp ((1 / 3) * Real.log 2) := hexple
      -- turn ih into the (n+1) bound
      have hsplit : Real.exp (((n + 1 : ℕ) : ℝ) / 3 * Real.log 2)
          = Real.exp (((n : ℕ) : ℝ) / 3 * Real.log 2) * Real.exp ((1 / 3) * Real.log 2) := by
        rw [← Real.exp_add]; congr 1; push_cast; ring
      have hn14 : (3 : ℝ) ^ 14 * ((n + 1 : ℕ) : ℝ) ^ 14
          = (3 : ℝ) ^ 14 * (n : ℝ) ^ 14 * (1 + 1 / (n : ℝ)) ^ 14 := by
        have hne : (n : ℝ) ≠ 0 := ne_of_gt hnR
        have hnn1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) * (1 + 1 / (n : ℝ)) := by
          push_cast; field_simp
        rw [hnn1, mul_pow]; ring
      rw [hsplit, hn14]
      have hihnn : (0 : ℝ) ≤ (3 : ℝ) ^ 14 * (n : ℝ) ^ 14 := by positivity
      have hexpnn : (0 : ℝ) ≤ Real.exp (((n : ℕ) : ℝ) / 3 * Real.log 2) := (Real.exp_pos _).le
      calc (3 : ℝ) ^ 14 * (n : ℝ) ^ 14 * (1 + 1 / (n : ℝ)) ^ 14
          ≤ (3 : ℝ) ^ 14 * (n : ℝ) ^ 14 * Real.exp ((1 / 3) * Real.log 2) :=
            mul_le_mul_of_nonneg_left hratiobound hihnn
        _ ≤ Real.exp (((n : ℕ) : ℝ) / 3 * Real.log 2) * Real.exp ((1 / 3) * Real.log 2) :=
            mul_le_mul_of_nonneg_right ih (Real.exp_pos _).le

/-- **Finite check for the residual `6 ≤ k < 450` (`native_decide`).**  For every near-critical
`(k, m)` with `k < 450`, the separation `3^(3k) ≤ (2^m−3^k)^3·2^k` holds outright.  `m` is bounded by
`2^m < 2·3^449 < 2^713`, so this is a finite decidable table. -/
theorem sep_two_three_finite_check_450 :
    ∀ k ∈ Finset.range 450, ∀ m ∈ Finset.range 713,
      ¬ (6 ≤ k ∧ 3 ^ k < 2 ^ m ∧ 2 ^ m < 2 * 3 ^ k) ∨
        3 ^ (3 * k) ≤ (2 ^ m - 3 ^ k) ^ 3 * 2 ^ k := by
  native_decide

/-- **Small-`k` case of `sep_two_three` for the `κ=14` threshold (sorry-free).**  For near-critical
`6 ≤ k < 450` the separation holds unconditionally — the `hfin` input to
`sep_of_linear_form_poly_threshold` at `K = 450`. -/
theorem sep_two_three_small_450 (k m : ℕ) (hk : 6 ≤ k) (hklt : k < 450)
    (h1 : 3 ^ k < 2 ^ m) (h2 : 2 ^ m < 2 * 3 ^ k) :
    3 ^ (3 * k) ≤ (2 ^ m - 3 ^ k) ^ 3 * 2 ^ k := by
  have hmlt : m < 713 := by
    have hlt : 2 ^ m < 2 ^ 713 := by
      calc 2 ^ m < 2 * 3 ^ k := h2
        _ ≤ 2 * 3 ^ 449 := by
              have hk449 : k ≤ 449 := by omega
              gcongr
              norm_num
        _ < 2 ^ 713 := by native_decide
    exact (Nat.pow_lt_pow_iff_right (a := 2) (by norm_num)).mp hlt
  rcases sep_two_three_finite_check_450 k (Finset.mem_range.mpr hklt) m (Finset.mem_range.mpr hmlt)
    with h | h
  · exact absurd ⟨hk, h1, h2⟩ h
  · exact h

/-- **Effective irrationality measure of `log₂ 3`, concrete constants (from the Rhin 1987 axiom).**
On the near-critical window (`3^k < 2^m < 2·3^k`, `k ≥ 1`) the Baker linear form obeys
`(1/3^14) / k^14 ≤ m·log2 − k·log3`.  This is the concrete-`(κ,c)` form (`κ = 14`, `c = 1/3^14`)
consumed as `hLF` by `sep_of_linear_form_poly_threshold`.

Proved from `Assumed.rhin_1987_log_two_three_measure` (`|u₀+u₁log2+u₂log3| ≥ 1/H^14`, `H ≥ 2`) at
`(u₀,u₁,u₂) = (0, m, −k)`: then `Λ = m·log2 − k·log3 > 0`, `H = max(m,k) = m ≥ 2` (since `m > k ≥ 1`
on the window), giving `Λ ≥ 1/m^14`, and `m < 3k` gives `1/m^14 ≥ (1/3^14)/k^14`. -/
theorem log23_effective_measure_concrete
    (k m : ℕ) (hk : 1 ≤ k) (h1 : 3 ^ k < 2 ^ m) (h2 : 2 ^ m < 2 * 3 ^ k) :
    (1 / 3 ^ 14) / (k : ℝ) ^ 14 ≤ (m : ℝ) * Real.log 2 - (k : ℝ) * Real.log 3 := by
  -- `m` sits in `(k, 3k)` on the near-critical window.
  have hkm : k < m := by
    have h2k : (2 : ℕ) ^ k ≤ 3 ^ k := Nat.pow_le_pow_left (by norm_num) k
    have : (2 : ℕ) ^ k < 2 ^ m := lt_of_le_of_lt h2k h1
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
  have hm3k : m < 3 * k := by
    have hbnd : 2 * 3 ^ k ≤ 2 ^ (3 * k) := by
      calc 2 * 3 ^ k ≤ 2 * 4 ^ k := by gcongr; norm_num
        _ ≤ 2 ^ k * 4 ^ k := by
            gcongr
            calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
              _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
        _ = 2 ^ (3 * k) := by rw [← Nat.mul_pow]; norm_num [pow_mul]
    have : (2 : ℕ) ^ m < 2 ^ (3 * k) := lt_of_lt_of_le h2 hbnd
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
  -- `Λ > 0`.
  have hΛpos : (0 : ℝ) < (m : ℝ) * Real.log 2 - (k : ℝ) * Real.log 3 := by
    have h3lt : (3 : ℝ) ^ k < (2 : ℝ) ^ m := by exact_mod_cast h1
    have hlog : Real.log ((3 : ℝ) ^ k) < Real.log ((2 : ℝ) ^ m) :=
      Real.log_lt_log (by positivity) h3lt
    rw [Real.log_pow, Real.log_pow] at hlog
    linarith
  -- Apply Rhin at `(0, m, −k)`.  `H = max |m| |−k| = m` (since `m > k`), and `m ≥ 2`.
  have hax := Assumed.rhin_1987_log_two_three_measure 0 (m : ℤ) (-(k : ℤ)) ?_
  · -- rewrite the Rhin bound to `1/m^14 ≤ Λ`
    have hz : max |(m : ℤ)| |-(k : ℤ)| = (m : ℤ) := by
      rw [abs_of_nonneg (by positivity), abs_neg, abs_of_nonneg (by positivity)]
      exact max_eq_left (by exact_mod_cast hkm.le)
    rw [hz, Int.cast_neg] at hax
    have hval : |((0 : ℤ) : ℝ) + ((m : ℤ) : ℝ) * Real.log 2 + -((k : ℤ) : ℝ) * Real.log 3|
        = (m : ℝ) * Real.log 2 - (k : ℝ) * Real.log 3 := by
      rw [abs_of_pos]
      · push_cast; ring
      · push_cast; linarith [hΛpos]
    have haxΛ : 1 / ((m : ℤ) : ℝ) ^ 14 ≤ (m : ℝ) * Real.log 2 - (k : ℝ) * Real.log 3 :=
      hval ▸ hax
    -- `(1/3^14)/k^14 ≤ 1/m^14 ≤ Λ` since `m < 3k`.
    have hmlt : ((m : ℤ) : ℝ) ≤ 3 * (k : ℝ) := by push_cast; exact_mod_cast hm3k.le
    have hstep : (1 / 3 ^ 14) / (k : ℝ) ^ 14 ≤ 1 / ((m : ℤ) : ℝ) ^ 14 := by
      have hle : ((m : ℤ) : ℝ) ^ 14 ≤ 3 ^ 14 * (k : ℝ) ^ 14 := by
        calc ((m : ℤ) : ℝ) ^ 14 ≤ (3 * (k : ℝ)) ^ 14 :=
              pow_le_pow_left₀ (by positivity) hmlt 14
          _ = 3 ^ 14 * (k : ℝ) ^ 14 := by rw [mul_pow]
      have hmpos : (0 : ℝ) < ((m : ℤ) : ℝ) ^ 14 := by
        have : (0 : ℝ) < ((m : ℤ) : ℝ) := by exact_mod_cast (by omega : 0 < m)
        positivity
      have h1 := one_div_le_one_div_of_le hmpos hle
      rw [div_div]; exact h1
    exact le_trans hstep haxΛ
  · -- `max |m| |−k| ≥ 2` since `m ≥ 2`
    rw [abs_of_nonneg (by positivity : (0:ℤ) ≤ (m:ℤ))]
    have : (2 : ℤ) ≤ (m : ℤ) := by exact_mod_cast (by omega : 2 ≤ m)
    exact le_trans this (le_max_left _ _)

/-- **Effective irrationality measure of `log₂ 3` (existential audit surface).**  Repackages
`log23_effective_measure_concrete` in the `∃ κ c` shape used elsewhere (`κ = 14`, `c = 1/3^14`). -/
theorem log23_effective_measure :
    ∃ (κ : ℕ) (c : ℝ), 0 < c ∧
      ∀ k m : ℕ, 1 ≤ k → 3 ^ k < 2 ^ m → 2 ^ m < 2 * 3 ^ k →
        c / (k : ℝ) ^ κ ≤ (m : ℝ) * Real.log 2 - (k : ℝ) * Real.log 3 :=
  ⟨14, 1 / 3 ^ 14, by positivity, fun k m hk h1 h2 => log23_effective_measure_concrete k m hk h1 h2⟩

/-- **Weak power separation `β = 1/3` (sorry-free, modulo the cited Rhin 1987 axiom).**  For the
near-critical power `2^m` just above `3^k` (`3^k < 2^m < 2·3^k`) with `k ≥ 6`,
`3^(3k) ≤ (2^m − 3^k)^3 · 2^k`, i.e. `2^m − 3^k ≥ 3^k · 2^(−k/3)`.

Discharged by instantiating `sep_of_linear_form_poly_threshold` at the concrete Rhin measure
constants `κ = 14`, `c = 1/3^14` (`log23_effective_measure_concrete`), threshold `K = 450` (past the
crossover point `k ≈ 435`), crossover `crossover_exp_450`, and the finite check
`sep_two_three_small_450` on `6 ≤ k < 450`.  The sole remaining mathematical input is the cited
`Assumed.rhin_1987_log_two_three_measure`; everything else is elementary + a `native_decide` table. -/
theorem sep_two_three (k m : ℕ) (hk : 6 ≤ k) (h1 : 3 ^ k < 2 ^ m) (h2 : 2 ^ m < 2 * 3 ^ k) :
    3 ^ (3 * k) ≤ (2 ^ m - 3 ^ k) ^ 3 * 2 ^ k := by
  refine sep_of_linear_form_poly_threshold (1 / 3 ^ 14) 14 450 ?_ ?_ ?_ k m hk h1 h2
  · intro k m hk450 h1 h2
    exact log23_effective_measure_concrete k m (by omega) h1 h2
  · intro k hk450
    have hc := crossover_exp_450 k hk450
    rw [show (1 : ℝ) / 3 ^ 14 * Real.exp ((k : ℝ) / 3 * Real.log 2)
          = Real.exp ((k : ℝ) / 3 * Real.log 2) / 3 ^ 14 by ring,
        le_div_iff₀ (by positivity : (0 : ℝ) < (3 : ℝ) ^ 14)]
    linarith [hc, mul_comm ((3 : ℝ) ^ 14) ((k : ℝ) ^ 14)]
  · intro k m hk6 hklt h1 h2
    exact sep_two_three_small_450 k m hk6 hklt h1 h2

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
