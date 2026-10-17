/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.WythoffRunCriterion

/-!
# Elementary tools for the finiteness of the sporadic Wythoff set (Lemmas U*, H½, SG, O∞)

Research note `wythoff-finite`, §2 (Lemma H½, Lemma U\* with Corollaries U1 and U2, Lemma SG)
and §3.3 (Lemma O∞), with the notation of `WythoffAutomaton` and `WythoffPisot`.  Let
`x ∈ (1/2, 1)` be a root of a monic `P = t^d + ⋯ + a_0 ∈ ℤ[t]`, `q_k = synDiv P x k` the
coefficients of `Q = P/(t − x)`, and `q̃_0 = q_0 + 2a_0` (`qTilde`), the coefficient of `ε_0`
in the top row.

**The `q̃_0` identity** (`qTilde_eq`, `qTilde_eq_mul`).  `a_0 = −xq_0`
(`coeff_zero_eq_synDiv`), so `q̃_0 = (1 − 2x)q_0 = a_0(2x − 1)/x`.  In particular
`|q̃_0| ∈ {1, 2}` makes `x = a_0/(2a_0 ∓ |q̃_0|)` rational (`not_irrational_of_abs_qTilde`).

**Lemma U\*** (`ustar_runSystem`).  If `|q̃_0| > 1` and `|q̃_0| ≠ 2`, the run system has a
solution of every length, given by one infinite sequence (`ustarSeq`): `ε_i = 1 − x ∈ (0, 1/2)`
for `i ≥ 1`.  *Proof.*  Every standard row is `Q(1)(1 − x) = P(1) ∈ ℤ`
(`eval_one_eq_mul_sum_synDiv`).  The top row is
`T = q̃_0ε_0 + (1 − x)(Q(1) − q_0) = P(1) + a_0 − q̃_0(1 − ε_0)`, using
`a_0(1 − x)/x = a_0 − q̃_0`.  So we need an integer `q̃_0(1 − ε_0)` with `ε_0 ∈ (0, 1/2)`, i.e.
an integer strictly between `q̃_0/2` and `q̃_0`: `±1` for `|q̃_0| ∈ (1, 2)`, and the interval
is longer than `1` for `|q̃_0| > 2` (`exists_int_eq_mul_one_sub`).  For irreducible `P` of
degree `≥ 2`, `x` is irrational (`irrational_of_irreducible`), so `|q̃_0| ≠ 2` is automatic.

**Headline** (`ustar_infinite_runs_of_weyl`), conditional on `WeylEquidistributionMulti` via
`runCriterion_of_weyl`: `|q̃_0| > 1` gives infinitely many runs of every length.
**Corollary U1** (`abs_qTilde_lt_one_of_boundedRuns`, `xOf_lt_of_boundedRuns`).  Bounded runs
(`BoundedRuns`) force `|q̃_0| < 1` (`|q̃_0| = 1` is rational), i.e.
`x < |a_0|/(2|a_0| − 1) = 1/2 + 1/(2(2|a_0| − 1))`.

**Lemma H½** (`qTilde_mul_prod_eq`).  With `x_s` the other complex roots,
`q̃_0·2^{d−1}·∏_s(1 − 1/(2x_s)) = 2^dP(1/2) =: N`, an odd integer
(`two_pow_mul_aeval_half_odd`).  *Proof.*  `P(t) = (t − x)∏(t − x_s)`; at `t = 0`,
`a_0 = −x∏(−x_s)`, so `q̃_0 = (1 − 2x)∏(−x_s)`; at `t = 1/2`,
`P(1/2) = (1/2 − x)∏(−x_s)∏(1 − 1/(2x_s))`.
**Corollary U2** (`abs_two_pow_aeval_half_lt`, `one_lt_three_pow_mul_abs_qTilde`,
`u2_of_boundedRuns`).  If every `|x_s| > 1`, each `|1 − 1/(2x_s)| < 3/2`; so `|q̃_0| < 1` gives
`1 ≤ |N| < 3^{d−1}`, and always `|q̃_0| > 3^{1−d}`.

**Lemma SG** (`sg_runSystem`, `sg_runSystem_conj`).  Slide a sequence `γ` with every row
integral and margin `μ` on indices `≥ 1` along a homogeneous `c` (`c_0 = 1`, `|c_i| ≤ ρ^i`):
`ε_i = γ_i + κc_i` with `κ = g − γ_0`, `g` on the grid `2a_0g ∈ ℤ`, `g ∈ (0, 1/2)`.  Rows are
unchanged, `ε_0 = g`, the top row is `R_0(γ) + 2a_0g ∈ ℤ`, and `|κ|ρ^{n−1} < μ` keeps the box.

**Lemma O∞** (`synDiv_half_zero`, `oInf`).  For `E = t^d + Σ_{k=1}^{d−1}e_kt^k ∈ ℤ[t]`,
`c_k = synDiv E (1/2) k = Σ_{j>k} e_j 2^{−(j−k−1)}` (so `c_0 = 2E(1/2)`).  If every `c_k ≥ 0`
and `Σ_{k<d} c_k ≤ 2`, then `E = t^d`.  *Proof.*  `c_k = 2^{k+1−d}m_k` with
`m_k = Σ_{j>k} e_j2^{d−j}` an odd integer, so `m_k ≥ 1`; `Σ 2^km_k ≤ 2^d = 1 + Σ 2^k` forces
every `m_k = 1` (raising one to `3` adds `2^{k+1} ≥ 2`), and `e_k2^{d−k} = m_{k−1} − m_k = 0`.

Truth checks: `tmp/drafter-ustar/check.py` (gitignored; copy of
`~/personal/tmp/amusical-agents/out/wythoff-ustar-lean/check.py`).
-/

namespace CollatzMoonshot.WythoffUStar

open CollatzMoonshot.WythoffGeneral CollatzMoonshot.WythoffAutomaton
  CollatzMoonshot.WythoffPisot CollatzMoonshot.WythoffRunCriterion Polynomial

/-! ## Definitions -/

/-- `q̃_0 = q_0 + 2a_0`, the coefficient of `ε_0` in the top row. -/
noncomputable def qTilde (P : ℤ[X]) (x : ℝ) : ℝ :=
  synDiv P x 0 + 2 * (P.coeff 0 : ℝ)

/-- Lemma U\*'s sequence: `ε_0 = e0` and `ε_i = 1 − x` for `i ≥ 1`. -/
noncomputable def ustarSeq (e0 x : ℝ) (i : ℕ) : ℝ :=
  if i = 0 then e0 else 1 - x

/-- `W_α` has bounded runs after up-points, off a finite set: some `J` such that only finitely
many positive even `u` are followed by `J + 1` odd iterates. -/
def BoundedRuns (α : ℝ) : Prop :=
  ∃ J : ℕ, {u : ℤ | 0 < u ∧ u % 2 = 0 ∧ ∀ j ∈ Finset.Icc 1 (J + 1), (wy α)^[j] u % 2 = 1}.Finite

/-! ## The `q̃_0` identity -/

section QTilde

variable {P : ℤ[X]} {x : ℝ}

/-- **(proved).**  `q̃_0 = (1 − 2x)q_0`.  Paper proof: `a_0 = −xq_0`
(`coeff_zero_eq_synDiv`). -/
theorem qTilde_eq_mul (hroot : aeval x P = 0) : qTilde P x = (1 - 2 * x) * synDiv P x 0 := by
  unfold qTilde
  rw [coeff_zero_eq_synDiv hroot]
  ring

/-- **(proved; the `q̃_0` identity).**  For a root `x ≠ 0` of `P`, `q̃_0 = a_0(2x − 1)/x`.
Paper proof: `a_0 = −xq_0` (`coeff_zero_eq_synDiv`), so `q_0 = −a_0/x`. -/
theorem qTilde_eq (hroot : aeval x P = 0) (hx : x ≠ 0) :
    qTilde P x = P.coeff 0 * (2 * x - 1) / x := by
  rw [eq_div_iff hx, qTilde_eq_mul hroot, coeff_zero_eq_synDiv hroot]
  ring

/-- **(proved; U\*, the excluded values).**  `|q̃_0| = 1` or `|q̃_0| = 2` makes `x`
rational.  Paper proof: `q̃_0 = s ∈ {±1, ±2}` and `qTilde_eq` give `x(2a_0 − s) = a_0`.  If
`2a_0 = s`, then `a_0 = 0` and `sx = 0`, impossible; otherwise `x = a_0/(2a_0 − s) ∈ ℚ`. -/
theorem not_irrational_of_abs_qTilde (hroot : aeval x P = 0) (hx : x ≠ 0)
    (h : |qTilde P x| = 1 ∨ |qTilde P x| = 2) : ¬ Irrational x := by
  intro hirr
  rw [qTilde_eq hroot hx] at h
  obtain ⟨s, hs, hsv⟩ : ∃ s : ℤ, s ≠ 0 ∧ (P.coeff 0 : ℝ) * (2 * x - 1) / x = s := by
    rcases h with h | h <;> rcases (abs_eq (by norm_num)).1 h with h' | h'
    · exact ⟨1, by norm_num, by rw [h']; norm_num⟩
    · exact ⟨-1, by norm_num, by rw [h']; norm_num⟩
    · exact ⟨2, by norm_num, by rw [h']; norm_num⟩
    · exact ⟨-2, by norm_num, by rw [h']; norm_num⟩
  rw [div_eq_iff hx] at hsv
  by_cases h0 : 2 * P.coeff 0 - s = 0
  · have ha : (P.coeff 0 : ℝ) = 0 := by
      have : ((2 * P.coeff 0 - s : ℤ) : ℝ) = 0 := by exact_mod_cast h0
      push_cast at this
      linear_combination -hsv + x * this
    have : (s : ℝ) = 0 := by
      have : ((2 * P.coeff 0 - s : ℤ) : ℝ) = 0 := by exact_mod_cast h0
      push_cast at this
      linarith
    exact hs (by exact_mod_cast this)
  · have hne : ((2 * P.coeff 0 - s : ℤ) : ℝ) ≠ 0 := by exact_mod_cast h0
    apply hirr ⟨(P.coeff 0 : ℚ) / ((2 * P.coeff 0 - s : ℤ) : ℚ), ?_⟩
    push_cast at hne ⊢
    rw [div_eq_iff hne]
    linarith

/-- **(proved).**  A root of a monic irreducible `P ∈ ℤ[t]` of degree `≥ 2` is
irrational.  Paper proof: as in `WythoffRunCriterion.eq_zero_of_natDegree_lt`,
`P.map (algebraMap ℤ ℚ) = minpoly ℚ x`; if `x = r ∈ ℚ`, then `X − C r` (degree `1 < d`) vanishes
at `x`, contradicting `minpoly.degree_le_of_ne_zero`. -/
theorem irrational_of_irreducible (hP : P.Monic) (hirr : Irreducible P) (hd : 2 ≤ P.natDegree)
    (hroot : aeval x P = 0) : Irrational x := by
  rintro ⟨r, hr⟩
  set PQ : ℚ[X] := P.map (algebraMap ℤ ℚ) with hPQ
  have hirrQ : Irreducible PQ := (hP.irreducible_iff_irreducible_map_fraction_map).1 hirr
  have hxQ : aeval x PQ = 0 := by rw [hPQ, aeval_map_algebraMap]; exact hroot
  have hmin : PQ = minpoly ℚ x := minpoly.eq_of_irreducible_of_monic hirrQ hxQ (hP.map _)
  have hQx : aeval x (X - C r : ℚ[X]) = 0 := by simp [← hr]
  have h := minpoly.degree_le_of_ne_zero ℚ x (X_sub_C_ne_zero r) hQx
  rw [← hmin, degree_eq_natDegree (hP.map _).ne_zero, degree_X_sub_C, hP.natDegree_map] at h
  have : P.natDegree ≤ 1 := by exact_mod_cast h
  omega

end QTilde

/-! ## Lemma U\*, automaton form -/

section UStar

variable {P : ℤ[X]} {x : ℝ}

/-- **(proved).**  `ε_0 = e0`. -/
theorem ustarSeq_zero (e0 x : ℝ) : ustarSeq e0 x 0 = e0 := if_pos rfl

/-- **(proved).**  `ε_i = 1 − x` for `i ≠ 0`. -/
theorem ustarSeq_of_ne (e0 x : ℝ) {i : ℕ} (hi : i ≠ 0) : ustarSeq e0 x i = 1 - x := if_neg hi

/-- **(proved; U\*, the integer in `(q̃_0/2, q̃_0)`).**  For real `q` with `|q| > 1` and
`|q| ≠ 2`, some `e0 ∈ (0, 1/2)` makes `q(1 − e0)` an integer.  Paper proof: by symmetry
`q > 1`.  If `q < 2`, take `m = 1`, `e0 = 1 − 1/q ∈ (0, 1/2)`.  If `q > 2`, take
`m = ⌈q⌉ − 1 ∈ [q − 1, q)`, so `m > q/2`, and `e0 = 1 − m/q`.  For `q < −1`, negate `m`. -/
theorem exists_int_eq_mul_one_sub {q : ℝ} (h1 : 1 < |q|) (h2 : |q| ≠ 2) :
    ∃ e0 : ℝ, 0 < e0 ∧ e0 < 1 / 2 ∧ ∃ m : ℤ, q * (1 - e0) = m := by
  have key : ∀ q : ℝ, 1 < q → q ≠ 2 →
      ∃ e0 : ℝ, 0 < e0 ∧ e0 < 1 / 2 ∧ ∃ m : ℤ, q * (1 - e0) = m := by
    intro q h1 h2
    rcases lt_or_gt_of_ne h2 with h | h
    · refine ⟨1 - 1 / q, ?_, ?_, 1, ?_⟩
      · have : 1 / q < 1 := by rw [div_lt_one (by linarith)]; exact h1
        linarith
      · have : 1 / 2 < 1 / q := by rw [div_lt_div_iff₀ (by norm_num) (by linarith)]; linarith
        linarith
      · rw [sub_sub_cancel]; push_cast; field_simp
    · have hm1 : ((⌈q⌉ - 1 : ℤ) : ℝ) < q := by push_cast; linarith [Int.ceil_lt_add_one q]
      have hm2 : q - 1 ≤ ((⌈q⌉ - 1 : ℤ) : ℝ) := by push_cast; linarith [Int.le_ceil q]
      refine ⟨1 - ((⌈q⌉ - 1 : ℤ) : ℝ) / q, ?_, ?_, ⌈q⌉ - 1, ?_⟩
      · have : ((⌈q⌉ - 1 : ℤ) : ℝ) / q < 1 := by rw [div_lt_one (by linarith)]; exact hm1
        linarith
      · have : 1 / 2 < ((⌈q⌉ - 1 : ℤ) : ℝ) / q := by rw [lt_div_iff₀ (by linarith)]; linarith
        linarith
      · rw [sub_sub_cancel]; field_simp
  rcases le_or_gt 0 q with hq | hq
  · rw [abs_of_nonneg hq] at h1 h2; exact key q h1 h2
  · rw [abs_of_neg hq] at h1 h2
    obtain ⟨e0, h0, h1', m, hm⟩ := key (-q) h1 h2
    exact ⟨e0, h0, h1', -m, by push_cast; linarith⟩

/-- **(proved; U\*, the standard rows).**  For `i ≥ 1`, `R_i(ustarSeq) = Q(1)(1 − x) = P(1)`.
Paper proof: every index `i + k ≥ 1`, so the sequence is the constant `1 − x` there;
`eval_one_eq_mul_sum_synDiv`. -/
theorem stdRow_ustarSeq (hroot : aeval x P = 0) (e0 : ℝ) {i : ℕ} (hi : 1 ≤ i) :
    stdRow (synDiv P x) P.natDegree (ustarSeq e0 x) i = ((P.eval 1 : ℤ) : ℝ) := by
  have h : ∀ k ∈ Finset.range P.natDegree,
      synDiv P x k * ustarSeq e0 x (i + k) = synDiv P x k * (1 - x) := fun k _ => by
    rw [ustarSeq_of_ne e0 x (by omega)]
  rw [stdRow, Finset.sum_congr rfl h, ← Finset.sum_mul, eval_one_eq_mul_sum_synDiv hroot]
  ring

/-- **(proved; U\*, the top row).**  `T(ustarSeq) = P(1) + a_0 − q̃_0(1 − e0)`.  Paper
proof: `topRow = q̃_0e0 + (1 − x)(Q(1) − q_0)` (split `range d = {0} ∪ Ico 1 d`); then
`(1 − x)Q(1) = P(1)` (`eval_one_eq_mul_sum_synDiv`) and `a_0 = −xq_0`
(`coeff_zero_eq_synDiv`) make the rest `ring`. -/
theorem topRow_ustarSeq (hd : 1 ≤ P.natDegree) (hroot : aeval x P = 0) (e0 : ℝ) :
    topRow (synDiv P x) P.natDegree (P.coeff 0) (ustarSeq e0 x) =
      ((P.eval 1 : ℤ) : ℝ) + P.coeff 0 - qTilde P x * (1 - e0) := by
  have h1 := eval_one_eq_mul_sum_synDiv hroot
  have h0 := coeff_zero_eq_synDiv hroot
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)] at h1
  simp only [zero_add] at h1
  have hs : ∑ k ∈ Finset.Ico 1 P.natDegree, synDiv P x k * ustarSeq e0 x k =
      (∑ k ∈ Finset.Ico 1 P.natDegree, synDiv P x k) * (1 - x) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k hk => by
      rw [ustarSeq_of_ne e0 x (by have := (Finset.mem_Ico.1 hk).1; omega)]
  unfold topRow qTilde
  rw [hs, h1, h0, ustarSeq_zero]
  ring

/-- **(proved; Lemma U\*, automaton form).**  Let `x ∈ (1/2, 1)` be a root of
`P ∈ ℤ[t]` of degree `≥ 1` with `|q̃_0| > 1` and `|q̃_0| ≠ 2`.  Then one infinite sequence
`ustarSeq e0 x` solves the run system of every length `n`.  Paper proof:
`exists_int_eq_mul_one_sub` gives `e0`; the box is `e0 ∈ (0, 1/2)` and `1 − x ∈ (0, 1/2)`;
the rows are `stdRow_ustarSeq` and `topRow_ustarSeq`. -/
theorem ustar_runSystem (hd : 1 ≤ P.natDegree) (hx1 : 1 / 2 < x) (hx2 : x < 1)
    (hroot : aeval x P = 0) (hq1 : 1 < |qTilde P x|) (hq2 : |qTilde P x| ≠ 2) :
    ∃ e0 : ℝ, ∀ n : ℕ, RunSystem (synDiv P x) P.natDegree (P.coeff 0) n (ustarSeq e0 x) := by
  obtain ⟨e0, he0, he1, m, hm⟩ := exists_int_eq_mul_one_sub hq1 hq2
  refine ⟨e0, fun n => ⟨fun i _ => ?_, ?_, fun i hi _ => ?_⟩⟩
  · rcases Nat.eq_zero_or_pos i with h | h
    · subst h; rw [ustarSeq_zero]; exact ⟨he0, he1⟩
    · rw [ustarSeq_of_ne e0 x (by omega)]
      constructor <;> linarith
  · exact ⟨P.eval 1 + P.coeff 0 - m, by rw [topRow_ustarSeq hd hroot, hm]; push_cast; ring⟩
  · exact ⟨P.eval 1, stdRow_ustarSeq hroot e0 hi⟩

/-- **(proved; Lemma U\*, irrational form).**  As `ustar_runSystem`, with `x` irrational in
place of `|q̃_0| ≠ 2`.  Paper proof: `not_irrational_of_abs_qTilde`. -/
theorem ustar_runSystem_of_irrational (hd : 1 ≤ P.natDegree) (hx1 : 1 / 2 < x) (hx2 : x < 1)
    (hroot : aeval x P = 0) (hq1 : 1 < |qTilde P x|) (hirr : Irrational x) :
    ∃ e0 : ℝ, ∀ n : ℕ, RunSystem (synDiv P x) P.natDegree (P.coeff 0) n (ustarSeq e0 x) :=
  ustar_runSystem hd hx1 hx2 hroot hq1 fun h2 =>
    not_irrational_of_abs_qTilde hroot (by linarith) (Or.inr h2) hirr

end UStar

/-! ## Lemma U\*, headline, and Corollary U1 -/

section Headline

variable {α : ℝ} {P : ℤ[X]}

/-- **(proved; Lemma U\*, headline, conditional on Weyl).**  Let `α > 2` with `x = xOf α` a
root of a monic irreducible `P ∈ ℤ[t]` of degree `≥ 2` and `|q̃_0| > 1`.  Then, under
`WeylEquidistributionMulti`, for every `n` infinitely many positive even `u` are followed by `n`
odd iterates.  Paper proof: for `n ≥ d`, `ustar_runSystem_of_irrational`
(`irrational_of_irreducible`, `xOf_mem`) feeds `runCriterion_of_weyl`; for `n < d`, the set for
`d` is contained in the set for `n`. -/
theorem ustar_infinite_runs_of_weyl (hW : WeylEquidistributionMulti) (hα : 2 < α)
    (hP : P.Monic) (hirr : Irreducible P) (hd : 2 ≤ P.natDegree) (hroot : aeval (xOf α) P = 0)
    (hq : 1 < |qTilde P (xOf α)|) (n : ℕ) :
    {u : ℤ | 0 < u ∧ u % 2 = 0 ∧ ∀ j ∈ Finset.Icc 1 n, (wy α)^[j] u % 2 = 1}.Infinite := by
  obtain ⟨hx1, hx2⟩ := xOf_mem hα
  obtain ⟨e0, he0⟩ := ustar_runSystem_of_irrational (by omega) hx1 hx2 hroot hq
    (irrational_of_irreducible hP hirr hd hroot)
  have key : ∀ n, P.natDegree ≤ n →
      {u : ℤ | 0 < u ∧ u % 2 = 0 ∧ ∀ j ∈ Finset.Icc 1 n, (wy α)^[j] u % 2 = 1}.Infinite :=
    fun n hn => runCriterion_of_weyl hW α P hα hP hirr hd hroot n hn ⟨_, he0 n⟩
  rcases le_total P.natDegree n with h | h
  · exact key n h
  · refine (key _ le_rfl).mono ?_
    rintro u ⟨h0, h2, h3⟩
    exact ⟨h0, h2, fun j hj => h3 j
      (Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hj).1, (Finset.mem_Icc.1 hj).2.trans h⟩)⟩

/-- **(proved; Corollary U1, first half).**  Under `WeylEquidistributionMulti`, bounded
runs force `|q̃_0| < 1`.  Paper proof: if `|q̃_0| > 1`, `ustar_infinite_runs_of_weyl` at
`n = J + 1` contradicts `BoundedRuns` (that set is finite); `|q̃_0| = 1` is excluded by
`not_irrational_of_abs_qTilde` and `irrational_of_irreducible`. -/
theorem abs_qTilde_lt_one_of_boundedRuns (hW : WeylEquidistributionMulti) (hα : 2 < α)
    (hP : P.Monic) (hirr : Irreducible P) (hd : 2 ≤ P.natDegree) (hroot : aeval (xOf α) P = 0)
    (hB : BoundedRuns α) : |qTilde P (xOf α)| < 1 := by
  by_contra hge
  rw [not_lt] at hge
  have hx := xOf_mem hα
  have hq1 : 1 < |qTilde P (xOf α)| := lt_of_le_of_ne hge fun h =>
    not_irrational_of_abs_qTilde hroot (ne_of_gt (by linarith [hx.1])) (Or.inl h.symm)
      (irrational_of_irreducible hP hirr hd hroot)
  obtain ⟨J, hJ⟩ := hB
  exact (ustar_infinite_runs_of_weyl hW hα hP hirr hd hroot hq1 (J + 1)) hJ

/-- **(proved; Corollary U1, the arithmetic).**  For a root `x > 1/2` of `P` with
`a_0 ≠ 0`, `|q̃_0| < 1` gives `x < |a_0|/(2|a_0| − 1)`.  Paper proof: `qTilde_eq` gives
`|a_0|(2x − 1) < x`, i.e. `x(2|a_0| − 1) < |a_0|`, and `2|a_0| − 1 ≥ 1`. -/
theorem lt_of_abs_qTilde_lt_one {x : ℝ} (hroot : aeval x P = 0) (hx1 : 1 / 2 < x)
    (ha0 : P.coeff 0 ≠ 0) (hq : |qTilde P x| < 1) :
    x < |(P.coeff 0 : ℝ)| / (2 * |(P.coeff 0 : ℝ)| - 1) := by
  have ha : 1 ≤ |(P.coeff 0 : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs ha0
  rw [qTilde_eq hroot (ne_of_gt (by linarith)), abs_div, abs_mul,
    abs_of_pos (by linarith : (0 : ℝ) < 2 * x - 1), abs_of_pos (by linarith : (0 : ℝ) < x),
    div_lt_one (by linarith)] at hq
  rw [lt_div_iff₀ (by linarith)]
  nlinarith

/-- **(proved; Corollary U1, contrapositive form).**  Under `WeylEquidistributionMulti`, if
`W_α` has bounded runs (`α > 2`, `x = xOf α` a root of a monic irreducible `P` of degree
`≥ 2`), then `x < |a_0|/(2|a_0| − 1) = 1/2 + 1/(2(2|a_0| − 1))`.  Paper proof:
`abs_qTilde_lt_one_of_boundedRuns`, `lt_of_abs_qTilde_lt_one`, `a_0 ≠ 0` by irreducibility. -/
theorem xOf_lt_of_boundedRuns (hW : WeylEquidistributionMulti) (hα : 2 < α) (hP : P.Monic)
    (hirr : Irreducible P) (hd : 2 ≤ P.natDegree) (hroot : aeval (xOf α) P = 0)
    (hB : BoundedRuns α) :
    xOf α < |(P.coeff 0 : ℝ)| / (2 * |(P.coeff 0 : ℝ)| - 1) :=
  lt_of_abs_qTilde_lt_one hroot (xOf_mem hα).1 (coeff_zero_ne_zero_of_irreducible hirr hd)
    (abs_qTilde_lt_one_of_boundedRuns hW hα hP hirr hd hroot hB)

end Headline

/-! ## Lemma H½ and Corollary U2 -/

section HalfPoint

variable {P : ℤ[X]} {x : ℝ}

/-- **(proved; Lemma H½, the half-point identity).**  Let `x` be a root of a monic
`P ∈ ℤ[t]` with `a_0 ≠ 0`, and `x_s` the other complex roots (the roots of `P` over `ℂ` with
one copy of `x` removed).  Then `q̃_0·2^{d−1}·∏_s(1 − 1/(2x_s)) = 2^dP(1/2)`.  Paper proof: as
in `two_mul_sub_one_gt`, `P = (t − x)∏_s(t − x_s)` over `ℂ`.  At `t = 0`:
`a_0 = −x·∏(−x_s)`, so (`qTilde_eq`, `x ≠ 0` since `a_0 ≠ 0`) `q̃_0 = (1 − 2x)∏(−x_s)`.  At
`t = 1/2`: `P(1/2) = (1/2 − x)∏(1/2 − x_s)` and `1/2 − x_s = (−x_s)(1 − 1/(2x_s))` (`x_s ≠ 0`
since `a_0 ≠ 0`), so `q̃_0∏(1 − 1/(2x_s)) = 2P(1/2)`; multiply by `2^{d−1}` (`d ≥ 1`, as `P`
has a root). -/
theorem qTilde_mul_prod_eq (hP : P.Monic) (hroot : aeval x P = 0) (ha0 : P.coeff 0 ≠ 0) :
    (qTilde P x : ℂ) * 2 ^ (P.natDegree - 1) *
        (((P.map (Int.castRingHom ℂ)).roots.erase (x : ℂ)).map fun s => 1 - 1 / (2 * s)).prod =
      ((2 ^ P.natDegree * aeval (1 / 2 : ℝ) P : ℝ) : ℂ) := by
  set Pc := P.map (Int.castRingHom ℂ) with hPcdef
  set S := Pc.roots.erase (x : ℂ) with hSdef
  have hPc : Pc.Monic := hP.map _
  have hcard : Multiset.card Pc.roots = Pc.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hfac := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hPc hcard
  have hx : (x : ℂ) ∈ Pc.roots := by
    rw [mem_roots hPc.ne_zero, IsRoot.def, hPcdef, eval_ofReal_map, hroot, Complex.ofReal_zero]
  have hroots : Pc.roots = (x : ℂ) ::ₘ S := (Multiset.cons_erase hx).symm
  have hev : ∀ c : ℂ, eval c Pc = (c - x) * (S.map fun s => c - s).prod := by
    intro c
    conv_lhs => rw [← hfac, hroots]
    rw [Multiset.map_cons, Multiset.prod_cons, eval_mul, eval_multiset_prod, Multiset.map_map]
    simp
  have e3 : eval (0 : ℂ) Pc = ((P.coeff 0 : ℝ) : ℂ) := by
    rw [← coeff_zero_eq_eval_zero, hPcdef, coeff_map]; simp
  have e1 : eval (1 / 2 : ℂ) Pc = ((aeval (1 / 2 : ℝ) P : ℝ) : ℂ) := by
    rw [← eval_ofReal_map]; push_cast; rfl
  have hx0 : x ≠ 0 := by
    rintro rfl
    have := coeff_zero_eq_synDiv hroot
    rw [zero_mul, neg_zero] at this
    exact ha0 (by exact_mod_cast this)
  have hS0 : ∀ s ∈ S, s ≠ 0 := by
    rintro s hs rfl
    have hmem : (0 : ℂ) ∈ Pc.roots := Multiset.mem_of_mem_erase hs
    rw [mem_roots hPc.ne_zero, IsRoot.def, e3] at hmem
    exact ha0 (by exact_mod_cast hmem)
  have hd : 1 ≤ P.natDegree := by
    by_contra h
    have : P = 1 := hP.natDegree_eq_zero.1 (by omega)
    rw [this, map_one] at hroot; exact one_ne_zero hroot
  have hsplit : (S.map fun s => (1 / 2 : ℂ) - s).prod =
      (S.map fun s => (0 : ℂ) - s).prod * (S.map fun s => 1 - 1 / (2 * s)).prod := by
    rw [← Multiset.prod_map_mul]
    refine congrArg _ (Multiset.map_congr rfl fun s hs => ?_)
    have := hS0 s hs
    field_simp
    ring
  have h0 := hev 0
  have hh := hev (1 / 2)
  rw [e3] at h0
  rw [e1, hsplit] at hh
  rw [qTilde_eq hroot hx0]
  obtain ⟨k, hk⟩ : ∃ k, P.natDegree = k + 1 := ⟨P.natDegree - 1, by omega⟩
  rw [hk, Nat.add_sub_cancel, Complex.ofReal_mul, hh, Complex.ofReal_div, Complex.ofReal_mul, h0]
  have : (x : ℂ) ≠ 0 := by exact_mod_cast hx0
  push_cast
  field_simp
  ring

/-- `‖∏ f(s)‖ = ∏‖f(s)‖` over a multiset. -/
theorem norm_multiset_prod_map (S : Multiset ℂ) (f : ℂ → ℂ) :
    ‖(S.map f).prod‖ = (S.map fun s => ‖f s‖).prod := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih => simp [ih]

/-- `‖1 − 1/(2s)‖ < 3/2` when `‖s‖ > 1`. -/
theorem norm_one_sub_inv_lt {s : ℂ} (hs : 1 < ‖s‖) : ‖1 - 1 / (2 * s)‖ < 3 / 2 := by
  have hs0 : 0 < ‖s‖ := by linarith
  have h : ‖1 / (2 * s)‖ = 1 / (2 * ‖s‖) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_two]
  have h2 : 1 / (2 * ‖s‖) < 1 / 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
  calc ‖1 - 1 / (2 * s)‖ ≤ ‖(1 : ℂ)‖ + ‖1 / (2 * s)‖ := norm_sub_le _ _
    _ < 3 / 2 := by rw [norm_one, h]; linarith

/-- `∏‖1 − 1/(2s)‖ ≤ (3/2)^{#S}` when every `‖s‖ > 1`. -/
theorem prod_norm_one_sub_inv_le (S : Multiset ℂ) (hS : ∀ s ∈ S, 1 < ‖s‖) :
    (S.map fun s => ‖1 - 1 / (2 * s)‖).prod ≤ (3 / 2) ^ Multiset.card S := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    have ha := norm_one_sub_inv_lt (hS a (Multiset.mem_cons_self a S))
    have ih' := ih fun s hs => hS s (Multiset.mem_cons_of_mem hs)
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ]
    rw [mul_comm _ (3 / 2 : ℝ)]
    exact mul_le_mul ha.le ih' (Multiset.prod_nonneg fun y hy => by
      obtain ⟨s, _, rfl⟩ := Multiset.mem_map.1 hy; exact norm_nonneg _) (by norm_num)

/-- The strict form for a nonempty multiset. -/
theorem prod_norm_one_sub_inv_lt (S : Multiset ℂ) (hS : ∀ s ∈ S, 1 < ‖s‖) (hne : S ≠ 0) :
    (S.map fun s => ‖1 - 1 / (2 * s)‖).prod < (3 / 2) ^ Multiset.card S := by
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hne
  obtain ⟨T, rfl⟩ := Multiset.exists_cons_of_mem ha
  have ha' := norm_one_sub_inv_lt (hS a (Multiset.mem_cons_self a T))
  have hT := prod_norm_one_sub_inv_le T fun s hs => hS s (Multiset.mem_cons_of_mem hs)
  simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ]
  rw [mul_comm _ (3 / 2 : ℝ)]
  calc ‖1 - 1 / (2 * a)‖ * (T.map fun s => ‖1 - 1 / (2 * s)‖).prod
      ≤ ‖1 - 1 / (2 * a)‖ * (3 / 2) ^ Multiset.card T :=
        mul_le_mul_of_nonneg_left hT (norm_nonneg _)
    _ < 3 / 2 * (3 / 2) ^ Multiset.card T := mul_lt_mul_of_pos_right ha' (by positivity)

/-- Norms in Lemma H½: `|2^dP(1/2)| = |q̃_0|·2^{d−1}·∏‖1 − 1/(2x_s)‖`. -/
theorem abs_two_pow_aeval_half_eq (hP : P.Monic) (hroot : aeval x P = 0)
    (ha0 : P.coeff 0 ≠ 0) :
    |(2 : ℝ) ^ P.natDegree * aeval (1 / 2 : ℝ) P| = |qTilde P x| * 2 ^ (P.natDegree - 1) *
      (((P.map (Int.castRingHom ℂ)).roots.erase (x : ℂ)).map
        fun s => ‖1 - 1 / (2 * s)‖).prod := by
  have h := congrArg norm (qTilde_mul_prod_eq hP hroot ha0)
  rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_mul, norm_multiset_prod_map,
    Complex.norm_real, Real.norm_eq_abs, norm_pow, Complex.norm_two] at h
  exact h.symm

/-- Under the conjugate hypothesis, `a_0 ≠ 0` (else `0` is another root) and the other roots
number `d − 1`. -/
theorem coeff_zero_ne_zero_of_conj (hP : P.Monic) (hx1 : 1 / 2 < x)
    (hconj : ∀ z ∈ (P.map (Int.castRingHom ℂ)).roots.erase (x : ℂ), 1 < ‖z‖) :
    P.coeff 0 ≠ 0 := by
  have hx0 : (0 : ℂ) ≠ (x : ℂ) := fun h' => by
    have := congrArg Complex.re h'
    simp at this
    linarith
  intro h0
  have hmem : (0 : ℂ) ∈ (P.map (Int.castRingHom ℂ)).roots.erase (x : ℂ) := by
    rw [Multiset.mem_erase_of_ne hx0, mem_roots (hP.map _).ne_zero, IsRoot.def,
      ← coeff_zero_eq_eval_zero, coeff_map, h0, map_zero]
  have := hconj 0 hmem
  rw [norm_zero] at this
  linarith

/-- The other roots number `d − 1`. -/
theorem card_roots_erase (hP : P.Monic) (hroot : aeval x P = 0) :
    Multiset.card ((P.map (Int.castRingHom ℂ)).roots.erase (x : ℂ)) = P.natDegree - 1 := by
  have hPc := hP.map (Int.castRingHom ℂ)
  have hx : (x : ℂ) ∈ (P.map (Int.castRingHom ℂ)).roots := by
    rw [mem_roots hPc.ne_zero, IsRoot.def, eval_ofReal_map, hroot, Complex.ofReal_zero]
  rw [Multiset.card_erase_of_mem hx, IsAlgClosed.card_roots_eq_natDegree,
    hP.natDegree_map]
  rfl

/-- **(proved; Corollary U2, upper bound, automaton form).**  Under
`two_mul_sub_one_gt`'s hypotheses (every other conjugate `‖x_s‖ > 1`), `|q̃_0| < 1` gives
`|2^dP(1/2)| < 3^{d−1}`.  Paper proof: `qTilde_mul_prod_eq` (`a_0 ≠ 0` as in
`run_bound_B2`); `‖1 − 1/(2x_s)‖ ≤ 1 + 1/(2‖x_s‖) < 3/2` (as in `prod_norm_half_sub_le`), so
`|N| ≤ |q̃_0|·2^{d−1}(3/2)^{d−1} < 3^{d−1}`. -/
theorem abs_two_pow_aeval_half_lt (hP : P.Monic) (hd : 2 ≤ P.natDegree) (hx1 : 1 / 2 < x)
    (hx2 : x < 1) (hroot : aeval x P = 0)
    (hconj : ∀ z ∈ (P.map (Int.castRingHom ℂ)).roots.erase (x : ℂ), 1 < ‖z‖)
    (hq : |qTilde P x| < 1) :
    |(2 : ℝ) ^ P.natDegree * aeval (1 / 2 : ℝ) P| < 3 ^ (P.natDegree - 1) := by
  -- `hd` and `hx2` are not needed; they keep the ratified statement parallel to B2's.
  have _ : 2 ≤ P.natDegree ∧ x < 1 := ⟨hd, hx2⟩
  have ha0 := coeff_zero_ne_zero_of_conj hP hx1 hconj
  have hR := prod_norm_one_sub_inv_le _ hconj
  have hR0 : 0 ≤ (((P.map (Int.castRingHom ℂ)).roots.erase (x : ℂ)).map
      fun s => ‖1 - 1 / (2 * s)‖).prod := Multiset.prod_nonneg fun y hy => by
    obtain ⟨s, _, rfl⟩ := Multiset.mem_map.1 hy; exact norm_nonneg _
  rw [card_roots_erase hP hroot] at hR
  rw [abs_two_pow_aeval_half_eq hP hroot ha0,
    show (3 : ℝ) = 2 * (3 / 2) by norm_num, mul_pow]
  generalize (((P.map (Int.castRingHom ℂ)).roots.erase (x : ℂ)).map
      fun s => ‖1 - 1 / (2 * s)‖).prod = R at hR hR0 ⊢
  have hA := abs_nonneg (qTilde P x)
  have hB : (0 : ℝ) < 2 ^ (P.natDegree - 1) := by positivity
  have hC : (0 : ℝ) < (3 / 2) ^ (P.natDegree - 1) := by positivity
  generalize |qTilde P x| = A at hA hq ⊢
  generalize (2 : ℝ) ^ (P.natDegree - 1) = B at hB ⊢
  generalize (3 / 2 : ℝ) ^ (P.natDegree - 1) = C at hC hR ⊢
  nlinarith [mul_le_mul_of_nonneg_left hR (mul_nonneg hA hB.le), mul_pos hB hC]

/-- **(proved; Corollary U2, lower bound).**  Under the same conjugate hypothesis,
`|q̃_0| > 3^{1−d}`.  Paper proof: `1 ≤ |N|` (`abs_aeval_half_ge`), and by
`qTilde_mul_prod_eq` with each `‖1 − 1/(2x_s)‖ < 3/2` (the product is over `d − 1 ≥ 1`
factors), `|N| < |q̃_0|·3^{d−1}`. -/
theorem one_lt_three_pow_mul_abs_qTilde (hP : P.Monic) (hd : 2 ≤ P.natDegree)
    (hx1 : 1 / 2 < x) (hx2 : x < 1) (hroot : aeval x P = 0)
    (hconj : ∀ z ∈ (P.map (Int.castRingHom ℂ)).roots.erase (x : ℂ), 1 < ‖z‖) :
    1 < 3 ^ (P.natDegree - 1) * |qTilde P x| := by
  have ha0 := coeff_zero_ne_zero_of_conj hP hx1 hconj
  have hcard := card_roots_erase hP hroot
  have hne : (P.map (Int.castRingHom ℂ)).roots.erase (x : ℂ) ≠ 0 := by
    intro h; rw [h, Multiset.card_zero] at hcard; omega
  have hR := prod_norm_one_sub_inv_lt _ hconj hne
  rw [hcard] at hR
  have hN := abs_two_pow_aeval_half_eq hP hroot ha0
  obtain ⟨m, hodd, hm⟩ := two_pow_mul_aeval_half_odd hP
  have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs (by rintro rfl; simp at hodd)
  rw [hm] at hN
  rw [show (3 : ℝ) = 2 * (3 / 2) by norm_num, mul_pow]
  generalize (((P.map (Int.castRingHom ℂ)).roots.erase (x : ℂ)).map
      fun s => ‖1 - 1 / (2 * s)‖).prod = R at hR hN
  have hA := abs_nonneg (qTilde P x)
  have hB : (0 : ℝ) < 2 ^ (P.natDegree - 1) := by positivity
  generalize |qTilde P x| = A at hA hN ⊢
  generalize (2 : ℝ) ^ (P.natDegree - 1) = B at hB hN ⊢
  generalize (3 / 2 : ℝ) ^ (P.natDegree - 1) = C at hR ⊢
  rw [hN] at hm1
  have hA0 : 0 < A := by
    rcases hA.lt_or_eq with h | h
    · exact h
    · rw [← h] at hm1; simp at hm1; linarith
  nlinarith [mul_lt_mul_of_pos_left hR (mul_pos hA0 hB)]

/-- **(proved; Corollary U2, headline form).**  Under `WeylEquidistributionMulti`, if
`W_α` has bounded runs (`α > 2`, `x = xOf α` a root of a monic irreducible `P` of degree
`≥ 2`), then `1 ≤ |2^dP(1/2)| < 3^{d−1}`.  Paper proof: the lower bound is
`abs_aeval_half_ge`.  For the upper bound, `hconj` holds: a `z ∈ roots.erase x` is a root with
`z ≠ x` (irreducible over `ℚ` in characteristic `0` is separable, so the roots are `Nodup`:
`Polynomial.nodup_roots`, `Irreducible.separable`), and `‖z‖ ≤ 1` would contradict
`BoundedRuns` via `n3_infinite_runs_of_weyl` at `n = J + 1`.  Then
`abs_qTilde_lt_one_of_boundedRuns` and `abs_two_pow_aeval_half_lt`. -/
theorem u2_of_boundedRuns {α : ℝ} (hW : WeylEquidistributionMulti) (hα : 2 < α)
    (hP : P.Monic) (hirr : Irreducible P) (hd : 2 ≤ P.natDegree) (hroot : aeval (xOf α) P = 0)
    (hB : BoundedRuns α) :
    1 ≤ |(2 : ℝ) ^ P.natDegree * aeval (1 / 2 : ℝ) P| ∧
      |(2 : ℝ) ^ P.natDegree * aeval (1 / 2 : ℝ) P| < 3 ^ (P.natDegree - 1) := by
  obtain ⟨hx1, hx2⟩ := xOf_mem hα
  refine ⟨?_, ?_⟩
  · obtain ⟨m, hodd, hm⟩ := two_pow_mul_aeval_half_odd hP
    rw [hm, ← Int.cast_abs]; exact_mod_cast Int.one_le_abs (by rintro rfl; simp at hodd)
  refine abs_two_pow_aeval_half_lt hP hd hx1 hx2 hroot ?_
    (abs_qTilde_lt_one_of_boundedRuns hW hα hP hirr hd hroot hB)
  have hnodup : (P.map (Int.castRingHom ℂ)).roots.Nodup := by
    have hirrQ : Irreducible (P.map (algebraMap ℤ ℚ)) :=
      (hP.irreducible_iff_irreducible_map_fraction_map).1 hirr
    have hsep := hirrQ.separable.map (f := algebraMap ℚ ℂ)
    rw [Polynomial.map_map, show (algebraMap ℚ ℂ).comp (algebraMap ℤ ℚ) = Int.castRingHom ℂ
      from RingHom.ext_int _ _] at hsep
    exact nodup_roots hsep
  intro z hz
  rw [hnodup.mem_erase_iff] at hz
  obtain ⟨hzx, hzr⟩ := hz
  have hza : aeval z P = 0 := by
    rw [mem_roots (hP.map _).ne_zero, IsRoot.def, ← algebraMap_int_eq,
      eval_map_algebraMap] at hzr
    exact hzr
  by_contra hz1
  obtain ⟨J, hJ⟩ := hB
  exact n3_infinite_runs_of_weyl hW hα hP hirr hd hroot hza hzx (not_lt.1 hz1) (J + 1) hJ

end HalfPoint

/-! ## Lemma SG: slide to the grid -/

section SlideGrid

variable {q : ℕ → ℝ} {d : ℕ}

/-- **(proved; Lemma SG, automaton form).**  Let `γ` be a real sequence with every
standard row `R_i(γ)` (`i ≥ 0`) an integer and `γ_i ∈ [μ, 1/2 − μ]` for `i ≥ 1`; let `c` be
homogeneous (`R_i(c) = 0` for all `i`) with `c_0 = 1` and `|c_i| ≤ ρ^i` (`ρ ≥ 1`); let `g` lie on
the grid `2a_0g ∈ ℤ` with `g ∈ (0, 1/2)`, and `κ = g − γ_0` with `|κ|ρ^{n−1} < μ`.  Then
`ε_i = γ_i + κc_i` solves the run system of length `n`.  Paper proof: `stdRow_add_smul`
gives `R_i(ε) = R_i(γ)`; `ε_0 = γ_0 + κ = g`; the top row is `R_0(γ) + 2a_0g ∈ ℤ`
(`topRow_eq_stdRow_add`); for `1 ≤ i < n`, `|κc_i| ≤ |κ|ρ^i ≤ |κ|ρ^{n−1} < μ`
(`pow_le_pow_right₀`). -/
theorem sg_runSystem (hd : 1 ≤ d) (a0 : ℤ) {γ : ℕ → ℝ} (hrow : ∀ i, ∃ m : ℤ, stdRow q d γ i = m)
    {μ : ℝ} (hγ : ∀ i, 1 ≤ i → μ ≤ γ i ∧ γ i ≤ 1 / 2 - μ) {c : ℕ → ℝ}
    (hc : ∀ i, stdRow q d c i = 0) (hc0 : c 0 = 1) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hcρ : ∀ i, |c i| ≤ ρ ^ i) {g : ℝ} (hg : ∃ k : ℤ, 2 * a0 * g = k) (hg0 : 0 < g)
    (hg1 : g < 1 / 2) {n : ℕ} (hκ : |g - γ 0| * ρ ^ (n - 1) < μ) :
    RunSystem q d a0 n (fun i => γ i + (g - γ 0) * c i) := by
  obtain ⟨k, hk⟩ := hg
  obtain ⟨m0, hm0⟩ := hrow 0
  have hrows : ∀ i, stdRow q d (fun i => γ i + (g - γ 0) * c i) i = stdRow q d γ i := fun i => by
    rw [stdRow_add_smul, hc, mul_zero, add_zero]
  refine ⟨fun i hi => ?_, ⟨m0 + k, ?_⟩, fun i _ _ => ?_⟩
  · rcases Nat.eq_zero_or_pos i with h | h
    · subst h; simp only [hc0, mul_one]; constructor <;> linarith
    · have hci : |(g - γ 0) * c i| < μ := by
        rw [abs_mul]
        calc |g - γ 0| * |c i| ≤ |g - γ 0| * ρ ^ (n - 1) :=
              mul_le_mul_of_nonneg_left ((hcρ i).trans (pow_le_pow_right₀ hρ (by omega)))
                (abs_nonneg _)
          _ < μ := hκ
      obtain ⟨hl, hr⟩ := abs_lt.1 hci
      obtain ⟨h1, h2⟩ := hγ i h
      constructor <;> linarith
  · rw [topRow_eq_stdRow_add hd, hrows, hm0]
    simp only [hc0, mul_one]
    push_cast
    linear_combination hk
  · obtain ⟨m, hm⟩ := hrow i
    exact ⟨m, by rw [hrows, hm]⟩

/-- **(proved; Lemma SG with a conjugate direction).**  For another complex root
`z ≠ x` of `P` with `‖z‖ ≥ 1`, `sg_runSystem` applies with `c_i = Re(z^i)` and `ρ = ‖z‖`; so a
conjugate with `‖z‖` near `1` buys runs of length about `log(μ/|κ|)/log‖z‖`.  Paper proof:
`stdRow_re_pow` (homogeneity), `Re(z^0) = 1`, `|Re(z^i)| ≤ ‖z‖^i`
(`Complex.abs_re_le_norm`, `norm_pow`). -/
theorem sg_runSystem_conj {P : ℤ[X]} {x : ℝ} (hd : 1 ≤ P.natDegree) (hroot : aeval x P = 0)
    {z : ℂ} (hz : aeval z P = 0) (hzx : z ≠ (x : ℂ)) (hz1 : 1 ≤ ‖z‖) {γ : ℕ → ℝ}
    (hrow : ∀ i, ∃ m : ℤ, stdRow (synDiv P x) P.natDegree γ i = m) {μ : ℝ}
    (hγ : ∀ i, 1 ≤ i → μ ≤ γ i ∧ γ i ≤ 1 / 2 - μ) {g : ℝ}
    (hg : ∃ k : ℤ, 2 * P.coeff 0 * g = k) (hg0 : 0 < g) (hg1 : g < 1 / 2) {n : ℕ}
    (hκ : |g - γ 0| * ‖z‖ ^ (n - 1) < μ) :
    RunSystem (synDiv P x) P.natDegree (P.coeff 0) n
      (fun i => γ i + (g - γ 0) * (z ^ i).re) :=
  sg_runSystem hd (P.coeff 0) hrow hγ (stdRow_re_pow hroot hz hzx) (by simp) hz1
    (fun i => by rw [← norm_pow]; exact Complex.abs_re_le_norm _) hg hg0 hg1 hκ

end SlideGrid

/-! ## Lemma O∞: the G-shaped limit -/

section OInf

/-- **(proved).**  For `E ∈ ℤ[t]` with `E(0) = 0`, `c_0 = synDiv E (1/2) 0 = 2E(1/2)`.
Paper proof: `E(1/2) = Σ_{1 ≤ j ≤ d} e_j2^{−j} = (1/2)Σ_{j ∈ (0, d]} e_j2^{−(j−1)}`
(`aeval_eq_sum_range`, `Finset.sum_range_succ'` to drop `j = 0`). -/
theorem synDiv_half_zero {E : ℤ[X]} (hE0 : E.coeff 0 = 0) :
    synDiv E (1 / 2) 0 = 2 * aeval (1 / 2 : ℝ) E := by
  rw [aeval_eq_sum_range, Finset.sum_range_succ', hE0, zero_smul, add_zero, Finset.mul_sum]
  unfold synDiv
  rw [show Finset.Ioc 0 E.natDegree = Finset.Ico 1 (E.natDegree + 1) by ext j; simp; omega,
    Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [zsmul_eq_mul, show 1 + k - 0 - 1 = k by omega, show 1 + k = k + 1 by omega, pow_succ]
  ring

/-- **(proved; Lemma O∞, the limit Theorem O).**  Let `E = t^d + Σ_{k=1}^{d−1}e_kt^k`
(monic, `E(0) = 0`) and `c_k = synDiv E (1/2) k = Σ_{j>k} e_j2^{−(j−k−1)}` (`c_0 = 2E(1/2)` by
`synDiv_half_zero`).  If every `c_k ≥ 0` (`k < d`) and `Σ_{k<d} c_k ≤ 2`, then `E = t^d`.  Paper
proof: `m_k := 2^{d−k−1}c_k = Σ_{k<j≤d} e_j2^{d−j}` is an odd integer (the `j = d` term is `1`,
the rest even, as in `two_pow_mul_aeval_half_odd`), so `c_k ≥ 0` forces `m_k ≥ 1`.  Then
`Σ_{k<d} 2^km_k = 2^{d−1}Σc_k ≤ 2^d = 1 + Σ_{k<d}2^k`, so `Σ 2^k(m_k − 1) ≤ 1` with every
`m_k − 1` even and `≥ 0`: all `m_k = 1`.  Finally `m_{k−1} − m_k = e_k2^{d−k} = 0` for
`1 ≤ k < d`, and `Polynomial.ext` (`coeff 0 = 0`, `coeff d = 1`, zero above `d`). -/
theorem oInf {E : ℤ[X]} (hE : E.Monic) (hE0 : E.coeff 0 = 0)
    (hc : ∀ k < E.natDegree, 0 ≤ synDiv E (1 / 2) k)
    (hsum : ∑ k ∈ Finset.range E.natDegree, synDiv E (1 / 2) k ≤ 2) :
    E = X ^ E.natDegree := by
  obtain ⟨n, hn⟩ : ∃ n, E.natDegree = n + 1 := by
    refine ⟨E.natDegree - 1, ?_⟩
    by_contra h
    have : E = 1 := hE.natDegree_eq_zero.1 (by omega)
    rw [this, coeff_one_zero] at hE0
    exact one_ne_zero hE0
  have hlead : E.coeff (n + 1) = 1 := by rw [← hn]; exact hE.coeff_natDegree
  -- `m_k = Σ_{k<j≤d} e_j2^{d−j} = 2^{d−k−1}c_k`
  set m : ℕ → ℤ := fun k => ∑ j ∈ Finset.Ioc k (n + 1), E.coeff j * 2 ^ (n + 1 - j) with hmdef
  have hm_eq : ∀ k, k ≤ n → (2 : ℝ) ^ (n - k) * synDiv E (1 / 2) k = m k := by
    intro k hk
    rw [hmdef, synDiv, hn, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun j hj => ?_
    obtain ⟨hj1, hj2⟩ := Finset.mem_Ioc.1 hj
    have h2 : (2 : ℝ) ^ (n - k) = 2 ^ (n + 1 - j) * 2 ^ (j - k - 1) := by
      rw [← pow_add]; congr 1; omega
    have h3 : (2 : ℝ) ^ (j - k - 1) * (1 / 2) ^ (j - k - 1) = 1 := by
      rw [← mul_pow]; norm_num
    rw [h2]
    linear_combination (2 ^ (n + 1 - j) * (E.coeff j : ℝ)) * h3
  have hm_odd : ∀ k, k ≤ n → Odd (m k) := by
    intro k hk
    rw [hmdef]
    dsimp only
    rw [Finset.sum_Ioc_succ_top hk, Nat.sub_self, pow_zero, mul_one, hlead]
    refine ⟨∑ j ∈ Finset.Ioc k n, E.coeff j * 2 ^ (n - j), ?_⟩
    rw [Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [show n + 1 - j = (n - j) + 1 by have := (Finset.mem_Ioc.1 hj).2; omega, pow_succ]
    ring
  have hm_pos : ∀ k, k ≤ n → 1 ≤ m k := by
    intro k hk
    have h0 : (0 : ℝ) ≤ m k := by
      rw [← hm_eq k hk]; exact mul_nonneg (by positivity) (hc k (by omega))
    have h0' : 0 ≤ m k := by exact_mod_cast h0
    obtain ⟨r, hr⟩ := hm_odd k hk
    omega
  -- `Σ_{k<d} 2^km_k = 2^{d−1}Σc_k ≤ 2^d`
  have hsumm : ∑ k ∈ Finset.range (n + 1), 2 ^ k * m k ≤ 2 ^ (n + 1) := by
    have e : ((∑ k ∈ Finset.range (n + 1), 2 ^ k * m k : ℤ) : ℝ) =
        (2 : ℝ) ^ n * ∑ k ∈ Finset.range (n + 1), synDiv E (1 / 2) k := by
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk := Finset.mem_range.1 hk
      rw [← hm_eq k (by omega), ← mul_assoc, ← pow_add, show k + (n - k) = n by omega]
    have h : ((∑ k ∈ Finset.range (n + 1), 2 ^ k * m k : ℤ) : ℝ) ≤ ((2 ^ (n + 1) : ℤ) : ℝ) := by
      rw [e]
      rw [hn] at hsum
      push_cast
      rw [pow_succ]
      nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) n]
    exact_mod_cast h
  have hgeom : ∀ N, ∑ k ∈ Finset.range N, (2 : ℤ) ^ k = 2 ^ N - 1 := by
    intro N
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  -- so every `m_k = 1`
  have hm1 : ∀ k, k ≤ n → m k = 1 := by
    intro k hk
    have hle : 2 ^ k * (m k - 1) ≤ ∑ j ∈ Finset.range (n + 1), 2 ^ j * (m j - 1) :=
      Finset.single_le_sum (f := fun j => 2 ^ j * (m j - 1))
        (fun j hj => mul_nonneg (by positivity)
          (by linarith [hm_pos j (by have := Finset.mem_range.1 hj; omega)]))
        (Finset.mem_range.2 (by omega))
    have htot : ∑ j ∈ Finset.range (n + 1), 2 ^ j * (m j - 1) ≤ 1 := by
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
      rw [hgeom]
      linarith
    have h2k : (1 : ℤ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    obtain ⟨r, hr⟩ := hm_odd k hk
    have := hm_pos k hk
    have hr0 : r ≤ 0 := by nlinarith
    omega
  -- `e_k2^{d−k} = m_{k−1} − m_k = 0`
  have hek : ∀ k, 1 ≤ k → k ≤ n → E.coeff k = 0 := by
    intro k hk1 hk2
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hsplit : m k' = E.coeff (k' + 1) * 2 ^ (n + 1 - (k' + 1)) + m (k' + 1) := by
      rw [hmdef]
      dsimp only
      rw [← Finset.sum_Ioc_consecutive _ (Nat.le_succ k') (by omega : k' + 1 ≤ n + 1),
        Nat.Ioc_succ_singleton, Finset.sum_singleton]
    rw [hm1 _ (by omega), hm1 _ hk2] at hsplit
    have h : E.coeff (k' + 1) * 2 ^ (n + 1 - (k' + 1)) = 0 := by linarith
    exact (mul_eq_zero.1 h).resolve_right (by positivity)
  ext j
  rw [coeff_X_pow, hn]
  rcases Nat.lt_trichotomy j (n + 1) with h | h | h
  · rw [if_neg (by omega)]
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0; exact hE0
    · exact hek j h0 (by omega)
  · rw [if_pos h, h, hlead]
  · rw [if_neg (by omega)]
    exact coeff_eq_zero_of_natDegree_lt (by omega)

end OInf

end CollatzMoonshot.WythoffUStar
