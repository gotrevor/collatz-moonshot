/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.WythoffAutomaton

/-!
# Bounded Wythoff runs force a Pisot-dual slope (Theorem N3, Lemma B2)

Research note `wythoff-pisot`, §1-§3, with the notation of `wythoff-classify` §1-§2 and of
`WythoffAutomaton`.  Let `x ∈ (1/2, 1)` be a root of a monic `P = t^d + ⋯ + a_0 ∈ ℤ[t]` and let
`q_k = synDiv P x k` be the coefficients of `Q(t) = P(t)/(t − x)` (`q_{d−1} = 1`,
`q̃_0 = q_0 + 2a_0`).

**The run system** (`RunSystem`, half-scale `ε = G/2` of the zonotope criterion of
`wythoff-classify` §1).  A vector `(ε_0, …, ε_{n−1}) ∈ (0, 1/2)^n` with
* the **top row** `T(ε) = q̃_0 ε_0 + Σ_{k=1}^{d−1} q_k ε_k ∈ ℤ` (`topRow`), and
* the **standard rows** `R_i(ε) = Σ_{k<d} q_k ε_{i+k} ∈ ℤ` for `1 ≤ i ≤ n − d` (`stdRow`).
By Theorem N (`WythoffAutomaton.first_step_eq_ceil`, `iterate_odd_iff_autoPhi`) plus the
uniformity of the fresh phases (`wythoff-classify` Theorem N4, **not in Lean**), runs of length
`≥ n` after an up-point occur with positive density iff the run system has a solution.  Two
identities: `T(ε) = R_0(ε) + 2a_0ε_0` (`topRow_eq_stdRow_add`), and adding a homogeneous sequence
(`R_i(c) = 0` for all `i`) changes no standard row (`stdRow_add_smul`).

**Lemma 1** (`sum_synDiv_mul_fixGamma`, `fixGamma_mem`).  `Q(1) = P(1)/(1 − x)`, so
`γ = (1 − x)/|P(1)|` (`fixGamma`) lies in `(0, 1/2)` when `P(1) ≠ 0`, and the constant sequence
`γ` has every standard row `Q(1)γ = ±1`: the later-step automaton always has a continuing fixed
point.

**Theorem N3** (`n3_runSystem`).  If some other complex root `z ≠ x` of `P` (monic, irreducible,
degree `≥ 2`) has `‖z‖ ≤ 1`, the run system has a solution for every `n`.  *Proof.*
1. *Direction* (`stdRow_re_pow`, `abs_re_pow_lt_one_of_norm_le`).  `c_i = Re(z^i)` is
   homogeneous (`Q(z) = 0`), `c_0 = 1`, and `|c_i| < 1` for `i ≥ 1`: if `‖z‖ < 1` trivially; if
   `‖z‖ = 1`, `|Re(z^i)| = 1` would make `z^{2i} = 1`, and no root of `P` is a root of unity since
   `P` has the root `x ∈ (0, 1)` (`pow_ne_one_of_irreducible`).
2. *Boundary sequence* (`boundarySeq`, `n3_boundary`).  `κ = −γ` if `γ ≤ 1/4`, else `1/2 − γ`;
   `ε°_i = γ + κc_i` has `ε°_0 ∈ {0, 1/2}`, `ε°_i ∈ (0, 1/2)` for `i ≥ 1`, every standard row
   `= Q(1)γ ∈ ℤ`, and top row `R_0 + 2a_0ε°_0 ∈ ℤ` since `2a_0ε°_0 ∈ {0, a_0}`.
3. *Perturbation* (`perturb`).  Move `ε_0` into `(0, 1/2)` by `σδ` and compensate the top row by
   `λb_i` on indices `≥ 1`, where `b` is homogeneous on indices `≥ 1` with
   `S_b = Σ_{k=1}^{d−1} q_k b_k ≠ 0`.  Here `b = c` itself works: `S_c = −q_0c_0 = −q_0 ≠ 0`
   (`q_0 = −a_0/x`, `a_0 ≠ 0` by irreducibility).  `n3_core` = steps 2 + 3 in pure real arithmetic.

**Headline** (`n3_infinite_runs`).  Conditional on the named prior-report hypothesis
`RunCriterion` (the sufficiency half of `wythoff-classify`'s zonotope criterion, whose
positive-density step N4 is not in Lean), for every `n` infinitely many positive even `u` are
followed by `n` odd iterates under `W_α`.

**Lemma B2** (`two_pow_mul_aeval_half_odd`, `two_mul_sub_one_gt`, `run_bound_B2`).
`2^d P(1/2)` is an odd integer, so `|P(1/2)| ≥ 2^{−d}`; if every other conjugate has `‖z‖ > 1`,
then `2x − 1 > 1/(2·3^{d−1}|a_0|)`, and a run bound `J` with `c_J = x^{J+1}/(2x − 1) > 1` gives
`2·3^{d−1}|a_0|·x^{J+1} > 1`.

Truth checks: `tmp/drafter-pisot/check.py` (gitignored; mpmath, exact Fractions, LP).
-/

namespace CollatzMoonshot.WythoffPisot

open CollatzMoonshot.WythoffGeneral CollatzMoonshot.WythoffAutomaton Polynomial Filter Topology

/-! ## Definitions -/

/-- The standard row `R_i(ε) = Σ_{k<d} q_k ε_{i+k}`. -/
noncomputable def stdRow (q : ℕ → ℝ) (d : ℕ) (ε : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ k ∈ Finset.range d, q k * ε (i + k)

/-- The top row `T(ε) = (q_0 + 2a_0) ε_0 + Σ_{1 ≤ k < d} q_k ε_k`. -/
noncomputable def topRow (q : ℕ → ℝ) (d : ℕ) (a0 : ℤ) (ε : ℕ → ℝ) : ℝ :=
  (q 0 + 2 * a0) * ε 0 + ∑ k ∈ Finset.Ico 1 d, q k * ε k

/-- The run system of length `n`: `ε_i ∈ (0, 1/2)` for `i < n`, the top row is an integer, and
the standard rows `R_i` with `1 ≤ i` and `i + d ≤ n` are integers. -/
def RunSystem (q : ℕ → ℝ) (d : ℕ) (a0 : ℤ) (n : ℕ) (ε : ℕ → ℝ) : Prop :=
  (∀ i < n, 0 < ε i ∧ ε i < 1 / 2) ∧ (∃ m : ℤ, topRow q d a0 ε = m) ∧
    ∀ i, 1 ≤ i → i + d ≤ n → ∃ m : ℤ, stdRow q d ε i = m

/-- Lemma 1's fixed point `γ = (1 − x)/|P(1)|`. -/
noncomputable def fixGamma (P : ℤ[X]) (x : ℝ) : ℝ :=
  (1 - x) / |((P.eval 1 : ℤ) : ℝ)|

/-- N3's boundary sequence `ε°_i = γ + κ c_i`, `κ = −γ` if `γ ≤ 1/4` and `κ = 1/2 − γ`
otherwise. -/
noncomputable def boundarySeq (γ : ℝ) (c : ℕ → ℝ) (i : ℕ) : ℝ :=
  γ + (if γ ≤ 1 / 4 then -γ else 1 / 2 - γ) * c i

/-! ## Row identities -/

section Rows

variable {q : ℕ → ℝ} {d : ℕ}

/-- **(proved).**  `T(ε) = R_0(ε) + 2a_0 ε_0` for `d ≥ 1`.  Paper proof:
`range d = {0} ∪ Ico 1 d` (`Finset.sum_range_eq_add_Ico`). -/
theorem topRow_eq_stdRow_add (hd : 1 ≤ d) (a0 : ℤ) (ε : ℕ → ℝ) :
    topRow q d a0 ε = stdRow q d ε 0 + 2 * a0 * ε 0 := by
  unfold topRow stdRow
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (a := 0) (b := d) (by omega)]
  simp only [zero_add]
  ring

/-- **(proved).**  Rows are linear: `R_i(ε + λb) = R_i(ε) + λR_i(b)`.  Paper proof:
distribute the finite sum. -/
theorem stdRow_add_smul (ε b : ℕ → ℝ) (lam : ℝ) (i : ℕ) :
    stdRow q d (fun j => ε j + lam * b j) i = stdRow q d ε i + lam * stdRow q d b i := by
  simp only [stdRow, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- **(proved).**  A constant sequence has every row `Q(1)γ`. -/
theorem stdRow_const (γ : ℝ) (i : ℕ) :
    stdRow q d (fun _ => γ) i = (∑ k ∈ Finset.range d, q k) * γ := by
  simp only [stdRow, Finset.sum_mul]

/-- **(proved).**  A solution of length `n'` restricts to every `n ≤ n'`. -/
theorem RunSystem.mono {a0 : ℤ} {n n' : ℕ} {ε : ℕ → ℝ} (h : RunSystem q d a0 n' ε)
    (hn : n ≤ n') : RunSystem q d a0 n ε :=
  ⟨fun i hi => h.1 i (by omega), h.2.1, fun i hi hin => h.2.2 i hi (by omega)⟩

end Rows

/-! ## Lemma 1: the fixed point -/

section Lemma1

variable {P : ℤ[X]} {x : ℝ}

/-- **(proved).**  `P(1) = (1 − x)·Q(1)` with `Q(1) = Σ_{k<d} q_k`.  Paper proof:
`WythoffAutomaton.sum_coeff_mul_eq_synDiv` with `w ≡ 1`, and
`P(1) = Σ_{j ≤ d} a_j` (`Polynomial.eval_eq_sum_range`, cast to `ℝ`). -/
theorem eval_one_eq_mul_sum_synDiv (hroot : aeval x P = 0) :
    ((P.eval 1 : ℤ) : ℝ) = (1 - x) * ∑ k ∈ Finset.range P.natDegree, synDiv P x k := by
  have h := sum_coeff_mul_eq_synDiv hroot (fun _ => (1 : ℝ))
  rw [eval_eq_sum_range]
  push_cast
  simp only [one_pow, mul_one] at h ⊢
  rw [h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- **(proved; Lemma 1, the row value).**  `Q(1)·γ = sign P(1)` (`= ±1` when
`P(1) ≠ 0`; both sides are `0` when `P(1) = 0`, since then `γ = 0` by Lean's `a/0 = 0`).
Paper proof: `Q(1)γ = Q(1)(1 − x)/|P(1)| = P(1)/|P(1)|` (`eval_one_eq_mul_sum_synDiv`). -/
theorem sum_synDiv_mul_fixGamma (hroot : aeval x P = 0) :
    (∑ k ∈ Finset.range P.natDegree, synDiv P x k) * fixGamma P x = ((P.eval 1).sign : ℝ) := by
  unfold fixGamma
  have e := eval_one_eq_mul_sum_synDiv hroot
  rcases lt_trichotomy (P.eval 1) 0 with h | h | h
  · have hl : ((P.eval 1 : ℤ) : ℝ) < 0 := by exact_mod_cast h
    rw [Int.sign_eq_neg_one_of_neg h, abs_of_neg hl]
    push_cast
    rw [mul_div_assoc', div_eq_iff (by linarith)]
    linarith
  · simp [h]
  · have hl : 0 < ((P.eval 1 : ℤ) : ℝ) := by exact_mod_cast h
    rw [Int.sign_eq_one_of_pos h, abs_of_pos hl]
    push_cast
    rw [mul_div_assoc', div_eq_iff (by linarith)]
    linarith

/-- **(proved; Lemma 1, the range).**  For `x ∈ (1/2, 1)` and `P(1) ≠ 0`,
`γ = (1 − x)/|P(1)| ∈ (0, 1/2)`.  Paper proof: `|P(1)| ≥ 1` is a nonzero integer, so
`0 < γ ≤ 1 − x < 1/2`. -/
theorem fixGamma_mem (hx1 : 1 / 2 < x) (hx2 : x < 1) (hP1 : P.eval 1 ≠ 0) :
    0 < fixGamma P x ∧ fixGamma P x < 1 / 2 := by
  have h1 : (1 : ℝ) ≤ |((P.eval 1 : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hP1
  unfold fixGamma
  constructor
  · exact div_pos (by linarith) (by linarith)
  · rw [div_lt_iff₀ (by linarith)]; nlinarith

/-- **(proved; Lemma 1, the fixed point).**  The constant sequence `γ` has every standard
row equal to the integer `sign P(1)`.  Paper proof: `stdRow_const`, `sum_synDiv_mul_fixGamma`. -/
theorem stdRow_fixGamma (hroot : aeval x P = 0) (i : ℕ) :
    stdRow (synDiv P x) P.natDegree (fun _ => fixGamma P x) i = ((P.eval 1).sign : ℝ) := by
  rw [stdRow_const, sum_synDiv_mul_fixGamma hroot]

end Lemma1

/-! ## Roots of unity and the homogeneous direction -/

section RootOfUnity

/-- **(proved).**  For `‖z‖ < 1` and `i ≥ 1`, `|Re(z^i)| < 1`.  Paper proof:
`|Re w| ≤ ‖w‖ = ‖z‖^i < 1` (`Complex.abs_re_le_norm`, `pow_lt_one₀`). -/
theorem abs_re_pow_lt_one_of_norm_lt {z : ℂ} (hz : ‖z‖ < 1) {i : ℕ} (hi : 1 ≤ i) :
    |(z ^ i).re| < 1 := by
  calc |(z ^ i).re| ≤ ‖z ^ i‖ := Complex.abs_re_le_norm _
    _ = ‖z‖ ^ i := norm_pow _ _
    _ < 1 := pow_lt_one₀ (norm_nonneg _) hz (by omega)

/-- **(proved).**  For `‖w‖ ≤ 1` and `w² ≠ 1`, `|Re w| < 1`.  Paper proof: `|Re w| = 1`
and `Re² + Im² ≤ 1` force `Im w = 0`, so `w = ±1` and `w² = 1`. -/
theorem abs_re_lt_one_of_norm_le_of_sq_ne_one {w : ℂ} (hw : ‖w‖ ≤ 1) (hw2 : w ^ 2 ≠ 1) :
    |w.re| < 1 := by
  by_contra h
  rw [not_lt] at h
  have hre : |w.re| ≤ 1 := (Complex.abs_re_le_norm w).trans hw
  have h1 : |w.re| = 1 := le_antisymm hre h
  have hn : w.re * w.re + w.im * w.im ≤ 1 := by
    have h2 := Complex.normSq_eq_norm_sq w
    rw [Complex.normSq_apply] at h2
    nlinarith [norm_nonneg w]
  have hre2 : w.re * w.re = 1 := by
    have h3 := sq_abs w.re
    rw [h1] at h3; nlinarith
  have him : w.im = 0 := by nlinarith [mul_self_nonneg w.im]
  apply hw2
  apply Complex.ext <;> simp [pow_two, Complex.mul_re, Complex.mul_im, him, hre2]

/-- **(proved; N3 step 1).**  If `‖z‖ ≤ 1` and `z` is not a root of unity, then
`|Re(z^i)| < 1` for every `i ≥ 1`.  Paper proof: `abs_re_lt_one_of_norm_le_of_sq_ne_one` with
`w = z^i` (`‖z^i‖ ≤ 1`), since `w² = z^{2i} ≠ 1`. -/
theorem abs_re_pow_lt_one_of_norm_le {z : ℂ} (hz : ‖z‖ ≤ 1)
    (hru : ∀ m : ℕ, 0 < m → z ^ m ≠ 1) {i : ℕ} (hi : 1 ≤ i) : |(z ^ i).re| < 1 := by
  apply abs_re_lt_one_of_norm_le_of_sq_ne_one
  · rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hz
  · rw [← pow_mul]; exact hru _ (by omega)

/-- **(proved; the bridge).**  A complex root `z` of a monic irreducible `P ∈ ℤ[t]` that
also has a real root `x ∈ (0, 1)` is not a root of unity (in particular `z ≠ ±1`).  Paper proof:
`P = minpoly ℤ z` (`minpoly.eq_of_irreducible_of_monic`), so `z^m = 1` gives
`P ∣ t^m − 1` (`minpoly.isIntegrallyClosed_dvd`), hence `x^m = 1`, but `0 < x^m < 1`. -/
theorem pow_ne_one_of_irreducible {P : ℤ[X]} (hP : P.Monic) (hirr : Irreducible P) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) (hroot : aeval x P = 0) {z : ℂ} (hz : aeval z P = 0) {m : ℕ}
    (hm : 0 < m) : z ^ m ≠ 1 := by
  intro hzm
  set PQ : ℚ[X] := P.map (algebraMap ℤ ℚ) with hPQ
  have hirrQ : Irreducible PQ := (hP.irreducible_iff_irreducible_map_fraction_map).1 hirr
  have hzQ : aeval z PQ = 0 := by rw [hPQ, aeval_map_algebraMap]; exact hz
  have hxQ : aeval x PQ = 0 := by rw [hPQ, aeval_map_algebraMap]; exact hroot
  have hmin : PQ = minpoly ℚ z := minpoly.eq_of_irreducible_of_monic hirrQ hzQ (hP.map _)
  have hdvd : PQ ∣ X ^ m - 1 := by
    rw [hmin]
    exact minpoly.dvd ℚ z (by rw [map_sub, map_pow, aeval_X, map_one, hzm, sub_self])
  obtain ⟨R, hR⟩ := hdvd
  have h : aeval x ((X : ℚ[X]) ^ m - 1) = 0 := by rw [hR, map_mul, hxQ, zero_mul]
  rw [map_sub, map_pow, aeval_X, map_one] at h
  have := pow_lt_one₀ hx0.le hx1 hm.ne'
  linarith

/-- A polynomial divisible by a monic linear `D` and irreducible has degree `1`. -/
theorem natDegree_eq_one_of_dvd {P D : ℤ[X]} (hirr : Irreducible P) (hD : D.natDegree = 1)
    (hDm : D.Monic) (hdvd : D ∣ P) : P.natDegree = 1 := by
  obtain ⟨R, rfl⟩ := hdvd
  rcases hirr.isUnit_or_isUnit rfl with h | h
  · have := natDegree_eq_zero_of_isUnit h; omega
  · rw [hDm.natDegree_mul' (by rintro rfl; simp at h), natDegree_eq_zero_of_isUnit h, hD]

/-- **(proved).**  An irreducible `P ∈ ℤ[t]` of degree `≥ 2` has `P(1) ≠ 0`.  Paper
proof: `P(1) = 0` gives `t − 1 ∣ P` (`Polynomial.mul_divByMonic_eq_iff_isRoot`), so `P` is
associated to `t − 1` and has degree `1`. -/
theorem eval_one_ne_zero_of_irreducible {P : ℤ[X]} (hirr : Irreducible P)
    (hd : 2 ≤ P.natDegree) : P.eval 1 ≠ 0 := by
  intro h
  have := natDegree_eq_one_of_dvd hirr (natDegree_X_sub_C 1) (monic_X_sub_C 1)
    (dvd_iff_isRoot.2 h)
  omega

/-- **(proved).**  An irreducible `P ∈ ℤ[t]` of degree `≥ 2` has `a_0 = P(0) ≠ 0`.
Paper proof: `a_0 = 0` gives `t ∣ P` (`Polynomial.X_dvd_iff`), so `P` is associated to `t`. -/
theorem coeff_zero_ne_zero_of_irreducible {P : ℤ[X]} (hirr : Irreducible P)
    (hd : 2 ≤ P.natDegree) : P.coeff 0 ≠ 0 := by
  intro h
  have := natDegree_eq_one_of_dvd hirr natDegree_X monic_X (X_dvd_iff.2 h)
  omega

/-- **(proved).**  `q_0 ≠ 0` when `a_0 ≠ 0`.  Paper proof: `a_0 = −x q_0`
(`coeff_zero_eq_synDiv`). -/
theorem synDiv_zero_ne_zero {P : ℤ[X]} {x : ℝ} (hroot : aeval x P = 0)
    (ha0 : P.coeff 0 ≠ 0) : synDiv P x 0 ≠ 0 := by
  intro h
  have := coeff_zero_eq_synDiv hroot
  rw [h, mul_zero, neg_zero] at this
  exact ha0 (by exact_mod_cast this)

/-- `sum_coeff_mul_eq_synDiv` for a complex sequence `w` (real and imaginary parts). -/
theorem sum_coeff_mul_eq_synDiv_complex {P : ℤ[X]} {x : ℝ} (hroot : aeval x P = 0)
    (w : ℕ → ℂ) :
    ∑ j ∈ Finset.range (P.natDegree + 1), (((P.coeff j : ℝ)) : ℂ) * w j =
      ∑ k ∈ Finset.range P.natDegree, (synDiv P x k : ℂ) * (w (k + 1) - x * w k) := by
  have hre := sum_coeff_mul_eq_synDiv hroot (fun j => (w j).re)
  have him := sum_coeff_mul_eq_synDiv hroot (fun j => (w j).im)
  apply Complex.ext
  · simp only [Complex.re_sum, Complex.re_ofReal_mul, Complex.sub_re] at *
    rw [hre]
  · simp only [Complex.im_sum, Complex.im_ofReal_mul, Complex.sub_im] at *
    rw [him]

/-- **(proved).**  For another root `z ≠ x` of `P`, `Q(z) = Σ_{k<d} q_k z^k = 0`.  Paper
proof: `P(z) = (z − x)Q(z)` (`sum_coeff_mul_eq_synDiv` applied to `w_j = Re(z^j)` and to
`w_j = Im(z^j)`, recombined), and `z − x ≠ 0`. -/
theorem sum_synDiv_mul_pow_eq_zero {P : ℤ[X]} {x : ℝ} (hroot : aeval x P = 0) {z : ℂ}
    (hz : aeval z P = 0) (hzx : z ≠ (x : ℂ)) :
    ∑ k ∈ Finset.range P.natDegree, (synDiv P x k : ℂ) * z ^ k = 0 := by
  have h := sum_coeff_mul_eq_synDiv_complex hroot (fun j => z ^ j)
  have key : aeval z P = (z - x) * ∑ k ∈ Finset.range P.natDegree, (synDiv P x k : ℂ) * z ^ k := by
    rw [aeval_eq_sum_range]
    have e1 : ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i • z ^ i =
        ∑ j ∈ Finset.range (P.natDegree + 1), (((P.coeff j : ℝ)) : ℂ) * z ^ j :=
      Finset.sum_congr rfl fun j _ => by rw [zsmul_eq_mul]; push_cast; rfl
    rw [e1, h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [key] at hz
  exact (mul_eq_zero.1 hz).resolve_left (sub_ne_zero.2 hzx)

/-- **(proved; N3 step 1, homogeneity).**  `c_i = Re(z^i)` is homogeneous:
`R_i(c) = Re(z^i Q(z)) = 0` (the `q_k` are real). -/
theorem stdRow_re_pow {P : ℤ[X]} {x : ℝ} (hroot : aeval x P = 0) {z : ℂ}
    (hz : aeval z P = 0) (hzx : z ≠ (x : ℂ)) (i : ℕ) :
    stdRow (synDiv P x) P.natDegree (fun j => (z ^ j).re) i = 0 := by
  have h := sum_synDiv_mul_pow_eq_zero hroot hz hzx
  have h2 : (z ^ i * ∑ k ∈ Finset.range P.natDegree, (synDiv P x k : ℂ) * z ^ k).re = 0 := by
    rw [h, mul_zero, Complex.zero_re]
  rw [Finset.mul_sum, Complex.re_sum] at h2
  unfold stdRow
  rw [← h2]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only
  rw [pow_add, mul_left_comm, Complex.re_ofReal_mul]

end RootOfUnity

/-! ## The N3 core (pure real arithmetic) -/

section Core

variable {q : ℕ → ℝ} {d : ℕ}

/-- **(proved; N3 step 2).**  `ε°_0 ∈ {0, 1/2}` when `c_0 = 1`.  Paper proof: `γ − γ = 0`
or `γ + 1/2 − γ = 1/2`. -/
theorem boundarySeq_zero {γ : ℝ} {c : ℕ → ℝ} (hc0 : c 0 = 1) :
    boundarySeq γ c 0 = 0 ∨ boundarySeq γ c 0 = 1 / 2 := by
  unfold boundarySeq
  rw [hc0]
  split_ifs
  · left; ring
  · right; ring

/-- **(proved; N3 step 2).**  For `γ ∈ (0, 1/2)` and `|c_i| < 1`, `ε°_i ∈ (0, 1/2)`.
Paper proof: if `γ ≤ 1/4`, `ε°_i = γ(1 − c_i) ∈ (0, 2γ)`; otherwise
`ε°_i ∈ (2γ − 1/2, 1/2)`. -/
theorem boundarySeq_mem {γ : ℝ} {c : ℕ → ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1 / 2) {i : ℕ}
    (hc : |c i| < 1) : 0 < boundarySeq γ c i ∧ boundarySeq γ c i < 1 / 2 := by
  unfold boundarySeq
  rw [abs_lt] at hc
  obtain ⟨hc1, hc2⟩ := hc
  split_ifs with h
  · constructor
    · nlinarith [mul_pos hγ0 (by linarith : (0 : ℝ) < 1 - c i)]
    · nlinarith [mul_pos hγ0 (by linarith : (0 : ℝ) < 1 + c i)]
  · rw [not_le] at h
    constructor
    · nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 / 2 - γ) (by linarith : (0 : ℝ) < 1 + c i)]
    · nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 / 2 - γ) (by linarith : (0 : ℝ) < 1 - c i)]

/-- **(proved; N3 step 2).**  For homogeneous `c`, every standard row of `ε°` is `Q(1)γ`.
Paper proof: `boundarySeq = γ + κc`, `stdRow_add_smul`, `stdRow_const`, `R_i(c) = 0`. -/
theorem stdRow_boundarySeq {γ : ℝ} {c : ℕ → ℝ} (hc : ∀ i, stdRow q d c i = 0) (i : ℕ) :
    stdRow q d (boundarySeq γ c) i = (∑ k ∈ Finset.range d, q k) * γ := by
  have e : boundarySeq γ c =
      fun j => (fun _ => γ) j + (if γ ≤ 1 / 4 then -γ else 1 / 2 - γ) * c j := rfl
  rw [e, stdRow_add_smul, stdRow_const, hc, mul_zero, add_zero]

/-- **(proved; N3 step 2, assembled).**  The boundary sequence of `γ ∈ (0, 1/2)` with
`Q(1)γ ∈ ℤ` and a homogeneous `c` (`c_0 = 1`, `|c_i| < 1` for `i ≥ 1`) has `ε°_0 ∈ [0, 1/2]`,
`ε°_i ∈ (0, 1/2)` for `i ≥ 1`, every standard row integral, and an integral top row.  Paper
proof: `boundarySeq_zero`, `boundarySeq_mem`, `stdRow_boundarySeq`; the top row is
`R_0 + 2a_0ε°_0` (`topRow_eq_stdRow_add`) with `2a_0ε°_0 ∈ {0, a_0}`. -/
theorem n3_boundary (hd : 1 ≤ d) (a0 : ℤ) {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1 / 2)
    (hm : ∃ m : ℤ, (∑ k ∈ Finset.range d, q k) * γ = m) {c : ℕ → ℝ}
    (hc : ∀ i, stdRow q d c i = 0) (hc0 : c 0 = 1) (hc1 : ∀ i, 1 ≤ i → |c i| < 1) :
    (0 ≤ boundarySeq γ c 0 ∧ boundarySeq γ c 0 ≤ 1 / 2) ∧
      (∀ i, 1 ≤ i → 0 < boundarySeq γ c i ∧ boundarySeq γ c i < 1 / 2) ∧
      (∃ m : ℤ, topRow q d a0 (boundarySeq γ c) = m) ∧
      ∀ i, ∃ m : ℤ, stdRow q d (boundarySeq γ c) i = m := by
  obtain ⟨m, hm⟩ := hm
  refine ⟨?_, fun i hi => boundarySeq_mem hγ0 hγ1 (hc1 i hi), ?_,
    fun i => ⟨m, by rw [stdRow_boundarySeq hc, hm]⟩⟩
  · rcases boundarySeq_zero (γ := γ) hc0 with h | h <;> rw [h] <;> norm_num
  · rw [topRow_eq_stdRow_add hd, stdRow_boundarySeq hc, hm]
    rcases boundarySeq_zero (γ := γ) hc0 with h | h
    · exact ⟨m, by rw [h]; ring⟩
    · exact ⟨m + a0, by rw [h]; push_cast; ring⟩

/-- **(proved; N3 step 3, the perturbation).**  Let `e` have `e_0 ∈ [0, 1/2]`,
`e_i ∈ (0, 1/2)` for `i ≥ 1`, an integral top row and integral standard rows `R_i`, `i ≥ 1`.
If `b` is homogeneous on indices `≥ 1` (`R_i(b) = 0` for `i ≥ 1`) with
`S_b = Σ_{k=1}^{d−1} q_k b_k ≠ 0`, the run system has a solution of every length `n`.  Paper
proof: `σ = 1` if `e_0 ≤ 1/4`, else `−1`; `ε_0 = e_0 + σδ`, `ε_i = e_i + λb_i` (`i ≥ 1`),
`λ = −σq̃_0δ/S_b`.  Rows `R_i`, `i ≥ 1`, use indices `≥ 1` only (`stdRow_add_smul`); the top
row moves by `σq̃_0δ + λS_b = 0`.  With `μ = min_{1 ≤ i < n} min(e_i, 1/2 − e_i) > 0` and
`B = max_{i<n} |b_i|`, any `0 < δ ≤ 1/4` with `|q̃_0|δB < μ|S_b|` keeps every `ε_i`, `i < n`, in
`(0, 1/2)`. -/
theorem perturb (hd : 1 ≤ d) (a0 : ℤ) {e : ℕ → ℝ} (he0 : 0 ≤ e 0 ∧ e 0 ≤ 1 / 2)
    (he : ∀ i, 1 ≤ i → 0 < e i ∧ e i < 1 / 2) (htop : ∃ m : ℤ, topRow q d a0 e = m)
    (hrow : ∀ i, 1 ≤ i → ∃ m : ℤ, stdRow q d e i = m) {b : ℕ → ℝ}
    (hb : ∀ i, 1 ≤ i → stdRow q d b i = 0) (hSb : ∑ k ∈ Finset.Ico 1 d, q k * b k ≠ 0)
    (n : ℕ) : ∃ ε : ℕ → ℝ, RunSystem q d a0 n ε := by
  have _ : 1 ≤ d := hd  -- `d ≥ 1` is part of the setting; the construction does not need it
  set Sb := ∑ k ∈ Finset.Ico 1 d, q k * b k with hSbdef
  set σ : ℝ := if e 0 ≤ 1 / 4 then 1 else -1 with hσ
  set qt : ℝ := q 0 + 2 * a0 with hqt
  let ε : ℝ → ℕ → ℝ := fun δ i =>
    if i = 0 then e 0 + σ * δ else e i + (-σ * qt * δ / Sb) * b i
  -- the rows hold for every δ
  have hrows : ∀ δ : ℝ, (∃ m : ℤ, topRow q d a0 (ε δ) = m) ∧
      ∀ i, 1 ≤ i → i + d ≤ n → ∃ m : ℤ, stdRow q d (ε δ) i = m := by
    intro δ
    refine ⟨?_, fun i hi _ => ?_⟩
    · obtain ⟨m, hm⟩ := htop
      refine ⟨m, ?_⟩
      rw [← hm]
      unfold topRow
      have hsum : ∑ k ∈ Finset.Ico 1 d, q k * ε δ k =
          ∑ k ∈ Finset.Ico 1 d, q k * e k + (-σ * qt * δ / Sb) * Sb := by
        rw [hSbdef, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk0 : k ≠ 0 := by have := (Finset.mem_Ico.1 hk).1; omega
        simp only [ε, if_neg hk0]
        ring
      rw [hsum]
      simp only [ε, if_pos rfl]
      rw [div_mul_cancel₀ _ hSb, ← hqt]
      ring
    · obtain ⟨m, hm⟩ := hrow i hi
      refine ⟨m, ?_⟩
      have heq : stdRow q d (ε δ) i =
          stdRow q d (fun j => e j + (-σ * qt * δ / Sb) * b j) i := by
        unfold stdRow
        refine Finset.sum_congr rfl fun k _ => ?_
        have : i + k ≠ 0 := by omega
        simp only [ε, if_neg this]
      rw [heq, stdRow_add_smul, hb i hi, mul_zero, add_zero, hm]
  -- the box holds eventually as δ → 0⁺
  have hbox : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ i ∈ Finset.range n, 0 < ε δ i ∧ ε δ i < 1 / 2 := by
    rw [Filter.eventually_all_finset]
    intro i _
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · have h4 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ∈ Set.Ioo (0 : ℝ) (1 / 4) :=
        Ioo_mem_nhdsGT (by norm_num)
      filter_upwards [h4] with δ hδ
      obtain ⟨hδ0, hδ1⟩ := hδ
      simp only [ε, if_pos rfl, hσ]
      split_ifs with h
      · constructor <;> linarith
      · rw [not_le] at h; constructor <;> linarith
    · have hcont : Tendsto (fun δ : ℝ => e i + (-σ * qt * δ / Sb) * b i) (𝓝 0) (𝓝 (e i)) := by
        have : Continuous (fun δ : ℝ => e i + (-σ * qt * δ / Sb) * b i) := by fun_prop
        simpa using this.tendsto 0
      have hev := (hcont.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))).eventually
        (Ioo_mem_nhds (he i hi).1 (he i hi).2)
      filter_upwards [hev] with δ hδ
      simp only [ε, if_neg (Nat.pos_iff_ne_zero.1 hi)]
      exact hδ
  obtain ⟨δ, hδ⟩ := hbox.exists
  exact ⟨ε δ, fun i hi => hδ i (Finset.mem_range.2 hi), (hrows δ).1, (hrows δ).2⟩

/-- **(proved; the N3 core).**  For real `q` with `q_0 ≠ 0`, `γ ∈ (0, 1/2)` with
`Q(1)γ ∈ ℤ`, and a homogeneous `c` with `c_0 = 1` and `|c_i| < 1` for `i ≥ 1`, the run system (any
integer `a_0`) has a solution of every length.  Paper proof: `n3_boundary`, then `perturb` with
`b = c`: `R_i(c) = 0`, and `S_c = R_0(c) − q_0c_0 = −q_0 ≠ 0`. -/
theorem n3_core (hd : 1 ≤ d) (hq0 : q 0 ≠ 0) (a0 : ℤ) {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1 / 2)
    (hm : ∃ m : ℤ, (∑ k ∈ Finset.range d, q k) * γ = m) {c : ℕ → ℝ}
    (hc : ∀ i, stdRow q d c i = 0) (hc0 : c 0 = 1) (hc1 : ∀ i, 1 ≤ i → |c i| < 1) (n : ℕ) :
    ∃ ε : ℕ → ℝ, RunSystem q d a0 n ε := by
  obtain ⟨h0, h1, htop, hrow⟩ := n3_boundary hd a0 hγ0 hγ1 hm hc hc0 hc1
  refine perturb hd a0 h0 h1 htop (fun i _ => hrow i) (b := c) (fun i _ => hc i) ?_ n
  have h := hc 0
  unfold stdRow at h
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (a := 0) (b := d) (by omega)] at h
  simp only [zero_add] at h
  rw [hc0, mul_one] at h
  intro hS
  exact hq0 (by linarith)

end Core

/-! ## Theorem N3, automaton form -/

section TheoremN3

/-- **(proved; Theorem N3, automaton form).**  Let `x ∈ (1/2, 1)` be a root of a
monic irreducible `P ∈ ℤ[t]` of degree `d ≥ 2` with another complex root `z ≠ x`, `‖z‖ ≤ 1`.  Then
for every `n` the run system with `q = synDiv P x` and `a_0 = P.coeff 0` has a solution in
`(0, 1/2)^n`.  Paper proof: `n3_core` with `γ = fixGamma P x` (`fixGamma_mem`,
`eval_one_ne_zero_of_irreducible`, `sum_synDiv_mul_fixGamma`), `c_i = Re(z^i)` (`stdRow_re_pow`;
`|c_i| < 1` by `abs_re_pow_lt_one_of_norm_le` and `pow_ne_one_of_irreducible`), and `q_0 ≠ 0`
(`synDiv_zero_ne_zero`, `coeff_zero_ne_zero_of_irreducible`). -/
theorem n3_runSystem {P : ℤ[X]} (hP : P.Monic) (hirr : Irreducible P) (hd : 2 ≤ P.natDegree)
    {x : ℝ} (hx1 : 1 / 2 < x) (hx2 : x < 1) (hroot : aeval x P = 0) {z : ℂ}
    (hz : aeval z P = 0) (hzx : z ≠ (x : ℂ)) (hz1 : ‖z‖ ≤ 1) (n : ℕ) :
    ∃ ε : ℕ → ℝ, RunSystem (synDiv P x) P.natDegree (P.coeff 0) n ε := by
  have hP1 := eval_one_ne_zero_of_irreducible hirr hd
  have ha0 := coeff_zero_ne_zero_of_irreducible hirr hd
  obtain ⟨hγ0, hγ1⟩ := fixGamma_mem hx1 hx2 hP1
  exact n3_core (by omega) (synDiv_zero_ne_zero hroot ha0) _ hγ0 hγ1
    ⟨(P.eval 1).sign, sum_synDiv_mul_fixGamma hroot⟩ (c := fun j => (z ^ j).re)
    (stdRow_re_pow hroot hz hzx) (by simp) (fun i hi => abs_re_pow_lt_one_of_norm_le hz1
      (fun m hm => pow_ne_one_of_irreducible hP hirr (by linarith) hx2 hroot hz hm) hi) n

end TheoremN3

/-! ## Headline, conditional on the run criterion -/

section Headline

/-- **Prior-report hypothesis (`wythoff-classify` §1, zonotope criterion with Theorem N4, the
sufficiency direction; PROVED 95-97% there; not in Lean).**  For `α > 2` (main side,
`x = xOf α = β/2 ∈ (1/2, 1)`, up-class = the evens) with `x` a root of a monic irreducible
`P ∈ ℤ[t]` of degree `d ≥ 2`, and every `n ≥ d`: if the run system of length `n` (`q = synDiv P x`,
`a_0 = P.coeff 0`) has a solution, then infinitely many positive even `u` are followed by a run
of length `≥ n`, i.e. `W(u), …, W^n(u)` are all odd.  *Where it comes from.*  Theorem N
(`WythoffAutomaton`, proved) identifies the run with the automaton on the phases
`G_l = 2ε_{l−1}`: row integrality is the evenness of `P(S)w`, which is the continuation test.
The solution set is relatively open in an affine slice parametrised by the free phases
`(G_1, …, G_{d−1})` (`q_{d−1} = 1`), so it has positive measure; N4 (fresh steps: those phases are
uniform on `(0, 1)^{d−1}` given the cylinder `E O^{d−1}`, via `WeylEquidistributionMulti` and
`1, x, …, x^{d−1}` independent) turns positive measure into positive density.  Expected to be
provable from `WythoffAutomaton` and `WeylEquidistributionMulti`; that is a separate layer. -/
def RunCriterion : Prop :=
  ∀ (α : ℝ) (P : ℤ[X]), 2 < α → P.Monic → Irreducible P → 2 ≤ P.natDegree →
    aeval (xOf α) P = 0 → ∀ n : ℕ, P.natDegree ≤ n →
      (∃ ε : ℕ → ℝ, RunSystem (synDiv P (xOf α)) P.natDegree (P.coeff 0) n ε) →
        {u : ℤ | 0 < u ∧ u % 2 = 0 ∧ ∀ j ∈ Finset.Icc 1 n, (wy α)^[j] u % 2 = 1}.Infinite

/-- **(proved).**  For `α > 2`, `x = β/2 ∈ (1/2, 1)`.  Paper proof:
`x = α/(2(α − 1))`; `x > 1/2 ⟺ α > α − 1`, `x < 1 ⟺ α < 2α − 2`. -/
theorem xOf_mem {α : ℝ} (hα : 2 < α) : 1 / 2 < xOf α ∧ xOf α < 1 := by
  unfold xOf
  have h : 0 < α - 1 := by linarith
  constructor
  · rw [lt_div_iff₀ (by norm_num), lt_div_iff₀ h]; linarith
  · rw [div_lt_iff₀ (by norm_num), div_lt_iff₀ h]; linarith

/-- **(proved; Theorem N3, headline, conditional on `RunCriterion`).**  Let `α > 2`
with `x = xOf α` a root of a monic irreducible `P ∈ ℤ[t]` of degree `≥ 2` having another complex
root `z ≠ x` with `‖z‖ ≤ 1`.  Then for every `n` infinitely many positive even `u` are followed by
`n` odd iterates: `W_α` does not have bounded runs (so it is not solvable, `wythoff-classify`
Corollary P″).  Paper proof: for `n ≥ d`, `n3_runSystem` (with `xOf_mem`) feeds `RunCriterion`; for
`n < d`, the set for `d` is contained in the set for `n`. -/
theorem n3_infinite_runs (hRC : RunCriterion) {α : ℝ} (hα : 2 < α) {P : ℤ[X]} (hP : P.Monic)
    (hirr : Irreducible P) (hd : 2 ≤ P.natDegree) (hroot : aeval (xOf α) P = 0) {z : ℂ}
    (hz : aeval z P = 0) (hzx : z ≠ (xOf α : ℂ)) (hz1 : ‖z‖ ≤ 1) (n : ℕ) :
    {u : ℤ | 0 < u ∧ u % 2 = 0 ∧ ∀ j ∈ Finset.Icc 1 n, (wy α)^[j] u % 2 = 1}.Infinite := by
  obtain ⟨hx1, hx2⟩ := xOf_mem hα
  have key : ∀ n, P.natDegree ≤ n →
      {u : ℤ | 0 < u ∧ u % 2 = 0 ∧ ∀ j ∈ Finset.Icc 1 n, (wy α)^[j] u % 2 = 1}.Infinite :=
    fun n hn => hRC α P hα hP hirr hd hroot n hn
      (n3_runSystem hP hirr hd hx1 hx2 hroot hz hzx hz1 n)
  rcases le_total P.natDegree n with h | h
  · exact key n h
  · refine (key _ le_rfl).mono ?_
    rintro u ⟨h0, h2, h3⟩
    exact ⟨h0, h2, fun j hj => h3 j
      (Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hj).1, (Finset.mem_Icc.1 hj).2.trans h⟩)⟩

end Headline

/-! ## Lemma B2 -/

section LemmaB2

variable {P : ℤ[X]}

/-- **(proved; Lemma B2, parity).**  For monic `P` of degree `d`, `2^d P(1/2)` is an odd
integer.  Paper proof: `2^d P(1/2) = Σ_{j ≤ d} a_j 2^{d−j}`; the `j = d` term is `1`
(`Monic.coeff_natDegree`), every other term is even. -/
theorem two_pow_mul_aeval_half_odd (hP : P.Monic) :
    ∃ m : ℤ, Odd m ∧ (2 : ℝ) ^ P.natDegree * aeval (1 / 2 : ℝ) P = m := by
  set d := P.natDegree
  refine ⟨2 * ∑ j ∈ Finset.range d, P.coeff j * 2 ^ (d - j - 1) + 1, odd_two_mul_add_one _, ?_⟩
  rw [aeval_eq_sum_range, Finset.sum_range_succ, mul_add, Finset.mul_sum]
  have hlast : (2 : ℝ) ^ d * (P.coeff d • (1 / 2 : ℝ) ^ d) = 1 := by
    rw [hP.coeff_natDegree, one_smul, ← mul_pow]; norm_num
  rw [hlast]
  push_cast
  rw [Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj : j < d := Finset.mem_range.1 hj
  rw [zsmul_eq_mul]
  have h2 : (2 : ℝ) ^ d = 2 ^ (d - j - 1) * 2 * 2 ^ j := by
    rw [← pow_succ, ← pow_add]; congr 1; omega
  have h3 : (2 : ℝ) ^ j * (1 / 2) ^ j = 1 := by rw [← mul_pow]; norm_num
  rw [h2]
  linear_combination (2 ^ (d - j - 1) * 2 * (P.coeff j : ℝ)) * h3

/-- **(proved; Lemma B2, size).**  `|P(1/2)| ≥ 2^{−d}` for monic `P` of degree `d`.
Paper proof: `two_pow_mul_aeval_half_odd`; an odd integer has `|m| ≥ 1`. -/
theorem abs_aeval_half_ge (hP : P.Monic) :
    (1 / 2 : ℝ) ^ P.natDegree ≤ |aeval (1 / 2 : ℝ) P| := by
  obtain ⟨m, hodd, hm⟩ := two_pow_mul_aeval_half_odd hP
  have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs (by rintro rfl; simp at hodd)
  have h2 : (0 : ℝ) < 2 ^ P.natDegree := by positivity
  rw [one_div_pow, div_le_iff₀ h2]
  calc (1 : ℝ) ≤ |(m : ℝ)| := hm1
    _ = |aeval (1 / 2 : ℝ) P| * 2 ^ P.natDegree := by
      rw [← hm, abs_mul, abs_of_pos h2, mul_comm]

/-- `‖∏(c − s)‖ = ∏‖c − s‖` over a multiset. -/
theorem norm_multiset_prod_sub (S : Multiset ℂ) (c : ℂ) :
    ‖(S.map fun s => c - s).prod‖ = (S.map fun s => ‖c - s‖).prod := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih => simp [ih]

/-- `∏|1/2 − s| ≤ (3/2)^{#S}∏|s|` when every `‖s‖ > 1`. -/
theorem prod_norm_half_sub_le (S : Multiset ℂ) (hS : ∀ s ∈ S, 1 < ‖s‖) :
    (S.map fun s => ‖(1 / 2 : ℂ) - s‖).prod ≤
      (3 / 2) ^ Multiset.card S * (S.map fun s => ‖(0 : ℂ) - s‖).prod := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    have ha := hS a (Multiset.mem_cons_self a S)
    have ih' := ih fun s hs => hS s (Multiset.mem_cons_of_mem hs)
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ]
    have h1 : ‖(1 / 2 : ℂ) - a‖ ≤ 3 / 2 * ‖(0 : ℂ) - a‖ := by
      rw [zero_sub, norm_neg]
      calc ‖(1 / 2 : ℂ) - a‖ ≤ ‖(1 / 2 : ℂ)‖ + ‖a‖ := norm_sub_le _ _
        _ = 1 / 2 + ‖a‖ := by norm_num
        _ ≤ 3 / 2 * ‖a‖ := by linarith
    have h0 : 0 ≤ (S.map fun s => ‖(1 / 2 : ℂ) - s‖).prod :=
      Multiset.prod_nonneg fun y hy => by
        obtain ⟨s, _, rfl⟩ := Multiset.mem_map.1 hy; exact norm_nonneg _
    calc ‖(1 / 2 : ℂ) - a‖ * (S.map fun s => ‖(1 / 2 : ℂ) - s‖).prod
        ≤ (3 / 2 * ‖(0 : ℂ) - a‖) *
            ((3 / 2) ^ Multiset.card S * (S.map fun s => ‖(0 : ℂ) - s‖).prod) :=
          mul_le_mul h1 ih' h0 (by positivity)
      _ = _ := by ring

/-- Evaluating `P` over `ℂ` at a real point is the cast of the real evaluation. -/
theorem eval_ofReal_map {P : ℤ[X]} (t : ℝ) :
    eval (t : ℂ) (P.map (Int.castRingHom ℂ)) = ((aeval t P : ℝ) : ℂ) := by
  rw [← algebraMap_int_eq, eval_map_algebraMap]
  exact aeval_algebraMap_apply ℂ t P

/-- **(proved; Lemma B2, the gap `2x − 1`).**  Let `x ∈ (1/2, 1)` be a root of a monic
`P ∈ ℤ[t]` of degree `d ≥ 2` whose other complex roots (the multiset of roots of `P` over `ℂ`
with one copy of `x` removed) all have `‖z‖ > 1`.  Then `2x − 1 > 1/(2·3^{d−1}|a_0|)`.  Paper
proof: over `ℂ`, `P = (t − x)∏_s(t − x_s)` (`Polynomial.eq_prod_roots_of_monic_of_splits_id`,
`IsAlgClosed.splits`).  So `|P(1/2)| = |x − 1/2|·∏|1/2 − x_s|` with
`|1/2 − x_s| ≤ 1/2 + |x_s| < (3/2)|x_s|`, and `|a_0| = x∏|x_s|`, so
`∏|x_s| = |a_0|/x < 2|a_0|`.  With `abs_aeval_half_ge`:
`2^{−d} ≤ |x − 1/2|·(3/2)^{d−1}·2|a_0|` strictly, i.e. `x − 1/2 > 1/(4·3^{d−1}|a_0|)`. -/
theorem two_mul_sub_one_gt (hP : P.Monic) (hd : 2 ≤ P.natDegree) {x : ℝ} (hx1 : 1 / 2 < x)
    (hx2 : x < 1) (hroot : aeval x P = 0)
    (hconj : ∀ z ∈ (P.map (Int.castRingHom ℂ)).roots.erase (x : ℂ), 1 < ‖z‖) :
    1 / (2 * 3 ^ (P.natDegree - 1) * |(P.coeff 0 : ℝ)|) < 2 * x - 1 := by
  set Pc := P.map (Int.castRingHom ℂ) with hPcdef
  set S := Pc.roots.erase (x : ℂ) with hSdef
  have hPc : Pc.Monic := hP.map _
  have hdeg : Pc.natDegree = P.natDegree := hP.natDegree_map _
  have hcard : Multiset.card Pc.roots = Pc.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hfac := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hPc hcard
  have hx : (x : ℂ) ∈ Pc.roots := by
    rw [mem_roots hPc.ne_zero, IsRoot.def, hPcdef, eval_ofReal_map, hroot, Complex.ofReal_zero]
  have hroots : Pc.roots = (x : ℂ) ::ₘ S := (Multiset.cons_erase hx).symm
  have hcardS : Multiset.card S = P.natDegree - 1 := by
    rw [hSdef, Multiset.card_erase_of_mem hx, hcard, hdeg]; rfl
  have hev : ∀ c : ℂ, ‖eval c Pc‖ = ‖c - x‖ * (S.map fun s => ‖c - s‖).prod := by
    intro c
    conv_lhs => rw [← hfac, hroots]
    rw [Multiset.map_cons, Multiset.prod_cons, eval_mul, eval_multiset_prod, Multiset.map_map,
      norm_mul, ← norm_multiset_prod_sub]
    simp
  -- evaluate at `1/2` and at `0`
  have hhalf := hev (1 / 2)
  have e1 : eval (1 / 2 : ℂ) Pc = ((aeval (1 / 2 : ℝ) P : ℝ) : ℂ) := by
    rw [← eval_ofReal_map]; push_cast; rfl
  rw [e1, Complex.norm_real, Real.norm_eq_abs] at hhalf
  have e2 : ‖(1 / 2 : ℂ) - x‖ = x - 1 / 2 := by
    rw [show (1 / 2 : ℂ) - x = ((1 / 2 - x : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
      Real.norm_eq_abs, abs_sub_comm, abs_of_pos (by linarith)]
  rw [e2] at hhalf
  have hzero := hev 0
  have e3 : eval (0 : ℂ) Pc = ((P.coeff 0 : ℝ) : ℂ) := by
    rw [← coeff_zero_eq_eval_zero, hPcdef, coeff_map]; simp
  rw [e3, Complex.norm_real, Real.norm_eq_abs, zero_sub, norm_neg, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < x)] at hzero
  set A := (S.map fun s => ‖(1 / 2 : ℂ) - s‖).prod
  set B := (S.map fun s => ‖(0 : ℂ) - s‖).prod
  have hAB : A ≤ (3 / 2) ^ (P.natDegree - 1) * B := by
    rw [← hcardS]; exact prod_norm_half_sub_le S hconj
  have hlow := abs_aeval_half_ge hP
  rw [hhalf] at hlow
  obtain ⟨k, hk⟩ : ∃ k, P.natDegree = k + 1 := ⟨P.natDegree - 1, by omega⟩
  rw [hk, Nat.add_sub_cancel] at hAB ⊢
  rw [hk] at hlow
  have hT : (1 / 2 : ℝ) ^ k * 2 ^ k = 1 := by rw [← mul_pow]; norm_num
  have hK : (3 / 2 : ℝ) ^ k * 2 ^ k = 3 ^ k := by rw [← mul_pow]; norm_num
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hB0 : 0 ≤ B := Multiset.prod_nonneg fun y hy => by
    obtain ⟨s, _, rfl⟩ := Multiset.mem_map.1 hy; exact norm_nonneg _
  have hA : (x - 1 / 2) * A ≤ (x - 1 / 2) * ((3 / 2) ^ k * B) :=
    mul_le_mul_of_nonneg_left hAB (by linarith)
  have hone : 1 ≤ (2 * x - 1) * 3 ^ k * B := by
    have h := mul_le_mul_of_nonneg_right (hlow.trans hA) (by positivity : (0 : ℝ) ≤ 2 * 2 ^ k)
    rw [pow_succ] at h
    have e : (1 / 2 : ℝ) ^ k * (1 / 2) * (2 * 2 ^ k) = (1 / 2) ^ k * 2 ^ k := by ring
    have e' : (x - 1 / 2) * ((3 / 2) ^ k * B) * (2 * 2 ^ k) =
        (2 * x - 1) * ((3 / 2) ^ k * 2 ^ k) * B := by ring
    rw [e, e', hT, hK] at h
    exact h
  have hpos : 0 < (2 * x - 1) * 3 ^ k * B := by linarith
  have hBpos : 0 < B := by
    rcases hB0.lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hpos; exact absurd hpos (lt_irrefl 0)
  rw [hzero, div_lt_iff₀ (by positivity)]
  nlinarith [mul_pos hpos (by linarith : (0 : ℝ) < 2 * x - 1)]

/-- **(proved; Lemma B2, the run bound).**  Under `two_mul_sub_one_gt`'s
hypotheses, a run bound `J` with return slope `c_J = x^{J+1}/(2x − 1) > 1` forces
`2·3^{d−1}|a_0|·x^{J+1} > 1`, i.e. `(J + 1)·log(1/x) < log(2·3^{d−1}|a_0|)`.  (With `J ≥ d − 1`
and `x^d ≥ x^{J+1} > 2x − 1` one gets `x < x_d*`, the root of `t^d = 2t − 1` in `(1/2, 1)` for
`d ≥ 3`, hence the research note's `J + 1 < log(2·3^{d−1}|a_0|)/log(1/x_d*)`.)  Paper proof:
`x^{J+1} > 2x − 1 > 1/(2·3^{d−1}|a_0|)` by `two_mul_sub_one_gt`; multiply out, with `a_0 ≠ 0`
because otherwise `0` would be another root with `‖0‖ ≤ 1`. -/
theorem run_bound_B2 (hP : P.Monic) (hd : 2 ≤ P.natDegree) {x : ℝ} (hx1 : 1 / 2 < x)
    (hx2 : x < 1) (hroot : aeval x P = 0)
    (hconj : ∀ z ∈ (P.map (Int.castRingHom ℂ)).roots.erase (x : ℂ), 1 < ‖z‖) {J : ℕ}
    (hJ : 2 * x - 1 < x ^ (J + 1)) :
    1 < 2 * 3 ^ (P.natDegree - 1) * |(P.coeff 0 : ℝ)| * x ^ (J + 1) := by
  have h := two_mul_sub_one_gt hP hd hx1 hx2 hroot hconj
  have hx0 : (0 : ℂ) ≠ (x : ℂ) := fun h' => by
    have := congrArg Complex.re h'
    simp at this
    linarith
  have ha0 : P.coeff 0 ≠ 0 := by
    intro h0
    have hmem : (0 : ℂ) ∈ (P.map (Int.castRingHom ℂ)).roots.erase (x : ℂ) := by
      rw [Multiset.mem_erase_of_ne hx0, mem_roots (hP.map _).ne_zero, IsRoot.def,
        ← coeff_zero_eq_eval_zero, coeff_map, h0, map_zero]
    have := hconj 0 hmem
    rw [norm_zero] at this
    linarith
  have hK : 0 < 2 * 3 ^ (P.natDegree - 1) * |(P.coeff 0 : ℝ)| := by
    have : (0 : ℝ) < |(P.coeff 0 : ℝ)| := abs_pos.2 (by exact_mod_cast ha0)
    positivity
  rw [div_lt_iff₀ hK] at h
  nlinarith [mul_lt_mul_of_pos_left hJ hK]

end LemmaB2

end CollatzMoonshot.WythoffPisot
