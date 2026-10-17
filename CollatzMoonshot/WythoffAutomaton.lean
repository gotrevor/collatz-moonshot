/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.WythoffGeneral

/-!
# The run automaton of an algebraic Wythoff member (Theorems N and O)

Research note `wythoff-classify`, §1 and §3.1.  Let `W = W_α` (`WythoffGeneral.wy`:
`2k ↦ ⌊kα⌋`, `2k − 1 ↦ ⌈kβ⌉ − 1`, `β = α/(α − 1)`) and let `x = β/2` (`xOf`), the slope of the
odd branch.  Let `P = t^d + a_{d−1}t^{d−1} + ⋯ + a_0 ∈ ℤ[t]` be monic with `P(x) = 0` (any monic
integer polynomial with root `x`, not necessarily the minimal one), and let
`Q(t) = P(t)/(t − x) = Σ_{k<d} q_k t^k` be the synthetic-division quotient:
`q_k = Σ_{k<j≤d} a_j x^{j−k−1}` (`synDiv`), so `q_{d−1} = 1`, `a_j = q_{j−1} − x q_j` for
`j ≥ 1` (`coeff_succ_eq_synDiv`, unconditional) and `a_0 = −x q_0` (`coeff_zero_eq_synDiv`,
this is `P(x) = 0`).

**Lemma N0** (`wy_add_one_eq_ceil`).  For odd `v`, `W(v) + 1 = ⌈x(v + 1)⌉`.  So with `w = v + 1`,
an odd step is `w ↦ ⌈xw⌉`, and the odd-step phase `G(v) = (W(v) + 1) − x(v + 1)` (`oddPhase`)
lies in `[0, 1)`.  The even-step phase `G(n) = (W(n) + 1) − (α/2)n` (`evenPhase`) lies in
`(0, 1]` for even `n`.

**Theorem N (1)** (`sum_coeff_iterate_eq`, `sum_coeff_iterate_eq_ceil`).  For any `u ∈ ℤ`, with
`w_j = W^j(u) + 1` and `G_{k+1} = G(W^k u)`:
  `Σ_{j ≤ d} a_j w_j = Σ_{k < d} q_k G_{k+1}`   (pure algebra, from `Q(S)(S − x) = P(S)`),
and if `W^{d−1}(u)` is odd then `G_d ∈ [0, 1)`, so `Σ_j a_j w_j = ⌈Φ⌉` with
`Φ = Σ_{k ≤ d−2} q_k G_{k+1}` (`autoPhi`).  If `u, W(u), …, W^{d−1}(u)` are all odd, every
`a_j w_j` (`j < d`) is even, so `W^d(u)` is odd iff `⌈Φ⌉` is even (`iterate_odd_iff_autoPhi`).
For irrational `x` and `W^{d−1}(u) ≠ −1`, `Φ ∉ ℤ` and `⌈Φ⌉ = ⌊Φ⌋ + 1`, the research note's form.
The research note's phases `g = 1 − {y}` are these `G` (they agree off the integers).

**Theorem N (2)** (`first_step_eq_ceil`).  The step right after `E O^{d−1}`: with the virtual
real `w_0 = n/(2x − 1)` one has `x w_0 = (α/2)n` and `a_0 w_0 = a_0(2(w_1 − G_1) − n)`, so
  `w_d + Σ_{1≤j<d} a_j w_j + 2a_0 w_1 − a_0 n = ⌈Φ₀⌉`,
  `Φ₀ = (q_0 + 2a_0) G_1 + Σ_{1≤k≤d−2} q_k G_{k+1}`
(`autoPhi0`, `G_1 = evenPhase n`).  For even `n` with `W(n), …, W^{d−1}(n)` odd, `W^d(n)` is
odd iff `⌈Φ₀⌉` is even (`first_step_odd_iff`).

*Known answers.*  For Theorem G's `P = t^{m+1} − 2rt + r`: `q_k = x^{m−k}` (`k ≥ 1`),
`q_0 + 2a_0 = x^m`, `Φ₀ = Σ_{j=1}^{m} x^{m+1−j} G_j ∈ (0, 1)`, so the left side is `1`:
`W^{m+1}(n) = rn`.  For Theorem Y's `P = t³ + t² + 3t − 2`: `q = (3 + x + x², 1 + x, 1)`,
`q_0 + 2a_0 = x² + x − 1`, `Φ₀ = Δ′` (`WythoffSporadic.yPhase3`) and the left side is
`W³ + 2n − W + W² + 1`.

**Theorem O** (`thmO`, `firstRowCond_gPoly`, `thmO_iff`).  Let `x ∈ (1/2, 1)` be a root of a
monic `P ∈ ℤ[t]` of degree `d ≥ 2`.  The first-step value `Φ₀` ranges over the open interval
between the sums of the negative and positive coefficients of `(q̃_0, q_1, …, q_{d−2})`,
`q̃_0 = q_0 + 2a_0`; it avoids every odd cell iff (`FirstRowCond`) `q̃_0 ≥ 0`, `q_k ≥ 0` and
`q̃_0 + Σ_{k=1}^{d−2} q_k ≤ 1`.  **This holds iff `P = t^d − 2rt + r` for an integer `r ≥ 1`**
(`gPoly`; `r = 1` is `(t − 1)·(multinacci)`, `r ≥ 2` is Theorem G with `m = d − 1`).  So the G
line is exactly the class whose runs stop as early as the fair coins allow.

*Paper proof of `thmO`.*  All of `q̃_0, q_1, …, q_{d−2}` lie in `[0, 1]`.  For `2 ≤ k ≤ d − 1`,
`a_k = q_{k−1} − x q_k ∈ [−x, 1]` (`q_{d−1} = 1`), so `a_k ∈ {0, 1}`, and `a_k = 1` forces
`q_{k−1} = 1`, hence every other term of the sum is `0`; then `a_{d−1} = q_{d−2} − x` is
`−x` or `1 − x`, not an integer: contradiction.  So `a_k = 0` for `2 ≤ k ≤ d − 1`, and downward
`q_k = x^{d−1−k}` for `k ≥ 1`.  Then `q̃_0 = a_0(2x − 1)/x` (from `a_0 = −x q_0`), so `a_0 ≥ 0`,
and `a_1 + 2a_0 = q̃_0 − x^{d−1} ∈ [−x^{d−1}, 1 − x − ⋯ − x^{d−1}] ⊂ (−1, 1)`, so
`a_1 = −2a_0`.  `a_0 = 0` would make `P = t^d`, so `r := a_0 ≥ 1`.  Converse: for
`P = t^d − 2rt + r`, `q̃_0 = r(2x − 1)/x > 0`, `q_k = x^{d−1−k} > 0`, and the sum condition is
`(1 − x)(x + ⋯ + x^{d−1}) = x − x^d = x − r(2x − 1) ≤ 1 − x`, i.e. `(r − 1)(2x − 1) ≥ 0`.

Design: `P` is a `Polynomial ℤ` (`Monic`, `natDegree`, `aeval`: Mathlib's notions, and Theorem
O's conclusion is a polynomial equality); `Q`'s coefficients are the explicit Horner sums
`synDiv` (real-valued, no `/ₘ` API needed, and the recursion `a_j = q_{j−1} − x q_j` is a
one-line `Finset.sum` split).  Truth checks: `tmp/drafter-classify/check.py`.
-/

namespace CollatzMoonshot.WythoffAutomaton

open CollatzMoonshot.WythoffGeneral Polynomial

/-! ## Definitions -/

/-- The odd-branch slope `x = β/2`, `β = α/(α − 1)`. -/
noncomputable def xOf (α : ℝ) : ℝ :=
  α / (α - 1) / 2

/-- The synthetic-division (Horner) coefficient `q_k = Σ_{k<j≤d} a_j x^{j−k−1}` of
`P(t)/(t − x)`, `d = deg P`. -/
noncomputable def synDiv (P : ℤ[X]) (x : ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ioc k P.natDegree, (P.coeff j : ℝ) * x ^ (j - k - 1)

/-- The odd-step phase `G(v) = (W(v) + 1) − x(v + 1)` (in `[0, 1)` for odd `v`). -/
noncomputable def oddPhase (α : ℝ) (v : ℤ) : ℝ :=
  (wy α v : ℝ) + 1 - xOf α * ((v : ℝ) + 1)

/-- The even-step phase `G(n) = (W(n) + 1) − (α/2)n` (in `(0, 1]` for even `n`). -/
noncomputable def evenPhase (α : ℝ) (n : ℤ) : ℝ :=
  (wy α n : ℝ) + 1 - α / 2 * n

/-- Theorem N (1)'s automaton value `Φ = Σ_{k ≤ d−2} q_k G(W^k u)`. -/
noncomputable def autoPhi (P : ℤ[X]) (α : ℝ) (u : ℤ) : ℝ :=
  ∑ k ∈ Finset.range (P.natDegree - 1), synDiv P (xOf α) k * oddPhase α ((wy α)^[k] u)

/-- Theorem N (2)'s first-step value
`Φ₀ = (q_0 + 2a_0) G_E(n) + Σ_{1 ≤ k ≤ d−2} q_k G(W^k n)`. -/
noncomputable def autoPhi0 (P : ℤ[X]) (α : ℝ) (n : ℤ) : ℝ :=
  (synDiv P (xOf α) 0 + 2 * P.coeff 0) * evenPhase α n +
    ∑ k ∈ Finset.Ico 1 (P.natDegree - 1), synDiv P (xOf α) k * oddPhase α ((wy α)^[k] n)

/-- Theorem G's polynomial `t^d − 2rt + r`. -/
noncomputable def gPoly (d : ℕ) (r : ℤ) : ℤ[X] :=
  X ^ d - C (2 * r) * X + C r

/-- Theorem O's first-row condition: `q̃_0 = q_0 + 2a_0 ≥ 0`, `q_k ≥ 0` for `1 ≤ k ≤ d − 2`, and
`q̃_0 + Σ_{k=1}^{d−2} q_k ≤ 1` (equivalently `Φ₀((0, 1)^{d−1}) ⊆ [0, 1]`). -/
def FirstRowCond (P : ℤ[X]) (x : ℝ) : Prop :=
  0 ≤ synDiv P x 0 + 2 * P.coeff 0 ∧
    (∀ k ∈ Finset.Icc 1 (P.natDegree - 2), 0 ≤ synDiv P x k) ∧
    synDiv P x 0 + 2 * P.coeff 0 + ∑ k ∈ Finset.Icc 1 (P.natDegree - 2), synDiv P x k ≤ 1

/-! ## Synthetic division -/

section SynDiv

variable {P : ℤ[X]} {x : ℝ}

/-- **(drafted, 99%).**  `q_{d−1} = a_d = 1` for monic `P` of degree `≥ 1`.  Paper proof:
`Finset.Ioc (d − 1) d = {d}`, `P.coeff d = 1` (`Monic.coeff_natDegree`), `x⁰ = 1`. -/
theorem synDiv_natDegree_sub_one (hP : P.Monic) (hd : 1 ≤ P.natDegree) :
    synDiv P x (P.natDegree - 1) = 1 := by
  sorry

/-- **(proved).**  `q_k = 0` for `k ≥ d` (empty sum). -/
theorem synDiv_of_le {k : ℕ} (hk : P.natDegree ≤ k) : synDiv P x k = 0 := by
  unfold synDiv
  rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]

/-- **(drafted, 99%; the Horner recursion, unconditional).**  `a_{k+1} = q_k − x q_{k+1}` for
every `k`.  Paper proof: `Ioc k d = insert (k + 1) (Ioc (k + 1) d)` when `k < d` (and both sides
vanish when `k ≥ d`, `coeff_eq_zero_of_natDegree_lt`); `x · x^{j−k−2} = x^{j−k−1}`. -/
theorem coeff_succ_eq_synDiv (k : ℕ) :
    (P.coeff (k + 1) : ℝ) = synDiv P x k - x * synDiv P x (k + 1) := by
  sorry

/-- **(drafted, 99%).**  `a_0 = −x q_0` iff `P(x) = 0`; here the forward direction.  Paper proof:
`aeval x P = Σ_{j ≤ d} a_j x^j` (`aeval_eq_sum_range`) `= a_0 + x Σ_{0<j≤d} a_j x^{j−1}`. -/
theorem coeff_zero_eq_synDiv (hroot : aeval x P = 0) :
    (P.coeff 0 : ℝ) = -(x * synDiv P x 0) := by
  sorry

end SynDiv

/-! ## Lemma N0 and the phases -/

section Phases

variable {α : ℝ}

/-- **(drafted, 99%; Lemma N0).**  For odd `v`, `W(v) + 1 = ⌈x(v + 1)⌉` (`x = β/2`).  Paper proof:
`v = 2k − 1`, `W(v) = ⌈kβ⌉ − 1` (`wy_two_mul_sub_one`) and `x(v + 1) = kβ`.  No hypothesis on
`α`. -/
theorem wy_add_one_eq_ceil (α : ℝ) {v : ℤ} (hv : v % 2 = 1) :
    wy α v + 1 = ⌈xOf α * ((v : ℝ) + 1)⌉ := by
  sorry

/-- **(drafted, 99%).**  For odd `v`, `0 ≤ G(v) < 1` (`Int.le_ceil`, `Int.ceil_lt_add_one`). -/
theorem oddPhase_mem {v : ℤ} (hv : v % 2 = 1) : 0 ≤ oddPhase α v ∧ oddPhase α v < 1 := by
  sorry

/-- **(drafted, 99%).**  For even `n`, `0 < G_E(n) ≤ 1` (`W(2k) = ⌊kα⌋`, `(α/2)·2k = kα`). -/
theorem evenPhase_mem {n : ℤ} (hn : n % 2 = 0) : 0 < evenPhase α n ∧ evenPhase α n ≤ 1 := by
  sorry

/-- **(drafted, 99%).**  The virtual-point identity `x/(2x − 1) = α/2` for `α > 1`
(`2x − 1 = β − 1 = 1/(α − 1)`; `field_simp`). -/
theorem xOf_div_two_mul_sub_one (hα : 1 < α) : xOf α / (2 * xOf α - 1) = α / 2 := by
  sorry

end Phases

/-! ## Theorem N -/

section TheoremN

variable {α : ℝ} {P : ℤ[X]}

/-- **(drafted, 98%; Theorem N (1), the algebra).**  For every `u ∈ ℤ` (no parity hypothesis),
`Σ_{j ≤ d} a_j (W^j u + 1) = Σ_{k < d} q_k G(W^k u)`.  Paper proof: `G(W^k u) = w_{k+1} − x w_k`
by definition (`w_j = W^j u + 1`); expand, reindex, and collect: the coefficient of `w_j` is
`q_{j−1} − x q_j = a_j` for `1 ≤ j ≤ d` (`coeff_succ_eq_synDiv`, `q_d = 0`) and `−x q_0 = a_0`
for `j = 0` (`coeff_zero_eq_synDiv`). -/
theorem sum_coeff_iterate_eq (hroot : aeval (xOf α) P = 0) (u : ℤ) :
    ∑ j ∈ Finset.range (P.natDegree + 1), (P.coeff j : ℝ) * (((wy α)^[j] u : ℝ) + 1) =
      ∑ k ∈ Finset.range P.natDegree, synDiv P (xOf α) k * oddPhase α ((wy α)^[k] u) := by
  sorry

/-- **(drafted, 97%; Theorem N (1)).**  If `W^{d−1}(u)` is odd (in particular along `d`
consecutive odd points `u, …, W^{d−1}u`), `Σ_{j ≤ d} a_j (W^j u + 1) = ⌈Φ⌉`.  Paper proof:
`sum_coeff_iterate_eq`, split off `k = d − 1` (`q_{d−1} = 1`): the integer equals
`Φ + G(W^{d−1}u)` with `G ∈ [0, 1)` (`oddPhase_mem`); `Int.ceil_eq_iff`. -/
theorem sum_coeff_iterate_eq_ceil (hP : P.Monic) (hd : 1 ≤ P.natDegree)
    (hroot : aeval (xOf α) P = 0) {u : ℤ} (hodd : (wy α)^[P.natDegree - 1] u % 2 = 1) :
    ∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j * ((wy α)^[j] u + 1) =
      ⌈autoPhi P α u⌉ := by
  sorry

/-- **(drafted, 96%; Theorem N (1), research-note form).**  If moreover `x` is irrational and
`W^{d−1}(u) ≠ −1`, then `Φ ∉ ℤ`, so the integer is `⌊Φ⌋ + 1`.  Paper proof: `Φ ∈ ℤ` forces
`G(W^{d−1}u) = 0`, i.e. `x(v + 1) = W(v) + 1 ∈ ℤ` with `v + 1 ≠ 0`;
`Int.ceil_eq_floor_add_one_iff_notMem`. -/
theorem sum_coeff_iterate_eq_floor_add_one (hP : P.Monic) (hd : 1 ≤ P.natDegree)
    (hroot : aeval (xOf α) P = 0) (hirr : Irrational (xOf α)) {u : ℤ}
    (hodd : (wy α)^[P.natDegree - 1] u % 2 = 1) (hne : (wy α)^[P.natDegree - 1] u ≠ -1) :
    ∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j * ((wy α)^[j] u + 1) =
      ⌊autoPhi P α u⌋ + 1 := by
  sorry

/-- **(drafted, 97%; Theorem N (1), parity).**  If `u, W(u), …, W^{d−1}(u)` are odd, then
`W^d(u)` is odd iff `⌈Φ⌉` is even.  Paper proof: `sum_coeff_iterate_eq_ceil`; for `j < d`,
`W^j u + 1` is even, and `a_d = 1`, so the sum is `≡ W^d u + 1 (mod 2)`. -/
theorem iterate_odd_iff_autoPhi (hP : P.Monic) (hd : 1 ≤ P.natDegree)
    (hroot : aeval (xOf α) P = 0) {u : ℤ}
    (hodd : ∀ i < P.natDegree, (wy α)^[i] u % 2 = 1) :
    (wy α)^[P.natDegree] u % 2 = 1 ↔ ⌈autoPhi P α u⌉ % 2 = 0 := by
  sorry

/-- **(drafted, 96%; Theorem N (2), the first deterministic step).**  For `α > 1`, `d ≥ 2` and
`W^{d−1}(n)` odd (in particular on the cylinder `E O^{d−1}`):
`w_d + Σ_{1 ≤ j < d} a_j w_j + 2a_0 w_1 − a_0 n = ⌈Φ₀⌉`, `w_j = W^j n + 1`.  Paper proof: apply
the algebra of `sum_coeff_iterate_eq` from the virtual real `w_0 = n/(2x − 1)`, for which
`x w_0 = (α/2) n` (`xOf_div_two_mul_sub_one`) so that `G_E(n) = w_1 − x w_0`; then
`a_0 w_0 = a_0 (2(w_1 − G_E(n)) − n)` (`1/(2x − 1) = α − 1 = 2(α/2) − 1`); move `−2a_0 G_E(n)`
to the phase side; the last phase `G(W^{d−1} n) ∈ [0, 1)`. -/
theorem first_step_eq_ceil (hα : 1 < α) (hP : P.Monic) (hd : 2 ≤ P.natDegree)
    (hroot : aeval (xOf α) P = 0) {n : ℤ} (hodd : (wy α)^[P.natDegree - 1] n % 2 = 1) :
    ∑ j ∈ Finset.Ico 1 (P.natDegree + 1), P.coeff j * ((wy α)^[j] n + 1) +
        2 * P.coeff 0 * (wy α n + 1) - P.coeff 0 * n =
      ⌈autoPhi0 P α n⌉ := by
  sorry

/-- **(drafted, 96%; Theorem N (2), parity).**  For even `n` with `W(n), …, W^{d−1}(n)` odd,
`W^d(n)` is odd iff `⌈Φ₀⌉` is even.  Paper proof: `first_step_eq_ceil`; `n`, `2a_0 w_1` and
`w_j` (`1 ≤ j < d`) are even. -/
theorem first_step_odd_iff (hα : 1 < α) (hP : P.Monic) (hd : 2 ≤ P.natDegree)
    (hroot : aeval (xOf α) P = 0) {n : ℤ} (hn : n % 2 = 0)
    (hodd : ∀ i : ℕ, 1 ≤ i → i < P.natDegree → (wy α)^[i] n % 2 = 1) :
    (wy α)^[P.natDegree] n % 2 = 1 ↔ ⌈autoPhi0 P α n⌉ % 2 = 0 := by
  sorry

end TheoremN

/-! ## Theorem O -/

section TheoremO

/-- **(drafted, 99%).**  `t^d − 2rt + r` is monic of degree `d` for `d ≥ 2`. -/
theorem monic_gPoly {d : ℕ} (hd : 2 ≤ d) (r : ℤ) : (gPoly d r).Monic := by
  sorry

/-- **(drafted, 99%).** -/
theorem natDegree_gPoly {d : ℕ} (hd : 2 ≤ d) (r : ℤ) : (gPoly d r).natDegree = d := by
  sorry

/-- **(drafted, 97%; the G line's Horner coefficients).**  For `P = t^d − 2rt + r` (`d ≥ 2`):
`q_k = x^{d−1−k}` for `1 ≤ k ≤ d − 1` and `q_0 = x^{d−1} − 2r` (unconditional: `synDiv` does
not use the root).  Paper proof: `coeff_gPoly`: `a_d = 1`, `a_1 = −2r`, `a_0 = r`, others `0`;
the sum `Σ_{k<j≤d}` has the single term `j = d` for `k ≥ 1`, and the terms `j ∈ {1, d}` for
`k = 0`. -/
theorem synDiv_gPoly {d : ℕ} (hd : 2 ≤ d) (r : ℤ) (x : ℝ) (k : ℕ) :
    synDiv (gPoly d r) x k = if k = 0 then x ^ (d - 1) - 2 * r else
      if k < d then x ^ (d - 1 - k) else 0 := by
  sorry

/-- **(drafted, 95%; Theorem O, algebraic core).**  If `x ∈ (1/2, 1)` is a root of a monic
`P ∈ ℤ[t]` of degree `d ≥ 2` satisfying the first-row condition, then `P = t^d − 2rt + r` for an
integer `r ≥ 1`.  Paper proof: module docstring.  (No irreducibility is assumed; `r = 1` occurs:
the multinacci factor of `(t − 1)(t^{d−1} + ⋯ + t − 1)`, with equality in the sum condition.) -/
theorem thmO {x : ℝ} (hx1 : 1 / 2 < x) (hx2 : x < 1) {P : ℤ[X]} (hP : P.Monic)
    (hd : 2 ≤ P.natDegree) (hroot : aeval x P = 0) (hc : FirstRowCond P x) :
    ∃ r : ℤ, 1 ≤ r ∧ P = gPoly P.natDegree r := by
  sorry

/-- **(drafted, 97%; Theorem O, converse).**  Every root `x ∈ (1/2, 1)` of `t^d − 2rt + r`
(`d ≥ 2`, `r ≥ 1`) satisfies the first-row condition.  Paper proof: `synDiv_gPoly`;
`q̃_0 = (x^{d−1} − 2r) + 2r = x^{d−1} ≥ 0`; `q_k = x^{d−1−k} ≥ 0`; the sum is
`x + ⋯ + x^{d−1}`, and `(1 − x)(x + ⋯ + x^{d−1}) = x − x^d = x − r(2x − 1) ≤ 1 − x` is
`(r − 1)(2x − 1) ≥ 0`. -/
theorem firstRowCond_gPoly {x : ℝ} (hx1 : 1 / 2 < x) (hx2 : x < 1) {d : ℕ} (hd : 2 ≤ d)
    {r : ℤ} (hr : 1 ≤ r) (hroot : aeval x (gPoly d r) = 0) : FirstRowCond (gPoly d r) x := by
  sorry

/-- **(drafted, 95%; Theorem O).**  For a root `x ∈ (1/2, 1)` of a monic `P ∈ ℤ[t]` of degree
`d ≥ 2`: the first-row condition holds iff `P = t^d − 2rt + r` with `r ≥ 1`.  Paper proof:
`thmO` and `firstRowCond_gPoly`. -/
theorem thmO_iff {x : ℝ} (hx1 : 1 / 2 < x) (hx2 : x < 1) {P : ℤ[X]} (hP : P.Monic)
    (hd : 2 ≤ P.natDegree) (hroot : aeval x P = 0) :
    FirstRowCond P x ↔ ∃ r : ℤ, 1 ≤ r ∧ P = gPoly P.natDegree r := by
  sorry

end TheoremO

end CollatzMoonshot.WythoffAutomaton
