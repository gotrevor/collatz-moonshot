/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.AmusicalTrap
import CollatzMoonshot.WythoffGeneral
import CollatzMoonshot.WythoffCone

/-!
# The degree-`d` trap identity on `E^d`, and the cubic trap member `A³ = 3A² − 1`

Research note `wythoff-solvable`, §9 ("The cubic (and degree-d) analogue"), generalising Theorem
A′/K (`WythoffCone`, the case `d = 2`).  Let `α` be real, `A = α/2`, `W = W_α`
(`WythoffGeneral.wy`), and suppose `A^d = Σ_{j<d} p_j A^j` with `p_j ∈ ℤ`.  Write
`P(t) = t^d − Σ_{j<d} p_j t^j` and `Q(t) = (P(t) − P(A))/(t − A) = Σ_{k<d} q_k t^k`
(`quotCoeff`, synthetic division: `q_k = A^{d−1−k} − Σ_{k<j<d} p_j A^{j−k−1}`, `q_{d−1} = 1`;
`sub_mul_sum_quotCoeff`).

1. **Identity** (`wy_iterate_eq_floor`, any real `α`, every `n ∈ ℤ`).  On `E^d` (`n, W n, …,
   W^{d−1} n` all even), with the phases `f_{i+1} = A·Wⁱ(n) − W^{i+1}(n) ∈ [0, 1)` (`ePhase`):
   `W^d(n) = Σ_{j<d} p_j W^j(n) + ⌊−Σ_{i<d−1} q_i f_{i+1}⌋`.
   *Proof.*  On an even point the step is `v ↦ ⌊A v⌋`, so `v_{i+1} = A v_i − f_{i+1}`.  For any
   sequence, `v_d − Σ p_j v_j = P(A)·v_0 − Σ_{i<d} q_i (A v_i − v_{i+1})` (`phase_identity`; the
   coefficients telescope by `q_{k} = A q_{k+1} − p_{k+1}` and `A q_0 = P(A) + p_0`).  With
   `P(A) = 0`, `q_{d−1} = 1` and `f_d ∈ [0, 1)`, the integer `W^d(n) − Σ p_j W^j(n)` equals
   `X − f_d` with `X = −Σ_{i<d−1} q_i f_{i+1}`, so it is `⌊X⌋`.
2. **Trap** (`wy_iterate_eq_of_trap`, `trapSetD_trap`).  If `q_k ≤ 0` for `k < d − 1` and
   `Q(1) = Σ_k q_k ≥ 0`, then `0 ≤ X ≤ (max f)·(1 − Q(1)) < 1`, the floor vanishes, and
   `W^d = Σ p_j W^j` is even on `E^d`.  So `T_d = {n > 0 : n, …, W^{d−1} n even}` is a `W`-trap,
   along which `W^{j+d} = Σ_i p_i W^{j+i}` (`wy_iterate_add_of_mem_trapSetD`).  (These conditions
   put every other root of `P` in the open unit disk when `Q(1) > 0`, so `A` is a Pisot number;
   for `d = 3` they read `A″ < 0 < A′ < 1`, `A′ + A″ ≥ 0`.)
3. **Infinitely many infinite orbits** (`wyPerm_infinitelyManyInfiniteOrbits_of_trapD`), for
   `α > 2`, **conditional** on multidimensional Weyl equidistribution
   (`WeylEquidistributionMulti`, a literature hypothesis) and `deg A = d` (`hind`).  With
   `n = 2k` and `φ_i = {k Aⁱ}`, `n ∈ T_d` as soon as `φ_i − A φ_{i−1} ∈ [0, 1/2)` for
   `1 ≤ i ≤ d − 1` (`φ_0 = 0`); a small box of such `φ` has positive volume, so `T_d` has positive
   lower density, while finitely many entry points would make `#(T_d ∩ [1, X]) = O(log X)` (on
   `T_d`, `W(t) ≥ (α/2)t − 1`).  The trap theorem (`AmusicalTrap`) concludes.
4. **The cubic member** `A³ = 3A² − 1` (`cRoot ≈ 2.87939`, `alphaC = 2A ≈ 5.75877`, the smallest
   cubic trap member of the research note): `q_0 = A² − 3A`, `q_1 = A − 3`, `Q(1) = A² − 2A − 2`,
   so `W³(n) = 3W²(n) − n` on `EEE` for every `n ∈ ℤ` (`wy_iterate_three_cubic`), `T_3` is a trap
   (`cubicSet_trap`), and (conditional on Weyl) `W` has infinitely many infinite orbits.
5. **`d = 2` consistency.**  `quotCoeff A 2 p 0 = A − p_1`, so the identity at `d = 2` is Theorem
   A′ (`wy_iterate_two_eq_floor`, to be proved **from** `wy_iterate_eq_floor`), and `T_2` is the
   E-cone `coneSet` (`trapSetD_two_alphaK`).

**Encoding.**  Coefficients are a function `p : ℕ → ℤ` (values at `j ≥ d` unused) and every sum
is over `Finset.range` / `Finset.Ioo` on `ℕ`, so no `Fin d` casts appear; `Q` is given by its
coefficients rather than as `P /ₘ (X − C A)` in `ℝ[X]`, so the identity is a finite sum the proof
can unfold, and `sub_mul_sum_quotCoeff` certifies that they are the quotient's coefficients.

Truth checks: `tmp/drafter-trapd/check.py` (gitignored; certified interval floors).
-/

namespace CollatzMoonshot.WythoffTrapDegree

open CollatzMoonshot.WythoffGeneral
open CollatzMoonshot.WythoffCone (alphaK coneSet)
open CollatzMoonshot.AmusicalTrap (permOrbit InfinitelyManyInfiniteOrbits
  infinitelyManyInfiniteOrbits_of_trap)
open Filter Topology Polynomial

/-! ## Synthetic division -/

/-- The coefficient `q_k` of `Q(t) = (P(t) − P(A))/(t − A)`, `P(t) = t^d − Σ_{j<d} p_j t^j`:
`q_k = A^{d−1−k} − Σ_{k<j<d} p_j A^{j−k−1}` (for `k < d`). -/
noncomputable def quotCoeff (A : ℝ) (d : ℕ) (p : ℕ → ℤ) (k : ℕ) : ℝ :=
  A ^ (d - 1 - k) - ∑ j ∈ Finset.Ioo k d, (p j : ℝ) * A ^ (j - k - 1)

/-- **(proved).**  The leading coefficient `q_{d−1} = 1`. -/
theorem quotCoeff_last (A : ℝ) {d : ℕ} (hd : 1 ≤ d) (p : ℕ → ℤ) :
    quotCoeff A d p (d - 1) = 1 := by
  unfold quotCoeff
  have : Finset.Ioo (d - 1) d = ∅ := by
    ext j; simp only [Finset.mem_Ioo, Finset.notMem_empty, iff_false]; omega
  rw [this, Finset.sum_empty, show d - 1 - (d - 1) = 0 by omega, pow_zero, sub_zero]

/-- **(helper, proved).**  Horner step: `q_k = A·q_{k+1} − p_{k+1}` for `k + 1 < d`.
Paper proof: split `j = k + 1` off `Ioo k d = insert (k+1) (Ioo (k+1) d)`; `A·A^{j−k−2} =
A^{j−k−1}`. -/
theorem quotCoeff_rec (A : ℝ) {d k : ℕ} (hk : k + 1 < d) (p : ℕ → ℤ) :
    quotCoeff A d p k = A * quotCoeff A d p (k + 1) - p (k + 1) := by
  unfold quotCoeff
  rw [← Finset.Ico_add_one_left_eq_Ioo k d, Finset.sum_eq_sum_Ico_succ_bot hk,
    Finset.Ico_add_one_left_eq_Ioo (k + 1) d]
  have h1 : A ^ (d - 1 - k) = A * A ^ (d - 1 - (k + 1)) := by
    rw [← pow_succ']; congr 1; omega
  have h2 : ∑ j ∈ Finset.Ioo (k + 1) d, (p j : ℝ) * A ^ (j - k - 1) =
      A * ∑ j ∈ Finset.Ioo (k + 1) d, (p j : ℝ) * A ^ (j - (k + 1) - 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_Ioo] at hj
    rw [show j - k - 1 = j - (k + 1) - 1 + 1 by omega, pow_succ]
    ring
  rw [h1, h2, show k + 1 - k - 1 = 0 by omega]
  ring

/-- **(helper, proved).**  `A·q_0 = P(A) + p_0` (for `1 ≤ d`).  Paper proof: as
`quotCoeff_rec`, with `range d = insert 0 (Ioo 0 d)`. -/
theorem mul_quotCoeff_zero (A : ℝ) {d : ℕ} (hd : 1 ≤ d) (p : ℕ → ℤ) :
    A * quotCoeff A d p 0 = (A ^ d - ∑ j ∈ Finset.range d, (p j : ℝ) * A ^ j) + p 0 := by
  unfold quotCoeff
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < d),
    Finset.Ico_add_one_left_eq_Ioo 0 d]
  have h1 : A * A ^ (d - 1 - 0) = A ^ d := by
    rw [← pow_succ']; congr 1; omega
  have h2 : A * ∑ j ∈ Finset.Ioo 0 d, (p j : ℝ) * A ^ (j - 0 - 1) =
      ∑ j ∈ Finset.Ioo 0 d, (p j : ℝ) * A ^ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_Ioo] at hj
    rw [show A ^ j = A * A ^ (j - 0 - 1) by rw [← pow_succ']; congr 1; omega]
    ring
  rw [mul_sub, h1, h2]
  simp
  ring

/-- **(proved).**  The phase identity, for **any** real sequence `v`:
`v_d − Σ_{j<d} p_j v_j = P(A)·v_0 − Σ_{i<d} q_i (A v_i − v_{i+1})`.  Paper proof: expand the
right sum as `Σ_i (A q_i − q_{i−1}) v_i − q_{d−1} v_d` (`q_{−1} := 0`,
`Finset.sum_range_succ_sub_sum`-style reindexing) and use `mul_quotCoeff_zero`,
`quotCoeff_rec` (`A q_i − q_{i−1} = p_i` for `1 ≤ i < d`) and `quotCoeff_last`; `d = 0` is
`v_0 = v_0`. -/
theorem phase_identity (A : ℝ) (d : ℕ) (p : ℕ → ℤ) (v : ℕ → ℝ) :
    v d - ∑ j ∈ Finset.range d, (p j : ℝ) * v j =
      (A ^ d - ∑ j ∈ Finset.range d, (p j : ℝ) * A ^ j) * v 0 -
        ∑ i ∈ Finset.range d, quotCoeff A d p i * (A * v i - v (i + 1)) := by
  rcases d with _ | m
  · simp
  have hl : quotCoeff A (m + 1) p m = 1 := by
    simpa using quotCoeff_last A (d := m + 1) (by omega) p
  have h0 := mul_quotCoeff_zero A (d := m + 1) (by omega) p
  set q := quotCoeff A (m + 1) p with hqdef
  set P := A ^ (m + 1) - ∑ j ∈ Finset.range (m + 1), (p j : ℝ) * A ^ j
  have hsplit : ∑ i ∈ Finset.range (m + 1), q i * (A * v i - v (i + 1)) =
      ∑ i ∈ Finset.range (m + 1), A * q i * v i -
        ∑ i ∈ Finset.range (m + 1), q i * v (i + 1) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hrec : ∑ i ∈ Finset.range m, A * q (i + 1) * v (i + 1) =
      ∑ i ∈ Finset.range m, q i * v (i + 1) +
        ∑ i ∈ Finset.range m, (p (i + 1) : ℝ) * v (i + 1) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [hqdef, quotCoeff_rec A (by omega : i + 1 < m + 1) p]
    ring
  rw [hsplit, Finset.sum_range_succ' (fun i => A * q i * v i), hrec,
    Finset.sum_range_succ (fun i => q i * v (i + 1)), hl,
    Finset.sum_range_succ' (fun j => (p j : ℝ) * v j)]
  linear_combination v 0 * h0

/-- **(proved).**  The `q_k` are the coefficients of the quotient:
`(t − A)·Σ_{k<d} q_k t^k = P(t) − P(A)`.  Proof: `phase_identity` with `v_i = tⁱ`, where
`A tⁱ − t^{i+1} = −(t − A)tⁱ`.  (Stated after `phase_identity` for that reason.) -/
theorem sub_mul_sum_quotCoeff (A t : ℝ) (d : ℕ) (p : ℕ → ℤ) :
    (t - A) * ∑ k ∈ Finset.range d, quotCoeff A d p k * t ^ k =
      (t ^ d - ∑ j ∈ Finset.range d, (p j : ℝ) * t ^ j) -
        (A ^ d - ∑ j ∈ Finset.range d, (p j : ℝ) * A ^ j) := by
  have h := phase_identity A d p (fun i => t ^ i)
  simp only [pow_zero, mul_one] at h
  have h2 : ∑ i ∈ Finset.range d, quotCoeff A d p i * (A * t ^ i - t ^ (i + 1)) =
      -((t - A) * ∑ k ∈ Finset.range d, quotCoeff A d p k * t ^ k) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h2] at h
  linarith

/-! ## Phases and the identity on `E^d` -/

/-- **(proved).**  On an even point `W(v) = ⌊A v⌋`, `A = α/2`. -/
theorem wy_of_even (α : ℝ) {v : ℤ} (h : v % 2 = 0) : wy α v = ⌊α / 2 * (v : ℝ)⌋ := by
  obtain ⟨k, rfl⟩ : ∃ k, v = 2 * k := ⟨v / 2, by omega⟩
  rw [wy_two_mul]
  congr 1
  push_cast
  ring

/-- The phase of the `(i + 1)`-st step: `f_{i+1} = A·Wⁱ(n) − W^{i+1}(n)`, `A = α/2`. -/
noncomputable def ePhase (α : ℝ) (n : ℤ) (i : ℕ) : ℝ :=
  α / 2 * ((wy α)^[i] n : ℝ) - ((wy α)^[i + 1] n : ℝ)

/-- **(proved).**  After an even point the phase is a fractional part. -/
theorem ePhase_eq_fract {α : ℝ} {n : ℤ} {i : ℕ} (h : (wy α)^[i] n % 2 = 0) :
    ePhase α n i = Int.fract (α / 2 * ((wy α)^[i] n : ℝ)) := by
  unfold ePhase
  rw [Function.iterate_succ_apply', wy_of_even α h, Int.fract]

/-- **(proved).**  After an even point the phase lies in `[0, 1)`. -/
theorem ePhase_mem {α : ℝ} {n : ℤ} {i : ℕ} (h : (wy α)^[i] n % 2 = 0) :
    0 ≤ ePhase α n i ∧ ePhase α n i < 1 := by
  rw [ePhase_eq_fract h]
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- helper: the integer `W^d − Σ p_j W^j` equals `X − f_{d−1}` -/
theorem wy_iterate_sub_eq {α : ℝ} {m : ℕ} {p : ℕ → ℤ}
    (hP : (α / 2) ^ (m + 1) = ∑ j ∈ Finset.range (m + 1), (p j : ℝ) * (α / 2) ^ j) (n : ℤ) :
    (((wy α)^[m + 1] n - ∑ j ∈ Finset.range (m + 1), p j * (wy α)^[j] n : ℤ) : ℝ) =
      -∑ i ∈ Finset.range m, quotCoeff (α / 2) (m + 1) p i * ePhase α n i - ePhase α n m := by
  have h := phase_identity (α / 2) (m + 1) p (fun i => ((wy α)^[i] n : ℝ))
  have hl : quotCoeff (α / 2) (m + 1) p m = 1 := by
    simpa using quotCoeff_last (α / 2) (d := m + 1) (by omega) p
  rw [hP, sub_self, zero_mul, zero_sub, Finset.sum_range_succ (fun i =>
    quotCoeff (α / 2) (m + 1) p i * (α / 2 * ((wy α)^[i] n : ℝ) - ((wy α)^[i + 1] n : ℝ))),
    hl, one_mul] at h
  push_cast
  rw [h]
  simp only [ePhase]
  ring

/-- **(proved; the degree-`d` identity).**  If `A = α/2` satisfies `A^d = Σ_{j<d} p_j A^j`
and `n, W n, …, W^{d−1} n` are even, then
`W^d(n) = Σ_{j<d} p_j W^j(n) + ⌊−Σ_{i<d−1} q_i f_{i+1}⌋`, for any real `α` and `n ∈ ℤ`.  Paper
proof: `phase_identity` with `v_i = Wⁱ(n)` (cast), `P(A) = 0`; split off `i = d − 1`
(`quotCoeff_last`, `d ≥ 1` since `d = 0` contradicts `hP`), so the integer
`W^d − Σ p_j W^j` equals `X − f_d` with `f_d = ePhase α n (d − 1) ∈ [0, 1)` (`ePhase_mem`);
`Int.floor_eq_iff`. -/
theorem wy_iterate_eq_floor {α : ℝ} {d : ℕ} {p : ℕ → ℤ}
    (hP : (α / 2) ^ d = ∑ j ∈ Finset.range d, (p j : ℝ) * (α / 2) ^ j) {n : ℤ}
    (hE : ∀ i < d, (wy α)^[i] n % 2 = 0) :
    (wy α)^[d] n = ∑ j ∈ Finset.range d, p j * (wy α)^[j] n +
      ⌊-∑ i ∈ Finset.range (d - 1), quotCoeff (α / 2) d p i * ePhase α n i⌋ := by
  rcases d with _ | m
  · simp at hP
  have h := wy_iterate_sub_eq hP n
  obtain ⟨hf0, hf1⟩ := ePhase_mem (hE m (by omega))
  have hfl : ⌊-∑ i ∈ Finset.range m, quotCoeff (α / 2) (m + 1) p i * ePhase α n i⌋ =
      (wy α)^[m + 1] n - ∑ j ∈ Finset.range (m + 1), p j * (wy α)^[j] n := by
    rw [Int.floor_eq_iff, h]
    constructor <;> linarith
  simp only [Nat.add_sub_cancel, hfl]
  ring

/-! ## The trap -/

/-- **(proved; exact identity).**  If moreover `q_k ≤ 0` for `k < d − 1` and
`Q(1) = Σ_{k<d} q_k ≥ 0`, then `W^d(n) = Σ_{j<d} p_j W^j(n)` on `E^d`.  Paper proof:
`X = Σ_{i<d−1} (−q_i) f_{i+1} ≥ 0`; with `F = max_i f_{i+1} < 1`,
`X ≤ F·Σ_{i<d−1}(−q_i) = F·(1 − Q(1)) ≤ F < 1` (`quotCoeff_last`: `Q(1) = 1 + Σ_{i<d−1} q_i`;
for `d = 1` the sum is empty), so `⌊X⌋ = 0` (`Int.floor_eq_zero_iff`). -/
theorem wy_iterate_eq_of_trap {α : ℝ} {d : ℕ} {p : ℕ → ℤ}
    (hP : (α / 2) ^ d = ∑ j ∈ Finset.range d, (p j : ℝ) * (α / 2) ^ j)
    (hq : ∀ k < d - 1, quotCoeff (α / 2) d p k ≤ 0)
    (hQ : 0 ≤ ∑ k ∈ Finset.range d, quotCoeff (α / 2) d p k) {n : ℤ}
    (hE : ∀ i < d, (wy α)^[i] n % 2 = 0) :
    (wy α)^[d] n = ∑ j ∈ Finset.range d, p j * (wy α)^[j] n := by
  rw [wy_iterate_eq_floor hP hE]
  rcases d with _ | m
  · simp at hP
  simp only [Nat.add_sub_cancel] at hq ⊢
  set q := quotCoeff (α / 2) (m + 1) p
  have hl : q m = 1 := by simpa using quotCoeff_last (α / 2) (d := m + 1) (by omega) p
  rw [Finset.sum_range_succ, hl] at hQ
  have hf : ∀ i ∈ Finset.range m, 0 ≤ ePhase α n i ∧ ePhase α n i < 1 := fun i hi =>
    ePhase_mem (hE i (by rw [Finset.mem_range] at hi; omega))
  have hX : -∑ i ∈ Finset.range m, q i * ePhase α n i =
      ∑ i ∈ Finset.range m, -q i * ePhase α n i := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  have hS : ∑ i ∈ Finset.range m, -q i ≤ 1 := by
    rw [Finset.sum_neg_distrib]; linarith
  have hX0 : 0 ≤ ∑ i ∈ Finset.range m, -q i * ePhase α n i :=
    Finset.sum_nonneg fun i hi => mul_nonneg (by
      have := hq i (by rw [Finset.mem_range] at hi; omega); linarith) (hf i hi).1
  have hgap : ∑ i ∈ Finset.range m, -q i * ePhase α n i =
      ∑ i ∈ Finset.range m, -q i - ∑ i ∈ Finset.range m, -q i * (1 - ePhase α n i) := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  have hg0 : ∀ i ∈ Finset.range m, 0 ≤ -q i * (1 - ePhase α n i) := fun i hi =>
    mul_nonneg (by have := hq i (by rw [Finset.mem_range] at hi; omega); linarith)
      (by linarith [(hf i hi).2])
  have hX1 : ∑ i ∈ Finset.range m, -q i * ePhase α n i < 1 := by
    rcases hS.lt_or_eq with hS | hS
    · rw [hgap]; linarith [Finset.sum_nonneg hg0]
    · obtain ⟨i, hi, hqi⟩ : ∃ i ∈ Finset.range m, 0 < -q i := by
        by_contra hcon
        simp only [not_exists, not_and, not_lt] at hcon
        linarith [Finset.sum_nonpos hcon]
      have : 0 < ∑ i ∈ Finset.range m, -q i * (1 - ePhase α n i) :=
        Finset.sum_pos' hg0 ⟨i, hi, mul_pos hqi (by linarith [(hf i hi).2])⟩
      rw [hgap]; linarith
  rw [hX, Int.floor_eq_zero_iff.2 ⟨hX0, hX1⟩, add_zero]

/-- The trap `T_d = {n > 0 : n, W n, …, W^{d−1} n even}`. -/
def trapSetD (α : ℝ) (d : ℕ) : Set ℤ :=
  {n | 0 < n ∧ ∀ i < d, (wy α)^[i] n % 2 = 0}

/-- **(proved; trap).**  `W(T_d) ⊆ T_d`.  Paper proof: for `n ∈ T_d`, `W n > 0`
(`wy_pos_iff`); `W^i(W n) = W^{i+1} n` is even for `i + 1 < d` by hypothesis and for
`i + 1 = d` by `wy_iterate_eq_of_trap` (a `ℤ`-combination of evens); `d = 0` contradicts
`hP`. -/
theorem trapSetD_trap {α : ℝ} (hα : 1 < α) {d : ℕ} {p : ℕ → ℤ}
    (hP : (α / 2) ^ d = ∑ j ∈ Finset.range d, (p j : ℝ) * (α / 2) ^ j)
    (hq : ∀ k < d - 1, quotCoeff (α / 2) d p k ≤ 0)
    (hQ : 0 ≤ ∑ k ∈ Finset.range d, quotCoeff (α / 2) d p k) :
    ∀ n ∈ trapSetD α d, wyPerm α hα n ∈ trapSetD α d := by
  rintro n ⟨hn, hE⟩
  rw [wyPerm_apply]
  refine ⟨(wy_pos_iff hα n).2 hn, fun i hi => ?_⟩
  rw [← Function.iterate_succ_apply]
  rcases Nat.lt_or_ge (i + 1) d with h | h
  · exact hE _ h
  · rw [show i.succ = d by omega, wy_iterate_eq_of_trap hP hq hQ hE]
    apply Int.emod_eq_zero_of_dvd
    refine Finset.dvd_sum fun j hj => Dvd.dvd.mul_left ?_ _
    exact Int.dvd_of_emod_eq_zero (hE j (Finset.mem_range.1 hj))

theorem trapSetD_iterate {α : ℝ} (hα : 1 < α) {d : ℕ} {p : ℕ → ℤ}
    (hP : (α / 2) ^ d = ∑ j ∈ Finset.range d, (p j : ℝ) * (α / 2) ^ j)
    (hq : ∀ k < d - 1, quotCoeff (α / 2) d p k ≤ 0)
    (hQ : 0 ≤ ∑ k ∈ Finset.range d, quotCoeff (α / 2) d p k) {n : ℤ}
    (hn : n ∈ trapSetD α d) (j : ℕ) : (wy α)^[j] n ∈ trapSetD α d := by
  induction j with
  | zero => exact hn
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact trapSetD_trap hα hP hq hQ _ ih

/-- **(proved; recurrence).**  Along the trap, `W^{j+d} = Σ_{i<d} p_i W^{j+i}`.  Paper
proof: `Wʲ n ∈ T_d` (induction with `trapSetD_trap`), then `wy_iterate_eq_of_trap` at `Wʲ n`
(`Function.iterate_add_apply`). -/
theorem wy_iterate_add_of_mem_trapSetD {α : ℝ} (hα : 1 < α) {d : ℕ} {p : ℕ → ℤ}
    (hP : (α / 2) ^ d = ∑ j ∈ Finset.range d, (p j : ℝ) * (α / 2) ^ j)
    (hq : ∀ k < d - 1, quotCoeff (α / 2) d p k ≤ 0)
    (hQ : 0 ≤ ∑ k ∈ Finset.range d, quotCoeff (α / 2) d p k) {n : ℤ}
    (hn : n ∈ trapSetD α d) (j : ℕ) :
    (wy α)^[j + d] n = ∑ i ∈ Finset.range d, p i * (wy α)^[j + i] n := by
  have h := wy_iterate_eq_of_trap hP hq hQ (trapSetD_iterate hα hP hq hQ hn j).2
  simp only [← Function.iterate_add_apply] at h
  rw [add_comm j d, h]
  exact Finset.sum_congr rfl fun i _ => by rw [add_comm i j]

/-- **(drafted, 95%; infinitely many entry points, conditional on Weyl).**  For `α > 2` of
degree `d + 1` (`hind`) satisfying the trap conditions, `T_{d+1} ∖ W(T_{d+1})` is infinite.
Paper proof.  *Lower bound.*  For `k ≥ 1` put `φ_i = {k Aⁱ}`, `N_i = ⌊k Aⁱ⌋` (`1 ≤ i ≤ d`),
`ψ_i = φ_i − A φ_{i−1}` (`φ_0 = 0`).  If every `ψ_i ∈ [0, 1/2)` then `Wⁱ(2k) = 2N_i` for
`i ≤ d` (induction: `A·2N_{i−1} = 2(N_i + ψ_i)`, `wy_of_even`), so `2k ∈ T_{d+1}`.  The box
`B = Π_{i<d} [L_i, L_i + η)` with `L_0 = 0`, `L_{i+1} = A(L_i + η)`, `η = 1/(2(A + 2)^{d+1})`
lies in `[0, 1)^d` and forces every `ψ_i ∈ [0, (A + 1)η) ⊆ [0, 1/2)`.
`WeylEquidistributionMulti` with `θ_i = A^{i+1}` (`hind` gives the `Fin.cons 1 θ`
independence) gives `#{k ≤ N : φ(k) ∈ B} / N → η^d > 0`, so `#(T_{d+1} ∩ [1, X]) ≥ c X` for
large `X`.  *Upper bound if finite.*  On `T_{d+1}`, `W(t) ≥ (α/2)t − 1`; if the entry set `E`
were finite, every `t ∈ T_{d+1}` above the finitely many `t` with `W(t) ≤ t` would be a forward
iterate of a point of `E` (backward inside `T_{d+1}` the values decrease, as in
`WythoffCone.exists_entry`), and each forward orbit has `O(log X)` points `≤ X`.
Contradiction.  (`WythoffCone.coneEntry_infinite` is the `d = 1` model, with Dirichlet in place
of Weyl.) -/
theorem trapSetD_entry_infinite {α : ℝ} (hα : 2 < α) {d : ℕ} {p : ℕ → ℤ}
    (hP : (α / 2) ^ (d + 1) = ∑ j ∈ Finset.range (d + 1), (p j : ℝ) * (α / 2) ^ j)
    (hq : ∀ k < d, quotCoeff (α / 2) (d + 1) p k ≤ 0)
    (hQ : 0 ≤ ∑ k ∈ Finset.range (d + 1), quotCoeff (α / 2) (d + 1) p k)
    (hind : LinearIndependent ℚ fun i : Fin (d + 1) => (α / 2) ^ (i : ℕ))
    (hW : WeylEquidistributionMulti) :
    {n : ℤ | 0 ≤ n ∧
      n ∈ trapSetD α (d + 1) \ wyPerm α (one_lt_two.trans hα) '' trapSetD α (d + 1)}.Infinite := by
  sorry

/-- **(proved from the two above; conditional on Weyl).**  Every member as in
`trapSetD_entry_infinite` has infinitely many infinite orbits:
`infinitelyManyInfiniteOrbits_of_trap` with `trapSetD_trap` and `trapSetD_entry_infinite`. -/
theorem wyPerm_infinitelyManyInfiniteOrbits_of_trapD {α : ℝ} (hα : 2 < α) {d : ℕ} {p : ℕ → ℤ}
    (hP : (α / 2) ^ (d + 1) = ∑ j ∈ Finset.range (d + 1), (p j : ℝ) * (α / 2) ^ j)
    (hq : ∀ k < d, quotCoeff (α / 2) (d + 1) p k ≤ 0)
    (hQ : 0 ≤ ∑ k ∈ Finset.range (d + 1), quotCoeff (α / 2) (d + 1) p k)
    (hind : LinearIndependent ℚ fun i : Fin (d + 1) => (α / 2) ^ (i : ℕ))
    (hW : WeylEquidistributionMulti) :
    InfinitelyManyInfiniteOrbits (wyPerm α (one_lt_two.trans hα)) :=
  infinitelyManyInfiniteOrbits_of_trap _ (trapSetD_trap _ hP (by simpa using hq) hQ)
    (trapSetD_entry_infinite hα hP hq hQ hind hW)

/-! ## `d = 2`: Theorem A′ and the E-cone -/

/-- **(proved).**  `q_0 = A − p_1` at `d = 2`. -/
theorem quotCoeff_two (A : ℝ) (p : ℕ → ℤ) : quotCoeff A 2 p 0 = A - p 1 := by
  unfold quotCoeff
  rw [show Finset.Ioo 0 2 = {1} by decide]
  simp

/-- **(proved; consistency with Theorem A′).**  The identity at `d = 2`, `p = (c, b)`, is
`WythoffCone.wy_wy_of_even_even`.  Prove it **from** `wy_iterate_eq_floor` (not by citing
Theorem A′), so that it checks the general statement: `p 0 = c`, `p 1 = b`, `quotCoeff_two`,
`ePhase_eq_fract` at `i = 0` with `α/2·(2k) = kα`, and `⌊−(A − b)f⌋ = ⌊(b − A)f⌋`. -/
theorem wy_iterate_two_eq_floor {α : ℝ} {b c : ℤ} (hx : (α / 2) ^ 2 = b * (α / 2) + c) (k : ℤ)
    (h : wy α (2 * k) % 2 = 0) :
    (wy α)^[2] (2 * k) =
      b * wy α (2 * k) + c * (2 * k) + ⌊((b : ℝ) - α / 2) * Int.fract ((k : ℝ) * α)⌋ := by
  set p : ℕ → ℤ := fun j => if j = 0 then c else b with hp
  have hP : (α / 2) ^ 2 = ∑ j ∈ Finset.range 2, (p j : ℝ) * (α / 2) ^ j := by
    simp [Finset.sum_range_succ, hp, hx]; ring
  have hE : ∀ i < 2, (wy α)^[i] (2 * k) % 2 = 0 := by
    intro i hi
    interval_cases i
    · simp
    · simpa using h
  rw [wy_iterate_eq_floor hP hE]
  have h0 : ePhase α (2 * k) 0 = Int.fract ((k : ℝ) * α) := by
    rw [ePhase_eq_fract (by simp)]
    congr 1
    simp
    ring
  simp [Finset.sum_range_succ, hp, quotCoeff_two, h0]
  ring_nf

/-- **(proved).**  `T_2` is the E-cone of Theorem K. -/
theorem trapSetD_two_alphaK (b c : ℤ) : trapSetD (alphaK b c) 2 = coneSet b c := by
  ext n
  simp only [trapSetD, coneSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h0, h⟩
    exact ⟨h0, h 0 (by norm_num), h 1 (by norm_num)⟩
  · rintro ⟨h0, h1, h2⟩
    refine ⟨h0, fun i hi => ?_⟩
    interval_cases i
    · exact h1
    · exact h2

/-! ## The cubic member `A³ = 3A² − 1` -/

/-- `t³ − 3t² + 1` changes sign on `[14/5, 29/10]` (IVT). -/
theorem exists_cRoot : ∃ x : ℝ, 14 / 5 < x ∧ x < 29 / 10 ∧ x ^ 3 = 3 * x ^ 2 - 1 := by
  have hc : ContinuousOn (fun x : ℝ => x ^ 3 - 3 * x ^ 2 + 1) (Set.Icc (14 / 5) (29 / 10)) := by
    fun_prop
  obtain ⟨x, ⟨h1, h2⟩, hx⟩ := intermediate_value_Icc (by norm_num) hc
    (show (0 : ℝ) ∈ Set.Icc _ _ by constructor <;> norm_num)
  simp only at hx
  refine ⟨x, lt_of_le_of_ne h1 ?_, lt_of_le_of_ne h2 ?_, by linarith⟩ <;> rintro rfl <;>
    norm_num at hx

open Classical in
/-- The root `A ∈ (14/5, 29/10)` of `A³ = 3A² − 1` (`cRoot_spec`), `A ≈ 2.8793852`. -/
noncomputable def cRoot : ℝ :=
  if h : ∃ x : ℝ, 14 / 5 < x ∧ x < 29 / 10 ∧ x ^ 3 = 3 * x ^ 2 - 1 then h.choose else 0

/-- `α = 2A ≈ 5.7587705`. -/
noncomputable def alphaC : ℝ :=
  2 * cRoot

/-- The coefficients `(p_0, p_1, p_2) = (−1, 0, 3)`: `A³ = 3A² + 0·A − 1`. -/
def cubicP : ℕ → ℤ
  | 0 => -1
  | 2 => 3
  | _ => 0

/-- **(proved).**  The root exists. -/
theorem cRoot_spec : 14 / 5 < cRoot ∧ cRoot < 29 / 10 ∧ cRoot ^ 3 = 3 * cRoot ^ 2 - 1 := by
  unfold cRoot
  rw [dif_pos exists_cRoot]
  exact exists_cRoot.choose_spec

/-- **(proved).**  Uniqueness above `2`: `t³ − 3t² + 1` is strictly increasing on `(2, ∞)`
(`F(b) − F(a) = (b − a)(a² + ab + b² − 3a − 3b)`, and the second factor is `> 0` for
`a, b > 2`). -/
theorem cRoot_unique {y : ℝ} (hy : 2 < y) (h : y ^ 3 = 3 * y ^ 2 - 1) : y = cRoot := by
  obtain ⟨h1, -, h3⟩ := cRoot_spec
  have key : ∀ a b : ℝ, 2 < a → 2 < b → a < b → a ^ 3 - 3 * a ^ 2 < b ^ 3 - 3 * b ^ 2 := by
    intro a b ha hb hab
    have hpos : 0 < a ^ 2 + a * b + b ^ 2 - 3 * a - 3 * b := by nlinarith
    nlinarith [mul_pos (sub_pos.2 hab) hpos]
  rcases lt_trichotomy y cRoot with hl | he | hl
  · have := key _ _ hy (by linarith) hl; linarith
  · exact he
  · have := key _ _ (by linarith) hy hl; linarith

/-- **(proved).**  `α/2 = A`. -/
theorem alphaC_half : alphaC / 2 = cRoot := by
  unfold alphaC; ring

/-- **(proved).**  `α > 2` (indeed `α > 28/5`). -/
theorem two_lt_alphaC : 2 < alphaC := by
  unfold alphaC; linarith [cRoot_spec.1]

/-- `W_α` for the cubic member, as a permutation of `ℤ`. -/
noncomputable def cubicPerm : Equiv.Perm ℤ :=
  wyPerm alphaC (one_lt_two.trans two_lt_alphaC)

theorem cubicPerm_apply (n : ℤ) : cubicPerm n = wy alphaC n := rfl

/-- **(proved).**  The polynomial hypothesis `A³ = Σ_{j<3} p_j Aʲ`. -/
theorem alphaC_pow :
    (alphaC / 2) ^ 3 = ∑ j ∈ Finset.range 3, (cubicP j : ℝ) * (alphaC / 2) ^ j := by
  rw [alphaC_half, cRoot_spec.2.2]
  simp [Finset.sum_range_succ, cubicP]
  ring

/-- **(proved).**  `q_0 = A² − 3A`, `q_1 = A − 3`, `q_2 = 1`. -/
theorem quotCoeff_cubic (A : ℝ) :
    quotCoeff A 3 cubicP 0 = A ^ 2 - 3 * A ∧ quotCoeff A 3 cubicP 1 = A - 3 ∧
      quotCoeff A 3 cubicP 2 = 1 := by
  unfold quotCoeff
  rw [show Finset.Ioo 0 3 = {1, 2} by decide, show Finset.Ioo 1 3 = {2} by decide,
    show Finset.Ioo 2 3 = ∅ by decide]
  simp [cubicP]

/-- **(proved).**  The sign conditions: `q_0 = A(A − 3) < 0`, `q_1 = A − 3 < 0`, and
`Q(1) = A² − 2A − 2 > 0` (`A > 1 + √3`; `A > 14/5` suffices). -/
theorem quotCoeff_cubic_signs :
    (∀ k < 3 - 1, quotCoeff (alphaC / 2) 3 cubicP k ≤ 0) ∧
      0 < ∑ k ∈ Finset.range 3, quotCoeff (alphaC / 2) 3 cubicP k := by
  obtain ⟨h0, h1, h2⟩ := quotCoeff_cubic (alphaC / 2)
  obtain ⟨hl, hu, -⟩ := cRoot_spec
  rw [alphaC_half] at h0 h1 h2 ⊢
  refine ⟨fun k hk => ?_, ?_⟩
  · interval_cases k
    · rw [h0]; nlinarith
    · rw [h1]; linarith
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, h0, h1, h2]
    nlinarith

/-- **(proved from `wy_iterate_eq_of_trap`; the cubic identity).**  On `EEE`,
`W³(n) = 3W²(n) − n`, for every `n ∈ ℤ`: `wy_iterate_eq_of_trap` with `alphaC_pow` and
`quotCoeff_cubic_signs`; expand `Σ_{j<3} p_j Wʲ = −n + 3W²`. -/
theorem wy_iterate_three_cubic {n : ℤ} (hE : ∀ i < 3, (wy alphaC)^[i] n % 2 = 0) :
    (wy alphaC)^[3] n = 3 * (wy alphaC)^[2] n - n := by
  rw [wy_iterate_eq_of_trap alphaC_pow quotCoeff_cubic_signs.1 quotCoeff_cubic_signs.2.le hE]
  simp [Finset.sum_range_succ, cubicP]
  ring

/-- **(proved from `trapSetD_trap`; the cubic trap).**  `W(T_3) ⊆ T_3`. -/
theorem cubicSet_trap : ∀ n ∈ trapSetD alphaC 3, cubicPerm n ∈ trapSetD alphaC 3 :=
  trapSetD_trap _ alphaC_pow quotCoeff_cubic_signs.1 quotCoeff_cubic_signs.2.le

/-- The cubic `t³ − 3t² + 1` has no rational root (a rational root of the monic integer cubic
is an integer dividing `1`, and `F(1) = −1`, `F(−1) = −3`). -/
theorem cCubic_ne_zero_rat (q : ℚ) : q ^ 3 - 3 * q ^ 2 + 1 ≠ 0 := by
  intro h
  have hmon : (X ^ 3 - C 3 * X ^ 2 + 1 : ℤ[X]).Monic := by monicity!
  have hr : aeval q (X ^ 3 - C 3 * X ^ 2 + 1 : ℤ[X]) = 0 := by
    simp only [map_sub, map_add, map_pow, map_mul, aeval_X, aeval_C, map_one]
    simpa using h
  obtain ⟨z, hz⟩ := isInteger_of_is_root_of_monic hmon hr
  have hz' : (z : ℚ) = q := hz
  subst hz'
  have hz3 : z ^ 3 - 3 * z ^ 2 + 1 = 0 := by exact_mod_cast h
  have hdvd : z ∣ 1 := ⟨3 * z - z ^ 2, by linear_combination hz3⟩
  rcases Int.isUnit_iff.1 (isUnit_of_dvd_one hdvd) with rfl | rfl <;> norm_num at hz3

theorem natDegree_cCubic : (X ^ 3 - C 3 * X ^ 2 + 1 : ℚ[X]).natDegree = 3 := by
  compute_degree!

/-- **(proved).**  `deg A = 3`: `1, A, A²` are `ℚ`-independent.  Paper proof: as
`WythoffSporadic.linearIndependent_yRoot` (`cCubic_ne_zero_rat`,
`Polynomial.irreducible_of_degree_le_three_of_not_isRoot`, `minpoly.eq_of_irreducible_of_monic`,
`linearIndependent_pow`). -/
theorem linearIndependent_cRoot : LinearIndependent ℚ fun i : Fin 3 => cRoot ^ (i : ℕ) := by
  have hirr : Irreducible (X ^ 3 - C 3 * X ^ 2 + 1 : ℚ[X]) := by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · rw [natDegree_cCubic]; decide
    · intro q hq
      apply cCubic_ne_zero_rat q
      simpa using hq
  have hmin : (X ^ 3 - C 3 * X ^ 2 + 1 : ℚ[X]) = minpoly ℚ cRoot := by
    apply minpoly.eq_of_irreducible_of_monic hirr
    · simp only [map_sub, map_add, map_pow, map_mul, aeval_X, aeval_C, map_one]
      have := cRoot_spec.2.2
      simp only [eq_ratCast, Rat.cast_ofNat]
      linarith
    · monicity!
  have h := linearIndependent_pow (K := ℚ) cRoot
  rw [← hmin, natDegree_cCubic] at h
  exact h

/-- **(proved from `wyPerm_infinitelyManyInfiniteOrbits_of_trapD`; conditional on Weyl).**  The
cubic member has infinitely many infinite orbits.  Paper proof:
`wyPerm_infinitelyManyInfiniteOrbits_of_trapD` at `d + 1 = 3` with
`two_lt_alphaC`, `alphaC_pow`, `quotCoeff_cubic_signs`, `linearIndependent_cRoot`
(`alphaC_half`). -/
theorem cubicPerm_infinitelyManyInfiniteOrbits (hW : WeylEquidistributionMulti) :
    InfinitelyManyInfiniteOrbits cubicPerm := by
  have hind : LinearIndependent ℚ fun i : Fin (2 + 1) => (alphaC / 2) ^ (i : ℕ) := by
    rw [alphaC_half]; exact linearIndependent_cRoot
  exact wyPerm_infinitelyManyInfiniteOrbits_of_trapD (d := 2) two_lt_alphaC alphaC_pow
    quotCoeff_cubic_signs.1 quotCoeff_cubic_signs.2.le hind hW

end CollatzMoonshot.WythoffTrapDegree
