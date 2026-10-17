/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.WythoffPisot

/-!
# The run criterion from Weyl (`RunCriterion` is a theorem modulo `WeylEquidistributionMulti`)

Research notes `wythoff-classify` §1-§2 (Theorem N, the zonotope criterion, Theorem N4) and
`wythoff-pisot` §1 (the half-scale run system), with the notation of `WythoffAutomaton` and
`WythoffPisot`.  Let `α > 1`, `x = xOf α = β/2`, `P` monic of degree `d ≥ 2` with `P(x) = 0`,
`q_k = synDiv P x k`, and for an even up-point `u = 2k` let `w_j = W^j(u) + 1`.

**Phase coordinates** (`phaseVec`).  `ε_0 = G_E(u)/2` and `ε_l = G(W^l u)/2` for `l ≥ 1`, the
half-scale phases (`evenPhase`, `oddPhase`).  Three exact identities, none needing a parity
hypothesis:
* *Standard rows* (`two_mul_stdRow_phaseVec`).  For `i ≥ 1`,
  `2R_i(ε) = Σ_{j ≤ d} a_j w_{i+j}`: `sum_coeff_iterate_eq` started at `W^i u`.
* *Top row* (`two_mul_topRow_phaseVec`).
  `2T(ε) = Σ_{1≤j≤d} a_j w_j + 2a_0 w_1 − a_0 u`: the identity behind `first_step_eq_ceil`
  (virtual `w_0 = u(α − 1)`, `x w_0 = (α/2)u`).
* *Fresh steps* (`half_iterate_eq`).  `w_{l+1}/2 = kθ_l + Σ_{j ≤ l} x^{l−j} ε_j` with the
  **frequencies** `θ_l = (α/2)x^l` (`freqVec`): unroll `w_{j+1} = x w_j + G_{j+1}`.

So, along a run, the step-`(l+1)` parity is: for `l < d − 1` (fresh steps) "`kθ_l + Σ` is an
integer" (`iterate_odd_iff_fresh`); for `l = d − 1` "the top row is an integer"
(`topRow_phaseVec_int_iff`); for `l ≥ d` "the standard row `R_{l−d+1}` is an integer"
(`stdRow_phaseVec_int_iff`).  The exact correspondence (`runSystem_phaseVec_iff`): given the
fresh steps `W^1 u, …, W^{d−1} u` odd, `W^1 u, …, W^n u` are all odd iff the phase vector of `u`
solves `RunSystem` of length `n ≥ d` (for irrational `α`, which keeps the phases off the box
boundary; the direction "solves ⇒ odd", `iterate_odd_of_runSystem`, needs no irrationality).

**Weyl** (`linearIndependent_freqVec`, `setOf_fract_mem_openBox_infinite`).  `1, θ_0, …, θ_{d−2}`
are `ℚ`-independent: multiplying a relation by `2x − 1` (`α/2 = x/(2x − 1)`) gives a rational
polynomial of degree `≤ d − 1` vanishing at `x`, and `x` has degree `d` (`P` irreducible).  So
`WeylEquidistributionMulti` puts a positive proportion of the `k` with `({kθ_l})_l` in any open
box of positive volume.

**Openness** (`exists_runBox`, the zonotope "relatively open" step done dynamically).  Let `ε*`
solve `RunSystem` of length `n ≥ d`, with margin `μ = min_{l<n} min(ε*_l, 1/2 − ε*_l) > 0`.  Put
`f_l = {−Σ_{j ≤ l} x^{l−j} ε*_j}` (`boxCorner`).  For `r > 0` small enough, every `k` with
`{kθ_l} ∈ (f_l, f_l + r)` for all `l < d − 1` has `W^1(2k), …, W^n(2k)` odd.  *Proof.*
Induction on `l < n`: `W^{l+1}(2k)` is odd and `|ε_l − ε*_l| < η_l` (`ε` = phase vector of `2k`),
with `η_l` growing geometrically and `η_{n−1} < μ`.  At a fresh step,
`w_{l+1}/2 − (integer) = s + (ε_l − ε*_l) + E` with `s ∈ (0, r)` from the box and
`|E| ≤ Σ_{j<l} x^{l−j}η_j`; at a row step, `R(ε) − R(ε*) = (ε_l − ε*_l) + E` (the coefficient of
`ε_l` is `q_{d−1} = 1`) with `|E| ≤ Σ|q_k|η_{l−d+1+k}`.  Either way the left side lies in `½ℤ`
and `ε_l ∈ [0, 1/2]`, so `half_int_pin` forces it to be `0`: the step is odd, and
`|ε_l − ε*_l| ≤ r + |E|`.

**Headline** (`runCriterion_of_weyl`).  `WeylEquidistributionMulti → WythoffPisot.RunCriterion`,
exactly as stated there.  **Corollary** (`n3_infinite_runs_of_weyl`): Theorem N3's headline
conditional on `WeylEquidistributionMulti` alone.

Truth checks: `tmp/drafter-runcrit/check.py` (gitignored; exact `W` via certified floors).
-/

namespace CollatzMoonshot.WythoffRunCriterion

open CollatzMoonshot.WythoffGeneral CollatzMoonshot.WythoffAutomaton
  CollatzMoonshot.WythoffPisot Polynomial Filter Topology MeasureTheory

/-! ## Definitions -/

/-- The half-scale phase vector of `u`: `ε_0 = G_E(u)/2`, `ε_l = G(W^l u)/2` for `l ≥ 1`. -/
noncomputable def phaseVec (α : ℝ) (u : ℤ) (l : ℕ) : ℝ :=
  if l = 0 then evenPhase α u / 2 else oddPhase α ((wy α)^[l] u) / 2

/-- The torus frequencies `θ_l = (α/2)·x^l`, `l < m`, `x = xOf α`. -/
noncomputable def freqVec (α : ℝ) (m : ℕ) : Fin m → ℝ :=
  fun l => α / 2 * xOf α ^ (l : ℕ)

/-- The corner of the target box: `f_l = {−Σ_{j ≤ l} x^{l−j} ε_j}`, `l < m`. -/
noncomputable def boxCorner (x : ℝ) (ε : ℕ → ℝ) (m : ℕ) : Fin m → ℝ :=
  fun l => Int.fract (-∑ j ∈ Finset.range ((l : ℕ) + 1), x ^ ((l : ℕ) - j) * ε j)

/-- The one-sided open box `Π_l (f_l, f_l + r)`. -/
def openBox {m : ℕ} (f : Fin m → ℝ) (r : ℝ) : Set (Fin m → ℝ) :=
  Set.univ.pi fun l => Set.Ioo (f l) (f l + r)

/-! ## Phase coordinates and the exact identities -/

section Phases

variable {α : ℝ} {P : ℤ[X]}

/-- **(proved).** -/
theorem phaseVec_zero (α : ℝ) (u : ℤ) : phaseVec α u 0 = evenPhase α u / 2 := if_pos rfl

/-- **(proved).** -/
theorem phaseVec_of_ne_zero (α : ℝ) (u : ℤ) {l : ℕ} (hl : l ≠ 0) :
    phaseVec α u l = oddPhase α ((wy α)^[l] u) / 2 := if_neg hl

/-- **(proved).**  For even `u`, `ε_0 ∈ (0, 1/2]` (`evenPhase_mem`). -/
theorem phaseVec_zero_mem {u : ℤ} (hu : u % 2 = 0) :
    0 < phaseVec α u 0 ∧ phaseVec α u 0 ≤ 1 / 2 := by
  rw [phaseVec_zero]
  obtain ⟨h0, h1⟩ := evenPhase_mem (α := α) hu
  constructor <;> linarith

/-- **(proved).**  For `l ≥ 1` with `W^l u` odd, `ε_l ∈ [0, 1/2)` (`oddPhase_mem`). -/
theorem phaseVec_mem_of_odd {u : ℤ} {l : ℕ} (hl : l ≠ 0) (hodd : (wy α)^[l] u % 2 = 1) :
    0 ≤ phaseVec α u l ∧ phaseVec α u l < 1 / 2 := by
  rw [phaseVec_of_ne_zero α u hl]
  obtain ⟨h0, h1⟩ := oddPhase_mem (α := α) hodd
  constructor <;> linarith

/-- **(proved; the standard rows).**  For `i ≥ 1` and every `u` (no parity hypothesis),
`2R_i(ε) = Σ_{j ≤ d} a_j (W^{i+j} u + 1)`.  Paper proof: `sum_coeff_iterate_eq` at `W^i u`
(`Function.iterate_add_apply`); every index `i + k ≥ 1`, so `ε_{i+k} = G(W^{i+k} u)/2`. -/
theorem two_mul_stdRow_phaseVec (hroot : aeval (xOf α) P = 0) (u : ℤ) {i : ℕ} (hi : 1 ≤ i) :
    2 * stdRow (synDiv P (xOf α)) P.natDegree (phaseVec α u) i =
      ∑ j ∈ Finset.range (P.natDegree + 1), (P.coeff j : ℝ) * (((wy α)^[i + j] u : ℝ) + 1) := by
  have h := sum_coeff_iterate_eq hroot ((wy α)^[i] u)
  have e1 : ∀ j, (wy α)^[j] ((wy α)^[i] u) = (wy α)^[i + j] u := fun j => by
    rw [← Function.iterate_add_apply, add_comm]
  simp only [e1] at h
  unfold stdRow
  rw [Finset.mul_sum, h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [phaseVec_of_ne_zero α u (by omega)]
  ring

/-- **(proved; the top row).**  For `α > 1`, `d ≥ 1` and every `u` (no parity hypothesis),
`2T(ε) = Σ_{1≤j≤d} a_j w_j + 2a_0 w_1 − a_0 u` (`w_j = W^j u + 1`).  Paper proof: the algebra of
`first_step_eq_ceil` without its last (ceiling) step: `sum_coeff_mul_eq_synDiv` on the virtual
sequence `w_0 = u(α − 1)` (`x w_0 = (α/2)u`, so `w_1 − x w_0 = G_E(u)`), and
`a_0 w_0 = −x q_0 u(α − 1)` regrouped against `2a_0 w_1 − a_0 u`. -/
theorem two_mul_topRow_phaseVec (hα : 1 < α) (hd : 1 ≤ P.natDegree)
    (hroot : aeval (xOf α) P = 0) (u : ℤ) :
    2 * topRow (synDiv P (xOf α)) P.natDegree (P.coeff 0) (phaseVec α u) =
      ∑ j ∈ Finset.Ico 1 (P.natDegree + 1), (P.coeff j : ℝ) * (((wy α)^[j] u : ℝ) + 1) +
        2 * (P.coeff 0 : ℝ) * ((wy α u : ℝ) + 1) - (P.coeff 0 : ℝ) * u := by
  set d := P.natDegree with hdd
  set x := xOf α with hxdef
  let w : ℕ → ℝ := fun j => if j = 0 then (u : ℝ) * (α - 1) else ((wy α)^[j] u : ℝ) + 1
  have h := sum_coeff_mul_eq_synDiv hroot w
  have hx : x * (α - 1) = α / 2 := by
    simp only [x, xOf]; have : α - 1 ≠ 0 := by linarith
    field_simp
  simp only [Finset.range_eq_Ico] at h
  rw [Finset.sum_eq_sum_Ico_succ_bot (show 0 < d + 1 by omega),
    Finset.sum_eq_sum_Ico_succ_bot (show 0 < d by omega)] at h
  have g0 : w (0 + 1) - x * w 0 = evenPhase α u := by
    simp only [w, if_pos rfl, evenPhase, Function.iterate_one, zero_add, if_neg one_ne_zero]
    linear_combination (-(u : ℝ)) * hx
  have gk : ∀ k, 1 ≤ k → w (k + 1) - x * w k = oddPhase α ((wy α)^[k] u) := by
    intro k hk
    simp only [w, if_neg (show k + 1 ≠ 0 by omega), if_neg (show k ≠ 0 by omega), oddPhase,
      Function.iterate_succ_apply']
    rfl
  have hL : ∑ j ∈ Finset.Ico (0 + 1) (d + 1), (P.coeff j : ℝ) * w j =
      ∑ j ∈ Finset.Ico 1 (d + 1), (P.coeff j : ℝ) * (((wy α)^[j] u : ℝ) + 1) :=
    Finset.sum_congr rfl fun j hj => by
      rw [Finset.mem_Ico] at hj; simp only [w, if_neg (show j ≠ 0 by omega)]
  have hR : ∑ k ∈ Finset.Ico (0 + 1) d, synDiv P x k * (w (k + 1) - x * w k) =
      ∑ k ∈ Finset.Ico 1 d, synDiv P x k * oddPhase α ((wy α)^[k] u) :=
    Finset.sum_congr rfl fun k hk => by rw [gk k (Finset.mem_Ico.1 hk).1]
  rw [g0, hL, hR, coeff_zero_eq_synDiv hroot] at h
  have hw0 : w 0 = (u : ℝ) * (α - 1) := if_pos rfl
  rw [hw0] at h
  have hT : ∑ k ∈ Finset.Ico 1 d, synDiv P x k * phaseVec α u k =
      (∑ k ∈ Finset.Ico 1 d, synDiv P x k * oddPhase α ((wy α)^[k] u)) / 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [phaseVec_of_ne_zero α u (by have := (Finset.mem_Ico.1 hk).1; omega)]
    ring
  unfold topRow
  rw [hT, phaseVec_zero, coeff_zero_eq_synDiv hroot]
  have hE : evenPhase α u = ((wy α u : ℤ) : ℝ) + 1 - α / 2 * u := rfl
  rw [hE] at h ⊢
  linear_combination -h

/-- **(proved; the fresh steps).**  For every `k ∈ ℤ` and `l` (no parity hypothesis),
`(W^{l+1}(2k) + 1)/2 = kθ_l + Σ_{j ≤ l} x^{l−j} ε_j` with `θ_l = (α/2)x^l`.  Paper proof:
induction on `l`; `l = 0` is the definition of `G_E` (`(α/2)·2k = kα`), and the step is the
definition of `G`: `w_{l+2} = x w_{l+1} + G(W^{l+1}(2k))`. -/
theorem half_iterate_eq (α : ℝ) (k : ℤ) (l : ℕ) :
    (((wy α)^[l + 1] (2 * k) : ℝ) + 1) / 2 =
      k * (α / 2 * xOf α ^ l) +
        ∑ j ∈ Finset.range (l + 1), xOf α ^ (l - j) * phaseVec α (2 * k) j := by
  induction l with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, Nat.sub_self, pow_zero, one_mul, mul_one,
      phaseVec_zero, Function.iterate_one, evenPhase]
    push_cast; ring
  | succ l ih =>
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, one_mul,
      phaseVec_of_ne_zero α _ (by omega)]
    have hs : ∑ j ∈ Finset.range (l + 1), xOf α ^ (l + 1 - j) * phaseVec α (2 * k) j =
        xOf α * ∑ j ∈ Finset.range (l + 1), xOf α ^ (l - j) * phaseVec α (2 * k) j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [show l + 1 - j = (l - j) + 1 by have := Finset.mem_range.1 hj; omega, pow_succ]
      ring
    rw [hs]
    unfold oddPhase
    rw [Function.iterate_succ_apply' (wy α) (l + 1)]
    linear_combination (xOf α) * ih

/-- **(proved).**  The fresh-step parity: `W^{l+1}(2k)` is odd iff
`kθ_l + Σ_{j ≤ l} x^{l−j} ε_j` is an integer.  Paper proof: `half_iterate_eq`; `(v + 1)/2 ∈ ℤ`
iff `v` is odd. -/
theorem iterate_odd_iff_fresh (α : ℝ) (k : ℤ) (l : ℕ) :
    (wy α)^[l + 1] (2 * k) % 2 = 1 ↔
      ∃ m : ℤ, (k : ℝ) * (α / 2 * xOf α ^ l) +
        ∑ j ∈ Finset.range (l + 1), xOf α ^ (l - j) * phaseVec α (2 * k) j = m := by
  rw [← half_iterate_eq]
  set v := (wy α)^[l + 1] (2 * k)
  constructor
  · intro h
    refine ⟨(v + 1) / 2, ?_⟩
    have e : v + 1 = 2 * ((v + 1) / 2) := by omega
    have e' : (v : ℝ) + 1 = 2 * (((v + 1) / 2 : ℤ) : ℝ) := by exact_mod_cast e
    rw [e']; ring
  · rintro ⟨m, hm⟩
    have e : (v : ℝ) + 1 = 2 * m := by linarith
    have e' : v + 1 = 2 * m := by exact_mod_cast e
    omega

end Phases

/-! ## The phase ⇔ parity correspondence -/

section Correspondence

variable {α : ℝ} {P : ℤ[X]}

/-- **(proved; the top-row parity).**  For `α > 1`, `P` monic of degree `d ≥ 2`, `u`
even and `W^1 u, …, W^{d−1} u` odd: the top row of the phase vector is an integer iff `W^d u` is
odd.  Paper proof: `two_mul_topRow_phaseVec` makes `2T(ε)` the integer
`N = w_d + Σ_{1≤j<d} a_j w_j + 2a_0 w_1 − a_0 u` (`a_d = 1`); `w_1, …, w_{d−1}` and `u` are even,
so `N ≡ w_d (mod 2)`, and `T ∈ ℤ ⟺ N` even `⟺ w_d` even (as in `first_step_odd_iff`). -/
theorem topRow_phaseVec_int_iff (hα : 1 < α) (hP : P.Monic) (hd : 2 ≤ P.natDegree)
    (hroot : aeval (xOf α) P = 0) {u : ℤ} (hu : u % 2 = 0)
    (hfresh : ∀ i : ℕ, 1 ≤ i → i < P.natDegree → (wy α)^[i] u % 2 = 1) :
    (∃ m : ℤ, topRow (synDiv P (xOf α)) P.natDegree (P.coeff 0) (phaseVec α u) = m) ↔
      (wy α)^[P.natDegree] u % 2 = 1 := by
  have hid := two_mul_topRow_phaseVec hα (by omega) hroot u
  set N : ℤ := ∑ j ∈ Finset.Ico 1 (P.natDegree + 1), P.coeff j * ((wy α)^[j] u + 1) +
      2 * P.coeff 0 * (wy α u + 1) - P.coeff 0 * u with hNdef
  have hN : 2 * topRow (synDiv P (xOf α)) P.natDegree (P.coeff 0) (phaseVec α u) = (N : ℝ) := by
    rw [hid, hNdef]; push_cast; ring
  have hpar : N % 2 = ((wy α)^[P.natDegree] u + 1) % 2 := by
    rw [hNdef, Finset.sum_Ico_succ_top (by omega), hP.coeff_natDegree, one_mul]
    have hev : (2 : ℤ) ∣ ∑ j ∈ Finset.Ico 1 P.natDegree, P.coeff j * ((wy α)^[j] u + 1) :=
      Finset.dvd_sum fun j hj => Dvd.dvd.mul_left (by
        have := hfresh j (Finset.mem_Ico.1 hj).1 (Finset.mem_Ico.1 hj).2; omega) _
    have hn' : (2 : ℤ) ∣ P.coeff 0 * u := Dvd.dvd.mul_left (by omega) _
    have h2 : (2 : ℤ) ∣ 2 * P.coeff 0 * (wy α u + 1) := ⟨_, mul_assoc _ _ _⟩
    generalize ∑ j ∈ Finset.Ico 1 P.natDegree, P.coeff j * ((wy α)^[j] u + 1) = S at hev ⊢
    generalize P.coeff 0 * u = T at hn' ⊢
    generalize 2 * P.coeff 0 * (wy α u + 1) = U at h2 ⊢
    omega
  constructor
  · rintro ⟨m, hm⟩
    have h' : (N : ℝ) = ((2 * m : ℤ) : ℝ) := by rw [← hN, hm]; push_cast; ring
    have := Int.cast_injective h'
    omega
  · intro h
    obtain ⟨m, hm⟩ : ∃ m, N = 2 * m := ⟨N / 2, by omega⟩
    refine ⟨m, ?_⟩
    have : (N : ℝ) = 2 * m := by exact_mod_cast hm
    linarith

/-- **(proved; the standard-row parity).**  For `i ≥ 1`, `P` monic of degree `d`
and `W^i u, …, W^{i+d−1} u` odd: `R_i` of the phase vector is an integer iff `W^{i+d} u` is
odd.  Paper proof: `two_mul_stdRow_phaseVec` makes `2R_i` the integer `Σ_{j ≤ d} a_j w_{i+j}`
`≡ w_{i+d} (mod 2)` (as in `iterate_odd_iff_autoPhi`). -/
theorem stdRow_phaseVec_int_iff (hP : P.Monic) (hroot : aeval (xOf α) P = 0) {u : ℤ} {i : ℕ}
    (hi : 1 ≤ i)
    (hodd : ∀ j < P.natDegree, (wy α)^[i + j] u % 2 = 1) :
    (∃ m : ℤ, stdRow (synDiv P (xOf α)) P.natDegree (phaseVec α u) i = m) ↔
      (wy α)^[i + P.natDegree] u % 2 = 1 := by
  have hid := two_mul_stdRow_phaseVec (α := α) hroot u hi
  set N : ℤ := ∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j * ((wy α)^[i + j] u + 1)
    with hNdef
  have hN : 2 * stdRow (synDiv P (xOf α)) P.natDegree (phaseVec α u) i = (N : ℝ) := by
    rw [hid, hNdef]; push_cast; ring
  have hpar : N % 2 = ((wy α)^[i + P.natDegree] u + 1) % 2 := by
    rw [hNdef, Finset.sum_range_succ, hP.coeff_natDegree, one_mul]
    have hev : (2 : ℤ) ∣ ∑ j ∈ Finset.range P.natDegree, P.coeff j * ((wy α)^[i + j] u + 1) :=
      Finset.dvd_sum fun j hj => Dvd.dvd.mul_left (by
        have := hodd j (Finset.mem_range.1 hj); omega) _
    generalize ∑ j ∈ Finset.range P.natDegree, P.coeff j * ((wy α)^[i + j] u + 1) = S at hev ⊢
    omega
  constructor
  · rintro ⟨m, hm⟩
    have h' : (N : ℝ) = ((2 * m : ℤ) : ℝ) := by rw [← hN, hm]; push_cast; ring
    have := Int.cast_injective h'
    omega
  · intro h
    obtain ⟨m, hm⟩ : ∃ m, N = 2 * m := ⟨N / 2, by omega⟩
    refine ⟨m, ?_⟩
    have : (N : ℝ) = 2 * m := by exact_mod_cast hm
    linarith

/-- **(proved; solves ⇒ odd).**  For `α > 1`, `P` monic of degree `d ≥ 2`, `u` even with
`W^1 u, …, W^{d−1} u` odd: if the phase vector of `u` satisfies the rows of `RunSystem` of length
`n`, then `W^1 u, …, W^n u` are all odd.  (The box condition is not used.)  Paper proof: strong
induction on `j ∈ [1, n]`: `j < d` is `hfresh`; `j = d` is `topRow_phaseVec_int_iff`; `j > d`
is `stdRow_phaseVec_int_iff` with `i = j − d ≥ 1` (`i + d = j ≤ n`), its hypothesis being the
induction hypothesis on `j − d, …, j − 1`. -/
theorem iterate_odd_of_runSystem (hα : 1 < α) (hP : P.Monic) (hd : 2 ≤ P.natDegree)
    (hroot : aeval (xOf α) P = 0) {u : ℤ} (hu : u % 2 = 0)
    (hfresh : ∀ i : ℕ, 1 ≤ i → i < P.natDegree → (wy α)^[i] u % 2 = 1) {n : ℕ}
    (hε : RunSystem (synDiv P (xOf α)) P.natDegree (P.coeff 0) n (phaseVec α u)) :
    ∀ j ∈ Finset.Icc 1 n, (wy α)^[j] u % 2 = 1 := by
  intro j hj
  obtain ⟨hj1, hjn⟩ := Finset.mem_Icc.1 hj
  clear hj
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases lt_trichotomy j P.natDegree with h | h | h
    · exact hfresh j hj1 h
    · subst h
      exact (topRow_phaseVec_int_iff hα hP hd hroot hu hfresh).1 hε.2.1
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + P.natDegree := ⟨j - P.natDegree, by omega⟩
      refine (stdRow_phaseVec_int_iff hP hroot (by omega : 1 ≤ i)
        fun l hl => ?_).1 (hε.2.2 i (by omega) hjn)
      exact ih (i + l) (by omega) (by omega) (by omega)

/-- **(proved).**  `x = xOf α` is irrational when `α` is.  Paper proof:
`α = 2x/(2x − 1)` (`2x − 1 = 1/(α − 1) ≠ 0` for `α > 1`), a rational function of `x` with
rational coefficients. -/
theorem irrational_xOf (hα : 1 < α) (hirr : Irrational α) : Irrational (xOf α) := by
  have hβ : α / (α - 1) = 1 + (α - 1)⁻¹ := by
    have : α - 1 ≠ 0 := by linarith
    field_simp; ring
  have h1 : Irrational (α - 1) := by exact_mod_cast hirr.sub_intCast 1
  have h2 : Irrational (α / (α - 1)) := by rw [hβ]; exact_mod_cast h1.inv.intCast_add 1
  unfold xOf
  exact_mod_cast h2.div_natCast (m := 2) (by norm_num)

/-- **(drafted, 90%; odd ⇒ solves).**  For irrational `α > 1`, `P` monic of degree
`2 ≤ d ≤ n`, `k ≥ 1`: if `W^1(2k), …, W^n(2k)` are all odd, the phase vector of `2k` solves
`RunSystem` of length `n`.  Paper proof.  *Box:* `ε_0 = G_E(2k)/2 ∈ (0, 1/2]` with
`G_E(2k) = 1 − {kα} < 1` (`kα ∉ ℤ`); for `1 ≤ l < n`, `ε_l = G(v)/2 ∈ [0, 1/2)` with
`v = W^l(2k)` odd (`phaseVec_mem_of_odd`) and `G(v) = ⌈x(v + 1)⌉ − x(v + 1) ≠ 0` since
`v + 1 ≠ 0` (`v > 0`, `wy_pos_iff`) and `x` is irrational (`irrational_xOf`).  *Rows:*
`topRow_phaseVec_int_iff` (step `d`) and `stdRow_phaseVec_int_iff` (steps `d + 1, …, n`). -/
theorem runSystem_phaseVec_of_odd (hα : 1 < α) (hirr : Irrational α) (hP : P.Monic)
    (hd : 2 ≤ P.natDegree) (hroot : aeval (xOf α) P = 0) {k : ℤ} (hk : 0 < k) {n : ℕ}
    (hn : P.natDegree ≤ n) (hodd : ∀ j ∈ Finset.Icc 1 n, (wy α)^[j] (2 * k) % 2 = 1) :
    RunSystem (synDiv P (xOf α)) P.natDegree (P.coeff 0) n (phaseVec α (2 * k)) := by
  sorry

/-- **(assembled from `runSystem_phaseVec_of_odd`, 90%; the exact
correspondence).**  For irrational `α > 1`, `P` monic of degree
`2 ≤ d ≤ n` with `P(x) = 0`, `k ≥ 1`, and the fresh steps `W^1(2k), …, W^{d−1}(2k)` odd: the phase
vector of `2k` solves `RunSystem` of length `n` iff `W^1(2k), …, W^n(2k)` are all odd.  Paper
proof: `iterate_odd_of_runSystem` and `runSystem_phaseVec_of_odd`. -/
theorem runSystem_phaseVec_iff (hα : 1 < α) (hirr : Irrational α) (hP : P.Monic)
    (hd : 2 ≤ P.natDegree) (hroot : aeval (xOf α) P = 0) {k : ℤ} (hk : 0 < k) {n : ℕ}
    (hn : P.natDegree ≤ n)
    (hfresh : ∀ i : ℕ, 1 ≤ i → i < P.natDegree → (wy α)^[i] (2 * k) % 2 = 1) :
    RunSystem (synDiv P (xOf α)) P.natDegree (P.coeff 0) n (phaseVec α (2 * k)) ↔
      ∀ j ∈ Finset.Icc 1 n, (wy α)^[j] (2 * k) % 2 = 1 :=
  ⟨iterate_odd_of_runSystem hα hP hd hroot (by omega) hfresh,
    runSystem_phaseVec_of_odd hα hirr hP hd hroot hk hn⟩

end Correspondence

/-! ## Independence of the frequencies -/

section Independence

variable {α : ℝ} {P : ℤ[X]}

/-- **(drafted, 93%).**  If `x = xOf α` is a root of a monic irreducible `P ∈ ℤ[t]` of degree
`d` (`α > 1`), then `1, θ_0, …, θ_{d−2}` (`θ_l = (α/2)x^l`) are linearly independent over `ℚ`.
Paper proof: `α/2 = x/(2x − 1)` (`xOf_div_two_mul_sub_one`).  A relation
`c_0 + Σ_l c_{l+1}θ_l = 0` times `2x − 1` is `c_0(2x − 1) + Σ_{l<d−1} c_{l+1}x^{l+1} = 0`, a
rational polynomial of degree `≤ d − 1` in `x` with coefficients `(−c_0, 2c_0 + c_1, c_2, …,
c_{d−1})`.  `P.map (algebraMap ℤ ℚ) = minpoly ℚ x` (Gauss, as in `pow_ne_one_of_irreducible`)
has degree `d`, so `1, x, …, x^{d−1}` are independent (`linearIndependent_pow`) and every
coefficient vanishes: `c_0 = 0`, then `c_1 = 0`, then `c_l = 0`. -/
theorem linearIndependent_freqVec (hα : 1 < α) (hP : P.Monic) (hirr : Irreducible P)
    (hroot : aeval (xOf α) P = 0) :
    LinearIndependent ℚ
      (Fin.cons (1 : ℝ) (freqVec α (P.natDegree - 1)) : Fin (P.natDegree - 1 + 1) → ℝ) := by
  sorry

end Independence

/-! ## Boxes and Weyl -/

section Weyl

/-- **(proved).** -/
theorem measurableSet_openBox {m : ℕ} (f : Fin m → ℝ) (r : ℝ) : MeasurableSet (openBox f r) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioo

/-- **(proved).**  The frontier of a box is Lebesgue-null.  Paper proof: it lies in
`Π[f_l, f_l + r] ∖ Π(f_l, f_l + r)`, of measure `r^m − r^m = 0` (as
`WythoffTrapDegree.volume_frontier_trapBox`). -/
theorem volume_frontier_openBox {m : ℕ} (f : Fin m → ℝ) {r : ℝ} (hr : 0 < r) :
    volume (frontier (openBox f r)) = 0 := by
  set a : Fin m → ℝ := f
  set b : Fin m → ℝ := fun i => f i + r
  have hsub : frontier (openBox f r) ⊆
      Set.Icc a b \ Set.univ.pi fun i => Set.Ioo (a i) (b i) := by
    rw [frontier, openBox, closure_pi_set, interior_pi_set Set.finite_univ, ← Set.pi_univ_Icc]
    refine Set.sdiff_subset_sdiff (Set.pi_mono fun i _ => ?_) (Set.pi_mono fun i _ => ?_)
    · rw [closure_Ioo (ne_of_lt (by linarith))]
    · rw [interior_Ioo]
  refine measure_mono_null hsub ?_
  rw [measure_sdiff (fun x hx => Set.mem_Icc.2 ⟨fun i => (hx i (Set.mem_univ _)).1.le,
      fun i => (hx i (Set.mem_univ _)).2.le⟩)
    (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet
    (by rw [Real.volume_pi_Ioo]; exact ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top),
    Real.volume_Icc_pi, Real.volume_pi_Ioo, tsub_self]

/-- **(proved).**  A box inside the unit cube has volume `r^m` there.  Paper proof:
`openBox f r ⊆ [0, 1)^m` (`0 ≤ f_l`, `f_l + r ≤ 1`), and `Real.volume_pi_Ioo_toReal`. -/
theorem volume_openBox {m : ℕ} {f : Fin m → ℝ} {r : ℝ} (hr : 0 < r) (hf0 : ∀ l, 0 ≤ f l)
    (hf1 : ∀ l, f l + r ≤ 1) :
    (volume (openBox f r ∩ Set.univ.pi fun _ => Set.Ico (0 : ℝ) 1)).toReal = r ^ m := by
  have hsub : openBox f r ⊆ Set.univ.pi fun _ => Set.Ico (0 : ℝ) 1 := by
    intro y hy
    simp only [openBox, Set.mem_univ_pi, Set.mem_Ioo, Set.mem_Ico] at hy ⊢
    intro i
    obtain ⟨h0, h1⟩ := hy i
    exact ⟨by linarith [hf0 i], by linarith [hf1 i]⟩
  rw [Set.inter_eq_left.2 hsub, openBox, Real.volume_pi_Ioo_toReal fun i => by simp [hr.le]]
  simp

/-- **(proved; Weyl ⇒ infinitely many hits).**  Under `WeylEquidistributionMulti`, for
`ℚ`-independent `1, θ_0, …, θ_{m−1}` and a box `Π(f_l, f_l + r) ⊆ [0, 1)^m` with `r > 0`,
infinitely many `k ≥ 1` have `({kθ_l})_l` in the box.  Paper proof: the hit count over
`[1, N]` divided by `N` tends to `r^m > 0` (`volume_frontier_openBox`, `volume_openBox`); a
finite hit set would make that ratio `≤ C/N → 0`. -/
theorem setOf_fract_mem_openBox_infinite (hW : WeylEquidistributionMulti) {m : ℕ}
    {θ : Fin m → ℝ} (hθ : LinearIndependent ℚ (Fin.cons (1 : ℝ) θ : Fin (m + 1) → ℝ))
    {f : Fin m → ℝ} {r : ℝ} (hr : 0 < r) (hf0 : ∀ l, 0 ≤ f l) (hf1 : ∀ l, f l + r ≤ 1) :
    {k : ℕ | 0 < k ∧ (fun l => Int.fract ((k : ℝ) * θ l)) ∈ openBox f r}.Infinite := by
  classical
  have hT := hW m θ hθ (openBox f r) (measurableSet_openBox f r) (volume_frontier_openBox f hr)
  rw [volume_openBox hr hf0 hf1] at hT
  by_contra hfin
  rw [Set.not_infinite] at hfin
  have hle : ∀ N : ℕ, ((Finset.Icc 1 N).filter fun k : ℕ =>
      (fun l => Int.fract ((k : ℝ) * θ l)) ∈ openBox f r).card ≤ hfin.toFinset.card := by
    intro N
    refine Finset.card_le_card fun k hk => ?_
    simp only [Finset.mem_filter, Finset.mem_Icc, Set.Finite.mem_toFinset,
      Set.mem_ofPred_eq] at hk ⊢
    exact ⟨by omega, hk.2⟩
  have h0 : Tendsto (fun N : ℕ => (((Finset.Icc 1 N).filter fun k : ℕ =>
      (fun l => Int.fract ((k : ℝ) * θ l)) ∈ openBox f r).card : ℝ) / N) atTop (𝓝 0) :=
    squeeze_zero (fun N => by positivity)
      (fun N => div_le_div_of_nonneg_right
        (show (_ : ℝ) ≤ (hfin.toFinset.card : ℝ) by exact_mod_cast hle N) (Nat.cast_nonneg _))
      (tendsto_const_div_atTop_nhds_zero_nat (hfin.toFinset.card : ℝ))
  exact (pow_pos hr m).ne' (tendsto_nhds_unique hT h0)

end Weyl

/-! ## Openness: a box of `k` that follow a given run-system solution -/

section Openness

variable {α : ℝ} {P : ℤ[X]}

/-- **(proved; the half-integer pin).**  If `a ∈ [0, 1/2]`, `b ∈ [μ, 1/2 − μ]`, `|e| < μ` and
`a − b + e ∈ ½ℤ`, then `a − b + e = 0`.  Paper proof: `|a − b + e| < 1/2`. -/
theorem half_int_pin {a b e μ : ℝ} (ha : 0 ≤ a ∧ a ≤ 1 / 2) (hb : μ ≤ b ∧ b ≤ 1 / 2 - μ)
    (he : |e| < μ) (hz : ∃ m : ℤ, 2 * (a - b + e) = m) : a - b + e = 0 := by
  obtain ⟨m, hm⟩ := hz
  have he' := abs_lt.1 he
  have h1 : (m : ℝ) < 1 := by rw [← hm]; linarith
  have h2 : (-1 : ℝ) < m := by rw [← hm]; linarith
  have h0 := int_eq_zero_of_abs_lt h2 h1
  rw [h0, Int.cast_zero] at hm
  linarith

/-- **(drafted, 88%; the box of followers).**  Let `α > 1`, `P` monic of degree `2 ≤ d ≤ n`
with `P(x) = 0`, and let `ε*` solve `RunSystem` of length `n`.  Then there is `r > 0` with
`f_l + r ≤ 1` (`f = boxCorner x ε* (d − 1)`) such that every `k ∈ ℤ` with `{kθ_l} ∈ (f_l, f_l + r)`
for all `l < d − 1` has `W^1(2k), …, W^n(2k)` all odd.  Paper proof (module docstring,
"Openness").  Let `ε` be the phase vector of `2k`, `μ` the margin of `ε*` on `[0, n)`,
`K = 1 + 2|a_0| + Σ_{k<d}|q_k| + Σ_{j<n} x^j`, `η_l = (2K)^{l+1} r`, and take `r > 0` with
`η_{n−1} < μ` and `r ≤ 1 − f_l`.  Claim for `l < n`: `W^{l+1}(2k)` odd and
`|ε_l − ε*_l| < η_l`.  By strong induction:
* `l < d − 1`: `kθ_l = N + {kθ_l}`, `−S*_l = M + f_l` (`S*_l = Σ_{j≤l} x^{l−j}ε*_j`), so
  `kθ_l + S_l − (N − M) = s + (ε_l − ε*_l) + Σ_{j<l} x^{l−j}(ε_j − ε*_j)` with
  `s = {kθ_l} − f_l ∈ (0, r)`; `ε_l ∈ [0, 1/2]` (`phaseVec_zero_mem`, or `phaseVec_mem_of_odd`
  with the induction hypothesis), and `half_int_pin` with `iterate_odd_iff_fresh` (the left
  side is in `½ℤ` because `kθ_l + S_l = w_{l+1}/2`, `half_iterate_eq`).
* `l = d − 1`: `T(ε) − T(ε*) = (ε_l − ε*_l) + Σ_{k<d−1} q̃_k(ε_k − ε*_k)` (`q_{d−1} = 1`);
  `2T(ε) ∈ ℤ` (`two_mul_topRow_phaseVec`), `T(ε*) ∈ ℤ`; `half_int_pin`, then
  `topRow_phaseVec_int_iff`.
* `l ≥ d`: the same with `R_{l−d+1}` (`two_mul_stdRow_phaseVec`, `stdRow_phaseVec_int_iff`). -/
theorem exists_runBox (hα : 1 < α) (hP : P.Monic) (hd : 2 ≤ P.natDegree)
    (hroot : aeval (xOf α) P = 0) {n : ℕ} (hn : P.natDegree ≤ n) {ε : ℕ → ℝ}
    (hε : RunSystem (synDiv P (xOf α)) P.natDegree (P.coeff 0) n ε) :
    ∃ r : ℝ, 0 < r ∧ (∀ l, boxCorner (xOf α) ε (P.natDegree - 1) l + r ≤ 1) ∧
      ∀ k : ℤ, (fun l => Int.fract ((k : ℝ) * freqVec α (P.natDegree - 1) l)) ∈
          openBox (boxCorner (xOf α) ε (P.natDegree - 1)) r →
        ∀ j ∈ Finset.Icc 1 n, (wy α)^[j] (2 * k) % 2 = 1 := by
  sorry

end Openness

/-! ## Headline -/

section Headline

/-- **(assembled from `exists_runBox` and `linearIndependent_freqVec`, 88%; conditional on
Weyl).**  `RunCriterion` (the sufficiency half of
`wythoff-classify`'s zonotope criterion, exactly as stated in `WythoffPisot`) follows from
`WeylEquidistributionMulti`.  Paper proof: given a solution `ε*` of length `n ≥ d`,
`exists_runBox` gives a box `B` of positive side `r` inside `[0, 1)^{d−1}`;
`linearIndependent_freqVec` and `setOf_fract_mem_openBox_infinite` give infinitely many `k ≥ 1`
with `({kθ_l})_l ∈ B`; each such `u = 2k` is positive, even, and followed by `n` odd iterates,
and `k ↦ 2k` is injective. -/
theorem runCriterion_of_weyl (hW : WeylEquidistributionMulti) : RunCriterion := by
  intro α P hα hP hirr hd hroot n hn ⟨ε, hε⟩
  have hα1 : 1 < α := by linarith
  obtain ⟨r, hr, hr1, hbox⟩ := exists_runBox hα1 hP hd hroot hn hε
  have hinf := setOf_fract_mem_openBox_infinite hW (linearIndependent_freqVec hα1 hP hirr hroot)
    hr (fun l => Int.fract_nonneg _) hr1
  have hinj : Set.InjOn (fun k : ℕ => 2 * (k : ℤ)) {k : ℕ | 0 < k ∧
      (fun l => Int.fract ((k : ℝ) * freqVec α (P.natDegree - 1) l)) ∈
        openBox (boxCorner (xOf α) ε (P.natDegree - 1)) r} := by
    intro a _ b _ hab
    have : (a : ℤ) = b := by simpa using hab
    exact_mod_cast this
  refine (hinf.image hinj).mono ?_
  rintro _ ⟨k, ⟨hk0, hk⟩, rfl⟩
  refine ⟨show (0 : ℤ) < 2 * (k : ℤ) by omega, show 2 * (k : ℤ) % 2 = 0 by omega, hbox k ?_⟩
  simpa only [Int.cast_natCast] using hk

/-- **(assembled, 88%; Theorem N3, headline, conditional on Weyl alone).**  Let `α > 2` with
`x = xOf α` a root of a monic irreducible `P ∈ ℤ[t]` of degree `≥ 2` having another complex root
`z ≠ x` with `‖z‖ ≤ 1`.  Then, under `WeylEquidistributionMulti`, for every `n` infinitely many
positive even `u` are followed by `n` odd iterates.  Paper proof: `n3_infinite_runs` with
`runCriterion_of_weyl`. -/
theorem n3_infinite_runs_of_weyl (hW : WeylEquidistributionMulti) {α : ℝ} (hα : 2 < α)
    {P : ℤ[X]} (hP : P.Monic) (hirr : Irreducible P) (hd : 2 ≤ P.natDegree)
    (hroot : aeval (xOf α) P = 0) {z : ℂ} (hz : aeval z P = 0) (hzx : z ≠ (xOf α : ℂ))
    (hz1 : ‖z‖ ≤ 1) (n : ℕ) :
    {u : ℤ | 0 < u ∧ u % 2 = 0 ∧ ∀ j ∈ Finset.Icc 1 n, (wy α)^[j] u % 2 = 1}.Infinite :=
  n3_infinite_runs (runCriterion_of_weyl hW) hα hP hirr hd hroot hz hzx hz1 n

end Headline

end CollatzMoonshot.WythoffRunCriterion
