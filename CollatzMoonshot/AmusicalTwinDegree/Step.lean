/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalTwinDegree.Den

/-!
# The twin's degree walk and the cycle identity (Theorem D)

* `exc` is the exceptional set `{0, 1, t + 1, Q}`; `U` maps it onto itself, so its complement is
  forward invariant (`twinU_not_mem_exc`).
* Off `exc`, one step is `t^d U y = Q y + e` with `(d, e) = (1, 0), (2, t + 1), (3, e_B),
  (3, e_C)` and `deg U y = deg y + 2 − d` (`step`).
* Iterating at a cycle minimum: `t^{N_j} U^j x = Q^j x + c_j` with `N_j + deg U^j x = 2j + deg x`
  and `deg c_j ≤ 2j + 2` (`iter_identity`).  On the cycle `N_p = 2p`, so
  `x (t^{2p} − Q^p) = c_p` and D1 gives `deg x ≤ 2^v + 2` (`cycleMin_natDegree_le`).
-/

namespace CollatzMoonshot.Amusical.TwinDeg

open Polynomial Function

lemma twinU_E (k : (ZMod 2)[X]) : twinU (X * k) = twinQ * k := FFTwin.fU_E k
lemma twinU_A (k : (ZMod 2)[X]) : twinU (1 + X ^ 2 * k) = twinQ * k + 1 := FFTwin.fU_A k
lemma twinU_B (k : (ZMod 2)[X]) : twinU (1 + X + X ^ 3 * k) = twinQ * k + X := FFTwin.fU_B k
lemma twinU_C (k : (ZMod 2)[X]) :
    twinU (1 + X + X ^ 2 + X ^ 3 * k) = twinQ * k + (1 + X) := FFTwin.fU_C k

lemma twinU_injective : Injective twinU := FFTwin.fU_injective

lemma twinU_zero : twinU 0 = 0 := by simpa using twinU_E 0
lemma twinU_one : twinU 1 = 1 := by simpa using twinU_A 0
lemma twinU_X : twinU X = twinQ := by simpa using twinU_E 1
lemma twinU_Q : twinU twinQ = X + 1 := by
  have := twinU_C 0
  simp only [mul_zero, add_zero, zero_add] at this
  rw [show twinQ = 1 + X + X ^ 2 by unfold twinQ; ring, this, add_comm]
lemma twinU_X_add_one : twinU (X + 1) = X := by
  have := twinU_B 0
  simp only [mul_zero, add_zero, zero_add] at this
  rw [add_comm, this]

/-- The invariant exceptional set `{0, 1, t, t + 1, Q}`: two fixed points and the 3-cycle.  (The
ratified `twinExceptional` omits `t`, which is harmless: `t` has degree `1`.) -/
noncomputable def exc : Set (ZMod 2)[X] := {0, 1, X, X + 1, twinQ}

lemma twinU_mem_exc_iff (y : (ZMod 2)[X]) : twinU y ∈ exc ↔ y ∈ exc := by
  constructor
  · intro h
    simp only [exc, Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
    rcases h with h | h | h | h | h
    · left; exact twinU_injective (h.trans twinU_zero.symm)
    · right; left; exact twinU_injective (h.trans twinU_one.symm)
    · right; right; right; left; exact twinU_injective (h.trans twinU_X_add_one.symm)
    · right; right; right; right; exact twinU_injective (h.trans twinU_Q.symm)
    · right; right; left; exact twinU_injective (h.trans twinU_X.symm)
  · intro h
    simp only [exc, Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
    rcases h with rfl | rfl | rfl | rfl | rfl
    · left; exact twinU_zero
    · right; left; exact twinU_one
    · right; right; right; right; exact twinU_X
    · right; right; left; exact twinU_X_add_one
    · right; right; right; left; exact twinU_Q

lemma iterate_mem_exc_iff (y : (ZMod 2)[X]) (j : ℕ) : twinU^[j] y ∈ exc ↔ y ∈ exc := by
  induction j with
  | zero => rfl
  | succ j ih => rw [iterate_succ_apply', twinU_mem_exc_iff, ih]

lemma natDegree_le_two_of_mem_exc {y : (ZMod 2)[X]} (h : y ∈ exc) : y.natDegree ≤ 2 := by
  simp only [exc, Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with rfl | rfl | rfl | rfl | rfl
  · simp
  · simp
  · simp
  · compute_degree!
  · rw [twinQ_natDegree]

lemma natDegree_Q_mul {k : (ZMod 2)[X]} (hk : k ≠ 0) :
    (twinQ * k).natDegree = k.natDegree + 2 := by
  rw [natDegree_mul twinQ_monic.ne_zero hk, twinQ_natDegree, add_comm]

lemma natDegree_X_pow_mul {k : (ZMod 2)[X]} (hk : k ≠ 0) (d : ℕ) :
    (X ^ d * k).natDegree = k.natDegree + d := by
  rw [natDegree_mul (pow_ne_zero _ X_ne_zero) hk, natDegree_X_pow, add_comm]

/-- **The step.**  Off `exc`, `t^d U y = Q y + e` by class, with the degree moving `+1, 0, −1, −1`.
-/
lemma step (y : (ZMod 2)[X]) (hy : y ∉ exc) :
    (X * twinU y = twinQ * y ∧ (twinU y).natDegree = y.natDegree + 1) ∨
    (X ^ 2 * twinU y = twinQ * y + (X + 1) ∧ (twinU y).natDegree = y.natDegree) ∨
    (X ^ 3 * twinU y = twinQ * y + (X ^ 4 + X ^ 3 + 1) ∧
      (twinU y).natDegree + 1 = y.natDegree) ∨
    (X ^ 3 * twinU y = twinQ * y + (X ^ 3 + X ^ 2 + 1) ∧
      (twinU y).natDegree + 1 = y.natDegree) := by
  rcases FFTwin.fU_cases y with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have hk : k ≠ 0 := by rintro rfl; exact hy (by simp [exc])
    left
    refine ⟨by rw [twinU_E]; ring, ?_⟩
    rw [twinU_E, natDegree_Q_mul hk, natDegree_mul X_ne_zero hk, natDegree_X]; ring
  · have hk : k ≠ 0 := by rintro rfl; exact hy (by simp [exc])
    right; left
    have hd : (1 + X ^ 2 * k).natDegree = k.natDegree + 2 := by
      rw [natDegree_add_eq_right_of_natDegree_lt] <;> rw [natDegree_X_pow_mul hk] <;> simp
    refine ⟨?_, ?_⟩
    · rw [twinU_A]; unfold twinQ
      linear_combination (norm := (ring_nf; reduce_mod_char))
    · rw [twinU_A, hd, natDegree_add_eq_left_of_natDegree_lt] <;> rw [natDegree_Q_mul hk] <;>
        simp
  · have hk : k ≠ 0 := by
      rintro rfl
      apply hy; rw [mul_zero, add_zero]
      simp only [exc, Set.mem_insert_iff, Set.mem_singleton_iff]; right; right; right; left; ring
    right; right; left
    have hd : (1 + X + X ^ 3 * k).natDegree = k.natDegree + 3 := by
      rw [natDegree_add_eq_right_of_natDegree_lt] <;> rw [natDegree_X_pow_mul hk]
      have : (1 + X : (ZMod 2)[X]).natDegree ≤ 1 := by compute_degree!
      omega
    refine ⟨?_, ?_⟩
    · rw [twinU_B]; unfold twinQ
      linear_combination (norm := (ring_nf; reduce_mod_char))
    · rw [twinU_B, hd, natDegree_add_eq_left_of_natDegree_lt] <;> rw [natDegree_Q_mul hk] <;>
        simp
  · have hk : k ≠ 0 := by
      rintro rfl
      apply hy; rw [mul_zero, add_zero]
      simp only [exc, Set.mem_insert_iff, Set.mem_singleton_iff]; right; right; right; right
      unfold twinQ; ring
    right; right; right
    have hd : (1 + X + X ^ 2 + X ^ 3 * k).natDegree = k.natDegree + 3 := by
      rw [natDegree_add_eq_right_of_natDegree_lt] <;> rw [natDegree_X_pow_mul hk]
      have : (1 + X + X ^ 2 : (ZMod 2)[X]).natDegree ≤ 2 := by compute_degree!
      omega
    refine ⟨?_, ?_⟩
    · rw [twinU_C]; unfold twinQ
      linear_combination (norm := (ring_nf; reduce_mod_char))
    · rw [twinU_C, hd, natDegree_add_eq_left_of_natDegree_lt] <;> rw [natDegree_Q_mul hk]
      have : (1 + X : (ZMod 2)[X]).natDegree ≤ 1 := by compute_degree!
      omega

/-- The step in uniform shape: `t^d U y = Q y + e`, `d + deg U y = deg y + 2`, `deg e ≤ 4`. -/
lemma step' (y : (ZMod 2)[X]) (hy : y ∉ exc) :
    ∃ d e, X ^ d * twinU y = twinQ * y + e ∧ d + (twinU y).natDegree = y.natDegree + 2 ∧
      e.natDegree ≤ 4 ∧ 1 ≤ d ∧ d ≤ 3 := by
  rcases step y hy with ⟨h, hd⟩ | ⟨h, hd⟩ | ⟨h, hd⟩ | ⟨h, hd⟩
  · exact ⟨1, 0, by rw [pow_one, h, add_zero], by omega, by simp, le_rfl, by norm_num⟩
  · exact ⟨2, X + 1, h, by omega, by compute_degree!, by norm_num, by norm_num⟩
  · exact ⟨3, _, h, by omega, by compute_degree!, by norm_num, le_rfl⟩
  · exact ⟨3, _, h, by omega, by compute_degree!, by norm_num, le_rfl⟩

/-- One step changes the degree by at most one, either way. -/
lemma natDegree_step_le (y : (ZMod 2)[X]) (hy : y ∉ exc) :
    (twinU y).natDegree ≤ y.natDegree + 1 ∧ y.natDegree ≤ (twinU y).natDegree + 1 := by
  obtain ⟨d, e, -, hd, -, h1, h3⟩ := step' y hy
  omega

lemma natDegree_iterate_le (y : (ZMod 2)[X]) (hy : y ∉ exc) (j : ℕ) :
    (twinU^[j] y).natDegree ≤ y.natDegree + j ∧ y.natDegree ≤ (twinU^[j] y).natDegree + j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hj : twinU^[j] y ∉ exc := by rwa [iterate_mem_exc_iff]
    have := natDegree_step_le _ hj
    rw [iterate_succ_apply']
    omega

/-- **The iterated identity** at a cycle minimum: `t^N U^j x = Q^j x + c` with
`N + deg U^j x = 2j + deg x` and `deg c ≤ 2j + 2`. -/
lemma iter_identity (x : (ZMod 2)[X]) (hx : x ∉ exc)
    (hmin : ∀ j, x.natDegree ≤ (twinU^[j] x).natDegree) (j : ℕ) :
    ∃ N c, N + (twinU^[j] x).natDegree = 2 * j + x.natDegree ∧ c.natDegree ≤ 2 * j + 2 ∧
      X ^ N * twinU^[j] x = twinQ ^ j * x + c := by
  induction j with
  | zero => exact ⟨0, 0, by simp, by simp, by simp⟩
  | succ j ih =>
    obtain ⟨N, c, hN, hc, hid⟩ := ih
    have hj : twinU^[j] x ∉ exc := by rwa [iterate_mem_exc_iff]
    obtain ⟨d, e, hstep, hd, he, -, -⟩ := step' _ hj
    have hNle : N ≤ 2 * j := by have := hmin j; omega
    refine ⟨N + d, twinQ * c + X ^ N * e, ?_, ?_, ?_⟩
    · rw [iterate_succ_apply']; omega
    · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
      · refine (natDegree_mul_le).trans ?_
        rw [twinQ_natDegree]; omega
      · refine (natDegree_mul_le).trans ?_
        rw [natDegree_X_pow]; omega
    · rw [iterate_succ_apply', pow_add, mul_assoc, hstep, mul_add, mul_left_comm, hid]
      ring

/-- **Theorem D (internal form).** -/
theorem cycleMin_natDegree_le (x : (ZMod 2)[X]) (hx : x ∈ periodicPts twinU)
    (hmin : ∀ j, x.natDegree ≤ (twinU^[j] x).natDegree) :
    x.natDegree ≤ 2 ^ padicValNat 2 (minimalPeriod twinU x) + 2 := by
  by_cases hxe : x ∈ exc
  · have := natDegree_le_two_of_mem_exc hxe
    have : 0 < 2 ^ padicValNat 2 (minimalPeriod twinU x) := by positivity
    omega
  set p := minimalPeriod twinU x with hpdef
  have hp : 0 < p := minimalPeriod_pos_of_mem_periodicPts hx
  have hfix : twinU^[p] x = x := iterate_minimalPeriod
  obtain ⟨N, c, hN, hc, hid⟩ := iter_identity x hxe hmin p
  rw [hfix] at hN hid
  have hN2 : N = 2 * p := by omega
  subst hN2
  have hD : ((X ^ 2 : (ZMod 2)[X]) ^ p - twinQ ^ p) * x = c := by
    rw [sub_mul, ← pow_mul, hid]; ring
  have hvle : 2 ^ padicValNat 2 p ≤ p := Nat.le_of_dvd hp pow_padicValNat_dvd
  have hdeg := den_natDegree p hp
  have hDne : (X ^ 2 : (ZMod 2)[X]) ^ p - twinQ ^ p ≠ 0 := by
    intro h; rw [h, natDegree_zero] at hdeg; omega
  have hx0 : x ≠ 0 := by rintro rfl; exact hxe (by simp [exc])
  have := congrArg natDegree hD
  rw [natDegree_mul hDne hx0, hdeg] at this
  omega

end CollatzMoonshot.Amusical.TwinDeg
