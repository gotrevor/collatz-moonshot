/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Obstructions.Amusical
import CollatzMoonshot.AmusicalBound

/-!
# Chain connectivity: what one chain can and cannot carry

From the 2026-10-13 "chains" research agent (research note §7).  Treadmill target
(`KICKOFF-2026-10-13-amusical-chains.md`): close every `sorry` here.

* Window minima are spread out along an orbit (`IsWindowMin.iterate_eq_of_isWindowMin`).
* The window densities are uniformly positive: `fwdSurv L ≥ 1/6`, `bwdSurv L ≥ 1/6`, by the
  induction `g_L(s) ≥ 1 − e^{-s}` that uses only the Haar balance `E[e^{-X}] = 1`.
* Together with `windowMinDensity`, finitely many orbits would force an infinite orbit with
  `liminf |U^j x| / |j| = 0`: the **sublinear** recurrence, sharper than
  `exists_linearlyRecurrent_of_finitelyManyOrbits`.
* `AmusicalAtLeastSevenOrbits ∨ (amusicalOrbit 8).Infinite`.
-/

namespace CollatzMoonshot.Amusical

open CollatzMoonshot.Obstructions.Amusical

/-! The survival estimates are most transparent with the current multiplicative
height retained as a rational number `a / b`.  These recursors are the finite
horizon walks before translating back to the word sums `fwdSurv` and
`bwdSurv`. -/

def fwdWalk : ℕ → ℕ → ℕ → ℚ
  | 0, _, _ => 1
  | L + 1, a, b =>
      (if 2 * a < 3 * b then (1 / 2 : ℚ) * fwdWalk L (2 * a) (3 * b) else 0) +
      (if 4 * a < 3 * b then (1 / 2 : ℚ) * fwdWalk L (4 * a) (3 * b) else 0)

def bwdWalk : ℕ → ℕ → ℕ → ℚ
  | 0, _, _ => 1
  | L + 1, a, b =>
      (if 3 * a < 2 * b then (1 / 3 : ℚ) * bwdWalk L (3 * a) (2 * b) else 0) +
      (if 3 * a < 4 * b then (2 / 3 : ℚ) * bwdWalk L (3 * a) (4 * b) else 0)

theorem fwdWalk_ge (L a b : ℕ) (ha : 0 < a) (hab : a < b) :
    1 - (a : ℚ) / b ≤ fwdWalk L a b := by
  induction L generalizing a b with
  | zero => simp [fwdWalk, div_nonneg]
  | succ L ih =>
      have hb : 0 < b := lt_trans ha hab
      have h2 : 2 * a < 3 * b := by omega
      rw [fwdWalk, if_pos h2]
      by_cases h4 : 4 * a < 3 * b
      · rw [if_pos h4]
        have hpos2 : 0 < 2 * a := by positivity
        have hpos4 : 0 < 4 * a := by positivity
        have hleft := ih (2 * a) (3 * b) hpos2 h2
        have hright := ih (4 * a) (3 * b) hpos4 h4
        norm_num [Nat.cast_mul] at hleft hright
        have hbq : (0 : ℚ) < b := by exact_mod_cast hb
        calc
          1 - (a : ℚ) / b =
              (1 / 2 : ℚ) * (1 - (2 * a : ℕ) / (3 * b)) +
                (1 / 2 : ℚ) * (1 - (4 * a : ℕ) / (3 * b)) := by
                  norm_num [Nat.cast_mul]
                  field_simp
                  ring
          _ ≤ (1 / 2 : ℚ) * fwdWalk L (2 * a) (3 * b) +
                (1 / 2 : ℚ) * fwdWalk L (4 * a) (3 * b) := by
                  gcongr
                  · simpa [Nat.cast_mul] using ih (2 * a) (3 * b) hpos2 h2
                  · simpa [Nat.cast_mul] using ih (4 * a) (3 * b) hpos4 h4
      · rw [if_neg h4]
        have hleft := ih (2 * a) (3 * b) (by positivity) h2
        norm_num [Nat.cast_mul] at hleft
        have hbq : (0 : ℚ) < b := by exact_mod_cast hb
        have h4' : 3 * b ≤ 4 * a := by omega
        calc
          1 - (a : ℚ) / b ≤ (1 / 2 : ℚ) * (1 - (2 * a : ℕ) / (3 * b)) := by
            have h4q : (3 : ℚ) * b ≤ 4 * a := by exact_mod_cast h4'
            push_cast
            field_simp
            linarith
          _ ≤ (1 / 2 : ℚ) * fwdWalk L (2 * a) (3 * b) := by
            gcongr
            simpa [Nat.cast_mul] using ih (2 * a) (3 * b) (by positivity) h2
          _ = _ := by ring

theorem bwdWalk_ge (L a b : ℕ) (ha : 0 < a) (hab : a < b) :
    1 - (a : ℚ) / b ≤ bwdWalk L a b := by
  induction L generalizing a b with
  | zero => simp [bwdWalk, div_nonneg]
  | succ L ih =>
      have hb : 0 < b := lt_trans ha hab
      have h4 : 3 * a < 4 * b := by omega
      rw [bwdWalk, if_pos h4]
      by_cases h2 : 3 * a < 2 * b
      · rw [if_pos h2]
        have hleft := ih (3 * a) (2 * b) (by positivity) h2
        have hright := ih (3 * a) (4 * b) (by positivity) h4
        norm_num [Nat.cast_mul] at hleft hright
        have hbq : (0 : ℚ) < b := by exact_mod_cast hb
        calc
          1 - (a : ℚ) / b =
              (1 / 3 : ℚ) * (1 - (3 * a : ℕ) / (2 * b)) +
                (2 / 3 : ℚ) * (1 - (3 * a : ℕ) / (4 * b)) := by
                  norm_num [Nat.cast_mul]
                  field_simp
                  ring
          _ ≤ (1 / 3 : ℚ) * bwdWalk L (3 * a) (2 * b) +
                (2 / 3 : ℚ) * bwdWalk L (3 * a) (4 * b) := by
                  gcongr
                  · simpa [Nat.cast_mul] using ih (3 * a) (2 * b) (by positivity) h2
                  · simpa [Nat.cast_mul] using ih (3 * a) (4 * b) (by positivity) h4
      · rw [if_neg h2]
        have hright := ih (3 * a) (4 * b) (by positivity) h4
        norm_num [Nat.cast_mul] at hright
        have hbq : (0 : ℚ) < b := by exact_mod_cast hb
        have h2' : 2 * b ≤ 3 * a := by omega
        calc
          1 - (a : ℚ) / b ≤ (2 / 3 : ℚ) * (1 - (3 * a : ℕ) / (4 * b)) := by
            have h2q : (2 : ℚ) * b ≤ 3 * a := by exact_mod_cast h2'
            push_cast
            field_simp
            linarith
          _ ≤ (2 / 3 : ℚ) * bwdWalk L (3 * a) (4 * b) := by
            gcongr
            simpa [Nat.cast_mul] using ih (3 * a) (4 * b) (by positivity) h4
          _ = _ := by ring

open Classical in
/-- Split a sum over Boolean words by the first letter. -/
theorem sum_bool_cons {n : ℕ} (f : (Fin (n + 1) → Bool) → ℚ) :
    ∑ w, f w = ∑ b : Bool, ∑ u : Fin n → Bool, f (Fin.cons b u) := by
  refine ((Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) ↦ Bool))
    (fun x => f (Fin.cons x.1 x.2)) f (fun _ => rfl)).symm).trans ?_
  exact Fintype.sum_prod_type _

/-- The forward survival condition, retaining the current exponential deficit `a / b`. -/
def FwdWalkGood {L : ℕ} (a b : ℕ) (w : Fin L → Bool) : Prop :=
  ∀ t : ℕ, 1 ≤ t → t ≤ L →
    a * 2 ^ (t + latticePrefixMarked w t) < b * 3 ^ t

/-- The backward survival condition, retaining the current exponential deficit `a / b`. -/
def BwdWalkGood {L : ℕ} (a b : ℕ) (w : Fin L → Bool) : Prop :=
  ∀ t : ℕ, 1 ≤ t → t ≤ L →
    a * 3 ^ t < b * 2 ^ (t + latticePrefixMarked w t)

theorem latticePrefixMarked_cons_succ {n t : ℕ} (c : Bool) (u : Fin n → Bool) :
    latticePrefixMarked (Fin.cons c u) (t + 1) =
      (if c then 1 else 0) + latticePrefixMarked u t := by
  simp only [latticePrefixMarked, Finset.card_filter]
  rw [Fin.sum_univ_succ]
  cases c <;> simp

@[simp] theorem latticePrefixMarked_zero {n : ℕ} (u : Fin n → Bool) :
    latticePrefixMarked u 0 = 0 := by
  simp [latticePrefixMarked]

theorem two_pow_step_false (t p : ℕ) :
    2 ^ (t + 1 + p) = 2 * 2 ^ (t + p) := by
  rw [show t + 1 + p = (t + p) + 1 by omega, pow_succ]
  ring

theorem two_pow_step_true (t p : ℕ) :
    2 ^ (t + 1 + (1 + p)) = 4 * 2 ^ (t + p) := by
  rw [show t + 1 + (1 + p) = (t + p) + 2 by omega, pow_add]
  norm_num
  ring

theorem three_pow_step (t : ℕ) : 3 ^ (t + 1) = 3 * 3 ^ t := by
  rw [pow_succ]
  ring

theorem fwdWalkGood_cons_false {n a b : ℕ} (u : Fin n → Bool) :
    FwdWalkGood a b (Fin.cons false u) ↔
      2 * a < 3 * b ∧ FwdWalkGood (2 * a) (3 * b) u := by
  constructor
  · intro h
    constructor
    · simpa [FwdWalkGood, latticePrefixMarked_cons_succ, mul_comm] using
        h 1 (by omega) (by omega)
    · intro t ht1 htn
      have ht := h (t + 1) (by omega) (by omega)
      rw [latticePrefixMarked_cons_succ] at ht
      simp only [Bool.false_eq_true, ↓reduceIte, zero_add] at ht
      rw [two_pow_step_false, three_pow_step] at ht
      simpa [mul_assoc, mul_comm, mul_left_comm] using ht
  · rintro ⟨hfirst, htail⟩ t ht1 ht
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    cases s with
    | zero => simpa [FwdWalkGood, latticePrefixMarked_cons_succ, mul_comm] using hfirst
    | succ s =>
        have hs := htail (s + 1) (by omega) (by omega)
        rw [latticePrefixMarked_cons_succ]
        simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
        rw [two_pow_step_false, three_pow_step]
        simpa [mul_assoc, mul_comm, mul_left_comm] using hs

theorem fwdWalkGood_cons_true {n a b : ℕ} (u : Fin n → Bool) :
    FwdWalkGood a b (Fin.cons true u) ↔
      4 * a < 3 * b ∧ FwdWalkGood (4 * a) (3 * b) u := by
  constructor
  · intro h
    constructor
    · simpa [FwdWalkGood, latticePrefixMarked_cons_succ, pow_succ, mul_comm] using
        h 1 (by omega) (by omega)
    · intro t ht1 htn
      have ht := h (t + 1) (by omega) (by omega)
      rw [latticePrefixMarked_cons_succ] at ht
      simp only [↓reduceIte] at ht
      rw [two_pow_step_true, three_pow_step] at ht
      simpa [mul_assoc, mul_comm, mul_left_comm] using ht
  · rintro ⟨hfirst, htail⟩ t ht1 ht
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    cases s with
    | zero => simpa [FwdWalkGood, latticePrefixMarked_cons_succ, pow_succ, mul_comm] using hfirst
    | succ s =>
        have hs := htail (s + 1) (by omega) (by omega)
        rw [latticePrefixMarked_cons_succ]
        simp only [↓reduceIte]
        rw [two_pow_step_true, three_pow_step]
        simpa [mul_assoc, mul_comm, mul_left_comm] using hs

theorem bwdWalkGood_cons_false {n a b : ℕ} (u : Fin n → Bool) :
    BwdWalkGood a b (Fin.cons false u) ↔
      3 * a < 2 * b ∧ BwdWalkGood (3 * a) (2 * b) u := by
  constructor
  · intro h
    constructor
    · simpa [BwdWalkGood, latticePrefixMarked_cons_succ, mul_comm] using
        h 1 (by omega) (by omega)
    · intro t ht1 htn
      have ht := h (t + 1) (by omega) (by omega)
      rw [latticePrefixMarked_cons_succ] at ht
      simp only [Bool.false_eq_true, ↓reduceIte, zero_add] at ht
      rw [three_pow_step, two_pow_step_false] at ht
      simpa [mul_assoc, mul_comm, mul_left_comm] using ht
  · rintro ⟨hfirst, htail⟩ t ht1 ht
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    cases s with
    | zero => simpa [BwdWalkGood, latticePrefixMarked_cons_succ, mul_comm] using hfirst
    | succ s =>
        have hs := htail (s + 1) (by omega) (by omega)
        rw [latticePrefixMarked_cons_succ]
        simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
        rw [three_pow_step, two_pow_step_false]
        simpa [mul_assoc, mul_comm, mul_left_comm] using hs

theorem bwdWalkGood_cons_true {n a b : ℕ} (u : Fin n → Bool) :
    BwdWalkGood a b (Fin.cons true u) ↔
      3 * a < 4 * b ∧ BwdWalkGood (3 * a) (4 * b) u := by
  constructor
  · intro h
    constructor
    · simpa [BwdWalkGood, latticePrefixMarked_cons_succ, pow_succ, mul_comm] using
        h 1 (by omega) (by omega)
    · intro t ht1 htn
      have ht := h (t + 1) (by omega) (by omega)
      rw [latticePrefixMarked_cons_succ] at ht
      simp only [↓reduceIte] at ht
      rw [three_pow_step, two_pow_step_true] at ht
      simpa [mul_assoc, mul_comm, mul_left_comm] using ht
  · rintro ⟨hfirst, htail⟩ t ht1 ht
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    cases s with
    | zero => simpa [BwdWalkGood, latticePrefixMarked_cons_succ, pow_succ, mul_comm] using hfirst
    | succ s =>
        have hs := htail (s + 1) (by omega) (by omega)
        rw [latticePrefixMarked_cons_succ]
        simp only [↓reduceIte]
        rw [three_pow_step, two_pow_step_true]
        simpa [mul_assoc, mul_comm, mul_left_comm] using hs

def latticeUnmarked {L : ℕ} (w : Fin L → Bool) : ℕ :=
  (Finset.univ.filter fun i => w i = false).card

theorem latticeMarked_cons {n : ℕ} (c : Bool) (u : Fin n → Bool) :
    latticeMarked (Fin.cons c u) = (if c then 1 else 0) + latticeMarked u := by
  simp only [latticeMarked, Finset.card_filter]
  rw [Fin.sum_univ_succ]
  cases c <;> simp

theorem latticeUnmarked_cons {n : ℕ} (c : Bool) (u : Fin n → Bool) :
    latticeUnmarked (Fin.cons c u) = (if c then 0 else 1) + latticeUnmarked u := by
  simp only [latticeUnmarked, Finset.card_filter]
  rw [Fin.sum_univ_succ]
  cases c <;> simp

noncomputable def fwdWalkSum (L a b : ℕ) : ℚ := by
  classical
  exact ∑ w : Fin L → Bool, if FwdWalkGood a b w then (1 / 2 : ℚ) ^ L else 0

def bwdWalkWeight {L : ℕ} (w : Fin L → Bool) : ℚ :=
  (2 / 3 : ℚ) ^ latticeMarked w * (1 / 3 : ℚ) ^ latticeUnmarked w

theorem bwdWalkWeight_cons_false {n : ℕ} (u : Fin n → Bool) :
    bwdWalkWeight (Fin.cons false u) = (1 / 3 : ℚ) * bwdWalkWeight u := by
  simp only [bwdWalkWeight, latticeMarked_cons, latticeUnmarked_cons, Bool.false_eq_true,
    ↓reduceIte, zero_add]
  rw [show 1 + latticeUnmarked u = latticeUnmarked u + 1 by omega, pow_succ]
  ring

theorem bwdWalkWeight_cons_true {n : ℕ} (u : Fin n → Bool) :
    bwdWalkWeight (Fin.cons true u) = (2 / 3 : ℚ) * bwdWalkWeight u := by
  simp only [bwdWalkWeight, latticeMarked_cons, latticeUnmarked_cons, ↓reduceIte, zero_add]
  rw [show 1 + latticeMarked u = latticeMarked u + 1 by omega, pow_succ]
  ring

noncomputable def bwdWalkSum (L a b : ℕ) : ℚ := by
  classical
  exact ∑ w : Fin L → Bool, if BwdWalkGood a b w then bwdWalkWeight w else 0

theorem fwdWalkSum_succ (L a b : ℕ) :
    fwdWalkSum (L + 1) a b =
      (if 2 * a < 3 * b then (1 / 2 : ℚ) * fwdWalkSum L (2 * a) (3 * b) else 0) +
      (if 4 * a < 3 * b then (1 / 2 : ℚ) * fwdWalkSum L (4 * a) (3 * b) else 0) := by
  classical
  unfold fwdWalkSum
  rw [sum_bool_cons, Fintype.sum_bool]
  simp_rw [fwdWalkGood_cons_false, fwdWalkGood_cons_true]
  by_cases h2 : a * 2 < b * 3 <;> by_cases h4 : a * 4 < b * 3 <;>
    simp [h2, h4, pow_succ, Finset.mul_sum, mul_comm, add_comm]

theorem bwdWalkSum_succ (L a b : ℕ) :
    bwdWalkSum (L + 1) a b =
      (if 3 * a < 2 * b then (1 / 3 : ℚ) * bwdWalkSum L (3 * a) (2 * b) else 0) +
      (if 3 * a < 4 * b then (2 / 3 : ℚ) * bwdWalkSum L (3 * a) (4 * b) else 0) := by
  classical
  unfold bwdWalkSum
  rw [sum_bool_cons, Fintype.sum_bool]
  simp_rw [bwdWalkGood_cons_false, bwdWalkGood_cons_true, bwdWalkWeight_cons_false,
    bwdWalkWeight_cons_true]
  by_cases h2 : a * 3 < b * 2 <;> by_cases h4 : a * 3 < b * 4 <;>
    simp [h2, h4, Finset.mul_sum, mul_comm, add_comm]

theorem fwdWalkSum_eq_fwdWalk (L a b : ℕ) : fwdWalkSum L a b = fwdWalk L a b := by
  induction L generalizing a b with
  | zero =>
      unfold fwdWalkSum
      simp only [Fintype.sum_unique]
      rw [if_pos (by intro t ht1 ht0; omega)]
      simp [fwdWalk]
  | succ L ih => rw [fwdWalkSum_succ, fwdWalk, ih, ih]

theorem bwdWalkSum_eq_bwdWalk (L a b : ℕ) : bwdWalkSum L a b = bwdWalk L a b := by
  induction L generalizing a b with
  | zero =>
      unfold bwdWalkSum
      simp only [Fintype.sum_unique]
      rw [if_pos (by intro t ht1 ht0; omega)]
      simp [bwdWalkWeight, latticeMarked, latticeUnmarked, bwdWalk]
  | succ L ih => rw [bwdWalkSum_succ, bwdWalk, ih, ih]

theorem fwdSurv_eq_fwdWalk (L : ℕ) : fwdSurv L = fwdWalk L 1 1 := by
  rw [← fwdWalkSum_eq_fwdWalk L 1 1]
  classical
  unfold fwdSurv fwdWalkSum FwdWalkGood latticePrefixMarked
  simp

theorem bwdSurv_eq_bwdWalk (L : ℕ) : bwdSurv L = bwdWalk L 1 1 := by
  rw [← bwdWalkSum_eq_bwdWalk L 1 1]
  classical
  unfold bwdSurv bwdWalkSum BwdWalkGood bwdWalkWeight latticePrefixMarked latticeMarked
    latticeUnmarked
  simp

/-- **Target.**  Two `L`-window minima at most `L` steps apart on one orbit coincide:
`n ≤ U^t n` and `U^t n ≤ U^-t (U^t n) = n`. -/
theorem IsWindowMin.iterate_eq_of_isWindowMin {L t : ℕ} {n : ℤ} (h : IsWindowMin L n)
    (ht : 0 < t) (htL : t ≤ L) (h' : IsWindowMin L (amusical^[t] n)) : amusical^[t] n = n := by
  apply le_antisymm
  · have hback := (h' t ht htL).2
    rw [amusicalInv_iterate_eq_perm_pow, amusical_iterate_eq_perm_pow] at hback
    have hback' : (amusicalPerm ^ (t : ℤ)) n ≤ n := by
      simpa [← Equiv.Perm.mul_apply] using hback
    rwa [amusical_iterate_eq_perm_pow]
  · exact (h t ht htL).1

/-- **Target.**  The forward survival probability is at least `1/6` for every `L`. -/
theorem fwdSurv_ge (L : ℕ) : 1 / 6 ≤ fwdSurv L := by
  cases L with
  | zero => rw [fwdSurv_eq_fwdWalk]; norm_num [fwdWalk]
  | succ L =>
      rw [fwdSurv_eq_fwdWalk, fwdWalk]
      norm_num
      have h := fwdWalk_ge L 2 3 (by omega) (by omega)
      norm_num at h ⊢
      linarith

/-- **Target.**  The backward survival probability is at least `1/6` for every `L`. -/
theorem bwdSurv_ge (L : ℕ) : 1 / 6 ≤ bwdSurv L := by
  cases L with
  | zero => rw [bwdSurv_eq_bwdWalk]; norm_num [bwdWalk]
  | succ L =>
      rw [bwdSurv_eq_bwdWalk, bwdWalk]
      norm_num
      have h := bwdWalk_ge L 3 4 (by omega) (by omega)
      norm_num at h ⊢
      linarith

/-- Window minima have density at least `1/36` for every window length. -/
theorem windowDensity_ge (L : ℕ) : 1 / 36 ≤ fwdSurv L * bwdSurv L := by
  have h1 := fwdSurv_ge L
  have h2 := bwdSurv_ge L
  calc (1 : ℚ) / 36 = 1 / 6 * (1 / 6) := by norm_num
    _ ≤ fwdSurv L * bwdSurv L := mul_le_mul h1 h2 (by norm_num) (by linarith)

/-- **Target.**  The sublinear recurrence: finitely many orbits would force some infinite orbit
to come back below `|j|/C` at arbitrarily late times, for every `C`.  Paper proof: at least
`δ_L X − o(X) ≥ X/37` window minima lie below `X`; on one chain their times are more than `L`
apart, so `k` chains span time `≥ L X/37 − O(k)`; one chain has `|j| ≥ L X/(75k)` with value
`< X`; let `L → ∞` and pigeonhole over the finitely many chains. -/
theorem exists_sublinearlyRecurrent_of_finitelyManyOrbits (h : ¬ AmusicalInfinitelyManyOrbits) :
    ∃ x : ℤ, 0 ≤ x ∧ (amusicalOrbit x).Infinite ∧ ∀ C : ℝ, 0 < C → ∀ J : ℕ,
      ∃ j : ℤ, (J : ℤ) ≤ |j| ∧ C * (((amusicalPerm ^ j) x : ℤ) : ℝ) ≤ |(j : ℝ)| := by
  sorry

/-- **Target.**  A seventh orbit, or the orbit of `8` is infinite: if the orbit of `8` were a
cycle, the least integer outside it and the five known cycles would start a seventh orbit. -/
theorem atLeastSeven_or_orbitEight_infinite :
    AmusicalAtLeastSevenOrbits ∨ (amusicalOrbit 8).Infinite := by
  by_cases h8 : (amusicalOrbit 8).Infinite
  · exact Or.inr h8
  left
  have hknown : (knownCycleMembers : Set ℤ).Finite := Finset.finite_toSet _
  have hfinite : ((knownCycleMembers : Set ℤ) ∪ amusicalOrbit 8).Finite :=
    hknown.union (Set.not_infinite.1 h8)
  obtain ⟨n, hn0, hn⟩ :=
    (Set.Ici_infinite (0 : ℤ)).sdiff hfinite |>.nonempty
  have hclosed : ∀ a ∈ ({0, 1, 2, 4, 44} : Finset ℤ),
      amusicalOrbit a ⊆ (knownCycleMembers : Set ℤ) := by
    intro a ha
    apply amusicalOrbit_subset_of_closed (S := (knownCycleMembers : Set ℤ))
        (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> decide
  have hnorb : ∀ a ∈ ({0, 1, 2, 4, 44, 8} : Finset ℤ),
      amusicalOrbit n ≠ amusicalOrbit a := by
    intro a ha heq
    apply hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Or.inl (hclosed _ (by decide) (heq ▸ mem_amusicalOrbit_self n))
      | exact Or.inr (heq ▸ mem_amusicalOrbit_self n)
  refine ⟨insert n {0, 1, 2, 4, 44, 8}, ?_, ?_, ?_⟩
  · have : n ∉ ({0, 1, 2, 4, 44, 8} : Finset ℤ) := by
      intro hn'
      exact hnorb n (by simpa using hn') rfl
    simp [this]
  · intro x hx
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact hn0
    · simp only [Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · intro a ha b hb hab
    change a ∈ (insert n {0, 1, 2, 4, 44, 8} : Finset ℤ) at ha
    change b ∈ (insert n {0, 1, 2, 4, 44, 8} : Finset ℤ) at hb
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hnorb b (Finset.mem_insert.mp hb |>.resolve_left hab.symm)
    · rcases Finset.mem_insert.mp hb with hbn | hb
      · subst b
        exact (hnorb a ha).symm
      · exact amusical_six_distinct_orbits a ha b hb hab

/-- **Reopen condition (weaker than `NoLinearRecurrence`).**  Every aperiodic orbit grows at
least linearly in time: `|U^j x| ≥ c |j|` for all large `|j|`. -/
def AtLeastLinearGrowth : Prop :=
  ∀ x : ℤ, 0 ≤ x → (amusicalOrbit x).Infinite → ∃ c : ℝ, 0 < c ∧ ∃ J : ℕ, ∀ j : ℤ,
    (J : ℤ) ≤ |j| → c * |(j : ℝ)| ≤ (((amusicalPerm ^ j) x : ℤ) : ℝ)

/-- At-least-linear growth of every aperiodic orbit settles Klamkin's problem (a). -/
theorem amusicalInfinitelyManyOrbits_of_atLeastLinearGrowth (hg : AtLeastLinearGrowth) :
    AmusicalInfinitelyManyOrbits := by
  by_contra hfin
  obtain ⟨x, hx0, hinf, hrec⟩ := exists_sublinearlyRecurrent_of_finitelyManyOrbits hfin
  obtain ⟨c, hc, J, hJ⟩ := hg x hx0 hinf
  obtain ⟨j, hjJ, hj⟩ := hrec (2 / c) (by positivity) (J + 1)
  have h1 := hJ j (by omega)
  have hjpos : (0 : ℝ) < |(j : ℝ)| := by
    have : (1 : ℤ) ≤ |j| := by omega
    exact_mod_cast lt_of_lt_of_le one_pos this
  have : 2 / c * (c * |(j : ℝ)|) ≤ |(j : ℝ)| :=
    le_trans (mul_le_mul_of_nonneg_left h1 (by positivity)) hj
  rw [← mul_assoc, div_mul_cancel₀ 2 hc.ne'] at this
  linarith

end CollatzMoonshot.Amusical
