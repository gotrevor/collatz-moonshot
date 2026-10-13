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

/-- Two `L`-window minima at increasing orbit indices no more than `L` apart coincide. -/
theorem IsWindowMin.eq_of_orbit_indices_of_lt {L : ℕ} {x n m : ℤ} {i j : ℤ}
    (hn : IsWindowMin L n) (hm : IsWindowMin L m)
    (hi : (amusicalPerm ^ i) x = n) (hj : (amusicalPerm ^ j) x = m)
    (hij : i < j) (hdist : j - i ≤ (L : ℤ)) : n = m := by
  set t := (j - i).toNat with ht
  have hji0 : 0 ≤ j - i := by omega
  have htcast : (t : ℤ) = j - i := by simp [t, Int.toNat_of_nonneg hji0]
  have htpos : 0 < t := by
    exact_mod_cast (show (0 : ℤ) < (t : ℤ) by rw [htcast]; omega)
  have htL : t ≤ L := by exact_mod_cast (show (t : ℤ) ≤ L by rwa [htcast])
  have hiter : amusical^[t] n = m := by
    rw [amusical_iterate_eq_perm_pow, ← hi, ← hj, ← Equiv.Perm.mul_apply, ← zpow_add]
    congr 2
    omega
  have heq := hn.iterate_eq_of_isWindowMin htpos htL (hiter ▸ hm)
  exact heq.symm.trans hiter

/-- Two `L`-window minima represented at orbit indices at distance at most `L` coincide. -/
theorem IsWindowMin.eq_of_orbit_indices {L : ℕ} {x n m : ℤ} {i j : ℤ}
    (hn : IsWindowMin L n) (hm : IsWindowMin L m)
    (hi : (amusicalPerm ^ i) x = n) (hj : (amusicalPerm ^ j) x = m)
    (hdist : |j - i| ≤ (L : ℤ)) : n = m := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact hn.eq_of_orbit_indices_of_lt hm hi hj hij
      (by simpa [abs_of_nonneg (show 0 ≤ j - i by omega)] using hdist)
  · exact hi.symm.trans hj
  · exact (hm.eq_of_orbit_indices_of_lt hn hj hi hji
      (by simpa [abs_of_nonpos (show j - i ≤ 0 by omega)] using hdist)).symm

/-- Packing bound for window minima on one orbit.  Around every chosen orbit index put the
`L+1` consecutive indices beginning there.  The preceding separation lemma makes these blocks
disjoint, while a uniform index bound puts all blocks in one integer interval. -/
theorem windowMin_card_mul_le {L m : ℕ} {x : ℤ} (S : Finset ℕ)
    (hwin : ∀ n ∈ S, IsWindowMin L (n : ℤ))
    (htime : ∀ n ∈ S, ∃ j : ℤ, (amusicalPerm ^ j) x = n ∧ |j| ≤ (m : ℤ)) :
    S.card * (L + 1) ≤ 2 * (m + L) + 1 := by
  classical
  choose! g hg hgabs using htime
  let D := S.product (Finset.range (L + 1))
  let shift : ℕ × ℕ → ℤ := fun p => g p.1 + p.2
  have hinj : Set.InjOn shift D := by
    rintro ⟨n, r⟩ hnr ⟨n', r'⟩ hnr' heq
    change (n, r) ∈ S.product (Finset.range (L + 1)) at hnr
    change (n', r') ∈ S.product (Finset.range (L + 1)) at hnr'
    have hnr0 := Finset.mem_product.mp hnr
    have hnr0' := Finset.mem_product.mp hnr'
    have hrL := Finset.mem_range.mp hnr0.2
    have hrL' := Finset.mem_range.mp hnr0'.2
    have hdist : |g n' - g n| ≤ (L : ℤ) := by
      dsimp only [shift] at heq
      have hr : (r : ℤ) ≤ L := by exact_mod_cast (show r ≤ L by omega)
      have hr' : (r' : ℤ) ≤ L := by exact_mod_cast (show r' ≤ L by omega)
      rw [abs_le]
      constructor <;> omega
    have hnn' : (n : ℤ) = n' :=
      (hwin n hnr0.1).eq_of_orbit_indices (hwin n' hnr0'.1) (hg n hnr0.1)
        (hg n' hnr0'.1) hdist
    have hn : n = n' := by exact_mod_cast hnn'
    subst n'
    have hr : r = r' := by
      dsimp only [shift] at heq
      omega
    subst r'
    rfl
  have hsubset : D.image shift ⊆ Finset.Icc (-(m + L : ℕ) : ℤ) (m + L : ℕ) := by
    intro z hz
    obtain ⟨⟨n, r⟩, hnr, rfl⟩ := Finset.mem_image.mp hz
    change (n, r) ∈ S.product (Finset.range (L + 1)) at hnr
    have hnr0 := Finset.mem_product.mp hnr
    have hrL := Finset.mem_range.mp hnr0.2
    have habs := hgabs n hnr0.1
    have hbounds := abs_le.mp habs
    have hr : (r : ℤ) ≤ L := by exact_mod_cast (show r ≤ L by omega)
    simp only [Finset.mem_Icc, shift]
    push_cast at hbounds hr ⊢
    omega
  calc
    S.card * (L + 1) = D.card := by simp [D]
    _ = (D.image shift).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.Icc (-(m + L : ℕ) : ℤ) (m + L : ℕ)).card :=
      Finset.card_le_card hsubset
    _ = 2 * (m + L) + 1 := by rw [Int.card_Icc]; omega

open Classical in
/-- Quantitative form of the packing bound when large orbit indices grow at most linearly in
the value they represent. -/
theorem windowMin_on_orbit_card_mul_le (L X J : ℕ) (x : ℤ) (C : ℝ) (hC : 0 < C)
    (hlinear : ∀ j : ℤ, (J : ℤ) ≤ |j| →
      |(j : ℝ)| < C * (((amusicalPerm ^ j) x : ℤ) : ℝ)) :
    ((Finset.range X).filter fun n : ℕ =>
      IsWindowMin L (n : ℤ) ∧ (n : ℤ) ∈ amusicalOrbit x).card * (L + 1) ≤
      2 * (Nat.ceil (C * X) + J + L) + 1 := by
  classical
  let S := (Finset.range X).filter fun n : ℕ =>
    IsWindowMin L (n : ℤ) ∧ (n : ℤ) ∈ amusicalOrbit x
  apply windowMin_card_mul_le S (m := Nat.ceil (C * X) + J)
  · intro n hn
    exact (Finset.mem_filter.mp hn).2.1
  · intro n hn
    have hn' := Finset.mem_filter.mp hn
    obtain ⟨j, hj⟩ := hn'.2.2
    refine ⟨j, hj, ?_⟩
    by_cases hsmall : |j| < (J : ℤ)
    · push_cast
      omega
    · have hJ : (J : ℤ) ≤ |j| := le_of_not_gt hsmall
      have hjlin := hlinear j hJ
      change (amusicalPerm ^ j) x = (n : ℤ) at hj
      rw [hj] at hjlin
      have hnX : (n : ℝ) < X := by exact_mod_cast Finset.mem_range.mp hn'.1
      have hjX : |(j : ℝ)| < C * X := lt_trans hjlin (mul_lt_mul_of_pos_left hnX hC)
      have hceil : C * X ≤ Nat.ceil (C * X) := Nat.le_ceil _
      have hceilJ : (Nat.ceil (C * X) : ℝ) ≤ (Nat.ceil (C * X) + J : ℕ) := by
        exact_mod_cast Nat.le_add_right (Nat.ceil (C * X)) J
      push_cast at hceilJ
      have hreal : |(j : ℝ)| ≤ (Nat.ceil (C * X) + J : ℕ) := by
        push_cast
        exact le_trans hjX.le (hceil.trans hceilJ)
      exact_mod_cast hreal

/-- **Target.**  The sublinear recurrence: finitely many orbits would force some infinite orbit
to come back below `|j|/C` at arbitrarily late times, for every `C`.  Paper proof: at least
`δ_L X − o(X) ≥ X/37` window minima lie below `X`; on one chain their times are more than `L`
apart, so `k` chains span time `≥ L X/37 − O(k)`; one chain has `|j| ≥ L X/(75k)` with value
`< X`; let `L → ∞` and pigeonhole over the finitely many chains. -/
theorem exists_sublinearlyRecurrent_of_finitelyManyOrbits (h : ¬ AmusicalInfinitelyManyOrbits) :
    ∃ x : ℤ, 0 ≤ x ∧ (amusicalOrbit x).Infinite ∧ ∀ C : ℝ, 0 < C → ∀ J : ℕ,
      ∃ j : ℤ, (J : ℤ) ≤ |j| ∧ C * (((amusicalPerm ^ j) x : ℤ) : ℝ) ≤ |(j : ℝ)| := by
  classical
  rw [AmusicalInfinitelyManyOrbits, Set.not_infinite] at h
  set T := h.toFinset with hT
  have hmem : ∀ O ∈ T, ∃ x : ℤ, 0 ≤ x ∧ O = amusicalOrbit x := fun O hO => by
    simpa [hT] using hO
  choose! seed hseed0 hseedO using hmem
  by_contra hrec
  have hfail : ∀ O ∈ T, O.Infinite → ∃ C : ℝ, 0 < C ∧ ∃ J : ℕ, ∀ j : ℤ,
      (J : ℤ) ≤ |j| → |(j : ℝ)| < C * (((amusicalPerm ^ j) (seed O) : ℤ) : ℝ) := by
    intro O hO hOinf
    have hseedinf : (amusicalOrbit (seed O)).Infinite := by rwa [← hseedO O hO]
    have hn : ¬ (∀ C : ℝ, 0 < C → ∀ J : ℕ, ∃ j : ℤ,
        (J : ℤ) ≤ |j| ∧
          C * (((amusicalPerm ^ j) (seed O) : ℤ) : ℝ) ≤ |(j : ℝ)|) := by
      intro hsub
      exact hrec ⟨seed O, hseed0 O hO, hseedinf, hsub⟩
    push Not at hn
    exact hn
  have hdata : ∀ O ∈ T, ∃ C : ℝ, 0 < C ∧ ∃ J : ℕ, O.Infinite → ∀ j : ℤ,
      (J : ℤ) ≤ |j| → |(j : ℝ)| < C * (((amusicalPerm ^ j) (seed O) : ℤ) : ℝ) := by
    intro O hO
    by_cases hOinf : O.Infinite
    · obtain ⟨C, hC, J, hJ⟩ := hfail O hO hOinf
      exact ⟨C, hC, J, fun _ => hJ⟩
    · exact ⟨1, by norm_num, 0, fun h => absurd h hOinf⟩
  choose! C hC J hlinear using hdata
  let A : ℝ := ∑ O ∈ T, C O
  have hA0 : 0 ≤ A := by
    apply Finset.sum_nonneg
    intro O hO
    exact (hC O hO).le
  obtain ⟨L, hL⟩ := exists_nat_gt (75 * A)
  let gap : ℝ := (L + 1) / 37 - 2 * A
  have hgap : 0 < gap := by
    dsimp only [gap]
    nlinarith
  let K : ℕ := ∑ O ∈ T,
    (2 * (J O + L + 1) + 1 + O.ncard * (L + 1))
  have hdelta : (1 / 37 : ℝ) < ((fwdSurv L * bwdSurv L : ℚ) : ℝ) := by
    have hge : (1 / 36 : ℝ) ≤ ((fwdSurv L * bwdSurv L : ℚ) : ℝ) := by
      have hcast := (Rat.cast_le (K := ℝ)).2 (windowDensity_ge L)
      norm_num at hcast ⊢
      exact hcast
    norm_num at hge ⊢
    linarith
  have hdensity : ∀ᶠ X : ℕ in Filter.atTop,
      (1 / 37 : ℝ) <
        (((Finset.range X).filter fun n : ℕ => IsWindowMin L n).card : ℝ) / X :=
    (windowMinDensity L).eventually (lt_mem_nhds hdelta)
  have hlarge := hdensity.and
    (Filter.eventually_ge_atTop (Nat.ceil ((K : ℝ) / gap) + 1))
  obtain ⟨X, hXdensity, hXlarge⟩ := hlarge.exists
  have hXpos : (0 : ℝ) < X := by
    have : (0 : ℕ) < Nat.ceil ((K : ℝ) / gap) + 1 := by omega
    exact_mod_cast lt_of_lt_of_le this hXlarge
  have hKX : (K : ℝ) < gap * X := by
    have hceil := Nat.le_ceil ((K : ℝ) / gap)
    have hratio : (K : ℝ) / gap < X := by
      have hXlarge' : ((Nat.ceil ((K : ℝ) / gap) + 1 : ℕ) : ℝ) ≤ X := by
        exact_mod_cast hXlarge
      push_cast at hXlarge'
      linarith
    rw [div_lt_iff₀ hgap] at hratio
    nlinarith
  let S := (Finset.range X).filter fun n : ℕ => IsWindowMin L n
  let F : Set ℤ → Finset ℕ := fun O =>
    (Finset.range X).filter fun n : ℕ => IsWindowMin L n ∧ (n : ℤ) ∈ O
  have hcover : S ⊆ T.biUnion F := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    rw [Finset.mem_biUnion]
    refine ⟨amusicalOrbit n, ?_, ?_⟩
    · simp [hT]
      exact ⟨n, by positivity, rfl⟩
    · simp only [F, Finset.mem_filter, hn'.1, hn'.2, true_and]
      exact mem_amusicalOrbit_self n
  have hcard : S.card ≤ ∑ O ∈ T, (F O).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hFbound : ∀ O ∈ T, (F O).card * (L + 1) ≤
      2 * (Nat.ceil (C O * X) + J O + L) + 1 + O.ncard * (L + 1) := by
    intro O hO
    by_cases hOinf : O.Infinite
    · have hb := windowMin_on_orbit_card_mul_le L X (J O) (seed O) (C O) (hC O hO)
          (hlinear O hO hOinf)
      rw [← hseedO O hO] at hb
      exact le_add_right hb
    · have hOfin : O.Finite := Set.not_infinite.mp hOinf
      have hcardO : (F O).card ≤ O.ncard := by
        have hi : (F O).card ≤ hOfin.toFinset.card := by
          refine Finset.card_le_card_of_injOn (fun n : ℕ => (n : ℤ)) ?_ ?_
          · intro n hn
            exact hOfin.mem_toFinset.mpr (Finset.mem_filter.mp hn).2.2
          · intro a _ b _ hab
            exact Int.ofNat_inj.mp hab
        rwa [← Set.ncard_eq_toFinset_card O hOfin] at hi
      have := Nat.mul_le_mul_right (L + 1) hcardO
      omega
  let R : Set ℤ → ℕ := fun O =>
    2 * (Nat.ceil (C O * X) + J O + L) + 1 + O.ncard * (L + 1)
  have htotal : S.card * (L + 1) ≤ ∑ O ∈ T, R O := by
    calc
      S.card * (L + 1) ≤ (∑ O ∈ T, (F O).card) * (L + 1) :=
        Nat.mul_le_mul_right (L + 1) hcard
      _ = ∑ O ∈ T, (F O).card * (L + 1) := by rw [Finset.sum_mul]
      _ ≤ ∑ O ∈ T, R O := by
        apply Finset.sum_le_sum
        intro O hO
        exact hFbound O hO
  have hpoint : ∀ O ∈ T, ((R O : ℕ) : ℝ) ≤
      2 * C O * X + (2 * (J O + L + 1) + 1 + O.ncard * (L + 1) : ℕ) := by
    intro O hO
    have hceil := Nat.ceil_lt_add_one (mul_nonneg (hC O hO).le (by positivity : (0 : ℝ) ≤ X))
    dsimp only [R]
    push_cast at hceil ⊢
    nlinarith
  have hsum : ((∑ O ∈ T, R O : ℕ) : ℝ) ≤ 2 * A * X + K := by
    calc
      ((∑ O ∈ T, R O : ℕ) : ℝ) = ∑ O ∈ T, ((R O : ℕ) : ℝ) := by
        push_cast
        rfl
      _ ≤ ∑ O ∈ T,
          (2 * C O * X + (2 * (J O + L + 1) + 1 + O.ncard * (L + 1) : ℕ)) := by
        apply Finset.sum_le_sum
        intro O hO
        exact hpoint O hO
      _ = 2 * A * X + K := by
        simp only [A, K]
        push_cast
        rw [Finset.sum_add_distrib]
        congr 1
        rw [Finset.mul_sum, Finset.sum_mul]
  have htotalR : (S.card : ℝ) * (L + 1) ≤ 2 * A * X + K := by
    have hcast : ((S.card * (L + 1) : ℕ) : ℝ) ≤
        ((∑ O ∈ T, R O : ℕ) : ℝ) := by exact_mod_cast htotal
    calc
      (S.card : ℝ) * (L + 1) = ((S.card * (L + 1) : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ ((∑ O ∈ T, R O : ℕ) : ℝ) := hcast
      _ ≤ 2 * A * X + K := hsum
  have hdensS : (1 / 37 : ℝ) < (S.card : ℝ) / X := by
    simpa only [S] using hXdensity
  have hSX : (1 / 37 : ℝ) * X < S.card := (lt_div_iff₀ hXpos).mp hdensS
  have hlower : X * ((L + 1 : ℕ) : ℝ) / 37 < (S.card : ℝ) * (L + 1) := by
    have hLpos : (0 : ℝ) < (L + 1 : ℕ) := by positivity
    have := mul_lt_mul_of_pos_right hSX hLpos
    norm_num at this ⊢
    nlinarith
  dsimp only [gap] at hKX
  push_cast at hlower htotalR
  nlinarith

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
