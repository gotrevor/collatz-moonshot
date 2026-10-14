/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalCycleBound.Step

/-!
# The cycle-minimum bound `M(p, e)` in natural-number arithmetic

`natMinBound p e` is `cycleMinBound p e` with `|2^e − 3^p|` written as a natural-number case
split.  This file proves:

* `le_natMinBound`: the two Theorem A★ inequalities force `m ≤ natMinBound p e` (Bernoulli's
  inequality `(1 − 1/t)^k ≥ 1 − k/t`, cleared of denominators, replaces logarithms);
* `natMinBound_le_of_far`: if `2^e ≥ 2 · 3^p` or `3^p ≥ 2 · 2^e` then `natMinBound p e ≤ e − p`;
* `natMinBound_le_31866`: `natMinBound p e ≤ 167195612` for `p ≤ 31866` and `p < e ≤ 2p`, by one
  `decide +kernel` call on a `Nat.rec` checker that visits the two `e` with
  `2^e ≈ 3^p` for each `p`.
-/

namespace CollatzMoonshot.Amusical

/-- `|2^e − 3^p|` as a natural number. -/
def natDist (p e : ℕ) : ℕ :=
  if 3 ^ p ≤ 2 ^ e then 2 ^ e - 3 ^ p else 3 ^ p - 2 ^ e

/-- `M(p, e) = ⌊(k · max(2^e, 3^p) + D) / (3D)⌋` in `ℕ`, with `D = natDist p e`. -/
def natMinBound (p e : ℕ) : ℕ :=
  ((e - p) * max (2 ^ e) (3 ^ p) + natDist p e) / (3 * natDist p e)

theorem natAbs_two_pow_sub_three_pow (p e : ℕ) :
    Int.natAbs ((2 : ℤ) ^ e - 3 ^ p) = natDist p e := by
  have h2 : ((2 : ℤ) ^ e) = ((2 ^ e : ℕ) : ℤ) := by push_cast; rfl
  have h3 : ((3 : ℤ) ^ p) = ((3 ^ p : ℕ) : ℤ) := by push_cast; rfl
  rw [h2, h3, natDist]
  split_ifs with h <;> omega

theorem natDist_pos {p e : ℕ} (hp : 1 ≤ p) : 0 < natDist p e := by
  have hne : 2 ^ e ≠ 3 ^ p := by
    intro h
    have h3 : 3 ∣ 2 ^ e := h ▸ dvd_pow_self 3 (by omega)
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    omega
  unfold natDist
  split_ifs <;> omega

/-- Bernoulli's inequality `(1 − 1/t)^k ≥ 1 − k/t`, cleared of denominators. -/
theorem bernoulli_clear (t : ℤ) (k : ℕ) (ht : 1 ≤ t) :
    t ^ k * (t - k) ≤ (t - 1) ^ k * t := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 := mul_le_mul_of_nonneg_left ih (by omega : (0 : ℤ) ≤ t - 1)
    have h2 : (0 : ℤ) ≤ t ^ k * k := by positivity
    push_cast
    rw [pow_succ, pow_succ]
    nlinarith [h1, h2]

/-- **Real-to-floor step.**  The two Theorem A★ inequalities bound the cycle minimum `m` by
`natMinBound p e`. -/
theorem le_natMinBound {p e m : ℕ} (hp : 1 ≤ p) (hm : 1 ≤ m)
    (H1 : (3 : ℤ) ^ p * (3 * m - 1) ^ (e - p) ≤ 2 ^ e * (3 * m) ^ (e - p))
    (H2 : (2 : ℤ) ^ e * (3 * m) ^ (e - p) ≤ 3 ^ p * (3 * m + 1) ^ (e - p)) :
    m ≤ natMinBound p e := by
  have hD := natDist_pos (e := e) hp
  unfold natMinBound
  rw [Nat.le_div_iff_mul_le (by omega)]
  set k := e - p
  have h2 : ((2 : ℤ) ^ e) = ((2 ^ e : ℕ) : ℤ) := by push_cast; rfl
  have h3 : ((3 : ℤ) ^ p) = ((3 ^ p : ℕ) : ℤ) := by push_cast; rfl
  rw [h2, h3] at H1 H2
  set a := 2 ^ e
  set b := 3 ^ p
  have hm' : (1 : ℤ) ≤ m := by exact_mod_cast hm
  unfold natDist
  split_ifs with hab
  · -- `3^p ≤ 2^e`: use the upper inequality with `t = 3m + 1`.
    have hB := bernoulli_clear (3 * m + 1) k (by omega)
    simp only [add_sub_cancel_right] at hB
    have hpow : (0 : ℤ) < (3 * m + 1) ^ k := by positivity
    have ha : (0 : ℤ) ≤ a := by positivity
    have key : (a : ℤ) * (3 * m + 1 - k) ≤ b * (3 * m + 1) := by
      have := mul_le_mul_of_nonneg_left hB ha
      have h4 := mul_le_mul_of_nonneg_right H2 (by omega : (0 : ℤ) ≤ 3 * m + 1)
      refine le_of_mul_le_mul_left ?_ hpow
      nlinarith [this, h4]
    have hmax : max a b = a := max_eq_left hab
    rw [hmax]
    have : (m : ℤ) * (3 * (a - b : ℕ)) ≤ k * a + (a - b : ℕ) := by
      rw [Nat.cast_sub (show b ≤ a from hab)]
      nlinarith [key]
    exact_mod_cast this
  · -- `2^e < 3^p`: use the lower inequality with `t = 3m`.
    have hB := bernoulli_clear (3 * m) k (by omega)
    have hpow : (0 : ℤ) < (3 * m) ^ k := by positivity
    have hb : (0 : ℤ) ≤ b := by positivity
    have key : (b : ℤ) * (3 * m - k) ≤ a * (3 * m) := by
      have := mul_le_mul_of_nonneg_left hB hb
      have h4 := mul_le_mul_of_nonneg_right H1 (by omega : (0 : ℤ) ≤ 3 * m)
      refine le_of_mul_le_mul_left ?_ hpow
      nlinarith [this, h4]
    have hmax : max a b = b := max_eq_right (by omega)
    rw [hmax]
    have : (m : ℤ) * (3 * (b - a : ℕ)) ≤ k * b + (b - a : ℕ) := by
      rw [Nat.cast_sub (show a ≤ b by omega)]
      nlinarith [key]
    exact_mod_cast this

/-- **Reduction.**  Away from `2^e ≈ 3^p` the bound is at most the number `e − p` of odd steps. -/
theorem natMinBound_le_of_far {p e : ℕ} (hp : 1 ≤ p) (hpe : p < e)
    (hfar : 2 * 3 ^ p ≤ 2 ^ e ∨ 2 * 2 ^ e ≤ 3 ^ p) : natMinBound p e ≤ e - p := by
  have hD := natDist_pos (e := e) hp
  unfold natMinBound
  apply Nat.div_le_of_le_mul
  have hk : 1 ≤ e - p := by omega
  have hmax : max (2 ^ e) (3 ^ p) ≤ 2 * natDist p e := by
    unfold natDist
    rcases hfar with h | h <;> split_ifs <;> omega
  calc (e - p) * max (2 ^ e) (3 ^ p) + natDist p e
      ≤ (e - p) * (2 * natDist p e) + (e - p) * natDist p e := by
        gcongr
        exact Nat.le_mul_of_pos_left _ hk
    _ = 3 * natDist p e * (e - p) := by ring

/-! ## The kernel checker

The checker is written with `Nat.pow`, `Nat.ble` and friends directly, and recurses with a bare
`Nat.rec` whose own literal supplies `p`.  Both choices matter for the kernel: typeclass
instances and `Decidable` wrappers are re-unfolded at every step, and an accumulator `p + 1`
builds an unevaluated term.  `Nat.log2` is avoided too: the kernel unfolds it bit by bit.  The
candidate `L = ⌊p · 1.584962500721156⌋` is checked against `2^L ≤ 3^p < 2^{L+1}` instead.
Measured 2026-10-14 on `p ≤ 31866`: 9 s, 3.1 GB peak RSS (about 1 GB is the bare `lean`
process); `X = 167195611` is rejected (control). -/

/-- `natMinBound p e ≤ X`, as a `Bool` built from kernel-accelerated primitives. -/
def minBoundOkB (X p e : ℕ) : Bool :=
  cond (Nat.ble (Nat.pow 3 p) (Nat.pow 2 e))
    (Nat.ble (Nat.div (Nat.add (Nat.mul (Nat.sub e p) (Nat.pow 2 e))
      (Nat.sub (Nat.pow 2 e) (Nat.pow 3 p))) (Nat.mul 3 (Nat.sub (Nat.pow 2 e) (Nat.pow 3 p)))) X)
    (Nat.ble (Nat.div (Nat.add (Nat.mul (Nat.sub e p) (Nat.pow 3 p))
      (Nat.sub (Nat.pow 3 p) (Nat.pow 2 e))) (Nat.mul 3 (Nat.sub (Nat.pow 3 p) (Nat.pow 2 e)))) X)

/-- `e` is out of range, or `natMinBound p e ≤ X`. -/
def minBoundOkE (X p e : ℕ) : Bool :=
  Nat.ble e p || Nat.blt (Nat.mul 2 p) e || minBoundOkB X p e

/-- The candidate `⌊log₂ 3^p⌋`. -/
def log23Floor (p : ℕ) : ℕ :=
  Nat.div (Nat.mul p 1584962500721156) 1000000000000000

/-- Check `p`: the candidate is `⌊log₂ 3^p⌋`, and both `e` next to it pass. -/
def minBoundOkP (X p : ℕ) : Bool :=
  Nat.ble (Nat.pow 2 (log23Floor p)) (Nat.pow 3 p) &&
    Nat.blt (Nat.pow 3 p) (Nat.pow 2 (Nat.add (log23Floor p) 1)) &&
    minBoundOkE X p (log23Floor p) && minBoundOkE X p (Nat.add (log23Floor p) 1)

/-- Check every `p ∈ [1, n]`. -/
noncomputable def minBoundCheck (X n : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => minBoundOkP X (Nat.succ k) && ih) n

theorem minBoundOkB_iff (X p e : ℕ) : minBoundOkB X p e = true ↔ natMinBound p e ≤ X := by
  unfold minBoundOkB natMinBound natDist
  simp only [Nat.pow_eq, Nat.sub_eq, Nat.mul_eq, Nat.add_eq]
  by_cases h : 3 ^ p ≤ 2 ^ e
  · have : Nat.ble (3 ^ p) (2 ^ e) = true := Nat.ble_eq.mpr h
    simp only [this, cond_true, if_pos h, max_eq_left h, Nat.ble_eq]
    rfl
  · have : Nat.ble (3 ^ p) (2 ^ e) = false := by
      rw [← Bool.not_eq_true, Nat.ble_eq]; exact h
    simp only [this, cond_false, if_neg h, max_eq_right (by omega : 2 ^ e ≤ 3 ^ p), Nat.ble_eq]
    rfl

theorem minBoundCheck_succ (X n : ℕ) :
    minBoundCheck X (n + 1) = (minBoundOkP X (n + 1) && minBoundCheck X n) := rfl

theorem minBoundOkP_of_check {X n : ℕ} (h : minBoundCheck X n = true) :
    ∀ p, 1 ≤ p → p ≤ n → minBoundOkP X p = true := by
  induction n with
  | zero => intro p hp hpn; omega
  | succ n ih =>
    rw [minBoundCheck_succ, Bool.and_eq_true] at h
    intro p hp hpn
    rcases Nat.lt_or_ge p (n + 1) with hlt | hge
    · exact ih h.2 p hp (by omega)
    · rw [show p = n + 1 by omega]; exact h.1

theorem natMinBound_le_of_okP {X p e : ℕ} (hp : 1 ≤ p) (hpX : p ≤ X) (hpe : p < e)
    (he : e ≤ 2 * p) (h : minBoundOkP X p = true) : natMinBound p e ≤ X := by
  unfold minBoundOkP at h
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, Nat.pow_eq, Nat.add_eq] at h
  obtain ⟨⟨⟨hL1, hL2⟩, hE1⟩, hE2⟩ := h
  generalize log23Floor p = L at hL1 hL2 hE1 hE2
  have hokE : ∀ e', e' = L ∨ e' = L + 1 → p < e' → e' ≤ 2 * p → natMinBound p e' ≤ X := by
    intro e' he' hpe' he2'
    have hb : minBoundOkE X p e' = true := by rcases he' with rfl | rfl <;> assumption
    unfold minBoundOkE at hb
    simp only [Bool.or_eq_true, Nat.ble_eq, Nat.blt_eq, Nat.mul_eq] at hb
    rcases hb with (hb | hb) | hb
    · omega
    · omega
    · exact (minBoundOkB_iff X p e').mp hb
  by_cases hnear : e = L ∨ e = L + 1
  · exact hokE e hnear hpe he
  · have hfar : 2 * 3 ^ p ≤ 2 ^ e ∨ 2 * 2 ^ e ≤ 3 ^ p := by
      rcases Nat.lt_or_ge e L with hlt | hge
      · right
        calc 2 * 2 ^ e = 2 ^ (e + 1) := by ring
          _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ ≤ 3 ^ p := hL1
      · left
        calc 2 * 3 ^ p ≤ 2 * 2 ^ (L + 1) := Nat.mul_le_mul_left 2 hL2.le
          _ = 2 ^ (L + 2) := by ring
          _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact (natMinBound_le_of_far hp hpe hfar).trans (by omega)

/-- The checker's single kernel computation. -/
theorem minBoundCheck_31866 : minBoundCheck 167195612 31866 = true := by
  decide +kernel

/-- **Proved.**  `M(p, e) ≤ 167195612` for every `p ≤ 31866` and `p < e ≤ 2p`. -/
theorem natMinBound_le_31866 (p e : ℕ) (hp : 1 ≤ p) (hpP : p ≤ 31866) (hpe : p < e)
    (he : e ≤ 2 * p) : natMinBound p e ≤ 167195612 :=
  natMinBound_le_of_okP hp (by omega) hpe he
    (minBoundOkP_of_check minBoundCheck_31866 p hp hpP)

end CollatzMoonshot.Amusical
