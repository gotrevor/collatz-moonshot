/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalOddRewire
import CollatzMoonshot.AmusicalRewireRatio.Restriction
import CollatzMoonshot.AmusicalReglue.BackwardStep
import CollatzMoonshot.AmusicalReglue.Segments
import CollatzMoonshot.AmusicalReglue.WordOrder

/-!
# Sparse regluing makes forward survivors arbitrarily sparse (Theorem Π)

The 2026-10-14 "fsarith" agent (research §41) asked for an arithmetic mechanism forcing many
forward survivors, and found instead that survivor density is a gluing artifact.

**`exists_reglue_sparseFS` (Theorem Π).**  Let `f` be a permutation of `ℕ` with finitely many
periodic points.  For any `F, G → ∞` there is a permutation `π` that differs from `f` (or `π⁻¹`
from `f⁻¹`) at `≤ F X` points below `X`, keeps `f`'s cycles, merges all infinite orbits into one,
and has `≤ G X` forward survivors below `X`.  Construction: cut every chain at sparse high points;
group the pieces into finite blocks by their minimum along a sparse spine `s₁ < s₂ < ⋯` of
singleton pieces; traverse each block in **decreasing** order of piece minimum, and lay out the
blocks as `⋯ B₆ B₄ B₂ | B₁ B₃ B₅ ⋯`.  A non-spine point is followed inside its block by a piece of
smaller minimum, so only the spine survives.

**`exists_reglue_sparseFS_amusical` (Π′).**  For `U` every cut can be at an odd point, so
`π (2m) = 3m`, and the separation lemma, staircases and every window statistic survive.  So no
property of `U` that is robust to sparse modification implies a forward-survivor floor beyond
"infinitely many": the survivor analogue of Theorem TT (`tail_threshold`).

**`bwd_iter_affine`, `lt_bwd_iter_iff` (Lemma BW).**  The backward map is affine on residue
classes with carry `< 4^i`, so above `4^i` the sign of `V^i m − m` is that of `2^w − 3^i`.

**`chernoff_duality`.**  The forward and backward Chernoff functions agree under `s ↦ 1 − s`.
-/

namespace CollatzMoonshot.Amusical

/-- `m` is a forward survivor of the permutation `π` of `ℕ`. -/
def PermFwdSurvivor (π : Equiv.Perm ℕ) (m : ℕ) : Prop := ∀ t : ℕ, m ≤ (⇑π)^[t] m

/-- `x` lies on a cycle of `f`. -/
def PermPeriodic (f : Equiv.Perm ℕ) (x : ℕ) : Prop := ∃ k ≥ 1, (⇑f)^[k] x = x

/-- The points below `X` where `π` or `π⁻¹` differs from `f` or `f⁻¹`. -/
def nChanged (π f : Equiv.Perm ℕ) (X : ℕ) : ℕ :=
  ((Finset.range X).filter fun x => π x ≠ f x ∨ π.symm x ≠ f.symm x).card

open Classical in
/-- **Target (Theorem Π).**  Sparse regluing to one infinite orbit with arbitrarily sparse forward
survivors. -/
theorem exists_reglue_sparseFS (f : Equiv.Perm ℕ) (hcyc : {x | PermPeriodic f x}.Finite)
    (F G : ℕ → ℕ) (hF : Filter.Tendsto F .atTop .atTop) (hG : Filter.Tendsto G .atTop .atTop) :
    ∃ π : Equiv.Perm ℕ,
      (∀ᶠ X in .atTop, nChanged π f X ≤ F X) ∧
      (∀ x, PermPeriodic f x → π x = f x) ∧
      (∀ x y, ¬ PermPeriodic f x → ¬ PermPeriodic f y → π.SameCycle x y) ∧
      (∀ᶠ X in .atTop, ((Finset.range X).filter (PermFwdSurvivor π)).card ≤ G X) := by
  sorry

open Classical in
/-- **Target (Π′).**  For the amusical map all cuts can be odd, so the even branch is kept. -/
theorem exists_reglue_sparseFS_amusical (hcyc : {x | PermPeriodic amusicalNatPerm x}.Finite)
    (F G : ℕ → ℕ) (hF : Filter.Tendsto F .atTop .atTop) (hG : Filter.Tendsto G .atTop .atTop) :
    ∃ π : Equiv.Perm ℕ, (∀ m, π (2 * m) = 3 * m) ∧
      (∀ᶠ X in .atTop, nChanged π amusicalNatPerm X ≤ F X) ∧
      (∀ x, PermPeriodic amusicalNatPerm x → π x = amusicalNatPerm x) ∧
      (∀ x y, ¬ PermPeriodic amusicalNatPerm x → ¬ PermPeriodic amusicalNatPerm y →
        π.SameCycle x y) ∧
      (∀ᶠ X in .atTop, ((Finset.range X).filter (PermFwdSurvivor π)).card ≤ G X) := by
  sorry

/-- The bits consumed by the first `i` backward steps: `1` at a multiple of `3`, else `2`. -/
def bwdWeight (m i : ℕ) : ℕ :=
  i + ((Finset.range i).filter fun j => ¬ 3 ∣ amusicalNatPerm.symm^[j] m).card

theorem bwdWeight_succ (m i : ℕ) :
    bwdWeight m (i + 1) =
      bwdWeight m i + if 3 ∣ amusicalNatPerm.symm^[i] m then 1 else 2 := by
  unfold bwdWeight
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h1
  · omega
  · rw [Finset.card_insert_of_notMem (by simp)]; omega

/-- Lemma BW with the sharp carry invariant `|E| ≤ 4^i − 3^i`
(`4(4^i − 3^i) + 3^i = 4^{i+1} − 3^{i+1}`). -/
theorem bwd_iter_affine_le (m i : ℕ) :
    ∃ E : ℤ, (3 : ℤ) ^ i * (amusicalNatPerm.symm^[i] m : ℤ) = 2 ^ bwdWeight m i * m + E ∧
      |E| ≤ 4 ^ i - 3 ^ i := by
  induction i with
  | zero => exact ⟨0, by simp [bwdWeight]⟩
  | succ i ih =>
    obtain ⟨E, hE, hb⟩ := ih
    rw [Function.iterate_succ_apply', bwdWeight_succ]
    set y := amusicalNatPerm.symm^[i] m
    obtain ⟨h1, h2⟩ := three_mul_symm_step y
    have h3 : (0 : ℤ) ≤ 3 ^ i := by positivity
    have h4 : (3 : ℤ) ^ i ≤ 4 ^ i := pow_le_pow_left₀ (by norm_num) (by norm_num) i
    by_cases h : 3 ∣ y
    · refine ⟨2 * E, ?_, ?_⟩
      · rw [if_pos h, pow_succ, pow_succ]
        linear_combination 2 * hE + 3 ^ i * h1 h
      · rw [abs_mul, pow_succ, pow_succ]
        norm_num
        linarith
    · refine ⟨4 * E + 3 ^ i * (3 * (amusicalNatPerm.symm y : ℤ) - 4 * y), ?_, ?_⟩
      · rw [if_neg h, pow_add, pow_succ]
        linear_combination 4 * hE
      · have := h2 h
        calc _ ≤ |4 * E| + |3 ^ i * (3 * (amusicalNatPerm.symm y : ℤ) - 4 * y)| :=
              abs_add_le _ _
          _ ≤ 4 * |E| + 3 ^ i * 1 := by
              rw [abs_mul, abs_mul, abs_of_nonneg h3]
              have := mul_le_mul_of_nonneg_left this h3
              norm_num at this ⊢
              linarith
          _ ≤ _ := by rw [pow_succ, pow_succ]; linarith

/-- **Target (Lemma BW, affine form).** -/
theorem bwd_iter_affine (m i : ℕ) :
    ∃ E : ℤ, (3 : ℤ) ^ i * (amusicalNatPerm.symm^[i] m : ℤ) = 2 ^ bwdWeight m i * m + E ∧
      |E| < 4 ^ i := by
  obtain ⟨E, hE, hb⟩ := bwd_iter_affine_le m i
  exact ⟨E, hE, by have : (0 : ℤ) < 3 ^ i := by positivity
                   linarith⟩

/-- **Target (Lemma BW, sign form).** -/
theorem lt_bwd_iter_iff (m i : ℕ) (hi : 1 ≤ i) (hm : 4 ^ i < m) :
    m < amusicalNatPerm.symm^[i] m ↔ 3 ^ i < 2 ^ bwdWeight m i := by
  obtain ⟨E, hE, hb⟩ := bwd_iter_affine m i
  have hw : i ≤ bwdWeight m i := by unfold bwdWeight; omega
  have hne := two_pow_ne_three_pow (i := i) (hi.trans hw)
  set w := bwdWeight m i
  set v := amusicalNatPerm.symm^[i] m
  have hmZ : (4 : ℤ) ^ i < m := by exact_mod_cast hm
  have hE' := abs_lt.mp (hb.trans hmZ)
  have hT : (0 : ℤ) < 3 ^ i := by positivity
  constructor
  · intro hv
    by_contra hc
    have hlt : 2 ^ w + 1 ≤ 3 ^ i := by omega
    have hltZ : (2 : ℤ) ^ w + 1 ≤ 3 ^ i := by exact_mod_cast hlt
    have hvZ : (m : ℤ) + 1 ≤ v := by exact_mod_cast hv
    have h1 := mul_le_mul_of_nonneg_right hltZ (Int.natCast_nonneg m)
    have h2 := mul_le_mul_of_nonneg_left hvZ hT.le
    nlinarith
  · intro hc
    have hltZ : (3 : ℤ) ^ i + 1 ≤ 2 ^ w := by exact_mod_cast hc
    have h1 := mul_le_mul_of_nonneg_right hltZ (Int.natCast_nonneg m)
    have : (3 : ℤ) ^ i * m < 3 ^ i * v := by nlinarith
    exact_mod_cast lt_of_mul_lt_mul_left this hT.le

/-- **Target.**  Forward and backward Chernoff functions agree under `s ↦ 1 − s`. -/
theorem chernoff_duality (s : ℝ) :
    (1 / 3) * (3 / 2 : ℝ) ^ s + (2 / 3) * (3 / 4 : ℝ) ^ s =
      (1 / 2) * (3 / 2 : ℝ) ^ (-(1 - s)) + (1 / 2) * (3 / 4 : ℝ) ^ (-(1 - s)) := by
  rw [show -(1 - s) = s + (-1) by ring, Real.rpow_add (by norm_num), Real.rpow_add (by norm_num),
    Real.rpow_neg_one, Real.rpow_neg_one]
  ring

end CollatzMoonshot.Amusical
