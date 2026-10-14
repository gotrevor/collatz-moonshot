/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalOddRewire
import CollatzMoonshot.AmusicalRewireRatio.Restriction
import CollatzMoonshot.AmusicalReglue.BackwardStep
import CollatzMoonshot.AmusicalReglue.General

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

/-- A non-periodic point has an infinite orbit. -/
theorem infinite_orbit_of_not_periodic {f : Equiv.Perm ℕ} {x : ℕ} (hx : ¬ PermPeriodic f x) :
    (Set.range fun j : ℤ => (f ^ j) x).Infinite := by
  have key (i j : ℤ) (hlt : i < j) (hij : (f ^ i) x = (f ^ j) x) : False := by
    apply hx
    refine ⟨(j - i).toNat, by omega, ?_⟩
    have : (f ^ ((j - i).toNat : ℤ)) x = x := by
      rw [Int.toNat_of_nonneg (by omega), show j - i = -i + j by ring, zpow_add,
        Equiv.Perm.mul_apply, ← hij, ← Equiv.Perm.mul_apply, ← zpow_add]
      simp
    rwa [zpow_natCast, Equiv.Perm.coe_pow] at this
  refine Set.infinite_range_of_injective fun i j hij => ?_
  rcases lt_trichotomy i j with h | h | h
  · exact (key i j h hij).elim
  · exact h
  · exact (key j i h hij.symm).elim

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
  have hglue (x : ℕ) (hx : ¬ PermPeriodic f x) : GluePt f Set.univ x :=
    ⟨infinite_orbit_of_not_periodic hx, fun K => ⟨K, le_rfl, trivial⟩,
      fun K => ⟨K, le_rfl, trivial⟩⟩
  have hsp : {y | GluePt f Set.univ y ∧ y ∈ Set.univ ∧ f.symm y ∈ Set.univ}.Infinite :=
    hcyc.infinite_compl.mono fun y hy => ⟨hglue y hy, trivial, trivial⟩
  obtain ⟨π, -, hchg, hper, hsame, hsurv⟩ :=
    exists_reglue_of_gluable f Set.univ hcyc hglue hsp F G hF hG
  exact ⟨π, Filter.Eventually.of_forall hchg, hper, hsame, hsurv⟩

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
  set σ := amusicalNatPerm
  have hglue (x : ℕ) (hx : ¬ PermPeriodic σ x) : GluePt σ {n | Odd n} x :=
    gluePt_odd_of_infinite (infinite_orbit_of_not_periodic hx)
  have hsp : {y | GluePt σ {n | Odd n} y ∧ y ∈ {n | Odd n} ∧
      σ.symm y ∈ {n | Odd n}}.Infinite := by
    have h6 : {y : ℕ | y % 6 = 1}.Infinite :=
      (Set.infinite_range_of_injective (f := fun n : ℕ => 6 * n + 1) fun a b h => by
        simp only at h; omega).mono (by rintro _ ⟨n, rfl⟩; simp only [Set.mem_ofPred_eq]; omega)
    refine (h6.sdiff hcyc).mono fun y hy => ?_
    have hy6 : y % 6 = 1 := hy.1
    refine ⟨hglue y hy.2, ?_, ?_⟩
    · exact Nat.odd_iff.2 (by omega)
    · refine Nat.odd_iff.2 ?_
      have h : ((σ.symm y : ℕ) : ℤ) = amusicalInv y := amusicalNatPerm_symm_apply_cast y
      unfold amusicalInv at h
      split_ifs at h <;> omega
  obtain ⟨π, hS, hchg, hper, hsame, hsurv⟩ :=
    exists_reglue_of_gluable σ {n | Odd n} hcyc hglue hsp F G hF hG
  refine ⟨π, fun m => ?_, Filter.Eventually.of_forall hchg, hper, hsame, hsurv⟩
  by_cases h : π (2 * m) = σ (2 * m)
  · apply Nat.cast_injective (R := ℤ)
    rw [h, amusicalNatPerm_apply_cast]
    push_cast
    exact amusical_two_mul m
  · exact absurd (hS _ h) (by simp)

/-- **Proved (why Π′ uses singleton spine pieces).**  If `π (2m) = 3m` for all `m`, a forward
survivor `3k` makes `2k` a survivor.  So every survivor `m` brings `v₃(m) + 1` survivors below it,
and an `E`-run spine piece `2ᵃr, …, 3ᵃr` survives whole.  That kills the paper route's bound
`Σ_{s_b < X} (log₂ X + 1)` for slowly growing `G`.  The proof instead takes the spine at
non-periodic `y ≡ 1 (mod 6)`: `y` and `U⁻¹ y` are both odd, so `{y}` is a singleton piece with
odd cuts. -/
theorem permFwdSurvivor_two_mul {π : Equiv.Perm ℕ} (h2 : ∀ m, π (2 * m) = 3 * m) {k : ℕ}
    (hk : PermFwdSurvivor π (3 * k)) : PermFwdSurvivor π (2 * k) := by
  intro t
  rcases t with _ | s
  · exact le_rfl
  · rw [Function.iterate_succ_apply, h2]
    exact le_trans (by omega) (hk s)

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
