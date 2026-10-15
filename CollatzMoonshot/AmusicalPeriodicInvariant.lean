/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalSeventh

/-!
# Periodic `U`-invariant functions are constant (the arithmetic core of Theorem Z, research §48)

Theorem Z (research §48, checked by the "zverify" agent) says a finite affine operator that
commutes with `U` and is an isometry is unitary.  Its only use of `U`'s arithmetic is that the
column and row masses `‖S δ_n‖²`, `‖S* δ_m‖²` are `U`-invariant and agree with periodic functions
off a finite set, hence are constant.  That step is below.

**`periodic_invariant_const`.**  An `M`-periodic function on `ℤ` with `f ∘ U = f` is constant: each
level set is a union of residue classes mod `M` that `U` maps onto itself, so it is empty or
everything (`amusical_pow_classUnion_invariant`).

**`periodic_eventually_invariant_const`.**  The same if `f (U n) = f n` only for `|n| ≥ N`: since
`U` is affine on residues mod 4, `n ↦ f (U n)` is `4M`-periodic, so the defect vanishes everywhere.
-/

namespace CollatzMoonshot.Amusical

/-- An `M`-periodic function is `j M`-periodic for every integer `j`. -/
theorem periodic_int_mul {α : Type*} (f : ℤ → α) (M : ℤ) (hper : ∀ n, f (n + M) = f n)
    (j k : ℤ) : f (k + j * M) = f k := by
  induction j using Int.induction_on with
  | zero => simp
  | succ i ih => rw [show k + (i + 1) * M = k + i * M + M by ring, hper, ih]
  | pred i ih =>
    rw [← ih, ← hper]; congr 1; ring

/-- An `M`-periodic function only sees the residue mod `M`. -/
theorem periodic_eq_mod {α : Type*} (f : ℤ → α) (M : ℕ) (hM : 0 < M)
    (hper : ∀ n, f (n + M) = f n) (k : ℤ) : f (((k : ZMod M).val : ℤ)) = f k := by
  have : NeZero M := ⟨hM.ne'⟩
  rw [ZMod.val_intCast]
  have := periodic_int_mul f M hper (k / M) (k % M)
  rw [← this]; congr 1; exact Int.emod_add_ediv_mul k M

/-- **Proved.**  An `M`-periodic `U`-invariant function on `ℤ` is constant. -/
theorem periodic_invariant_const {α : Type*} (f : ℤ → α) (M : ℕ) (hM : 0 < M)
    (hper : ∀ n, f (n + M) = f n) (hinv : ∀ n, f (amusical n) = f n) (n m : ℤ) : f n = f m := by
  set R : Set (ZMod M) := {r | f (r.val : ℤ) = f n} with hR
  have hS : {k : ℤ | (k : ZMod M) ∈ R} = {k | f k = f n} := by
    ext k; simp [hR, periodic_eq_mod f M hM hper]
  have himg : (amusical^[1]) '' {k : ℤ | (k : ZMod M) ∈ R} = {k : ℤ | (k : ZMod M) ∈ R} := by
    rw [hS, Function.iterate_one]
    ext k
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨j, hj, rfl⟩; rw [hinv, hj]
    · intro hk
      exact ⟨amusicalInv k, by rw [← hinv, amusical_amusicalInv, hk], amusical_amusicalInv k⟩
  rcases amusical_pow_classUnion_invariant 1 M one_pos hM R himg with h | h
  · have : n ∈ {k : ℤ | (k : ZMod M) ∈ R} := by rw [hS]; rfl
    simp [h] at this
  · have : m ∈ {k : ℤ | (k : ZMod M) ∈ R} := by simp [h]
    rw [hS] at this; exact this.symm

/-- **Proved.**  The same when invariance holds only away from a finite window. -/
theorem periodic_eventually_invariant_const {α : Type*} (f : ℤ → α) (M N : ℕ) (hM : 0 < M)
    (hper : ∀ n, f (n + M) = f n) (hinv : ∀ n : ℤ, (N : ℤ) ≤ |n| → f (amusical n) = f n)
    (n m : ℤ) : f n = f m := by
  have hg : ∀ k, f (amusical (k + 4 * M)) = f (amusical k) := by
    intro k
    rw [amusical_add_four_mul]
    split_ifs
    · exact periodic_int_mul f M hper 6 _
    · exact periodic_int_mul f M hper 3 _
  refine periodic_invariant_const f M hM hper (fun k => ?_) n m
  obtain ⟨j, hjd⟩ : ∃ j : ℤ, j = N + |k| := ⟨_, rfl⟩
  have hj : (N : ℤ) ≤ |k + j * (4 * M)| := by
    have h1 : (1 : ℤ) ≤ M := by exact_mod_cast hM
    have h0 : 0 ≤ j := by rw [hjd]; positivity
    have : 4 * j ≤ j * (4 * M) := by nlinarith
    have hk := neg_abs_le k
    rw [abs_of_nonneg (by linarith)]
    linarith
  calc f (amusical k) = f (amusical (k + j * (4 * M))) :=
        (periodic_int_mul (fun x => f (amusical x)) (4 * M) hg j k).symm
    _ = f (k + j * (4 * M)) := hinv _ hj
    _ = f k := by
        rw [show j * (4 * (M : ℤ)) = (4 * j) * M by ring]
        exact periodic_int_mul f M hper _ k

end CollatzMoonshot.Amusical
