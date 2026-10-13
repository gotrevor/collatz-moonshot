/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Obstructions.Amusical

/-!
# Time reversal: the mechanism the amusical permutation lacks

From the 2026-10-13 "relative" research agent.  A permutation `σ` with a reversing involution
`ι` (`ι σ ι = σ⁻¹`) has each orbit meeting `Fix ι` in at most two points, so an infinite fixed
set forces infinitely many orbits.  The Gaussian relative in `GaussianRelative.lean` has
complex conjugation as such a reversor.  For `U`:

* Klamkin's problem (a) is *equivalent* to the existence of a reversing involution of `U` with
  infinitely many nonnegative fixed points (`infinitelyManyOrbits_iff_reversor`), so a reversor
  is a costume of the problem in general;
* but **no reversor is affine on finitely many pieces** (`no_piecewiseAffine_reversor`): every
  step of `U` adds `1` to the `3`-adic valuation of the slope and every step of `U⁻¹` removes
  one, and a piecewise-affine conjugacy changes valuations by a bounded amount.  `ℚ` has no
  automorphism exchanging `2` and `3`; in `ℤ[i]` conjugation exchanges `2 + i` and `2 − i`.

Treadmill target (`KICKOFF-2026-10-13-amusical-reversal.md`): close every `sorry` here.
-/

namespace CollatzMoonshot.Amusical

/-- **The reversal lemma.**  If `ι` is an involution reversing `σ` and both `x` and `σ^k x` are
fixed by `ι`, then `σ^(2k) x = x`. -/
theorem reversing_zpow_fixed {α : Type*} {σ ι : Equiv.Perm α} (hι : ι * ι = 1)
    (hrev : ι * σ * ι = σ⁻¹) {x : α} (hx : ι x = x) {k : ℤ} (hk : ι ((σ ^ k) x) = (σ ^ k) x) :
    (σ ^ (2 * k)) x = x := by
  have hinv : ι⁻¹ = ι := (eq_inv_of_mul_eq_one_left hι).symm
  -- conjugation by `ι` is a group hom, so it reverses every power
  have hpow : ι * σ ^ k * ι = σ ^ (-k) := by
    have := map_zpow (MulAut.conj ι) σ k
    simp only [MulAut.conj_apply, hinv] at this
    rw [this, hrev, inv_zpow', zpow_neg]
  have h1 : (σ ^ k) x = (σ ^ (-k)) x := by
    calc (σ ^ k) x = ι ((σ ^ k) x) := hk.symm
      _ = ι ((σ ^ k) (ι x)) := by rw [hx]
      _ = (ι * σ ^ k * ι) x := rfl
      _ = (σ ^ (-k)) x := by rw [hpow]
  calc (σ ^ (2 * k)) x = (σ ^ k) ((σ ^ k) x) := by rw [two_mul, zpow_add, Equiv.Perm.mul_apply]
    _ = (σ ^ k) ((σ ^ (-k)) x) := by rw [← h1]
    _ = x := by rw [← Equiv.Perm.mul_apply, ← zpow_add, add_neg_cancel, zpow_zero]; rfl

/-- **Target.**  An orbit of a reversible permutation meets the fixed set of the reversor in at
most two points (at most one if the orbit is infinite; `k ≡ 0, p/2 (mod p)` on a `p`-cycle). -/
theorem orbit_inter_fixedPoints_ncard_le_two {α : Type*} {σ ι : Equiv.Perm α}
    (hι : ι * ι = 1) (hrev : ι * σ * ι = σ⁻¹) (x : α) :
    (Set.range (fun k : ℤ => (σ ^ k) x) ∩ Function.fixedPoints ι).ncard ≤ 2 := by
  sorry

/-- **Target.**  Klamkin's problem (a) is equivalent to the existence of a sign-preserving
reversing involution of `U` with infinitely many nonnegative fixed points.  (`⇐`: the orbit
count lemma above.  `⇒`: on each orbit `(x_k)` with chosen base point, set `ι x_k = x_{-k}`.) -/
theorem infinitelyManyOrbits_iff_reversor :
    AmusicalInfinitelyManyOrbits ↔ ∃ ι : Equiv.Perm ℤ, ι * ι = 1 ∧
      ι * amusicalPerm * ι = amusicalPerm⁻¹ ∧ (∀ x, 0 ≤ ι x ↔ 0 ≤ x) ∧
      {x : ℤ | 0 ≤ x ∧ ι x = x}.Infinite := by
  sorry

/-- **Target (Theorem NR).**  No bijection of `ℤ` that is affine with rational slope on each of
finitely many pieces (`c · ι x = a · x + b` on piece `j`) conjugates `U` to `U⁻¹`.  Paper proof:
`ι U^ℓ = U^{-ℓ} ι`; refine `ℤ` into finitely many cells (the piece of `n`, the residue class of
`n` fixing the first `ℓ` branches of `U`, the piece of `U^ℓ n`, the class of `ι n` for `U^{-ℓ}`);
some cell is infinite; on it both sides are single affine maps agreeing at two points, so their
slopes agree: `v₃(slope) + ℓ = v₃(slope') − ℓ`, impossible once `2ℓ` exceeds twice the largest
`|v₃|` among the finitely many piece slopes. -/
theorem no_piecewiseAffine_reversor :
    ¬ ∃ (ι : Equiv.Perm ℤ) (n : ℕ) (piece : ℤ → Fin n) (a b c : Fin n → ℤ),
      (∀ j, c j ≠ 0) ∧ (∀ x, c (piece x) * ι x = a (piece x) * x + b (piece x)) ∧
      ι * amusicalPerm * ι⁻¹ = amusicalPerm⁻¹ := by
  sorry

end CollatzMoonshot.Amusical
