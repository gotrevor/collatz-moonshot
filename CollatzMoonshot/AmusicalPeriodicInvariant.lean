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

/-- **Target.**  An `M`-periodic `U`-invariant function on `ℤ` is constant. -/
theorem periodic_invariant_const {α : Type*} (f : ℤ → α) (M : ℕ) (hM : 0 < M)
    (hper : ∀ n, f (n + M) = f n) (hinv : ∀ n, f (amusical n) = f n) (n m : ℤ) : f n = f m := by
  sorry

/-- **Target.**  The same when invariance holds only away from a finite window. -/
theorem periodic_eventually_invariant_const {α : Type*} (f : ℤ → α) (M N : ℕ) (hM : 0 < M)
    (hper : ∀ n, f (n + M) = f n) (hinv : ∀ n : ℤ, (N : ℤ) ≤ |n| → f (amusical n) = f n)
    (n m : ℤ) : f n = f m := by
  sorry

end CollatzMoonshot.Amusical
