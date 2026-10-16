/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalOddRewire

/-!
# Finite-depth fusion (meta-theorem M1, research §55)

An argument that reads each point `n` of `U` only to a finite depth `D(n)`, and tolerates a sparse
set of exceptions, cannot decide whether `U` has infinitely many infinite orbits.

`exists_depthFusion`: for any depth function `D` and any budget `G` with `G(X)/D*(X) → ∞`
(`D*(X) = max_{n < X} D(n)`), there is a permutation `τ` of `ℕ` that keeps `U`'s even branch and
every finite orbit of `U`, fuses all infinite orbits of `U` into one, and agrees with `U` to depth
`D(n)` at every `n < X` outside a set of at most `G(X)` points, for all large `X`.  Theorem TT
(`tail_threshold`) is the infinite-depth version.

Proof idea: take the odd rewire `exists_oddRewire` with a change budget `F` small enough that the
changes below `B(X)` (the largest value on a depth-`D*(X)` segment from `n < X`) number at most
`G(X)/(2D*(X) + 1)`.  A disagreement at depth `d` at `n` needs a change of `τ` at some point of
`U`'s segment `U^i n`, `|i| ≤ d` (backward disagreements too: `τ⁻¹ y ≠ U⁻¹ y` makes `U⁻¹ y` a
change of `τ`), and each change point lies on at most `2D*(X) + 1` such segments.
-/

namespace CollatzMoonshot.Amusical

/-- `τ` and `U` disagree at depth `d` at `n`: `τ^j n ≠ U^j n` for some `|j| ≤ d`. -/
def DisagreeAtDepth (τ : Equiv.Perm ℕ) (d n : ℕ) : Prop :=
  ∃ j : ℤ, |j| ≤ d ∧ (τ ^ j) n ≠ (amusicalNatPerm ^ j) n

/-- The largest depth `max_{n < X} D(n)`. -/
def maxDepth (D : ℕ → ℕ) (X : ℕ) : ℕ :=
  (Finset.range X).sup D

open Classical in
/-- **Open (M1, finite-depth fusion).**  If `G(X)/(D*(X) + 1) → ∞`, some permutation of `ℕ` with
`U`'s even branch and finite orbits, and a single infinite orbit through all infinite orbits of
`U`, agrees with `U` to depth `D(n)` at all but at most `G(X)` points `n < X`, for all large `X`. -/
theorem exists_depthFusion (D G : ℕ → ℕ)
    (hG : ∀ C : ℕ, ∀ᶠ X in Filter.atTop, C * (maxDepth D X + 1) ≤ G X) :
    ∃ τ : Equiv.Perm ℕ,
      (∀ m : ℕ, τ (2 * m) = 3 * m) ∧
      (∀ n : ℕ, (amusicalOrbit n).Finite → (τ n : ℤ) = amusical n) ∧
      (∀ a b : ℕ, (amusicalOrbit a).Infinite → (amusicalOrbit b).Infinite →
        ∃ j : ℤ, (τ ^ j) a = b) ∧
      ∀ᶠ X in Filter.atTop,
        ((Finset.range X).filter fun n => DisagreeAtDepth τ (D n) n).card ≤ G X := by
  sorry

end CollatzMoonshot.Amusical
