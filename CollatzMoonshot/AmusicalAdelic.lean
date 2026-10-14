/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Amusical

/-!
# The adelic space adds nothing: lattice rigidity, and a single orbit that passes for `ℤ`

The 2026-10-14 "quasicrystal" agent embedded `ℤ` diagonally in `K = ℝ × ℤ₂ × ℤ₃`, where `U`
extends to `Û` (its three affine formulas, reading the class from the `ℤ₂` coordinate).  It asked
whether a rigidity or measure-classification property of `Û` on `K` could force infinitely many
orbits on the diagonal.  Two results say no.

**Theorem M (Masquerade, agent's proof, research §25; not in Lean).**  Either `U` has infinitely
many cycles, or for every `ε` a single `Û`-orbit in `K` shadows `ι(ℤ ∖ 0)` to within `ε`.  It
has `o(X)` extra points per box and agrees with `U` off `O(log² X)` places, so every
finite-window, box-count, Haar or Delone statistic of `ι(ℤ)` is matched by one orbit.

**Proposition L (`amusicalRat_subgroup_one_mem`, rational form).**  The `Û`-invariant subgroups
are arithmetic.  A nonzero subgroup of `ℤ_(2) ⊂ ℚ` closed under `Ũ` contains `1`.  Paper proof:
`Ũ x = 3x/2` lowers `v₂` until `x` is a `2`-adic unit, then `4 Ũ y − 3 y = ±1`.  So invariant
subgroups see exactly `ℤ` (and its layers `(1/q) ℤ`, `gcd(q, 6) = 1`), where the question is
Klamkin (a) itself.  A proof must use the ring structure of `ℤ`, as Theorem W and the twin's
Frobenius do.

**Where statistics stop (Corollary S_K, research §25).**  A single orbit with the lattice's window
statistics has forward plus backward survival density at most
`p_f + p_b − p_f p_b ≈ 0.3972`, while `ℤ` measures `0.4470`.  Survival is the first statistic the
masquerade cannot fake: the §20 typicality wall.

Treadmill target: close every `sorry` here.
-/

namespace CollatzMoonshot.Amusical

/-- `U` extended to `ℤ_(2) ⊂ ℚ` (odd denominators): the class of `x = n/d` mod `4` is `n d mod 4`,
since `d⁻¹ ≡ d (mod 8)` for odd `d`.  Rationals with even denominator are left fixed. -/
def amusicalRat (x : ℚ) : ℚ :=
  if x.den % 2 = 0 then x
  else if (x.num * x.den) % 2 = 0 then 3 * x / 2
  else if (x.num * x.den) % 4 = 1 then (3 * x + 1) / 4
  else (3 * x - 1) / 4

/-- **Target.**  `amusicalRat` extends `U`. -/
theorem amusicalRat_intCast (n : ℤ) : amusicalRat n = amusical n := by
  sorry

/-- **Target (Proposition L, rational form).**  A nonzero subgroup of `ℤ_(2)` closed under the
extension of `U` contains `1`, hence `ℤ`.  Paper proof: pick `x ≠ 0`; while `v₂ x > 0`,
`Ũ x = 3x/2 ∈ Λ`; at a `2`-adic unit `y`, `4 Ũ y − 3 y = ±1`. -/
theorem amusicalRat_subgroup_one_mem (Λ : AddSubgroup ℚ) (hden : ∀ x ∈ Λ, x.den % 2 = 1)
    (hinv : ∀ x ∈ Λ, amusicalRat x ∈ Λ) (hne : Λ ≠ ⊥) : (1 : ℚ) ∈ Λ := by
  sorry

end CollatzMoonshot.Amusical
