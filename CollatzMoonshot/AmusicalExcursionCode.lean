/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Amusical

/-!
# T1 integrality is the 2-adic code, read at the endpoints (Theorems R, LOC, DIV)

The 2026-10-14 "t1arith" agent (research §42) asked whether T1's integrality
`Δ_w ∣ 2^a d − C_w` (`Δ_w = 3^g − 2^a`) is an arithmetic invariant of whole excursions that could
separate `U` from Theorem G's order-only `σ`.  It is not.

**`defect_mod_delta` (Theorem R).**  On the class of a word, `2^a (U^g p − p) = Δ p + C_w`, so the
defect is `C_w 2^{−a} (mod Δ)`: the residue is the 2-adic code shifted by the word's periodic
rational, with no further digit structure.

**`eq_amusical_of_branch`, `eq_amusical_of_forall_branch` (Theorem LOC).**  Exactly one of `3x/2`,
`(3x ± 1)/4` is an integer, namely `U x`.  So "integrality along a whole excursion" is stepwise
agreement with `U`, and a map built from `U`'s three branches is `U`.

**`gcd_offset_eq_gcd_defect` (Theorem DIV).**  `gcd(C_w, Δ) = gcd(d, Δ)` (`Δ` is odd).

**`amusical_iterate_ge_iff_offset`.**  `U^g p ≥ p` iff `Δ p + C_w ≥ 0`.
-/

namespace CollatzMoonshot.Amusical

/-- **Target (LOC.1, branch uniqueness).** -/
theorem eq_amusical_of_branch {x y : ℤ}
    (h : 2 * y = 3 * x ∨ 4 * y = 3 * x + 1 ∨ 4 * y = 3 * x - 1) : y = amusical x := by
  sorry

/-- **Target (LOC.1).**  A self-map of `ℤ` built from `U`'s branches is `U`. -/
theorem eq_amusical_of_forall_branch (π : ℤ → ℤ)
    (h : ∀ x, 2 * π x = 3 * x ∨ 4 * π x = 3 * x + 1 ∨ 4 * π x = 3 * x - 1) : π = amusical := by
  sorry

/-- **Target (Theorem R).**  The defect is the residue `C · 2^{−a}` modulo `Δ = 3^g − 2^a`. -/
theorem defect_mod_delta {g a : ℕ} {p C : ℤ}
    (h : 2 ^ a * amusical^[g] p = 3 ^ g * p + C) :
    2 ^ a * (amusical^[g] p - p) ≡ C [ZMOD (3 ^ g - 2 ^ a)] := by
  sorry

/-- **Target (Theorem DIV).**  The offset and the defect have the same gcd with `Δ`. -/
theorem gcd_offset_eq_gcd_defect {g a : ℕ} {p C : ℤ} (ha : 1 ≤ a)
    (h : 2 ^ a * amusical^[g] p = 3 ^ g * p + C) :
    Int.gcd C (3 ^ g - 2 ^ a) = Int.gcd (amusical^[g] p - p) (3 ^ g - 2 ^ a) := by
  sorry

/-- **Target.**  `U^g p ≥ p` iff `Δ p + C ≥ 0`. -/
theorem amusical_iterate_ge_iff_offset {g a : ℕ} {p C : ℤ}
    (h : 2 ^ a * amusical^[g] p = 3 ^ g * p + C) :
    p ≤ amusical^[g] p ↔ 0 ≤ (3 ^ g - 2 ^ a) * p + C := by
  sorry

end CollatzMoonshot.Amusical
