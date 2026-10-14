/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Amusical

/-!
# One orbit realizes every residue-graph path of `U`

The step lemma behind `amusical_topologicallyTransitive`.  Fix a modulus `M` and a class `r`.  Say
`(n, c)` is *full* when every `y ≡ Uⁿ c (mod 3ⁿ M)` is `Uⁿ x` for some `x ≡ r (mod M)`.  Since `U`
is affine on classes mod `4` with slopes `3/2`, `3/4` and `U⁻¹` is affine on classes mod `3` with
slopes `2/3`, `4/3`:

* forward, any `z ≡ Uⁿ c (mod M)` can be replaced by `y₀ ≡ z (mod 4M)` lying in the full class
  (CRT: `4` is a unit mod `3ⁿ`), and then `U y₀ ≡ U z (mod M)`;
* backward, `U⁻¹` maps the class `U y₀ + 3ⁿ⁺¹ M ℤ` into `y₀ + 3ⁿ M ℤ`, so `(n + 1, U⁻ⁿ y₀)` is full.

So fullness propagates along every edge of the residue graph mod `M`
(`amusical_full_step`), and the set of classes reached by full pairs is forward closed.
-/

namespace CollatzMoonshot.Amusical

theorem amusical_add_four_mul_cases (z P : ℤ) :
    amusical (z + 4 * P) = amusical z + 6 * P ∨ amusical (z + 4 * P) = amusical z + 3 * P := by
  unfold amusical
  split_ifs <;> omega

theorem amusicalInv_add_three_mul_cases (w Q : ℤ) :
    amusicalInv (w + 3 * Q) = amusicalInv w + 2 * Q ∨
      amusicalInv (w + 3 * Q) = amusicalInv w + 4 * Q := by
  unfold amusicalInv
  split_ifs <;> omega

/-- `(n, c)` is full for the class `r` mod `M`: the class `Uⁿ c + 3ⁿ M ℤ` lies in the image of
`r + M ℤ` under `Uⁿ`. -/
def AmusicalFull (M r : ℤ) (n : ℕ) (c : ℤ) : Prop :=
  ∀ y, y ≡ amusical^[n] c [ZMOD 3 ^ n * M] → ∃ x, x ≡ r [ZMOD M] ∧ amusical^[n] x = y

theorem amusicalFull_zero (M r : ℤ) : AmusicalFull M r 0 r := by
  intro y hy
  refine ⟨y, ?_, rfl⟩
  simpa using hy

/-- **Step lemma.**  Fullness propagates along any residue-graph edge `Uⁿ c ≡ z ↦ U z`. -/
theorem amusical_full_step {M r : ℤ} {n : ℕ} {c : ℤ} (hP : AmusicalFull M r n c)
    {z : ℤ} (hz : z ≡ amusical^[n] c [ZMOD M]) :
    ∃ c', AmusicalFull M r (n + 1) c' ∧ amusical^[n + 1] c' ≡ amusical z [ZMOD M] := by
  obtain ⟨d, hd⟩ := Int.modEq_iff_dvd.mp hz
  have hcop : IsCoprime (4 : ℤ) (3 ^ n) :=
    IsCoprime.pow_right (⟨1, -1, by norm_num⟩ : IsCoprime (4 : ℤ) 3)
  obtain ⟨u, v, huv⟩ := hcop
  set y₀ := z + 4 * (M * (u * d)) with hy₀def
  have hy₀ : y₀ ≡ amusical^[n] c [ZMOD 3 ^ n * M] := by
    apply Int.modEq_iff_dvd.mpr
    exact ⟨d * v, by rw [hy₀def]; linear_combination hd - (M * d) * huv⟩
  obtain ⟨x₀, -, hx₀⟩ := hP y₀ hy₀
  refine ⟨x₀, ?_, ?_⟩
  · intro y' hy'
    rw [Function.iterate_succ_apply', hx₀] at hy'
    obtain ⟨e, he⟩ := Int.modEq_iff_dvd.mp hy'.symm
    have hy'eq : y' = amusical y₀ + 3 * (3 ^ n * M * e) := by
      rw [pow_succ] at he
      linear_combination he
    have hpre : amusicalInv y' ≡ amusical^[n] c [ZMOD 3 ^ n * M] := by
      refine Int.ModEq.trans ?_ hy₀
      apply Int.modEq_iff_dvd.mpr
      rcases amusicalInv_add_three_mul_cases (amusical y₀) (3 ^ n * M * e) with h | h <;>
        rw [hy'eq, h, amusicalInv_amusical]
      · exact ⟨-(2 * e), by ring⟩
      · exact ⟨-(4 * e), by ring⟩
    obtain ⟨x, hxr, hx⟩ := hP _ hpre
    refine ⟨x, hxr, ?_⟩
    rw [Function.iterate_succ_apply', hx, amusical_amusicalInv]
  · rw [Function.iterate_succ_apply', hx₀]
    apply Int.modEq_iff_dvd.mpr
    rcases amusical_add_four_mul_cases z (M * (u * d)) with h | h <;> rw [hy₀def, h]
    · exact ⟨-(6 * (u * d)), by ring⟩
    · exact ⟨-(3 * (u * d)), by ring⟩

end CollatzMoonshot.Amusical
