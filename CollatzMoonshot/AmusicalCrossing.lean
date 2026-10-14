/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalTwin
import CollatzMoonshot.AmusicalReturns

/-!
# Crossing the cut at `0`: an archimedean certificate of infinite orbits

The 2026-10-14 "bridge" agent observed that Kohl's determinant of a class-wise order-preserving
RCWA permutation is the net number of integers crossing `0`:
`det σ = #{x < 0 ≤ σ x} − #{x ≥ 0 > σ x}`.  An orbit with an up-crossing and no down-crossing
cannot close, so `σ` has at least `|det σ|` infinite orbits.  The certificate reads finite residue
data, and it is disjoint from reversal, Frobenius, and Theorem W.  It is silent on `U`, whose
determinant is `0` (`U` is odd).

**`not_periodic_of_upCrossing`.**  If `σ` maps `ℕ` into `ℕ`, a point `x < 0` with `σ x ≥ 0` is not
periodic.

**`twinW_zero_not_periodic`.**  So the statistical twin `twinW` of `AmusicalTwin` (U's cylinder
laws, window densities and full-shift coding; a 3-cycle that `U` lacks) has an infinite orbit
through `0`: `0, 3, 2, 6, 12, 21, 16, 27, …`.  Its only crossing is `−2 ↦ 0`.

Paper proofs: agent report `bridge.md` §2–§3, summarized in
`RESEARCH-2026-10-13-amusical-single-chain.md` §24.  I re-checked the determinant formula against
brute-force flux on nine twins (`scripts/amusical/flux_ren.py`).  Teeth: `U` gives `0`, and a count
window that misses `−2` misses the crossing.
-/

namespace CollatzMoonshot.Amusical

/-- **Proved.**  A map sending `ℕ` into `ℕ` has no periodic point below `0` that crosses into `ℕ`:
the forward orbit from `σ x ≥ 0` never returns below `0`. -/
theorem not_periodic_of_upCrossing (σ : ℤ → ℤ) (hσ : ∀ y, 0 ≤ y → 0 ≤ σ y) {x : ℤ} (hx : x < 0)
    (hup : 0 ≤ σ x) : x ∉ Function.periodicPts σ := by
  rintro ⟨n, hn, hper⟩
  have hge : ∀ k, 0 ≤ σ^[k + 1] x := by
    intro k
    induction k with
    | zero => simpa using hup
    | succ k ih => rw [Function.iterate_succ_apply']; exact hσ _ ih
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have := hge k
  rw [hper.eq] at this
  omega

/-- `twinW` sends `ℕ` into `ℕ ∖ {0}`: every offset is non-negative, and `0` is hit only by `−2`. -/
theorem twinW_pos {y : ℤ} (hy : 0 ≤ y) : 1 ≤ twinW y := by
  unfold twinW
  split_ifs <;> omega

/-- The up-crossing `−2 ↦ 0`. -/
theorem twinW_neg_two : twinW (-2) = 0 := by
  unfold twinW; norm_num

/-- **Proved.**  The orbit of `0` under the statistical twin `twinW` is infinite: its forward
orbit stays in `ℕ ∖ {0}`.  This is `not_periodic_of_upCrossing` at the crossing `−2 ↦ 0`. -/
theorem twinW_zero_not_periodic : (0 : ℤ) ∉ Function.periodicPts twinW := by
  rintro ⟨n, hn, hper⟩
  have hge : ∀ k, 1 ≤ twinW^[k + 1] 0 := by
    intro k
    induction k with
    | zero => exact twinW_pos le_rfl
    | succ k ih => rw [Function.iterate_succ_apply']; exact twinW_pos (by omega)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have := hge k
  rw [hper.eq] at this
  omega

/-- **Proved.**  The orbit of `−2` is infinite too (it is the orbit of `0`). -/
theorem twinW_neg_two_not_periodic : (-2 : ℤ) ∉ Function.periodicPts twinW :=
  not_periodic_of_upCrossing twinW (fun _ hy => by have := twinW_pos hy; omega)
    (by norm_num) (by rw [twinW_neg_two])

/-- **Proved (why the certificate is silent on `U`).**  `U` preserves sign, so it has no crossing
at all and its determinant is `0`: every orbit has both ends on one side of `0`. -/
theorem amusical_no_crossing (x : ℤ) : 0 ≤ amusical x ↔ 0 ≤ x := by
  refine ⟨fun h => ?_, amusical_nonneg⟩
  by_contra hx
  have := amusical_pos (show 0 < -x by omega)
  rw [amusical_neg] at this
  omega

end CollatzMoonshot.Amusical
