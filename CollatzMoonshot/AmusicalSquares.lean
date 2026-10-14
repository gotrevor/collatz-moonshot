/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalSquares.Cylinder

/-!
# Square visits, prefix roots, and automatic invariants (the "newroutes-astra" lap)

The 2026-10-14 Codex ideation lap (research §44) proposed four new approaches to Klamkin (a); one
survives, and two side theorems came out of the others.

**`infinitelyManyOrbits_of_squareReturnConfinement` (SRC ⇒ (a)).**  If three square visits with
roots `≤ H`, in three distinct `E`-only blocks of one orbit segment, always lie within
`C log(2 + H)` steps, then every infinite orbit holds `O(log H)` of the `H` squares `≤ H²`, and
finitely many orbits cannot cover them.  `SquareReturnConfinement` is an open hypothesis `Prop`.

**`prefixRoot_eq_iff` (SQG1).**  The prefix affine maps `F_j(X) = A_j X + B_j` of a branch word
have roots `−B_j / A_j = −Σ_{h<j} e_h 2^{a_h} / 3^{h+1}`; two prefixes share a root iff every
branch between them is `E` (the last odd branch has the unique least `3`-adic valuation).  So
square visits in distinct `E`-blocks give distinct linear factors and a multiquadratic curve of
genus `1 + (k − 3) 2^{k−2}`.

**`amusicalInv_iterate_cylinder`, `invariant_kernel_three_pow` (AUT core).**  `V^k` maps the
cylinder `3^k n + r` affinely onto `2^a n + s` with `0 ≤ s < 2^a`, so the `3^m`-kernel of a
`U^m`-invariant colouring lies in its `2`-kernel.  With Cobham's theorem this makes a
binary-automatic `U^m`-invariant set finite or cofinite (research §44).
-/

namespace CollatzMoonshot.Amusical

/-- **Open hypothesis (SRC).**  Three square visits with roots `≤ H` in three distinct `E`-only
blocks of a repetition-free orbit segment lie within `C log(2 + H)` steps. -/
def SquareReturnConfinement : Prop :=
  ∃ C : ℝ, ∀ (x : ℤ) (s t H : ℕ), 0 < s → s < t →
    (∀ i j, i ≤ t → j ≤ t → amusical^[i] x = amusical^[j] x → i = j) →
    (∃ q ≤ H, x = (q : ℤ) ^ 2) → (∃ q ≤ H, amusical^[s] x = (q : ℤ) ^ 2) →
    (∃ q ≤ H, amusical^[t] x = (q : ℤ) ^ 2) →
    (∃ i < s, Odd (amusical^[i] x)) → (∃ i, s ≤ i ∧ i < t ∧ Odd (amusical^[i] x)) →
    (t : ℝ) ≤ C * Real.log (2 + H)

/-- **Target (SRC ⇒ (a)).** -/
theorem infinitelyManyOrbits_of_squareReturnConfinement (h : SquareReturnConfinement) :
    AmusicalInfinitelyManyOrbits := by
  sorry

/-- Bits consumed by the first `h` branches (`0` = `E` costs 1, `1` = `A` and `2` = `B` cost 2). -/
def wordWeight (w : List (Fin 3)) (h : ℕ) : ℕ :=
  ((w.take h).map fun b => if b = 0 then 1 else 2).sum

/-- The offset sign of a branch: `0` for `E`, `+1` for `A`, `−1` for `B`. -/
def branchSign (b : Fin 3) : ℤ := if b = 0 then 0 else if b = 1 then 1 else -1

/-- The root `−B_j / A_j` of the `j`-th prefix affine map of the word `w`. -/
def prefixRoot (w : List (Fin 3)) (j : ℕ) : ℚ :=
  -∑ h ∈ Finset.range j, (branchSign (w.getD h 0) : ℚ) * 2 ^ wordWeight w h / 3 ^ (h + 1)

/-- **Target (SQG1).**  Two prefixes share a root iff every branch between them is `E`. -/
theorem prefixRoot_eq_iff (w : List (Fin 3)) {i j : ℕ} (hij : i < j) (hj : j ≤ w.length) :
    prefixRoot w i = prefixRoot w j ↔ ∀ h, i ≤ h → h < j → w.getD h 0 = 0 := by
  sorry

/-- **Target (canonical cylinder).**  `V^k` is affine on each cylinder `3^k n + r`, landing on a
canonical class `2^a n + s`. -/
theorem amusicalInv_iterate_cylinder (k : ℕ) (r : ℤ) (hr0 : 0 ≤ r) (hr : r < 3 ^ k) :
    ∃ a : ℕ, ∃ s : ℤ, k ≤ a ∧ a ≤ 2 * k ∧ 0 ≤ s ∧ s < 2 ^ a ∧
      ∀ n : ℤ, amusicalInv^[k] (3 ^ k * n + r) = 2 ^ a * n + s :=
  amusicalInv_iterate_cylinder_aux k r hr0 hr

/-- **Target (AUT core).**  The `3^m`-kernel of a `U^m`-invariant colouring lies in its
`2`-kernel. -/
theorem invariant_kernel_three_pow {α : Type*} (f : ℤ → α) (m : ℕ)
    (hf : ∀ n, f (amusical^[m] n) = f n) (k : ℕ) (r : ℤ) (hr0 : 0 ≤ r) (hr : r < 3 ^ (m * k)) :
    ∃ a : ℕ, ∃ s : ℤ, 0 ≤ s ∧ s < 2 ^ a ∧ ∀ n : ℤ, f (3 ^ (m * k) * n + r) = f (2 ^ a * n + s) := by
  have hV : ∀ x, f (amusicalInv^[m] x) = f x := fun x => by
    rw [← hf, (Function.LeftInverse.iterate amusical_amusicalInv m) x]
  have hVk : ∀ x, f (amusicalInv^[m * k] x) = f x := by
    intro x
    rw [Function.iterate_mul]
    clear hr
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', hV, ih]
  obtain ⟨a, s, -, -, hs0, hsa, hcyl⟩ := amusicalInv_iterate_cylinder (m * k) r hr0 hr
  exact ⟨a, s, hs0, hsa, fun n => by rw [← hVk, hcyl]⟩

end CollatzMoonshot.Amusical
