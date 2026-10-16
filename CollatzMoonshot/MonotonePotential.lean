/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.AmusicalTrap

/-!
# Lemma P: orbit classification from a monotone potential

Research note `wythoff-solvable`, §1.  Let `σ` be a permutation of `ℤ` preserving `ℕ⁺`, `S` a
set of "up" points, `Φ` a `σ`-invariant set of exceptional points (in the applications `Φ = {1}`,
a fixed point, or `Φ = ∅`), and `T` a return bound.  Assume, on `ℕ⁺`:

* **(H1)** every `z ∉ S ∪ Φ` steps down: `σ z < z`;
* **(H2)** every `s ∈ S ∖ Φ` returns to `S` within `T` steps, and its first return
  `R(s) = σ^τ(s) s` is larger: `s < R(s)`.

**Lemma P.**  Every orbit through a positive point off `Φ` meets `S`, is infinite, and tends to
`∞` in both time directions (`permOrbit_infinite`, `tendsto_pow`, `tendsto_pow_neg`).  Its minimum
is its unique point of `S` whose `T` predecessors all lie off `S` (`isOrbitMin_iff`); equivalently
the minima off `Φ` are `(S ∖ Φ) ∖ R(S ∖ Φ)` (`isOrbitMin_iff_returnMap`).  Since `R` is injective
and `R(s) > s`, for every `X`

  `#{orbit minima ≤ X off Φ} + #{s ∈ (S ∖ Φ) ∩ [1, X] : R(s) ≤ X} = #((S ∖ Φ) ∩ [1, X])`

(`minCountOff_add_returnCount`).  When `Φ` consists of fixed points, they are exactly the finite
orbits in `ℕ⁺` (`permOrbit_finite_iff`) and each is its own minimum, adding `#(Φ ∩ [1, X])`
(`minCount_add_returnCount`; Theorem F's `1 + A − B` is the case `Φ = {1}`).

Paper proof (research note §1).  An orbit off `Φ` that avoids `S` strictly decreases forever in
`ℕ⁺` by (H1), impossible.  Along an orbit the `S`-visits satisfy `s < R(s) < R²(s) < ⋯`, and the
points strictly between `s` and `R(s)` lie off `S ∪ Φ`, so by (H1) they decrease to `R(s)`: each
exceeds `R(s)`.  Read backward the `S`-visits decrease in `ℕ⁺`, so there is a first one `y*`, and
before it every point lies off `S ∪ Φ`, increasing read backward.  Hence every point other than
`y*` exceeds `y*`, and both tails go to `∞`.  An `S`-point `y ≠ y*` has a last earlier `S`-visit
`s'` with `R(s') = y` at distance `τ(s') ≤ T`, so the `T`-predecessor test detects it.
-/

namespace CollatzMoonshot.MonotonePotential

open CollatzMoonshot.AmusicalTrap (permOrbit InfinitelyManyInfiniteOrbits)
open Filter Topology

/-- The hypotheses of Lemma P for a permutation `σ` of `ℤ`, an up-set `S`, an invariant
exceptional set `Φ`, and a return bound `T`. -/
structure Hyp (σ : Equiv.Perm ℤ) (S Φ : Set ℤ) (T : ℕ) : Prop where
  /-- `σ` preserves `ℕ⁺` (hence also `ℤ≤0`). -/
  pos_iff : ∀ n, 0 < σ n ↔ 0 < n
  /-- `Φ` is `σ`-invariant. -/
  mem_fix_iff : ∀ z, σ z ∈ Φ ↔ z ∈ Φ
  /-- (H1) Off `S ∪ Φ`, positive points step down. -/
  desc : ∀ z, 0 < z → z ∉ S → z ∉ Φ → σ z < z
  /-- (H2) A positive `s ∈ S ∖ Φ` first returns to `S` after `τ ≤ T` steps, to a larger
  value. -/
  ret : ∀ s, s ∈ S → 0 < s → s ∉ Φ → ∃ τ : ℕ, 1 ≤ τ ∧ τ ≤ T ∧ (σ ^ τ) s ∈ S ∧
    s < (σ ^ τ) s ∧ ∀ i : ℕ, 1 ≤ i → i < τ → (σ ^ i) s ∉ S

/-- `x` is the minimum of its two-sided orbit. -/
def IsOrbitMin (σ : Equiv.Perm ℤ) (x : ℤ) : Prop :=
  ∀ y ∈ permOrbit σ x, x ≤ y

open Classical in
/-- First-return time of `s` to `S` (`0` if `s` never returns). -/
noncomputable def returnTime (σ : Equiv.Perm ℤ) (S : Set ℤ) (s : ℤ) : ℕ :=
  if h : ∃ τ : ℕ, 0 < τ ∧ (σ ^ τ) s ∈ S then Nat.find h else 0

/-- The first-return map `R(s) = σ^τ(s) s`. -/
noncomputable def returnMap (σ : Equiv.Perm ℤ) (S : Set ℤ) (s : ℤ) : ℤ :=
  (σ ^ returnTime σ S s) s

open Classical in
/-- The number of orbit minima in `[1, X]`. -/
noncomputable def minCount (σ : Equiv.Perm ℤ) (X : ℕ) : ℕ :=
  ((Finset.Icc (1 : ℤ) X).filter fun x => IsOrbitMin σ x).card

open Classical in
/-- The number of orbit minima in `[1, X]` off `Φ`. -/
noncomputable def minCountOff (σ : Equiv.Perm ℤ) (Φ : Set ℤ) (X : ℕ) : ℕ :=
  ((Finset.Icc (1 : ℤ) X).filter fun x => x ∉ Φ ∧ IsOrbitMin σ x).card

open Classical in
/-- `#(A ∩ [1, X])`. -/
noncomputable def setCount (A : Set ℤ) (X : ℕ) : ℕ :=
  ((Finset.Icc (1 : ℤ) X).filter fun x => x ∈ A).card

open Classical in
/-- `#{s ∈ (S ∖ Φ) ∩ [1, X] : R(s) ≤ X}`, which is `#(R(S ∖ Φ) ∩ [1, X])` since `R` is
injective with `R(s) > s`. -/
noncomputable def returnCount (σ : Equiv.Perm ℤ) (S Φ : Set ℤ) (X : ℕ) : ℕ :=
  ((Finset.Icc (1 : ℤ) X).filter fun s => s ∈ S ∧ s ∉ Φ ∧ returnMap σ S s ≤ X).card

section LemmaP

variable {σ : Equiv.Perm ℤ} {S Φ : Set ℤ} {T : ℕ}

/-- **(ratified).**  Orbits of positive points stay positive.  Paper proof: `zpow` induction with
`pos_iff` in both directions. -/
theorem permOrbit_subset_pos (h : Hyp σ S Φ T) {x : ℤ} (hx : 0 < x) :
    permOrbit σ x ⊆ {y | 0 < y} := by
  sorry

/-- **(ratified).**  Orbits of points off `Φ` avoid `Φ` (`Φ` is invariant). -/
theorem permOrbit_subset_compl (h : Hyp σ S Φ T) {x : ℤ} (hx : x ∉ Φ) :
    permOrbit σ x ⊆ Φᶜ := by
  sorry

/-- **(ratified).**  The first-return time is the `τ` of (H2): it lies in `[1, T]`, the return
lands in `S` above `s`, and the intermediate points are off `S`.  Paper proof: `Nat.find` is the
least positive `τ` with `σ^τ s ∈ S`; (H2)'s `τ` is such a `τ` with no smaller one. -/
theorem returnTime_spec (h : Hyp σ S Φ T) {s : ℤ} (hs : s ∈ S) (hs0 : 0 < s) (hsΦ : s ∉ Φ) :
    1 ≤ returnTime σ S s ∧ returnTime σ S s ≤ T ∧ returnMap σ S s ∈ S ∧
      s < returnMap σ S s ∧ ∀ i : ℕ, 1 ≤ i → i < returnTime σ S s → (σ ^ i) s ∉ S := by
  sorry

/-- **(ratified).**  `R` stays positive and off `Φ`. -/
theorem returnMap_pos_not_mem (h : Hyp σ S Φ T) {s : ℤ} (hs : s ∈ S) (hs0 : 0 < s)
    (hsΦ : s ∉ Φ) : 0 < returnMap σ S s ∧ returnMap σ S s ∉ Φ := by
  sorry

/-- **(ratified).**  `R` is injective on `(S ∖ Φ) ∩ ℕ⁺`.  Paper proof: if `R(s) = R(s') = y`
with `τ(s) < τ(s')`, then `s = σ^{τ(s') − τ(s)} s'` is an intermediate point of the first return
of `s'` (index in `[1, τ(s') − 1]`), yet `s ∈ S`: contradiction (`returnTime_spec`). -/
theorem returnMap_injOn (h : Hyp σ S Φ T) :
    Set.InjOn (returnMap σ S) {s | s ∈ S ∧ 0 < s ∧ s ∉ Φ} := by
  sorry

/-- **(ratified, Lemma P).**  An orbit through a positive point off `Φ` meets `S`. -/
theorem exists_mem_orbit_mem (h : Hyp σ S Φ T) {x : ℤ} (hx : 0 < x) (hxΦ : x ∉ Φ) :
    ∃ y ∈ permOrbit σ x, y ∈ S := by
  sorry

/-- **(ratified, Lemma P).**  Such an orbit is infinite. -/
theorem permOrbit_infinite (h : Hyp σ S Φ T) {x : ℤ} (hx : 0 < x) (hxΦ : x ∉ Φ) :
    (permOrbit σ x).Infinite := by
  sorry

/-- **(ratified).**  The orbit of a fixed point is a singleton (no `Hyp` needed). -/
theorem permOrbit_eq_singleton_of_fixed {x : ℤ} (hx : σ x = x) : permOrbit σ x = {x} := by
  sorry

/-- **(ratified, Lemma P (1)).**  When `Φ` consists of fixed points, the finite orbits through
`ℕ⁺` are exactly the points of `Φ`. -/
theorem permOrbit_finite_iff (h : Hyp σ S Φ T) (hfix : ∀ z ∈ Φ, σ z = z) {x : ℤ} (hx : 0 < x) :
    (permOrbit σ x).Finite ↔ x ∈ Φ := by
  sorry

/-- **(ratified, Lemma P (2), forward).**  The forward orbit tends to `∞`. -/
theorem tendsto_pow (h : Hyp σ S Φ T) {x : ℤ} (hx : 0 < x) (hxΦ : x ∉ Φ) :
    Tendsto (fun n : ℕ => (σ ^ n) x) atTop atTop := by
  sorry

/-- **(ratified, Lemma P (2), backward).**  The backward orbit tends to `∞`. -/
theorem tendsto_pow_neg (h : Hyp σ S Φ T) {x : ℤ} (hx : 0 < x) (hxΦ : x ∉ Φ) :
    Tendsto (fun n : ℕ => (σ ^ (-(n : ℤ))) x) atTop atTop := by
  sorry

/-- **(ratified, Lemma P (3)).**  The orbit has a minimum. -/
theorem exists_isOrbitMin (h : Hyp σ S Φ T) {x : ℤ} (hx : 0 < x) (hxΦ : x ∉ Φ) :
    ∃ y ∈ permOrbit σ x, IsOrbitMin σ y := by
  sorry

/-- **(ratified, Lemma P (3)).**  A positive `x ∉ Φ` is the minimum of its orbit iff `x ∈ S` and
its `T` predecessors are all off `S`. -/
theorem isOrbitMin_iff (h : Hyp σ S Φ T) {x : ℤ} (hx : 0 < x) (hxΦ : x ∉ Φ) :
    IsOrbitMin σ x ↔
      x ∈ S ∧ ∀ i : ℕ, 1 ≤ i → i ≤ T → (σ ^ (-(i : ℤ))) x ∉ S := by
  sorry

/-- **(ratified, Lemma P (4)).**  The minima off `Φ` are `(S ∖ Φ) ∖ R(S ∖ Φ)`. -/
theorem isOrbitMin_iff_returnMap (h : Hyp σ S Φ T) {x : ℤ} (hx : 0 < x) (hxΦ : x ∉ Φ) :
    IsOrbitMin σ x ↔
      x ∈ S ∧ ∀ s, s ∈ S → 0 < s → s ∉ Φ → returnMap σ S s ≠ x := by
  sorry

/-- **(ratified).**  A fixed point is the minimum of its orbit. -/
theorem isOrbitMin_of_fixed {x : ℤ} (hx : σ x = x) : IsOrbitMin σ x := by
  sorry

/-- **(ratified, Lemma P (4), exact count off `Φ`).**
`#{minima ≤ X off Φ} + #{s ∈ (S ∖ Φ) ∩ [1, X] : R(s) ≤ X} = #((S ∖ Φ) ∩ [1, X])`.
Paper proof: by `isOrbitMin_iff_returnMap` the minima in `[1, X]` off `Φ` are
`((S ∖ Φ) ∩ [1, X]) ∖ R(…)`; `R` maps `{s ∈ (S ∖ Φ) ∩ [1, X] : R(s) ≤ X}` injectively onto
`R(S ∖ Φ) ∩ [1, X]` (`R(s) ≤ X` forces `s < X`), a subset of `(S ∖ Φ) ∩ [1, X]`;
`Finset.card_sdiff`. -/
theorem minCountOff_add_returnCount (h : Hyp σ S Φ T) (X : ℕ) :
    minCountOff σ Φ X + returnCount σ S Φ X = setCount (S \ Φ) X := by
  sorry

/-- **(ratified, Lemma P (4), exact count).**  When `Φ` consists of fixed points,
`#{minima ≤ X} + #{s ∈ (S ∖ Φ) ∩ [1, X] : R(s) ≤ X} = #(Φ ∩ [1, X]) + #((S ∖ Φ) ∩ [1, X])`.
The `#Φ` term is Theorem F's `+1`. -/
theorem minCount_add_returnCount (h : Hyp σ S Φ T) (hfix : ∀ z ∈ Φ, σ z = z) (X : ℕ) :
    minCount σ X + returnCount σ S Φ X = setCount Φ X + setCount (S \ Φ) X := by
  sorry

/-- **(ratified).**  Infinitely many positive minima off `Φ` give infinitely many infinite
orbits.  Paper proof: distinct minima lie on distinct orbits (two minima of one orbit are equal by
`le_antisymm`), each infinite by `permOrbit_infinite`. -/
theorem infinitelyManyInfiniteOrbits_of_minima (h : Hyp σ S Φ T)
    (hinf : {x : ℤ | 0 < x ∧ x ∉ Φ ∧ IsOrbitMin σ x}.Infinite) :
    InfinitelyManyInfiniteOrbits σ := by
  sorry

end LemmaP

end CollatzMoonshot.MonotonePotential
