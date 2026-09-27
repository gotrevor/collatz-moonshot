import CollatzMoonshot.Obstructions.ArithmeticLifts

/-!
# Anchored finite-cut transfer inequality

This file formalizes the elementary finite-cut transfer identity for the real-valued
predecessor transfer operator attached to `CollatzMoonshot.FrontB.tstep`, together with
the anchored lower bound it implies.

The key point is that no infinite norm, summability, or finite-support hypothesis is
needed: the identity holds for arbitrary signed coefficient functions `a : ℕ → ℝ`, and
nonnegativity enters only when isolating one boundary term.
-/

namespace CollatzMoonshot.Obstructions.ArithmeticLifts

open CollatzMoonshot.FrontB

/-- Real-valued transfer: sum of `a` over the positive `tstep`-predecessors of `v`. -/
def transferReal (a : ℕ → ℝ) (v : ℕ) : ℝ :=
  a (2 * v) + if v % 3 = 2 then a ((2 * v - 1) / 3) else 0

/-- All positive `tstep`-predecessors of the elements of `A`. -/
def predecessors (A : Finset ℕ) : Finset ℕ :=
  (A.image fun v => 2 * v) ∪
    ((A.filter fun v => v % 3 = 2).image fun v => (2 * v - 1) / 3)

/-- Incoming boundary of `A`: positive predecessors of `A` lying outside `A`. -/
def incoming (A : Finset ℕ) : Finset ℕ := predecessors A \ A

/-- Fiber lemma: a positive `u` whose `tstep`-image lands in `A` is a predecessor of `A`. -/
theorem mem_predecessors {A : Finset ℕ} {u : ℕ} (_hu : 0 < u) (h : tstep u ∈ A) :
    u ∈ predecessors A := by
  rcases Nat.even_or_odd u with he | ho
  · have h2 : u % 2 = 0 := Nat.even_iff.mp he
    have ht : tstep u = u / 2 := by simp [tstep, h2]
    refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨u / 2, ?_, ?_⟩)
    · rwa [← ht]
    · omega
  · have h2 : u % 2 = 1 := Nat.odd_iff.mp ho
    have ht : tstep u = (3 * u + 1) / 2 := by simp [tstep, h2]
    have hv2 : 2 * tstep u = 3 * u + 1 := by rw [ht]; omega
    refine Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨tstep u, Finset.mem_filter.mpr ⟨h, ?_⟩, ?_⟩)
    · omega
    · omega

/-- Every element of a positive forward-closed cut is itself a predecessor of the cut. -/
theorem subset_predecessors {A : Finset ℕ} (hpos : ∀ v ∈ A, 0 < v)
    (hclosed : ∀ v ∈ A, tstep v ∈ A) : A ⊆ predecessors A :=
  fun u hu => mem_predecessors (hpos u hu) (hclosed u hu)

/-- Members of `predecessors A` are positive when `A` is. -/
theorem pos_of_mem_predecessors {A : Finset ℕ} (hpos : ∀ v ∈ A, 0 < v) {u : ℕ}
    (hu : u ∈ predecessors A) : 0 < u := by
  rw [predecessors] at hu
  rcases Finset.mem_union.mp hu with h | h
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h
    have := hpos v hv; omega
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h
    have h3 := (Finset.mem_filter.mp hv).2
    have := hpos v (Finset.mem_filter.mp hv).1
    omega

/-- Reindexing: the total transfer over a positive cut is the total mass of `a` on the
predecessor set.  Valid for arbitrary signed `a`. -/
theorem sum_transferReal (A : Finset ℕ) (a : ℕ → ℝ) (hpos : ∀ v ∈ A, 0 < v) :
    (∑ v ∈ A, transferReal a v) = ∑ u ∈ predecessors A, a u := by
  have hinj1 : ∀ x ∈ A, ∀ y ∈ A, 2 * x = 2 * y → x = y := by
    intro x _ y _ h; omega
  have hinj2 : ∀ x ∈ A.filter (fun v => v % 3 = 2), ∀ y ∈ A.filter (fun v => v % 3 = 2),
      (2 * x - 1) / 3 = (2 * y - 1) / 3 → x = y := by
    intro x hx y hy h
    have hx3 := (Finset.mem_filter.mp hx).2
    have hy3 := (Finset.mem_filter.mp hy).2
    have hxp := hpos x (Finset.mem_filter.mp hx).1
    have hyp := hpos y (Finset.mem_filter.mp hy).1
    omega
  have hdisj : Disjoint (A.image fun v => 2 * v)
      ((A.filter fun v => v % 3 = 2).image fun v => (2 * v - 1) / 3) := by
    rw [Finset.disjoint_left]
    intro u hu1 hu2
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hu1
    obtain ⟨w, hw, hwe⟩ := Finset.mem_image.mp hu2
    have hw3 := (Finset.mem_filter.mp hw).2
    have hwp := hpos w (Finset.mem_filter.mp hw).1
    omega
  rw [predecessors, Finset.sum_union hdisj, Finset.sum_image hinj1,
    Finset.sum_image hinj2, Finset.sum_filter]
  simp only [transferReal]
  rw [Finset.sum_add_distrib]

theorem finiteCut_identity (A : Finset ℕ) (a : ℕ → ℝ)
    (hpos : ∀ v ∈ A, 0 < v)
    (hclosed : ∀ v ∈ A, tstep v ∈ A) :
    (∑ v ∈ A, (transferReal a v - a v)) =
      ∑ u ∈ incoming A, a u := by
  rw [Finset.sum_sub_distrib, sum_transferReal A a hpos, incoming,
    Finset.sum_sdiff_eq_sub (subset_predecessors hpos hclosed)]

theorem finiteCut_anchored_lower (A : Finset ℕ) (a : ℕ → ℝ)
    (n M : ℕ)
    (hpos : ∀ v ∈ A, 0 < v)
    (hclosed : ∀ v ∈ A, tstep v ∈ A)
    (hnpos : 0 < n) (hnout : n ∉ A) (henter : tstep n ∈ A)
    (ha : ∀ u, 0 < u → 0 ≤ a u)
    (hM : ∀ v ∈ A, v ≤ M) :
    (a n : ℝ) ≤ (M : ℝ) *
      ∑ v ∈ A, |transferReal a v - a v| / (v : ℝ) := by
  have hnin : n ∈ incoming A :=
    Finset.mem_sdiff.mpr ⟨mem_predecessors hnpos henter, hnout⟩
  have h1 : a n ≤ ∑ u ∈ incoming A, a u :=
    Finset.single_le_sum (f := a)
      (fun u hu => ha u (pos_of_mem_predecessors hpos (Finset.mem_sdiff.mp hu).1)) hnin
  rw [← finiteCut_identity A a hpos hclosed] at h1
  refine h1.trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun v hv => ?_
  have hv0 : (0 : ℝ) < v := by exact_mod_cast hpos v hv
  have hvM : (v : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM v hv
  calc transferReal a v - a v ≤ |transferReal a v - a v| := le_abs_self _
    _ = (v : ℝ) * (|transferReal a v - a v| / (v : ℝ)) := by
        field_simp
    _ ≤ (M : ℝ) * (|transferReal a v - a v| / (v : ℝ)) :=
        mul_le_mul_of_nonneg_right hvM (by positivity)

theorem finiteCut_unit_lower (A : Finset ℕ) (a : ℕ → ℝ)
    (n M : ℕ)
    (hpos : ∀ v ∈ A, 0 < v)
    (hclosed : ∀ v ∈ A, tstep v ∈ A)
    (hnpos : 0 < n) (hnout : n ∉ A) (henter : tstep n ∈ A)
    (ha : ∀ u, 0 < u → 0 ≤ a u)
    (hM : ∀ v ∈ A, v ≤ M) (hanchor : a n = 1) :
    (1 : ℝ) / (M : ℝ) ≤
      ∑ v ∈ A, |transferReal a v - a v| / (v : ℝ) := by
  have hMpos : 0 < M := lt_of_lt_of_le (hpos _ henter) (hM _ henter)
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMpos
  have h := finiteCut_anchored_lower A a n M hpos hclosed hnpos hnout henter ha hM
  rw [hanchor] at h
  rw [div_le_iff₀ hM0]
  linarith

/-! ### Statement controls

These are concrete sanity anchors for the frozen statements, not a substitute for the
quantified theorems above.  `tstep 2 = 1` and the odd predecessor `1` of `2` are inside
the cuts checked here. -/

example : tstep 2 = 1 := by decide
example : tstep 1 = 2 := by decide
example : predecessors {4, 2, 1} = {8, 4, 2, 1} := by decide
example : incoming {4, 2, 1} = {8} := by decide
example : predecessors {5, 8, 4, 2, 1} = {10, 16, 8, 4, 2, 5, 3, 1} := by decide
example : incoming {5, 8, 4, 2, 1} = {10, 16, 3} := by decide

/-- Even anchor `n = 8` over the cut `{4,2,1}` with bound `M = 4`. -/
example (a : ℕ → ℝ) (ha : ∀ u, 0 < u → 0 ≤ a u) (hanchor : a 8 = 1) :
    (1 : ℝ) / 4 ≤ ∑ v ∈ ({4, 2, 1} : Finset ℕ), |transferReal a v - a v| / (v : ℝ) :=
  finiteCut_unit_lower {4, 2, 1} a 8 4 (by decide) (by decide) (by norm_num)
    (by decide) (by decide) ha (by decide) hanchor

/-- Odd anchor `n = 3` over the cut `{5,8,4,2,1}` with bound `M = 8`. -/
example (a : ℕ → ℝ) (ha : ∀ u, 0 < u → 0 ≤ a u) (hanchor : a 3 = 1) :
    (1 : ℝ) / 8 ≤ ∑ v ∈ ({5, 8, 4, 2, 1} : Finset ℕ), |transferReal a v - a v| / (v : ℝ) :=
  finiteCut_unit_lower {5, 8, 4, 2, 1} a 3 8 (by decide) (by decide) (by norm_num)
    (by decide) (by decide) ha (by decide) hanchor

end CollatzMoonshot.Obstructions.ArithmeticLifts
