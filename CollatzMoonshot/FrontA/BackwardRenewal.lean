/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.FrontA.BackwardHeightTransfer

/-!
# Telescoping weights for the barriered backward renewal

The rational certificate in `BackwardHeightTransfer` is a finite way to prove
local expansion.  Those rational edge weights do not themselves telescope
along a path.  The correct renewal weight is

`sqrt (parent / child)`.

It telescopes exactly, and the Collatz odd-block identity proves that every
rational certificate weight is strictly smaller.  This file upgrades the two
actual-child local expansion theorems to that exact weight.  It also records
the constant-factor conversion from odd endpoints to the full forward block.

This is the nonstandard analytic bridge needed before applying a generic
stopping-line/tree renewal theorem.  No global growth conclusion is claimed in
this file.
-/

namespace CollatzMoonshot.FrontA

/-- The real version of the rational edge underweight used by the finite
certificate. -/
noncomputable def netHalfRationalWeight (j : ℕ) : ℝ :=
  (5 / 3 : ℝ) * (7 / 10 : ℝ) ^ j

/-- The exact exponent-`1/2` weight of an edge between odd endpoints. -/
noncomputable def netHalfEdgeWeight (x y : ℕ) : ℝ :=
  Real.sqrt ((x : ℝ) / (y : ℝ))

theorem netHalfRationalWeight_pos (j : ℕ) : 0 < netHalfRationalWeight j := by
  unfold netHalfRationalWeight
  positivity

theorem netHalfEdgeWeight_nonneg (x y : ℕ) : 0 ≤ netHalfEdgeWeight x y := by
  exact Real.sqrt_nonneg _

/-- The elementary rational comparisons imply the required squared-weight
bound for every positive exponent. -/
theorem netHalfRationalWeight_sq_lt (j : ℕ) (hj : 1 ≤ j) :
    (netHalfRationalWeight j) ^ 2 < 3 / (2 : ℝ) ^ j := by
  have hbase :
      ((7 / 10 : ℝ) ^ 2) ^ j < ((1 / 2 : ℝ)) ^ j :=
    pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
  calc
    (netHalfRationalWeight j) ^ 2 =
        (5 / 3 : ℝ) ^ 2 * ((7 / 10 : ℝ) ^ 2) ^ j := by
          simp only [netHalfRationalWeight, mul_pow, ← pow_mul]
          congr 2
          omega
    _ < 3 * ((7 / 10 : ℝ) ^ 2) ^ j := by
      apply mul_lt_mul_of_pos_right (by norm_num)
      positivity
    _ < 3 * ((1 / 2 : ℝ) ^ j) :=
      mul_lt_mul_of_pos_left hbase (by norm_num)
    _ = 3 / (2 : ℝ) ^ j := by
      rw [one_div_pow]
      ring

/-- On every actual positive odd block, the rational certificate weight is
strictly below the exact telescoping endpoint weight. -/
theorem netHalfRationalWeight_lt_edgeWeight {x y j : ℕ}
    (hy : 1 ≤ y) (hj : 1 ≤ j) (h : 3 * y + 1 = 2 ^ j * x) :
    netHalfRationalWeight j < netHalfEdgeWeight x y := by
  have hb : (3 : ℝ) * y + 1 = (2 : ℝ) ^ j * x := by
    exact_mod_cast h
  have hratio : (3 : ℝ) / (2 : ℝ) ^ j < (x : ℝ) / (y : ℝ) := by
    rw [div_lt_div_iff₀ (pow_pos (by norm_num) _) (by exact_mod_cast hy)]
    nlinarith
  unfold netHalfEdgeWeight
  exact Real.lt_sqrt_of_sq_lt
    ((netHalfRationalWeight_sq_lt j hj).trans hratio)

/-- Exact telescoping along two positive endpoint edges. -/
theorem netHalfEdgeWeight_mul {x y z : ℕ} (hy : 1 ≤ y) (hz : 1 ≤ z) :
    netHalfEdgeWeight x y * netHalfEdgeWeight y z =
      netHalfEdgeWeight x z := by
  unfold netHalfEdgeWeight
  rw [← Real.sqrt_mul (by positivity)]
  congr 1
  field_simp

/-! ## Macro ancestry and the cycle alternative -/

/-- Positive-time forward reachability. -/
def ReachesValuePos (n d : ℕ) : Prop :=
  ∃ k, 0 < k ∧ step^[k] n = d

theorem ReachesValuePos.trans {a b c : ℕ}
    (hab : ReachesValuePos a b) (hbc : ReachesValuePos b c) :
    ReachesValuePos a c := by
  obtain ⟨k, hk, hab⟩ := hab
  obtain ⟨l, hl, hbc⟩ := hbc
  refine ⟨l + k, by omega, ?_⟩
  rw [Function.iterate_add_apply, hab, hbc]

@[simp] theorem reachesValuePos_self_iff_onCycle {x : ℕ} :
    ReachesValuePos x x ↔ OnCycle x := by
  rfl

/-- A reusable odd inverse macro-edge, allowing both growing edges and the
safe shrinking `j=1` edge. -/
def ReusableOddBlockChild (x y : ℕ) : Prop :=
  ∃ j, 1 ≤ j ∧ y % 2 = 1 ∧ ¬3 ∣ y ∧
    3 * y + 1 = 2 ^ j * x

theorem GrowingUnitOddBlockChild.toReusable {x y j : ℕ}
    (h : GrowingUnitOddBlockChild x y j) : ReusableOddBlockChild x y := by
  obtain ⟨hj, hyodd, hy3, _, hblock⟩ := h
  exact ⟨j, by omega, hyodd, hy3, hblock⟩

theorem UnitOddBlockChildAtOne.toReusable {x y : ℕ}
    (h : UnitOddBlockChildAtOne x y) : ReusableOddBlockChild x y := by
  obtain ⟨hyodd, hy3, _, hblock⟩ := h
  exact ⟨1, by norm_num, hyodd, hy3, by simpa using hblock⟩

/-- Every reusable macro-child reaches its parent in positive forward time. -/
theorem ReusableOddBlockChild.reachesValuePos {x y : ℕ}
    (h : ReusableOddBlockChild x y) : ReachesValuePos y x := by
  obtain ⟨j, hj, hyodd, _, hblock⟩ := h
  have hstep : step y = 2 ^ j * x := by
    unfold step
    simp [hyodd, hblock]
  refine ⟨j + 1, by omega, ?_⟩
  rw [Function.iterate_succ_apply, hstep, iterate_pow_two_mul]

/-- Reusable children of distinct odd parents cannot merge. -/
theorem reusableOddBlockChild_parent_eq {x x' y : ℕ}
    (hx : x % 2 = 1) (hx' : x' % 2 = 1)
    (h : ReusableOddBlockChild x y) (h' : ReusableOddBlockChild x' y) :
    x = x' := by
  obtain ⟨j, _, _, _, hblock⟩ := h
  obtain ⟨j', _, _, _, hblock'⟩ := h'
  exact oddBlock_parent_eq_of_odd hx hx' hblock hblock'

/-- If a new macro-child is already an ancestor of its parent, the two positive
macro paths compose to an explicit Collatz cycle. -/
theorem onCycle_of_reusable_child_of_parent_reaches_child {x y : ℕ}
    (hchild : ReusableOddBlockChild x y) (hback : ReachesValuePos x y) :
    OnCycle y := by
  rw [← reachesValuePos_self_iff_onCycle]
  exact hchild.reachesValuePos.trans hback

/-! ## Generic finite-frontier replacement -/

/-- Replacing every node of a nonempty finite frontier by pairwise-disjoint
children increases root-weighted mass whenever the local mass expands and the
edge weights telescope.  This is the finite algebraic core of the eventual
stopping-line argument. -/
theorem weighted_biUnion_expands
    {α : Type*} [DecidableEq α] (S : Finset α) (hS : S.Nonempty)
    (children : α → Finset α) (rootWeight potential : α → ℝ)
    (edgeWeight : α → α → ℝ)
    (hdisj : ∀ a ∈ S, ∀ b ∈ S, a ≠ b →
      Disjoint (children a) (children b))
    (hroot : ∀ x ∈ S, 0 < rootWeight x)
    (hlocal : ∀ x ∈ S, potential x <
      ∑ y ∈ children x, edgeWeight x y * potential y)
    (htelescope : ∀ x ∈ S, ∀ y ∈ children x,
      rootWeight x * edgeWeight x y = rootWeight y) :
    (∑ x ∈ S, rootWeight x * potential x) <
      ∑ y ∈ S.biUnion children, rootWeight y * potential y := by
  have hone (x : α) (hx : x ∈ S) :
      rootWeight x * potential x <
        ∑ y ∈ children x, rootWeight y * potential y := by
    calc
      rootWeight x * potential x <
          rootWeight x *
            (∑ y ∈ children x, edgeWeight x y * potential y) :=
        mul_lt_mul_of_pos_left (hlocal x hx) (hroot x hx)
      _ = ∑ y ∈ children x,
          rootWeight x * (edgeWeight x y * potential y) := by
            rw [Finset.mul_sum]
      _ = ∑ y ∈ children x, rootWeight y * potential y := by
            apply Finset.sum_congr rfl
            intro y hy
            rw [← mul_assoc, htelescope x hx y hy]
  calc
    (∑ x ∈ S, rootWeight x * potential x) <
        ∑ x ∈ S, ∑ y ∈ children x, rootWeight y * potential y := by
          apply Finset.sum_lt_sum_of_nonempty hS
          intro x hx
          exact hone x hx
    _ = ∑ y ∈ S.biUnion children, rootWeight y * potential y := by
      rw [Finset.sum_biUnion hdisj]

/-! ## The finite stopping-line target -/

/-- A finite first-exit frontier with enough telescoping mass.  The state/value
injectivity clause ensures its cardinality counts distinct natural endpoints.
The existence of such a frontier, or alternatively an orbit repeat, is the
remaining recursive renewal theorem. -/
def NetHalfStoppingFrontier (d H : ℕ) (S : Finset (Bool × ℕ)) : Prop :=
  (∀ a ∈ S, ∀ b ∈ S, a.2 = b.2 → a = b) ∧
  (netHalfStatePotential false d : ℝ) <
    ∑ s ∈ S, netHalfEdgeWeight d s.2 * netHalfStatePotential s.1 s.2 ∧
  ∀ s ∈ S, H < s.2 ∧ s.2 < 2 ^ 23 * H ∧
    ReachesInBand d (2 ^ 25 * H) s.2

/-- The remaining scoped theorem: every odd reusable root either exposes a
positive cycle above its floor or has a finite first-exit frontier carrying the
certified square-root mass.  This is a definition until the recursive
stopping-line bookkeeping is completed. -/
def NetHalfRepeatOrStoppingGrowth : Prop :=
  ∀ d H : ℕ, 2 ≤ d → d % 2 = 1 → ¬3 ∣ d → d ≤ H →
    (∃ n, d ≤ n ∧ OnCycle n) ∨
      ∃ S : Finset (Bool × ℕ), NetHalfStoppingFrontier d H S

/-- Once the cycle front is available, the repeat alternative in
`NetHalfRepeatOrStoppingGrowth` is impossible for an odd root `d ≥ 2`. -/
theorem stoppingFrontier_of_repeatOrStoppingGrowth
    (hgrowth : NetHalfRepeatOrStoppingGrowth) (hnc : NoNontrivialCycle)
    {d H : ℕ} (hd : 2 ≤ d) (hdodd : d % 2 = 1) (hd3 : ¬3 ∣ d) (hdH : d ≤ H) :
    ∃ S : Finset (Bool × ℕ), NetHalfStoppingFrontier d H S := by
  rcases hgrowth d H hd hdodd hd3 hdH with hcycle | hfrontier
  · obtain ⟨n, hdn, hncycle⟩ := hcycle
    have hn : 1 ≤ n := by omega
    rcases hnc n hn hncycle with rfl | rfl | rfl <;> omega
  · exact hfrontier

/-- The mass clause of a stopping frontier forces square-root-many distinct
endpoints.  This deliberately leaves the bound in multiplication form, avoiding
irrelevant square-root division algebra while displaying the exponent exactly. -/
theorem NetHalfStoppingFrontier.card_bound {d H : ℕ} {S : Finset (Bool × ℕ)}
    (hd : 1 ≤ d) (hH : 1 ≤ H) (h : NetHalfStoppingFrontier d H S) :
    (netHalfStatePotential false d : ℝ) <
      (S.card : ℝ) * (200 * Real.sqrt ((d : ℝ) / (H : ℝ))) := by
  obtain ⟨_, hmass, hleaves⟩ := h
  have hterm (s : Bool × ℕ) (hs : s ∈ S) :
      netHalfEdgeWeight d s.2 * netHalfStatePotential s.1 s.2 ≤
        200 * Real.sqrt ((d : ℝ) / (H : ℝ)) := by
    have hHy : H ≤ s.2 := (hleaves s hs).1.le
    have hratio : (d : ℝ) / (s.2 : ℝ) ≤ (d : ℝ) / (H : ℝ) := by
      rw [div_le_div_iff_of_pos_left (by exact_mod_cast hd)
        (by exact_mod_cast (hH.trans hHy)) (by exact_mod_cast hH)]
      exact_mod_cast hHy
    have hedge : netHalfEdgeWeight d s.2 ≤
        Real.sqrt ((d : ℝ) / (H : ℝ)) :=
      Real.sqrt_le_sqrt hratio
    have hpotential : (netHalfStatePotential s.1 s.2 : ℝ) ≤ 200 := by
      exact_mod_cast netHalfStatePotential_le_twoHundred s.1 s.2
    calc
      netHalfEdgeWeight d s.2 * netHalfStatePotential s.1 s.2 ≤
          Real.sqrt ((d : ℝ) / (H : ℝ)) *
            netHalfStatePotential s.1 s.2 :=
        mul_le_mul_of_nonneg_right hedge (by positivity)
      _ ≤ Real.sqrt ((d : ℝ) / (H : ℝ)) * 200 :=
        mul_le_mul_of_nonneg_left hpotential (Real.sqrt_nonneg _)
      _ = 200 * Real.sqrt ((d : ℝ) / (H : ℝ)) := by ring
  calc
    (netHalfStatePotential false d : ℝ) <
        ∑ s ∈ S, netHalfEdgeWeight d s.2 *
          netHalfStatePotential s.1 s.2 := hmass
    _ ≤ S.card • (200 * Real.sqrt ((d : ℝ) / (H : ℝ))) :=
      Finset.sum_le_card_nsmul S _ _ hterm
    _ = (S.card : ℝ) * (200 * Real.sqrt ((d : ℝ) / (H : ℝ))) := by
      simp [nsmul_eq_mul]

private theorem rationalGrowingExpansion_real {d x : ℕ} (high : Bool)
    (hx : 2 ≤ x) (h3 : ¬3 ∣ x) (hstate : InHeightState d high x)
    (hn : netHalfHasShrinkingChild high x = false) :
    ∃ ys : Fin 7 → ℕ, Function.Injective ys ∧
      (∀ i, GrowingUnitOddBlockChild x (ys i) (sevenCostsAt x i) ∧
        InHeightState d (nextGrowingHeightState high (sevenCostsAt x i)) (ys i)) ∧
      (netHalfStatePotential high x : ℝ) <
        (5 / 3 : ℝ) *
          ∑ i : Fin 7, (7 / 10 : ℝ) ^ sevenCostsAt x i *
            netHalfStatePotential
              (nextGrowingHeightState high (sevenCostsAt x i)) (ys i) := by
  obtain ⟨ys, hys, hchildren, hrat⟩ :=
    exists_netHalfGrowingExpansion high hx h3 hstate hn
  have hc :
      (((netHalfStatePotential high x : ℚ) : ℝ)) <
        (((5 / 3 : ℚ) *
          ∑ i : Fin 7, (7 / 10 : ℚ) ^ sevenCostsAt x i *
            netHalfStatePotential
              (nextGrowingHeightState high (sevenCostsAt x i)) (ys i) : ℚ) : ℝ) :=
    Rat.cast_lt.mpr hrat
  refine ⟨ys, hys, hchildren, ?_⟩
  norm_num at hc ⊢
  exact hc

/-- With no safe shrinking edge, the seven actual children strictly expand
the potential under the exact telescoping weights. -/
theorem exists_netHalfGrowingEdgeExpansion {d x : ℕ} (high : Bool)
    (hx : 2 ≤ x) (h3 : ¬3 ∣ x) (hstate : InHeightState d high x)
    (hn : netHalfHasShrinkingChild high x = false) :
    ∃ ys : Fin 7 → ℕ, Function.Injective ys ∧
      (∀ i, GrowingUnitOddBlockChild x (ys i) (sevenCostsAt x i) ∧
        InHeightState d (nextGrowingHeightState high (sevenCostsAt x i)) (ys i)) ∧
      (netHalfStatePotential high x : ℝ) <
        ∑ i : Fin 7, netHalfEdgeWeight x (ys i) *
          netHalfStatePotential
            (nextGrowingHeightState high (sevenCostsAt x i)) (ys i) := by
  obtain ⟨ys, hys, hchildren, hrat⟩ :=
    rationalGrowingExpansion_real high hx h3 hstate hn
  rw [Finset.mul_sum] at hrat
  have hsum :
      (∑ i : Fin 7, (5 / 3 : ℝ) *
          ((7 / 10 : ℝ) ^ sevenCostsAt x i *
            netHalfStatePotential
              (nextGrowingHeightState high (sevenCostsAt x i)) (ys i))) <
        ∑ i : Fin 7, netHalfEdgeWeight x (ys i) *
          netHalfStatePotential
            (nextGrowingHeightState high (sevenCostsAt x i)) (ys i) := by
    apply Finset.sum_lt_sum_of_nonempty
    · exact Finset.univ_nonempty
    · intro i _
      rw [← mul_assoc]
      apply mul_lt_mul_of_pos_right
      · simpa [netHalfRationalWeight] using
          netHalfRationalWeight_lt_edgeWeight
            (by have := (hchildren i).1.2.1; omega)
            (by have := (hchildren i).1.1; omega)
            (hchildren i).1.2.2.2.2
      · exact_mod_cast netHalfStatePotential_pos
          (nextGrowingHeightState high (sevenCostsAt x i))
          (hchildren i).1.2.2.1
  exact ⟨ys, hys, hchildren, hrat.trans hsum⟩

private theorem rationalShrinkingExpansion_real {d x : ℕ}
    (hx : 2 ≤ x) (h3 : ¬3 ∣ x) (hstate : InHeightState d true x)
    (hrem : x % 9 = 2 ∨ x % 9 = 8) :
    ∃ (ys : Fin 7 → ℕ) (z : ℕ), Function.Injective ys ∧
      (∀ i, GrowingUnitOddBlockChild x (ys i) (sevenCostsAt x i) ∧
        InHeightState d (nextGrowingHeightState true (sevenCostsAt x i)) (ys i)) ∧
      UnitOddBlockChildAtOne x z ∧ InHeightState d false z ∧
      (∀ i, z ≠ ys i) ∧
      (netHalfStatePotential true x : ℝ) <
        (5 / 3 : ℝ) *
          ((∑ i : Fin 7, (7 / 10 : ℝ) ^ sevenCostsAt x i *
            netHalfStatePotential
              (nextGrowingHeightState true (sevenCostsAt x i)) (ys i)) +
            (7 / 10 : ℝ) * netHalfStatePotential false z) := by
  obtain ⟨ys, z, hys, hchildren, hz, hzstate, hdisj, hrat⟩ :=
    exists_netHalfShrinkingExpansion hx h3 hstate hrem
  have hc :
      (((netHalfStatePotential true x : ℚ) : ℝ)) <
        (((5 / 3 : ℚ) *
          ((∑ i : Fin 7, (7 / 10 : ℚ) ^ sevenCostsAt x i *
            netHalfStatePotential
              (nextGrowingHeightState true (sevenCostsAt x i)) (ys i)) +
            (7 / 10 : ℚ) * netHalfStatePotential false z) : ℚ) : ℝ) :=
    Rat.cast_lt.mpr hrat
  refine ⟨ys, z, hys, hchildren, hz, hzstate, hdisj, ?_⟩
  norm_num at hc ⊢
  exact hc

/-- In a safe high source class, the seven growing children and shrinking
child strictly expand the potential under the exact telescoping weights. -/
theorem exists_netHalfShrinkingEdgeExpansion {d x : ℕ}
    (hx : 2 ≤ x) (h3 : ¬3 ∣ x) (hstate : InHeightState d true x)
    (hrem : x % 9 = 2 ∨ x % 9 = 8) :
    ∃ (ys : Fin 7 → ℕ) (z : ℕ), Function.Injective ys ∧
      (∀ i, GrowingUnitOddBlockChild x (ys i) (sevenCostsAt x i) ∧
        InHeightState d (nextGrowingHeightState true (sevenCostsAt x i)) (ys i)) ∧
      UnitOddBlockChildAtOne x z ∧ InHeightState d false z ∧
      (∀ i, z ≠ ys i) ∧
      (netHalfStatePotential true x : ℝ) <
        (∑ i : Fin 7, netHalfEdgeWeight x (ys i) *
          netHalfStatePotential
            (nextGrowingHeightState true (sevenCostsAt x i)) (ys i)) +
          netHalfEdgeWeight x z * netHalfStatePotential false z := by
  obtain ⟨ys, z, hys, hchildren, hz, hzstate, hdisj, hrat⟩ :=
    rationalShrinkingExpansion_real hx h3 hstate hrem
  rw [mul_add, Finset.mul_sum] at hrat
  have hgrow :
      (∑ i : Fin 7, (5 / 3 : ℝ) *
          ((7 / 10 : ℝ) ^ sevenCostsAt x i *
            netHalfStatePotential
              (nextGrowingHeightState true (sevenCostsAt x i)) (ys i))) <
        ∑ i : Fin 7, netHalfEdgeWeight x (ys i) *
          netHalfStatePotential
            (nextGrowingHeightState true (sevenCostsAt x i)) (ys i) := by
    apply Finset.sum_lt_sum_of_nonempty
    · exact Finset.univ_nonempty
    · intro i _
      rw [← mul_assoc]
      apply mul_lt_mul_of_pos_right
      · simpa [netHalfRationalWeight] using
          netHalfRationalWeight_lt_edgeWeight
            (by have := (hchildren i).1.2.1; omega)
            (by have := (hchildren i).1.1; omega)
            (hchildren i).1.2.2.2.2
      · exact_mod_cast netHalfStatePotential_pos
          (nextGrowingHeightState true (sevenCostsAt x i))
          (hchildren i).1.2.2.1
  have hshrink :
      (5 / 3 : ℝ) * ((7 / 10 : ℝ) * netHalfStatePotential false z) <
        netHalfEdgeWeight x z * netHalfStatePotential false z := by
    rw [← mul_assoc]
    apply mul_lt_mul_of_pos_right
    · simpa [netHalfRationalWeight] using
        netHalfRationalWeight_lt_edgeWeight (x := x) (y := z) (j := 1)
          (by have hblock := hz.2.2.2; omega) (by norm_num)
          (by simpa using hz.2.2.2)
    · exact_mod_cast netHalfStatePotential_pos false hz.2.1
  exact ⟨ys, z, hys, hchildren, hz, hzstate, hdisj,
    hrat.trans (add_lt_add hgrow hshrink)⟩

/-! ## A uniform finite child-set interface -/

/-- A height state paired with its odd endpoint. -/
abbrev NetHalfNode := Bool × ℕ

/-- The local child relation used by the stopping construction. -/
def NetHalfChildAt (d : ℕ) (parent child : NetHalfNode) : Prop :=
  ReusableOddBlockChild parent.2 child.2 ∧
    InHeightState d child.1 child.2

/-- A finite state frontier does not count one natural endpoint twice under
different state labels. -/
def NetHalfValuesInjective (C : Finset NetHalfNode) : Prop :=
  ∀ a ∈ C, ∀ b ∈ C, a.2 = b.2 → a = b

private theorem exists_growingChildFinset {d x : ℕ} (high : Bool)
    (hx : 2 ≤ x) (h3 : ¬3 ∣ x) (hstate : InHeightState d high x)
    (hn : netHalfHasShrinkingChild high x = false) :
    ∃ C : Finset NetHalfNode, C.Nonempty ∧ NetHalfValuesInjective C ∧
      (∀ c ∈ C, NetHalfChildAt d (high, x) c) ∧
      (netHalfStatePotential high x : ℝ) <
        ∑ c ∈ C, netHalfEdgeWeight x c.2 *
          netHalfStatePotential c.1 c.2 := by
  obtain ⟨ys, hys, hchildren, hexpand⟩ :=
    exists_netHalfGrowingEdgeExpansion high hx h3 hstate hn
  let f : Fin 7 → NetHalfNode := fun i =>
    (nextGrowingHeightState high (sevenCostsAt x i), ys i)
  have hf : Function.Injective f := by
    intro i i' hii'
    apply hys
    exact congrArg Prod.snd hii'
  let C : Finset NetHalfNode := Finset.univ.image f
  refine ⟨C, ?_, ?_, ?_, ?_⟩
  · exact Finset.Nonempty.image Finset.univ_nonempty f
  · intro a ha b hb hab
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨i', _, rfl⟩ := Finset.mem_image.mp hb
    have hii' : i = i' := hys hab
    subst i'
    rfl
  · intro c hc
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hc
    exact ⟨(hchildren i).1.toReusable, (hchildren i).2⟩
  · rw [show (∑ c ∈ C, netHalfEdgeWeight x c.2 *
        netHalfStatePotential c.1 c.2) =
      ∑ i : Fin 7, netHalfEdgeWeight x (ys i) *
        netHalfStatePotential
          (nextGrowingHeightState high (sevenCostsAt x i)) (ys i) by
        unfold C
        rw [Finset.sum_image]
        exact fun _ _ _ _ hii => hf hii]
    exact hexpand

private theorem exists_shrinkingChildFinset {d x : ℕ}
    (hx : 2 ≤ x) (h3 : ¬3 ∣ x) (hstate : InHeightState d true x)
    (hrem : x % 9 = 2 ∨ x % 9 = 8) :
    ∃ C : Finset NetHalfNode, C.Nonempty ∧ NetHalfValuesInjective C ∧
      (∀ c ∈ C, NetHalfChildAt d (true, x) c) ∧
      (netHalfStatePotential true x : ℝ) <
        ∑ c ∈ C, netHalfEdgeWeight x c.2 *
          netHalfStatePotential c.1 c.2 := by
  obtain ⟨ys, z, hys, hchildren, hz, hzstate, hdisj, hexpand⟩ :=
    exists_netHalfShrinkingEdgeExpansion hx h3 hstate hrem
  let f : Fin 7 → NetHalfNode := fun i =>
    (nextGrowingHeightState true (sevenCostsAt x i), ys i)
  have hf : Function.Injective f := by
    intro i i' hii'
    apply hys
    exact congrArg Prod.snd hii'
  let G : Finset NetHalfNode := Finset.univ.image f
  have hznot : (false, z) ∉ G := by
    intro hzmem
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hzmem
    exact hdisj i (congrArg Prod.snd hi).symm
  let C : Finset NetHalfNode := insert (false, z) G
  refine ⟨C, ⟨(false, z), by simp [C]⟩, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    rcases Finset.mem_insert.mp ha with rfl | ha
    · rcases Finset.mem_insert.mp hb with rfl | hb
      · rfl
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hb
        exact (hdisj i hab).elim
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact (hdisj i hab.symm).elim
      · obtain ⟨i', _, rfl⟩ := Finset.mem_image.mp hb
        have hii' : i = i' := hys hab
        subst i'
        rfl
  · intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact ⟨hz.toReusable, hzstate⟩
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hc
      exact ⟨(hchildren i).1.toReusable, (hchildren i).2⟩
  · rw [show (∑ c ∈ C, netHalfEdgeWeight x c.2 *
        netHalfStatePotential c.1 c.2) =
      (∑ i : Fin 7, netHalfEdgeWeight x (ys i) *
        netHalfStatePotential
          (nextGrowingHeightState true (sevenCostsAt x i)) (ys i)) +
        netHalfEdgeWeight x z * netHalfStatePotential false z by
        unfold C
        rw [Finset.sum_insert hznot]
        unfold G
        rw [Finset.sum_image]
        · ring
        · exact fun _ _ _ _ hii => hf hii]
    exact hexpand

/-- Every reusable parent state has a nonempty, value-injective finite child
set with exact telescoping-weight expansion. -/
theorem exists_netHalfChildFinset {d x : ℕ} (high : Bool)
    (hx : 2 ≤ x) (h3 : ¬3 ∣ x) (hstate : InHeightState d high x) :
    ∃ C : Finset NetHalfNode, C.Nonempty ∧ NetHalfValuesInjective C ∧
      (∀ c ∈ C, NetHalfChildAt d (high, x) c) ∧
      (netHalfStatePotential high x : ℝ) <
        ∑ c ∈ C, netHalfEdgeWeight x c.2 *
          netHalfStatePotential c.1 c.2 := by
  cases high with
  | false =>
      exact exists_growingChildFinset false hx h3 hstate
        (by simp [netHalfHasShrinkingChild])
  | true =>
      by_cases hn : netHalfHasShrinkingChild true x = false
      · exact exists_growingChildFinset true hx h3 hstate hn
      · have hyes : netHalfHasShrinkingChild true x = true :=
          Bool.eq_true_of_not_eq_false hn
        exact exists_shrinkingChildFinset hx h3 hstate
          (by simpa [netHalfHasShrinkingChild] using hyes)

/-! ## Endpoint-to-band conversion -/

/-- A path from `y` to `x` whose floor `d` is allowed to lie below the
destination.  `ReachesInBand d X y` is the special case `x = d`; separating
these parameters is essential for a shrinking inverse edge. -/
def ReachesToInBand (d X x y : ℕ) : Prop :=
  ∃ k, step^[k] y = x ∧
    ∀ t, t ≤ k → d ≤ step^[t] y ∧ step^[t] y ≤ X

/-- A standard band witness is also a generalized witness with destination
equal to its floor. -/
theorem ReachesInBand.toReachesToInBand {d X y : ℕ}
    (h : ReachesInBand d X y) : ReachesToInBand d X d y := h

/-- Lowering the floor of a local band witness leaves its destination
unchanged. -/
theorem reachesToInBand_of_reachesInBand {d x X y : ℕ} (hdx : d ≤ x)
    (h : ReachesInBand x X y) : ReachesToInBand d X x y := by
  obtain ⟨k, hk, hband⟩ := h
  exact ⟨k, hk, fun t ht => ⟨hdx.trans (hband t ht).1, (hband t ht).2⟩⟩

/-- Generalized band witnesses compose through an intermediate destination. -/
theorem reachesToInBand_trans {d X x m Y y Z : ℕ}
    (h1 : ReachesToInBand d Y m y) (h2 : ReachesToInBand d X x m)
    (hYZ : Y ≤ Z) (hXZ : X ≤ Z) : ReachesToInBand d Z x y := by
  obtain ⟨k1, hk1, hb1⟩ := h1
  obtain ⟨k2, hk2, hb2⟩ := h2
  refine ⟨k2 + k1, ?_, ?_⟩
  · rw [Function.iterate_add_apply, hk1, hk2]
  · intro t ht
    rcases Nat.lt_or_ge k1 t with hgt | hle
    · have hsplit : step^[t] y = step^[t - k1] m := by
        rw [← hk1, ← Function.iterate_add_apply]
        congr 1
        omega
      obtain ⟨hlo, hhi⟩ := hb2 (t - k1) (by omega)
      rw [hsplit]
      exact ⟨hlo, hhi.trans hXZ⟩
    · obtain ⟨hlo, hhi⟩ := hb1 t hle
      exact ⟨hlo, hhi.trans hYZ⟩

/-- A growing odd block has peak at most four times its child endpoint. -/
theorem GrowingUnitOddBlockChild.reachesInEndpointBand {x y j : ℕ}
    (h : GrowingUnitOddBlockChild x y j) : ReachesInBand x (4 * y) y := by
  apply reachesInBand_mono_ceiling (h := h.reachesInBand)
  obtain ⟨_, hyodd, _, _, hblock⟩ := h
  have hy : 1 ≤ y := by omega
  omega

/-- A safe shrinking block has its two-step forward path inside `[d, 2x]`. -/
theorem UnitOddBlockChildAtOne.reachesToInBand {d x y : ℕ}
    (hd : d ≤ y) (h : UnitOddBlockChildAtOne x y) :
    ReachesToInBand d (2 * x) x y := by
  obtain ⟨hyodd, _, hyx, hblock⟩ := h
  have hstep : step y = 2 * x := by
    unfold step
    simp [hyodd, hblock]
  refine ⟨2, ?_, ?_⟩
  · rw [show step^[2] y = step (step y) by rfl, hstep, step_two_mul]
  · intro t ht
    interval_cases t
    · simp only [Function.iterate_zero_apply]
      exact ⟨hd, by omega⟩
    · simp only [Function.iterate_one, hstep]
      exact ⟨by omega, le_rfl⟩
    · rw [show step^[2] y = x by rw [show step^[2] y = step (step y) by rfl,
          hstep, step_two_mul]]
      exact ⟨hd.trans hyx.le, by omega⟩

end CollatzMoonshot.FrontA
