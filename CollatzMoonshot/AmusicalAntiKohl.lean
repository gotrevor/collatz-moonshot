/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Obstructions.Amusical

/-!
# The anti-Kohl conjecture and transient cones

Kohl's permutation `ω` has a single orbit containing residue-class tails, built from slope-`1`
pieces.  `U` has none: every slope `3/2^k` has `3`-adic valuation exactly `1`, so the slope of
`Uˡ` has valuation `ℓ`.  The 2026-10-13 "global" agent isolated the hypothesis that survives every
proved counter-model:

**Anti-Kohl conjecture** (`AntiKohlConjecture p`, believed ~93%).  A residue-class-wise affine
permutation of `ℤ` whose slopes all have `p`-adic valuation `1` has no orbit containing a
residue-class tail.  For `p = 3` it gives `U` a seventh orbit (`atLeastSevenOrbits_of_antiKohl`).

The "antikohl" agent (same day) proved it for explicit wild members of the class via
**Theorem T** (`orbit_densityZero_of_transientCone`).  Suppose `σ(S) ⊆ S`, and both the forward
core `σⁿ(S)` and the never-entering set `{x : σʲ x ∉ S, j ≤ n}` have densities tending to `0`.  Then
every finite union of orbits has density `0`.  So:

* `κ` (modulus `6`, slopes `2`, `2/3`, cone `odd ∪ 12ℤ`) has only density-`0` orbits;
* `σ_τ = τ ∘ U`, with `τ` the class transposition `2k+1 ↔ 4k+2`, does too (cone `2 + 4ℤ`, on which
  `σ_τ x = 3x`).  This holds for `31` of the `32` single-class-transposition perturbations of `U`
  that have a cone.

For `U` itself the method is vacuous: no union of residue classes is a cone
(`amusical_no_periodic_cone`).  "One fixed prime" is essential.  Conjugating translation by an
RCWA map gives slopes `3/2` and `2/3` only, valuation `1` at *some* prime on every piece, and one
orbit (`mixedPrime_single_orbit`).

Paper proofs: agent report `antikohl.md` (2026-10-13), summarized in
`RESEARCH-2026-10-13-amusical-single-chain.md` §15.  Core densities re-checked by box counting
(`scripts/amusical/cores.py`); cone-freeness of `U` for moduli up to `200` by
`scripts/amusical/cone.py`.  Treadmill target (`KICKOFF-2026-10-13-amusical-antikohl.md`): close
every `sorry` here.
-/

namespace CollatzMoonshot.Amusical

open CollatzMoonshot.Obstructions.Amusical

/-- `σ` is residue-class-wise affine with modulus `m`: on the class of `r`,
`c r * σ x = a r * x + b r`. -/
structure IsRCWA (σ : ℤ → ℤ) (m : ℕ) (a b c : ℤ → ℤ) : Prop where
  pos : 0 < m
  coeff : ∀ r, 0 < c r ∧ a r ≠ 0
  eqn : ∀ x, c (x % m) * σ x = a (x % m) * x + b (x % m)

/-- Every slope `a r / c r` has `p`-adic valuation exactly `1`. -/
def SlopeValOne (p m : ℕ) (a c : ℤ → ℤ) : Prop :=
  ∀ r : ℤ, 0 ≤ r → r < m → padicValRat p ((a r : ℚ) / c r) = 1

/-- The two-sided orbit of `x` under a permutation `σ`. -/
def permOrbit (σ : Equiv.Perm ℤ) (x : ℤ) : Set ℤ :=
  Set.range fun n : ℤ => (σ ^ n) x

/-- `O` contains a tail `{y ≡ r (mod M), y ≥ N}` of a residue class. -/
def ContainsClassTail (O : Set ℤ) : Prop :=
  ∃ M r N : ℤ, 0 < M ∧ ∀ y, y ≡ r [ZMOD M] → N ≤ y → y ∈ O

/-- **Believed (~93%), open: the anti-Kohl conjecture at the prime `p`.** -/
def AntiKohlConjecture (p : ℕ) : Prop :=
  ∀ (σ : Equiv.Perm ℤ) (m : ℕ) (a b c : ℤ → ℤ), IsRCWA σ m a b c → SlopeValOne p m a c →
    ∀ x, ¬ ContainsClassTail (permOrbit σ x)

/-- **Target.**  `U` belongs to the anti-Kohl class at `p = 3`: modulus `4`, `a = 3`,
`c ∈ {2, 4}`, `b ∈ {0, 1, −1}`. -/
theorem amusical_antiKohl_class :
    ∃ a b c : ℤ → ℤ, IsRCWA amusical 4 a b c ∧ SlopeValOne 3 4 a c := by
  refine ⟨fun _ => 3, fun r => if r % 2 = 0 then 0 else if r % 4 = 1 then 1 else -1,
    fun r => if r % 2 = 0 then 2 else 4, ?_, ?_⟩
  · refine ⟨by norm_num, ?_, ?_⟩
    · intro r
      dsimp
      split_ifs <;> omega
    · intro x
      dsimp
      unfold amusical
      split_ifs <;> omega
  · intro r hr0 hr4
    have h3 : padicValRat 3 (3 : ℚ) = 1 := padicValRat.self (by norm_num)
    have h2 : padicValRat 3 (2 : ℚ) = 0 := by
      change padicValRat 3 ((2 : ℕ) : ℚ) = 0
      rw [padicValRat.of_nat]
      rw [padicValNat.eq_zero_of_not_dvd (p := 3) (n := 2) (by norm_num)]
      norm_num
    have h4 : padicValRat 3 (4 : ℚ) = 0 := by
      change padicValRat 3 ((4 : ℕ) : ℚ) = 0
      rw [padicValRat.of_nat]
      rw [padicValNat.eq_zero_of_not_dvd (p := 3) (n := 4) (by norm_num)]
      norm_num
    have hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases hr with rfl | rfl | rfl | rfl
    all_goals
      dsimp
      rw [padicValRat.div (by norm_num) (by norm_num), h3]
      first | rw [h2] | rw [h4]
      norm_num

/-- **Target.**  The anti-Kohl conjecture at `3` gives `U` a seventh orbit.  Paper proof: without a
seventh orbit, the orbit of `8` contains every nonnegative integer off the twenty known cycle
members (`AmusicalChains`: the six orbits cover `ℕ`), so it contains the class tail
`{y ≥ 112}`; `permOrbit amusicalPerm 8 = amusicalOrbit 8`. -/
theorem atLeastSevenOrbits_of_antiKohl (h : AntiKohlConjecture 3) :
    AmusicalAtLeastSevenOrbits := by
  obtain ⟨a, b, c, hrcwa, hslope⟩ := amusical_antiKohl_class
  have hnoTail : ¬ ContainsClassTail (permOrbit amusicalPerm 8) :=
    h amusicalPerm 4 a b c (by
      change IsRCWA amusical 4 a b c
      exact hrcwa) hslope 8
  have hcomp : ({n : ℤ | 0 ≤ n} \ amusicalOrbit 8).Infinite := by
    by_contra hnotinf
    have hfinite : ({n : ℤ | 0 ≤ n} \ amusicalOrbit 8).Finite :=
      Set.not_infinite.1 hnotinf
    obtain ⟨N, hN⟩ := hfinite.bddAbove
    apply hnoTail
    refine ⟨1, 0, max N 0 + 1, by norm_num, ?_⟩
    intro y _ hy
    change y ∈ amusicalOrbit 8
    by_contra hyorb
    have hmax0 : 0 ≤ max N 0 := le_max_right N 0
    have hmaxN : N ≤ max N 0 := le_max_left N 0
    have hstep : max N 0 ≤ max N 0 + 1 := by omega
    have hycomp : y ∈ {n : ℤ | 0 ≤ n} \ amusicalOrbit 8 :=
      ⟨hmax0.trans (hstep.trans hy), hyorb⟩
    have hygtN : N < y := lt_of_le_of_lt hmaxN (lt_of_lt_of_le (by omega) hy)
    exact (not_le_of_gt hygtN) (hN hycomp)
  have hknown : (knownCycleMembers : Set ℤ).Finite := Finset.finite_toSet _
  obtain ⟨n, ⟨hn0, hn8⟩, hnknown⟩ := (hcomp.sdiff hknown).nonempty
  have hclosed : ∀ a ∈ ({0, 1, 2, 4, 44} : Finset ℤ),
      amusicalOrbit a ⊆ (knownCycleMembers : Set ℤ) := by
    intro a ha
    apply amusicalOrbit_subset_of_closed (S := (knownCycleMembers : Set ℤ))
        (by decide) (by decide)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> decide
  have hnorb : ∀ a ∈ ({0, 1, 2, 4, 44, 8} : Finset ℤ),
      amusicalOrbit n ≠ amusicalOrbit a := by
    intro a ha heq
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hnknown (hclosed _ (by decide) (heq ▸ mem_amusicalOrbit_self n))
      | exact hn8 (heq ▸ mem_amusicalOrbit_self n)
  refine ⟨insert n {0, 1, 2, 4, 44, 8}, ?_, ?_, ?_⟩
  · have hnmem : n ∉ ({0, 1, 2, 4, 44, 8} : Finset ℤ) := by
      intro hn'
      exact hnorb n (by simpa using hn') rfl
    simp [hnmem]
  · intro x hx
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact hn0
    · simp only [Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · intro a ha b hb hab
    change a ∈ (insert n {0, 1, 2, 4, 44, 8} : Finset ℤ) at ha
    change b ∈ (insert n {0, 1, 2, 4, 44, 8} : Finset ℤ) at hb
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hnorb b (Finset.mem_insert.mp hb |>.resolve_left hab.symm)
    · rcases Finset.mem_insert.mp hb with hbn | hb
      · subst b
        exact (hnorb a ha).symm
      · exact amusical_six_distinct_orbits a ha b hb hab

/-- **Target (the gate).**  `U` has no periodic cone: a union of residue classes mod `M` that `U`
maps into itself is empty or everything.  Paper proof: the residue graph of `U` mod `M` (edge
`r → s` when `U` maps some `x ≡ r` to `s`) is strongly connected (agent report `seventh.md`, T4);
a forward-closed class union is a union of strongly connected components with no exit. -/
theorem amusical_no_periodic_cone (M : ℕ) (hM : 0 < M) (R : Set (ZMod M))
    (h : ∀ n : ℤ, (n : ZMod M) ∈ R → ((amusical n : ℤ) : ZMod M) ∈ R) :
    R = ∅ ∨ R = Set.univ := by
  sorry

/-! ## Theorem T -/

open Classical in
/-- `A` has density `0` in the symmetric boxes `[−X, X]`. -/
def IntDensityZero (A : Set ℤ) : Prop :=
  Filter.Tendsto (fun X : ℕ => (((Finset.Icc (-(X : ℤ)) X).filter (· ∈ A)).card : ℝ) / X)
    Filter.atTop (nhds 0)

open Classical in
/-- `A` has upper density at most `ε` in the symmetric boxes, eventually. -/
def IntDensityLE (A : Set ℤ) (ε : ℝ) : Prop :=
  ∀ᶠ X : ℕ in Filter.atTop, (((Finset.Icc (-(X : ℤ)) X).filter (· ∈ A)).card : ℝ) ≤ ε * X

/-- Membership in a forward-invariant cone is monotone along the integer coordinates of an
orbit.  This is the order-theoretic core of the finite-error term in Theorem T. -/
theorem cone_mem_zpow_mono (σ : Equiv.Perm ℤ) (S : Set ℤ)
    (hS : ∀ x ∈ S, σ x ∈ S) {x : ℤ} {a b : ℤ} (hab : a ≤ b)
    (ha : (σ ^ a) x ∈ S) : (σ ^ b) x ∈ S := by
  let d := (b - a).toNat
  have hd : b = a + d := by
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hab)]
    omega
  rw [hd]
  induction d with
  | zero => simpa
  | succ d ih =>
      rw [Nat.cast_succ]
      have he : a + ((d : ℤ) + 1) = 1 + (a + (d : ℤ)) := by omega
      rw [he, zpow_add, Equiv.Perm.mul_apply, zpow_one]
      exact hS _ ih

/-- A nontrivial monotone truth set on `ℤ` has a first true index.  Applied to cone membership
along an orbit, this supplies the unique transition around which Theorem T discards finitely many
points. -/
theorem exists_first_of_monotone_int (P : ℤ → Prop)
    (hmono : ∀ ⦃a b⦄, a ≤ b → P a → P b) (htrue : ∃ a, P a)
    (hfalse : ∃ a, ¬ P a) : ∃ t, P t ∧ ¬ P (t - 1) := by
  obtain ⟨a, ha⟩ := hfalse
  have hbdd : ∃ b : ℤ, ∀ z, P z → b ≤ z := by
    refine ⟨a + 1, ?_⟩
    intro z hz
    by_contra h
    have hza : z ≤ a := by omega
    exact ha (hmono hza hz)
  obtain ⟨t, ht, hleast⟩ := Int.exists_least_of_bdd hbdd htrue
  refine ⟨t, ht, ?_⟩
  intro hprev
  have := hleast (t - 1) hprev
  omega

/-- Every orbit is wholly in the cone, wholly outside it, or crosses its boundary exactly once
in the ordered integer parametrization. -/
theorem cone_orbit_trichotomy (σ : Equiv.Perm ℤ) (S : Set ℤ)
    (hS : ∀ x ∈ S, σ x ∈ S) (x : ℤ) :
    (∀ k : ℤ, (σ ^ k) x ∈ S) ∨ (∀ k : ℤ, (σ ^ k) x ∉ S) ∨
      ∃ t : ℤ, (σ ^ t) x ∈ S ∧ (σ ^ (t - 1)) x ∉ S := by
  classical
  by_cases hall : ∀ k : ℤ, (σ ^ k) x ∈ S
  · exact Or.inl hall
  by_cases hnone : ∀ k : ℤ, (σ ^ k) x ∉ S
  · exact Or.inr (Or.inl hnone)
  · apply Or.inr
    apply Or.inr
    apply exists_first_of_monotone_int (fun k => (σ ^ k) x ∈ S)
    · intro a b hab ha
      exact cone_mem_zpow_mono σ S hS hab ha
    · obtain ⟨k, hk⟩ := not_forall.mp hnone
      exact ⟨k, Classical.not_not.mp hk⟩
    · exact not_forall.mp hall

/-- Away from at most `2n + 1` consecutive coordinates, one orbit is covered by the forward
`n`-core of a cone and its `n`-step never-entering set. -/
theorem exists_orbit_exception (σ : Equiv.Perm ℤ) (S : Set ℤ)
    (hS : ∀ x ∈ S, σ x ∈ S) (x : ℤ) (n : ℕ) :
    ∃ E : Finset ℤ, E.card ≤ 2 * n + 1 ∧
      permOrbit σ x ⊆ ((σ ^ n) '' S) ∪ {y | ∀ j ≤ n, (σ ^ j) y ∉ S} ∪ (E : Set ℤ) := by
  classical
  rcases cone_orbit_trichotomy σ S hS x with hall | hnone | ⟨t, ht, htprev⟩
  · refine ⟨∅, by simp, ?_⟩
    rintro y ⟨k, rfl⟩
    apply Or.inl
    apply Or.inl
    refine ⟨(σ ^ (k - n)) x, hall _, ?_⟩
    rw [← Equiv.Perm.mul_apply, ← zpow_natCast, ← zpow_add,
      show (n : ℤ) + (k - n) = k by omega]
  · refine ⟨∅, by simp, ?_⟩
    rintro y ⟨k, rfl⟩
    apply Or.inl
    apply Or.inr
    intro j hj
    rw [← Equiv.Perm.mul_apply, ← zpow_natCast, ← zpow_add]
    exact hnone _
  · let E : Finset ℤ :=
      (Finset.range (2 * n + 1)).image fun i : ℕ => (σ ^ (t - n + i)) x
    refine ⟨E, ?_, ?_⟩
    · calc
        E.card ≤ (Finset.range (2 * n + 1)).card := by
          exact Finset.card_image_le
        _ = 2 * n + 1 := Finset.card_range _
    · rintro y ⟨k, rfl⟩
      by_cases hlo : k < t - n
      · apply Or.inl
        apply Or.inr
        intro j hj hmem
        apply htprev
        apply cone_mem_zpow_mono σ S hS (a := k + j) (b := t - 1) (by omega)
        have hmem' : (σ ^ ((j : ℤ) + k)) x ∈ S := by
          rw [zpow_add, Equiv.Perm.mul_apply, zpow_natCast]
          exact hmem
        simpa [add_comm] using hmem'
      by_cases hhi : t + n ≤ k
      · apply Or.inl
        apply Or.inl
        refine ⟨(σ ^ (k - n)) x, cone_mem_zpow_mono σ S hS (a := t)
          (b := k - n) (by omega) ht, ?_⟩
        rw [← Equiv.Perm.mul_apply, ← zpow_natCast, ← zpow_add,
          show (n : ℤ) + (k - n) = k by omega]
      · apply Or.inr
        have hi0 : 0 ≤ k - (t - n) := by omega
        have hilt : k - (t - n) < 2 * n + 1 := by omega
        have hi : (k - (t - n)).toNat < 2 * n + 1 := by omega
        change (σ ^ k) x ∈ E
        rw [Finset.mem_image]
        refine ⟨(k - (t - n)).toNat, Finset.mem_range.mpr hi, ?_⟩
        rw [Int.toNat_of_nonneg hi0]
        congr 2
        omega

/-- Every natural iterate of a permutation preserves a forward-invariant cone. -/
theorem cone_pow_mem (σ : Equiv.Perm ℤ) (S : Set ℤ)
    (hS : ∀ x ∈ S, σ x ∈ S) {x : ℤ} (n : ℕ) (hx : x ∈ S) :
    (σ ^ n) x ∈ S := by
  have h := cone_mem_zpow_mono σ S hS (x := x) (a := 0) (b := (n : ℤ))
    (by omega) (by simpa using hx)
  simpa [zpow_natCast] using h

/-- Later forward cores of a forward-invariant cone are contained in earlier cores. -/
theorem cone_pow_image_antitone (σ : Equiv.Perm ℤ) (S : Set ℤ)
    (hS : ∀ x ∈ S, σ x ∈ S) {a b : ℕ} (hab : a ≤ b) :
    ((σ ^ b) '' S) ⊆ ((σ ^ a) '' S) := by
  rintro y ⟨x, hx, rfl⟩
  refine ⟨(σ ^ (b - a)) x, cone_pow_mem σ S hS (b - a) hx, ?_⟩
  rw [← Equiv.Perm.mul_apply, ← pow_add]
  congr 2
  omega

/-- The exceptional intervals for finitely many seeds can be combined with the expected linear
cardinality bound. -/
theorem exists_orbits_exception (σ : Equiv.Perm ℤ) (S : Set ℤ)
    (hS : ∀ x ∈ S, σ x ∈ S) (F : Finset ℤ) (n : ℕ) :
    ∃ E : Finset ℤ, E.card ≤ F.card * (2 * n + 1) ∧
      (⋃ x ∈ F, permOrbit σ x) ⊆
        ((σ ^ n) '' S) ∪ {y | ∀ j ≤ n, (σ ^ j) y ∉ S} ∪ (E : Set ℤ) := by
  classical
  choose E hEcard hEcover using fun x : ℤ => exists_orbit_exception σ S hS x n
  refine ⟨F.biUnion E, Finset.card_biUnion_le_card_mul F E (2 * n + 1) ?_, ?_⟩
  · intro x hx
    exact hEcard x
  · intro y hy
    rcases Set.mem_iUnion.mp hy with ⟨x, hy⟩
    rcases Set.mem_iUnion.mp hy with ⟨hx, hy⟩
    rcases hEcover x hy with hy | hy
    · exact Or.inl hy
    · exact Or.inr (Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨x, hx, hy⟩))

open Classical in
private noncomputable def intBoxCount (A : Set ℤ) (X : ℕ) : ℕ :=
  ((Finset.Icc (-(X : ℤ)) X).filter (· ∈ A)).card

private theorem intBoxCount_mono {A B : Set ℤ} (hAB : A ⊆ B) (X : ℕ) :
    intBoxCount A X ≤ intBoxCount B X := by
  classical
  unfold intBoxCount
  apply Finset.card_le_card
  intro y hy
  simp only [Finset.mem_filter] at hy ⊢
  exact ⟨hy.1, hAB hy.2⟩

private theorem intBoxCount_le_union_finset {U A B : Set ℤ} {E : Finset ℤ}
    (hU : U ⊆ A ∪ B ∪ (E : Set ℤ)) (X : ℕ) :
    intBoxCount U X ≤ intBoxCount A X + intBoxCount B X + E.card := by
  classical
  let box := Finset.Icc (-(X : ℤ)) X
  let UA := box.filter (· ∈ A)
  let UB := box.filter (· ∈ B)
  have hsubset : box.filter (· ∈ U) ⊆ (UA ∪ UB) ∪ E := by
    intro y hy
    simp only [Finset.mem_filter] at hy
    rcases hU hy.2 with (hyA | hyB) | hyE
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inl (Finset.mem_filter.mpr ⟨hy.1, hyA⟩))))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inr (Finset.mem_filter.mpr ⟨hy.1, hyB⟩))))
    · exact Finset.mem_union.mpr (Or.inr hyE)
  calc
    intBoxCount U X = (box.filter (· ∈ U)).card := by rfl
    _ ≤ ((UA ∪ UB) ∪ E).card := Finset.card_le_card hsubset
    _ ≤ (UA ∪ UB).card + E.card := Finset.card_union_le _ _
    _ ≤ (UA.card + UB.card) + E.card :=
      Nat.add_le_add_right (Finset.card_union_le _ _) _

/-- **Target (Theorem T).**  A cone `S` (`σ S ⊆ S`) whose forward cores `σⁿ S` and never-entering
sets `{x : σʲ x ∉ S, j ≤ n}` both have density tending to `0` makes every finite union of orbits
density `0`.  Paper proof: an orbit is inside `S`, inside the complement, or a backward ray in the
complement followed by a forward ray in `S`; in each case all but `2n` of its points lie in `σⁿ S`
or in the `n`-th never-entering set. -/
theorem orbit_densityZero_of_transientCone (σ : Equiv.Perm ℤ) (S : Set ℤ)
    (hS : ∀ x ∈ S, σ x ∈ S)
    (hfwd : ∀ ε > 0, ∃ n : ℕ, IntDensityLE ((σ ^ n) '' S) ε)
    (hbwd : ∀ ε > 0, ∃ n : ℕ, IntDensityLE {x | ∀ j ≤ n, (σ ^ j) x ∉ S} ε)
    (F : Finset ℤ) : IntDensityZero (⋃ x ∈ F, permOrbit σ x) := by
  classical
  unfold IntDensityZero
  change Filter.Tendsto
    (fun X : ℕ => (intBoxCount (⋃ x ∈ F, permOrbit σ x) X : ℝ) / X)
      Filter.atTop (nhds 0)
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  let δ := ε / 4
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  obtain ⟨nf, hnf⟩ := hfwd δ hδ
  obtain ⟨nb, hnb⟩ := hbwd δ hδ
  let n := nf + nb
  let A : Set ℤ := (σ ^ n) '' S
  let B : Set ℤ := {x | ∀ j ≤ n, (σ ^ j) x ∉ S}
  have hAset : A ⊆ ((σ ^ nf) '' S) := by
    dsimp [A, n]
    exact cone_pow_image_antitone σ S hS (by omega)
  have hBset : B ⊆ {x | ∀ j ≤ nb, (σ ^ j) x ∉ S} := by
    intro x hx j hj
    exact hx j (by dsimp [B, n] at hx; omega)
  have hA : IntDensityLE A δ := by
    unfold IntDensityLE at hnf ⊢
    change ∀ᶠ X : ℕ in Filter.atTop,
      (intBoxCount ((σ ^ nf) '' S) X : ℝ) ≤ δ * X at hnf
    change ∀ᶠ X : ℕ in Filter.atTop, (intBoxCount A X : ℝ) ≤ δ * X
    filter_upwards [hnf] with X hX
    have hcard := intBoxCount_mono hAset X
    have hcard' : (intBoxCount A X : ℝ) ≤ intBoxCount ((σ ^ nf) '' S) X := by
      exact_mod_cast hcard
    exact hcard'.trans hX
  have hB : IntDensityLE B δ := by
    unfold IntDensityLE at hnb ⊢
    change ∀ᶠ X : ℕ in Filter.atTop,
      (intBoxCount {x | ∀ j ≤ nb, (σ ^ j) x ∉ S} X : ℝ) ≤ δ * X at hnb
    change ∀ᶠ X : ℕ in Filter.atTop, (intBoxCount B X : ℝ) ≤ δ * X
    filter_upwards [hnb] with X hX
    have hcard := intBoxCount_mono hBset X
    have hcard' : (intBoxCount B X : ℝ) ≤
        intBoxCount {x | ∀ j ≤ nb, (σ ^ j) x ∉ S} X := by
      exact_mod_cast hcard
    exact hcard'.trans hX
  obtain ⟨E, hEcard, hcover⟩ := exists_orbits_exception σ S hS F n
  have hEzero : Filter.Tendsto (fun X : ℕ => (E.card : ℝ) / X)
      Filter.atTop (nhds 0) := tendsto_const_div_atTop_nhds_zero_nat _
  have hE : ∀ᶠ X : ℕ in Filter.atTop, (E.card : ℝ) / X < δ :=
    hEzero.eventually (gt_mem_nhds hδ)
  filter_upwards [hA, hB, hE, Filter.eventually_ge_atTop 1] with X hAX hBX hEX hX
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX
  have hEX' : (E.card : ℝ) < δ * X := by
    rwa [div_lt_iff₀ hXpos] at hEX
  have hcard : intBoxCount (⋃ x ∈ F, permOrbit σ x) X ≤
      intBoxCount A X + intBoxCount B X + E.card :=
    intBoxCount_le_union_finset hcover X
  have hcard' : (intBoxCount (⋃ x ∈ F, permOrbit σ x) X : ℝ) ≤
      intBoxCount A X + intBoxCount B X + E.card := by
    exact_mod_cast hcard
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by positivity) hXpos.le),
    div_lt_iff₀ hXpos]
  have hsum : (intBoxCount (⋃ x ∈ F, permOrbit σ x) X : ℝ) <
      δ * X + δ * X + δ * X := by
    exact hcard'.trans_lt (add_lt_add_of_le_of_lt (add_le_add hAX hBX) hEX')
  have hthree : δ + δ + δ < ε := by
    dsimp [δ]
    linarith
  calc
    (intBoxCount (⋃ x ∈ F, permOrbit σ x) X : ℝ) <
      δ * X + δ * X + δ * X := hsum
    _ = (δ + δ + δ) * X := by ring
    _ < ε * X := mul_lt_mul_of_pos_right hthree hXpos

/-- A residue-class tail has positive lower density in the symmetric boxes. -/
theorem not_intDensityZero_of_containsClassTail (A : Set ℤ) :
    ContainsClassTail A → ¬ IntDensityZero A := by
  classical
  rintro ⟨M, r, N, hM, htail⟩ hzero
  let K : ℤ := max 0 (max (N - r) (-r))
  have hK0 : 0 ≤ K := le_max_left _ _
  have hKN : N - r ≤ K :=
    (le_max_left (N - r) (-r)).trans (le_max_right 0 (max (N - r) (-r)))
  have hKr : -r ≤ K :=
    (le_max_right (N - r) (-r)).trans (le_max_right 0 (max (N - r) (-r)))
  have hM1 : 1 ≤ M := by omega
  have hKM : K ≤ M * K := by nlinarith
  let y0 := r + M * K
  have hy00 : 0 ≤ y0 := by
    dsimp [y0]
    nlinarith
  have hy0N : N ≤ y0 := by
    dsimp [y0]
    nlinarith
  let m := M.toNat
  have hmpos : 0 < m := by
    dsimp [m]
    omega
  have hmcast : (m : ℤ) = M := by
    dsimp [m]
    rw [Int.toNat_of_nonneg hM.le]
  let a := y0.toNat
  have hacast : (a : ℤ) = y0 := by
    dsimp [a]
    rw [Int.toNat_of_nonneg hy00]
  have hlim : Filter.Tendsto
      (fun X : ℕ => (intBoxCount A X : ℝ) / X) Filter.atTop (nhds 0) := by
    exact hzero
  let c : ℝ := 1 / (2 * (m : ℝ))
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hevent : ∀ᶠ X : ℕ in Filter.atTop,
      (intBoxCount A X : ℝ) / X < c :=
    hlim.eventually (gt_mem_nhds hc)
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨X0, hX0⟩ := hevent
  let t := max 1 (max X0 a)
  have htpos : 0 < t := by
    dsimp [t]
    omega
  have hX0t : X0 ≤ t := by
    dsimp [t]
    omega
  have hat : a ≤ t := by
    dsimp [t]
    omega
  let X := a + m * t
  have htmt : t ≤ m * t := by
    simpa using Nat.mul_le_mul_right t hmpos
  have hX0X : X0 ≤ X := by
    dsimp [X]
    omega
  have hsmall := hX0 X hX0X
  let g : ℕ → ℤ := fun i => (a + m * i : ℕ)
  have hginj : Function.Injective g := by
    intro i j hij
    dsimp [g] at hij
    have hij' : a + m * i = a + m * j := by exact_mod_cast hij
    have hmul : m * i = m * j := Nat.add_left_cancel hij'
    exact Nat.mul_left_cancel hmpos hmul
  let P : Finset ℤ := (Finset.range t).image g
  have hPcard : P.card = t := by
    dsimp [P]
    rw [Finset.card_image_of_injective _ hginj, Finset.card_range]
  have hPsubset : P ⊆ (Finset.Icc (-(X : ℤ)) X).filter (· ∈ A) := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨i, hi, rfl⟩ := hz
    have hit : i < t := Finset.mem_range.mp hi
    have hgi0 : (0 : ℤ) ≤ g i := by
      dsimp [g]
      positivity
    have hgiX : g i ≤ (X : ℤ) := by
      dsimp [g, X]
      norm_cast
      exact Nat.add_le_add_left (Nat.mul_le_mul_left m hit.le) a
    have hgieq : g i = y0 + M * i := by
      dsimp [g]
      rw [hmcast, hacast]
    have hgiN : N ≤ g i := by
      rw [hgieq]
      have hi0 : (0 : ℤ) ≤ i := by omega
      nlinarith
    have hgimod : g i ≡ r [ZMOD M] := by
      rw [Int.modEq_iff_dvd]
      refine ⟨-(K + i), ?_⟩
      rw [hgieq]
      dsimp [y0]
      ring
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hgiX⟩,
      htail (g i) hgimod hgiN⟩
  have hcount : t ≤ intBoxCount A X := by
    unfold intBoxCount
    rw [← hPcard]
    exact Finset.card_le_card hPsubset
  have hXposNat : 0 < X := by
    have hmtpos : 0 < m * t := Nat.mul_pos hmpos htpos
    dsimp [X]
    omega
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hXposNat
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hmpos
  have htreal : (0 : ℝ) < t := by exact_mod_cast htpos
  have hXleNat : X ≤ 2 * m * t := by
    dsimp [X]
    nlinarith
  have hXle : (X : ℝ) ≤ 2 * (m : ℝ) * t := by exact_mod_cast hXleNat
  have hlower : c ≤ (t : ℝ) / X := by
    dsimp [c]
    rw [div_le_div_iff₀ (mul_pos (by norm_num) hmreal) hXpos]
    nlinarith
  have hcountReal : (t : ℝ) ≤ intBoxCount A X := by exact_mod_cast hcount
  have hratio : (t : ℝ) / X ≤ (intBoxCount A X : ℝ) / X :=
    div_le_div_of_nonneg_right hcountReal hXpos.le
  exact (not_lt_of_ge (hlower.trans hratio)) hsmall

/-- **Target.**  Under Theorem T's hypotheses `σ` has infinitely many orbits and none contains a
residue-class tail.  Paper proof: finitely many orbits would cover `ℤ`, of density `1`; a class
tail has density `1/(2M)` in the symmetric boxes. -/
theorem infinitelyManyOrbits_of_transientCone (σ : Equiv.Perm ℤ) (S : Set ℤ)
    (hS : ∀ x ∈ S, σ x ∈ S)
    (hfwd : ∀ ε > 0, ∃ n : ℕ, IntDensityLE ((σ ^ n) '' S) ε)
    (hbwd : ∀ ε > 0, ∃ n : ℕ, IntDensityLE {x | ∀ j ≤ n, (σ ^ j) x ∉ S} ε) :
    {O : Set ℤ | ∃ x, O = permOrbit σ x}.Infinite ∧ ∀ x, ¬ ContainsClassTail (permOrbit σ x) := by
  classical
  let Ω : Set (Set ℤ) := {O | ∃ x, O = permOrbit σ x}
  change Ω.Infinite ∧ ∀ x, ¬ ContainsClassTail (permOrbit σ x)
  constructor
  · by_contra hnot
    have hfinite : Ω.Finite := Set.not_infinite.mp hnot
    letI : Fintype Ω := hfinite.fintype
    let rep : Ω → ℤ := fun O => Classical.choose O.2
    have hrep (O : Ω) : O.1 = permOrbit σ (rep O) :=
      Classical.choose_spec O.2
    let F : Finset ℤ := Finset.univ.image rep
    have hcover : (⋃ x ∈ F, permOrbit σ x) = Set.univ := by
      rw [Set.eq_univ_iff_forall]
      intro y
      let O : Ω := ⟨permOrbit σ y, ⟨y, rfl⟩⟩
      have hmemF : rep O ∈ F := by
        exact Finset.mem_image.mpr ⟨O, Finset.mem_univ O, rfl⟩
      apply Set.mem_iUnion.mpr
      refine ⟨rep O, Set.mem_iUnion.mpr ⟨hmemF, ?_⟩⟩
      rw [← hrep O]
      exact ⟨0, by simp⟩
    have hdensity := orbit_densityZero_of_transientCone σ S hS hfwd hbwd F
    rw [hcover] at hdensity
    apply not_intDensityZero_of_containsClassTail Set.univ
      ⟨1, 0, 0, by norm_num, by simp⟩
    exact hdensity
  · intro x htail
    apply not_intDensityZero_of_containsClassTail (permOrbit σ x) htail
    simpa using orbit_densityZero_of_transientCone σ S hS hfwd hbwd ({x} : Finset ℤ)

/-! ## `κ`: an explicit member of the class at `p = 2` -/

/-- `κ(6k) = 12k+5`, `κ(6k+1) = 4k+3`, `κ(6k+2) = 4k+2`, `κ(6k+3) = 12k+1`, `κ(6k+4) = 4k`,
`κ(6k+5) = 12k+9`: slopes `2` and `2/3`. -/
def kappa (x : ℤ) : ℤ :=
  if x % 6 = 0 then 2 * x + 5
  else if x % 6 = 1 then (2 * x + 7) / 3
  else if x % 6 = 2 then (2 * x + 2) / 3
  else if x % 6 = 3 then 2 * x - 5
  else if x % 6 = 4 then (2 * x - 8) / 3
  else 2 * x - 1

/-- The inverse of `κ`, by image class. -/
def kappaInv (y : ℤ) : ℤ :=
  if y % 4 = 0 then (3 * y + 8) / 2
  else if y % 4 = 2 then (3 * y - 2) / 2
  else if y % 4 = 3 then (3 * y - 7) / 2
  else if y % 12 = 5 then (y - 5) / 2
  else if y % 12 = 1 then (y + 5) / 2
  else (y + 1) / 2

theorem kappaInv_kappa (x : ℤ) : kappaInv (kappa x) = x := by
  have h : x % 6 = 0 ∨ x % 6 = 1 ∨ x % 6 = 2 ∨ x % 6 = 3 ∨ x % 6 = 4 ∨ x % 6 = 5 := by omega
  rcases h with h | h | h | h | h | h <;> simp only [kappa, h] <;> norm_num <;>
    unfold kappaInv <;> split_ifs <;> omega

theorem kappa_kappaInv (y : ℤ) : kappa (kappaInv y) = y := by
  have h : y % 4 = 0 ∨ y % 4 = 2 ∨ y % 4 = 3 ∨ y % 12 = 5 ∨ y % 12 = 1 ∨ y % 12 = 9 := by omega
  rcases h with h | h | h | h | h | h
  · rw [kappaInv, if_pos h]; unfold kappa; split_ifs <;> omega
  · rw [kappaInv, if_neg (by omega), if_pos h]; unfold kappa; split_ifs <;> omega
  · rw [kappaInv, if_neg (by omega), if_neg (by omega), if_pos h]; unfold kappa
    split_ifs <;> omega
  · rw [kappaInv, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h]
    unfold kappa; split_ifs <;> omega
  · rw [kappaInv, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_pos h]
    unfold kappa; split_ifs <;> omega
  · rw [kappaInv, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
    unfold kappa; split_ifs <;> omega

/-- `κ` as a permutation of `ℤ`. -/
def kappaPerm : Equiv.Perm ℤ where
  toFun := kappa
  invFun := kappaInv
  left_inv := kappaInv_kappa
  right_inv := kappa_kappaInv

/-- The cone `odd ∪ 12ℤ` is mapped into the odds. -/
theorem kappa_cone (x : ℤ) (h : x % 2 = 1 ∨ x % 12 = 0) : kappa x % 2 = 1 := by
  unfold kappa; split_ifs <;> omega

/-- **Target.**  `κ` is in the anti-Kohl class at `p = 2`. -/
theorem kappa_antiKohl_class :
    ∃ a b c : ℤ → ℤ, IsRCWA kappa 6 a b c ∧ SlopeValOne 2 6 a c := by
  refine ⟨fun _ => 2,
    fun r => if r % 6 = 0 then 5 else if r % 6 = 1 then 7 else if r % 6 = 2 then 2
      else if r % 6 = 3 then -5 else if r % 6 = 4 then -8 else -1,
    fun r => if r % 6 = 0 then 1 else if r % 6 = 1 then 3 else if r % 6 = 2 then 3
      else if r % 6 = 3 then 1 else if r % 6 = 4 then 3 else 1, ?_, ?_⟩
  · refine ⟨by norm_num, ?_, ?_⟩
    · intro r
      dsimp
      split_ifs <;> omega
    · intro x
      dsimp
      unfold kappa
      split_ifs <;> omega
  · intro r hr0 hr6
    have h2 : padicValRat 2 (2 : ℚ) = 1 := padicValRat.self (by norm_num)
    have h3 : padicValRat 2 (3 : ℚ) = 0 := by
      change padicValRat 2 ((3 : ℕ) : ℚ) = 0
      rw [padicValRat.of_nat]
      rw [padicValNat.eq_zero_of_not_dvd (p := 2) (n := 3) (by norm_num)]
      norm_num
    have hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 := by omega
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      dsimp
      first
      | simpa using h2
      | rw [padicValRat.div (by norm_num) (by norm_num), h2, h3]
        norm_num

/-- **Target.**  Every orbit of `κ` has density `0`, so `κ` has infinitely many orbits and none
contains a class tail.  Paper proof: Theorem T with `S = odd ∪ 12ℤ`.
* Backward core: survival forces `y_j = κʲ x / 2 ∉ 3ℤ`, where `y ↦ (2y+1)/3` or `(2y−4)/3`, and
  each branch maps a class mod `2^a · 3` onto a class mod `2^(a+1)`, equidistributed mod `3`; so the
  density is exactly `(5/12)(2/3)ⁿ`.
* Forward core: on odds `x = 2y+1`, `κ` acts as `y ↦ (2y+3)/3, 2y−2, 2y` by `y mod 3`.  The image
  classes have `v₃(modulus) ≤ 1`, and their masses by type (3-free / `0, 1, 2 mod 3`) evolve
  linearly with spectral radius `0.9196…`, the root of `8λ³ − 4λ² − 2λ − 1`. -/
theorem kappa_orbit_densityZero (x : ℤ) : IntDensityZero (permOrbit kappaPerm x) := by
  sorry

/-! ## `σ_τ`: `U` followed by one class transposition -/

/-- The class transposition `2k+1 ↔ 4k+2`, fixing `4ℤ`. -/
def ctau (x : ℤ) : ℤ :=
  if x % 2 = 1 then 2 * x else if x % 4 = 2 then x / 2 else x

theorem ctau_ctau (x : ℤ) : ctau (ctau x) = x := by
  unfold ctau; split_ifs <;> omega

/-- `τ` as an involutive permutation. -/
def ctauPerm : Equiv.Perm ℤ where
  toFun := ctau
  invFun := ctau
  left_inv := ctau_ctau
  right_inv := ctau_ctau

/-- `σ_τ = τ ∘ U`. -/
def sigmaTauPerm : Equiv.Perm ℤ :=
  amusicalPerm.trans ctauPerm

/-- On the cone `2 + 4ℤ`, `σ_τ` is multiplication by `3`. -/
theorem sigmaTau_two_mod_four (x : ℤ) (h : x % 4 = 2) : sigmaTauPerm x = 3 * x := by
  show ctau (amusical x) = 3 * x
  unfold ctau amusical; split_ifs <;> omega

/-- The class `2 mod 4` is a forward-invariant cone for `σ_τ`. -/
theorem sigmaTau_cone (x : ℤ) (hx : x % 4 = 2) : sigmaTauPerm x % 4 = 2 := by
  rw [sigmaTau_two_mod_four x hx, Int.mul_emod, hx]
  norm_num

/-- Iterating `σ_τ` on its cone is simply multiplication by the corresponding power of `3`. -/
theorem sigmaTau_pow_two_mod_four (n : ℕ) (x : ℤ) (hx : x % 4 = 2) :
    (sigmaTauPerm ^ n) x = (3 : ℤ) ^ n * x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih]
      rw [sigmaTau_two_mod_four]
      · ring
      · have h3pow : (3 : ℤ) ^ n % 4 = 1 ∨ (3 : ℤ) ^ n % 4 = 3 := by
          clear ih
          induction n with
          | zero => simp
          | succ n hn =>
              rw [pow_succ, Int.mul_emod]
              rcases hn with hn | hn <;> omega
        rw [Int.mul_emod]
        rcases h3pow with h3pow | h3pow <;> rw [h3pow, hx] <;> norm_num

/-- The `n`th forward core of the `σ_τ` cone is the dilated residue class
`3^n · (2 + 4ℤ)`. -/
theorem sigmaTau_forward_core (n : ℕ) :
    ((sigmaTauPerm ^ n) '' {x : ℤ | x % 4 = 2}) =
      {y : ℤ | ∃ x : ℤ, x % 4 = 2 ∧ y = (3 : ℤ) ^ n * x} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, sigmaTau_pow_two_mod_four n x hx⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, sigmaTau_pow_two_mod_four n x hx⟩

/-- **Target.**  Every orbit of `σ_τ = τ ∘ U` has density `0`.  Paper proof: Theorem T with
`S = 2 + 4ℤ`.  The forward core is `3ⁿ (2 + 4ℤ)`, of density `3⁻ⁿ/4`.  The backward core
`{x : σ_τʲ x ∉ S, j ≤ n}` has density `(1/2)(3/4)ⁿ⁻¹`.  This comes from a closed 13-type
automaton on image classes typed by known `2`-adic digits and residue mod `3`, with
characteristic polynomial `λ¹²(4λ − 3)/4` (agent scripts `typeauto.py`, `typeauto2.py`). -/
theorem sigmaTau_orbit_densityZero (x : ℤ) : IntDensityZero (permOrbit sigmaTauPerm x) := by
  sorry

/-! ## One fixed prime is essential -/

/-- `h(6k+r) = 5k+r` (`r ∈ {0, 2, 4}`), `h(4k+r) = 5k+r` (`r ∈ {1, 3}`). -/
def hFive (x : ℤ) : ℤ :=
  if x % 2 = 0 then 5 * (x / 6) + x % 6 else 5 * (x / 4) + x % 4

/-- **Target.**  `hFive` is a bijection of `ℤ` (images: `5k + {0, 2, 4}` from evens, `5k + {1, 3}`
from odds). -/
theorem hFive_bijective : Function.Bijective hFive := by
  let g : ℤ → ℤ := fun y =>
    if y % 5 = 0 then 6 * (y / 5)
    else if y % 5 = 1 then 4 * (y / 5) + 1
    else if y % 5 = 2 then 6 * (y / 5) + 2
    else if y % 5 = 3 then 4 * (y / 5) + 3
    else 6 * (y / 5) + 4
  have hg_left : Function.LeftInverse g hFive := by
    intro x
    have hx :
        (x % 2 = 0 ∧ x % 6 = 0) ∨ (x % 2 = 0 ∧ x % 6 = 2) ∨
        (x % 2 = 0 ∧ x % 6 = 4) ∨ (x % 2 = 1 ∧ x % 4 = 1) ∨
        (x % 2 = 1 ∧ x % 4 = 3) := by omega
    rcases hx with hx | hx | hx | hx | hx
    all_goals
      dsimp [g]
      unfold hFive
      split_ifs <;> omega
  have hg_right : Function.RightInverse g hFive := by
    intro y
    have hy : y % 5 = 0 ∨ y % 5 = 1 ∨ y % 5 = 2 ∨ y % 5 = 3 ∨ y % 5 = 4 := by
      omega
    rcases hy with hy | hy | hy | hy | hy
    all_goals
      dsimp [g]
      unfold hFive
      split_ifs <;> omega
  exact ⟨hg_left.injective, hg_right.surjective⟩

set_option maxHeartbeats 1000000 in
/-- **Target.**  `h ∘ (· + 1) ∘ h⁻¹` has modulus `30` and only the slopes `3/2` and `2/3` (the
parity of `h⁻¹ y` flips under `+1`), so each slope has valuation `1` at `3` or at `2`; being
conjugate to a translation, it has a single orbit. -/
theorem mixedPrime_single_orbit :
    let σ := (Equiv.ofBijective hFive hFive_bijective).symm.trans
      ((Equiv.addRight (1 : ℤ)).trans (Equiv.ofBijective hFive hFive_bijective))
    (∃ a b c : ℤ → ℤ, IsRCWA σ 30 a b c ∧
      ∀ r, (a r : ℚ) / c r = 3 / 2 ∨ (a r : ℚ) / c r = 2 / 3) ∧
      ∀ x y : ℤ, ∃ n : ℤ, (σ ^ n) x = y := by
  let e : Equiv.Perm ℤ := Equiv.ofBijective hFive hFive_bijective
  let σ : Equiv.Perm ℤ := e.symm.trans ((Equiv.addRight (1 : ℤ)).trans e)
  change (∃ a b c : ℤ → ℤ, IsRCWA σ 30 a b c ∧
      ∀ r, (a r : ℚ) / c r = 3 / 2 ∨ (a r : ℚ) / c r = 2 / 3) ∧
    ∀ x y : ℤ, ∃ n : ℤ, (σ ^ n) x = y
  let g : ℤ → ℤ := fun y =>
    if y % 5 = 0 then 6 * (y / 5)
    else if y % 5 = 1 then 4 * (y / 5) + 1
    else if y % 5 = 2 then 6 * (y / 5) + 2
    else if y % 5 = 3 then 4 * (y / 5) + 3
    else 6 * (y / 5) + 4
  have hg_right : Function.RightInverse g hFive := by
    intro y
    have hlt : y % 5 < 5 := Int.emod_lt_of_pos y (by norm_num)
    have hnonneg : 0 ≤ y % 5 := Int.emod_nonneg y (by norm_num)
    interval_cases hy : y % 5 <;>
      dsimp [g] <;> unfold hFive <;> split_ifs <;> omega
  have he (y : ℤ) : e.symm y = g y := by
    apply hFive_bijective.1
    calc
      hFive (e.symm y) = y := e.apply_symm_apply y
      _ = hFive (g y) := (hg_right y).symm
  have hsigma (y : ℤ) : σ y = hFive (g y + 1) := by
    change hFive (e.symm y + 1) = hFive (g y + 1)
    rw [he]
  let a : ℤ → ℤ := fun r => if g r % 2 = 0 then 3 else 2
  let c : ℤ → ℤ := fun r => if g r % 2 = 0 then 2 else 3
  let b : ℤ → ℤ := fun r => c r * hFive (g r + 1) - a r * r
  constructor
  · refine ⟨a, b, c, ?_, ?_⟩
    · refine ⟨by norm_num, ?_, ?_⟩
      · intro r
        dsimp [a, c]
        split_ifs <;> omega
      · intro x
        rw [hsigma]
        have hlt : x % 30 < 30 := Int.emod_lt_of_pos x (by norm_num)
        have hnonneg : 0 ≤ x % 30 := Int.emod_nonneg x (by norm_num)
        interval_cases hx : x % 30 <;>
          dsimp [a, b, c, g] <;> unfold hFive <;> split_ifs <;> omega
    · intro r
      dsimp [a, c]
      split_ifs
      · left
        norm_num
      · right
        norm_num
  · intro x y
    have hcoord (z : ℤ) : e.symm (σ z) = e.symm z + 1 := by
      change e.symm (e (e.symm z + 1)) = e.symm z + 1
      exact e.symm_apply_apply (e.symm z + 1)
    have hinvcoord (z : ℤ) : e.symm (σ⁻¹ z) = e.symm z - 1 := by
      have hz := hcoord (σ⁻¹ z)
      have happ : σ (σ⁻¹ z) = z := by simp
      rw [happ] at hz
      omega
    have hpow : ∀ n : ℤ, ∀ z : ℤ, e.symm ((σ ^ n) z) = e.symm z + n := by
      intro n
      induction n using Int.induction_on with
      | zero => intro z; simp
      | succ n ih =>
          intro z
          rw [zpow_add_one, Equiv.Perm.mul_apply, ih, hcoord]
          omega
      | pred n ih =>
          intro z
          rw [zpow_sub_one, Equiv.Perm.mul_apply, ih, hinvcoord]
          omega
    refine ⟨e.symm y - e.symm x, ?_⟩
    apply e.symm.injective
    rw [hpow]
    omega

end CollatzMoonshot.Amusical
