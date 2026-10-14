/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Obstructions.Amusical
import CollatzMoonshot.AmusicalAntiKohl.Connect
import CollatzMoonshot.AmusicalAntiKohl.Periodic

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
`scripts/amusical/cone.py`.  Kernel-checked 2026-10-14 by the antikohl treadmill
(`HANDOFF-amusical-antikohl.md`).
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

/-- **Proved.**  `U` belongs to the anti-Kohl class at `p = 3`: modulus `4`, `a = 3`,
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

/-- **Proved.**  The anti-Kohl conjecture at `3` gives `U` a seventh orbit.  Paper proof: without a
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

/-- **Proved (the gate).**  `U` has no periodic cone: a union of residue classes mod `M` that `U`
maps into itself is empty or everything.  Paper proof: the residue graph of `U` mod `M` (edge
`r → s` when `U` maps some `x ≡ r` to `s`) is strongly connected (agent report `seventh.md`, T4);
a forward-closed class union is a union of strongly connected components with no exit. -/
theorem amusical_no_periodic_cone (M : ℕ) (hM : 0 < M) (R : Set (ZMod M))
    (h : ∀ n : ℤ, (n : ZMod M) ∈ R → ((amusical n : ℤ) : ZMod M) ∈ R) :
    R = ∅ ∨ R = Set.univ := by
  haveI : NeZero M := ⟨hM.ne'⟩
  by_cases hR : R = ∅
  · exact Or.inl hR
  right
  obtain ⟨r, hr⟩ := Set.nonempty_iff_ne_empty.mpr hR
  have hiter : ∀ (t : ℕ) (n : ℤ), (n : ZMod M) ∈ R →
      ((amusical^[t] n : ℤ) : ZMod M) ∈ R := by
    intro t
    induction t with
    | zero => intro n hn; simpa using hn
    | succ t ih =>
        intro n hn
        rw [Function.iterate_succ_apply']
        exact h _ (ih n hn)
  rw [Set.eq_univ_iff_forall]
  intro s
  obtain ⟨x, L, hx, hL⟩ :=
    AntiKohlConnect.amusical_reach M hM ((r.val : ℕ) : ℤ) ((s.val : ℕ) : ℤ)
  have hxr : (x : ZMod M) = r := by
    rw [(ZMod.intCast_eq_intCast_iff _ _ _).mpr hx]
    simp
  have hLs : ((amusical^[L] x : ℤ) : ZMod M) = s := by
    rw [(ZMod.intCast_eq_intCast_iff _ _ _).mpr hL]
    simp
  rw [← hLs]
  exact hiter L x (hxr ▸ hr)

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

/-- **Proved (Theorem T).**  A cone `S` (`σ S ⊆ S`) whose forward cores `σⁿ S` and never-entering
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

/-- **Proved.**  Under Theorem T's hypotheses `σ` has infinitely many orbits and none contains a
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

open Classical in
/-- A set covered by a periodic predicate with few residues has small upper density. -/
theorem intDensityLE_of_isPer {Q : ℕ} (hQ : 0 < Q) {P : ℤ → Prop}
    (hP : AntiKohlPeriodic.IsPer Q P) (A : Set ℤ) (hA : ∀ x ∈ A, P x) (ε : ℝ)
    (hε : 3 * (AntiKohlPeriodic.resCount Q P : ℝ) < ε * Q) : IntDensityLE A ε := by
  unfold IntDensityLE
  filter_upwards [Filter.eventually_ge_atTop (2 * Q)] with X hX
  set c := AntiKohlPeriodic.resCount Q P
  have hsub : ((Finset.Icc (-(X : ℤ)) X).filter (· ∈ A)).card ≤
      ((Finset.Icc (-(X : ℤ)) X).filter P).card := by
    apply Finset.card_le_card
    intro y hy
    simp only [Finset.mem_filter] at hy ⊢
    exact ⟨hy.1, hA y hy.2⟩
  have hbox := AntiKohlPeriodic.box_count_le hQ hP X
  have hcnt : (((Finset.Icc (-(X : ℤ)) X).filter (· ∈ A)).card : ℝ) ≤
      c * (2 * ((X / Q : ℕ) : ℝ) + 2) := by
    exact_mod_cast hsub.trans hbox
  have hdiv : ((X / Q : ℕ) : ℝ) * Q ≤ X := by exact_mod_cast Nat.div_mul_le_self X Q
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hXr : 2 * (Q : ℝ) ≤ X := by exact_mod_cast hX
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg _
  have k1 := mul_le_mul_of_nonneg_left hdiv (by positivity : (0 : ℝ) ≤ 2 * c)
  have k2 := mul_le_mul_of_nonneg_left hXr hc0
  have k3 := mul_le_mul_of_nonneg_right hε.le hX0
  have key : (c * (2 * ((X / Q : ℕ) : ℝ) + 2)) * Q ≤ (ε * X) * Q := by
    nlinarith
  exact hcnt.trans (le_of_mul_le_mul_right key hQr)

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

/-- **Proved.**  `κ` is in the anti-Kohl class at `p = 2`. -/
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

/-- One step of an `n`-step never-entering condition, for any permutation and cone. -/
theorem perm_surv_succ (σ : Equiv.Perm ℤ) (S : Set ℤ) {n : ℕ} {x : ℤ}
    (h : ∀ j ≤ n + 1, (σ ^ j) x ∉ S) :
    x ∉ S ∧ σ x ∉ S ∧ ∀ j ≤ n, (σ ^ j) (σ x) ∉ S := by
  refine ⟨by simpa using h 0 (by omega), by simpa using h 1 (by omega), ?_⟩
  intro j hj
  have hj' := h (j + 1) (by omega)
  rwa [pow_succ, Equiv.Perm.mul_apply] at hj'

theorem kappaPerm_apply (x : ℤ) : kappaPerm x = kappa x := rfl

open AntiKohlPeriodic in
/-- **The `κ` backward automaton.**  Writing a never-entering point as `2y`, survival forces
`y ∉ 3ℤ` and continues through `2y' = κ(2y)` with `y' = 2⌊y/3⌋ + 1` (`y ≡ 1`) or `2⌊y/3⌋`
(`y ≡ 2`).  So the `n`-step survivors are covered by a predicate of period `3ⁿ` with at most
`2ⁿ` residues. -/
theorem kappa_survivor_cover (n : ℕ) :
    ∃ D : ℤ → Prop, IsPer (3 ^ n) D ∧ resCount (3 ^ n) D ≤ 2 ^ n ∧
      ∀ y, (∀ j ≤ n, (kappaPerm ^ j) (2 * y) ∉ {x : ℤ | x % 2 = 1 ∨ x % 12 = 0}) → D y := by
  induction n with
  | zero =>
      refine ⟨fun _ => True, fun _ => Iff.rfl, ?_, fun _ _ => trivial⟩
      simp [resCount]
  | succ n ih =>
      obtain ⟨D, hD, hcnt, hDs⟩ := ih
      have hQ : 0 < 3 ^ n := by positivity
      have h2 : IsCoprime (2 : ℤ) ((3 ^ n : ℕ) : ℤ) := by
        push_cast
        exact IsCoprime.pow_right ⟨-1, 1, by norm_num⟩
      have h3 : 0 < 3 := by norm_num
      let D' : ℤ → Prop := fun y =>
        (y % ((3 : ℕ) : ℤ) = 1 ∧ D (2 * (y / ((3 : ℕ) : ℤ)) + 1)) ∨
          (y % ((3 : ℕ) : ℤ) = 2 ∧ D (2 * (y / ((3 : ℕ) : ℤ)) + 0))
      have hsplit : 3 ^ (n + 1) = 3 * 3 ^ n := by ring
      refine ⟨D', ?_, ?_, ?_⟩
      · rw [hsplit]
        exact (hD.pull h3 1 2 1).or (hD.pull h3 2 2 0)
      · rw [hsplit]
        have e1 := resCount_pull_le hQ hD h3 1 2 1 h2
        have e2 := resCount_pull_le hQ hD h3 2 2 0 h2
        refine resCount_or_le.trans ?_
        rw [pow_succ]
        omega
      · intro y hy
        obtain ⟨h0, h1, hnext⟩ := perm_surv_succ kappaPerm _ hy
        simp only [Set.mem_ofPred_eq, kappaPerm_apply] at h0 h1
        have hy3 : y % 3 = 0 ∨ y % 3 = 1 ∨ y % 3 = 2 := by omega
        rcases hy3 with hy3 | hy3 | hy3
        · exfalso
          apply h1
          unfold kappa
          split_ifs <;> omega
        · have hκ : kappaPerm (2 * y) = 2 * (2 * (y / 3) + 1) := by
            rw [kappaPerm_apply]; unfold kappa; split_ifs <;> omega
          left
          refine ⟨by simpa using hy3, ?_⟩
          have := hDs _ (hκ ▸ hnext)
          simpa using this
        · have hκ : kappaPerm (2 * y) = 2 * (2 * (y / 3) + 0) := by
            rw [kappaPerm_apply]; unfold kappa; split_ifs <;> omega
          right
          refine ⟨by simpa using hy3, ?_⟩
          have := hDs _ (hκ ▸ hnext)
          simpa using this

/-- The never-entering sets of the `κ` cone have density tending to zero. -/
theorem kappa_backward_density (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, IntDensityLE
      {x | ∀ j ≤ n, (kappaPerm ^ j) x ∉ {x : ℤ | x % 2 = 1 ∨ x % 12 = 0}} ε := by
  have hlim : Filter.Tendsto (fun n : ℕ => ((2 : ℝ) / 3) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 3))).exists
  obtain ⟨D, hD, hcnt, hDs⟩ := kappa_survivor_cover n
  have hQ : 0 < 3 ^ n := by positivity
  let P : ℤ → Prop := fun x => x % ((2 : ℕ) : ℤ) = 0 ∧ D (1 * (x / ((2 : ℕ) : ℤ)) + 0)
  have hP : AntiKohlPeriodic.IsPer (2 * 3 ^ n) P := hD.pull (by norm_num : 0 < 2) 0 1 0
  have hPcnt : AntiKohlPeriodic.resCount (2 * 3 ^ n) P ≤ 2 ^ n :=
    (AntiKohlPeriodic.resCount_pull_le hQ hD (by norm_num : 0 < 2) 0 1 0
      isCoprime_one_left).trans hcnt
  refine ⟨n, intDensityLE_of_isPer (by positivity) hP _ ?_ ε ?_⟩
  · intro x hx
    have hx' : ∀ j ≤ n, (kappaPerm ^ j) x ∉ {x : ℤ | x % 2 = 1 ∨ x % 12 = 0} := hx
    have hx0 : ¬ (x % 2 = 1 ∨ x % 12 = 0) := by simpa using hx' 0 (by omega)
    refine ⟨by simp; omega, ?_⟩
    have hxe : x = 2 * (x / 2) := by omega
    have := hDs (x / 2) (by rw [← hxe]; exact hx')
    simpa using this
  · have hcast : (AntiKohlPeriodic.resCount (2 * 3 ^ n) P : ℝ) ≤ 2 ^ n := by
      exact_mod_cast hPcnt
    rw [div_pow, div_lt_iff₀ (by positivity)] at hn
    push_cast
    nlinarith

/-- `κ` on odd numbers, in the coordinate `x = 2y + 1`. -/
def kappaT (y : ℤ) : ℤ :=
  if y % 3 = 0 then 2 * (y / 3) + 1 else if y % 3 = 1 then 6 * (y / 3) else 6 * (y / 3) + 4

theorem kappa_two_mul_add_one (y : ℤ) : kappa (2 * y + 1) = 2 * kappaT y + 1 := by
  unfold kappa kappaT; split_ifs <;> omega

theorem kappaPerm_pow_odd (n : ℕ) (y : ℤ) :
    (kappaPerm ^ n) (2 * y + 1) = 2 * kappaT^[n] y + 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih, kappaPerm_apply, kappa_two_mul_add_one,
        Function.iterate_succ_apply']

/-- The forward cover `F ∪ 3Z ∪ (3O + 1)` of the `κ` forward core, in odd coordinates. -/
def kCover (F Z O : ℤ → Prop) (v : ℤ) : Prop :=
  F v ∨ (v % ((3 : ℕ) : ℤ) = 0 ∧ Z (1 * (v / ((3 : ℕ) : ℤ)) + 0)) ∨
    (v % ((3 : ℕ) : ℤ) = 1 ∧ O (1 * (v / ((3 : ℕ) : ℤ)) + 0))

/-- The free part after one step: `2(F/3) + 1 ∪ 2Z + 1`. -/
def kStepF (F Z : ℤ → Prop) (y : ℤ) : Prop :=
  (y % ((2 : ℕ) : ℤ) = 1 ∧ F (3 * (y / ((2 : ℕ) : ℤ)) + 0)) ∨
    (y % ((2 : ℕ) : ℤ) = 1 ∧ Z (1 * (y / ((2 : ℕ) : ℤ)) + 0))

/-- The `3ℤ` part after one step: `2((F − 1)/3) ∪ 2O`. -/
def kStepZ (F O : ℤ → Prop) (y : ℤ) : Prop :=
  (y % ((2 : ℕ) : ℤ) = 0 ∧ F (3 * (y / ((2 : ℕ) : ℤ)) + 1)) ∨
    (y % ((2 : ℕ) : ℤ) = 0 ∧ O (1 * (y / ((2 : ℕ) : ℤ)) + 0))

/-- The `3ℤ + 1` part after one step: `2((F − 2)/3) + 1`. -/
def kStepO (F : ℤ → Prop) (y : ℤ) : Prop :=
  y % ((2 : ℕ) : ℤ) = 1 ∧ F (3 * (y / ((2 : ℕ) : ℤ)) + 2)

theorem kCover_step {F Z O : ℤ → Prop} {v : ℤ} (h : kCover F Z O v) :
    kCover (kStepF F Z) (kStepZ F O) (kStepO F) (kappaT v) := by
  have key : ∀ {P : ℤ → Prop} {a b : ℤ}, a = b → P b → P a := fun h hb => h ▸ hb
  unfold kCover kStepF kStepZ kStepO
  simp only [Nat.cast_ofNat, one_mul, add_zero] at h ⊢
  have hv3 : v % 3 = 0 ∨ v % 3 = 1 ∨ v % 3 = 2 := by omega
  rcases h with hF | ⟨hv, hZ⟩ | ⟨hv, hO⟩
  · rcases hv3 with hv3 | hv3 | hv3
    · have hT : kappaT v = 2 * (v / 3) + 1 := by unfold kappaT; split_ifs <;> omega
      rw [hT]
      exact Or.inl (Or.inl ⟨by omega, key (by omega) hF⟩)
    · have hT : kappaT v = 6 * (v / 3) := by unfold kappaT; split_ifs <;> omega
      rw [hT]
      exact Or.inr (Or.inl ⟨by omega, Or.inl ⟨by omega, key (by omega) hF⟩⟩)
    · have hT : kappaT v = 6 * (v / 3) + 4 := by unfold kappaT; split_ifs <;> omega
      rw [hT]
      exact Or.inr (Or.inr ⟨by omega, by omega, key (by omega) hF⟩)
  · have hT : kappaT v = 2 * (v / 3) + 1 := by unfold kappaT; split_ifs <;> omega
    rw [hT]
    exact Or.inl (Or.inr ⟨by omega, key (by omega) hZ⟩)
  · have hT : kappaT v = 6 * (v / 3) := by unfold kappaT; split_ifs <;> omega
    rw [hT]
    exact Or.inr (Or.inl ⟨by omega, Or.inr ⟨by omega, key (by omega) hO⟩⟩)

open AntiKohlPeriodic in
/-- **The `κ` forward automaton.**  `kappaTⁿ ℤ` is covered by `F ∪ 3Z ∪ (3O + 1)` with `F, Z, O`
of period `2ⁿ` and residue counts `f, z, o`; the counts evolve by
`(f, z, o) ↦ (f + z, f + o, f)`, and the weights `(18, 10, 6)` grow by at most `17/9` per step
while the period doubles. -/
theorem kappa_forward_cover (n : ℕ) :
    ∃ F Z O : ℤ → Prop, IsPer (2 ^ n) F ∧ IsPer (2 ^ n) Z ∧ IsPer (2 ^ n) O ∧
      9 ^ n * (18 * resCount (2 ^ n) F + 10 * resCount (2 ^ n) Z + 6 * resCount (2 ^ n) O) ≤
        18 * 17 ^ n ∧
      ∀ y, kCover F Z O (kappaT^[n] y) := by
  induction n with
  | zero =>
      refine ⟨fun _ => True, fun _ => False, fun _ => False, fun _ => Iff.rfl,
        fun _ => Iff.rfl, fun _ => Iff.rfl, ?_, fun y => Or.inl trivial⟩
      simp [resCount]
  | succ n ih =>
      obtain ⟨F, Z, O, hF, hZ, hO, hcnt, hcov⟩ := ih
      have hQ : 0 < 2 ^ n := by positivity
      have h3 : IsCoprime (3 : ℤ) ((2 ^ n : ℕ) : ℤ) := by
        push_cast
        exact IsCoprime.pow_right ⟨1, -1, by norm_num⟩
      have h1 : IsCoprime (1 : ℤ) ((2 ^ n : ℕ) : ℤ) := isCoprime_one_left
      have h2 : 0 < 2 := by norm_num
      have hsplit : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
      refine ⟨kStepF F Z, kStepZ F O, kStepO F, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hsplit]; exact (hF.pull h2 1 3 0).or (hZ.pull h2 1 1 0)
      · rw [hsplit]; exact (hF.pull h2 0 3 1).or (hO.pull h2 0 1 0)
      · rw [hsplit]; exact hF.pull h2 1 3 2
      · rw [hsplit]
        have eF : resCount (2 * 2 ^ n) (kStepF F Z) ≤
            resCount (2 ^ n) F + resCount (2 ^ n) Z :=
          resCount_or_le.trans (add_le_add (resCount_pull_le hQ hF h2 1 3 0 h3)
            (resCount_pull_le hQ hZ h2 1 1 0 h1))
        have eZ : resCount (2 * 2 ^ n) (kStepZ F O) ≤
            resCount (2 ^ n) F + resCount (2 ^ n) O :=
          resCount_or_le.trans (add_le_add (resCount_pull_le hQ hF h2 0 3 1 h3)
            (resCount_pull_le hQ hO h2 0 1 0 h1))
        have eO : resCount (2 * 2 ^ n) (kStepO F) ≤ resCount (2 ^ n) F :=
          resCount_pull_le hQ hF h2 1 3 2 h3
        set f := resCount (2 ^ n) F
        set z := resCount (2 ^ n) Z
        set o := resCount (2 ^ n) O
        have hw : 9 * (18 * resCount (2 * 2 ^ n) (kStepF F Z) +
            10 * resCount (2 * 2 ^ n) (kStepZ F O) + 6 * resCount (2 * 2 ^ n) (kStepO F)) ≤
            17 * (18 * f + 10 * z + 6 * o) := by omega
        calc 9 ^ (n + 1) * (18 * resCount (2 * 2 ^ n) (kStepF F Z) +
              10 * resCount (2 * 2 ^ n) (kStepZ F O) + 6 * resCount (2 * 2 ^ n) (kStepO F))
            = 9 ^ n * (9 * (18 * resCount (2 * 2 ^ n) (kStepF F Z) +
              10 * resCount (2 * 2 ^ n) (kStepZ F O) +
                6 * resCount (2 * 2 ^ n) (kStepO F))) := by ring
          _ ≤ 9 ^ n * (17 * (18 * f + 10 * z + 6 * o)) := Nat.mul_le_mul_left _ hw
          _ = 17 * (9 ^ n * (18 * f + 10 * z + 6 * o)) := by ring
          _ ≤ 17 * (18 * 17 ^ n) := Nat.mul_le_mul_left _ hcnt
          _ = 18 * 17 ^ (n + 1) := by ring
      · intro y
        rw [Function.iterate_succ_apply']
        exact kCover_step (hcov y)

/-- The forward cores of the `κ` cone have density tending to zero. -/
theorem kappa_forward_density (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, IntDensityLE ((kappaPerm ^ n) '' {x : ℤ | x % 2 = 1 ∨ x % 12 = 0}) ε := by
  have hlim : Filter.Tendsto (fun n : ℕ => ((17 : ℝ) / 18) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 2))).exists
  obtain ⟨F, Z, O, hF, hZ, hO, hcnt, hcov⟩ := kappa_forward_cover n
  have hQ : 0 < 2 ^ n := by positivity
  have h3 : 0 < 3 := by norm_num
  have hCper : AntiKohlPeriodic.IsPer (3 * 2 ^ n) (kCover F Z O) :=
    (hF.mul 3).or ((hZ.pull h3 0 1 0).or (hO.pull h3 1 1 0))
  have hCcnt : AntiKohlPeriodic.resCount (3 * 2 ^ n) (kCover F Z O) ≤
      3 * AntiKohlPeriodic.resCount (2 ^ n) F + AntiKohlPeriodic.resCount (2 ^ n) Z +
        AntiKohlPeriodic.resCount (2 ^ n) O := by
    have e1 := AntiKohlPeriodic.resCount_mul_le hQ hF 3
    have e2 := AntiKohlPeriodic.resCount_pull_le hQ hZ h3 0 1 0 isCoprime_one_left
    have e3 := AntiKohlPeriodic.resCount_pull_le hQ hO h3 1 1 0 isCoprime_one_left
    unfold kCover
    refine AntiKohlPeriodic.resCount_or_le.trans ?_
    refine (add_le_add le_rfl AntiKohlPeriodic.resCount_or_le).trans ?_
    omega
  have hC3 : 0 < 3 * 2 ^ n := by positivity
  let P : ℤ → Prop := fun x => x % ((2 : ℕ) : ℤ) = 1 ∧ kCover F Z O (1 * (x / ((2 : ℕ) : ℤ)) + 0)
  have hP : AntiKohlPeriodic.IsPer (2 * (3 * 2 ^ n)) P := hCper.pull (by norm_num) 1 1 0
  have hPcnt : AntiKohlPeriodic.resCount (2 * (3 * 2 ^ n)) P ≤
      AntiKohlPeriodic.resCount (3 * 2 ^ n) (kCover F Z O) :=
    AntiKohlPeriodic.resCount_pull_le hC3 hCper (by norm_num) 1 1 0 isCoprime_one_left
  refine ⟨n + 1, intDensityLE_of_isPer (by positivity) hP _ ?_ ε ?_⟩
  · rintro x ⟨x0, hx0, rfl⟩
    have hodd : kappa x0 % 2 = 1 := kappa_cone x0 hx0
    have hxe : kappaPerm x0 = 2 * (kappa x0 / 2) + 1 := by rw [kappaPerm_apply]; omega
    rw [pow_succ, Equiv.Perm.mul_apply, hxe, kappaPerm_pow_odd]
    refine ⟨by simp, ?_⟩
    have := hcov (kappa x0 / 2)
    have he : 1 * ((2 * kappaT^[n] (kappa x0 / 2) + 1) / ((2 : ℕ) : ℤ)) + 0 =
        kappaT^[n] (kappa x0 / 2) := by simp; omega
    rw [he]
    exact this
  · have hc : (AntiKohlPeriodic.resCount (2 * (3 * 2 ^ n)) P : ℝ) ≤
        3 * AntiKohlPeriodic.resCount (2 ^ n) F + AntiKohlPeriodic.resCount (2 ^ n) Z +
          AntiKohlPeriodic.resCount (2 ^ n) O := by
      exact_mod_cast hPcnt.trans hCcnt
    have hw : (9 : ℝ) ^ n * (18 * (AntiKohlPeriodic.resCount (2 ^ n) F : ℝ) +
        10 * AntiKohlPeriodic.resCount (2 ^ n) Z + 6 * AntiKohlPeriodic.resCount (2 ^ n) O) ≤
        18 * 17 ^ n := by exact_mod_cast hcnt
    set f : ℝ := (AntiKohlPeriodic.resCount (2 ^ n) F : ℝ)
    set z : ℝ := (AntiKohlPeriodic.resCount (2 ^ n) Z : ℝ)
    set o : ℝ := (AntiKohlPeriodic.resCount (2 ^ n) O : ℝ)
    have hf : 0 ≤ f := Nat.cast_nonneg _
    have hz : 0 ≤ z := Nat.cast_nonneg _
    have ho : 0 ≤ o := Nat.cast_nonneg _
    have h9 : (0 : ℝ) < 9 ^ n := by positivity
    have hpow : ((17 : ℝ) / 18) ^ n * (18 ^ n) = 17 ^ n := by
      rw [div_pow]; field_simp
    have h18 : (18 : ℝ) ^ n = 9 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
    -- 3 c ≤ (18f + 10z + 6o) / 2 ≤ 9 (17/9)^n < (ε/2) · 18 · 2^n ... compare in the period
    have hmain : 3 * (3 * f + z + o) * 9 ^ n < ε * (2 * (3 * 2 ^ n)) * 9 ^ n := by
      have hn' : (17 : ℝ) ^ n < ε / 2 * 18 ^ n := by
        rw [← hpow]
        exact mul_lt_mul_of_pos_right hn (by positivity)
      rw [h18] at hn'
      nlinarith
    have hlt := lt_of_mul_lt_mul_right hmain h9.le
    push_cast
    linarith

/-- **Proved.**  Every orbit of `κ` has density `0`, so `κ` has infinitely many orbits and none
contains a class tail.  Paper proof: Theorem T with `S = odd ∪ 12ℤ`.
* Backward core: survival forces `y_j = κʲ x / 2 ∉ 3ℤ`, where `y ↦ (2y+1)/3` or `(2y−4)/3`, and
  each branch maps a class mod `2^a · 3` onto a class mod `2^(a+1)`, equidistributed mod `3`; so the
  density is exactly `(5/12)(2/3)ⁿ`.
* Forward core: on odds `x = 2y+1`, `κ` acts as `y ↦ (2y+3)/3, 2y−2, 2y` by `y mod 3`.  The image
  classes have `v₃(modulus) ≤ 1`, and their masses by type (3-free / `0, 1, 2 mod 3`) evolve
  linearly with spectral radius `0.9196…`, the root of `8λ³ − 4λ² − 2λ − 1`. -/
theorem kappa_orbit_densityZero (x : ℤ) : IntDensityZero (permOrbit kappaPerm x) := by
  have hS : ∀ x ∈ {x : ℤ | x % 2 = 1 ∨ x % 12 = 0},
      kappaPerm x ∈ {x : ℤ | x % 2 = 1 ∨ x % 12 = 0} :=
    fun x hx => Or.inl (kappa_cone x hx)
  simpa using orbit_densityZero_of_transientCone kappaPerm _ hS kappa_forward_density
    kappa_backward_density ({x} : Finset ℤ)

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

open Classical in
/-- A positive integral dilation has eventually arbitrarily small symmetric-box density. -/
theorem intDensityLE_dilate (q : ℕ) (hq : 0 < q) (A : Set ℤ) (ε : ℝ)
    (hqε : 3 / (q : ℝ) < ε) :
    IntDensityLE {y : ℤ | ∃ x ∈ A, y = (q : ℤ) * x} ε := by
  unfold IntDensityLE
  filter_upwards [Filter.eventually_ge_atTop (2 * q)] with X hX
  let B := (Finset.Icc (-(X : ℤ)) X).filter
    (· ∈ {y : ℤ | ∃ x ∈ A, y = (q : ℤ) * x})
  let f : ℤ → ℤ := fun y => y / q
  have hf_inj : Set.InjOn f B := by
    intro y hy z hz heq
    change y ∈ B at hy
    change z ∈ B at hz
    simp only [B, Finset.mem_filter, Finset.mem_Icc] at hy hz
    obtain ⟨xy, _, hxy⟩ := hy.2
    obtain ⟨xz, _, hxz⟩ := hz.2
    have hydiv : y / (q : ℤ) = xy := by
      apply Int.ediv_eq_of_eq_mul_left (by omega)
      simpa [mul_comm] using hxy
    have hzdiv : z / (q : ℤ) = xz := by
      apply Int.ediv_eq_of_eq_mul_left (by omega)
      simpa [mul_comm] using hxz
    dsimp [f] at heq
    rw [hydiv, hzdiv] at heq
    subst xz
    exact hxy.trans hxz.symm
  have hf_mem : ∀ y ∈ B, f y ∈ Finset.Icc (-(X / q : ℕ) - 1 : ℤ) (X / q : ℕ) := by
    intro y hy
    simp only [B, Finset.mem_filter, Finset.mem_Icc] at hy ⊢
    obtain ⟨xy, _, hxy⟩ := hy.2
    have hqz : (0 : ℤ) < q := by exact_mod_cast hq
    have hydiv : y / (q : ℤ) = xy := by
      apply Int.ediv_eq_of_eq_mul_left (by omega)
      simpa [mul_comm] using hxy
    have hupper : xy ≤ (X : ℤ) / q := by
      rw [Int.le_ediv_iff_mul_le hqz]
      simpa [mul_comm, hxy] using hy.1.2
    have hlower : -(X : ℤ) / q ≤ xy := by
      rw [Int.ediv_le_iff_le_mul hqz]
      rw [mul_comm xy, ← hxy]
      omega
    have hmod : X % q + q * (X / q) = X := Nat.mod_add_div X q
    have hfloorlower : (-(X / q : ℕ) - 1 : ℤ) ≤ -(X : ℤ) / q := by
      rw [Int.le_ediv_iff_mul_le hqz]
      have hbound : X ≤ q * (X / q + 1) := by
        calc
          X = X % q + q * (X / q) := hmod.symm
          _ ≤ q + q * (X / q) := Nat.add_le_add_right (Nat.mod_lt X hq).le _
          _ = q * (X / q + 1) := by ring
      have hbound' : (X : ℤ) ≤ (q : ℤ) * (((X / q : ℕ) : ℤ) + 1) := by
        exact_mod_cast hbound
      calc
        (-(X / q : ℕ) - 1 : ℤ) * q =
            -((q : ℤ) * (((X / q : ℕ) : ℤ) + 1)) := by ring
        _ ≤ -(X : ℤ) := neg_le_neg hbound'
    change (-(X / q : ℕ) - 1 : ℤ) ≤ y / q ∧ y / q ≤ (X / q : ℕ)
    constructor <;> rw [hydiv]
    · exact hfloorlower.trans hlower
    · simpa using hupper
  have hcard : B.card ≤ (Finset.Icc (-(X / q : ℕ) - 1 : ℤ) (X / q : ℕ)).card := by
    exact Finset.card_le_card_of_injOn f hf_mem hf_inj
  rw [Int.card_Icc] at hcard
  have hcard' : B.card ≤ 2 * (X / q) + 2 := by
    have heqcard : (((X / q : ℕ) : ℤ) + 1 - (-(X / q : ℕ) - 1 : ℤ)).toNat =
        2 * (X / q) + 2 := by omega
    rw [heqcard] at hcard
    exact hcard
  change (B.card : ℝ) ≤ ε * X
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
  have hXreal : (2 : ℝ) * q ≤ X := by exact_mod_cast hX
  have hXposreal : (0 : ℝ) < X := lt_of_lt_of_le (mul_pos (by norm_num) hqreal) hXreal
  have hdivreal : (X / q : ℕ) ≤ (X : ℝ) / q := by
    rw [le_div_iff₀ hqreal]
    exact_mod_cast Nat.div_mul_le_self X q
  have hcardreal : (B.card : ℝ) ≤ 2 * (X / q : ℕ) + 2 := by exact_mod_cast hcard'
  calc
    (B.card : ℝ) ≤ 2 * (X / q : ℕ) + 2 := hcardreal
    _ ≤ 2 * ((X : ℝ) / q) + 2 := by linarith
    _ ≤ 3 * ((X : ℝ) / q) := by
      have : (2 : ℝ) ≤ (X : ℝ) / q := (le_div_iff₀ hqreal).2 (by simpa using hXreal)
      linarith
    _ ≤ ε * X := by
      apply le_of_lt
      calc
        3 * ((X : ℝ) / q) = (3 / q) * X := by ring
        _ < ε * X := mul_lt_mul_of_pos_right hqε hXposreal

/-- The forward cores of the `σ_τ` cone have density tending to zero. -/
theorem sigmaTau_forward_density (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, IntDensityLE ((sigmaTauPerm ^ n) '' {x : ℤ | x % 4 = 2}) ε := by
  have hgrow : Filter.Tendsto (fun n : ℕ => (3 : ℝ) ^ n) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hevent := hgrow.eventually_gt_atTop (3 / ε)
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨n, hn⟩ := hevent
  have hratio : 3 / ((3 : ℝ) ^ n) < ε := by
    rw [div_lt_iff₀ (by positivity)]
    have := (div_lt_iff₀ hε).mp (hn n le_rfl)
    nlinarith
  refine ⟨n, ?_⟩
  rw [sigmaTau_forward_core]
  simpa using intDensityLE_dilate (3 ^ n) (by positivity)
    {x : ℤ | x % 4 = 2} ε (by simpa using hratio)

theorem sigmaTau_apply (x : ℤ) : sigmaTauPerm x = ctau (amusical x) := rfl

/-- One step of the `n`-step never-entering condition. -/
theorem sigmaTau_surv_succ {n : ℕ} {x : ℤ}
    (h : ∀ j ≤ n + 1, (sigmaTauPerm ^ j) x % 4 ≠ 2) :
    x % 4 ≠ 2 ∧ sigmaTauPerm x % 4 ≠ 2 ∧
      ∀ j ≤ n, (sigmaTauPerm ^ j) (sigmaTauPerm x) % 4 ≠ 2 := by
  refine ⟨by simpa using h 0 (by omega), by simpa using h 1 (by omega), ?_⟩
  intro j hj
  have hj' := h (j + 1) (by omega)
  rwa [pow_succ, Equiv.Perm.mul_apply] at hj'

open AntiKohlPeriodic in
/-- **The `σ_τ` backward automaton.**  The survivors of `n` steps among `4s` and among `2s + 1`
are covered by predicates of period `8ⁿ` in `s` with at most `2 · 6ⁿ` residues in total:
`4s` survives through `4·3t` (`s = 2t`) or `2(3t+1)+1` (`s = 2t+1`), while `2s+1` survives only
for `s ≡ 1, 2, 5, 6 (mod 8)`, through one of `2·3w+1, 4(3w+1), 4(3w+2), 2(3w+2)+1`. -/
theorem sigmaTau_survivor_cover (n : ℕ) :
    ∃ A B : ℤ → Prop, IsPer (8 ^ n) A ∧ IsPer (8 ^ n) B ∧
      resCount (8 ^ n) A + resCount (8 ^ n) B ≤ 2 * 6 ^ n ∧
      (∀ s, (∀ j ≤ n, (sigmaTauPerm ^ j) (4 * s) % 4 ≠ 2) → A s) ∧
      (∀ s, (∀ j ≤ n, (sigmaTauPerm ^ j) (2 * s + 1) % 4 ≠ 2) → B s) := by
  induction n with
  | zero =>
      refine ⟨fun _ => True, fun _ => True, fun _ => Iff.rfl, fun _ => Iff.rfl, ?_,
        fun _ _ => trivial, fun _ _ => trivial⟩
      simp [resCount]
  | succ n ih =>
      obtain ⟨A, B, hA, hB, hcnt, hAs, hBs⟩ := ih
      have hQ : 0 < 8 ^ n := by positivity
      have h3 : IsCoprime (3 : ℤ) ((8 ^ n : ℕ) : ℤ) := by
        push_cast
        exact IsCoprime.pow_right ⟨3, -1, by norm_num⟩
      have h2 : 0 < 2 := by norm_num
      have h8 : 0 < 8 := by norm_num
      let A' : ℤ → Prop := fun s =>
        (s % ((2 : ℕ) : ℤ) = 0 ∧ A (3 * (s / ((2 : ℕ) : ℤ)) + 0)) ∨
          (s % ((2 : ℕ) : ℤ) = 1 ∧ B (3 * (s / ((2 : ℕ) : ℤ)) + 1))
      let B' : ℤ → Prop := fun s =>
        ((s % ((8 : ℕ) : ℤ) = 6 ∧ B (3 * (s / ((8 : ℕ) : ℤ)) + 2)) ∨
          (s % ((8 : ℕ) : ℤ) = 2 ∧ A (3 * (s / ((8 : ℕ) : ℤ)) + 1))) ∨
        ((s % ((8 : ℕ) : ℤ) = 1 ∧ B (3 * (s / ((8 : ℕ) : ℤ)) + 0)) ∨
          (s % ((8 : ℕ) : ℤ) = 5 ∧ A (3 * (s / ((8 : ℕ) : ℤ)) + 2)))
      have hA'per : IsPer (2 * 8 ^ n) A' := (hA.pull h2 0 3 0).or (hB.pull h2 1 3 1)
      have hA'cnt : resCount (2 * 8 ^ n) A' ≤ resCount (8 ^ n) A + resCount (8 ^ n) B :=
        resCount_or_le.trans (add_le_add (resCount_pull_le hQ hA h2 0 3 0 h3)
          (resCount_pull_le hQ hB h2 1 3 1 h3))
      have hB'per : IsPer (8 * 8 ^ n) B' :=
        ((hB.pull h8 6 3 2).or (hA.pull h8 2 3 1)).or ((hB.pull h8 1 3 0).or (hA.pull h8 5 3 2))
      have hB'cnt : resCount (8 * 8 ^ n) B' ≤
          2 * (resCount (8 ^ n) A + resCount (8 ^ n) B) := by
        have e1 := resCount_pull_le hQ hB h8 6 3 2 h3
        have e2 := resCount_pull_le hQ hA h8 2 3 1 h3
        have e3 := resCount_pull_le hQ hB h8 1 3 0 h3
        have e4 := resCount_pull_le hQ hA h8 5 3 2 h3
        refine resCount_or_le.trans ?_
        refine (add_le_add resCount_or_le resCount_or_le).trans ?_
        omega
      have hsplit : 8 ^ (n + 1) = 4 * (2 * 8 ^ n) := by ring
      have hsplit' : 8 ^ (n + 1) = 8 * 8 ^ n := by ring
      refine ⟨A', B', ?_, ?_, ?_, ?_, ?_⟩
      · rw [hsplit]; exact hA'per.mul 4
      · rw [hsplit']; exact hB'per
      · have hA4 := resCount_mul_le (by positivity) hA'per 4
        rw [← hsplit] at hA4
        rw [← hsplit'] at hB'cnt
        rw [show 6 ^ (n + 1) = 6 * 6 ^ n by ring]
        omega
      · intro s hs
        obtain ⟨-, -, hnext⟩ := sigmaTau_surv_succ hs
        have hs2 : s % 2 = 0 ∨ s % 2 = 1 := by omega
        rcases hs2 with hs2 | hs2
        · have hσ : sigmaTauPerm (4 * s) = 4 * (3 * (s / 2) + 0) := by
            rw [sigmaTau_apply]; unfold ctau amusical; split_ifs <;> omega
          left
          refine ⟨by simpa using hs2, ?_⟩
          have := hAs _ (hσ ▸ hnext)
          simpa using this
        · have hσ : sigmaTauPerm (4 * s) = 2 * (3 * (s / 2) + 1) + 1 := by
            rw [sigmaTau_apply]; unfold ctau amusical; split_ifs <;> omega
          right
          refine ⟨by simpa using hs2, ?_⟩
          have := hBs _ (hσ ▸ hnext)
          simpa using this
      · intro s hs
        obtain ⟨-, hone, hnext⟩ := sigmaTau_surv_succ hs
        have hs8 : s % 8 = 0 ∨ s % 8 = 1 ∨ s % 8 = 2 ∨ s % 8 = 3 ∨ s % 8 = 4 ∨
            s % 8 = 5 ∨ s % 8 = 6 ∨ s % 8 = 7 := by omega
        rcases hs8 with hs8 | hs8 | hs8 | hs8 | hs8 | hs8 | hs8 | hs8
        · exfalso; apply hone
          rw [sigmaTau_apply]; unfold ctau amusical; split_ifs <;> omega
        · have hσ : sigmaTauPerm (2 * s + 1) = 2 * (3 * (s / 8) + 0) + 1 := by
            rw [sigmaTau_apply]; unfold ctau amusical; split_ifs <;> omega
          right; left
          refine ⟨by simpa using hs8, ?_⟩
          have := hBs _ (hσ ▸ hnext)
          simpa using this
        · have hσ : sigmaTauPerm (2 * s + 1) = 4 * (3 * (s / 8) + 1) := by
            rw [sigmaTau_apply]; unfold ctau amusical; split_ifs <;> omega
          left; right
          refine ⟨by simpa using hs8, ?_⟩
          exact hAs _ (hσ ▸ hnext)
        · exfalso; apply hone
          rw [sigmaTau_apply]; unfold ctau amusical; split_ifs <;> omega
        · exfalso; apply hone
          rw [sigmaTau_apply]; unfold ctau amusical; split_ifs <;> omega
        · have hσ : sigmaTauPerm (2 * s + 1) = 4 * (3 * (s / 8) + 2) := by
            rw [sigmaTau_apply]; unfold ctau amusical; split_ifs <;> omega
          right; right
          refine ⟨by simpa using hs8, ?_⟩
          exact hAs _ (hσ ▸ hnext)
        · have hσ : sigmaTauPerm (2 * s + 1) = 2 * (3 * (s / 8) + 2) + 1 := by
            rw [sigmaTau_apply]; unfold ctau amusical; split_ifs <;> omega
          left; left
          refine ⟨by simpa using hs8, ?_⟩
          exact hBs _ (hσ ▸ hnext)
        · exfalso; apply hone
          rw [sigmaTau_apply]; unfold ctau amusical; split_ifs <;> omega

/-- The never-entering sets of the `σ_τ` cone have density tending to zero. -/
theorem sigmaTau_backward_density (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, IntDensityLE {x | ∀ j ≤ n, (sigmaTauPerm ^ j) x ∉ {x : ℤ | x % 4 = 2}} ε := by
  have hlim : Filter.Tendsto (fun n : ℕ => ((3 : ℝ) / 4) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 3))).exists
  obtain ⟨A, B, hA, hB, hcnt, hAs, hBs⟩ := sigmaTau_survivor_cover n
  have hQ : 0 < 8 ^ n := by positivity
  let P : ℤ → Prop := fun x =>
    (x % ((4 : ℕ) : ℤ) = 0 ∧ A (1 * (x / ((4 : ℕ) : ℤ)) + 0)) ∨
      (x % ((2 : ℕ) : ℤ) = 1 ∧ B (1 * (x / ((2 : ℕ) : ℤ)) + 0))
  have hPA := hA.pull (by norm_num : 0 < 4) 0 1 0
  have hPB := (hB.pull (by norm_num : 0 < 2) 1 1 0).mul 2
  have hmul : 2 * (2 * 8 ^ n) = 4 * 8 ^ n := by ring
  rw [hmul] at hPB
  have hP : AntiKohlPeriodic.IsPer (4 * 8 ^ n) P := hPA.or hPB
  have hPcnt : AntiKohlPeriodic.resCount (4 * 8 ^ n) P ≤ 4 * 6 ^ n := by
    have e1 := AntiKohlPeriodic.resCount_pull_le hQ hA (by norm_num : 0 < 4) 0 1 0
      isCoprime_one_left
    have e2 := AntiKohlPeriodic.resCount_pull_le hQ hB (by norm_num : 0 < 2) 1 1 0
      isCoprime_one_left
    have e3 := AntiKohlPeriodic.resCount_mul_le (by positivity)
      (hB.pull (by norm_num : 0 < 2) 1 1 0) 2
    rw [hmul] at e3
    refine AntiKohlPeriodic.resCount_or_le.trans ?_
    omega
  refine ⟨n, intDensityLE_of_isPer (by positivity) hP _ ?_ ε ?_⟩
  · intro x hx
    have hx' : ∀ j ≤ n, (sigmaTauPerm ^ j) x % 4 ≠ 2 := hx
    have hx0 : x % 4 ≠ 2 := by simpa using hx' 0 (by omega)
    have hcases : x % 4 = 0 ∨ x % 2 = 1 := by omega
    rcases hcases with h4 | h2
    · left
      refine ⟨by simpa using h4, ?_⟩
      have hxe : x = 4 * (x / 4) := by omega
      have := hAs (x / 4) (by rw [← hxe]; exact hx')
      simpa using this
    · right
      refine ⟨by simpa using h2, ?_⟩
      have hxe : x = 2 * (x / 2) + 1 := by omega
      have := hBs (x / 2) (by rw [← hxe]; exact hx')
      simpa using this
  · have hcast : (AntiKohlPeriodic.resCount (4 * 8 ^ n) P : ℝ) ≤ 4 * 6 ^ n := by
      exact_mod_cast hPcnt
    have hpow : ((3 : ℝ) / 4) ^ n = (6 : ℝ) ^ n / 8 ^ n := by
      rw [div_pow]
      rw [show (6 : ℝ) ^ n = 3 ^ n * 2 ^ n by rw [← mul_pow]; norm_num,
        show (8 : ℝ) ^ n = 4 ^ n * 2 ^ n by rw [← mul_pow]; norm_num]
      field_simp
    rw [hpow, div_lt_iff₀ (by positivity)] at hn
    push_cast
    nlinarith

/-- **Proved.**  Every orbit of `σ_τ = τ ∘ U` has density `0`.  Paper proof: Theorem T with
`S = 2 + 4ℤ`.  The forward core is `3ⁿ (2 + 4ℤ)`, of density `3⁻ⁿ/4`.  The backward core
`{x : σ_τʲ x ∉ S, j ≤ n}` has density `(1/2)(3/4)ⁿ⁻¹`.  This comes from a closed 13-type
automaton on image classes typed by known `2`-adic digits and residue mod `3`, with
characteristic polynomial `λ¹²(4λ − 3)/4` (agent scripts `typeauto.py`, `typeauto2.py`). -/
theorem sigmaTau_orbit_densityZero (x : ℤ) : IntDensityZero (permOrbit sigmaTauPerm x) := by
  simpa using orbit_densityZero_of_transientCone sigmaTauPerm {x : ℤ | x % 4 = 2}
    (fun x hx => sigmaTau_cone x hx) sigmaTau_forward_density sigmaTau_backward_density
    ({x} : Finset ℤ)

/-! ## One fixed prime is essential -/

/-- `h(6k+r) = 5k+r` (`r ∈ {0, 2, 4}`), `h(4k+r) = 5k+r` (`r ∈ {1, 3}`). -/
def hFive (x : ℤ) : ℤ :=
  if x % 2 = 0 then 5 * (x / 6) + x % 6 else 5 * (x / 4) + x % 4

/-- **Proved.**  `hFive` is a bijection of `ℤ` (images: `5k + {0, 2, 4}` from evens, `5k + {1, 3}`
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
/-- **Proved.**  `h ∘ (· + 1) ∘ h⁻¹` has modulus `30` and only the slopes `3/2` and `2/3` (the
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
