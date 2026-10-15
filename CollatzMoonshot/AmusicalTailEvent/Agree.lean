/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Permutations of `ℕ` that agree outside a finite set

If `σ` and `τ` agree outside a finite set `S`, then
* every `σ`-orbit avoiding `S` is a `τ`-orbit, so the orbit sets differ by finitely many orbits
  (`infinite_orbits_iff_of_agree`);
* the infinite orbits correspond bijectively through their forward tails: an infinite orbit
  eventually leaves `S` for good, and past that point `σ` and `τ` move it identically
  (`encard_infiniteOrbits_eq_of_agree`).
-/

namespace CollatzMoonshot.Amusical.TailEvent

open Equiv

/-- The orbit of `x` under `σ` (the same set as `natPermOrbit`). -/
abbrev orb (σ : Perm ℕ) (x : ℕ) : Set ℕ := Set.range fun j : ℤ => (σ ^ j) x

variable {σ τ : Perm ℕ} {S : Set ℕ}

theorem mem_orb_self (σ : Perm ℕ) (x : ℕ) : x ∈ orb σ x := ⟨0, by simp⟩

theorem orb_eq_of_mem {x y : ℕ} (h : y ∈ orb σ x) : orb σ y = orb σ x := by
  have h' : σ.SameCycle x y := h
  ext z
  change σ.SameCycle y z ↔ σ.SameCycle x z
  exact ⟨h'.trans, h'.symm.trans⟩

theorem zpow_mem_orb (σ : Perm ℕ) (x : ℕ) (j : ℤ) : (σ ^ j) x ∈ orb σ x := ⟨j, rfl⟩

/-- On an orbit avoiding `S`, `τ` and `σ` move points identically. -/
theorem zpow_eq_of_agree (h : ∀ y ∉ S, σ y = τ y) {x : ℕ} (hx : ∀ j : ℤ, (σ ^ j) x ∉ S)
    (j : ℤ) : (τ ^ j) x = (σ ^ j) x := by
  induction j using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [add_comm (n : ℤ) 1, zpow_add, zpow_add, zpow_one, zpow_one, Perm.mul_apply,
      Perm.mul_apply, ih, h _ (hx n)]
  | pred n ih =>
    apply τ.injective
    have e1 : τ ((τ ^ (-(n : ℤ) - 1)) x) = (τ ^ (-(n : ℤ))) x := by
      rw [← Perm.mul_apply, ← zpow_one_add]; congr 2; ring
    have e2 : σ ((σ ^ (-(n : ℤ) - 1)) x) = (σ ^ (-(n : ℤ))) x := by
      rw [← Perm.mul_apply, ← zpow_one_add]; congr 2; ring
    rw [e1, ih, ← h _ (hx _), e2]

theorem orb_eq_of_agree (h : ∀ y ∉ S, σ y = τ y) {x : ℕ} (hx : ∀ j : ℤ, (σ ^ j) x ∉ S) :
    orb τ x = orb σ x := by
  ext z
  simp only [Set.mem_range, zpow_eq_of_agree h hx]

theorem orbits_subset_of_agree (h : ∀ y ∉ S, σ y = τ y) :
    {O | ∃ x, O = orb σ x} ⊆ {O | ∃ x, O = orb τ x} ∪ orb σ '' S := by
  rintro O ⟨x, rfl⟩
  by_cases hx : ∃ j : ℤ, (σ ^ j) x ∈ S
  · obtain ⟨j, hj⟩ := hx
    exact Or.inr ⟨_, hj, orb_eq_of_mem (zpow_mem_orb σ x j)⟩
  · push Not at hx
    exact Or.inl ⟨x, (orb_eq_of_agree h hx).symm⟩

/-- Orbit sets of permutations agreeing outside a finite set are finite together. -/
theorem infinite_orbits_iff_of_agree (hS : S.Finite) (h : ∀ y ∉ S, σ y = τ y) :
    {O | ∃ x, O = orb τ x}.Infinite ↔ {O | ∃ x, O = orb σ x}.Infinite := by
  have key : ∀ σ τ : Perm ℕ, (∀ y ∉ S, σ y = τ y) →
      {O | ∃ x, O = orb τ x}.Finite → {O | ∃ x, O = orb σ x}.Finite := fun σ τ h hf =>
    (hf.union (hS.image _)).subset (orbits_subset_of_agree h)
  exact ⟨fun hi hf => hi (key τ σ (fun y hy => (h y hy).symm) hf), fun hi hf => hi (key σ τ h hf)⟩

/-- An infinite orbit is injectively parametrised by forward times. -/
theorem pow_injective_of_infinite {x : ℕ} (hinf : (orb σ x).Infinite) :
    Function.Injective fun n : ℕ => (σ ^ n) x := by
  intro m n hmn
  by_contra hne
  wlog hlt : m < n generalizing m n
  · exact this hmn.symm (Ne.symm hne) (by omega)
  have hp : (σ ^ (n - m)) x = x := by
    apply (σ ^ m).injective
    simp only at hmn
    rw [← Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hlt.le, hmn]
  apply hinf
  apply ((Set.finite_range fun i : Fin (n - m) => (σ ^ (i : ℕ)) x)).subset
  rintro _ ⟨j, rfl⟩
  have hpz : ((σ ^ (n - m)) ^ (j / (n - m : ℕ) : ℤ)) x = x :=
    Perm.zpow_apply_eq_self_of_apply_eq_self hp _
  have hpos : (0 : ℤ) < (n - m : ℕ) := by omega
  refine ⟨⟨(j % (n - m : ℕ)).toNat, ?_⟩, ?_⟩
  · have := Int.emod_lt_of_pos j hpos
    omega
  · simp only
    have h0 : 0 ≤ j % (n - m : ℕ) := Int.emod_nonneg _ hpos.ne'
    rw [← zpow_natCast, Int.toNat_of_nonneg h0]
    conv_rhs => rw [← Int.emod_add_mul_ediv j (n - m : ℕ)]
    rw [zpow_add, Perm.mul_apply, zpow_mul, zpow_natCast, hpz]

/-- An infinite orbit eventually leaves a finite set for good. -/
theorem exists_forward_avoid {x : ℕ} (hS : S.Finite) (hinf : (orb σ x).Infinite) :
    ∃ N : ℕ, ∀ n : ℕ, (σ ^ n) ((σ ^ N) x) ∉ S := by
  have hinj := pow_injective_of_infinite hinf
  have hfin : ((fun n : ℕ => (σ ^ n) x) ⁻¹' S).Finite := hS.preimage hinj.injOn
  obtain ⟨N, hN⟩ := hfin.bddAbove
  refine ⟨N + 1, fun n hn => ?_⟩
  rw [← Perm.mul_apply, ← pow_add] at hn
  have := hN hn
  omega

theorem pow_eq_of_forward (h : ∀ y ∉ S, σ y = τ y) {x : ℕ} (hx : ∀ n : ℕ, (σ ^ n) x ∉ S)
    (n : ℕ) : (τ ^ n) x = (σ ^ n) x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_succ', Perm.mul_apply, Perm.mul_apply, ih, h _ (hx n)]

theorem orb_infinite_of_forward (h : ∀ y ∉ S, σ y = τ y) {x : ℕ}
    (hx : ∀ n : ℕ, (σ ^ n) x ∉ S) (hinf : (orb σ x).Infinite) : (orb τ x).Infinite := by
  have hr : (Set.range fun n : ℕ => (σ ^ n) x).Infinite :=
    Set.infinite_range_of_injective (pow_injective_of_infinite hinf)
  refine hr.mono ?_
  rintro _ ⟨n, rfl⟩
  exact ⟨n, by simp only [zpow_natCast, pow_eq_of_forward h hx]⟩

/-- The infinite orbits of `τ` are at least as many as those of `σ`. -/
theorem encard_infiniteOrbits_le_of_agree (hS : S.Finite) (h : ∀ y ∉ S, σ y = τ y) :
    {O | ∃ x, O = orb σ x ∧ O.Infinite}.encard ≤
      {O | ∃ x, O = orb τ x ∧ O.Infinite}.encard := by
  classical
  let P : Set ℕ → Prop := fun O => ∃ y ∈ O, ∀ n : ℕ, (σ ^ n) y ∉ S
  let f : Set ℕ → Set ℕ := fun O => if hO : P O then orb τ hO.choose else ∅
  have hP : ∀ O ∈ {O | ∃ x, O = orb σ x ∧ O.Infinite}, ∃ hO : P O,
      O = orb σ hO.choose ∧ O.Infinite ∧ f O = orb τ hO.choose := by
    rintro O ⟨x, rfl, hinf⟩
    obtain ⟨N, hN⟩ := exists_forward_avoid hS hinf
    have hO : P (orb σ x) := ⟨_, zpow_mem_orb σ x N, by simpa using hN⟩
    refine ⟨hO, (orb_eq_of_mem hO.choose_spec.1).symm, hinf, dif_pos hO⟩
  refine Set.encard_le_encard_of_injOn (f := f) (fun O hO => ?_) (fun O1 h1 O2 h2 he => ?_)
  · obtain ⟨hO, hOe, hinf, hf⟩ := hP O hO
    refine ⟨_, hf, hf ▸ orb_infinite_of_forward h hO.choose_spec.2 (hOe ▸ hinf)⟩
  · obtain ⟨hO1, e1, -, hf1⟩ := hP O1 h1
    obtain ⟨hO2, e2, -, hf2⟩ := hP O2 h2
    rw [hf1, hf2] at he
    have hz2 : hO2.choose ∈ orb τ hO1.choose := he ▸ mem_orb_self τ _
    obtain ⟨j, hj⟩ := hz2
    rw [e1, e2]
    rcases le_or_gt 0 j with hj0 | hj0
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hj0
      simp only [zpow_natCast, pow_eq_of_forward h hO1.choose_spec.2] at hj
      exact (orb_eq_of_mem ⟨n, by simpa using hj⟩).symm
    · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -j by omega)
      have hj' : (τ ^ (n : ℤ)) hO2.choose = hO1.choose := by
        rw [← hn, ← hj, ← Perm.mul_apply, ← zpow_add, neg_add_cancel, zpow_zero, Perm.one_apply]
      simp only [zpow_natCast, pow_eq_of_forward h hO2.choose_spec.2] at hj'
      exact orb_eq_of_mem ⟨n, by simpa using hj'⟩

/-- Permutations agreeing outside a finite set have equally many infinite orbits. -/
theorem encard_infiniteOrbits_eq_of_agree (hS : S.Finite) (h : ∀ y ∉ S, σ y = τ y) :
    {O | ∃ x, O = orb τ x ∧ O.Infinite}.encard = {O | ∃ x, O = orb σ x ∧ O.Infinite}.encard :=
  le_antisymm (encard_infiniteOrbits_le_of_agree hS fun y hy => (h y hy).symm)
    (encard_infiniteOrbits_le_of_agree hS h)

end CollatzMoonshot.Amusical.TailEvent
