/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalOddRewire.OddTails

/-!
# Ingredients of the tail threshold (Theorem TT)

* An `S`-free forward tail of `U` is a forward ray of every `τ` agreeing with `U` off `S`
  (`tau_pow_nat_eq_of_fwdTail`), and an `S`-free backward tail a backward ray
  (`tau_pow_neg_eq_of_bwdTail`).
* Disjoint rays never share a `τ`-orbit, so infinitely many tails give infinitely many infinite
  `τ`-orbits (`infinite_tauOrbits_of_rays`).
* Off the gluable points GL changes nothing, so there `τ`-orbits are `U`-orbits
  (`zpow_eq_of_not_gluePt`); a non-gluable infinite orbit has an `S`-free tail
  (`exists_tail_of_not_gluePt`).
-/

namespace CollatzMoonshot.Amusical

open CollatzMoonshot.Obstructions.Amusical

theorem tau_pow_nat_eq_of_fwdTail {S : Set ℤ} {τ : Equiv.Perm ℕ}
    (hτ : ∀ n : ℕ, (n : ℤ) ∉ S → (τ n : ℤ) = amusical n) {y : ℕ}
    (hy : ∀ j : ℕ, amusical^[j] (y : ℤ) ∉ S) (j : ℕ) :
    (τ ^ (j : ℤ)) y = (amusicalNatPerm ^ (j : ℤ)) y := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hS : (((amusicalNatPerm ^ (j : ℤ)) y : ℕ) : ℤ) ∉ S := by
        rw [amusicalNatPerm_pow_nat_cast]; exact hy j
      rw [Nat.cast_succ, ← sigma_zpow_apply, ← sigma_zpow_apply, ih]
      apply Nat.cast_injective (R := ℤ)
      rw [hτ _ hS, amusicalNatPerm_apply_cast]

theorem tau_pow_neg_eq_of_bwdTail {S : Set ℤ} {τ : Equiv.Perm ℕ}
    (hτ : ∀ n : ℕ, (n : ℤ) ∉ S → (τ n : ℤ) = amusical n) {y : ℕ}
    (hy : ∀ j : ℕ, 1 ≤ j → amusicalInv^[j] (y : ℤ) ∉ S) (j : ℕ) :
    (τ ^ (-(j : ℤ))) y = (amusicalNatPerm ^ (-(j : ℤ))) y := by
  induction j with
  | zero => simp
  | succ j ih =>
      set v := (amusicalNatPerm ^ (-((j + 1 : ℕ) : ℤ))) y with hvdef
      have hS : (v : ℤ) ∉ S := by
        rw [hvdef, amusicalNatPerm_pow_neg_nat_cast]; exact hy _ (by omega)
      have hv : τ v = (τ ^ (-(j : ℤ))) y := by
        rw [ih]
        apply Nat.cast_injective (R := ℤ)
        rw [hτ _ hS, ← amusicalNatPerm_apply_cast, hvdef, sigma_zpow_apply]
        congr 3
        push_cast
        ring
      apply τ.injective
      rw [hv, sigma_zpow_apply]
      congr 2
      push_cast
      ring

/-- Infinitely many `U`-orbits, each carrying a one-sided `τ`-ray (direction `ε = ±1`), give
infinitely many infinite `τ`-orbits. -/
theorem infinite_tauOrbits_of_rays (τ : Equiv.Perm ℕ) (ε : ℤ) (hε : ε * ε = 1)
    (𝒜 : Set (Set ℤ)) (h𝒜 : 𝒜.Infinite)
    (hray : ∀ O ∈ 𝒜, ∃ y : ℕ, O = amusicalOrbit y ∧ O.Infinite ∧
      ∀ j : ℕ, (τ ^ (ε * j)) y = (amusicalNatPerm ^ (ε * j)) y) :
    {P : Set ℕ | ∃ x : ℕ, P = Set.range (fun j : ℤ => (τ ^ j) x) ∧ P.Infinite}.Infinite := by
  choose! y hyO hyinf hyray using hray
  let f : Set ℤ → Set ℕ := fun O => Set.range fun j : ℤ => (τ ^ j) (y O)
  have hmem (O : Set ℤ) (hO : O ∈ 𝒜) (j : ℕ) :
      (((τ ^ (ε * j)) (y O) : ℕ) : ℤ) ∈ amusicalOrbit (y O) := by
    rw [hyray O hO j, amusicalNatPerm_zpow_apply_cast]
    exact ⟨_, rfl⟩
  have hfinf (O : Set ℤ) (hO : O ∈ 𝒜) : (f O).Infinite := by
    have hσ := perm_zpow_apply_injective_of_infinite amusicalNatPerm
      ((natOrbit_infinite_iff _).2 (hyO O hO ▸ hyinf O hO))
    have hinj : Function.Injective fun j : ℕ => (τ ^ (ε * j)) (y O) := by
      intro a b hab
      simp only [hyray O hO] at hab
      have h1 := congrArg (ε * ·) (hσ hab)
      simp only [← mul_assoc, hε, one_mul] at h1
      exact_mod_cast h1
    exact (Set.infinite_range_of_injective hinj).mono
      (Set.range_subset_iff.2 fun j => ⟨_, rfl⟩)
  have hinjOn : Set.InjOn f 𝒜 := by
    intro O hO O' hO' hff
    obtain ⟨j, hj⟩ : y O' ∈ f O := hff ▸ ⟨0, by simp⟩
    simp only at hj
    rw [hyO O hO, hyO O' hO']
    rcases le_or_gt 0 (ε * j) with hm | hm
    · have hj' : j = ε * (((ε * j).toNat : ℕ) : ℤ) := by
        rw [Int.toNat_of_nonneg hm, ← mul_assoc, hε, one_mul]
      have h1 := hmem O hO (ε * j).toNat
      rw [← hj', hj] at h1
      exact (amusicalOrbit_eq_of_mem h1).symm
    · have hj' : -j = ε * (((-(ε * j)).toNat : ℕ) : ℤ) := by
        rw [Int.toNat_of_nonneg (by omega), mul_neg, ← mul_assoc, hε, one_mul]
      have hback : (τ ^ (-j)) (y O') = y O := by
        rw [← hj, perm_zpow_apply_zpow]; simp
      have h1 := hmem O' hO' (-(ε * j)).toNat
      rw [← hj', hback] at h1
      exact amusicalOrbit_eq_of_mem h1
  refine (h𝒜.image hinjOn).mono ?_
  rintro P ⟨O, hO, rfl⟩
  exact ⟨y O, rfl, hfinf O hO⟩

/-- Where `τ` changes `σ` only at gluable points, the `τ`-orbit of a non-gluable point is its
`σ`-orbit. -/
theorem zpow_eq_of_not_gluePt {σ τ : Equiv.Perm ℕ} {S : Set ℕ}
    (hτ : ∀ n, τ n ≠ σ n → GluePt σ S n) {x : ℕ} (hx : ¬ GluePt σ S x) (j : ℤ) :
    (τ ^ j) x = (σ ^ j) x := by
  have hng (j : ℤ) : ¬ GluePt σ S ((σ ^ j) x) := fun h => hx (by
    simpa [perm_zpow_apply_zpow] using h.zpow (-j))
  have hag (j : ℤ) : τ ((σ ^ j) x) = σ ((σ ^ j) x) := by
    by_contra h; exact hng j (hτ _ h)
  induction j using Int.induction_on with
  | zero => simp
  | succ j ih => rw [← sigma_zpow_apply, ← sigma_zpow_apply, ih, hag]
  | pred j ih =>
      apply τ.injective
      rw [sigma_zpow_apply, sub_add_cancel, ih, hag, sigma_zpow_apply, sub_add_cancel]

/-- A non-gluable infinite orbit of `U` has an `S`-free forward or backward tail. -/
theorem exists_tail_of_not_gluePt {S : Set ℤ} {x : ℕ}
    (hinf : (Set.range fun j : ℤ => (amusicalNatPerm ^ j) x).Infinite)
    (hx : ¬ GluePt amusicalNatPerm {n : ℕ | (n : ℤ) ∈ S} x) :
    ∃ y : ℕ, amusicalOrbit (y : ℤ) = amusicalOrbit x ∧
      ((∀ j : ℕ, amusical^[j] (y : ℤ) ∉ S) ∨ ∀ j : ℕ, 1 ≤ j → amusicalInv^[j] (y : ℤ) ∉ S) := by
  have horb (k : ℤ) : amusicalOrbit (((amusicalNatPerm ^ k) x : ℕ) : ℤ) = amusicalOrbit x :=
    amusicalOrbit_eq_of_mem ⟨k, (amusicalNatPerm_zpow_apply_cast k x).symm⟩
  by_cases hf : ∀ K : ℤ, ∃ k : ℤ, K ≤ k ∧ (amusicalNatPerm ^ k) x ∈ {n : ℕ | (n : ℤ) ∈ S}
  · have hb : ¬ ∀ K : ℤ, ∃ k : ℤ, k ≤ K ∧
        (amusicalNatPerm ^ k) x ∈ {n : ℕ | (n : ℤ) ∈ S} := fun hb => hx ⟨hinf, hf, hb⟩
    push Not at hb
    obtain ⟨K, hK⟩ := hb
    refine ⟨(amusicalNatPerm ^ (K + 1)) x, horb _, Or.inr fun j hj => ?_⟩
    rw [← amusicalNatPerm_pow_neg_nat_cast, perm_zpow_apply_zpow]
    exact hK _ (by omega)
  · push Not at hf
    obtain ⟨K, hK⟩ := hf
    refine ⟨(amusicalNatPerm ^ K) x, horb _, Or.inl fun j => ?_⟩
    rw [← amusicalNatPerm_pow_nat_cast, perm_zpow_apply_zpow]
    exact hK _ (by omega)

end CollatzMoonshot.Amusical
