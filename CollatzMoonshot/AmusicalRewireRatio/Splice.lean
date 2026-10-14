/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalRewireRatio.Cuts

/-! Algebraic infrastructure for rewiring a permutation by permuting cut sources. -/

namespace CollatzMoonshot.Amusical

/-- Rewire `σ` by first permuting its cut sources.  Thus a source `n` receives the old target
`σ (p n)`.  Bijectivity is automatic; the remaining construction only has to build `p`. -/
def rewireBySource (σ p : Equiv.Perm ℕ) : Equiv.Perm ℕ := σ * p

@[simp] theorem rewireBySource_apply (σ p : Equiv.Perm ℕ) (n : ℕ) :
    rewireBySource σ p n = σ (p n) := by
  rfl

/-- Rewiring changes no source fixed by the source permutation. -/
theorem rewireBySource_eq_of_fixed {σ p : Equiv.Perm ℕ} {n : ℕ} (hn : p n = n) :
    rewireBySource σ p n = σ n := by
  simp [hn]

/-- Every changed value comes from a source moved by the source permutation. -/
theorem rewireBySource_changed_imp_moved {σ p : Equiv.Perm ℕ} {n : ℕ}
    (hn : rewireBySource σ p n ≠ σ n) : p n ≠ n := by
  contrapose! hn
  exact rewireBySource_eq_of_fixed hn

/-- A finite-range count for changed values is bounded by the corresponding count for moved
sources.  This isolates the quantitative part of the global construction from its orbit proof. -/
theorem rewireBySource_changed_card_le (σ p : Equiv.Perm ℕ) (N : ℕ) :
    ((Finset.range N).filter fun n => rewireBySource σ p n ≠ σ n).card ≤
      ((Finset.range N).filter fun n => p n ≠ n).card := by
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, rewireBySource_changed_imp_moved hn.2⟩

/-- Pointwise target comparison for a source permutation transfers verbatim to the rewired
permutation. -/
theorem rewireBySource_rel {σ p : Equiv.Perm ℕ} {R : ℕ → ℕ → Prop}
    (hR : ∀ n, R (σ (p n)) (σ n)) (n : ℕ) : R (rewireBySource σ p n) (σ n) := by
  exact hR n

/-- The affine factor-three estimate required by Theorem R follows once each moved cut source is
sent to a cut source at the same scale. -/
theorem rewireBySource_ratio {p : Equiv.Perm ℕ}
    (hratio : ∀ n, amusicalNatPerm (p n) ≤ 3 * amusicalNatPerm n + 3 ∧
      amusicalNatPerm n ≤ 3 * amusicalNatPerm (p n) + 3) (n : ℕ) :
    (rewireBySource amusicalNatPerm p n : ℤ) ≤ 3 * amusical n + 3 ∧
      amusical n ≤ 3 * (rewireBySource amusicalNatPerm p n : ℤ) + 3 := by
  rw [rewireBySource_apply, ← amusicalNatPerm_apply_cast]
  exact_mod_cast hratio n

/-- Fixing all points on finite orbits gives the finite-orbit clause of Theorem R. -/
theorem rewireBySource_eq_on_finiteOrbits {p : Equiv.Perm ℕ}
    (hfixed : ∀ n : ℕ, (amusicalOrbit n).Finite → p n = n) {n : ℕ}
    (hn : (amusicalOrbit n).Finite) :
    (rewireBySource amusicalNatPerm p n : ℤ) = amusical n := by
  rw [rewireBySource_eq_of_fixed (hfixed n hn), amusicalNatPerm_apply_cast]

/-- The exact interface the geometric cut construction must provide.  Its permutation `p`
permutes cut sources; all algebraic obligations for the resulting successor are recorded here. -/
structure BoundedRatioSourceRewire where
  sourcePerm : Equiv.Perm ℕ
  fixed_finite : ∀ n : ℕ, (amusicalOrbit n).Finite → sourcePerm n = n
  moved_card : ∃ C : ℕ, ∀ N : ℕ,
    ((Finset.range N).filter fun n => sourcePerm n ≠ n).card ≤
      C * (Nat.log 2 N + 1) ^ 2
  target_ratio : ∀ n, amusicalNatPerm (sourcePerm n) ≤ 3 * amusicalNatPerm n + 3 ∧
    amusicalNatPerm n ≤ 3 * amusicalNatPerm (sourcePerm n) + 3
  connected : ∀ a b : ℕ, (amusicalOrbit a).Infinite → (amusicalOrbit b).Infinite →
    ∃ j : ℤ, ((rewireBySource amusicalNatPerm sourcePerm) ^ j) a = b

/-- A level-preserving permutation of the canonical scale cuts automatically satisfies every
quantitative requirement.  The remaining obligation is exactly the global orbit proof. -/
noncomputable def BoundedRatioSourceRewire.ofScaleCutPerm
    (p : Equiv.Perm ScaleCutIndex) (hlevel : ∀ i, (p i).level = i.level)
    (hconnected : ∀ a b : ℕ, (amusicalOrbit a).Infinite → (amusicalOrbit b).Infinite →
      ∃ j : ℤ, ((rewireBySource amusicalNatPerm (scaleCutSourcePerm p)) ^ j) a = b) :
    BoundedRatioSourceRewire where
  sourcePerm := scaleCutSourcePerm p
  fixed_finite := scaleCutSourcePerm_fixed_finite p
  moved_card := scaleCutSourcePerm_moved_card p
  target_ratio := scaleCutSourcePerm_target_ratio p hlevel
  connected := hconnected

/-- A bounded-ratio source rewiring immediately yields every conclusion of Theorem R. -/
theorem BoundedRatioSourceRewire.realize (d : BoundedRatioSourceRewire) :
    ∃ τ : Equiv.Perm ℕ,
      (∀ n : ℕ, (amusicalOrbit n).Finite → (τ n : ℤ) = amusical n) ∧
      (∃ C : ℕ, ∀ N : ℕ, ((Finset.range N).filter fun n =>
        (τ n : ℤ) ≠ amusical n).card ≤ C * (Nat.log 2 N + 1) ^ 2) ∧
      (∀ n : ℕ, (τ n : ℤ) ≤ 3 * amusical n + 3 ∧
        amusical n ≤ 3 * (τ n : ℤ) + 3) ∧
      ∀ a b : ℕ, (amusicalOrbit a).Infinite → (amusicalOrbit b).Infinite →
        ∃ j : ℤ, (τ ^ j) a = b := by
  refine ⟨rewireBySource amusicalNatPerm d.sourcePerm,
    fun _ hn => rewireBySource_eq_on_finiteOrbits d.fixed_finite hn, ?_,
    rewireBySource_ratio d.target_ratio, d.connected⟩
  obtain ⟨C, hC⟩ := d.moved_card
  refine ⟨C, fun N => ?_⟩
  have heq : ((Finset.range N).filter fun n =>
      ((rewireBySource amusicalNatPerm d.sourcePerm n : ℕ) : ℤ) ≠ amusical n) =
      (Finset.range N).filter fun n =>
        rewireBySource amusicalNatPerm d.sourcePerm n ≠ amusicalNatPerm n := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    refine and_congr_right (fun _ => ?_)
    constructor
    · intro hne heq
      apply hne
      calc
        ((rewireBySource amusicalNatPerm d.sourcePerm n : ℕ) : ℤ) =
            (amusicalNatPerm n : ℤ) := congrArg (fun k : ℕ => (k : ℤ)) heq
        _ = amusical n := amusicalNatPerm_apply_cast n
    · intro hne heq
      apply hne
      apply Nat.cast_injective (R := ℤ)
      exact heq.trans (amusicalNatPerm_apply_cast n).symm
  rw [heq]
  exact (rewireBySource_changed_card_le amusicalNatPerm d.sourcePerm N).trans (hC N)

end CollatzMoonshot.Amusical
