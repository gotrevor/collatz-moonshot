/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalWindow

/-!
# Closed routes on Klamkin's problem (a) for the amusical permutation

The Lean witnesses behind the amusical rows of `Maze.lean`.  Narrative:
`RESEARCH-2026-10-13-amusical-single-chain.md`.

* **Balanced on `ℕ`.**  `amusical_mass_conservation`: for every `X`, as many `n < X` jump to
  `≥ X` as `m < X` are reached from `≥ X`.  Every density, measure or level-crossing argument
  that only uses this balance also holds for `ℕ`, a union of infinitely many orbits, so it
  cannot bound the number of orbits.  The forward/backward drift asymmetry is the same balance
  in two coordinates (`even_iff_amusical_mod_three`).
* **Invariants are a costume.**  `amusicalInfinitelyManyOrbits_iff_invariant`: an
  orbit-invariant function with infinitely many values on `ℕ` exists exactly when there are
  infinitely many orbits.
* **Residues cannot certify minima.**  `MinimaNotResidueDetermined`, believed, with the
  `χ²` evidence in its docstring.
* **The wall.**  `NoLinearRecurrence` reopens the route, via
  `amusicalInfinitelyManyOrbits_of_noLinearRecurrence`.
-/

namespace CollatzMoonshot.Obstructions.Amusical

open CollatzMoonshot.Amusical

theorem amusicalInv_nonneg {x : ℤ} (h : 0 ≤ x) : 0 ≤ amusicalInv x := by
  unfold amusicalInv; split_ifs <;> omega

open Classical in
/-- **Mass conservation on `ℕ`** (Tavares 2013, Lemma 2, for `U`).  The `n < X` that `U`
sends to `≥ X` are as many as the `m < X` whose preimage is `≥ X`. -/
theorem amusical_mass_conservation (X : ℕ) :
    ((Finset.range X).filter fun n : ℕ => (X : ℤ) ≤ amusical n).card =
      ((Finset.range X).filter fun m : ℕ => (X : ℤ) ≤ amusicalInv m).card := by
  -- the complements correspond under `U`
  have hstay : ((Finset.range X).filter fun n : ℕ => amusical n < (X : ℤ)).card =
      ((Finset.range X).filter fun m : ℕ => amusicalInv m < (X : ℤ)).card := by
    refine Finset.card_bij (fun n _ => (amusical n).toNat) ?_ ?_ ?_
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
      have h0 := amusical_nonneg (Int.natCast_nonneg n)
      refine ⟨by omega, ?_⟩
      rw [Int.toNat_of_nonneg h0, amusicalInv_amusical]
      exact_mod_cast hn.1
    · intro a ha b hb hab
      have ha0 := amusical_nonneg (Int.natCast_nonneg a)
      have hb0 := amusical_nonneg (Int.natCast_nonneg b)
      have : amusical a = amusical b := by omega
      exact_mod_cast amusical_injective this
    · intro m hm
      simp only [Finset.mem_filter, Finset.mem_range] at hm
      have h0 := amusicalInv_nonneg (Int.natCast_nonneg m)
      refine ⟨(amusicalInv m).toNat, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_range]
        rw [Int.toNat_of_nonneg h0, amusical_amusicalInv]
        exact ⟨by omega, by exact_mod_cast hm.1⟩
      · rw [Int.toNat_of_nonneg h0, amusical_amusicalInv]; simp
  have h1 := Finset.card_filter_add_card_filter_not (s := Finset.range X)
    (fun n : ℕ => (X : ℤ) ≤ amusical n)
  have h2 := Finset.card_filter_add_card_filter_not (s := Finset.range X)
    (fun m : ℕ => (X : ℤ) ≤ amusicalInv m)
  simp only [not_le] at h1 h2
  omega

/-- The least natural number in a set of integers (`0` if there is none). -/
noncomputable def minNatOf (O : Set ℤ) : ℕ := by
  classical
  exact if h : ∃ k : ℕ, (k : ℤ) ∈ O then Nat.find h else 0

/-- The least natural number on the orbit of `n`. -/
noncomputable def orbitMinNat (n : ℤ) : ℕ := minNatOf (amusicalOrbit n)

theorem orbitMinNat_mem {n : ℤ} (hn : 0 ≤ n) : (orbitMinNat n : ℤ) ∈ amusicalOrbit n := by
  classical
  have h : ∃ k : ℕ, (k : ℤ) ∈ amusicalOrbit n := ⟨n.toNat, by
    rw [Int.toNat_of_nonneg hn]; exact mem_amusicalOrbit_self n⟩
  unfold orbitMinNat minNatOf
  rw [dif_pos h]
  exact Nat.find_spec h

theorem orbitMinNat_eq_of_orbit_eq {a b : ℤ} (h : amusicalOrbit a = amusicalOrbit b) :
    orbitMinNat a = orbitMinNat b := by
  unfold orbitMinNat; rw [h]

theorem amusicalOrbit_amusical (n : ℤ) : amusicalOrbit (amusical n) = amusicalOrbit n :=
  amusicalOrbit_eq_of_mem ⟨1, by dsimp only; rw [zpow_one]; rfl⟩

/-- **Invariants are a costume of Klamkin (a).**  There are infinitely many orbits exactly when
some `U`-invariant function takes infinitely many values on the nonnegative integers. -/
theorem amusicalInfinitelyManyOrbits_iff_invariant :
    AmusicalInfinitelyManyOrbits ↔
      ∃ f : ℤ → ℤ, (∀ n, f (amusical n) = f n) ∧ (f '' {n | 0 ≤ n}).Infinite := by
  constructor
  · intro h
    refine ⟨fun n => (orbitMinNat n : ℤ), fun n => ?_, ?_⟩
    · simp only [orbitMinNat_eq_of_orbit_eq (amusicalOrbit_amusical n)]
    · intro hfin
      apply h
      -- each orbit is the orbit of its least element
      refine (hfin.image fun v => amusicalOrbit v).subset ?_
      rintro _ ⟨x, hx0, rfl⟩
      refine ⟨(orbitMinNat x : ℤ), ⟨x, hx0, rfl⟩, ?_⟩
      exact amusicalOrbit_eq_of_mem (orbitMinNat_mem hx0)
  · rintro ⟨f, hf, hinf⟩ hfin
    apply hinf
    have hfinv : ∀ n, f (amusicalInv n) = f n := fun n => by
      rw [← hf (amusicalInv n), amusical_amusicalInv]
    -- `f` is constant on orbits
    have hconst : ∀ (j : ℤ) (x : ℤ), f ((amusicalPerm ^ j) x) = f x := by
      intro j
      induction j using Int.induction_on with
      | zero => intro x; simp
      | succ i ih =>
        intro x
        rw [zpow_add_one, Equiv.Perm.mul_apply, ih]
        exact hf x
      | pred i ih =>
        intro x
        rw [zpow_sub_one, Equiv.Perm.mul_apply, ih]
        exact hfinv x
    classical
    let g : Set ℤ → ℤ := fun O =>
      if h : ∃ x : ℤ, 0 ≤ x ∧ O = amusicalOrbit x then f (Classical.choose h) else 0
    refine (hfin.image g).subset ?_
    rintro _ ⟨n, hn0, rfl⟩
    refine ⟨amusicalOrbit n, ⟨n, hn0, rfl⟩, ?_⟩
    have h : ∃ x : ℤ, 0 ≤ x ∧ amusicalOrbit n = amusicalOrbit x := ⟨n, hn0, rfl⟩
    simp only [g, dif_pos h]
    obtain ⟨_, hx⟩ := Classical.choose_spec h
    have hmem : n ∈ amusicalOrbit (Classical.choose h) := hx ▸ mem_amusicalOrbit_self n
    obtain ⟨j, hj⟩ := hmem
    have := hconst j (Classical.choose h)
    simp only at hj
    rw [hj] at this
    exact this.symm

/-- **Believed (~97%): residues cannot certify orbit minima.**  For no modulus `M` is being an
orbit minimum eventually a congruence condition.  Evidence (2026-10-13,
`scripts/amusical/minima_vs_window.py`, `n ≤ 10^6`): among `L`-window minima, the share that
are global minima shows no dependence on the class mod `72`, `864` or `2592` once `L` is large
(`χ²` mod 72 falls `62 → 30 → 16` on 15 df for `L = 20, 40, 80`).  The window condition itself
is a congruence condition (`windowMinDensity`); survival past it is not. -/
def MinimaNotResidueDetermined : Prop :=
  ∀ M : ℕ, 0 < M → ¬ ∃ (N : ℕ) (G : Finset ℕ), ∀ n : ℕ, N ≤ n → (IsOrbitMin n ↔ n % M ∈ G)

/-- **Reopen condition for the single-chain wall.**  No aperiodic orbit returns to linear
size arbitrarily late. -/
def NoLinearRecurrence : Prop :=
  ∀ x : ℤ, 0 ≤ x → (amusicalOrbit x).Infinite → ¬ AmusicalLinearlyRecurrent x

theorem amusicalInfinitelyManyOrbits_of_noLinearRecurrence (h : NoLinearRecurrence) :
    AmusicalInfinitelyManyOrbits := by
  by_contra hfin
  obtain ⟨x, hx0, hinf, hrec⟩ := exists_linearlyRecurrent_of_finitelyManyOrbits hfin
  exact h x hx0 hinf hrec

end CollatzMoonshot.Obstructions.Amusical
