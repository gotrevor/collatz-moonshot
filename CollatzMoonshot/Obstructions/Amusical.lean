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
  `χ²` evidence in its docstring; its provable half (every class mod `2^k 3^l` has arbitrarily
  large non-minima) is `exists_large_nonOrbitMin` in `AmusicalReturns.lean`, proved.
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

/-! ## How many orbits can be proved?  Six. -/

/-- An orbit stays inside any set closed under `U` and `U⁻¹`. -/
theorem amusicalOrbit_subset_of_closed {S : Set ℤ} (hU : ∀ y ∈ S, amusical y ∈ S)
    (hV : ∀ y ∈ S, amusicalInv y ∈ S) {x : ℤ} (hx : x ∈ S) : amusicalOrbit x ⊆ S := by
  rintro _ ⟨j, rfl⟩
  induction j using Int.induction_on with
  | zero => simpa using hx
  | succ i ih =>
    show (amusicalPerm ^ ((i : ℤ) + 1)) x ∈ S
    rw [add_comm, zpow_add, zpow_one, Equiv.Perm.mul_apply]
    exact hU _ ih
  | pred i ih =>
    show (amusicalPerm ^ (-(i : ℤ) - 1)) x ∈ S
    rw [sub_eq_add_neg, add_comm, zpow_add, zpow_neg, zpow_one, Equiv.Perm.mul_apply]
    exact hV _ ih

theorem amusicalOrbit_ne_of_closed {S : Set ℤ} (hU : ∀ y ∈ S, amusical y ∈ S)
    (hV : ∀ y ∈ S, amusicalInv y ∈ S) {a b : ℤ} (ha : a ∈ S) (hb : b ∉ S) :
    amusicalOrbit a ≠ amusicalOrbit b := fun h =>
  hb (amusicalOrbit_subset_of_closed hU hV ha (h ▸ mem_amusicalOrbit_self b))

/-- **Six provably distinct orbits on `ℕ`**: the four known cycles `{0}`, `{1}`, `{2, 3}`,
`{4, 6, 9, 7, 5}`, the 12-cycle through `44`, and the orbit of `8`. -/
theorem amusical_six_distinct_orbits : ∀ a ∈ ({0, 1, 2, 4, 44, 8} : Finset ℤ),
    ∀ b ∈ ({0, 1, 2, 4, 44, 8} : Finset ℤ), a ≠ b → amusicalOrbit a ≠ amusicalOrbit b := by
  -- each known cycle is a finite set closed under `U` and `U⁻¹`
  have cyc : ∀ C : Finset ℤ, (∀ y ∈ C, amusical y ∈ C) → (∀ y ∈ C, amusicalInv y ∈ C) →
      ∀ a ∈ C, ∀ b ∉ C, amusicalOrbit a ≠ amusicalOrbit b := fun C hU hV a ha b hb =>
    amusicalOrbit_ne_of_closed (S := (C : Set ℤ)) (by simpa using hU) (by simpa using hV)
      (by simpa using ha) (by simpa using hb)
  have c0 := cyc {0} (by decide) (by decide)
  have c1 := cyc {1} (by decide) (by decide)
  have c2 := cyc {2, 3} (by decide) (by decide)
  have c4 := cyc {4, 6, 9, 7, 5} (by decide) (by decide)
  have c44 := cyc {44, 66, 99, 74, 111, 83, 62, 93, 70, 105, 79, 59} (by decide) (by decide)
  intro a ha b hb hab
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | exact absurd rfl hab
      | exact c0 _ (by decide) _ (by decide) | exact (c0 _ (by decide) _ (by decide)).symm
      | exact c1 _ (by decide) _ (by decide) | exact (c1 _ (by decide) _ (by decide)).symm
      | exact c2 _ (by decide) _ (by decide) | exact (c2 _ (by decide) _ (by decide)).symm
      | exact c4 _ (by decide) _ (by decide) | exact (c4 _ (by decide) _ (by decide)).symm
      | exact c44 _ (by decide) _ (by decide) | exact (c44 _ (by decide) _ (by decide)).symm

/-- **Open: a seventh orbit.**  Some seven nonnegative integers lie on pairwise distinct
orbits.  Nobody can prove this: beyond the five known cycles and the orbit of `8`, separating
any further orbit means showing a number never meets the orbit of `8`, and Conway (2013,
Appendix 1) notes that `8` and `14` might share an orbit.  Its negation says the orbit of `8`
together with the known cycles is all of `ℕ`, so the orbit of `8` would have density `1`.
Implied by `AmusicalInfinitelyManyOrbits`.  Proved: it holds unless the orbit of `8` is
infinite (`atLeastSeven_or_orbitEight_infinite` in `AmusicalChains.lean`). -/
def AmusicalAtLeastSevenOrbits : Prop :=
  ∃ s : Finset ℤ, s.card = 7 ∧ (∀ x ∈ s, 0 ≤ x) ∧
    (s : Set ℤ).Pairwise fun a b => amusicalOrbit a ≠ amusicalOrbit b

/-! ## The adelic picture (closed: restates mass conservation)

Each branch of `U` scales the archimedean place by `3/2^a`, the `2`-adic place by `2^a` and the
`3`-adic place by `1/3`, so `U` extends to a Haar-preserving piecewise-affine bijection of
`ℝ × ℤ₂ × ℤ₃` in which `ℤ` is a covolume-`1` lattice.  This only restates
`amusical_mass_conservation`; almost every point drifts off in both time directions (no
recurrence to exploit), and in the quotient by `ℤ` every integer becomes the fixed point `0`,
so `×2 ×3`-rigidity theorems see nothing of the integer orbits (agent report 2026-10-13). -/

/-- The product formula on each branch: `|r|_∞ · |r|_2 · |r|_3 = 1` for `r = 3/2` and `3/4`. -/
theorem amusical_branch_product_formula :
    padicNorm 2 (3 / 2 : ℚ) * padicNorm 3 (3 / 2) * (3 / 2) = 1 ∧
      padicNorm 2 (3 / 4 : ℚ) * padicNorm 3 (3 / 4) * (3 / 4) = 1 := by
  have h2 : padicNorm 2 (2 : ℚ) = 1 / 2 := by simpa using padicNorm.padicNorm_p_of_prime (p := 2)
  have h3 : padicNorm 3 (3 : ℚ) = 1 / 3 := by simpa using padicNorm.padicNorm_p_of_prime (p := 3)
  have h23 : padicNorm 2 (3 : ℚ) = 1 := by
    simpa using padicNorm.padicNorm_of_prime_of_ne (p := 2) (q := 3) (by norm_num)
  have h32 : padicNorm 3 (2 : ℚ) = 1 := by
    simpa using padicNorm.padicNorm_of_prime_of_ne (p := 3) (q := 2) (by norm_num)
  have h4 : (4 : ℚ) = 2 * 2 := by norm_num
  refine ⟨?_, ?_⟩
  · rw [padicNorm.div, padicNorm.div, h2, h3, h23, h32]; norm_num
  · rw [padicNorm.div, padicNorm.div, h4, padicNorm.mul, padicNorm.mul, h2, h3, h23, h32]
    norm_num

/-- **Klamkin (a) or an infinite orbit.**  If every orbit on `ℕ` were finite, the orbits would
be infinitely many finite cycles.  (For the wider class of permutational maps Lagarias records
that even the existence of one infinite orbit is open: annotated bibliography 2003, entry on
Venturini 1992.) -/
theorem amusicalInfinitelyManyOrbits_or_exists_infinite :
    AmusicalInfinitelyManyOrbits ∨ ∃ x : ℤ, 0 ≤ x ∧ (amusicalOrbit x).Infinite := by
  by_contra h
  simp only [not_or, not_exists, not_and, Set.not_infinite, AmusicalInfinitelyManyOrbits] at h
  obtain ⟨hS, hfin⟩ := h
  have hU : (⋃₀ {O : Set ℤ | ∃ x : ℤ, 0 ≤ x ∧ O = amusicalOrbit x}).Finite := by
    refine hS.sUnion ?_
    rintro _ ⟨x, hx, rfl⟩
    exact hfin x hx
  apply Set.Ici_infinite (0 : ℤ)
  refine hU.subset fun x hx => ?_
  exact ⟨amusicalOrbit x, ⟨x, hx, rfl⟩, mem_amusicalOrbit_self x⟩

end CollatzMoonshot.Obstructions.Amusical
