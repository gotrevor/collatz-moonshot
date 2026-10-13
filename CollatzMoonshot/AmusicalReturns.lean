/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Obstructions.Amusical

/-!
# Returns, exits and residues: witnesses for the closed amusical routes

Statements from the 2026-10-13 research agents (reports in `RESEARCH-2026-10-13-amusical-
single-chain.md` §7), each proved on paper there.  Treadmill target
(`KICKOFF-2026-10-13-amusical-returns.md`): close every `sorry` in this file.

* `exists_large_nonOrbitMin`: every residue class mod `2^k 3^l` contains arbitrarily large
  non-minima, so no congruence certifies an orbit minimum (the provable half of
  `MinimaNotResidueDetermined`).
* `exits_eq_strictMinima`: the points of `[1, X]` that never come back are exactly as many as the
  strict orbit minima in `[1, X]` (true for any such bijection, so not a lever by itself).
* `exists_denseLinearReturns_of_finitelyManyOrbits`: the strongest form of the linear-recurrence
  reduction.
* `return_defect_bound`: at a return the linear form `n log 2 − j log 3 + log(y/x)` is only
  `O(log j)`, not small, which is why Baker-type bounds give nothing.
-/

namespace CollatzMoonshot.Amusical

/-- **Target.**  Every residue class mod `2^k 3^l` has arbitrarily large non-minima.  Paper
proof: by CRT choose `n` in the class whose 2-adic digits after the forced prefix make the next
`K` steps all of type `4m+1 ↦ 3m+1`, which contracts toward `1`; for `K` large compared with the
prefix length the orbit drops below `n`. -/
theorem exists_large_nonOrbitMin (k l c T : ℕ) :
    ∃ n : ℕ, T < n ∧ n ≡ c [MOD 2 ^ k * 3 ^ l] ∧ ¬ IsOrbitMin (n : ℤ) := by
  sorry

open Classical in
/-- **Target.**  Exits equal strict minima: each infinite orbit meeting `[1, X]` has exactly one
last forward visit there and exactly one strict minimum there; cycles have neither. -/
theorem exits_eq_strictMinima (X : ℕ) :
    ((Finset.Icc 1 X).filter fun n : ℕ =>
        ∀ j : ℕ, 0 < j → (X : ℤ) < (amusicalPerm ^ (j : ℤ)) n).card =
      ((Finset.Icc 1 X).filter fun n : ℕ =>
        ∀ j : ℤ, j ≠ 0 → (n : ℤ) < (amusicalPerm ^ j) n).card := by
  sorry

open Classical in
/-- **Target.**  The strong form of the linear-recurrence reduction: finitely many orbits give an
infinite orbit with, for infinitely many `X`, at least `εX/2 − 1` times `j` with `|j| ≥ εX/4`
and value in `[0, X)`.  Equivalent to positive upper density of that orbit. -/
theorem exists_denseLinearReturns_of_finitelyManyOrbits (h : ¬ AmusicalInfinitelyManyOrbits) :
    ∃ x : ℤ, 0 ≤ x ∧ (amusicalOrbit x).Infinite ∧ ∃ ε : ℝ, 0 < ε ∧
      ∃ᶠ X : ℕ in Filter.atTop, ∃ S : Finset ℤ, ε * X / 2 - 1 ≤ S.card ∧
        ∀ j ∈ S, ε * X / 4 ≤ |(j : ℝ)| ∧ 0 ≤ (amusicalPerm ^ j) x ∧
          (amusicalPerm ^ j) x < X := by
  have hz : ¬ AmusicalOrbitsZeroDensity := fun hz =>
    h (amusicalInfinitelyManyOrbits_of_zeroDensity hz)
  simp only [AmusicalOrbitsZeroDensity, not_forall] at hz
  obtain ⟨x, hx0, hnt⟩ := hz
  set f : ℕ → ℝ := fun X =>
    (((Finset.range X).filter fun n : ℕ => (n : ℤ) ∈ amusicalOrbit x).card : ℝ) / X with hf
  have hf0 : ∀ X, 0 ≤ f X := fun X => by positivity
  obtain ⟨ε, hε, hfreq⟩ : ∃ ε : ℝ, 0 < ε ∧ ∃ᶠ X in Filter.atTop, ε ≤ f X := by
    by_contra hne
    push Not at hne
    apply hnt
    rw [tendsto_order]
    refine ⟨fun a ha => Filter.Eventually.of_forall fun X => lt_of_lt_of_le ha (hf0 X), ?_⟩
    intro a ha
    simpa [Filter.not_frequently, not_le] using hne a ha
  refine ⟨x, hx0, ?_, ε, hε, ?_⟩
  · intro hfin
    set N := hfin.toFinset.card
    have hbound : ∀ X,
        ((Finset.range X).filter fun n : ℕ => (n : ℤ) ∈ amusicalOrbit x).card ≤ N := by
      intro X
      refine Finset.card_le_card_of_injOn (fun n : ℕ => (n : ℤ)) ?_ ?_
      · intro n hn
        simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hn
        simpa using hn.2
      · intro a _ b _ hab; simpa using hab
    have hlim : ∀ᶠ X : ℕ in Filter.atTop, f X < ε := by
      have ht : Filter.Tendsto (fun X : ℕ => (N : ℝ) / X) Filter.atTop (nhds 0) :=
        tendsto_const_div_atTop_nhds_zero_nat _
      filter_upwards [ht.eventually (gt_mem_nhds hε), Filter.eventually_ge_atTop 1] with X hX hX1
      refine lt_of_le_of_lt ?_ hX
      have hXpos : (0 : ℝ) < X := by exact_mod_cast hX1
      exact div_le_div_of_nonneg_right (by exact_mod_cast hbound X) hXpos.le
    exact (hfreq.and_eventually hlim).exists.elim fun X hX => absurd hX.1 (not_le.2 hX.2)
  · refine (hfreq.and_eventually (Filter.eventually_ge_atTop 1)).mono ?_
    rintro X ⟨hXε, hX1⟩
    have hXpos : (0 : ℝ) < X := by exact_mod_cast hX1
    set A := (Finset.range X).filter fun n : ℕ => (n : ℤ) ∈ amusicalOrbit x
    have hA : ε * X ≤ A.card := by
      have := hXε
      simp only [hf] at this
      rwa [le_div_iff₀ hXpos] at this
    let g : ℕ → ℤ := fun n =>
      if hn : (n : ℤ) ∈ amusicalOrbit x then Classical.choose hn else 0
    have hg : ∀ n ∈ A, (amusicalPerm ^ g n) x = n := by
      intro n hn
      have hn' : (n : ℤ) ∈ amusicalOrbit x := (Finset.mem_filter.1 hn).2
      simp only [g, dif_pos hn']
      exact Classical.choose_spec hn'
    have hginj : Set.InjOn g A := by
      intro a ha b hb hab
      have hab' := (hg a ha).symm.trans
        ((congrArg (fun j => (amusicalPerm ^ j) x) hab).trans (hg b hb))
      exact_mod_cast hab'
    set q : ℕ := Nat.ceil (ε * X / 4)
    have hqpos : 0 < q := by
      apply Nat.ceil_pos.2
      positivity
    set B := A.image g
    set S := B.filter fun j : ℤ => (q : ℤ) ≤ |j|
    refine ⟨S, ?_, ?_⟩
    · have hB : B.card = A.card := Finset.card_image_of_injOn hginj
      have hbad : (B.filter fun j : ℤ => ¬ (q : ℤ) ≤ |j|).card ≤ 2 * q - 1 := by
        calc
          _ ≤ (Finset.Icc (-(q : ℤ) + 1) ((q : ℤ) - 1)).card := by
            apply Finset.card_le_card
            intro z hz
            simp only [Finset.mem_filter, Finset.mem_Icc] at hz ⊢
            have hzabs : |z| < (q : ℤ) := by omega
            have hzrange := (abs_lt.mp hzabs)
            omega
          _ ≤ 2 * q - 1 := by
            rw [Int.card_Icc]
            omega
      have hsplit := Finset.card_filter_add_card_filter_not (s := B)
        (fun j : ℤ => (q : ℤ) ≤ |j|)
      have hq : (q : ℝ) < ε * X / 4 + 1 := Nat.ceil_lt_add_one (by positivity)
      have hcast : ((2 * q - 1 : ℕ) : ℝ) = 2 * (q : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ 2 * q)]
        push_cast
        rfl
      have hbadR : ((B.filter fun j : ℤ => ¬ (q : ℤ) ≤ |j|).card : ℝ) ≤
          ε * X / 2 + 1 := by
        have : ((B.filter fun j : ℤ => ¬ (q : ℤ) ≤ |j|).card : ℝ) ≤
            (2 * q - 1 : ℕ) := by exact_mod_cast hbad
        rw [hcast] at this
        linarith
      have hsplitR : (S.card : ℝ) +
          ((B.filter fun j : ℤ => ¬ (q : ℤ) ≤ |j|).card : ℝ) = B.card := by
        exact_mod_cast hsplit
      have hBR : (B.card : ℝ) = A.card := by exact_mod_cast hB
      linarith
    · intro j hj
      have hj' := Finset.mem_filter.1 hj
      obtain ⟨n, hnA, rfl⟩ := Finset.mem_image.1 hj'.1
      have hqceil : ε * X / 4 ≤ (q : ℝ) := Nat.le_ceil _
      have hqabs : ((q : ℤ) : ℝ) ≤ ((|g n| : ℤ) : ℝ) := by
        exact_mod_cast hj'.2
      have hn0 : 0 ≤ (n : ℤ) := by positivity
      have hnX : (n : ℤ) < X := by
        exact_mod_cast Finset.mem_range.1 (Finset.mem_filter.1 hnA).1
      rw [hg n hnA]
      refine ⟨?_, hn0, hnX⟩
      push_cast at hqabs ⊢
      exact hqceil.trans hqabs

/-- The 2-adic weight of the first `j` steps from `x`: `1` per even step, `2` per odd step, so
`U^j x ≈ 3^j x / 2^(stepWeight x j)`. -/
def stepWeight (x : ℤ) (j : ℕ) : ℕ :=
  ∑ i ∈ Finset.range j, if amusical^[i] x % 2 = 0 then 1 else 2

/-- **Target.**  The return defect: along an aperiodic orbit from `x ≥ 2`, odd steps multiply by
`(3/4)(1 ± 1/(3z))` with distinct `z ≥ 2`, so the linear form in `log 2`, `log 3` and
`log (U^j x / x)` is at most `Σ_{z=2}^{j+1} 1/(3z−1) ≤ (1/3) log((6j+7)/7)`. -/
theorem return_defect_bound {x : ℤ} (hx : 2 ≤ x) (hinf : (amusicalOrbit x).Infinite) (j : ℕ) :
    |(stepWeight x j : ℝ) * Real.log 2 - j * Real.log 3 +
        Real.log ((amusical^[j] x : ℝ) / x)| ≤ 1 / 3 * Real.log ((6 * j + 7) / 7) := by
  sorry

end CollatzMoonshot.Amusical
