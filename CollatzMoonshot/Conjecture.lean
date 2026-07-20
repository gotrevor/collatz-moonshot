/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.Basic

/-!
# The conjecture, its trivial disjunction, and the two-front split

`Conjecture` is the Collatz conjecture.  Per the approach map (`APPROACHES.md`,
barrier 1), the proof will almost certainly be TWO proofs, so the two fronts get
their own named `Prop`s:

* `NoDivergentOrbit` - the divergence front, where ergodic/statistical/structural
  methods live (and where `3x+1` and `3x-1` behave alike);
* `NoNontrivialCycle` - the cycle front, where the arithmetic lives (Baker,
  S-units, the continued fraction of `log₂ 3`) and where `+1` vs `-1` is visible.

`conjecture_iff_split` wires them together: the conjecture is exactly the
conjunction of the two fronts.  That equivalence is finite mathematics (pigeonhole
plus the trivial cycle), proved here with no axioms beyond the classical trio -
the first of the "wiring theorems, provable now" the approach map calls for.
-/

namespace CollatzMoonshot

/-- **The Collatz conjecture**: every positive integer's orbit reaches `1`. -/
def Conjecture : Prop := ∀ n, 1 ≤ n → ReachesOne n

/-- The orbit of `n` is unbounded. -/
def Diverges (n : ℕ) : Prop := ∀ M, ∃ k, M ≤ step^[k] n

/-- `n` lies on a cycle of the Collatz map. -/
def OnCycle (n : ℕ) : Prop := ∃ m, 0 < m ∧ step^[m] n = n

/-- **Front A (divergence)**: no positive orbit is unbounded.  Believed true for
`3x+1` and `3x-1` alike; this is the front where statistical and rigidity methods
apply, and a purely statistical proof of it would be no scandal (barrier 1 bites
the *cycle* front, not this one). -/
def NoDivergentOrbit : Prop := ∀ n, 1 ≤ n → ¬Diverges n

/-- **Front B (cycles)**: the only positive cycle is the trivial `1 → 4 → 2 → 1`.
False for `3x-1` (which has the cycles through `5` and `17`), so any proof must
consume `+1`-specific arithmetic - this is Baker/transcendence territory. -/
def NoNontrivialCycle : Prop := ∀ n, 1 ≤ n → OnCycle n → n = 1 ∨ n = 2 ∨ n = 4

/-- **Collatz or not Collatz** - decided, content-free, by the law of the excluded
middle.  A smoke test that `Conjecture` elaborates, and a wink at the logician's
ledger: `#print axioms conjecture_or_not` reports `Classical.choice` (Lean's `em`
comes from choice via Diaconescu).  The rest of this repo is about which disjunct. -/
theorem conjecture_or_not : Conjecture ∨ ¬Conjecture := Classical.em _

/-- A value that is both on a cycle and reaches `1` lies on THE trivial cycle.
(Reduce the arrival time mod the period; the whole cycle is then inside the
forward orbit of `1`.  No positivity hypothesis needed: `0` is on a cycle but
never reaches `1`.) -/
theorem eq_trivial_of_onCycle_of_reachesOne {n : ℕ} (hc : OnCycle n)
    (hr : ReachesOne n) : n = 1 ∨ n = 2 ∨ n = 4 := by
  obtain ⟨m, hm, hcyc⟩ := hc
  obtain ⟨k, hk⟩ := hr
  have key : step^[k % m] n = 1 := by
    have hfix : step^[m * (k / m)] n = n := by
      rw [Function.iterate_mul]
      exact Function.iterate_fixed hcyc (k / m)
    have h : step^[k % m + m * (k / m)] n = 1 := by rwa [Nat.mod_add_div]
    rwa [Function.iterate_add_apply, hfix] at h
  have hmod : k % m < m := Nat.mod_lt _ hm
  have hn14 : n = step^[m - k % m] 1 := by
    calc n = step^[m] n := hcyc.symm
    _ = step^[m - k % m + k % m] n := by rw [Nat.sub_add_cancel hmod.le]
    _ = step^[m - k % m] (step^[k % m] n) := Function.iterate_add_apply step _ _ n
    _ = step^[m - k % m] 1 := by rw [key]
  rcases iterate_one_mem (m - k % m) with h | h | h <;> rw [h] at hn14 <;> omega

/-- If an orbit repeats a value, `NoNontrivialCycle` pushes it into the trivial
cycle, and the whole orbit reaches `1`. -/
theorem reachesOne_of_orbit_repeat (hnc : NoNontrivialCycle) {n i j : ℕ} (hn : 1 ≤ n)
    (hlt : i < j) (heq : step^[i] n = step^[j] n) : ReachesOne n := by
  have hpp : 1 ≤ step^[i] n := iterate_step_pos hn i
  have hcyc : step^[j - i] (step^[i] n) = step^[i] n := by
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hlt.le]
    exact heq.symm
  have h14 := hnc _ hpp ⟨j - i, by omega, hcyc⟩
  have hpr : ∃ c, step^[c] (step^[i] n) = 1 := by
    rcases h14 with h | h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by rw [h]; decide⟩
    · exact ⟨2, by rw [h]; decide⟩
  obtain ⟨c, hc⟩ := hpr
  exact ⟨c + i, by rw [Function.iterate_add_apply]; exact hc⟩

/-- **The two-front decomposition**: the Collatz conjecture is exactly "no divergent
orbits" AND "no nontrivial cycles".  Finite mathematics (bounded orbits repeat by
pigeonhole; repeats are cycles; cycles that reach `1` are trivial), no axioms
beyond the classical trio - the wiring theorem that makes the two fronts an honest
partition of the problem. -/
theorem conjecture_iff_split : Conjecture ↔ NoDivergentOrbit ∧ NoNontrivialCycle := by
  constructor
  · intro hC
    refine ⟨?_, ?_⟩
    · -- A conjectured world has no divergent orbits: past the arrival time the
      -- orbit lives in the trivial cycle, so the whole orbit is bounded.
      rintro n hn hdiv
      obtain ⟨k₀, hk₀⟩ := hC n hn
      obtain ⟨j, hj⟩ := hdiv ((Finset.range (k₀ + 1)).sup (fun i => step^[i] n) + 5)
      rcases Nat.lt_or_ge k₀ j with h | h
      · have hsplit : step^[j] n = step^[j - k₀] (step^[k₀] n) := by
          rw [← Function.iterate_add_apply, Nat.sub_add_cancel h.le]
        rw [hk₀] at hsplit
        rcases iterate_one_mem (j - k₀) with h1 | h1 | h1 <;> rw [h1] at hsplit <;> omega
      · have hmem : j ∈ Finset.range (k₀ + 1) := Finset.mem_range.mpr (by omega)
        have hle : step^[j] n ≤ (Finset.range (k₀ + 1)).sup (fun i => step^[i] n) :=
          Finset.le_sup (f := fun i => step^[i] n) hmem
        omega
    · intro n hn hc
      exact eq_trivial_of_onCycle_of_reachesOne hc (hC n hn)
  · -- Bounded (non-divergent) orbits repeat a value by pigeonhole; a repeat is a
    -- cycle; `NoNontrivialCycle` makes it the trivial one, which reaches `1`.
    rintro ⟨hnd, hnc⟩ n hn
    have hb : ∃ M, ∀ k, step^[k] n < M := by
      have h := hnd n hn
      unfold Diverges at h
      push Not at h
      exact h
    obtain ⟨M, hM⟩ := hb
    obtain ⟨i, j, hij, hfeq⟩ :=
      Finite.exists_ne_map_eq_of_infinite (fun k : ℕ => (⟨step^[k] n, hM k⟩ : Fin M))
    have heq : step^[i] n = step^[j] n := by simpa using hfeq
    rcases Nat.lt_trichotomy i j with hlt | heq' | hlt
    · exact reachesOne_of_orbit_repeat hnc hn hlt heq
    · exact absurd heq' hij
    · exact reachesOne_of_orbit_repeat hnc hn hlt heq.symm

end CollatzMoonshot
