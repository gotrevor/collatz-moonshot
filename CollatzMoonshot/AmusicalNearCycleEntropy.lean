/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalNearCycleRuns
import CollatzMoonshot.AmusicalNearCycleEntropy.Chernoff

/-!
# Stopped prefixes: run tightness at a logarithmic threshold (Theorem RT-low)

The 2026-10-14 "ncentropy" agent (research §40) pushed the run-stratum method of §38 from
`m ≲ √log D` runs to `m ≤ log₂ D / 40`.  It counts each near-cycle excursion only up to its
`τ`-th `E`-step, not over its whole parity pattern, so pattern entropy is paid on `O(log D)`
steps.

**`nearCycleAt_prefix_balance` (P2′).**  At an interior local minimum, reached after `A` `E`-steps,
`B` odd steps and `j` completed runs, `B log(4/3) < A log(3/2) + j / (p + D)`.  The orbit is
still above `p`, and each completed odd run carries `< 1 / (X − 1) ≤ 1 / (p + D)` (MR I's run
estimate).

**`sum_stoppedPrefixes_le` (NB).**  The fair-coin mass of the `E`/`O` patterns that start with `E`,
end at their `τ`-th `E` and use at most `k` `E`-runs is a binomial tail: attach to each of the first
`τ − 1` `E`'s the coin "the run stops here".

**`card_stoppedPrefixes_le`.**  A pattern is fixed by a composition of `τ` into its `E`-runs and
of its `O`-count into its `O`-runs.

**`sum_choose_le_exp_binEntropy`.**  Chernoff for the fair binomial lower tail.

**`ncard_deep_lowRun_le` (RT-low, unconditional).**  Near-cycle starts below `D (log₂ D)^14` with
return time `> 0.61 log₂ D` and at most `log₂ D / 40` runs number `O(D^0.87)`.  Each such start
follows a stopped prefix with `#O < 1.41 τ + 4` (P2′); the prefix fixes a residue class mod
`2^{τ + 2#O}`; sum NB and the pattern count over dyadic blocks.

With Rhin's bound as a hypothesis the agent also proves the same count above
`D (log₂ D)^14` (RT-log) and that LIN's density clause is equivalent to beyond-horizon
negligibility.  Those are recorded in research §40.
-/

namespace CollatzMoonshot.Amusical

/-- **Target (P2′, prefix balance).**  At an interior local minimum the odd steps so far cannot
outweigh the `E`-mass before them, up to one carry `1 / (p + D)` per completed run. -/
theorem nearCycleAt_prefix_balance {D p g t : ℕ} (h : NearCycleAt D p g) (hp : 2 ≤ p)
    (ht : 0 < t) (htg : t < g) (hO : Odd (amusical^[t - 1] (p : ℤ)))
    (hE : Even (amusical^[t] (p : ℤ))) :
    ((t - numE p t : ℕ) : ℝ) * Real.log (4 / 3) <
      (numE p t : ℝ) * Real.log (3 / 2) + (eRuns p t : ℝ) / (p + D) := by
  sorry

/-- The number of maximal `true`-runs of a list, each counted at its last element. -/
def trueRuns : List Bool → ℕ
  | [] => 0
  | b :: s => trueRuns s + if b = true ∧ s.head? ≠ some true then 1 else 0

/-- All `Bool` lists of length at most `n`. -/
def boolListsUpTo : ℕ → Finset (List Bool)
  | 0 => {[]}
  | n + 1 => insert [] ((boolListsUpTo n).biUnion fun s => {true :: s, false :: s})

/-- `E`/`O` patterns (`true` = `E`) that start with `E`, end at their `τ`-th `E`, have at most `k`
`E`-runs and at most `M` `O`'s. -/
def stoppedPrefixes (τ k M : ℕ) : Finset (List Bool) :=
  (boolListsUpTo (τ + M)).filter fun s =>
    s.head? = some true ∧ s.getLast? = some true ∧ s.count true = τ ∧ s.count false ≤ M ∧
      trueRuns s ≤ k

/-- **Target (NB).**  The stopped-prefix mass is a binomial tail. -/
theorem sum_stoppedPrefixes_le (τ k M : ℕ) (hτ : 1 ≤ τ) :
    ∑ s ∈ stoppedPrefixes τ k M, ((1 : ℝ) / 2) ^ s.length ≤
      ∑ j ∈ Finset.range k, ((τ - 1).choose j : ℝ) / 2 ^ τ := by
  sorry

/-- **Target.**  The pattern count. -/
theorem card_stoppedPrefixes_le (τ k M : ℕ) :
    (stoppedPrefixes τ k M).card ≤ ∑ i ∈ Finset.range k, (τ - 1).choose i * M.choose i := by
  sorry

/-- **Target (Chernoff).**  The fair binomial lower tail, with the natural-log entropy. -/
theorem sum_choose_le_exp_binEntropy (n j : ℕ) (hj : 2 * j ≤ n) :
    (∑ i ∈ Finset.range (j + 1), (n.choose i : ℝ)) ≤
      Real.exp (n * Real.binEntropy ((j : ℝ) / n)) :=
  NearCycleEntropy.sum_choose_le_exp n j hj

/-- **Target (RT-low).**  Deep run-poor near-cycle starts below `D (log₂ D)^14` are `O(D^0.87)`. -/
theorem ncard_deep_lowRun_le :
    ∃ C : ℝ, ∀ D : ℕ, 2 ≤ D →
      (({p : ℕ | (p : ℝ) ≤ D * Real.logb 2 D ^ 14 ∧ ∃ g, NearCycleAt D p g ∧
          0.61 * Real.logb 2 D < g ∧ (eRuns p g : ℝ) ≤ Real.logb 2 D / 40}).ncard : ℝ) ≤
        C * (D : ℝ) ^ (0.87 : ℝ) := by
  sorry

end CollatzMoonshot.Amusical
