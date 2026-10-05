/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanLedger.MazeLinks
import CollatzMoonshot.Sibling
import CollatzMoonshot.Literature.LocalRank
import CollatzMoonshot.Obstructions.BoundedMerger
import CollatzMoonshot.Obstructions.CoefficientRay
import CollatzMoonshot.Obstructions.Q1Coalescence
import CollatzMoonshot.Obstructions.RayRefill
import CollatzMoonshot.Obstructions.NegativeShadow
import CollatzMoonshot.Obstructions.LocalGlobalBorrow23
import CollatzMoonshot.Obstructions.BorrowabilityHeight23
import CollatzMoonshot.Obstructions.SignedFlow
import CollatzMoonshot.FrontA.BallotCoalescenceWitness
import CollatzMoonshot.FrontA.FirstCrossingResidue
import CollatzMoonshot.Benchmark.FlattoCeiling
import CollatzMoonshot.Obstructions.ParityWordGenericity

/-!
# `Maze.lean`: the closed routes, as Lean data

A register of routes this repo has walked and closed, so a later session recognises a hall
before re-entering it.  Each row's verdict cites declarations through `mazeLinks`, and
`#maze_audit` (shared, `lean-agent-skills/lean`) fails the build on a row outside `mazeLegacy`
whose reasons are prose only.  Names are ``` ``Foo.bar ``` literals, so a renamed or deleted
obstruction breaks this file.

**Adding a row:** state its obstruction in Lean first (a theorem, a `¬`, a `sorry` statement with
a confidence, or a cited `Literature` Prop); for a `wall`, also its reopen condition as a
`def … : Prop`.  Then add the `Link`.

Not a status file (`STATUS.md`) and not a plan (`DIRECTION.md`).  Rows are never deleted: a
reopened hall keeps its row and gains a note.
-/

namespace CollatzMoonshot.Maze

open LeanLedger

/-! ## 1. The gates

Most closed routes here failed one of three gates, each recognisable before the work. -/

/-- The shape of a closed route. -/
inductive Verdict where
  /-- **2-ADIC ADVERSARY.** The method reads a bounded amount of the orbit (bounded time, a
  bounded window of digits, a bounded signature), so an infinite 2-adic / 3-adic residue class
  agrees with a good start on everything it reads.
  🚨 Tell: the certificate depends on finitely many residues of `n`.  Terras–Everett cylinders
  (`BoundedMerger.crt_no_bounded_smaller_merge`) defeat it. -/
  | adversary2adic
  /-- **SIBLING TRANSFER.** The method also "works" for a map where convergence is known to
  fail: 3x−1 at 5, or 5x+1 at 13.
  🚨 Tell: no step consumes the drift `log(3/4) < 0` or the size of `|2^m − 3^k|`.  Run the
  method on `Sibling.T 3 (-1)` at 5 before building on it. -/
  | siblingTransfer
  /-- **DENSITY ≠ ALL.** The method proves a statement for almost every `n` (natural, log, or
  logarithmic density), and the target needs every `n`.
  🚨 Tell: an averaging or counting step whose error term is a density. -/
  | densityNotAll
  /-- **COSTUME.** The criterion is logically equivalent to a front (A: no divergence,
  B: no cycles, or the full conjecture).
  🚨 Tell: you cannot name a proof route for the criterion that avoids the front. -/
  | costume
  /-- **REFUTED.** A counterexample or a computation kills the mechanism. -/
  | refuted
  /-- **WALL.** Sound, and needs an input nobody has; parked with a named reopen condition. -/
  | wall
  deriving DecidableEq, Repr

/-- One walked hall. -/
structure Hall where
  /-- Short name, in the repo's vocabulary. -/
  name : String
  /-- The shape of the closure. -/
  verdict : Verdict
  /-- Why it closed, one sentence. -/
  mechanism : String
  /-- File pointer. -/
  evidence : String
  /-- ISO date of the verdict. -/
  date : String
  deriving Repr

/-! ## 2. Reopen conditions -/

/-- Reopens the certificate-repair toolkit: a method that names its distinguishing input.
`Φ q c` is the input the method consumes (e.g. the drift, or the size of `|2^m − 3^k|`); it must
hold for 3x+1 and **fail** for both sibling controls, 3x−1 and 5x+1, and wherever it holds the
method must deliver a well-founded rank decreasing along `T_{q,c}` above 1. -/
def DistinguishingRepairRank : Prop :=
  ∃ Φ : ℤ → ℤ → Prop, Φ 3 1 ∧ ¬ Φ 3 (-1) ∧ ¬ Φ 5 1 ∧
    ∀ q c, Φ q c → ∃ (α : Type) (r : α → α → Prop), WellFounded r ∧
      ∃ rank : ℤ → α, ∀ n : ℤ, 1 < n → r (rank (Sibling.T q c n)) (rank n)

/-- Reopens the local-rank row: a ranking function outside both peer barriers, growing without
bound relative to `log₂ n` (so not `log₂ n + bounded`), that decreases at every step. -/
def UnboundedRelativeRank : Prop :=
  ∃ P : ℕ → ℝ, (¬ ∃ B, ∀ n, |P n| ≤ B) ∧
    ∀ n : ℕ, 1 < n → Real.logb 2 ((CollatzMoonshot.FrontB.tstep n : ℕ) : ℝ) +
      P (CollatzMoonshot.FrontB.tstep n) < Real.logb 2 (n : ℝ) + P n

/-! ## 3. The register -/

/-- Every closed route. -/
def register : List Hall := [
  ⟨"bounded smaller-seed merger", .adversary2adic,
   "a start in a simultaneous 2^K/3^K cylinder meets no smaller seed within K steps",
   "Obstructions/BoundedMerger.lean; RESEARCH-2026-09-29-bounded-small-merger.md", "2026-09-29"⟩,
  ⟨"coefficient-ray signature rank", .refuted,
   "the ray signatures 72·3^j carry an infinite descending edge chain, so no rank on them is well-founded",
   "Obstructions/CoefficientRay.lean", "2026-09-29"⟩,
  ⟨"Q1 coalescence of the cubic pair", .adversary2adic,
   "the cubic N and Q1 orbits are ordered-separated for any bounded time window",
   "Obstructions/Q1Coalescence.lean; RESEARCH-2026-09-29-q1-coalescence.md", "2026-09-29"⟩,
  ⟨"ray refill", .adversary2adic,
   "each refill consumes 6k binary digits of fuel that a bounded lookahead cannot supply",
   "Obstructions/RayRefill.lean; RESEARCH-2026-09-29-ray-refill-hard-lift.md", "2026-09-29"⟩,
  ⟨"certificate-repair toolkit (map controls)", .siblingTransfer,
   "supply, exchanges and scalar certificates all exist for 3x-1 at its cycle start 5",
   "Sibling.lean; RESEARCH-2026-09-29-map-controls.md", "2026-09-29"⟩,
  ⟨"locally computed rank", .wall,
   "automaton-computed digit ranks and log n + bounded corrections are excluded by peers",
   "Literature/LocalRank.lean; RESEARCH-2026-10-05-rewriting-lane-landscape.md", "2026-10-05"⟩,
  ⟨"negative-shadow score", .refuted,
   "weighted scores on the inverse basin of -1 are unbounded",
   "Obstructions/NegativeShadow.lean", "2026-09-27"⟩,
  ⟨"local-global borrowing at 23", .refuted,
   "every prime power has small companions, yet no integer companion exists below 23",
   "Obstructions/LocalGlobalBorrow23.lean", "2026-09-29"⟩,
  ⟨"quadratic borrowability height at 23", .refuted,
   "no strict quadratic height descent exists at 23",
   "Obstructions/BorrowabilityHeight23.lean", "2026-09-28"⟩,
  ⟨"signed flow as a new lever", .costume,
   "a signed flow from n to 1 exists iff n reaches 1",
   "Obstructions/SignedFlow.lean", "2026-09-29"⟩,
  ⟨"ballot-coalescence rigidity", .refuted,
   "two ballot words of one shape do coalesce (witness at length 34)",
   "FrontA/BallotCoalescenceWitness.lean", "2026-09-19"⟩,
  ⟨"first-crossing word periodicity", .refuted,
   "a first-crossing word is never a proper power, and the overshoot is one congruence mod D",
   "FrontA/FirstCrossingResidue.lean", "2026-09-22"⟩,
  ⟨"P_6 prefix-admission certificate for every L", .refuted,
   "a padded primitive Q=2 family is admitted by P_6 at unbounded length",
   "PREFIX-ADMISSION-OBSTRUCTION-2026-09-13.md", "2026-09-13"⟩,
  ⟨"Round A run bookkeeping", .wall,
   "the run admission equations carry one congruence (det D); multiplying run bounds loses magnitude",
   "RESEARCH-2026-09-22-mechanism-search.md", "2026-09-22"⟩,
  ⟨"coalescence / smaller-start reduction", .refuted,
   "measured zero gain at the stopping-time records",
   "DIRECTION.md 2026-09-19", "2026-09-19"⟩,
  ⟨"Hercher 2023 transfer", .wall,
   "his 68 -> 91 gain is the orbit-merging lemma, which needs a closed orbit",
   "DIRECTION.md 2026-09-19", "2026-09-19"⟩,
  ⟨"Christoffel-word residue signatures", .refuted,
   "probed, none found", "DIRECTION.md 2026-09-19", "2026-09-19"⟩,
  ⟨"minimal-counterexample suffix constraints", .costume,
   "all run starts lie above the least failure (circular)",
   "RESEARCH-2026-09-22-mechanism-search.md", "2026-09-22"⟩,
  ⟨"ballot-residue discrepancy", .densityNotAll,
   "needs exact count 0; every counting bound stops at error ~ sqrt|B_m|",
   "RESEARCH-2026-09-22-mechanism-search.md", "2026-09-22"⟩,
  ⟨"richer matrix interpretations of the rewriting system", .wall,
   "barred by Nashida Part II (non-negative affine matrix interpretations)",
   "RESEARCH-2026-10-05-rewriting-lane-landscape.md", "2026-10-05"⟩,
  ⟨"within-horizon refinement of Flatto's Z-number count", .adversary2adic,
   "a start g < 2^n fixes only its first n parities, every residue class is realized, and at least (3/2)^n itineraries are admissible, so the count stays at X^(log2 3/2)",
   "Benchmark/FlattoCeiling.lean; RESEARCH-2026-10-05-g2-hunt-and-flatto-ceiling.md", "2026-10-05"⟩,
  ⟨"normality of a divergent orbit's parity word", .refuted,
   "the raw word never contains 11, and the shortcut word's 1-density is forced to at least log 2 / log 3 > 1/2",
   "Obstructions/ParityWordGenericity.lean; APPROACHES.md", "2026-09-20"⟩,
  ⟨"disjunctivity of a divergent orbit's parity word", .wall,
   "open, and it implies arbitrarily long odd runs, so it is a stronger target than the run question it was meant to serve",
   "Obstructions/ParityWordGenericity.lean; APPROACHES.md", "2026-09-20"⟩,
  ⟨"irrationality of the parity real", .costume,
   "irrational iff the shortcut parity word is not eventually periodic, which divergence already forces",
   "Obstructions/ParityWordGenericity.lean; FrontA/ParityReconstruction.lean", "2026-09-20"⟩,
  ⟨"transcendence of the parity real via Adamczewski-Bugeaud", .wall,
   "the criterion needs linear factor complexity (the Sturmian end), which nothing about divergence forces",
   "Obstructions/ParityWordGenericity.lean; DIRECTION.md 2026-09-19", "2026-09-20"⟩]

/-! ## 4. The audit -/

/-- The audit's view: every `wall` row needs a reopen condition. -/
def mazeRows : List RowInfo :=
  register.map fun h => ⟨h.name, decide (h.verdict = Verdict.wall)⟩

open CollatzMoonshot.Obstructions CollatzMoonshot.Obstructions.ArithmeticLifts
  CollatzMoonshot.Obstructions.ArithmeticLifts.RestrictedRepair in
/-- Each linked row and the declarations it rests on. -/
def mazeLinks : List Link := [
  ⟨"bounded smaller-seed merger",
   [``BoundedMerger.crt_no_bounded_smaller_merge,
    ``BoundedMerger.arbitrarily_large_no_bounded_smaller_merge], []⟩,
  ⟨"coefficient-ray signature rank", [``no_uniform_ray_rank, ``ray_edge_exists], []⟩,
  ⟨"Q1 coalescence of the cubic pair", [``cubicN_q1_no_bounded_pairwise_meeting], []⟩,
  ⟨"ray refill", [``refill0_fuel], []⟩,
  ⟨"certificate-repair toolkit (map controls)",
   [``Sibling.threeMinus_cycle_five, ``Sibling.threeMinus_five_ne_one,
    ``Sibling.threeMinus_certificate_five, ``Sibling.fivePlus_cycle_thirteen,
    ``Sibling.unit_two_count_controls], [``DistinguishingRepairRank]⟩,
  ⟨"locally computed rank",
   [``Literature.NashidaPositiveAutomatonBarrier, ``Literature.KadirbekovBoundedCorrection,
    ``BoundedMerger.crt_no_bounded_smaller_merge], [``UnboundedRelativeRank]⟩,
  ⟨"negative-shadow score", [``NegativeShadow.inverse_basin_scores_unbounded], []⟩,
  ⟨"local-global borrowing at 23",
   [``each_prime_power_has_small_inputs_23, ``no_global_small_inputs_23], []⟩,
  ⟨"quadratic borrowability height at 23", [``no_strict_quadratic_height_descent_23], []⟩,
  ⟨"signed flow as a new lever", [``SignedFlow.exists_signed_flow_iff_reachesOne], []⟩,
  ⟨"ballot-coalescence rigidity", [``FrontA.FirstCrossing.not_ballot_ancestor_unique], []⟩,
  ⟨"first-crossing word periodicity",
   [``FrontA.FirstCrossing.at_primitive, ``FrontA.FirstCrossing.overshoot_modEq], []⟩,
  ⟨"within-horizon refinement of Flatto's Z-number count",
   [``Benchmark.FlattoCeiling.parityWord_injective,
    ``Benchmark.FlattoCeiling.zNumber_parityWord_admissible,
    ``Benchmark.FlattoCeiling.card_admissible_starts_ge], []⟩,
  ⟨"normality of a divergent orbit's parity word",
   [``Obstructions.ParityWord.rawWord_not_normal,
    ``Obstructions.ParityWord.accWord_not_normal_of_diverges], []⟩,
  ⟨"disjunctivity of a divergent orbit's parity word",
   [``Obstructions.ParityWord.divergentWordDisjunctive_imp_longOddRuns],
   [``Obstructions.ParityWord.DivergentWordDisjunctive]⟩,
  ⟨"irrationality of the parity real",
   [``Obstructions.ParityWord.irrational_parityReal_accWord,
    ``Obstructions.ParityWord.accWord_not_eventuallyPeriodic], []⟩,
  ⟨"transcendence of the parity real via Adamczewski-Bugeaud",
   [``Literature.AdamczewskiBugeaud2007,
    ``Obstructions.ParityWord.transcendental_parityReal_of_lowComplexity],
   [``Obstructions.ParityWord.DivergentWordLowComplexity]⟩]

/-- Rows whose reasons are still prose only (as of 2026-10-05).  Only shrinks. -/
def mazeLegacy : List String := [
  "P_6 prefix-admission certificate for every L",
  "Round A run bookkeeping",
  "coalescence / smaller-start reduction",
  "Hercher 2023 transfer",
  "Christoffel-word residue signatures",
  "minimal-counterexample suffix constraints",
  "ballot-residue discrepancy",
  "richer matrix interpretations of the rewriting system"]

/-- info: maze audit: 25 rows, 17 cite declarations, 8 legacy (prose only) -/
#guard_msgs in
#maze_audit mazeRows, mazeLinks, mazeLegacy

end CollatzMoonshot.Maze
