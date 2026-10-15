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
import CollatzMoonshot.Obstructions.Amusical
import CollatzMoonshot.AmusicalReturns
import CollatzMoonshot.AmusicalChains
import CollatzMoonshot.AmusicalReversal
import CollatzMoonshot.AmusicalContinuousReversor
import CollatzMoonshot.AmusicalLogBalance
import CollatzMoonshot.AmusicalSeventh
import CollatzMoonshot.AmusicalTwin
import CollatzMoonshot.AmusicalEscape
import CollatzMoonshot.AmusicalWindowThree
import CollatzMoonshot.AmusicalGlobal
import CollatzMoonshot.AmusicalRewireRatio
import CollatzMoonshot.AmusicalAntiKohl
import CollatzMoonshot.AmusicalPingPong
import CollatzMoonshot.AmusicalUniform
import CollatzMoonshot.AmusicalCycleBound
import CollatzMoonshot.AmusicalFormalMin
import CollatzMoonshot.AmusicalLateDrops
import CollatzMoonshot.AmusicalFunctionField
import CollatzMoonshot.AmusicalTwinDegree
import CollatzMoonshot.AmusicalCrossing
import CollatzMoonshot.AmusicalAdelic
import CollatzMoonshot.AmusicalAdditive
import CollatzMoonshot.AmusicalUnit
import CollatzMoonshot.AmusicalDeform
import CollatzMoonshot.AmusicalOddRewire
import CollatzMoonshot.AmusicalNearCycle
import CollatzMoonshot.AmusicalNearCycleLaw
import CollatzMoonshot.AmusicalReglue
import CollatzMoonshot.AmusicalExcursionCode
import CollatzMoonshot.AmusicalNearCycleEntropy
import CollatzMoonshot.AmusicalSquares
import CollatzMoonshot.AmusicalSwap
import CollatzMoonshot.AmusicalTailEvent
import CollatzMoonshot.AmusicalLoopInterleave

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

/-! ## 0. Pre-flight for a new route (Klamkin (a), the amusical lane)

Every amusical route through research §46 ended at the same wall; `RESEARCH-…-single-chain.md` §47
maps it.  Before proposing a route, answer three questions.  A route that fails any of them is a
hall already walked.

1. **Which Π₁ statement does it reduce to?**  If the answer is a lower bound on forward survivors
   (`FS` density, LIN, BHN, NC₀, a confinement such as SRC) about integers beyond depth `log X`, it
   is the beyond-horizon wall (verdict `beyondHorizon`).  Name the new input that crosses the
   horizon, or drop the route.
2. **Which foil survives it?**  Run the route against `σ` (Theorem G), `τ` and `τ_odd`, the
   masquerade, `π` and `π_β` (Theorems Π, Πβ), the block-swap family `F_L` (`ampSwap`), and
   `U + 6^N`.  If any foil satisfies every hypothesis the route uses and fails its conclusion, the
   route is closed.
3. **Does it use `U`'s exact branch law along entire tails** (Theorem TT, `tail_threshold`)?  An
   argument whose inputs are all real-affine (`Û`), windowed, sparse-robust, or bounded-depth
   residues cannot separate `ℤ` from the masquerade.
-/

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
  /-- **BEYOND THE HORIZON (Π₁ wall).** The route is sound but reduces to a Π₁ statement about
  integers past the residue horizon (depth `> log X`): a survivor lower bound, LIN's tail (BHN), or
  a return confinement.  Counting, residues and geometry stop at the horizon.
  🚨 Tell: the last open step is "no integer below `X` follows these `≫ log X` branches", or
  "survivors are not sparse".  Amusical research §40–§47. -/
  | beyondHorizon
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
  ⟨"amusical: density, measure and crossing counts for Klamkin (a)", .siblingTransfer,
   "each count balances on ℕ, a union of infinitely many orbits, so cannot bound the orbit count",
   "Obstructions/Amusical.lean; RESEARCH-2026-10-13-amusical-single-chain.md", "2026-10-13"⟩,
  ⟨"amusical: Tavares zero-density reduction with Rhin bounds", .siblingTransfer,
   "decreasing points drop by up to (3/4)^N, swamping the Rhin gain; the bound holds for ℕ too",
   "Obstructions/Amusical.lean; RESEARCH-2026-10-13-amusical-single-chain.md", "2026-10-13"⟩,
  ⟨"amusical: forward/backward drift asymmetry", .refuted,
   "0.0589 vs 0.0566 is one balance in 2-adic and 3-adic density (evens below 2X/3, threes below X)",
   "Obstructions/Amusical.lean; RESEARCH-2026-10-13-amusical-single-chain.md", "2026-10-13"⟩,
  ⟨"amusical: orbit invariant or rational height for Klamkin (a)", .costume,
   "an invariant with infinitely many values on ℕ exists iff there are infinitely many orbits",
   "Obstructions/Amusical.lean; RESEARCH-2026-10-13-amusical-single-chain.md §1, §5",
   "2026-10-13"⟩,
  ⟨"amusical: residue certification of orbit minima", .adversary2adic,
   "a class fixes finitely many steps; minima show no class dependence beyond long windows",
   "Obstructions/Amusical.lean; RESEARCH-2026-10-13-amusical-single-chain.md §6", "2026-10-13"⟩,
  ⟨"amusical: single-chain mechanism for Klamkin (a)", .wall,
   "finitely many orbits force a linearly recurrent orbit; refuting it is the orbit-of-8 wall",
   "Amusical.lean; Obstructions/Amusical.lean; RESEARCH-2026-10-13-amusical-single-chain.md §3",
   "2026-10-13"⟩,
  ⟨"amusical: adelic volume preservation and ×2×3 rigidity", .siblingTransfer,
   "Haar on ℝ×ℤ₂×ℤ₃ is preserved (product formula), which is mass conservation; ℤ sits at 0",
   "Obstructions/Amusical.lean; agent report adelic.md (2026-10-13)", "2026-10-13"⟩,
  ⟨"amusical: Diophantine bounds on linear returns", .refuted,
   "the return form n log 2 - j log 3 + log(y/x) is O(log j), not small; sums have ~0.585j terms",
   "AmusicalReturns.lean; agent report diophantine.md (2026-10-13)", "2026-10-13"⟩,
  ⟨"amusical: chain-connectivity statistics (records, excursions, pairs)", .wall,
   "finite-step statistics agree in both worlds; the span bound gives only sublinear recurrence",
   "AmusicalChains.lean; agent report chains.md (2026-10-13)", "2026-10-13"⟩,
  ⟨"amusical: reversing involution (works for the Gaussian relative)", .refuted,
   "no piecewise-affine reversor (3-adic slope valuation drifts); a general one is the problem",
   "AmusicalReversal.lean; GaussianRelative.lean; agent report relative.md", "2026-10-13"⟩,
  ⟨"amusical: reversor determined by residues ((2,3)-adically continuous)", .refuted,
   "even-step frequencies are dyadic forward, triadic backward: no linear growth; one prime: const",
   "AmusicalContinuousReversor.lean; agent report reversor.md (2026-10-13)", "2026-10-13"⟩,
  ⟨"amusical: fat orbits equidistribute (ergodic theory on ℤ₂ × ℤ₃)", .refuted,
   "Haar is conformal, not invariant, and Û is totally dissipative; only ½/⅓ log balance survives",
   "AmusicalLogBalance.lean; agent report equidist.md (2026-10-13)", "2026-10-13"⟩,
  ⟨"amusical: basin counting: near-cycle sparsity forces many survivors", .siblingTransfer,
   "a one-orbit order-only permutation has finite near-cycle sets and o(√X) survivors",
   "AmusicalNearCycleLaw.lean; agent report basin.md (2026-10-14)", "2026-10-14"⟩,
  ⟨"amusical: rung constraints (quantized ladder SQ) lower the survivor ceiling below c",
   .siblingTransfer,
   "SQ, Kraft and Lemma K hold on every real Û-orbit; the one-orbit masquerade attains c",
   "AmusicalNearCycle.lean; AmusicalSurvivorCeiling.lean; agent report sqceiling.md (2026-10-14)",
   "2026-10-14"⟩,
  ⟨"amusical: odd-branch agreement off a sparse set (any agreement set short of whole tails)",
   .siblingTransfer,
   "rewiring U on a set S meeting every chain late and early fuses all chains (Theorem TT)",
   "AmusicalOddRewire.lean; agent report oddbranch.md (2026-10-14)", "2026-10-14"⟩,
  ⟨"amusical: seventh orbit from density, window or crossing statistics", .siblingTransfer,
   "U rewired on a density-0 set has the same statistics and only the cycles plus one orbit",
   "AmusicalSeventh.lean; agent report seventh.md (2026-10-13)", "2026-10-13"⟩,
  ⟨"amusical: statistical twin with finitely many orbits", .costume,
   "a no-go for twins applies to U itself; twins differ in cycles (twin W has a 3-cycle, U none)",
   "AmusicalTwin.lean; AmusicalSeventh.lean; agent report twin.md (2026-10-13)", "2026-10-13"⟩,
  ⟨"amusical: residue reversor killed by escape (normal backward itinerary)", .wall,
   "sound, but needs one integer with a normal backward itinerary; finite checks stop at cycles",
   "AmusicalEscape.lean; AmusicalWindowThree.lean; agent report q1.md (2026-10-13)", "2026-10-13"⟩,
  ⟨"amusical: coarse-local global invariants for a seventh orbit", .siblingTransfer,
   "U rewired at O(log² N) points with bounded ratio has one orbit and shares them all",
   "AmusicalRewireRatio.lean; AmusicalGlobal.lean; agent report global.md (2026-10-13)",
   "2026-10-13"⟩,
  ⟨"amusical: maps commuting with U move orbits", .refuted,
   "the window-2 centralizer is 0, ±1, ±id, ±U; window 3 adds one numerically non-integral pair",
   "AmusicalGlobal.lean; agent report global.md (2026-10-13)", "2026-10-13"⟩,
  ⟨"amusical: survival densities (never undercut later)", .wall,
   "decisive and changed by rewiring, but needs late drops to be rare: orbit typicality",
   "AmusicalGlobal.lean; agent report global.md (2026-10-13)", "2026-10-13"⟩,
  ⟨"amusical: anti-Kohl via transient cones (Theorem T)", .refuted,
   "proves anti-Kohl for κ and τ∘U, but U has no periodic cone: its residue graphs are connected",
   "AmusicalAntiKohl.lean; agent report antikohl.md (2026-10-13)", "2026-10-13"⟩,
  ⟨"amusical: slopes of valuation 1 at some prime (not one fixed prime)", .refuted,
   "slopes 3/2 and 2/3 alone allow a conjugated translation, which has one orbit",
   "AmusicalAntiKohl.lean; agent report antikohl.md (2026-10-13)", "2026-10-13"⟩,
  ⟨"amusical: eventually-linear ping-pong engine (two counters)", .refuted,
   "gives ∞ orbits for a residue-transitive map, but U's one linear piece 2n ↦ 3n only lowers v₂",
   "AmusicalPingPong.lean; agent report transitive.md (2026-10-13)", "2026-10-13"⟩,
  ⟨"amusical: piecewise-affine reversor for one-signed slope valuations", .refuted,
   "one-signed v_p with unbounded accumulation forbids it (NR_p); symmetric cycles force ±1",
   "AmusicalUniform.lean; agent report uniform.md (2026-10-13)", "2026-10-13"⟩,
  ⟨"amusical: residue-local orbit invariants (valuations, digits, 6-free part)", .refuted,
   "transitivity on Ẑ equates an invariant across classes where it is locally constant",
   "AmusicalUniform.lean; agent report uniform.md (2026-10-13)", "2026-10-13"⟩,
  ⟨"amusical: excluding cycles by bounding every cycle element", .refuted,
   "element bounds grow like 3^p/|2^e−3^p|; only the minimum is polynomial (Theorem A★)",
   "AmusicalCycleBound.lean; agent report cycles.md (2026-10-13)", "2026-10-13"⟩,
  ⟨"amusical: coarse heights F(x mod M, scale) with bounded cocycle", .refuted,
   "two-visit steering makes them bounded once one orbit is infinite (Proposition G)",
   "AmusicalFormalMin.lean; agent report emptyint.md (2026-10-13)", "2026-10-13"⟩,
  ⟨"amusical: survival typicality beyond the residue horizon", .wall,
   "late drops after depth log₃ X are uncontrolled; τ matches U's windows with maximal late drops",
   "AmusicalLateDrops.lean; agent report survival.md (2026-10-13)", "2026-10-13"⟩,
  ⟨"amusical: infinitely many orbits via infinitely many cycles", .refuted,
   "works in 𝔽₂[t] by Frobenius; over ℤ the denominators 2^N − 3^p are never small (Baker)",
   "AmusicalFunctionField.lean; agent report freeform.md (2026-10-13)", "2026-10-13"⟩,
  ⟨"amusical twin: Frobenius self-similar certificate for an infinite orbit", .refuted,
   "U²(n²) = (Un)² only on E ∪ A: the depth-3 class read forgets n₂; no class-wise repair",
   "AmusicalTwinDegree.lean; agent report twin2.md §1, §7 (2026-10-13)", "2026-10-14"⟩,
  ⟨"amusical twin: exact-height pigeonhole for an infinite orbit", .costume,
   "Theorem D controls only the cycle minimum; every count needs the closing-word bound",
   "AmusicalTwinDegree.lean; agent report twin2.md §2, §4 (2026-10-13)", "2026-10-14"⟩,
  ⟨"amusical: archimedean crossing index (Kohl's det) for infinite orbits", .refuted,
   "det = net crossings of 0 certifies |det| infinite orbits (twinW has one), but U preserves sign",
   "AmusicalCrossing.lean; agent report bridge.md §2–§4 (2026-10-14)", "2026-10-14"⟩,
  ⟨"amusical: rigidity or statistics of Û on ℝ × ℤ₂ × ℤ₃", .costume,
   "invariant subgroups are ℤ's layers (Prop L); one Û-orbit fakes every window statistic (Thm M)",
   "AmusicalAdelic.lean; agent report quasicrystal.md §2–§5 (2026-10-14)", "2026-10-14"⟩,
  ⟨"amusical: additive structure (carry cocycle, orbit sums, Baker contrapositive)", .refuted,
   "carry unbounded; forced log 2 / log 3 relations only Dirichlet-sized; twins are translates",
   "AmusicalAdditive.lean; agent report ringadd.md (2026-10-14)", "2026-10-14"⟩,
  ⟨"amusical: partial multiplicative symmetry (Theorem W beyond zero offsets)", .wall,
   "transport is free; existence needs an integer sub-series of an orbit's 2-adic expansion",
   "AmusicalUnit.lean; agent report ringunit.md (2026-10-14)", "2026-10-14"⟩,
  ⟨"amusical: deformation Û + c, carried to the degenerate point c = 0", .refuted,
   "U + 6^N agrees with U for ~N steps yet roots every point of [0, 6^N) on its own infinite orbit",
   "AmusicalDeform.lean; agent report deform.md (2026-10-14)", "2026-10-14"⟩,
  ⟨"amusical: arithmetic of basins (2-/3-adic measure, congruences) forces many survivors",
   .siblingTransfer,
   "sparse odd regluing of U keeps the even branch and windows, one orbit, survivors as sparse",
   "AmusicalReglue.lean; agent report fsarith.md (2026-10-14)", "2026-10-14"⟩,
  ⟨"amusical: T1 integrality (C_w mod Δ_w) as an arithmetic invariant of whole excursions",
   .costume,
   "C_w mod Δ is the 2-adic code at the endpoints; integrality along an excursion is U itself",
   "AmusicalExcursionCode.lean; agent report t1arith.md (2026-10-14)", "2026-10-14"⟩,
  ⟨"amusical: run-stratum and stopped-prefix counting of near-cycles past the horizon",
   .beyondHorizon,
   "proved to m ≤ log₂D/40 runs; the method's ceiling is 0.131 log₂D; what is left is BHN",
   "AmusicalNearCycleEntropy.lean; agent reports ncbaker.md, ncentropy.md", "2026-10-14"⟩,
  ⟨"amusical: square-return confinement via curve geometry (Siegel, Faltings)",
   .beyondHorizon,
   "SRC ⇒ (a), but each word-curve has ≤ 1 relevant point; SRC is Π⁰₁ past the horizon",
   "AmusicalSquares.lean; agent reports newroutes-astra.md, srcprobe.md", "2026-10-14"⟩,
  ⟨"amusical: bounded-offset real-affine maps with U's E-runs force many survivors",
   .siblingTransfer,
   "block-swap maps keep MR(II), T2, SQ, Lemma K; one has one orbit, sparse FS (mod EXT)",
   "AmusicalSwap.lean; agent report gprime.md (2026-10-14)", "2026-10-14"⟩,
  ⟨"amusical: automatic (finite-state) orbit invariants or colourings", .costume,
   "a binary-automatic U^m-invariant colouring is constant; automatic orbits ⇔ (a)",
   "AmusicalSquares.lean; agent report newroutes-astra.md §2 (2026-10-14)", "2026-10-14"⟩,
  ⟨"amusical: loop-weighted (FKG) comparison of U with random block swaps", .refuted,
   "blocks 8 and 9 of U interleave on the orbit of 37: loop counts 0, 1, 1, 0, not supermodular",
   "AmusicalLoopInterleave.lean; agent report newroutes3-astra.md §6 (2026-10-14)",
   "2026-10-14"⟩,
  ⟨"amusical: tail-event transfer from random perturbations to U (0–1 law, coupling)", .costume,
   "summable noise is a.s. a finite change of U, so μ(A) = 1 iff A(U); otherwise U is null",
   "AmusicalTailEvent.lean; agent report newroutes3-astra.md §3–§4 (2026-10-14)",
   "2026-10-14"⟩]

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
  ⟨"amusical: density, measure and crossing counts for Klamkin (a)",
   [``CollatzMoonshot.Obstructions.Amusical.amusical_mass_conservation], []⟩,
  ⟨"amusical: Tavares zero-density reduction with Rhin bounds",
   [``CollatzMoonshot.Obstructions.Amusical.amusical_mass_conservation,
    ``CollatzMoonshot.Amusical.amusicalInfinitelyManyOrbits_of_zeroDensity], []⟩,
  ⟨"amusical: forward/backward drift asymmetry",
   [``CollatzMoonshot.Amusical.even_iff_amusical_mod_three,
    ``CollatzMoonshot.Obstructions.Amusical.amusical_mass_conservation], []⟩,
  ⟨"amusical: orbit invariant or rational height for Klamkin (a)",
   [``CollatzMoonshot.Obstructions.Amusical.amusicalInfinitelyManyOrbits_iff_invariant], []⟩,
  ⟨"amusical: residue certification of orbit minima",
   [``CollatzMoonshot.Obstructions.Amusical.MinimaNotResidueDetermined,
    ``CollatzMoonshot.Amusical.IsOrbitMin.isWindowMin,
    ``CollatzMoonshot.Amusical.exists_large_nonOrbitMin], []⟩,
  ⟨"amusical: single-chain mechanism for Klamkin (a)",
   [``CollatzMoonshot.Amusical.exists_linearlyRecurrent_of_finitelyManyOrbits,
    ``CollatzMoonshot.Obstructions.Amusical.amusicalInfinitelyManyOrbits_of_noLinearRecurrence],
   [``CollatzMoonshot.Obstructions.Amusical.NoLinearRecurrence]⟩,
  ⟨"amusical: adelic volume preservation and ×2×3 rigidity",
   [``CollatzMoonshot.Obstructions.Amusical.amusical_branch_product_formula,
    ``CollatzMoonshot.Obstructions.Amusical.amusical_mass_conservation], []⟩,
  ⟨"amusical: Diophantine bounds on linear returns",
   [``CollatzMoonshot.Amusical.return_defect_bound,
    ``CollatzMoonshot.Amusical.exists_denseLinearReturns_of_finitelyManyOrbits], []⟩,
  ⟨"amusical: chain-connectivity statistics (records, excursions, pairs)",
   [``CollatzMoonshot.Amusical.IsWindowMin.iterate_eq_of_isWindowMin,
    ``CollatzMoonshot.Amusical.exists_sublinearlyRecurrent_of_finitelyManyOrbits,
    ``CollatzMoonshot.Amusical.amusicalInfinitelyManyOrbits_of_atLeastLinearGrowth],
   [``CollatzMoonshot.Amusical.AtLeastLinearGrowth]⟩,
  ⟨"amusical: reversing involution (works for the Gaussian relative)",
   [``CollatzMoonshot.Amusical.no_piecewiseAffine_reversor,
    ``CollatzMoonshot.Amusical.infinitelyManyOrbits_iff_reversor,
    ``CollatzMoonshot.Amusical.reversing_zpow_fixed], []⟩,
  ⟨"amusical: reversor determined by residues ((2,3)-adically continuous)",
   [``CollatzMoonshot.Amusical.no_continuous_linear_reversor,
    ``CollatzMoonshot.Amusical.reversor_const_of_twoAdicContinuous,
    ``CollatzMoonshot.Amusical.reversor_const_of_threeAdicContinuous,
    ``CollatzMoonshot.Amusical.AmusicalNoContinuousReversor], []⟩,
  ⟨"amusical: fat orbits equidistribute (ergodic theory on ℤ₂ × ℤ₃)",
   [``CollatzMoonshot.Amusical.logWeight_even_balance,
    ``CollatzMoonshot.Amusical.logWeight_three_balance,
    ``CollatzMoonshot.Amusical.amusicalInfinitelyManyOrbits_of_logDensityZero], []⟩,
  ⟨"amusical: basin counting: near-cycle sparsity forces many survivors",
   [``CollatzMoonshot.Amusical.card_fwdSurvivor_block_le,
    ``CollatzMoonshot.Amusical.infinitelyManyOrbits_of_linearNearCycleLaw], []⟩,
  ⟨"amusical: rung constraints (quantized ladder SQ) lower the survivor ceiling below c",
   [``CollatzMoonshot.Amusical.rung_depth_spectrum,
    ``CollatzMoonshot.Amusical.fwdSurvivor_density_le_of_finite], []⟩,
  ⟨"amusical: odd-branch agreement off a sparse set (any agreement set short of whole tails)",
   [``CollatzMoonshot.Amusical.tail_threshold, ``CollatzMoonshot.Amusical.exists_oddRewire,
    ``CollatzMoonshot.Amusical.fwdSurvivor_three_separation_of], []⟩,
  ⟨"amusical: seventh orbit from density, window or crossing statistics",
   [``CollatzMoonshot.Amusical.rewire_single_orbit,
    ``CollatzMoonshot.Amusical.sparse_sweep,
    ``CollatzMoonshot.Amusical.amusical_pow_classUnion_invariant,
    ``CollatzMoonshot.Amusical.atLeastSeven_of_orbit8_not_cofinite], []⟩,
  ⟨"amusical: statistical twin with finitely many orbits",
   [``CollatzMoonshot.Amusical.twinW_not_conj_amusical,
    ``CollatzMoonshot.Amusical.twinW_threeCycle,
    ``CollatzMoonshot.Amusical.amusical_no_threeCycle,
    ``CollatzMoonshot.Amusical.rewire_single_orbit], []⟩,
  ⟨"amusical: residue reversor killed by escape (normal backward itinerary)",
   [``CollatzMoonshot.Amusical.escape_forward,
    ``CollatzMoonshot.Amusical.not_reversor_of_evenFrequency_lt,
    ``CollatzMoonshot.Amusical.not_reversor_of_backwardNormal,
    ``CollatzMoonshot.Amusical.no_window3_bijective_reversor],
   [``CollatzMoonshot.Amusical.BackwardNormal]⟩,
  ⟨"amusical: coarse-local global invariants for a seventh orbit",
   [``CollatzMoonshot.Amusical.exists_boundedRatio_rewire,
    ``CollatzMoonshot.Amusical.abs_le_four_pow_mul_iterate_sub,
    ``CollatzMoonshot.Amusical.amusical_iterate_eq_add_finite,
    ``CollatzMoonshot.Amusical.exists_many_returns], []⟩,
  ⟨"amusical: maps commuting with U move orbits",
   [``CollatzMoonshot.Amusical.infinitelyManyOrbits_of_commuting,
    ``CollatzMoonshot.Amusical.commuting_window_two], []⟩,
  ⟨"amusical: survival densities (never undercut later)",
   [``CollatzMoonshot.Amusical.infinitelyManyOrbits_of_survival],
   [``CollatzMoonshot.Amusical.FwdSurvivor, ``CollatzMoonshot.Amusical.BwdSurvivor]⟩,
  ⟨"amusical: anti-Kohl via transient cones (Theorem T)",
   [``CollatzMoonshot.Amusical.orbit_densityZero_of_transientCone,
    ``CollatzMoonshot.Amusical.sigmaTau_orbit_densityZero,
    ``CollatzMoonshot.Amusical.amusical_no_periodic_cone,
    ``CollatzMoonshot.Amusical.atLeastSevenOrbits_of_antiKohl],
   [``CollatzMoonshot.Amusical.AntiKohlConjecture]⟩,
  ⟨"amusical: slopes of valuation 1 at some prime (not one fixed prime)",
   [``CollatzMoonshot.Amusical.mixedPrime_single_orbit], []⟩,
  ⟨"amusical: eventually-linear ping-pong engine (two counters)",
   [``CollatzMoonshot.Amusical.infinitelyManyOrbits_of_pingPong,
    ``CollatzMoonshot.Amusical.amusical_not_eventually_linear], []⟩,
  ⟨"amusical: piecewise-affine reversor for one-signed slope valuations",
   [``CollatzMoonshot.Amusical.no_piecewiseAffine_reversor_of_valNonneg,
    ``CollatzMoonshot.Amusical.island_cycle_slope], []⟩,
  ⟨"amusical: residue-local orbit invariants (valuations, digits, 6-free part)",
   [``CollatzMoonshot.Amusical.amusical_invariant_eq_of_locallyConst,
    ``CollatzMoonshot.Amusical.amusical_topologicallyTransitive],
   [``CollatzMoonshot.Amusical.AmusicalTopologicallyTransitive]⟩,
  ⟨"amusical: excluding cycles by bounding every cycle element",
   [``CollatzMoonshot.Amusical.amusical_cycle_min_bound,
    ``CollatzMoonshot.Amusical.amusical_noNewCycles_31866], []⟩,
  ⟨"amusical: coarse heights F(x mod M, scale) with bounded cocycle",
   [``CollatzMoonshot.Amusical.coarse_quasiInvariant_bounded], []⟩,
  ⟨"amusical: survival typicality beyond the residue horizon",
   [``CollatzMoonshot.Amusical.card_windowMin_le, ``CollatzMoonshot.Amusical.lateDrops_dense],
   [``CollatzMoonshot.Amusical.AmusicalLateDropsSparse]⟩,
  ⟨"amusical: infinitely many orbits via infinitely many cycles",
   [``CollatzMoonshot.Amusical.amusical_EmBm_not_integral,
    ``CollatzMoonshot.Amusical.twin_infinitelyManyCycles], []⟩,
  ⟨"amusical twin: Frobenius self-similar certificate for an infinite orbit",
   [``CollatzMoonshot.Amusical.twinU_twinU_sq,
    ``CollatzMoonshot.Amusical.twin_no_classwise_frobenius,
    ``CollatzMoonshot.Amusical.twin_not_periodic_of_selfSimilar], []⟩,
  ⟨"amusical twin: exact-height pigeonhole for an infinite orbit",
   [``CollatzMoonshot.Amusical.twin_cycleMin_natDegree_le,
    ``CollatzMoonshot.Amusical.twin_den_natDegree], []⟩,
  ⟨"amusical: archimedean crossing index (Kohl's det) for infinite orbits",
   [``CollatzMoonshot.Amusical.twinW_zero_not_periodic,
    ``CollatzMoonshot.Amusical.amusical_no_crossing], []⟩,
  ⟨"amusical: rigidity or statistics of Û on ℝ × ℤ₂ × ℤ₃",
   [``CollatzMoonshot.Amusical.amusicalRat_subgroup_one_mem], []⟩,
  ⟨"amusical: additive structure (carry cocycle, orbit sums, Baker contrapositive)",
   [``CollatzMoonshot.Amusical.amusical_carry_unbounded,
    ``CollatzMoonshot.Amusical.twinW_eq_translate], []⟩,
  ⟨"amusical: partial multiplicative symmetry (Theorem W beyond zero offsets)",
   [``CollatzMoonshot.Amusical.two_mul_not_orbit_map,
    ``CollatzMoonshot.Amusical.amusical_three_mul_sub_four],
   [``CollatzMoonshot.Amusical.AmusicalSharedSkeleton]⟩,
  ⟨"amusical: deformation Û + c, carried to the degenerate point c = 0",
   [``CollatzMoonshot.Amusical.amusical_add_roots_distinct,
    ``CollatzMoonshot.Amusical.amusical_no_crossing], []⟩,
  ⟨"amusical: arithmetic of basins (2-/3-adic measure, congruences) forces many survivors",
   [``CollatzMoonshot.Amusical.exists_reglue_sparseFS,
    ``CollatzMoonshot.Amusical.exists_reglue_sparseFS_amusical], []⟩,
  ⟨"amusical: T1 integrality (C_w mod Δ_w) as an arithmetic invariant of whole excursions",
   [``CollatzMoonshot.Amusical.defect_mod_delta,
    ``CollatzMoonshot.Amusical.eq_amusical_of_forall_branch], []⟩,
  ⟨"amusical: run-stratum and stopped-prefix counting of near-cycles past the horizon",
   [``CollatzMoonshot.Amusical.ncard_deep_lowRun_le,
    ``CollatzMoonshot.Amusical.nearCycleAt_le_of_eRuns_le], []⟩,
  ⟨"amusical: square-return confinement via curve geometry (Siegel, Faltings)",
   [``CollatzMoonshot.Amusical.infinitelyManyOrbits_of_squareReturnConfinement,
    ``CollatzMoonshot.Amusical.prefixRoot_eq_iff], []⟩,
  ⟨"amusical: bounded-offset real-affine maps with U's E-runs force many survivors",
   [``CollatzMoonshot.Amusical.ampSwap_bijective,
    ``CollatzMoonshot.Amusical.ampSwap_even], []⟩,
  ⟨"amusical: automatic (finite-state) orbit invariants or colourings",
   [``CollatzMoonshot.Amusical.invariant_kernel_three_pow,
    ``CollatzMoonshot.Amusical.amusicalInv_iterate_cylinder], []⟩,
  ⟨"amusical: loop-weighted (FKG) comparison of U with random block swaps",
   [``CollatzMoonshot.Amusical.interleave_path,
    ``CollatzMoonshot.Amusical.swap_both_path], []⟩,
  ⟨"amusical: tail-event transfer from random perturbations to U (0–1 law, coupling)",
   [``CollatzMoonshot.Amusical.infinite_permOrbits_mul_swaps_iff,
    ``CollatzMoonshot.Amusical.pivot_raises,
    ``CollatzMoonshot.Amusical.pivot_lowers], []⟩]

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

/-- info: maze audit: 65 rows, 57 cite declarations, 8 legacy (prose only) -/
#guard_msgs in
#maze_audit mazeRows, mazeLinks, mazeLegacy

end CollatzMoonshot.Maze
