# HANDOFF 2026-10-17: wythoff-trapd done

Branch `wip/wythoff-trapd`, HEAD `d3bc8fb` (before this doc).  Kickoff:
`KICKOFF-2026-10-16-wythoff-trapd.md`.  Working notes: `HANDOFF-wythoff-trapd.md`.

## Done

`CollatzMoonshot/WythoffTrapDegree.lean`: all 10 kickoff `sorry`s proved; 0 remain.
`#print axioms` on `trapSetD_entry_infinite`, `wyPerm_infinitelyManyInfiniteOrbits_of_trapD`,
`cubicPerm_infinitelyManyInfiniteOrbits`, `wy_iterate_three_cubic`: `propext,
Classical.choice, Quot.sound`.  No ratified statement changed (diff vs `9971fac`: proof bodies,
status tags, verbatim move of `sub_mul_sum_quotCoeff` below `phase_identity`).

* Unconditional: synthetic division, degree-d identity on `E^d`, trap `T_d`, recurrence along
  the trap, `d = 2` consistency with Theorem A′, cubic `W³ = 3W² − n` and `T_3` trap.
* Conditional on `WeylEquidistributionMulti` (+ `hind`): infinitely many entry points, hence
  infinitely many infinite orbits (general and cubic).  Route: Weyl window
  `k ∈ (LN, (L+1)N]` + seeds + growth `W(t) ≥ ((A+1)/2)t` (pigeonhole as in
  `coneEntry_infinite`).

Full `lake build` green (umbrella needed `taskset -c 0-1`: spurious box "Too many open files").

## Next steps (out of scope of this kickoff, per its "later layers")

1. Unconditional entry-point theorem (model-set / relatively-dense argument, or Pisot-trace
   syndeticity for the cubic), removing the Weyl hypothesis.
2. Entry density `2^{−d}(1 − 2/α)` (shear volume of the full parity region).
3. `D = ±1` dictionary for K members (research note §9).
4. Merge `wip/wythoff-trapd` into `main` (host pushes / PR).
