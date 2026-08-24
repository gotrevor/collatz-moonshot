# PENDING_WORK

## Status (2026-08-24)

- **Harmonic-dual obstruction project: COMPLETE** (this session's scoped task).
  `no_positive_harmonic_local_certificate` proved sorry-free, depth-uniform,
  axiom-clean (`[propext, Classical.choice, Quot.sound]` + 4 `native_decide`).
  See `FRONT-A-HARMONIC-DUAL.md` §Results/§8 and `HANDOFF-2026-08-24-0530.md`.
- `src/` is sorry-free; full `lake build` green (8746 jobs).

## The repo's real headline cruxes (open, deep — narrow, don't clear in one lap)

The Collatz headline `Conjecture ↔ NoDivergentOrbit ∧ NoNontrivialCycle`
(`Descent.lean`, `Conjecture.lean`) rests on two fronts, each behind cited
axioms:

### Front B — `NoNontrivialCycle ↔ FrontB` (`FrontB/Dictionary.lean`)
Arithmetic front; cited axioms in `Assumed/`:
- `eliahou_min_cycle_length`, `hercher_odd_members_bound` (`Assumed/Cycles.lean`)
  — Baker linear-forms + continued fraction of `log₂3` + large computation.
- `baker_bounded_difference`, `hercher_min_circuit_count` (`FrontB/Threads.lean`).
- `abc` (`Assumed/ABC.lean`), used by `length_bounded_of_abc_and_boundedDen`.
- **Narrowing path** (not one lap): formalize the elementary cycle→S-unit/linear-
  forms reduction, isolating Baker's theorem as the single narrow cited input;
  or discharge the finite `hercher_*` circuit-count computations. See
  `FRONT-B-ROUTES.md`.

### Front A — `NoDivergentOrbit`
Rigidity front; rests on `tao_2019_almost_bounded` (`Assumed/Tao2019.lean`) and
`furstenberg_topological_rigidity` (`Assumed/Furstenberg.lean`, flagged OPEN).
The barriered backward-tree ladder (2/3→3/4→4/5 rungs, all green) is the
constructive lane; the harmonic no-go proved this session shows the uniform
local-certificate ladder **cannot** reach `α=1`, so Route A2 does not close the
divergence front alone — redirect to A1/A3 itinerary-rigidity.

## ACTIVE crux probe: Front B ladder base (`FrontB/OneCircuit.lean`, 1 sorry)

Special-case-first on the `Compression`/`LadderCompletes` crux: **a canonical
one-circuit integer cycle `trueᵃ falseᵇ` is trivial**.  Proved this lap
(machine-checked): the closed forms `ones=a`, `numer = 3ᵃ−2ᵃ` (b-independent),
`den = 2^(a+b)−3ᵃ`; the identity `numer+den = 2ᵃ(2ᵇ−1)`; the reduction
`den ∣ numer ↔ den ∣ 2ᵇ−1` (den odd); and the **a=1 slice** in full (den∣1 ⟹
den=1 ⟹ b=1).  Numerically the sole solution through a≤8 is (1,1).

**Open (the one `sorry`): a≥2 has no solution.**  Established facts in context:
`den ∣ 2ᵇ−1`, `0 < den = 2^(a+b)−3ᵃ`, `2 ≤ a`.  These force
`(3ᵃ+1)/2ᵃ ≤ 2ᵇ ≤ (3ᵃ−1)/(2ᵃ−1)` — a real interval of width-ratio `→1`, and it
contains **no power of 2** for a≥2.  Three attack paths:
1. **Interval-misses-power-of-2** (most concrete): from `den ∣ 2ᵇ−1` ⟹ `den ≤ 2ᵇ−1`
   and `den>0`, derive the two-sided bound on `2ᵇ`; show the endpoint ratio is `<2`
   so at most one power of 2 could fit, and the candidate makes `den ≤ 0` — a clean
   `omega`-after-`Nat.lt_pow`/`pow` monotonicity argument once the interval is set up.
2. **2-adic valuation**: reduce the surviving cases to `numer = den` (quotient 1),
   then `2^(a+b)+2ᵃ = 2·3ᵃ` ⟹ `2ᵃ(2ᵇ+1)=2·3ᵃ`, and `v₂(LHS)=a`, `v₂(RHS)=1` ⟹ a=1.
   (Blocker: showing quotient=1 needs a size bound that only path 1 supplies.)
3. **LTE / order of 2 mod den**: `2ᵇ ≡ 1 (mod den)` ⟹ `ord_den(2) ∣ b`; combine with
   `den ∣ 3ᵃ−2ᵃ` to bound `den`.  Heavier machinery; last resort.
Path 1 is the recommended attack.  Then: prove `circuits v = 1 → v` is a rotation
of `oneCircuitWord a b` to lift from the canonical rep to all one-circuit words,
and wire into the ladder base.

## Note for the next operator
The scoped harmonic project is finished. Picking up a Front A/B axiom-narrowing
task is a deliberate refocus (deep, multi-lap) that should be operator-directed
rather than started blind at a session boundary.
