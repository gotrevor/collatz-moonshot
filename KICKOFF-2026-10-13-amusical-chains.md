# KICKOFF 2026-10-13: chain connectivity lemmas (amusical)

Treadmill lane.  Target: close every `sorry` in `CollatzMoonshot/AmusicalChains.lean`.  Done when
that file is sorry-free.  Land each statement as a green commit.

## Ratified, do not change

The statements in `AmusicalChains.lean` (including the proved `windowDensity_ge` and
`amusicalInfinitelyManyOrbits_of_atLeastLinearGrowth`, which must keep compiling); everything in
`Amusical.lean`, `AmusicalWindow.lean`, `AmusicalConstant.lean`, `AmusicalBound.lean`,
`Obstructions/Amusical.lean`, `Maze.lean`; `AmusicalSpitzer.lean` and `AmusicalReturns.lean`
belong to other treadmills — do not edit them.  Helpers go in `AmusicalChains.lean` or
`CollatzMoonshot/AmusicalChains/*.lean`.  No `native_decide`, no new axioms.

## Paper proofs

1. **`IsWindowMin.iterate_eq_of_isWindowMin`.**  `h` at `t` gives `n ≤ U^t n`; `h'` at `t` gives
   `U^t n ≤ amusicalInv^[t] (U^t n) = n`.  Antisymmetry.
2. **`fwdSurv_ge`, `bwdSurv_ge`.**  Generalize to a start height: `g_L(s)` = probability the
   forward walk from `s > 0` stays `> 0` for `L` steps, with steps `+log(3/2)`, `+log(3/4)`
   (probability `1/2` each).  Claim `g_L(s) ≥ 1 − e^{-s}`: base `1 ≥ 1 − e^{-s}`; step
   `g_{L+1}(s) ≥ ½(1 − (2/3)e^{-s}) + ½·[1 − (4/3)e^{-s}]⁺ ≥ 1 − e^{-s}` (if the down-step crosses
   `0` then `(4/3)e^{-s} ≥ 1`, so dropping that term only helps).  Work on the lattice of heights
   `3^a/2^b` (so `e^{-s} = 2^b/3^a`, all rational) and with the pattern sums as in
   `AmusicalBound.lean`'s DP (a treadmill proved the DP equivalence there; reuse or mirror it).
   Then `fwdSurv L ≥ ½·g_{L-1}(log(3/2)) ≥ ½(1 − 2/3) = 1/6`.  Backward: steps `log(2/3)` w.p.
   `1/3`, `log(4/3)` w.p. `2/3`, same `E[e^{-X}] = 1`, first step must be up: `≥ ⅔(1 − ¾) = 1/6`.
3. **`exists_sublinearlyRecurrent_of_finitelyManyOrbits`.**  Use `windowMinDensity L` and
   `windowDensity_ge` (density `≥ 1/36`) for each fixed `L`, item 1 (window minima on one chain
   are more than `L` apart in time unless periodic — finitely many orbits means finitely many
   cycle points), and the counting as in `exists_linearlyRecurrent_of_finitelyManyOrbits`
   (`Amusical.lean`): `k` chains span time `≥ L·X/37 − O(k)`, so some chain has `|j| ≥ L X/(75k)`
   with value `< X`; for each `C` take `L > 75 k C`; pigeonhole over finitely many chains (the
   chain may depend on `C`; choose one chain that works for an unbounded set of `C`).
4. **`atLeastSeven_or_orbitEight_infinite`.**  If the orbit of `8` is finite, the set
   `known cycles ∪ orbit 8` is finite; take any `n ≥ 0` outside it; its orbit differs from all six
   (use `amusical_six_distinct_orbits` and `amusicalOrbit_eq_of_mem`), giving seven.

Notes for the next lap go in `HANDOFF-amusical-chains.md`.
