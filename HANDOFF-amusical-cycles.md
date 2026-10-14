# HANDOFF: amusical cycle bound (2026-10-14): DONE

`KICKOFF-2026-10-13-amusical-cycles.md` is fully discharged, stretch target included.
`CollatzMoonshot/AmusicalCycleBound.lean` is sorry-free, with its ratified statements unchanged.

## Results (all `[propext, Classical.choice, Quot.sound]`)

- `amusical_cycle_min_bound` (Theorem A★).
- `cycle_min_meet`, `cycle_min_mod_six`.
- `noNewCycles_of_search`: the reduction.  Its real-to-floor step is `le_natMinBound`
  (`MinBound.lean`), which uses Bernoulli's inequality `bernoulli_clear` in place of logarithms.
- `cycleMinBound_31866`: one `decide +kernel` on `minBoundCheck 167195612 31866` (9 s, 3.1 GB).
  Control: `X = 167195611` is rejected.
- `amusical_noNewCycles_31866`: Theorem 1, conditional only on `CycleMinSearch 167195612 15933`.
- `amusical_noNewCycles_199`, `atkinNoShortCycles : Literature.AtkinNoShortCycles`: Atkin 1966,
  unconditional, in the kernel.  The proof is one `decide +kernel` (`cycleCheck_199` in
  `Search.lean`) on `minBoundCheck 4964 199 && searchCheck 100 4964`, with soundness by
  `searchCheck_sound`.
  - Measured: the small instance (`X = 173`, `H = 6`) takes 15 ms of kernel time; the full one
    takes 6.5 s, about 1.1 GB over the 6.4 GB max-RSS of the bare import.
  - Controls: `minBoundCheck 4963 199` is rejected, and `searchOkN_fortyFour_fails` shows that
    without the exemption the check fails at `44`.

## Checker design (`Search.lean`)

`natU`/`natV` are `U`/`V` on `ℕ` built from `Nat` primitives, bridged to `amusical`/`amusicalInv`
by `natU_iterate_cast`/`natV_iterate_cast`.  The loops `anyLt`, `allNe` and `iterN` are bare
`Nat.rec` loops.  Per `n` the check is a lazy `||`: a forward dip, then a backward dip, then
"the first `H` forward iterates avoid `n` and `V^H n`".

## Not done (out of scope)

The full `CycleMinSearch 167195612 15933` in the kernel.  It is about `10¹²` steps, far beyond any
`decide`, and it stays an external computation, as the module docstring says.
