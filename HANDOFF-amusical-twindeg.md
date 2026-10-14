# HANDOFF: amusical twin degrees (2026-10-14)

`KICKOFF-2026-10-14-amusical-twindeg.md` is discharged: `CollatzMoonshot/AmusicalTwinDegree.lean`
has no `sorry`, and its statements are unchanged.  All seven targets depend only on `propext`,
`Classical.choice` and `Quot.sound`.  No `native_decide` and no `decide` over large cases.

## Proof architecture (helpers in `CollatzMoonshot/AmusicalTwinDegree/`)

- `Den.lean`: D1.  `Q^q` is monic of degree `2q` with `nextCoeff = q • 1 = 1` (`Monic.nextCoeff_pow`).
  So `t^{2q} − Q^q` has degree `2q − 1`, and Frobenius gives the `2^v`-th power.
- `Step.lean`:
  - `exc = {0, 1, t, t+1, Q}` is invariant (`twinU_mem_exc_iff`).
  - The four-way `step`: `t^d U y = Q y + e`, with the degree moving by `+1, 0, −1, −1`.
  - `iter_identity`: `t^N U^j x = Q^j x + c` with `N + deg U^j x = 2j + deg x` and
    `deg c ≤ 2j + 2`, at a cycle minimum.
  - `cycleMin_natDegree_le`: Theorem D.
- `Corollaries.lean`:
  - `period_lower_bound` takes a cycle minimum `y`.  It uses `|Δdeg| ≤ 1` per step from both
    sides of `y`, so `2 deg x ≤ 2 deg y + p`.  This is simpler than the docstring's `#E ≤ p/2`
    count.
  - `cycleMins_finite` uses `finite_natDegree_le`.
- `Frobenius.lean`: `twinU_twinU_sq` and Proposition M (a point of maximal degree on the orbit).
- `NoGo.lean`:
  - `eq_zero_or_one_of_twinU_twinU` proves `U² x = x → x ∈ {0,1}` with no search.  Degree changes
    leave the class pairs `EB, EC, BE, CE, AA`.  Evaluating the pair identity at `t = 1` kills the
    first four, and `AA` gives `(t+1)²(x−1) = 0`.
  - `no_classwise_core` uses the instances `n = 0, t, Q, t+1`.  `κ_E ∈ {0,1}`, then `n = t` fixes
    `κ_C`, `n = Q` fixes `κ_B`, and `n = t + 1` fails.

## Findings

- **`twinExceptional` omits `t`.**  `t` lies on the 3-cycle `t → Q → t+1 → t`, but the ratified
  set is `{0, 1, t+1, Q}`.  This is harmless: every target stays true.  Internally I use
  the invariant 5-point set `TwinDeg.exc`.
- **Theorem D does not need `hexc`.**  `TwinDeg.cycleMin_natDegree_le` drops the hypothesis
  (exceptional points have degree ≤ 2).  The ratified `twin_cycleMin_natDegree_le` keeps it,
  unused, which produces one unused-variable lint.

## Next

Nothing is owed on this kickoff.
