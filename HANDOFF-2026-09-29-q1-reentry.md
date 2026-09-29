# HANDOFF 2026-09-29 — Q1 exit / re-entry obstruction

Branch: `main`.  HEAD at write time: `ecf147c` (this work).
Next steps: **none** — the kickoff froze this as a terminal task with no
successor.  All eight targets are proved; nothing in this module is open.

Scope: `CollatzMoonshot/Obstructions/Q1Reentry.lean` only (plus this doc).
Status: **complete and green.** All eight frozen theorems proved, no `sorry`,
no new axioms (`#print axioms` on all eight: `propext`, `Quot.sound`, and
`Classical.choice` on four). Root `lake build` succeeds (8822 jobs).

## What was proved

Definitions `oddExitA`, `oddExitB`, `phaseWeight` and all eight theorem
statements are byte-identical to the frozen kickoff versions.

1. `odd_exit_actual_steps` — two actual `tstep` steps on each frontier, via
   private cores `stepsA_core` (`16P-1 → 24P-1 → 36P-1`) and `stepsB_core`
   (`1+2N → 3N+2 → (9N+7)/2`), applied with `P = 9^r*u`, `N = 3^r*u`.
2. `odd_exit_affine` — `2B = 9*3^r*u + 7` from oddness kills the division;
   then `ring` after `9^r = 3^r*3^r`.
3. `odd_exit_no_canonical_reentry` — the exact bracket
   `A+1 < 8*3^r*(B-1) < 3*(A+1)`, from `2*(8*3^r*(B-1)) = 72*Z + 40*3^r`
   with `Z = 3^r*3^r*u`. A hypothetical `j` forces `3^j < 3^r`, hence
   `j < r`, hence `3*(A+1) = 8*3^(j+1)*(B-1) ≤ 8*3^r*(B-1)`, contradicting
   the upper bound. `r = 0` is handled by the same inequality.
4. `odd_exit_target_two` — `36P-1 → 54P-1 → 81P-1`, with
   `3^(2r+4) = 81*9^r`. Needs no oddness hypothesis.
5. `odd_exit_target_halvings` — `tstep^[k] (2^k*x) = x` by induction
   (`tstep_iterate_two_pow`), composed via `Function.iterate_add_apply`.
6. `odd_exit_one_halving_expands` — `9^r % 4 = 1` gives `3^(2r+4)*u ≡ 3 mod 4`
   for `u ≡ 3 mod 4`, so the next step is even; expansion follows from
   `3^(2r+4)*u ≥ 81*u`.
7. `phaseWeight_normalized` / 8. `canonical_reset_rank_iff` — `8*d^4` after
   eliminating natural subtraction; strict monotonicity of `d ↦ d^4`.

## Anchors checked (`native_decide`, scratch file, not committed)

`tstep^[2] 143 = 323`, `tstep^[2] 7 = 17`, `oddExitA 1 1 = 323`,
`oddExitB 1 1 = 17`, `oddExitA 0 3 = 107`, `tstep^[3] (oddExitA 0 3) = 121`,
`tstep^[2+4] (oddExitA 0 1) = 5`.

## Notes for a successor (none scheduled)

Powers were kept opaque throughout: every nonlinear identity goes through an
explicit `ring`-proved `have`, and `omega` only ever sees `3^r`, `3^r*3^r*u`
and the product `8*3^r*(B-1)` as atoms. That is what avoids the long `omega`
timeouts the prior worker hit.

This records obstructions to *direct* canonical re-entry and to a *reset* to
the normalized pair. It does not exclude all adaptive repair.
