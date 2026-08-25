# Front A: consume Rhin 1987 and close the two-block theorem

> **Fallback only (2026-08-26):** this is the short citation/axiom route. The live independent
> formalization route is now `FRONT-A-RHIN-LITE.md`; do not run this assignment unless the decision
> is explicitly made to cite Rhin instead.

## Objective

Replace the sole source `sorry`, `FrontA.sep_two_three`, by consuming Georges Rhin's published
1987 linear-independence estimate as one narrow, theorem-grade named axiom. Then carry that result
through the existing pipeline to a sorry-free `le_two_blocks_not_acyclicParadoxical`.

This repository explicitly permits published literature to be represented by named axioms. Do
**not** formalize Rhin's Padé construction, finish the single-log detour, or add an open-conjecture
assumption. The new mathematical content here is the already-built downstream two-odd-block
exclusion; Rhin's result is cited infrastructure.

## Source-locked input

Use Rhin, *Approximants de Padé et mesures effectives d'irrationalité*, Séminaire de Théorie des
Nombres, Paris 1985–86, Progress in Mathematics 71 (1987), pp. 155–164, Proposition (7), p. 160:

For integers `u₀,u₁,u₂`, with `H = max |u₁| |u₂| >= 2`,

```text
|u₀ + u₁ log 2 + u₂ log 3| >= H^(-13.3).
```

The exponent is exactly `13.3 = 133/10`; the constant is `1`; `u₀` is not part of `H`; and the
threshold for (7) is exactly `H >= 2`. Read
`papers/rhin-1987-pade-mesures-effectives-summary.md` and
`ON-LINE-FINDINGS-2026-08-25-rhin-primary-source-verified.md`. Do not use the sharper `7.616`
estimate, whose threshold is not stated.

Create a small `CollatzMoonshot/Assumed/Rhin1987.lean` module following the repository's axiom
policy and provenance style. State no more than the proposition above (an exactly equivalent Lean
form is fine). Import it through `CollatzMoonshot/Assumed.lean`.

## Required derivation

1. Specialize Rhin with `(u₀,u₁,u₂) = (0,m,-k)` in the near-critical window
   `3^k < 2^m < 2*3^k`. Prove all sign, height, and cast facts in Lean; in particular, do not smuggle
   `H=m` or positivity of the linear form into the axiom.
2. Derive a concrete bound strong enough for the existing `sep_of_measure` or
   `sep_of_linear_form_poly` interface. The documented safe parameters are polynomial exponent
   `C=15`, large range `k >= 400`, and `k^45 <= 2^k` from that point. Exact equivalent constants are
   acceptable if fully proved.
3. Extend/discharge the finite near-critical range `6 <= k < 400` with `native_decide` (allowed),
   and replace the body of `sep_two_three` with the resulting theorem. Do not weaken, rename, turn
   into a definition, or leave a wrapper `sorry`.
4. Confirm that `le_two_blocks_not_acyclicParadoxical` is now sorry-free and its axiom ledger names
   Rhin's axiom rather than `sorryAx`. Preserve the existing theorem statements.
5. Correct stale comments/docs that say the obligation remains open or should be solved by
   continued fractions. Update `README.md`, `DIRECTION.md`, `STATUS.md`, `PENDING_WORK.md`, and the
   current handoff with an exact claim: the two-block exclusion is proved conditional only on the
   cited published theorem plus the ordinary trust base and finite `native_decide` artifacts. Do
   not claim Collatz, Front A, or finiteness of all paradoxical trajectories.

## Acceptance gate

- No `sorry` anywhere under `CollatzMoonshot/`.
- No new axiom except the single source-locked Rhin proposition.
- `lake build` passes.
- `scripts/check-proof-debt.sh` is updated to require zero sorries and passes.
- Run real `#print axioms` checks for `sep_two_three`,
  `le_two_blocks_not_acyclicParadoxical`, and `finite_acyclicParadoxical_imp_noDivergent`; record
  their exact output.
- Commit one coherent green checkpoint. Do not push.

## Stretch goal only after the acceptance gate

If the main milestone is completely green and ample lap budget remains, investigate whether the
same named Rhin axiom cleanly proves `FrontB.SteinerOneCircuit`. Land it only if the proof is direct
and does not destabilize the existing API; otherwise document the exact remaining conversion and
stop.
