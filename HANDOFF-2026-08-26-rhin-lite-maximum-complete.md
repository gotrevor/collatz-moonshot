# HANDOFF 2026-08-26 — Rhin-lite global maximum complete

- **Primary gate:** `sorry-free:CollatzMoonshot/FrontA/RhinLiteMaximum.lean` is complete.

## Concrete advance

Added and root-imported `CollatzMoonshot/FrontA/RhinLiteMaximum.lean`.  Its headline theorem

```text
rhinLiteKernelAbs_div_pow_le_on_Icc
```

proves the required `(9/40)^1000` bound for every `x ∈ [2,4]`, without `sorry` or new axioms.
The proof maximizes the squared signed normalized kernel, compares with `x=5/2` to force a
nonzero interior maximizer, transfers the maximum locally to the factorwise log-square, computes
its derivative from six small `HasDerivAt.log` arguments, clears the nonzero factors to the
existing checked degree-eight critical polynomial, applies root exhaustion and the seven local
interval certificates, then passes back from squares to the nonnegative absolute kernel.

The new headline theorem was added to `scripts/AxiomAudit.lean`; the route/status documents now
mark the compact-maximum bridge complete and point to the even-subsequence lift.

## Exact verification

- `lake env lean CollatzMoonshot/FrontA/RhinLiteMaximum.lean`
- `lake build` — green, 8759 jobs
- `bash scripts/check-proof-debt.sh` — exactly the one disclosed
  `CollatzMoonshot/FrontA/PowSeparation.lean:40` sorry
- `lake env lean scripts/AxiomAudit.lean` — the new global theorem has only
  `[propext, Classical.choice, Quot.sound]` plus the already-allowed native interval/root
  certificate axioms; no `sorryAx` or new math axiom

## Current blocker and next attack

No blocker.  Execute objective 2 of `FRONT-A-RHIN-LITE-NEXT.md`: define the original signed
polynomial at `N=2000t`, prove exact degree `2N`, identify its central coefficient with the
`RhinLite.lean` coefficient at parameter `2t`, establish positivity/nonzeroness of both interval
integrands, and raise the base theorem to `2t` for the pointwise and integral bounds.
