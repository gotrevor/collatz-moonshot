# Bounded Lean task: finite signed flow extracts convergence

Work only in `CollatzMoonshot/Obstructions/SignedFlow.lean`, starting from the staged skeleton.  Import `CollatzMoonshot.FrontB.Dictionary`; it already imports `Mathlib`.  Keep the frozen definitions and four theorem statements unchanged.  The objective is the full signed-flow equivalence and scaled corollary, with no nonnegativity assumption.  Do not add a conjecture hypothesis or hide `reachesOne n` inside an auxiliary premise.

The accelerated `tstep` has `tstep_one` and `tstep_two`.  For `reachesOne_step_iff`, reverse direction prepends one step.  Forward direction splits a witness `k`: if `k=0`, then `n=1` and `tstep n=2` reaches `1` in one step; if `k=k'+1`, the witness for `tstep n` is `k'`.  `Function.iterate_succ_apply` is the useful orientation.

For `boundary_pairing_invariant`, use linearity of `Finsupp.sum`.  Pairing a single weighted edge with `w` gives `z*(w u-w (tstep u))=0`.  A local helper for this pairing or induction on the finite support of `c` is fine.  Signed coefficients are deliberate: no `c u≥0` should appear.

For the forward half of `exists_signed_flow_iff_reachesOne`, take the invariant integer function `w u := if reachesOne u then 1 else 0`.  `reachesOne_step_iff` makes it edge-invariant.  Pair the claimed boundary with `w`.  The left side is zero; the right is `w n-w 1`, and `w 1=1` by the zero-step witness.  If `n` failed to reach `1`, this would read `0=-1`.

For the reverse half, use the finite signed path from `n` to `tstep^[k] n=1`.  A recursive helper is convenient:

```
pathChain n 0       = 0
pathChain n (k+1)   = single n 1 + pathChain (tstep n) k.
```

Prove by induction that `boundary (pathChain n k) = single n 1 - single (tstep^[k] n) 1`.  The edge terms telescope.  Repeated orbit vertices are fine because `Finsupp` accumulates integer multiplicities.  The proof is genuinely finite and does not assume a known path when extracting convergence from a signed flow.

For `scaled_signed_flow_reachesOne`, use the same invariant `w`.  The pairing gives `0=k*(w n-1)`.  With `k≠0`, a hypothetical `¬ reachesOne n` makes the right side `-k`, contradiction.  This extends extraction to any nonzero rational scale after clearing denominators.  It is not a method to construct the flow.

Acceptance: the four frozen theorem statements compile without `sorry` or additional axioms; the parent will run the normal root build and its audit.  Keep scope to this file and report any needed helper declarations.  Do not claim that signed balance has been constructed for arbitrary `n`: its existence is equivalent to the missing convergence assertion.


Operator scope: bounded Opus/low, at most three laps; no Aristotle.  The shared store and warm dependencies were checked this session.  Do not download dependencies.  Own only SignedFlow.lean and HANDOFF-2026-09-29-signed-flow.md.  Do not change definitions, theorem types, root imports, other proofs, or research documents.  Parent owns those files.  Build the module and root, commit green, then call box done --green immediately.  No extra research or theorem targets.  If a frozen statement is false, report it without weakening it.
