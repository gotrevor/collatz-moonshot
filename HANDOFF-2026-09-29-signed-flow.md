# HANDOFF 2026-09-29 — signed flow

Scope: `CollatzMoonshot/Obstructions/SignedFlow.lean` only (plus this doc).

All four frozen statements are proved; no `sorry`, no new axioms.
`#print axioms` on each gives only `propext, Classical.choice, Quot.sound`
(`reachesOne_step_iff` does not even need `Classical.choice`).

Definitions and theorem types are unchanged. The one structural edit outside
the proof bodies: the skeleton as staged did not compile, because `boundary`
and the helper chain are `Finsupp`-valued and therefore noncomputable, so the
body of the namespace is wrapped in `noncomputable section ... end`. No
statement text was touched.

Helper declarations added (all `private`):
- `pair_eq` — the pairing `f.sum (fun u z => z * w u)` is
  `Finsupp.linearCombination ℤ w f`; lets the invariant proof use `map_sum`,
  `map_sub`, `map_smul`.
- `boundary_add`, `boundary_zero`, `boundary_single` — additivity of
  `boundary` (via `Finsupp.sum_add_index'`) and its value on a unit edge.
- `pathChain : ℕ → ℕ → (ℕ →₀ ℤ)` — the finite signed orbit chain,
  `pathChain n 0 = 0`, `pathChain n (k+1) = single n 1 + pathChain (tstep n) k`.
- `boundary_pathChain` — telescoping:
  `boundary (pathChain n k) = single n 1 - single (tstep^[k] n) 1`.
- `basinIndicator u = if reachesOne u then 1 else 0`, with
  `basinIndicator_invariant`, `basinIndicator_one`, `basinIndicator_of_not`.

Proof shapes are exactly the ones the kickoff prescribed: iterate-successor
splitting for `reachesOne_step_iff`; linearity of `Finsupp.sum` plus
`z • (w u - w (tstep u)) = 0` for the invariant; indicator pairing for the
forward half and `pathChain` for the reverse half of the equivalence; and the
same indicator against `k • (single n 1 - single 1 1)` for the scaled
corollary, where `k ≠ 0` contradicts `0 = -k`.

No positivity hypothesis appears anywhere; coefficients stay signed.
No claim is made that the boundary equation can be constructed for arbitrary
`n` — by the equivalence, that is precisely the open convergence assertion.

Root `lake build` is green. Nothing further is in flight.

## Checkpoint

- Branch: `main`
- HEAD: `168c5e0` "Prove the four frozen signed-flow statements"
- Working tree: clean; root `lake build` green (pre-commit hook re-verified).
- `box done --green` signalled; stop sentinel written at
  `/Users/gotrevor/src/.treadmill/collatz-moonshot.stop`.

### Next steps (for the parent, not this bounded lap)

1. Run the normal root build and the `Statement.lean` audit over the new
   module; nothing in it is referenced elsewhere yet.
2. Decide whether `CollatzMoonshot.lean`'s new
   `import CollatzMoonshot.Obstructions.SignedFlow` line should stay (it was
   already staged before this lap; the commit carries it).
3. If the `noncomputable section` wrapper is unwanted, the alternative is
   marking `boundary` and `pathChain` `noncomputable` individually — that
   touches the frozen `boundary` line, which this lap deliberately avoided.
4. Nothing here constructs the boundary equation for arbitrary `n`; by
   `exists_signed_flow_iff_reachesOne` that is equivalent to the open
   convergence assertion, so it is not a route to the headline.
