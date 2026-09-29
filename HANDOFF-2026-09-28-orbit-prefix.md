# HANDOFF — arbitrary dyadic ray plus finite orbit prefix (frozen node)

Checkpointed 2026-09-29. Branch `main`, HEAD `5c0e1ef`
(`efbe346` is the proof commit; `5c0e1ef` only rewords an audit comment so the
sorry gate sees a clean file). Working tree otherwise carries only
`experiments/` changes owned by other agents — untouched here.

Status: **complete, sorry-free, axiom-clean.** `lake build CollatzMoonshot` green
(re-verified by the pre-commit hook on both commits).


## Delivered

`CollatzMoonshot/Obstructions/OrbitPrefix.lean` proves the frozen proposition

```lean
theorem orbitPrefix_defect (n L : ℕ) (hn : 0 < n) (hL : 0 < L) (v : ℕ) (hv : 0 < v) :
    transfer (orbitPrefixCoeff n L) v - orbitPrefixCoeff n L v =
      pointCoeff ((tstep^[L]) n) v
```

`pointCoeff`, `orbitPrefixCoeff` and the statement are exactly as staged; only
helper lemmas were added. `#print axioms orbitPrefix_defect` is pinned with
`#guard_msgs` to `[propext, Classical.choice, Quot.sound]`.

## Proof skeleton (all in the one module)

1. `transfer_pointCoeff (u v) (hv : 0 < v) : transfer (pointCoeff u) v = pointCoeff (tstep u) v`.
   Direct at rational coefficients: the two transfer preimages `2v` and `(2v-1)/3`
   fire exclusively — `2v = u` forces `u` even with `tstep u = v`, and
   `3u = 2v-1` forces `u` odd with `tstep u = v`. **Positivity of `u` is not
   needed**, which is why no induction on iterate positivity appears anywhere;
   step 1 of the kickoff plan turned out to be unnecessary.
2. `rayCoeff_two_mul (n v) (hn : 0 < n) : rayCoeff n (2*v) = rayCoeff n v + pointCoeff n (2*v)`.
   `2v = 2^j n` with `j ≥ 1` halves back onto the ray; `j = 0` is the single new
   point `2v = n`. The two cases are disjoint because `v = 2^j n` and `n = 2v`
   force `v = 0`. No parity assumption on `n` (so `rayAt_two_mul` is *not* used).
3. `rayCoeff_odd_pre (n v) (hn) (h3 : v % 3 = 2) : rayCoeff n ((2*v-1)/3) = pointCoeff n ((2*v-1)/3)`.
   `3u = 2v-1` is odd, so `u = 2^j n` forces `j = 0`, i.e. `u = n`.
4. `transfer_rayCoeff_eq`: 2+3 say `transfer (rayCoeff n) v = rayCoeff n v + transfer (pointCoeff n) v`;
   then 1 with `u = n` gives `= rayCoeff n v + pointCoeff (tstep n) v`.
5. `transfer_orbitPrefixCoeff`: `transfer` splits over ray + `Finset.Ico 1 L` sum.
6. `telescope_sub` (`Nat.le_induction` + `Finset.sum_Ico_succ_top`) collapses
   `∑_{j∈Ico 1 L} (P (j+1) - P j)` to `P L - P 1`; the two copies of
   `pointCoeff (tstep n) v` cancel and only `pointCoeff (tstep^[L] n) v` survives.

`ray_any_iff` is used only through `rayCoeff_eq_one` / `rayCoeff_eq_zero`,
which is exactly the intended lossless-cutoff interface.

## Controls

Three `example`s in the module, each obtained by specializing the general
theorem and then `decide`:

* `n = 8, L = 1` — even base, defect at `tstep 8 = 4`;
* `n = 3, L = 2` — odd base, defect at `tstep^[2] 3 = 8`;
* `n = 1, L = 3` — orbit `1,2,1,2`: the coefficient at `2` sits both on the ray
  and in the prefix, and the defect is still the single point mass at
  `tstep^[3] 1 = 2`.

## Next node (not started, per kickoff)

Combining this identity with the finite-cut lower bound in `AnchoredCut.lean`
to get the exact anchored infimum needs the separate 0/1 lemma, i.e. injectivity
of the prefix and disjointness from the dyadic ray. Those are nonperiodicity
consequences and are deliberately absent here.

## Exact next steps (none owed by this run)

This node is closed and the treadmill is stopping; `DIRECTION.md`'s CURRENT
DIRECTIVE (2026-09-13 reflection) is a standing pause on launching further proof
laps from the deferred list, so **no successor task is queued**. Should the
operator lift that pause, the natural continuation is the one named in the
kickoff:

1. Prove the 0/1 lemma for `orbitPrefixCoeff`: it needs injectivity of
   `j ↦ tstep^[j] n` on `[1, L)` and disjointness of that prefix from the dyadic
   ray `{2^h n}`. Both are consequences of nonperiodicity of the base, so they
   must enter as explicit hypotheses — they are deliberately absent from
   `orbitPrefix_defect`, which holds with multiplicity.
2. Feed that 0/1 lemma plus `orbitPrefix_defect` into the finite-cut lower bound
   in `CollatzMoonshot/Obstructions/AnchoredCut.lean` to get the exact anchored
   infimum.

Nothing in `OrbitPrefix.lean` needs revisiting for either step; its API is
`transfer_pointCoeff`, `rayCoeff_two_mul`, `rayCoeff_odd_pre`,
`transfer_rayCoeff_eq`, `transfer_orbitPrefixCoeff`, `telescope_sub`.
