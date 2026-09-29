# Authorized bounded proof task

Trevor explicitly requested pursuing the next targets with delegated implementation.  Work only in CollatzMoonshot/Obstructions/OrbitPrefix.lean and HANDOFF-2026-09-28-orbit-prefix.md.  The host owns root imports; other workers own disjoint experiments/notes.  Do not modify existing Lean modules, DIRECTION, root imports, or experiments.  The definitions pointCoeff and orbitPrefixCoeff and proposition orbitPrefix_defect are frozen.  If false, supply a counterexample rather than weakening it.  Prove the general theorem and include the three stated finite controls.  Build root, write handoff, commit green, and stop; no successor task.  Warm dependencies checked; no downloads/cache fetches.  This is a bounded algebraic formalization, not a general Collatz campaign.

# Frozen node: arbitrary dyadic ray plus finite orbit prefix

Source to add: `CollatzMoonshot/Obstructions/OrbitPrefix.lean`.  The staged skeleton is beside this kickoff.  Import `PositiveApproximation.lean`, which already proves that the `List.range (v+1)` cutoff in `rayCoeff` is lossless for a positive base (`ray_any_iff`, `rayCoeff_eq_one`, `rayCoeff_eq_zero`).  Use the actual `ArithmeticLifts.transfer : (ℕ → ℚ) → ℕ → ℚ` and `FrontB.tstep`.

## Frozen acceptance statement

For every `n>0`, `L>0`, and positive coefficient index `v`, with

```
orbitPrefixCoeff n L v = rayCoeff n v
  + ∑ j∈Finset.Ico 1 L, [v=(tstep^[j]) n],
```

prove

```
transfer (orbitPrefixCoeff n L) v - orbitPrefixCoeff n L v
  = [v=(tstep^[L]) n].
```

Here `[P]` is the rational point coefficient `if P then 1 else 0`.  The theorem is pointwise and uses the existing truncated-search implementation of the infinite dyadic ray.  It quantifies over every positive `n`, including even `n` and `n=1`.  Do not assume the orbit points are distinct, outside the ray, eventually bounded, or convergent.  If a point repeats, its coefficient is counted with multiplicity.  The theorem is an algebraic identity and is not an independent Collatz estimate.

The exact staged Lean type is `orbitPrefix_defect` in `OrbitPrefix.lean`.  Preserve that proposition; helper names and proof structure may change.

## Elementary proof

1. First establish positivity of every iterate `(tstep^[j]) n` from `hn` using `FrontB.tstep_pos` by induction.  This is needed when applying the point-mass transfer lemma.
2. Prove the point-mass formula, for positive `u,v`:
   `transfer (pointCoeff u) v = pointCoeff (tstep u) v`.  Split on parity of `u`.  If `u=2v`, the even predecessor term is one and the odd term zero; if `u=(2v-1)/3` with `v%3=2`, the odd predecessor term is one and the even term zero.  In all other cases both are zero.  `AnchoredCut.mem_predecessors` documents the same fiber arithmetic for the real transfer, but the point-mass proof should be direct at rational coefficients.
3. Prove the ray formula, for `n,v>0`:
   `transfer (rayCoeff n) v - rayCoeff n v = pointCoeff (tstep n) v`.  The dyadic ray is `{2^h n:h≥0}`.  Every term with `h≥1` is even and maps to its predecessor; those images reproduce the ray, one copy each.  The base term maps to `tstep n`.  This remains true if `n` is even, when `tstep n=n/2`, and if `n=1`, when the extra image at `2` overlaps an existing ray term.  Use `ray_any_iff` to replace the finite `List.range` search with an existential support statement before manipulating exponents.  Avoid assuming the base is odd: the `rayAt_two_mul` helper in `PositiveApproximation.lean` relies on that assumption and cannot be used unchanged.
4. Transfer is pointwise additive and distributes over the finite prefix sum.  By step 2, the transferred prefix is `∑_(j=1)^(L-1) pointCoeff (tstep^[j+1] n) v`.  Subtract the original prefix to obtain `pointCoeff (tstep^[L] n) v - pointCoeff (tstep n) v`.  This is a finite telescoping identity and remains valid with repeated states.
5. Add step 3.  The two `pointCoeff (tstep n) v` terms cancel.  There is no norm or infinite-sum step.

## Controls and next node

The case `L=1` reduces to the ray formula.  Test the even base `n=8,L=1` (defect at `4`) and the odd base `n=3,L=2` (defect at `8`).  `n=1,L=3` exercises repetition and ray overlap: the coefficient at `2` occurs both on the ray and in the prefix, yet the defect is still a single point mass at `tstep^[3] 1=2`.  These are concrete sanity controls; the quantified theorem is the deliverable.

After this identity is proved, the separate 0/1 lemma needs injectivity of the prefix and proof that its points miss the dyadic ray.  Those hypotheses are consequences of nonperiodicity for the sharp bounded-orbit extremizer, but they are intentionally absent from this algebraic node.  A later node can combine this identity with the finite-cut lower bound in `AnchoredCut.lean` to obtain the exact anchored infimum.
