# HANDOFF — amusical uniform

## 2026-10-14 review lap: `delta_periodic` complete

Fresh reconstruction from the ratified source commit `1f05431` found no statement drift: the
four original target declarations are unchanged, and the existing arithmetic transition lemmas
are on the advertised route.  This lap closed `delta_periodic` without changing its statement.

For a multiple of four, write the shifted coordinate as
`c = u * 2^a * 3^b`, where `u` is odd and not divisible by three.  The new proof constructs a
cycle rather than merely proving that the forward range is finite:

1. `delta_contract_run` transfers the `b` factors of three to factors of two.
2. `delta_expand_between_multiples` follows the intervening affine run in `a + b + 6` steps,
   transferring all `a + b` factors of two to factors of three.
3. A final `a` contractions recover the original coordinate.

Thus every nonzero `c` has the explicit positive period `2 * (a + b) + 6`; `c = 0` is the fixed
point `-8`.  The residue-class reachability lemmas show that every integer reaches a multiple of
four or the other fixed point `-7`.  Injectivity from `deltaInv_delta` cancels that finite prefix.
The previously added generic pigeonhole lemma `periodic_of_finite_forwardOrbit` also now checks in
the full module, although the constructive proof no longer needs it.

Verification run:

```text
lake env lean CollatzMoonshot/AmusicalUniform.lean
~/personal/bin/lean-green \
  /Users/gotrevor/src/collatz-moonshot-amusical-uniform \
  --target CollatzMoonshot.AmusicalUniform \
  --axioms CollatzMoonshot.Amusical.delta_periodic
```

The narrow check succeeded.  The real gate built 8711 jobs and ended
`FORMALIZE-TIER GREEN`.  The axiom ledger for `delta_periodic` is exactly
`[Classical.choice, Quot.sound, propext]`.  No `native_decide` or new axiom was introduced.
Only the three unchanged targets `no_piecewiseAffine_reversor_of_valNonneg`,
`island_cycle_slope`, and `amusical_topologicallyTransitive` remain open in the scoped file.

Next highest-value attack: `island_cycle_slope`, following the kickoff order.  First turn `hZ`
plus injectivity of `ι` into a permutation of the finite `σ`-orbit (with multiplicities modulo
`L`).  Refine one residue class around each of the finitely many cycle points so `σ`, `ι`, and
the required inverse branch are affine there.  The conjugacy gives the pointwise slope identity
`t(σx) * s(x) = t(x) / s(σ⁻¹ιx)`; multiplying around the `L` positions cancels the
`t` factors and permutes the denominator `s` factors, yielding `S² = 1`, hence `S = ±1` in `ℚ`.
`AmusicalReversal.lean` contains the group-conjugacy patterns to reuse.  Do not start the harder
topological-transitivity target before the Island Lemma and NR_p are closed.

## 2026-10-14 finite-orbit reduction checkpoint

The route-decisive `delta_periodic` proof now has its abstract pigeonhole layer discharged.
`periodic_of_finite_forwardOrbit` proves that an injective self-map is periodic at `x` whenever
the range of `n ↦ f^[n] x` is finite.  The proof uses finite pigeonhole, orders the repeated
indices, and cancels the shorter iterate using injectivity.  It is generic but was added beside
the `delta` lemmas because it is exactly the final step required once the `2`-`3` lattice
invariant makes the explicit forward orbit finite.

Verification attempted:

```text
ulimit -n 4096; lake env lean CollatzMoonshot/AmusicalUniform.lean
ulimit -n 4096; ~/personal/bin/lean-green \
  /Users/gotrevor/src/collatz-moonshot-amusical-uniform \
  --target CollatzMoonshot.AmusicalUniform
ulimit -n 4096; lake env lean /tmp/TestPeriodic.lean
```

The first narrow run reached the new proof and exposed two ordinary elaboration errors, which
were corrected.  Every subsequent narrow run and the real gate failed while opening unrelated
mathlib `.olean` files with host-wide `Too many open files`; the gate ended `RED` for that
environmental reason before elaborating this module.  A minimal file importing only the finite
set and pigeonhole modules checked the exact new proof successfully.  This checkpoint is
intentionally not committed yet: the treadmill policy permits committing only after a green gate.

Next highest-value attack: once the host file table clears, rerun the narrow check and real gate,
then commit.  Continue `delta_periodic` by defining the finite set of shifted coordinates with
fixed `6`-free part and fixed total `2`/`3` exponent.  The already proved transition lemmas show
the only changes at multiples of four are `c ↦ 2c/3` and `c ↦ 3c/2`; prove the forward orbit has
finite range and finish immediately with `periodic_of_finite_forwardOrbit` plus
`deltaInv_delta` for injectivity.

## 2026-10-14 lap checkpoint

Primary objective remains making `CollatzMoonshot/AmusicalUniform.lean` sorry-free. The file has
four unchanged open targets: `no_piecewiseAffine_reversor_of_valNonneg`, `island_cycle_slope`,
`amusical_topologicallyTransitive`, and `delta_periodic`.

This lap formalized both load-bearing arithmetic edges in the proposed proof of
`delta_periodic`. For a multiple of four written `4*k`, with shifted coordinate `c = k + 2`:

- `delta_four_contract` and `delta_four_contract_coordinate` prove that `3 ∣ c` sends
  `c` to `2*c/3` in one forward `delta` step.
- `deltaInv_four_expand` and `deltaInv_four_expand_coordinate` prove that `2 ∣ c` sends
  `c` to `3*c/2` in one backward `deltaInv` step.

All four lemmas are direct integer arithmetic proofs (`split_ifs; omega`) and introduce no new
axioms or computation certificates. This pins down the exact dihedral lattice action; previously
it existed only in the target docstring.

Verification run:

```text
ulimit -n 4096; lake env lean CollatzMoonshot/AmusicalUniform.lean
ulimit -n 4096; ~/personal/bin/lean-green \
  /Users/gotrevor/src/collatz-moonshot-amusical-uniform \
  --target CollatzMoonshot.AmusicalUniform
```

Both completed successfully. The real gate built 8711 jobs and ended `FORMALIZE-TIER GREEN`, with
only the four expected target `sorry` warnings (plus inherited proof debt in `AmusicalAntiKohl`).
The temporary `ulimit` was needed because the shared host intermittently returned `ENFILE`; it is
not a project setting or source change.

Next highest-value attack: finish `delta_periodic`. Prove that every point reaches a multiple of
four (or fixed point `-7`) within a uniformly bounded number of forward or backward steps. Then
show the shifted coordinates at multiples of four lie in the finite set obtained by redistributing
the fixed total exponents of `2` and `3` in `|c|`; use injectivity of `deltaPerm` to turn finiteness
of the two-sided orbit into a positive forward period. The newly proved coordinate lemmas are the
two transition cases needed for that invariant.
