# HANDOFF — amusical uniform

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
