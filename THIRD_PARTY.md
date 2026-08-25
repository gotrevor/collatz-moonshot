# Third-party material

## Shifted Legendre polynomial lemmas

Parts of `CollatzMoonshot/FrontA/Legendre.lean`—the definition of
`shiftedLegendre` and the lemmas `shiftedLegendre_eq_sum`,
`shiftedLegendre_eq_int_poly`, `shiftedLegendre_poly_eval_zero_eq_zero`, and
`shiftedLegendre_poly_eval_one_eq_zero`—were adapted for Lean `v4.33.1` from:

- ahhwuhu, [`zeta_3_irrational`](https://github.com/ahhwuhu/zeta_3_irrational),
  `Zeta3Irrational/LegendrePoly.lean`, commit
  [`e8785315a01c8fbcddaa0fc03b3c8b29a61bc1f1`](https://github.com/ahhwuhu/zeta_3_irrational/commit/e8785315a01c8fbcddaa0fc03b3c8b29a61bc1f1).

The source project is released under Apache-2.0. The adapted file changes imports,
namespace, proof details, documentation, and toolchain compatibility, and adds the
remaining CollatzMoonshot-specific analytic development.

## Published mathematical results

The repository encodes some published results as named Lean axioms rather than copying
their proofs. Each such declaration has a provenance note in `CollatzMoonshot/Assumed/`
or at its declaration site. These are logical dependencies, not claims that the cited
papers have themselves been formalized here.
