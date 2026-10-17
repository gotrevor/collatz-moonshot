# HANDOFF 2026-10-17: wythoff-pisot DONE

Branch `wip/wythoff-pisot-m`, HEAD `5cdaf7b` (before this doc).  Kickoff
`KICKOFF-2026-10-17-wythoff-pisot.md`; running notes `HANDOFF-wythoff-pisot.md`.

## Done

`CollatzMoonshot/WythoffPisot.lean` is sorry-free; `lake build CollatzMoonshot.WythoffPisot` green,
no warnings; `#print axioms` on all 41 declarations shows only `propext, Classical.choice,
Quot.sound`.  No ratified statement changed; `RunCriterion` remains a hypothesis.

* Theorem N3: `n3_runSystem` (unconditional), `n3_infinite_runs` (conditional on `RunCriterion`).
  New proofs: `perturb`, `sum_synDiv_mul_pow_eq_zero`, `pow_ne_one_of_irreducible`,
  `eval_one_ne_zero_of_irreducible`, `coeff_zero_ne_zero_of_irreducible`.
* Lemma B2: `two_pow_mul_aeval_half_odd`, `two_mul_sub_one_gt`, hence `abs_aeval_half_ge`,
  `run_bound_B2`.
* Helpers: `natDegree_eq_one_of_dvd`, `sum_coeff_mul_eq_synDiv_complex`,
  `norm_multiset_prod_sub`, `prod_norm_half_sub_le`, `eval_ofReal_map`.

`box done --green` signalled.  Not pushed (host pushes).

## Next steps (later layers, not started)

1. Prove `RunCriterion` from `WythoffAutomaton` + `WeylEquidistributionMulti` (Theorem N4: fresh
   phases uniform on `(0,1)^{d−1}`; zonotope openness gives positive measure).
2. Classify Theorem M (mirror side); Proposition B1 (Mahler bound) and the `(d, |a_0|)` lists;
   pisot §4 U pairings.
