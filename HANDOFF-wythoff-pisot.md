# HANDOFF: wythoff-pisot (Theorem N3, Lemma B2)

Kickoff: `KICKOFF-2026-10-17-wythoff-pisot.md`.  File: `CollatzMoonshot/WythoffPisot.lean`.

## Status

* Closed: `perturb`, `sum_synDiv_mul_pow_eq_zero`, `pow_ne_one_of_irreducible`,
  `eval_one_ne_zero_of_irreducible`, `coeff_zero_ne_zero_of_irreducible`,
  `two_pow_mul_aeval_half_odd`.  Theorem N3 (`n3_runSystem`, `n3_infinite_runs` conditional on
  `RunCriterion`) is fully proved.
* Closed: `two_mul_sub_one_gt` (Lemma B2 gap), hence `run_bound_B2`.
* **File sorry-free.**  `lake build CollatzMoonshot.WythoffPisot` green with no warnings;
  `#print axioms` on all 41 declarations: `propext, Classical.choice, Quot.sound` only.
  `RunCriterion` stays a hypothesis of `n3_infinite_runs`, as ratified.  No ratified statement
  changed.

## Notes

* `minpoly.eq_of_irreducible_of_monic` needs a *field* base: over `ℤ` it times out in instance
  search (whnf).  Route: Gauss (`Monic.irreducible_iff_irreducible_map_fraction_map`) to `ℚ[X]`,
  then the field lemma and `minpoly.dvd`; `aeval_map_algebraMap` moves roots across.
* `perturb` uses filters: `Ioo_mem_nhdsGT` for `ε_0`, continuity + `Ioo_mem_nhds` for `i ≥ 1`,
  `Filter.eventually_all_finset`, `Filter.Eventually.exists`.  `nhdsWithin_le_nhds` needs
  `(s := Set.Ioi 0)` spelled out.
* `perturb`'s `hd` is unused; `clear hd` does not silence the unused-variable linter, a
  `have _ : 1 ≤ d := hd` does.
* Helpers added: `natDegree_eq_one_of_dvd`, `sum_coeff_mul_eq_synDiv_complex`.
* B2 gap: only the non-strict `∏‖1/2 − s‖ ≤ (3/2)^{d−1}∏‖s‖` is needed (multiset induction,
  `prod_norm_half_sub_le`); strictness comes from `∏‖s‖ = |a_0|/x < 2|a_0|`.  Factorisation via
  `IsAlgClosed.card_roots_eq_natDegree` + `prod_multiset_X_sub_C_of_monic_of_roots_card_eq`,
  `Multiset.cons_erase`; real/complex bridge `eval_ofReal_map` (`algebraMap_int_eq`,
  `eval_map_algebraMap`, `aeval_algebraMap_apply`).

## Next (out of scope here, later layers)

Proving `RunCriterion` (Theorem N4 + zonotope openness, from `WeylEquidistributionMulti`); classify
Theorem M (mirror side); Proposition B1 and the `(d, |a_0|)` lists; pisot §4 U pairings.
