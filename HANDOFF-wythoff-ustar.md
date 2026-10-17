# HANDOFF: Wythoff Lemma U* (WythoffUStar)

Kickoff: `KICKOFF-2026-10-17-wythoff-ustar.md`.  Target: `CollatzMoonshot/WythoffUStar.lean`
sorry-free, warning-free.

## Status (2026-10-17)

* Proved: `qTilde_mul_prod_eq` (Lemma H½), `abs_two_pow_aeval_half_lt`,
  `one_lt_three_pow_mul_abs_qTilde`, `u2_of_boundedRuns` (Corollary U2).
  Helpers added above them: `norm_multiset_prod_map`, `norm_one_sub_inv_lt`,
  `prod_norm_one_sub_inv_le`, `prod_norm_one_sub_inv_lt`, `abs_two_pow_aeval_half_eq`,
  `coeff_zero_ne_zero_of_conj`, `card_roots_erase`.
* `abs_two_pow_aeval_half_lt` does not need `hd`, `hx2`; they are referenced by a dummy `have`
  to keep the ratified statement and silence the unused-variable linter.
* Open: `oInf` (Lemma O∞).
