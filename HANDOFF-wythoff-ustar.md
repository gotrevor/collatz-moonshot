# HANDOFF: Wythoff Lemma U* (WythoffUStar) — DONE

Kickoff: `KICKOFF-2026-10-17-wythoff-ustar.md`.  Target met: `CollatzMoonshot/WythoffUStar.lean`
is sorry-free; `lake build CollatzMoonshot.WythoffUStar` is green with no warnings; `#print
axioms` on every declaration shows only `propext`, `Classical.choice`, `Quot.sound`.  No ratified
statement changed (the diff against `79f9a1c` removes only `sorry`s and `(drafted, NN%)` labels).

## What landed (2026-10-17)

* `qTilde_mul_prod_eq` (Lemma H½): the factorization of `two_mul_sub_one_gt` without norms;
  `1/2 − s = (−s)(1 − 1/(2s))` per factor (`Multiset.prod_map_mul`), then `field_simp; ring`.
* `abs_two_pow_aeval_half_lt`, `one_lt_three_pow_mul_abs_qTilde` (Corollary U2 bounds), via the
  helpers `norm_multiset_prod_map`, `norm_one_sub_inv_lt`, `prod_norm_one_sub_inv_le/lt`,
  `abs_two_pow_aeval_half_eq` (norms of H½), `coeff_zero_ne_zero_of_conj`, `card_roots_erase`.
  `abs_two_pow_aeval_half_lt` does not need `hd`, `hx2`; a dummy `have` references them so the
  ratified statement stays and the unused-variable linter is quiet.
* `u2_of_boundedRuns`: roots `Nodup` from `Irreducible.separable` over `ℚ` (Gauss) mapped to `ℂ`
  (`RingHom.ext_int` identifies the composite), then `n3_infinite_runs_of_weyl` at `J + 1`.
* `oInf` (Lemma O∞): integers `m_k = Σ_{k<j≤d} e_j2^{d−j}`, odd and `≥ 1`; each single term
  `2^k(m_k − 1) ≤ Σ ≤ 1` (`Finset.single_le_sum`) forces `m_k = 1` directly (no need for
  `sum_eq_zero_iff`); `Finset.sum_Ioc_consecutive` + `Nat.Ioc_succ_singleton` give
  `e_k2^{d−k} = 0`.

## Next

Out of scope per kickoff (later layers): Lemma T, Lemma FL, Theorem L / C′(d), Lemma G, FP1, H1,
Corollary B, mirror side, degree bound.
