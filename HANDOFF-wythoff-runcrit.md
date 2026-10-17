# HANDOFF: wythoff-runcrit (RunCriterion from Weyl)

Kickoff: `KICKOFF-2026-10-17-wythoff-runcrit.md`.  File: `CollatzMoonshot/WythoffRunCriterion.lean`.

## Log

* `linearIndependent_freqVec` **proved** (helper `eq_zero_of_natDegree_lt`: a rational
  polynomial of degree `< d` vanishing at `x` is zero, via `minpoly`).  Degree-1 `P` handled
  separately (empty frequency family).
* `exists_runBox` **proved**, via three step lemmas `fresh_step`, `top_step`, `std_step` (each a
  `half_int_pin` application returning oddness and the exact error `e_l = −E`).  Main proof:
  `K = |q̃_0| + Σ_{k<d}|q_k| + Σ_{j≤n} x^j`, `η_l = (1+K)^l r` with `r + KΣ_{j<l}η_j = η_l`,
  `r` chosen by `∀ᶠ r in 𝓝[>] 0` (per-index margins `min(ε_l, 1/2 − ε_l)`, no global min).
  So `runCriterion_of_weyl` and `n3_infinite_runs_of_weyl` are now complete (headline path done).
* Remaining: `runSystem_phaseVec_of_odd` (off headline path).
* `runSystem_phaseVec_of_odd` **proved** (box via `Irrational.intCast_mul`/`ne_int` at `l = 0`,
  `irrational_xOf.mul_intCast` with `W^l(2k) > 0` for `l ≥ 1`; rows via the two parity iffs).

## Status: DONE

`CollatzMoonshot/WythoffRunCriterion.lean` sorry-free; `lake build
CollatzMoonshot.WythoffRunCriterion` green with no warnings.  `#print axioms` for
`runCriterion_of_weyl`, `n3_infinite_runs_of_weyl`, `runSystem_phaseVec_iff`:
`[propext, Classical.choice, Quot.sound]`.  No ratified statement changed (diff vs `11c6cf8`
removes only `sorry`s and `(drafted …)`/`(assembled …)` docstring labels).
`WeylEquidistributionMulti` remains a hypothesis argument.

Next layers (out of scope here, per kickoff): positive density of long-run up-points; necessity
half of the zonotope criterion; mirror side (Theorem M); wiring `CollatzMoonshot.lean`.
