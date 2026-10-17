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
