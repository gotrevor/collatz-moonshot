# HANDOFF: wythoff-runcrit (RunCriterion from Weyl)

Kickoff: `KICKOFF-2026-10-17-wythoff-runcrit.md`.  File: `CollatzMoonshot/WythoffRunCriterion.lean`.

## Log

* `linearIndependent_freqVec` **proved** (helper `eq_zero_of_natDegree_lt`: a rational
  polynomial of degree `< d` vanishing at `x` is zero, via `minpoly`).  Degree-1 `P` handled
  separately (empty frequency family).
