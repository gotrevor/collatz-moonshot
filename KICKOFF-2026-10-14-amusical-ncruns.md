# KICKOFF 2026-10-14: run-bounded near-cycles (amusical, ncbaker, Theorem MR)

Repo `collatz-moonshot-amusical-ncruns`: close every `sorry` in `CollatzMoonshot/AmusicalNearCycleRuns.lean`.

## Ratified, do not change

`RhinBound` (a literature hypothesis `Prop`: never prove or assume it outside a theorem's
hypotheses), `numE`, `eRuns`, `excursionWeight` and the four theorem statements.  Everything else is
read-only (you may remove `private` from helpers).  Helpers go in
`CollatzMoonshot/AmusicalNearCycleRuns/*.lean`.  No `native_decide`, no new axioms, no `decide` over
more than a few thousand cases.  Lean lines ≤ 100 characters.  Do **not** edit `RESEARCH-*.md`.
**Commit after every proved target.**

## Paper proofs (agent "ncbaker"; research §38)

Facts: `p` is even (an odd `p > 1` has `U p < p`, which would re-enter `[0, p + D]` below `p`).
Every intermediate point of the excursion is `> p + D`; `x_g = U^g p ∈ (p, p + D]`.

1. **MR (I) `nearCycleAt_linearForm`.**  Multiply the steps:
   `x_g / p = (3^g / 2^a) ∏_{odd i} (1 + e_i/(3 x_i))`, `e_i = +1` (A, `x ≡ 1 mod 4`), `−1` (B).
   So `Λ = ln(x_g/p) − S`, `S = Σ_odd ln(1 + e_i/(3x_i))`, and `0 < ln(x_g/p) ≤ ln(1 + D/p) < D/p`.
   Bound `|S|` run by run: an odd step `z → z'` has `3z ≥ 4z' − 1`, i.e. `z − 1 ≥ (4/3)(z' − 1)`; so
   the `i`-th odd source back from the run's end `X` has `z − 1 ≥ (4/3)^i (X − 1)`, and with
   `|ln(1 ± u)| ≤ u/(1 − u)` the term is `≤ 1/(3z − 1) < (3/4)^i/(3(X − 1))`; the run adds
   `< 1/(X − 1)`.  Each run ends at a local minimum `> p + D` or at `x_g ≥ p + 1`, so
   `|S| < m/p`.  Multiply by `p`.  (A run is a maximal block of odd steps between `E`-runs; the
   number of odd runs is `≤ eRuns p g`, since the excursion starts with an `E`-step.)
2. **MR (II) upper `nearCycleAt_numE_le`.**  Local minima `x_0 = p, x_1, …` (starts of `E`-runs).
   The `j`-th `E`-run has length `a_j ≤ log₂ x_j` (`2^{a_j} ∣ x_j`); it peaks at
   `(3/2)^{a_j} x_j ≤ x_j^θ`; the following odd run strictly decreases, so `x_{j+1} < x_j^θ`.
   Hence `log₂ x_j ≤ θ^j log₂ p`, and `#E ≤ Σ_{j < m} a_j ≤ log₂ p · (θ^m − 1)/(θ − 1)`.
3. **MR (II) lower `nearCycleAt_numE_ge`.**  From (I): `gθ − a = Λ/ln 2 > −m/(p ln 2) > −1` since
   `p > 1.5 m > m/ln 2`.  So `a < gθ + 1` and `#E = 2g − a > (2 − θ) g − 1`.
4. **MR-P `nearCycleAt_le_of_eRuns_le`.**  If `p ≤ 1.5 m` the bound is trivial for `C m ≥ 1.5 m`.
   Else by (I) `p · |Λ| < D + m` and `RhinBound` gives `|Λ| ≥ max(a, g)^(−13.3)` with
   `a ≤ 2g`, so `p < (D + m)(2g + 2)^13.3`.  By (II) `log₂ p ≥ c_m((2 − θ)g − 1)`,
   `c_m = (θ − 1)/(θ^m − 1)`, so `g ≤ C'_m (log₂ p + 1)`.  Combine:
   `p ≤ (D + m)(C''_m (log p + 1))^13.3`, which bootstraps to `p ≤ C_m D (log D + 1)^13.3`
   (the `log p` on the right is `≤ 2 log D + O_m(1)` once `p ≥ D^2`, else trivially).  Any explicit
   `C m` works; it need not be good.

Notes for the next lap go in `HANDOFF-amusical-ncruns.md`.
