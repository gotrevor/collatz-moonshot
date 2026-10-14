# KICKOFF 2026-10-13: Sparre Andersen for the amusical window densities

Treadmill lane.  Target: close the `sorry` in `windowDensityLimit` in
`CollatzMoonshot/AmusicalSpitzer.lean`.  Done when that file is sorry-free.

## Statement

`WindowDensityLimit` (`AmusicalConstant.lean`): `fwdSurv L * bwdSurv L → minimaConstant`, where
`minimaConstant = exp(-Σ'_{k≥0} spitzerTerm (k+1) / (k+1))` and
`spitzerTerm k = Σ_{o ≤ k} C(k,o)/2^k · min 1 (2^(k+o)/3^k)`.
`fwdSurv L` = probability that the forward walk (steps `log(3/2)` or `log(3/4)`, each `1/2`)
stays `> 0` for `L` steps; `bwdSurv L` the same for the backward walk (steps `log(2/3)` w.p.
`1/3`, `log(4/3)` w.p. `2/3`).  Numerics: limits `0.210136`, `0.236892`, product `0.049780`
(`scripts/amusical/spitzer.py`).

## Ratified, do not change

Everything in `Amusical.lean`, `AmusicalWindow.lean`, `AmusicalConstant.lean`,
`AmusicalBound.lean` (another treadmill owns `AmusicalBound.lean`; do not edit it), and the
statements in `AmusicalSpitzer.lean`.  New helpers go in `AmusicalSpitzer.lean` or
`CollatzMoonshot/AmusicalSpitzer/*.lean`.  General random-walk lemmas may go in a generic file
(e.g. `CollatzMoonshot/Probability/SparreAndersen.lean`) stated for any finite-step i.i.d.
walk with no zero partial sums.  No `native_decide`, no new axioms.

## Plan

1. **Duality (easy).**  `P(B_k ≤ 0) = E[e^{-S_k}; S_k > 0]`: both are
   `Σ_{o : 2^(k+o) < 3^k} C(k,o) 2^o / 3^k`.  So `P(S_k ≤ 0) + P(B_k ≤ 0) = spitzerTerm k`.
2. **Survival as a probability.**  Express `fwdSurv L` as `Σ` over patterns of the product
   weight times the all-prefixes-positive indicator (it already is), i.e. `P(S_1..S_L > 0)` for
   an i.i.d. walk; same for `bwdSurv`.
3. **Sparre Andersen.**  For an i.i.d. walk with `P(S_k = 0) = 0`:
   `Σ_{L≥0} P(S_1 > 0, …, S_L > 0) s^L = exp(Σ_{k≥1} s^k P(S_k > 0) / k)` for `|s| < 1`.
   Standard proofs: the cyclic (Spitzer) combinatorial lemma: among the `k` cyclic shifts of
   an increment sequence with positive total and no zero partial sums, exactly as many have
   all partial sums positive as the number of ... (Feller II, XII.6; Spitzer 1956); or the
   Baxter / Wiener-Hopf factorization.  Any route is fine; a finite-weighted-sum (not
   measure-theoretic) formulation over patterns `Fin L → Bool` is likely easiest.
4. **Limit.**  Survival is decreasing in `L`; with `Σ P(S_k ≤ 0)/k < ∞` (exponential tail by a
   Chernoff bound: the forward walk has drift `+½log(9/8) > 0`), Abel's theorem gives
   `lim_L P(survive L) = exp(-Σ_k P(S_k ≤ 0)/k)`.  Same backward (drift `> 0` as well).
5. **Assemble** with step 1: product of limits `= exp(-Σ_k spitzerTerm k / k) = minimaConstant`
   (prove summability so the `tsum` is the real sum).

If the full theorem resists, land the pieces as proved lemmas (duality, the cyclic lemma, the
generating-function identity), each committed green.  Notes for the next lap go in
`HANDOFF-amusical-spitzer.md`.
