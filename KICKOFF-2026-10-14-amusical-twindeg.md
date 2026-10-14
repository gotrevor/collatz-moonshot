# KICKOFF 2026-10-14: the twin's cycle degrees (amusical)

Repo `collatz-moonshot-amusical-twindeg`: close every `sorry` in `CollatzMoonshot/AmusicalTwinDegree.lean`.

## Ratified, do not change

All statements and definitions in that file (`twinExceptional`, `twinClass`, and the seven theorems),
and everything in `AmusicalFunctionField.lean` (`twinQ`, `twinU`, `twinCycle`, all proved; reuse
`FFTwin.*` and `AmusicalFunctionField/Cycle.lean`).  Everything else in the repo is read-only.  Helpers
go in `CollatzMoonshot/AmusicalTwinDegree/*.lean`.  No `native_decide`, no new axioms.  Lean lines ≤ 100
characters.  **Commit after every proved target** (an uncommitted final lap is lost to the merge).

⚠️ **Resource rule.**  Never use `decide` or `decide +kernel` over more than a few thousand cases.  An
exhaustive check on 2026-10-13 caused a global out-of-memory that took Docker down.  These proofs are
polynomial algebra and degree bookkeeping.

## Suggested order

1. **`twin_den_natDegree` (D1).**  Write `p = 2^v q` (`Nat.exists_eq_two_pow_mul_odd`).  Frobenius
   (`sub_pow_char_pow`) gives `(X^{2q} − Q^q)^{2^v}`, and `natDegree_pow`.  For odd `q`: the
   coefficient of `X^{2q}` in `Q^q` is `1` (leading, `Q` monic of degree 2) and that of `X^{2q−1}` is
   `q • 1 = 1` (`Polynomial.coeff_pow` / `nextCoeff`: `nextCoeff (Q^q) = q * nextCoeff Q`, see
   `Polynomial.nextCoeff_pow` or `Monic.nextCoeff_pow`).  So the difference has degree exactly `2q − 1`.
2. **`twinU_twinU_sq`.**  Unfold `twinU` on `n²`; in characteristic 2, `(n²).coeff (2k+1) = 0` and
   `(n²).coeff (2k) = n.coeff k` (`Polynomial.expand`, `frobenius`, `expand_char`).  Then `n = X m`
   or `n = 1 + X² m`, and `divByMonic` of an explicit multiple.
3. **`twin_not_periodic_of_selfSimilar` (Prop M).**  Pure dynamics plus degrees; paper proof in the
   docstring.  The forward orbit of a periodic point is finite (`Function.periodicOrbit`), so take
   `y` of maximal `natDegree` on it.
4. **Theorem D (`twin_cycleMin_natDegree_le`).**  The main target.
   * Step lemma: for `x ∉ twinExceptional`, `natDegree (twinU x) = natDegree x + 1, + 0, − 1, − 1` by
     class `E, A, B, C`, and `2^{depth} • twinU x`-style identity `X^{d} * twinU x = Q * x + e`.
   * Iterate: `X^{N_j} * twinU^[j] x = Q^j * x + c_j` with `c_{j+1} = Q c_j + X^{N_j} e_j`.
   * On a cycle `N_p = 2p` (degree returns), so `x * (X^{2p} − Q^p) = c_p` (characteristic 2).
   * Bound `natDegree c_p ≤ 2p + 2` termwise using `hmin`, then `twin_den_natDegree`.
5. **`twin_period_lower_bound`, `twin_cycleMins_finite`.**  From Theorem D and the walk; the
   exceptional cycles by hand (degrees ≤ 2).  Finiteness: polynomials of bounded degree over `ZMod 2`
   form a finite set (`Polynomial.degreeLTEquiv`).
6. **`twin_no_classwise_frobenius`.**  Paper proof in the docstring; it needs `U² x = x → x ∈ {0, 1}`,
   from step 5 (degree ≤ 5) plus a finite check over the 64 polynomials of degree ≤ 5 (that is the
   one place a small `decide` over explicit polynomials might help, but ZMod-2 polynomial equality is
   not decidable by `decide`; prefer evaluating `twinU` on explicit forms by hand).  Then compute
   `κ_B`, `κ_C` and the failure at `n = X` (`scripts/amusical/twin/classwise_ren.py` prints them).

Notes for the next lap go in `HANDOFF-amusical-twindeg.md`.
