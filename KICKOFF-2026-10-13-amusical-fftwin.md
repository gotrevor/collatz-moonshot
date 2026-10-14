# KICKOFF 2026-10-13: the F₂[t] twin (amusical)

Repo `collatz-moonshot-amusical-fftwin`: close every `sorry` in `CollatzMoonshot/AmusicalFunctionField.lean`.

## Ratified, do not change

All statements and definitions in that file (`twinQ`, `twinU`, `twinCycle`).  Everything else in the
repo is read-only.  Helpers go in `CollatzMoonshot/AmusicalFunctionField/*.lean`.  No `native_decide`,
no new axioms.  Lean lines ≤ 100 characters.

⚠️ **Resource rule.**  Never use `decide` or `decide +kernel` over more than a few thousand cases.  An
exhaustive check on 2026-10-13 caused a global out-of-memory that took Docker down.  These proofs are
polynomial algebra.

## Suggested order

1. **`amusical_EmBm_not_integral`.**  For `m ≥ 5`, show `0 < 8^m − 6^m < 9^m − 8^m`, then use
   `Int.eq_zero_of_dvd_of_natAbs_lt_natAbs` or similar.  `m = 2, 3, 4`: `decide`/`norm_num`.
   `2^m (4^m − 3^m) = 8^m − 6^m`.
2. **`twin_den_frobenius`.**  Characteristic 2: `sub_pow_char_pow` / `add_pow_char_pow`
   (`CharP (ZMod 2)[X] 2`), then `X^2 − (X^2+X+1) = X + 1` up to sign (`−1 = 1` in `ZMod 2`).
3. **`twinU_bijective`.**  Build the inverse, reading `y mod Q` (`modByMonic`, with `twinQ` monic of
   degree 2): residue `0 ↦ t m`, `1 ↦ 1 + t² m`, `t ↦ 1 + t + t³ m`, `1 + t ↦ 1 + t + t² + t³ m`,
   with `m = y /ₘ Q`.  Prove both compositions.  Low coefficients drive the case split; use
   `Polynomial.modByMonic_add_div`.
4. **`twinCycle_minimalPeriod`** (main).  Prove a step lemma for each branch on the explicit forms,
   then the orbit of `twinCycle e` in closed form.  The paper proof is in the docstring, and
   `scripts/amusical/twin/fftwin_ren.py` prints the itinerary.
   * Suggested invariant: after `j ≤ m` steps the point is `Q^j · e_B · t^{m−j} (t+1)^{m−3}`, which
     is still divisible by `t` while `j < m`.  So the `E` steps are pure multiplication by `Q/t`.
   * Then `m` `B` steps, with closed form via the geometric sum and Frobenius.
   * Exact period: the itinerary of length `2^e` is primitive, and a proper divisor period `d`
     would force the itinerary to be `d`-periodic.
5. **`twin_infinitelyManyCycles`.**  From step 4: the cycles of `twinCycle e` for `e ≥ 3` have
   distinct cardinalities `2^e`.

Notes for the next lap go in `HANDOFF-amusical-fftwin.md`.
