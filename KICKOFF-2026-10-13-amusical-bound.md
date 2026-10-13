# KICKOFF 2026-10-13: orbit minima of the amusical permutation have upper density < 1/20

Treadmill lane.  One target: close the `sorry` in `windowDensity_two_hundred_lt` in
`CollatzMoonshot/AmusicalBound.lean` (`fwdSurv 200 * bwdSurv 200 < 1/20`).  Done when that
file is sorry-free; `orbitMin_density_lt_one_twentieth` then follows (already proved from it).

## Context

`fwdSurv L` and `bwdSurv L` (`CollatzMoonshot/AmusicalWindow.lean`) are sums over all
`w : Fin L → Bool` of a weight times the indicator that every prefix survives:

* forward: weight `(1/2)^L`; prefix `t` survives when `2^(t + o_t) < 3^t`, `o_t` the number of
  `true` marks among the first `t`;
* backward: weight `(2/3)^#true (1/3)^#false`; prefix `t` survives when `3^t < 2^(t + b_t)`.

`windowMinDensity` (proved) makes `δ_L = fwdSurv L * bwdSurv L` an upper bound on the density
of orbit minima.  Exact values: `δ₄ = 4/27` (checked by `windowDensity_values`),
`δ₁₀₀ = 0.050844`, `δ₁₅₀ = 0.050098`, `δ₂₀₀ = 0.0498876` (lattice DP over exact rationals,
2026-10-13).  `2^200` terms cannot be enumerated, so a DP is required.

## Ratified, do not change

Everything in `Amusical.lean`, `AmusicalWindow.lean`, `AmusicalConstant.lean`, and the
statements of `windowDensity_two_hundred_lt` and `orbitMin_density_lt_one_twentieth`.  Add
helpers in `AmusicalBound.lean` or new `CollatzMoonshot/AmusicalBound/*.lean` files.  No
`native_decide`, no new axioms.  `decide +kernel` is allowed (used already in
`windowDensity_values`).

## Plan

1. **DP form.**  Define `fwdDP : ℕ → ℕ → ℚ` (`fwdDP t o` = total weight of surviving length-`t`
   prefixes with `o` marks), with `fwdDP 0 0 = 1` and the step adding a mark or not, keeping
   only states with `2^(t+1+o') < 3^(t+1)`.  Prove `fwdSurv L = Σ_o fwdDP L o`.  The induction
   splits `Fin (L+1) → Bool` into a prefix and a last bit (`Fin.snoc`/`Fin.cons` equivalences);
   survival of a length-`(t+1)` pattern is survival of its prefix and of the new full prefix.
   Same for `bwdDP` with weights `2/3`, `1/3`.
2. **Evaluate.**  Compute `Σ_o fwdDP 200 o * Σ_b bwdDP 200 b` as an exact rational and compare
   with `1/20`.  The state space has `≈ 200²/2` entries with `≈ 600`-bit numbers.  If a direct
   `decide +kernel` is too slow, (a) make the DP a `List`/array fold that the kernel reduces
   well, (b) prove a monotone upper bound with rounded (dyadic) entries instead of exact ones,
   or (c) split the evaluation into checked chunks.  Any certified upper bound below `1/20` is
   enough: `δ₂₀₀` has margin `1.1·10⁻⁴`.
3. If `L = 200` is impractical, a smaller `L` with an honest bound is still progress: record it
   as a proved theorem (`δ₁₀₀ < 51/1000`, say), commit, and keep pushing toward `1/20`.

## Checkpoints

Sanity-check the DP against `windowDensity_values` (`L ≤ 4`) before trusting it.  Commit each
green lemma.  Notes for the next lap go in `HANDOFF-amusical-bound.md`.
