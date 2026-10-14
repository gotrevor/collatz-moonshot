# KICKOFF 2026-10-13: escape and Theorem N (amusical)

Repo `collatz-moonshot-amusical-escape`: close every `sorry` in `CollatzMoonshot/AmusicalEscape.lean`.

## Ratified, do not change

All statements in that file, the definitions `stepBits`, `fwdBits`, `bwdBits`, `BackwardNormal`, and the
proved `abs_amusical_le`, `abs_amusicalInv_le`.  Everything else in the repo is read-only.  Helpers go in
your own file or in `CollatzMoonshot/AmusicalEscape/*.lean`.  No `native_decide`, no new axioms.  Lean
lines ≤ 100 characters.

## Paper proofs (agent report q1.md §2–§3)

1. **`escape_forward`.**
   * Since `U` is injective and `m` is not periodic, the points `Uʲ m` are pairwise distinct.  So
     for each `X`, only finitely many `j` have `|Uʲ m| < X`.
   * Suppose instead that `fwdBits m k > (λ + δ) k` for all `k ≥ K`, where `λ = log₂ 3`.
   * Choose `X` with `1 + 1/(3X) ≤ 2^(δ/2)`, and `k₀ ≥ K` with `|Uʲ m| ≥ X` for `j ≥ k₀`.
   * By `abs_amusical_le`, `|U x| ≤ (3/2^b)|x| · 2^(δ/2)` for `|x| ≥ X`.
   * Hence `|Uᵏ m| ≤ C · 3^k · 2^(−fwdBits m k) · 2^(δk/2) ≤ C · 2^(−δk/2) → 0`.  This contradicts
     `|Uᵏ m| ≥ X ≥ 1` for large `k` (pick `X ≥ 1`).
   * Work with logarithms, or with real powers `(2:ℝ)^(x:ℝ)`, so the exponent `λ k` needs no
     rounding.
2. **`escape_backward`.**
   * Same proof with `abs_amusicalInv_le`: `|U⁻¹ x| ≤ (2^b/3)|x|(1 + 1/(2X))`.
   * The points `U⁻ʲ m` are pairwise distinct too: if `U⁻ⁱ m = U⁻ʲ m` with `i < j`, apply `Uʲ`.
3. **`periodic_of_evenFrequency_lt`.**
   * `fwdBits m k = 2k − #even steps < k`, so `fwdBits m k / k → 2 − c > λ`.
   * Take `δ = (2 − c − λ)/2`.  Eventually `fwdBits m k ≥ (λ + δ) k`, which contradicts
     `escape_forward` unless `m` is periodic.
   * Argue by contradiction: assume `∀ p ≥ 1, Uᵖ m ≠ m`.
4. **`not_reversor_of_evenFrequency_lt`.**
   * `IsAmusicalReversor` gives `ι (U⁻ʲ n) = Uʲ (ι n)`: induct, using `amusical_amusicalInv`.
   * So `periodic_of_evenFrequency_lt` applies to `ι n` and gives `Uᵖ (ι n) = ι n`.
   * Then `ι (U⁻ᵖ n) = ι n`, so `U⁻ᵖ n = n` by injectivity, so `Uᵖ n = n`, which contradicts `hn`.
5. **`evenFrequency_of_backwardNormal`.**
   * For `j ≥ s`, the indicator of `stepSym (ι (U⁻ʲ n)) = 0` is
     `∑_{b ∈ f⁻¹(0)} [block of n at j − s + 1 is b]`.
   * Each term has limiting frequency `3⁻ʷ`; shift the index by `s` and drop the first `s` terms,
     which only shift the count by a bounded amount.
   * The sum of `3^(w−1)` such terms has limit `3^(w−1) · 3⁻ʷ = 1/3`.
6. **`not_reversor_of_backwardNormal`.**
   * Combine 5 and 4 with `c = 1/3`.
   * `1/3 < 2 − log₂ 3` iff `log₂ 3 < 5/3` iff `3³ < 2⁵`.

Notes for the next lap go in `HANDOFF-amusical-escape.md`.
