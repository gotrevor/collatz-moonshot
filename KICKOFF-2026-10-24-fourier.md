# Kickoff 2026-10-24: prove the five `sorry`s in `CollatzMoonshot/Conjugacy/Fourier.lean`

Branch `wip/conjugacy-fourier` (worktree `~/src/collatz-moonshot-fourier`), from `ren/conjugacy-ladder` at `daad7a1`.  Context: research note §12 and §10.6; the module docstrings carry the English proofs.

## Objective

Make `CollatzMoonshot/Conjugacy/Fourier.lean` sorry-free.  Five declarations, in suggested order:

1. `lowFreqDecay_of_twoAdicFreqDecay` - easy.  For odd `ξ : ℕ`, `(ξ : ℤ_[2])` is a unit; `PadicInt.appr (ξ : ℤ_[2]) (j+1) = ξ % 2^(j+1)` (look for `PadicInt.appr` lemmas, `PadicInt.zmodRepr`, `PadicInt.toZModPow`); prove a periodicity lemma `fourierCoeff j (ξ + 2^(j+1) * k) = fourierCoeff j ξ` (the exponential is `2πi`-periodic) and `fourierCoeff j (ξ % 2^(j+1)) = fourierCoeff j ξ`.
2. `fourierCoeff_succ` - the parity split.  `beyondSign (j+1) (2s) = beyondSign j s` and `beyondSign (j+1) (2s+1) = beyondSign j (3s+2)` from the definition of `tstep` (Ladder.lean / FrontB); `beyondSign j` depends only on `r % 2^(j+1)` (use `accWord_congr_mod` or the shift identity `tstep_iterate_add_mul_two_pow` in Ladder.lean); reindex the odd half by the bijection `s ↦ (3s+2) % 2^(j+1)` on `range (2^(j+1))`, using `hu : 3 * u % 2^(j+1) = 1`.
3. `sum_norm_sq_fourierCoeff` - Parseval on `ZMod (2^(j+1))`: orthogonality `Σ_{ξ<n} e(ξ(r−r')/n) = n·[r = r']` for `r, r' < n` (geometric sum of roots of unity; Mathlib has `IsPrimitiveRoot.geom_sum_eq_zero` and the `ZMod.dft` / `AddChar` orthogonality API - either route is fine) and `beyondSign j r ^ 2 = 1`.
4. `bias_div_le_lowFreq_add_tail` - the main one.  Proof in its docstring: window formula `bias j = n Σ_ξ G_j(ξ) · conj H(ξ)` (Fourier inversion of `beyondSign j` against the indicator of `[0, 2^j)`), `|H(ξ)| = n⁻¹/|sin(πξ/n)|` at odd `ξ`, `G_j` = 0 at even `ξ` (antiperiodicity `beyondSign j (r + 2^j) = − beyondSign j r`, from the shift identity), Jordan `Real.mul_le_sin` / `Real.two_div_pi_mul_le_sin`, Cauchy–Schwarz (`inner_mul_le_norm_mul_norm` or `Finset.sum_mul_sq_le_sq_mul_sq`), Parseval (item 3), `Σ_{m>K} 1/m² ≤ 1/K`.  Splitting into named helper lemmas is encouraged and counts as progress.
5. `biasDecays_of_lowFreqDecay` - from item 4 by an ε/2 argument over the finite set of odd `ξ ≤ K`.

## Rules

- **Do not change any frozen statement** (the five above, `LowFreqDecay`, `TwoAdicFreqDecay`, `fourierCoeff`, `beyondSign`).  If one is false as stated, stop and write the counterexample into the handoff; do not weaken it silently.  The numerics in the docstrings say all five are true.
- New helper lemmas go in `Fourier.lean` (or a new `Conjugacy/FourierAux.lean` imported by it).  Leave every other module alone.
- Commit each green checkpoint on `wip/conjugacy-fourier` with `git-safe`; update the handoff `HANDOFF-2026-10-24-fourier.md` (create it) with what is proved and what remains.
- Report the mathematics, not the certificate.
