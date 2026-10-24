# Kickoff 2026-10-24: prove the five `sorry`s in `FourierSup.lean` and `FourierLattice.lean`

Branch `wip/conjugacy-lattice` (worktree `~/src/collatz-moonshot-fourier`), from `ren/conjugacy-ladder` at `0f31e9a`.  Context: research note §12 (the lattice paragraph); the module docstrings carry the English proofs.  `Conjugacy/Fourier.lean` is fully proved and is your toolbox (`fourierCoeff_succ`, `fourierCoeff_add_period`, `padicInt_appr_natCast`, `beyondSign_congr_mod`, and their private helpers).

## Objective, in this order

1. `CollatzMoonshot/Conjugacy/FourierSup.lean` - three easy edges.
   - `supFreqDecay_of_sqrtBound`: `C / √j → 0`, so eventually `≤ ε`.
   - `lowFreqDecay_of_fixedFreqExpDecay`: `C · 2^{−(1/2+δ) j} → 0`.
   - `twoAdicFreqDecay_of_supFreqDecay`: for a unit `η : ℤ_[2]`, `PadicInt.appr η (j+1)` is odd (its residue mod 2 is the unit's; `PadicInt.appr_spec`, `PadicInt.isUnit_iff`, `PadicInt.norm_lt_one_iff_dvd` or the `toZMod` route), so the uniform bound applies at every level; conclude with `tendsto_order` / `Metric.tendsto_atTop`.
2. `CollatzMoonshot/Conjugacy/FourierLattice.lean` - the lattice formula.
   - `fourierCoeff_eq_latticeCoeff` by induction on `n` (generalising `m`).  Base: `G_0 = 1` at every odd frequency (compute the two-term sum; `ξ · 3^{−m}` is odd because `3⁻¹` and `ξ` are units mod `2`).  Step: `fourierCoeff_succ` with `u = ((3 : ZMod (2^(n+2)))⁻¹).val` (so `3u % 2^(n+1) = 1`), then three congruences: `u · (ξ3^{−m}) ≡ ξ3^{−(m+1)} (mod 2^(n+1))` (rewrite the frequency with periodicity), `ξ3^{−m} (1 − 4u) ≡ −ξ3^{−(m+1)} (mod 2^(n+2))` (because `3(1 − 4u) ≡ −1`), and `1`-periodicity of `Complex.exp (2πi ·)`.  Reductions between `ZMod (2^(n+2))` and `ZMod (2^(n+1))` go through `ZMod.castHom` (`2^(n+1) ∣ 2^(n+2)`) and `ZMod.val_cast_of_lt` / `ZMod.natCast_mod`.
   - `fourierCoeff_eq_latticeCoeff_zero`: `m = 0`, and `(ξ : ZMod _).val = ξ % 2^(j+1)`, then periodicity.

## Rules

- **Do not change any frozen statement**: the five theorems above, `SupFreqDecay`, `SupFreqSqrtBound`, `FixedFreqExpDecay`, `latticePhase`, `latticeCoeff`.  If one is false as stated, stop and write the counterexample into the handoff; do not weaken it silently.  The lattice formula is checked numerically to `2.6e-16` (`experiments/conjugacy/latticedp.py`, same conventions).
- New helper lemmas go in the module that uses them (or a new `Conjugacy/FourierLatticeAux.lean`).  Leave every other module alone, `Fourier.lean` included.
- Commit each green checkpoint on `wip/conjugacy-lattice` with `git-safe`; keep `HANDOFF-2026-10-24-lattice.md` (create it) current with what is proved and what remains.
- Report the mathematics, not the certificate.
