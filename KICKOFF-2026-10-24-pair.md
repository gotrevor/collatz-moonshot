# Kickoff 2026-10-24: prove the three `sorry`s in `CollatzMoonshot/Conjugacy/FourierPair.lean`

Branch `wip/conjugacy-pair` (worktree `~/src/collatz-moonshot-fourier`), from `ren/conjugacy-ladder` at `93109b7`.  Context: research note §12 ("Tao's pairing transfers pointwise"); the docstrings carry the English proofs.  `FourierLattice.lean` (proved) is the toolbox: `latticeCoeff`, `latticePhase`, `fourierCoeff_eq_latticeCoeff_zero`.

## Objective, in this order

1. `pairTheta_far` - elementary.  With `q = 3^t`, `X = ((3 : ZMod (2^k))⁻¹ ^ t * ξ).val`, show `q * X = ξ + 2^k * M` for an integer `M` (cast `q * X ≡ ξ` in `ZMod (2^k)` to `ℤ`; `ZMod.intCast_zmod_eq_zero_iff_dvd` or `ZMod.intCast_eq_intCast_iff_dvd_sub`).  Then `pairTheta = M/q + ξ/(q 2^k)`.  `q ∤ M`: else `q ∣ ξ` (because `gcd(q, 2^k) = 1`).  So `|M/q − z'| ≥ 1/q` for every integer `z'`, and `0 ≤ ξ/(q2^k) < 1/q`; conclude.
2. `norm_latticeCoeff_le_pairBound` - induction on `i` generalising `m`.  Unfold `latticeCoeff` twice (`2 * (i+1) = 2*i + 1 + 1`); collect `V_{2i}(m+1)` with coefficient `¼(latticePhase ξ (2i) m + latticePhase ξ (2i+1) m)`.  Key identity: the two phase arguments are `−⟨x⟩_{2i+2}` and `−⟨x⟩_{2i+3}` for `x = ξ·3^{−(m+1)}`, and `⟨x⟩_{2i+2} = 2⟨x⟩_{2i+3} − (0 or 1)` (the top bit; reduce `ZMod (2^(2i+3)) → ZMod (2^(2i+2))` with `ZMod.castHom`, inverse of 3 commutes with the cast).  Then `‖exp(−2πi·2a) + exp(−2πi·a)‖ = ‖1 + exp(−2πi·a)‖ = 2|cos πa|` (`Complex.abs_exp`, `Complex.norm_exp_ofReal_mul_I`, `Complex.cos`, half-angle).  Note `pairCos ξ (2i+3) (m+1)` uses `pairTheta ξ (2i+3) (m+1) = ⟨ξ 3^{−(m+1)}⟩_{2i+3}`, which matches `latticePhase ξ (2i+1) m`'s exponent.  Outer coefficients: `‖¼ V‖` and `‖¼ φφ' V‖` with `‖φ‖ = 1`.
3. `lowFreqDecay_of_pairBoundDecay` - even `j` directly; odd `j = 2i+1`: one unfolding gives `‖G_{2i+1}(ξ)‖ ≤ ½ U_i(0) + ½ U_i(1)`; `squeeze_zero`.

## Rules

- **Do not change any frozen statement**: the three theorems, `PairBoundDecay`, `pairTheta`, `pairCos`, `pairBound`.  If one is false as stated, stop and write the counterexample into the handoff; do not weaken it silently.  `pairbound.py` and `protect.py` check them numerically with the same conventions.
- Leave `PairBoundDecay` unproved (it is the open node).  Helpers go in `FourierPair.lean` or a new `Conjugacy/FourierPairAux.lean`.  Leave every other module alone.
- Commit each green checkpoint on `wip/conjugacy-pair` with `git-safe`; keep `HANDOFF-2026-10-24-pair.md` current.
- Report the mathematics, not the certificate.
