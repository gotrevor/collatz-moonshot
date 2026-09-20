# Probe 2026-09-20: the carry-budget handle is residues in costume ❌

**Question.**  Does surviving a long ballot prefix (`T^j(n) ≥ n` for `j ≤ k`, shortcut map)
change the binary digit structure of the iterates beyond the low bits that literally encode the
coming parities?  If it did, "carry budget" (`s₂(n_k) − s₂(n₀) = Σ_{odd steps}(s₂(nᵢ)+1−Cᵢ)`,
Kummer) would be a handle distinct from the residue-class description (Terras).

**Instrument.**  `experiments/carry_budget.py`: 2¹⁷ random odd starts in `[2⁴⁰, 2⁴¹)`, seed
20260920, `k = 40`; survivors (1512, 1.15%) vs the rest; per-bit-position 1-density and
carry-out probability of `n + 2n + 1` at steps 0, 20, 40.  The Kummer carry identity is asserted
against a bitwise addition on every odd iterate.

**Result.**  At step 0 survivors have 1-density `1.00 1.00 .83 .84 .67 .67 .60 .58` at bit
positions 0–7 and `0.50 ± 0.02` from position 8 upward (mid-bit density 0.504 vs control 0.501).
At step 20 the same profile, halved in amplitude.  At step 40, where the future is unconstrained,
survivors are at `0.50` on every position and every aggregate (`s₂/L` 0.510 vs 0.510, carries/L
0.550 vs 0.561).  The earlier hand-picked-orbit reading (`s₂/L ≈ 0.57–0.62` along 27, 703, …)
was this low-bit effect averaged over iterates whose bit length is small.

**Verdict.**  The digit-sum and carry statistics of survivors carry no information beyond the
residue class `n mod 2^k` that Terras already gives.  Carries flow low→high, so the archimedean
head never feeds back into the word, exactly as the one-way-joint picture says.  The
carry-budget identity is true and empty as a handle: it is bounded by the same low bits.  Retire
it.  What survives of the riff is the *negative* structural statement: any contradiction must be
global (counting / ergodic / integrality over a whole prefix), never a local digit statistic.

Cross-ref: `FRONT-A-ROUTES.md` filters 1–3, `DIRECTION.md` run-count gap node,
`collatz-cryptid` `Carry.lean` (same carry mechanism, base 3, for `2ⁿ`).
