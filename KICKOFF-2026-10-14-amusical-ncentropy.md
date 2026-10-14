# KICKOFF 2026-10-14: stopped prefixes, run tightness at a log threshold (amusical, ncentropy)

Repo `collatz-moonshot-amusical-ncentropy`: close every `sorry` in
`CollatzMoonshot/AmusicalNearCycleEntropy.lean`.

## Ratified, do not change

`trueRuns`, `boolListsUpTo`, `stoppedPrefixes` and the five theorem statements.  Everything else is
read-only (you may remove `private` from helpers in `AmusicalNearCycleRuns*`).  Helpers go in
`CollatzMoonshot/AmusicalNearCycleEntropy/*.lean`.  `RhinBound` is not used here: do not assume it.
No `native_decide`, no new axioms, no `decide` over more than a few thousand cases.  Lean lines ≤ 100
characters.  Do **not** edit `RESEARCH-*.md`.  **Commit after every proved target.**  Work in order:
the three combinatorial targets are self-contained, P2′ reuses MR I's run machinery, RT-low last.

## Paper proofs (agent "ncentropy"; research §40; full report §2 in the agent's notes)

Setup: `p ∈ NC_D` has word `E^{a₁}O^{b₁}⋯E^{a_m}O^{b_m}`; every point `x_k`, `0 < k < g`, is
`> p + D`.  `E`: `x ↦ 3x/2`.  Odd: `x ↦ (3x ± 1)/4 = (3/4) x (1 + e/(3x))`, `e = +1` if `x ≡ 1`,
`−1` if `x ≡ 3 (mod 4)`.

1. **`nearCycleAt_prefix_balance` (P2′).**  `x_t / p = (3/2)^A (3/4)^B ∏_{odd i < t} (1 + e_i/(3x_i))`
   with `A = numE p t`, `B = t − A`.  The odd steps before `t` form `j = eRuns p t` complete runs (the
   orbit starts with `E`, `t − 1` is odd, `t` is even).  Each run ends at an interior point
   `X = x_k`, `0 < k ≤ t < g`, so `X ≥ p + D + 1`; MR I's run estimate (`NearCycleRuns.carry_bound`
   and its run lemma in `AmusicalNearCycleRuns/Bootstrap.lean`) bounds the run's log-sum by
   `< 1/(X − 1) ≤ 1/(p + D)`.  Since `x_t > p`, `0 < ln(x_t/p)`; rearrange.  Checked numerically
   (Ren, 678 interior minima at `D = 64`, 0 violations; tightening by 0.05 gives violations).
2. **`sum_stoppedPrefixes_le` (NB).**  A pattern with `τ` `E`'s and length `ℓ` has weight `2^{−ℓ}`,
   the fair-coin measure of its cylinder.  The cylinders are disjoint (cut at the stopping time
   "the `τ`-th `E`").  Under fair iid `E`/`O`, the first symbol is `E` w.p. `1/2`, and the first
   `τ` `E`'s lie in `≤ k` runs iff at most `k − 1` of the `τ − 1` coins "the symbol after the `i`-th
   `E` is `O`" fire.  So the full sum (no `M` cap) is `(1/2) P(Bin(τ−1, 1/2) ≤ k − 1)`, which is
   the right side; the `M` cap only drops terms.  A Lean route: induction on `τ` with a recursion on
   the run structure, or an injection into `Finset.range` of coin sequences.  Checked exactly
   (Ren, all `τ ≤ 7`, `M ≤ 5`, `k ≤ 6`, rationals).
3. **`card_stoppedPrefixes_le`.**  With `i + 1` `E`-runs (`i ≤ k − 1`) there are `i` `O`-runs between
   them.  `E`-run lengths: compositions of `τ` into `i + 1` parts, `C(τ − 1, i)`.  `O`-run lengths:
   compositions of some `B ≤ M` into `i` parts; `Σ_{B ≤ M} C(B − 1, i − 1) = C(M, i)` (hockey stick;
   `i = 0` forces `B = 0`).  Equality often holds (252 tight small cases).
4. **`sum_choose_le_exp_binEntropy`.**  `α = j/n ≤ 1/2`.  `1 = Σ_i C(n,i) α^i (1−α)^{n−i} ≥
   Σ_{i≤j} C(n,i) α^j (1−α)^{n−j}` since `α/(1−α) ≤ 1`, and `α^j (1−α)^{n−j} = exp(−n H(α))`.
   Edge cases `j = 0` (`α = 0`, both sides 1) and `n = 0`.  Search Mathlib first
   (`Real.binEntropy`, `Nat.choose` sum bounds).
5. **`ncard_deep_lowRun_le` (RT-low).**  Put `L = log₂ D`, `m = ⌊L/40⌋`, `τ = ⌈L/4⌉`,
   `β = ln(3/2)/ln(4/3) < 1.41`.  For `D` large (small `D` go into `C`: the set is bounded by
   `D L^14`):
   * Discard `p` with `3 eRuns p g ≥ 2p` (`O(L)` points).  Otherwise `nearCycleAt_numE_ge` gives
     `#E > (2 − θ) g − 1 > 0.2532 L − 1 ≥ τ`.
   * Let `u(p)` be the word up to the `τ`-th `E`.  It uses `≤ m` `E`-runs, and its odd steps end at an
     interior local minimum, so P2′ gives `#O(u) < β τ + 4`.
   * The starts following a fixed word `u` with `#E = τ`, `#O = B` form one residue class mod
     `2^{τ + 2B}` (bits consumed), so a block `[Y, 2Y)` holds `≤ Y/2^{τ+2B} + 1` of them.  Summing over
     words, each pattern carries `2^B` words, so the main term is `Y ·` (pattern mass) `≤ Y·`NB.
   * Total over dyadic blocks below `Y₀ = D L^14`:
     `≤ 2 Y₀ · 2^{−(τ−1)(1 − H₂(0.1)) + o(L)} + L · 2^{βτ + 4} · #patterns`.  Exponents (powers of
     `D`): `1 − (1/4)(1 − H₂(0.1)) = 0.8672` and `0.5998`; both `< 0.87` after the polylog factors.
   Ren checked every step and every exponent (python).  Bookkeeping is the bulk: prefer coarse
   explicit constants (any `C` works).

Notes for the next lap go in `HANDOFF-amusical-ncentropy.md`.
