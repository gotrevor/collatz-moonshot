# KICKOFF 2026-10-14: near-cycles (amusical, ncnull)

Repo `collatz-moonshot-amusical-nclin`: close every `sorry` in `CollatzMoonshot/AmusicalNearCycleLaw.lean`.

## Ratified, do not change

`NearCycleAt`, `LinearNearCycleLaw` (an open conjecture: do not try to prove it) and the five
theorem statements.  Everything else is read-only (you may remove `private` from helpers such as
`amusical_iterate_affine`).  Helpers go in `CollatzMoonshot/AmusicalNearCycleLaw/*.lean`.  No
`native_decide`, no new axioms, no `decide` over more than a few thousand cases.  Lean lines ≤ 100
characters.  Do **not** edit `RESEARCH-*.md`.  **Commit after every proved target.**

## Paper proofs (agent "ncnull", research §37)

1. `nearCycleStart_mono`: same `g`, `p + D ≤ p + D'` (the re-entry clause gets weaker... check: the
   clause `p + D < U^k p` for `k < g` becomes `p + D' < U^k p`, which is *stronger*).  ⚠️ So
   monotonicity is not immediate: with larger `D'`, an earlier `k` may already re-enter `(p, p + D']`.
   Take `g' :=` the least `k ≥ 1` with `U^k p ≤ p + D'` (exists: `k = g` works).  Then
   `U^{g'} p > p`: if `U^{g'} p ≤ p` then `g' < g` (as `U^g p > p`), so `U^{g'} p > p + D ≥ p`
   by `h`, contradiction.  `Nat.find`.
2. `nearCycleAt_equation`: `amusical_iterate_affine` (in `AmusicalGlobal.lean`, currently `private`;
   un-private it) gives `2^a U^g x = 3^g x + C`; the second conjunct is `ring`/`linarith`.
3. `finite_nearCycleAt`: from T1 and `|C| < 4^g`, `a ≤ 2g` (from the affine lemma's bounds), with
   `d = U^g p − p ∈ (0, D]` and `3^g ≠ 2^a` (parity): `p ≤ 2^a D + 4^g ≤ 4^g (D + 1)`.  So the set
   is contained in `Finset.range (4^g * (D + 1) + 1)`.
4. `card_fwdSurvivor_block_le` (NCU).  `N :=` the number of orbits (`hfin.toFinset.card`, as in
   `infinitelyManyOrbits_of_fwdSurvivors_three`).  Fiber the block's forward survivors by orbit
   (reuse `AmusicalSurvivorCeiling/Packing.lean`).  On one orbit, list them `n₁ < ⋯ < n_m`.
   For `i ≥ 2`: `pred(n_i) = n_{i−1}`, using P′ (`fwdSurvivor_le_iterate_inv`-style lemma: the
   first backward drop `V^g n_i` is `≥ n_{i−1}`, is a forward survivor, and is `< n_i`, so it
   equals `n_{i−1}` since no survivor of the orbit lies strictly between).  If `n_i − n_{i−1} ≤ D`,
   then `n_{i−1}` is a `D`-near-cycle start in `(Y, 2Y)` (intermediate points are `> n_i`; the
   first re-entry of `[0, n_{i−1} + D]` is at time `≤ g` and lands in `(n_{i−1}, n_{i−1} + D]`), and
   `i ↦ n_{i−1}` is injective.  Gaps `> D` sum to `< Y`, so fewer than `Y/D` of them.  Per orbit:
   `m ≤ 1 + Y/D + #(near-cycle starts of that orbit in the block)`; sum over orbits.
5. `infinitelyManyOrbits_of_linearNearCycleLaw`: from LIN, `∃ K, ∀ D ≥ 1, #NC_D ≤ K D` (finite
   for each `D`, and the ratio converges, so it is bounded).  By contradiction with NCU at
   `D = ⌈√Y⌉`: `#FS ≤ N(1 + 2√Y) + K(√Y + 1) ≤ (3N + 2K)√Y` for `Y ≥ 1`; take `C = 3N + 2K`
   (`Y = 0` gives an empty block).

Notes for the next lap go in `HANDOFF-amusical-nclin.md`.
