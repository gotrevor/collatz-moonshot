# KICKOFF 2026-11-04: the orbit word law, from Tao's stabilisation

**This kickoff supersedes `DIRECTION.md`, `RESEARCH-*.md` "next" lists and every older `HANDOFF-*.md`
for this branch** (`wip/orbit-word-law`, worktree `~/src/collatz-moonshot-orbitwords`, off
`ren/conjugacy-ladder`).  Operator: Ren (Claude), attended session 2026-11-04.  Lane: new mathematics.

## The target

File: `CollatzMoonshot/Conjugacy/OrbitWordLaw.lean` (planted, one `sorry`).

    theorem orbitWordLaw_of_le_four (C : ℕ) (hC : 1 ≤ C) (hC4 : C ≤ 4) : OrbitWordLaw C

`OrbitWordLaw` and `BadStart` are in `ChampernowneLog.lean`, frozen.  Never weaken, restate or
re-hypothesise.  Host gate: `--done-when sorry-free:CollatzMoonshot/Conjugacy/OrbitWordLaw.lean`.
**Keep every leaf `sorry` in this file**, or in `OrbitWordLaw*.lean` siblings imported by it and named
in your handoff: a gate counts one file, so a sorry moved elsewhere fools it.  The settling instrument
is `#print axioms orbitWordLaw_of_le_four`.  Build only what you touch
(`lake build CollatzMoonshot.Conjugacy.OrbitWordLaw`); `TaoCollatz` is prebuilt in `.lake/packages`;
never `lake update`.

## The proof

Read `RESEARCH-2026-10-21-conjugacy-ladder.md` §16 first; it is the argument, as repaired by a referee.
Then read in `.lake/packages/TaoCollatz/TaoCollatz/`: `Sec5/Stabilization.lean`
(`stabilization_atCX`, `alpha`, `c_stab`, `C_stab`, `X_stab`), `Sec5/FirstPassage.lean` (`passes`,
`passTime`, `passLoc`, `logUnifOdd`, `passTime_stepback`), `Sec3/Reduction.lean` (`passTime_anti`,
and how Tao covers `[1, X]` by windows), `Sec5/ApproxFormula.lean` (`approx_good_tuple_whp`,
`syr_iterate_good_bracket'`), and the Lean form of Tao's Proposition 1.9 and (5.4), the valuation tuple
against iid Geometric(2).  Grep for these; do not re-derive them.

Split into named lemmas, statement before proof, and commit after each green lemma:

1. **Bridge.**  `syr N` with valuation `a` is `tstep^[a] N` for odd `N`, with letters `1 0^(a−1)`.  The
   parity letters of `N` (`accWord`) are the concatenation of those blocks.
2. **Terras at one scale.**  Under `logUnifOdd (x^α) (x^α²)`, the first `A = ⌊0.19 log₂ x⌋` letters are
   within total variation `≪ 2^(−c log x)` of iid fair bits (from (5.4), or directly: residues mod
   `2^A` are nearly uniform under the log-uniform law, then Terras via `card_windowMatch`, which may be
   shorter).  State `GoodWindows M A H u δ`: every window of length `≥ H` inside the first `A` letters
   has the frequency of `u` within `δ`.  Large deviations for an `L`-dependent sequence: split positions
   into `L` residue classes, Hoeffding on each.  Conclude `P(¬ GoodWindows N A (η log x) u (δ/2))` is at
   most `log^(−10) x` for large `x`, for both `u` and the word `[true]` (at `δ₁ = 0.011`).
3. **The location event `G_x`.**  `M > 1`; `GoodWindows` over the next `4H'` letters of `M`, for `u` and
   `[true]`; and passage below `x^(1/α)` within them.  `H'` is the number of letters to descend from `x`
   to `x^(1/α)`, about `(1 − 1/α) log₂ x / β`.  `ν_x(G_x^c) ≪ log^(−10) x`, where
   `ν_x = (logUnifOdd (x^α) (x^α²)).map (passLoc ⌊x⌋)`.  The event for `N` at offsets up to the passage
   time, plus the bracket for the passage time, implies `G_x` for `M`.  The union over offsets
   absorbs the random time.
4. **Composition.**  `passLoc ⌊x'⌋ (passLoc ⌊x⌋ N) = passLoc ⌊x'⌋ N` for `1 ≤ x' ≤ x`, including the
   non-passing branch (`passLoc = 1` there).
5. **The chain.**  `x_(j+1) = x_j^(1/α)`.  By induction on `j`, using step 4, `PMF` data processing and
   `stabilization_atCX`: `dTV ((logUnifOdd (x₀^α) (x₀^α²)).map (passLoc ⌊x_j⌋)) ν_(x_j)` is at most
   `∑_{i≤j} C_stab (log x_i)^(−c_stab)`.  `J = ⌈ln 10 / ln α⌉` steps, bounded, so the sum is
   `≪ log^(−c) x_*` with `x_* = x₀^(1/10)`.
6. **All scales at once.**  For all but `≪ log^(−c) x_*` of `N`, `G_(x_j)` holds for `passLoc ⌊x_j⌋ N` at
   every `j ≤ J`, and by induction each is `> 1` and a true orbit point, at the sum of the passage times.
7. **Reading off the orbit.**  The stretches between passages tile the letters.  Step 2 applied to `N`
   itself covers the letters before `x₀`.  Summing: the frequency of `u` over the first `t` letters is
   right within `δ`, where `t` is the time at height `x_*`, with `η ≲ δ (α − 1)`, since stretches below
   the window length cost `∑ H_j`.  The `[true]` frequency within `0.011` gives
   `t ≥ 0.9 k / (β + 0.0175) ≥ 4 k`, with `k = log₂ N`, `β = 1 − log₂ 3 / 2`.  Height bookkeeping uses
   `height_identity` in `ChampernowneHeight.lean`, or Tao's bracket.  So `C ≤ 4` is covered.
8. **Density.**  Cover `[1, X]` by windows `[y, y^α]`, as in `Sec3/Reduction.lean`: exception
   `≪ log^(−c) y` on a window of log-weight `≍ log y`, Cesàro `o(log X)`.  Even starts `2^a m` prepend
   `a` zeros: exclude `a ≥ ε log₂ N` (log density `0`), and run the odd case at a slightly larger `C`,
   which the margin `4.34 > 4` allows.  `BadStart` uses `Nat.size n`.

The rough edges a referee named are already in §16: `M > 1`, the top prefix, the letter-`1` frequency,
and `η ≲ δ (α − 1)`.  If a step turns out false, write the concrete failure in your handoff and stop
that branch; do not weaken the target.

## Rules

- No `native_decide`, no new axioms, no `maxHeartbeats` bumps without a `-- HEARTBEAT:` comment.
- Never edit statements in other files.  Prefer new `OrbitWordLaw*.lean` files over adding to shared ones.
- Do not touch `RESEARCH-*.md`, `DIRECTION.md`, `Maze.lean`.  Never `git add -A` (pathspec only).
- Handoff: `HANDOFF-2026-11-04-orbit-word-law.md`, with `#print axioms orbitWordLaw_of_le_four` and what
  remains.
- Lines ≤ 100 chars; a docstring on every new theorem.  No first-claim language.
