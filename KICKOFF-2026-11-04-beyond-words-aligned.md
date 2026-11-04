# KICKOFF 2026-11-04 (second run on this branch): aligned windows, the probe at larger `j`, and the SEC6S plan

**This kickoff supersedes `KICKOFF-2026-11-04-beyond-words-stretch.md` (its gate is met, commit
7e42b47; its handoff `HANDOFF-2026-11-04-beyond-words-stretch.md` records the probe) and every
older handoff** for branch `wip/beyond-words-stretch`, worktree `~/src/collatz-moonshot-stretch`.
Operator: Ren (Claude), attended session 2026-11-04.  Lane: new mathematics (conjugacy ladder).

## The target

File: `CollatzMoonshot/Conjugacy/BeyondWordsAligned.lean` (planted, builds green with three
`sorry`s).  Host gate: `--done-when sorry-free:CollatzMoonshot/Conjugacy/BeyondWordsAligned.lean`.
The two theorems marked **Frozen** are frozen (never weaken, restate or re-hypothesise; a
`JUDGE-FLAG:` in the handoff if you believe one is false).  `beyondTVAt_zero` is a teeth test.
Build only what you touch (`lake build CollatzMoonshot.Conjugacy.BeyondWordsAligned`); add the
module to the root `CollatzMoonshot.lean` once sorry-free.

**Build discipline (binding):** ONE `lake build` at a time, foreground; the shared box memory
ceiling OOM-kills a container that runs several (exit 137).  Commit every green file at once.

## The proof

1. **Shift identity.**  For `r < 2^j`, `a = oddCount r j`, and any `q`:
   `tstep^[j] (r + q * 2^j) = tstep^[j] r + 3^a * q`.  From `tstep_iterate_identity`
   (`FrontB/Dictionary.lean`: `2^m · T^m n = 3^(ones (traceWord n m)) · n + numer (traceWord n m)`)
   applied to `n = r + q 2^j` and to `n = r`, with `traceWord_add_mul` (`FrontA/OrbitPacking.lean`:
   `traceWord (a + q * 2^m) m = traceWord a m`, so `ones` and `numer` agree), then cancel `2^j`.
   Also `oddCount (r + q 2^j) j = oddCount r j` (`oddCount = ones ∘ traceWord`), so the window's
   slice `{r + q 2^j : r ∈ levelSet j a}` is the image of `levelSet j a` under `· + q 2^j`.
2. **Window residue sums are shifted slice sums.**  `resInd K c (y + s) = resInd K ((c + 2^K − s % 2^K) % 2^K) y`
   (unfold `resInd`; `(y + s) % 2^K = c ↔ y % 2^K = (c − s) mod 2^K`), so
   `Σ_{c<2^K} ‖Σ_{r ∈ levelSet j a} resInd K c (T^j r + 3^a q)‖ = Σ_{c<2^K} ‖Σ_{r} resInd K c (T^j r)‖`
   (reindex the outer sum by the bijection `c ↦ (c + 3^a q) % 2^K` of `range (2^K)`,
   `Finset.sum_bij`/`Equiv.sum_comp` with `Equiv.addRight` on `ZMod (2^K)` or `Nat` arithmetic).
3. **`beyondTVAt_le_of_band`.**  Mirror `beyondTV_le_of_band` (`BeyondWordsLinearSharp.lean`) for
   the window: decompose `Finset.Ico (q 2^j) (q 2^j + 2^j)` as the image of `range (2^j)` under
   `· + q 2^j` (`Finset.image_add_right_Ico`-type lemma or `Finset.map`), split by slices via
   `oddCount`, use 1 and 2; same off-band term `2 · #{r < 2^j : ¬P (oddCount r j)} / 2^j`.
4. **The two frozen theorems.**  Copy the assemblies of `beyondWordsUniformLog`
   (`BeyondWordsLinear.lean`, via `exists_norm_levelSum_le_rate` and `beyondTV_le_of_slice`'s band)
   and `beyondWordsUniformLinear_of_sliceOscDecay_sharp` (`BeyondWordsLinearSharp.lean`), replacing
   the final TV step by 3.  If the sharp proof's intermediate facts are `private`, make the
   needed ones non-private as NEW declarations (never change existing statements) or restate them.
5. **Teeth** `beyondTVAt_zero`: `Finset.Ico 0 (0 + 2^j) = Finset.range (2^j)`; unfold both sides.

## After the gate (do before filing `box done` if the budget allows; both are deliverables)

(c') **Probe at larger `j`.**  `experiments/conjugacy/levelosc_table.js` reaches `j = 26` in about
a minute; write `experiments/conjugacy/levelosc_table.rs` (single-file Rust, `rustc -O`, threads
by `std::thread`; if no Rust toolchain is in the box, a C program with `gcc -O2` is fine) and
extend the exact table to `j = 30` (and `32` if it finishes in minutes): central slice
`a = j/2 ± 1`, all `m`, the ratio `levelOsc j a m / card`, plus the sparse-edge slice
`a = ⌊3j/5⌋`.  Memory: counts for `y < 3^a` with `a ≤ 16` fit (`3^16 · 8 B ≈ 350 MB`).  Report the
same two shapes as the handoff (fixed co-scale vs `j`; fixed `m` vs `j`) and whether the
`j = 26` extrapolations hold.  No claim beyond the data.

(d) **`SEC6S-PLAN.md`**: the campaign spec for the edge `SliceCharDecay → SliceOscDecay` (Tao §6
for the sliced law).  Read `~/src/tao-collatz-sec7p/SEC7P-PLAN.md` (the model: how a long
unattended campaign was specified) and `~/src/tao-collatz/TaoCollatz/Sec6/*.lean` (4693 lines:
`MixingCore` 2482, `MixingError` 1335, `MixingMain` 646, `MixingRegime` 140, `MixingFromDecay` 90;
`osc_sum_le` in `MixingCore`, `osc` in `Fourier/ZMod3.lean`), both mounted read-only.  The plan
must name: (i) the sliced objects (`levelMass j a` as a density on `ZMod (3^a)`, `levelOsc j a m`
vs `osc m a`), with a Lean statement that identifies `levelOsc` with `osc` applied to the slice
density; (ii) the two structural facts and their sliced statements (reducing a slice law mod
`3^k` is a mixture of sub-slice laws, by `tstep_iterate_identity` read mod `3^k` through
`numer`; oscillation is subadditive over mixtures, `osc_sum_le` verbatim); (iii) which `Sec6`
theorems port verbatim (generic in the density), which need the slice decay `sliceCharDecay` in
place of Prop 1.17, and which are Syracuse-specific; (iv) the lap plan with gates and a sorry
budget.  If time remains, prove (i) in Lean (`SliceOscBridge.lean`): `levelOsc j a m = osc m a
hma (sliceDensity j a)` or the inequality in the needed direction.

## Rules

- No `native_decide`, no new axioms, no `maxHeartbeats` bumps without a `-- HEARTBEAT:` comment.
- Never edit statements in other files; new lemmas go in the gate file or new files.  Do not
  touch `RESEARCH-*.md`, `DIRECTION.md`, `Maze.lean`; no `git add -A` (pathspec only).  Never
  vendor Lean from `tao-collatz` (read it; port by rewriting; cite the source file).
- Handoff: `HANDOFF-2026-11-04-beyond-words-aligned.md` with `#print axioms` of both frozen
  theorems (expect only `propext`, `Classical.choice`, `Quot.sound`).
- Lines ≤ 100 chars; docstrings on every new theorem.
