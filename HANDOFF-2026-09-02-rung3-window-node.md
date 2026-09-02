# Handoff: rung 3 — crux decomposed, non-window branch PROVED, strong separation landed

**Date**: 2026-09-02 (evening) · **Branch**: `main` · nothing pushed — host pushes.

## 🎯 Objective (unchanged, `DIRECTION.md`)
Rung 3 of the odd-block ladder: `FrontA.threeBlock_gap_of_long`, hence "every acyclic paradoxical
segment whose word has three odd blocks has length 8".

## What this lap did
1. **Eliminated the cascade from the crux.**  `threeBlock_ceiling_gap`'s hypotheses never mention
   `w₁,w₂,w₃`, so the residual census is a statement about the exponent tuple alone:
   `threeBlock_leaves_infeasible`.
2. **Proved the non-window third.**  `threeBlock_nonwindow`: if `2·3^k ≤ 2^m` the tuple has
   `m ≤ 22`.  Chain: scale-free `_S1/_S2/_S3` → `_F1` (`3^d ≤ 2^(e+2)`) → `_F2` (`f ≤ 2`) →
   `_F3` (`b+g ≤ 4`) → `m ≤ e+13` → `_e_bound` / `2^m < 4·3^k`.
3. **Landed a strictly stronger separation theorem** (`FrontA/RhinLiteSep.lean`):
   `sep_strong_of_bracket_nat`, instantiated as `sep_strong_190537`:

       3^k ≤ (2^m − 3^k)·2^20     for every 0 < k < 190537 with 3^k < 2^m.

   The unimodular brackets already in the repo bound the gap by `2/2^j` with `2^j ≥ 2·max(b',d')`
   — a constant in `k`.  `sep_of_bracket_nat` discarded that because `sep_two_three` is stated at
   `β = 1/3` (its `3j ≤ k` hypothesis, which the strong form does not need).
   `threeBlock_window_scale` turns it into `2^m ≤ 2^21·D` in the near-critical window.
4. **Recorded the effectivity answer**: rung 3's residual needs a *stronger* separation input than
   rung 2.  At `β = 1/3` the normalized system has the fixed point `b/k = d/k = f/k = 1/3` and is
   feasible; the closing inequality is `k ≤ 5.1·log₂(1/(1−R)) + 6`.  The strong bracket gives
   `log₂(1/(1−R)) ≤ 21` and hence a genuinely finite, computable `k`-range.

## State
- `lake build` green (per-target; see the gotcha below).  Two disclosed sorries, both in
  `ThreeBlock.lean`: `threeBlock_finite_infeasible` (finite `m ≤ 27` check) and
  `threeBlock_window_infeasible` (THE crux).  Everything else in the rung-3 chain is sorry-free.
- No Front-A headline is affected; no Aristotle job in flight.

## Next actions
See the top section of `PENDING_WORK.md` — parameterize the `_S*/_F*` chain by the scale
`2^m ≤ 2^t·D` (`t=1` non-window, `t=21` window) with SHARP constants (`3^5 ≤ 2^8`, not `3 ≤ 4`),
then build one decision procedure for the finite census shared by both leftover nodes.

## ⚠️ Box gotcha hit this lap
A wide `lake build` failed repeatedly with `resource exhausted (error code 24, too many open
files)` — the known cold-build fd exhaustion
(`~/personal/claude/knowledge/core/projects/lean-journey/reference/lean-box-fd-exhaustion-is-mmap-not-nofile.md`).
Raising `ulimit -n` does nothing.  What worked: build ONE target at a time,
`taskset -c 0-3 lake build CollatzMoonshot.FrontA.ThreeBlock`.  Also: never run two `lake build`s
concurrently, and `lake build` has no `-j` flag.
