# Handoff: rung 3 of the odd-block ladder opened — engine sorry-free, crux = a 27-tuple census

**Date**: 2026-09-02 · **Branch**: `main` · **HEAD**: (this commit) · nothing pushed — host pushes

## 🎯 What we're doing
`DIRECTION.md` was retargeted by this **altitude lap**.  The previous objective (discharge
`Assumed.rozier_terracol_3_2`) is complete and must not be restarted.  The new objective is the
**odd-block ladder, rung 3**:

> every acyclic paradoxical segment whose word has three odd blocks has length `8`.

Rung 1 = Rozier–Terracol App. A, rung 2 = `le_two_blocks_not_acyclicParadoxical` (both exclusions,
both closed).  Rung 3 is the first rung whose answer is a **classification** — four words realize
it, all of length 8 — and it is the Front-A analogue of Front B's `m`-cycle ladder.

## 🧠 Context to carry forward
- **Ranking of the operator's three candidates** (recorded in `DIRECTION.md`): (a) rung 3 chosen —
  on-path, genuinely open, and already reduced to a finite census; (b) Rhin-lite tower extraction
  deferred (packaging, and `~/src/normal-numbers` is another session's, read-only here);
  (c) KS entropy deferred (multi-lap mathlib infrastructure, off the paradoxical path).
- **The lap's mathematics.**  Write the word `[T]^b[F]^c[T]^d[F]^e[T]^f[F]^g`,
  `m = b+c+d+e+f+g`, `k = b+d+f`, `D = 2^m − 3^k`, `T = 2^(c+d+e) − 2^(c+d) + 3^d(2^c−1)`,
  itinerary `n → X → Z → y`.
  · **Block-merge reduction** — rung 2 as a *black box* on both two-block sub-segments.  This
    needed rung-1/rung-2 tools in **identity form** (`headBlock_le_of_identity`,
    `two_block_residue_core` already was), because interior sub-segments carry no `traceWord`
    equation.  Cuts the length-≤24 space 126824 → 34832, 0 violations.
  · **Exact criterion** — `n < y ⟺ D·w₁ ≤ 3^f·T − 2^(c+d+e+f)` where `n + 1 = 2^b w₁`.
    ⚠️ The sharp form uses `y ≥ n+1`, **not** `y > n` scaled by `2^m`; the lazy version is weaker
    by a whole `2^(m−b)` and turns a finite relaxation into an infinite one.  I made exactly that
    slip mid-lap and caught it by re-deriving `core_of_gap`'s `hUP` — worth re-checking any future
    rung the same way.
  · **Integer cascade** — `3^b w₁ + 2^c = 2^(c+d) w₂ + 1`, `3^d w₂ + 2^e = 2^(e+f) w₃ + 1`,
    `3^f w₃ = 2^g y + 1`, all in ℕ, `w₃ ≥ 1`.  Eliminating `w₂`: `3^(b+d) w₁ = 2^(c+d+e+f) w₃ − T`.
- **THE FINDING.**  Dropping the integrality of the *interior* scale `w₂` (i.e. using only
  `w₃ ≥ 1`, the division-free relaxation `D·(2^(c+d+e+f) − T) ≤ 3^(b+d)·2^(c+d+e)·(3^f − 2^f)`)
  leaves an **infinite** set: 18 / 258 / 2489 / 18324 tuples at `m = 8 / 16 / 27 / 46`.  Keeping
  `w₂ ∈ ℕ` collapses the rung to **27 tuples at `m ∈ {5, 8, 16, 27}`**, exhaustive for all
  `m ≤ 130` and every `k` with `3^k/2^m > 1/8`.  The 10 tuples off `m = 8` die on the true
  realizing residue by factors 10²–10³.  So rung 3's finiteness is carried by a **two-level integer
  ceiling**, not by a linear form in logarithms — the effectivity asymmetry the operator asked
  about, against both rung 2 (needs Baker via `sep_two_three`) and Front B's `m`-cycle ladder.

## ✅ State (all observed this session)
- `lake build` → `Build completed successfully (8766 jobs)`.
- `scripts/check-proof-debt.sh` → `1 disclosed sorries`, `ThreeBlock.lean:410` only (gate's
  allowlist extended to `ThreeBlock.lean` with the reason written in the script).
- `lake env lean scripts/AxiomAudit.lean | grep -c sorryAx` → `0` (no audited headline touched).
- `#print axioms`: `threeBlock_slack`, `threeBlock_criterion`, `threeBlock_cascade`,
  `threeBlock_of_gap`, `threeBlock_segment_identities` = `[propext, Classical.choice, Quot.sound]`;
  `threeBlock_merge_reduction` / `threeBlock_criticality_of_acyclicParadoxical` add exactly the
  two-block exclusion's existing `native_decide` certificates (they consume rung 2);
  `threeBlock_not_acyclicParadoxical_of_long` carries the one disclosed `sorryAx`.
- No Aristotle job in flight.

## 🎬 Next actions
1. **Prove `threeBlock_gap_of_long`.**  Two-regime split (details in `PENDING_WORK.md`):
   Regime II `3^d > 2^(e+f)` forces `w₂ = 1`; Regime I `3^d ≤ 2^(e+f)` makes the `w₂`-ceiling a
   bounded correction.  Both funnel into `D·2^f ≲ 3^k·2^b` — a **two-log** linear form, so
   `sep_two_three` is the fallback.  **Record which regime actually consumes it**: that datum is
   the asymmetry result.
2. Then the finite tail: 10 tuples at `m ∈ {5,16,27}` by explicit realizing residue (`decide`),
   17 at `m = 8` are the exception.
3. Re-run `python3 experiments/rung3_census.py census 130` / `relax 46` / `verify` before
   trusting any number quoted above.

## ⚠️ Gotchas (Lean v4.33.1, mathlib as pinned)
- `rw [← hwz]` on a goal like `0 ≤ ↑y - 2^b * ↑w₁` fails to spot `2^b * ↑w₁`; use
  `linarith [hwz, hy]` and let `linarith` treat the product as an atom.
- `linear_combination -hM` (note the sign) is what proves `threeBlock_slack`; `ring_nf`-then-
  `linarith` gymnastics on the same goal is fragile and unnecessary.
- `List.append_inj hW hlen` is the splitting workhorse; normalise the replicate word with
  `simp only [List.append_assoc]` first, and prove the length side condition by plain `simp`.
- `Function.iterate_add_apply` then `congr 1; ring` moves `tstep^[d+e] (tstep^[b+c] n)` to
  `tstep^[b+c+d+e] n`.
- `push_neg` is deprecated → `push Not` (warnings only).
- Never `cd` inside a Bash call before `lake env lean` (toolchain resolves from cwd).

## 📁 Key files
- `CollatzMoonshot/FrontA/ThreeBlock.lean` — the rung-3 engine; module docstring is the map.
- `experiments/rung3_census.py` — the census instrument (`census` / `relax` / `verify`).
- `experiments/block_ladder_probe.py` — the earlier word-based rung-3 probe.
- `CollatzMoonshot/FrontA/Paradoxical.lean` — rungs 1 and 2, `two_block_residue_core`.
- `DIRECTION.md` — retargeted CURRENT DIRECTIVE + ranking of the three candidates.
- `PENDING_WORK.md` — top section = this lap's record and the next attack.

---
**→ Next session: start at "Next actions" #1.  Do not restart the `rozier_terracol_3_2` work, do
not restate rung 3 as an exclusion (`acyclicParadoxical_seven_eight` refutes that in kernel), and
do not move `threeBlock_gap_of_long` out of `src/` — it is the active crux.**
