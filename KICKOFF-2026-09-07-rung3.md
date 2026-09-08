## OPERATOR ADDENDUM 2026-09-07 20:31 — LAND THE WORK, then continue ⚠️

*This section outranks the body below where they conflict.  The body's
mathematics is unchanged; this is about getting it recorded.*

**Observed**: laps 1-3 of run `...-192938` each ended with **+0 commits** while
`CollatzMoonshot/FrontA/ThreeBlock.lean` carried **+155 uncommitted lines** whose
targeted build the lap itself reported green.  Adaptive has already escalated to
the `xhigh` ceiling.  An uncommitted artifact is **invisible to the next fresh
lap** — every lap that inherits it re-derives it or, worse, re-decides it.

1. 🔨 **Commit the ThreeBlock work before extending the algebra.**  A targeted
   green build on the module you touched **is** a coherent checkpoint under
   `codex-treadmill/AGENTS.md`.  Run the repository gate too; if the gate cannot
   run, or is red for reasons unrelated to your edit, commit anyway and **name
   the evidence tier in the commit message** (`targeted build green; full gate
   not run`).  Do not hold a green module hostage to a repo-wide check.
2. ✍️ **Every lap ends with a commit, or with an explicit written reason there
   is nothing to commit.**  "Still iterating" is not a reason after 15 minutes.

### Where the mathematics stands (carry this forward)

The live attack, from lap 2's own report, is the reduction of the window algebra
to **four aggregate exponent inequalities**, with the sharp constant pair

    2^19 ≤ 3^12   (lower log bound)      3^5 ≤ 2^8   (upper log bound)

which makes the feedback contract where the crude `3 ≤ 4` route does not.  Next:
formalize the aggregates, derive an absolute window range at scale `t = 21`, then
discharge with **one** pruned finite certificate covering both leftover nodes
(`threeBlock_finite_infeasible` and `threeBlock_window_infeasible`) — not two.

Keep `P` sharp in (A)/(B)/(C); `PENDING_WORK.md` records that the crude
`P < 1 + r2` elimination was **attempted and refuted**, so do not re-run it.

---

# KICKOFF 2026-09-07 — rung 3 of the odd-block ladder, the window node ⛓️

**Engine**: Codex, model `gpt-5.6-sol`, effort `high`.  **Branch**: `main`.
**Read `PENDING_WORK.md` BEFORE `DIRECTION.md`** — see the staleness note below.

## The objective (unchanged from the 2026-09-02 altitude lap)

Prove `FrontA.threeBlock_gap_of_long` (`FrontA/ThreeBlock.lean`), hence
`threeBlock_not_acyclicParadoxical_of_long`, hence the rung-3 classification:
**every acyclic paradoxical segment whose word has three odd blocks has
length 8.**  Rungs 1 and 2 are exclusions; rung 3 is the first rung whose answer
is a *classification*, and the whole engine is already sorry-free.

## ⚠️ DIRECTION.md is one lap stale — reconcile against git, not against prose

`DIRECTION.md` describes the open part as "a finite explicit census — 27 tuples
at four lengths".  Commits `5c8b48f … e644d3b` have moved past that.  The live
state is `PENDING_WORK.md` §"RUNG 3 — state after the lap of 2026-09-02
(evening)": the cascade scales `w₁,w₂,w₃` are **eliminated**, and the crux is
three named nodes —

| node | status |
|---|---|
| non-window `2·3^k ≤ 2^m` | **PROVED** (`threeBlock_nonwindow`, `m ≤ 22`) |
| `threeBlock_finite_infeasible` (`m ≤ 27`) | disclosed — finite `decide`, ~2·10⁵ tuples |
| `threeBlock_window_infeasible` (`m ≥ 28`, `3^k < 2^m < 2·3^k`) | disclosed — **THE crux** |

Trust the table and the commits over the DIRECTIVE's prose.  Do not restart the
Rozier–Terracol discharge (complete at `55a119b`) and do not re-attempt the
cross-repo Rhin-lite extraction (refuted; `DIRECTION.md` explains why, and the
refutation still stands).

## Attack order

1. **Re-run the `_S*/_F*` chain with the scale hypothesis `2^m ≤ 2^t·D` as a
   parameter `t`** (non-window `t = 1`, window `t = 21`).  Sharp constants
   matter: use `3^5 ≤ 2^8`, not `3 ≤ 4` — the crude `3^x ≤ 4^x` route lands at
   `m ≤ 78t + 43`, the sharp one near `m ≤ 20t`.
2. **One decision procedure over the exponent tuple, covering both leftover
   nodes.**  Do not brute-force `m ≤ 27` and `m ≤ O(t)` separately.
3. If the elementary route stalls, both regimes funnel into
   `D·2^f ≲ 3^k·2^b` — a linear form in **two** logs, so `sep_two_three`
   (axiom-free in this repo) is the available Baker input.  **Record which
   regime actually needs it**: that answer *is* the effectivity-asymmetry
   finding against Front B, and it is a publishable result even if rung 3
   itself does not close.
4. Known gap, do not paper over it: `k ≥ 190537` is not covered by the strong
   bracket (`sep_strong_190537`), and the polynomial measure only closes
   `k ≳ 2.4·10⁵`.  The interval `[190537, 2.4·10⁵]` needs one more convergent
   pair of `log₂3` with `decide +kernel` power certificates, next after
   `478245/301739`.

## Lap discipline

A lap succeeds by **advancing the crux**, not by lowering a `sorry` count —
decomposing one fat `sorry` into named leaves raises the count and is progress.
A refutation of a node is equally an advance; report it, do not patch around it.
Prefer `decide +kernel` over `native_decide` (the latter plants a bespoke
axiom).  No outward actions; `~/src/normal-numbers` is read-only from here.

## Launch (Trevor fires)

    lean-treadmill start collatz-moonshot --engine codex --model gpt-5.6-sol --effort high \
      --max-duration 8h --adaptive --effort-ceiling xhigh \
      --review-every 3 --reflect-every 9 \
      --prompt "Execute KICKOFF-2026-09-07-rung3.md: close the rung-3 window node. Read PENDING_WORK.md before DIRECTION.md; DIRECTION is one lap stale." \
      --allow-from-agent
