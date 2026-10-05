# KICKOFF 2026-10-05: `Maze.lean`, the closed routes as Lean data

**Lane:** bookkeeping in Lean, no new mathematics.  **Engine:** Opus/low treadmill, at most three laps.  **Do not launch without Trevor's go.**

## Why

The repo's closed routes (the 2026-09-27..29 certificate-repair toolkit, the 2026-09-13 relaxation ladder, the 2026-09-19 retirements, the 2026-09-22 Round A) exist only as prose in `DIRECTION.md` / `RESEARCH-*.md`, while their obstructions are real theorems under `CollatzMoonshot/Obstructions/` and `FrontA/`.  Standing rule (`../lean-agent-skills/context/LEAN-NEW-MATH.md`): a closed route is a `Maze.lean` row whose verdict cites declarations, checked by `#maze_audit`.

## Template

`~/src/normal-numbers/src/NormalNumbers/Maze.lean` + `MazeAudit.lean`.  Tool: `LeanLedger.MazeLinks` from `gotrevor/lean-agent-skills` (`subDir = "lean"`, pin a SHA).  Before any build: `lake-base status` + `relake plan` (never a cold `lake exe cache get`).

## Deliverables

1. `require LeanLedger` in `lakefile.toml` at a pinned SHA.
2. `CollatzMoonshot/Maze.lean`:
   - A `Verdict` enum carrying the three gates as constructors, each with its tell: **2-adic adversary** (bounded reading of the orbit leaves an infinite residue class), **sibling transfer** (the method also holds for 3x−1 at 5 or 5x+1 at 13), **density ≠ all**, plus `costume` (equivalent to a front) and `refuted`.
   - One row per closed route.  Each row cites its obstruction declaration (e.g. `BoundedMerger`, `CoefficientRay`, `Q1Coalescence`, `RayRefill`, the `P_6` prefix-admission family, `at_primitive`), and each wall cites a reopen `def … : Prop`.
3. **Make the sibling control a theorem, not a sentence.**  `CollatzMoonshot/Sibling.lean` defines the generic `T_{q,c}` and proves, by `decide`, the 3x−1 cycle `5 → 7 → 10 → 5` and the certificate `5 = 2^4 · s₁₁ s₂₅ s₃₇` from `RESEARCH-2026-09-29-map-controls.md`.  The map-control row cites them.
4. Rows whose reason is still only prose go in `mazeLegacy`; that list only shrinks.
5. Peer barriers enter as cited `Literature.*` Props, faithful-or-weaker: Nashida Part I's automaton-rank barrier and Kadirbekov's bounded-correction theorem (`RESEARCH-2026-10-05-rewriting-lane-landscape.md`).  The local-rank row cites them.

## Stop

Green build with `#maze_audit` passing.  Leave a dated handoff.  No successor task.
