# HANDOFF 2026-09-29 05:07Z — cubic-peel scoped lap, closed and verified

Branch: `main`.  HEAD at write time: `cc41f30` (parent's checkpoint), with the
proof content in `3e60f4c` and the file first added in `ace3715`.

This is the *verification* checkpoint for the scoped lap
`LEAN_DONE_WHEN=sorry-free:CollatzMoonshot/Obstructions/CubicPeel.lean`.
The narrative handoff is `HANDOFF-2026-09-29-cubic-peel.md`, which the parent
session owns and has already updated; this doc records only what I independently
checked, plus one authorship correction, and does not restate that content.

## Target status: MET

- `CollatzMoonshot/Obstructions/CubicPeel.lean`: **0** `sorry`/`admit`.
- Root `lake build`: green, 8818 jobs (also enforced by the pre-commit hook).
- Working tree for that file matches HEAD; `CollatzMoonshot.lean` imports it.
- All five frozen theorems are kernel-clean — `#print axioms` on each reports
  only `propext`, `Quot.sound`, `Classical.choice`, and no project axiom:
  `cubic_peel_value`, `cubic_peel_domain`, `cubic_peel_frontiers`,
  `cubic_peel_link`, `cubic_peel_growth_congruence`.

## Independent numerical check of the landed constants

Recomputed outside Lean against the *landed* defs (`cubicM` = `8979919405 +
13720313250*s`), all true:

- `(3*cubicV+1)/2 = 32*cubicM` and `(3*cubicN+1)/2 = cubicA` — matches
  `cubic_peel_frontiers`.
- `cubicM < cubicN`; all four exchanged labels `Q1,Q2,E1,E2 < cubicM`.
- `cubicP s + 1 = 4*(8081927465 + 12348281925*s)`, slope odd — the shape
  `cubic_peel_growth_congruence` relies on.

## Authorship correction (recorded so it is not mis-attributed later)

I first wrote this file's growth-congruence proof as an elementary
lift-the-exponent induction in ℕ (`odd_slope_hits`: for odd `m`, every `2^j`
divides `a + m*s` for some `s`, stepping `s ↦ s + 2^j` when the cofactor is
odd).  That version was **overwritten on disk by the parent session** between my
`lake build` and my `git add`, so it is not in the repo: `git show
ace3715:CollatzMoonshot/Obstructions/CubicPeel.lean | grep -c odd_slope_hits`
returns 0.  I committed the parent's file without re-reading it and briefly
reported my own version as landed; that report was wrong.

What is in the repo is the parent's `ZMod (2^j)` modular-inverse proof (the route
the kickoff specified), together with a halved `cubicM` and the consequent
`32*cubicM` in `cubic_peel_frontiers`.  It is correct and verified above.  The
two routes are interchangeable; no action is needed, and the ℕ-induction variant
is recorded here only in case a future lap wants a cast-free version.

**Lesson for concurrent laps:** when a system-reminder says an owned file changed
on disk, re-read it immediately before `git add` — a second silent overwrite is
possible, and the pre-commit `lake build` will happily pass on someone else's
correct file.

## Exact next steps

None in this scope: the lap is frozen at five statements by
`KICKOFF-2026-09-29-cubic-peel.md` ("Do not invent next targets or add extra
mathematical claims"), and `DIRECTION.md`'s current directive authorizes no
successor proof lap ("No lap without a mechanism for the gap node").  Two items
the parent may want to resolve at its own discretion, both outside my scope:

1. The commit message of `3e60f4c` states the common odd-ratio product is
   `4(2a-7)/(3(9a+61))`.  I could not confirm that constant; against the draft
   constants I computed a value 8× smaller.  No Lean theorem asserts the closed
   form, so nothing in the proof depends on it — but the prose is worth a
   recheck before it is quoted anywhere load-bearing.
2. The shortcut prefix formula that would turn `cubic_peel_growth_congruence`
   from a statement about an arithmetic progression into a dynamics claim is a
   separate lemma and was deliberately not attempted.

Nothing here claims a palette rule, restricted replay, repair, a balanced
certificate, or any trajectory convergence.
