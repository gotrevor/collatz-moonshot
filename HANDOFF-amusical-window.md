# HANDOFF: amusical window density (2026-10-13, target complete)

## Concrete advance

`CollatzMoonshot/AmusicalWindow.lean` is now sorry-free.  The ratified theorem
`windowMinDensity (L : ℕ) : WindowMinDensity L` is proved without changing its statement or
the definitions of `IsWindowMin`, `fwdSurv`, `bwdSurv`, or `WindowMinDensity`.

The completed route is the one prescribed by the kickoff:

- Every forward word of length `L` has exactly `2^L` fibers modulo `4^L`.
- A backward word has exactly `2^b` fibers modulo `3^L`, where `b` is its number of marked
  (`×4/3`) branches.
- The affine slopes are never equal to the diagonal at positive times, and their order is
  exactly the prefix inequality appearing in `fwdSurv` or `bwdSurv`.
- `windowBound` gives one explicit threshold beyond which `IsWindowMin` is precisely the
  conjunction of the forward and backward word-survival predicates.
- A finite CRT count factors the good joint residue classes, while general periodic-count and
  finite-perturbation lemmas establish the resulting natural density.

The reusable elementary counting and density infrastructure lives in the new module
`CollatzMoonshot/AmusicalWindow/Count.lean`.  The in-flight Aristotle project
`e94297bf-c4a8-41e0-bff8-722bef5437c0` supplied a partial snapshot during the lap; only lemmas
ported into the repository and independently accepted by the local kernel were retained.

No new axiom, certificate, `native_decide`, `sorry`, or heartbeat override was introduced.
The pre-existing untracked `CLAUDE.local.md` was left untouched.

## Exact verification

```text
python3 scripts/amusical/window.py
lake build CollatzMoonshot.AmusicalWindow
rg -n '(^|[^[:alnum:]_])sorry([^[:alnum:]_]|$)|(^|[^[:alnum:]_])axiom([^[:alnum:]_]|$)|native_decide|maxHeartbeats' \
  CollatzMoonshot/AmusicalWindow.lean CollatzMoonshot/AmusicalWindow/Count.lean
git diff --check
~/personal/bin/lean-green /Users/gotrevor/src/collatz-moonshot-amusical-window \
  --target CollatzMoonshot.AmusicalWindow \
  --axioms CollatzMoonshot.Amusical.windowMinDensity
```

The source scan has no matches.  The gate verdict is `FORMALIZE-TIER GREEN` (8708 jobs), and
the headline theorem reports only Lean's standard foundational axioms:
`Classical.choice`, `Quot.sound`, and `propext`.

## Current blocker

None.  The host predicate `sorry-free:CollatzMoonshot/AmusicalWindow.lean` is met.

## Next highest-value attack

No further work is in scope for this lap.  The host can accept the committed checkpoint and stop
the amusical-window treadmill objective.
