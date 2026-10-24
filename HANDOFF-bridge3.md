# Handoff: Bridge3 edges

Branch `ren/bridge3` (worktree `~/src/collatz-moonshot-bridge3`), cut from
`ren/conjugacy-ladder` at daad7a1.  Operator plan: `BRIDGE3-NEXT.md`.  Scoped completion target:
`sorry-free:CollatzMoonshot/Conjugacy/Bridge3.lean`.

## Checkpoint (2026-10-24, autonomous grind lap 1)

The scoped objective is complete.  `CollatzMoonshot/Conjugacy/Bridge3.lean` is sorry-free, all
three pinned edge statements are unchanged, and the three teeth still compile.

- `bias_eq_sum_levelSign` is the existing fiberwise band partition `sum_biasBand`.
- `abs_levelSign_le` now regroups the slice by its Syracuse value, splits mass into oscillation
  plus the uniform lift, and uses an exact alternating-sum lemma for the odd number
  `3^(a-m)` of lifts in each class.
- `biasDecays_of_truncatedSyracMixing` splits at `11j/20`.  Low slices contribute at most
  `2ε·2^j`.  For the upper tail, `Bridge3Aux.lean` proves the exact identity
  `Σ_{r<2^j} (2·oddCount(r,j)-j)^2 = j·2^j`; Chebyshev gives the explicit bound
  `#high/2^j ≤ 100/j`, which tends to zero.

Exact verification:

```text
~/personal/bin/lean-green ~/src/collatz-moonshot-bridge3 \
  --target CollatzMoonshot.Conjugacy.Bridge3 \
  --import CollatzMoonshot.Conjugacy.Bridge3 \
  --axioms CollatzMoonshot.Conjugacy.bias_eq_sum_levelSign \
  --axioms CollatzMoonshot.Conjugacy.abs_levelSign_le \
  --axioms CollatzMoonshot.Conjugacy.biasDecays_of_truncatedSyracMixing

✅ FORMALIZE-TIER GREEN
```

Each of the three declarations reports exactly `[propext, Classical.choice, Quot.sound]` (the
gate prints the same set in sorted order).  `rg` finds no `sorry`, `native_decide`, or declared
axiom in `Bridge3.lean` / `Bridge3Aux.lean`.

Current blocker: none.  Next highest-value action: no further in-scope proof work; preserve this
green checkpoint and return to the operator for any later objective.  In particular, do not touch
`Fourier.lean` or the other Conjugacy modules.

## Initial checkpoint (2026-10-24, lap 0, by the attended session personal-c5)

The statements, definitions and teeth are in place and build green, with three sorries:
`bias_eq_sum_levelSign`, `abs_levelSign_le` and `biasDecays_of_truncatedSyracMixing`.  The
mathematics is research note §11.  The numerical checks are `experiments/conjugacy/fsm_bridge.py`
(the reduction holds exactly for `j ≤ 20`) and `twisted_charfn.py`.

Next: edge 2 (elementary, self-contained), then edge 1, then edge 3.
