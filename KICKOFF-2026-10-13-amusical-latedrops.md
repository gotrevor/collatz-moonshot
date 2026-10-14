# KICKOFF 2026-10-13: late drops (amusical)

Repo `collatz-moonshot-amusical-latedrops`: close every `sorry` in `CollatzMoonshot/AmusicalLateDrops.lean`.

## Ratified, do not change

All statements and definitions in that file (`IsFwdWin`, `IsBwdWin`, `lateDropCount`,
`AmusicalLateDropsSparse`).  Everything else in the repo is read-only.  Other treadmills own other
`Amusical*.lean` files, including `AmusicalGlobal.lean`, which owns `infinitelyManyOrbits_of_survival`;
you may use it, but you don't need it.  Helpers go in `CollatzMoonshot/AmusicalLateDrops/*.lean`.
No `native_decide`, no new axioms.  Lean lines ≤ 100 characters.

⚠️ **Resource rule.**  Never use `decide` or `decide +kernel` over more than a few thousand cases.  An
exhaustive check on 2026-10-13 held 16 GB for 2 h and starved every other box.

## Suggested order

1. **`walk_mgf_tilt`.**  Use `Real.rpow_sub`, `Real.rpow_one`, and `(a/b)^θ = (b/a)^(−θ)`, or
   `Real.div_rpow`.  Pure algebra.
2. **`amusicalOrbit_infinite_of_strictFwd`.**  If the orbit is finite, `n` is periodic
   (`amusical` is injective, so pigeonhole on `amusical^[i] n`), and `amusical^[p] n = n`
   contradicts `n < amusical^[p] n`.
3. **`infinitelyManyOrbits_of_lateDrops`.**
   * Set `δ = f_L b_L` and apply `windowMinDensity L` (`AmusicalWindow.lean`).  Eventually the
     window minima below `X` number `≥ (δ − η/2) X`.
   * With `card_windowMin_le`, along the frequent sequence the survivors-both-ways below `X`
     number `≥ (η/2) X`, hence are unbounded as `X → ∞`.
   * A both-ways survivor is an orbit minimum (`IsOrbitMin`): orbit points are
     `(amusicalPerm ^ j) n`; use `amusical_iterate_eq_perm_pow` and
     `amusicalInv_iterate_eq_perm_pow`.
   * Finish with `amusicalInfinitelyManyOrbits_of_minima`.
4. **`lateDrops_dense`.**  The contrapositive of step 3, with `η = ε`.

Notes for the next lap go in `HANDOFF-amusical-latedrops.md`.
