# HANDOFF: amusical ping-pong

## 2026-10-14: Theorem L closed by 2-adic descent

- Proved `amusical_not_eventually_linear` without changing its statement.  Injectivity of
  `amusical` keeps every iterate of a nonzero input nonzero.  On an even iterate `y`, the defining
  equation gives `2 * amusical y = 3 * y`; multiplicativity of `padicValInt` therefore makes the
  2-adic valuation drop by exactly one.  Iterating this identity one step beyond the valuation at
  time `N` is impossible.
- Exact narrow verification: `lake env lean CollatzMoonshot/AmusicalPingPong.lean` (passes; only
  the two remaining target `sorry` warnings).
- Current blocker: `pingPong_seed_inEngine` is the route-decisive core.  It needs the kickoff's
  cycle lemma tracking `(v5, v7, mod 19)` through an A-run, hand-off, B-run, and return to a seed.
  The infinite-orbits target should then use that engine-forever invariant and the arithmetic
  progression `4705 + 9975 * t`.
- Next attack: create helpers under `CollatzMoonshot/AmusicalPingPong/` for valuation changes under
  multiplication/division by 5 and 7 and for the six-step phase cycle of 8 modulo 19.  Package the
  whole `2*A+2` transition as one seed-to-seed lemma before the strong induction on time.
