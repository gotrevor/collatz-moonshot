# HANDOFF: amusical ping-pong

## 2026-10-14: scoped objective complete

- Proved `pingPong_seed_inEngine` with its ratified statement unchanged.  The proof packages one
  complete cycle internally: an A-run lowers `v₅` and raises `v₇`, the `15x` hand-off starts the
  B-run, the B-run reverses the counters while doubling the accumulated `v₅`, and the final `3x`
  step returns to a seed of valuation `2A + 1`.  An exact mod-19 countdown invariant supplies both
  phase membership and the final seed congruence.  Strong induction on time then concatenates
  cycles of length `2A + 2`.
- Proved `infinitelyManyOrbits_of_pingPong`.  Every nonzero forward displacement of a seed is an
  engine image and hence divisible by `3`.  Thus two seeds prime to `3` in one two-sided orbit must
  coincide, treating negative displacement by applying the inverse exponent.  The injective
  progression `4705 + 9975t` consists of seeds prime to `3`, so its orbit image is infinite.
- Added three general phase helpers to `AmusicalPingPong/Phase.lean`: powers of `8` stay in `K`, a
  seed congruence forces A-phase membership, and either counter transition preserves a mod-19
  countdown while multiplying phase by `8`.
- Adversarial review found no statement drift or route defect.  In particular, the transition
  count is exactly `2A + 2`, and the positive/negative exponent split proves orbit injectivity
  without assuming that the engine is backward invariant.
- Exact verification:
  `~/personal/bin/lean-green ~/src/collatz-moonshot-amusical-pingpong --target
  CollatzMoonshot.AmusicalPingPong --import CollatzMoonshot.AmusicalPingPong --axioms
  CollatzMoonshot.Amusical.pingPong_seed_inEngine --axioms
  CollatzMoonshot.Amusical.infinitelyManyOrbits_of_pingPong --axioms
  CollatzMoonshot.Amusical.amusical_not_eventually_linear` — 8712-job build, final verdict
  `FORMALIZE-TIER GREEN`.
- All three headline declarations have exactly the canonical axiom footprint
  `[Classical.choice, Quot.sound, propext]`; none depends on the out-of-scope sorries in the
  imported `AmusicalAntiKohl.lean`.
- Current blocker: none.  `CollatzMoonshot/AmusicalPingPong.lean` is sorry-free, so the scoped host
  predicate is met.  No stretch objective was assigned; the next action is to stop rather than
  enter modules owned by other treadmills.

## 2026-10-14: residue and valuation transition kernel

- Added `CollatzMoonshot/AmusicalPingPong/Phase.lean`, imported by the ratified target file.  It
  proves the A- and B-phase residue sets are preserved by their respective `21/5` and `75/7`
  transitions, the A-to-B multiplication by `15`, and the common fact that every one of the four
  engine equations has output divisible by `3`.
- The same helper now proves the load-bearing counter arithmetic: `valuation_stepA` changes
  `(v₅,v₇)` by `(-1,+1)`, while `valuation_stepB` changes it by `(+2,-1)`, including
  nonzeroness of every successor.  `emod_eq_zero_iff_padicValInt_pos` bridges these counters back
  to the exact branch predicates in `InEngine`.
- Exact narrow verification: `lake env lean CollatzMoonshot/AmusicalPingPong/Phase.lean` (passes;
  no `sorry`).
- Current blocker: package these one-step facts into the full cycle lemma.  The remaining phase
  boundary facts are the initial A-phase membership from the seed congruence and the final seed
  congruence after `A` B-steps and multiplication by `3`.
- Next attack: define local A-run and B-run induction invariants in the proof of
  `pingPong_seed_inEngine`, prove the `2*A+2` seed-to-seed transition, then use strong induction
  on time.  After that, use `three_dvd_of_engine_equation` to prove uniqueness of prime-to-3
  engine-forever representatives and inject the progression `4705 + 9975*t` into orbit space.

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
