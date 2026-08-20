# Architect notes - 2026-08-20 🌙

*Session handoff.  Supersedes [architect-notes-2026-07-20.md](architect-notes-2026-07-20.md)
(still the reference for the founding design reasoning - the 2-adic-blindness trap, the
two-proof architecture, the `Assumed/` three-tier doctrine, Eliahou bookkeeping).  Written by
Ren; Trevor reopened the repo after a month with "we're going to prove the Collatz conjecture,
you and I and OpenAI."*

## What changed today

**The lane keystone moved from mass to frequency.**  W1 asked invariant measures to charge the
trivial cycle; W1′ asks them to keep the *odd set* below `log 2 / log 6`.  Same conditioning,
different currency - and the new currency is the one that controls archimedean size, so it
cashes out with no funnel upgrade owed.

### New, all axiom-clean (`propext`/`Classical.choice`/`Quot.sound`), verified 2026-08-20

| Theorem | File | Content |
|---|---|---|
| `continuous_T2`, `measurable_T2` | `Rigidity/Padic.lean`, `Invariant.lean` | K-B prerequisite |
| `evenSet_eq_ball`, `isClopen_evenSet` | `Rigidity/Padic.lean` | parity **is** the unit ball |
| `norm_half_sub`, `lipschitzOnWith_half` | `Rigidity/Padic.lean` | halving doubles distance |
| `T2_neg_one`, `T2_neg_two`, `T2_neg_cycle` | `Rigidity/Padic.lean` | the `-1 → -2` invariant 2-cycle |
| `iterate_mul_two_pow_le` | `Rigidity/Drift.lean` | **the drift estimate** |
| `lt_of_growth_lt`, `lt_of_oddSteps_freq_lt` | `Rigidity/Drift.lean` | descent criteria, power + frequency form |
| `freqThreshold_one`, `freqThreshold_lt_sharp`, `tendsto_freqThreshold` | `Rigidity/Drift.lean` | `1/3` → `log 2 / log 6` |
| `not_diverges_of_repeat`, `injective_of_diverges`, `exists_floor_of_diverges` | `Rigidity/Drift.lean` | **the floor is free** |
| `conjecture_of_freq_descent` | `Rigidity/Drift.lean` | the consumption form |
| `ParityRigidityW1'`, `oddSetZ2`, `isClopen_oddSetZ2` | `Rigidity/Invariant.lean` | the new keystone (a `def`, by doctrine) |

## Load-bearing reasoning (do not re-derive)

1. **The `+1` has no exact affine potential.**  `n ↦ n + c` transports the even branch only for
   `c ≤ 0` and the odd branch only for `c ≥ 1/2`.  So it cannot be conjugated away; it is
   *throttled* by a floor instead - `growth N = 3 + 1/N`, which is `4` at `N = 1` and tends to
   `3`.  Everything in `Drift.lean` is that one constant.
2. **The crude bound is blind by exactly one case.**  `freqThreshold 1 = 1/3` *is* the odd-step
   frequency of a typical orbit (one odd step per two halvings).  Moving off `1/3` toward
   `log 2 / log 6 ≈ 0.3868…` is the whole content.
3. **Clopen parity is the joint between the two pictures.**  `isClopen_evenSet` makes
   `μ ↦ μ oddSetZ2` weak-* continuous (Portmanteau with an *empty* boundary), so the empirical
   odd frequency of an orbit converges to it.  That single fact is what lets a measure statement
   (W1′) become an archimedean statement (`Drift.lean`).
4. **Divergence supplies its own floor**, so the divergence front gets the *sharp* constant, not
   the crude one: an unbounded orbit never repeats, hence is eventually above every `N`.
5. **The conditioning in W1′ is load-bearing and provably so.**  `T2_neg_cycle` is an invariant
   2-cycle with odd frequency `1/2`, above the threshold.  Any unconditioned parity-rigidity
   statement is *false*, exactly as for W1.  Same trap as the founding session's note 1.
6. **W1 is retained, not retired.**  It carries the funnel mechanism, which W1′ does not, and M3
   may want it.  Both are pins.

## Next moves (M2′)

`ParityRigidityW1' → NoDivergentOrbit` needs exactly two more pieces:

- **(b) Krylov-Bogolyubov**, THEOREM-grade axiom in a new `Assumed/KrylovBogolyubov.lean`:
  compact space + continuous map ⟹ orbit-empirical limit measures exist and are invariant and
  supported on the orbit closure.  Quantify over the orbit closure, per the blindness trap.
  `continuous_T2` is now available as the hypothesis it needs.
- **(c) Portmanteau on the clopen parity set**: empirical measures `(N+1)⁻¹ • ∑ dirac`, then
  `μ oddSetZ2` = the limiting odd-step frequency.  The clopen boundary is empty, so this is the
  easy form of Portmanteau.

Then infinite descent closes it: a divergent orbit above its floor descends strictly from every
point (`lt_of_oddSteps_freq_lt`), and an infinite strictly-decreasing sequence of naturals is
impossible.  That last step is not yet formalized - it is the third bite.

## House rules

Unchanged from 2026-07-20 (investigatory tier, `Assumed/` doctrine, explicit `git add <paths>`
never `add -A`, `*.pdf` gitignored, `step` not `col`, notes file per working day).  The parallel
session's `papers/` edits are still uncommitted in the tree - left alone deliberately.
