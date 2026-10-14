# KICKOFF 2026-10-13: cycle bound (amusical)

Repo `collatz-moonshot-amusical-cycles`: close every `sorry` in `CollatzMoonshot/AmusicalCycleBound.lean`.

## Ratified, do not change

All statements and definitions in that file (`cycleMinBound`, `CycleMinBoundHolds`,
`CycleMinSearch`, `AmusicalNoNewCyclesUpTo`).  Everything else in the repo is read-only; other
treadmills own other `Amusical*.lean` files.  Helpers go in `CollatzMoonshot/AmusicalCycleBound/*.lean`.
`stepBits` comes from `AmusicalEscape.lean`.  No `native_decide`, no new axioms.  Lean lines ≤ 100 characters.

⚠️ **Resource rule.**  Never use `decide` over more than a few thousand cases, and never `decide`
over an enumerated type.  An exhaustive check on 2026-10-13 held 16 GB for 2 h and starved every
other box.  The two computational targets below are allowed one `decide +kernel` each, on a single
call to a fuelled, structurally recursive `Bool` checker over `Nat`/`Int`.  The kernel's `Nat`
arithmetic is GMP-backed.  **Measure first** on the small instance named in the docstring, and
watch memory (`ps`/`/proc`).  If the small instance takes more than 2 GB or 2 minutes, stop and
leave the exact numbers in the HANDOFF instead of scaling up.

## Suggested order

1. **`cycle_min_mod_six`.**  Unfold `amusical` and `amusicalInv`; `U n` and `V n` lie on the cycle
   (`V n = U^[P−1] n`).
2. **`cycle_min_meet`.**  Pure iterate bookkeeping: `amusicalInv^[j] n = amusical^[P − j] n` for
   `j ≤ P` (use `amusicalInv_amusical`).
3. **`amusical_cycle_min_bound` (Theorem A★).**
   * Step identity: `2 ^ stepBits x * U x = 3 * x + d x` with `d ∈ {0, 1, −1}`.
   * Take the product over `Finset.range p` and reindex by the cycle (`hcyc`) to cancel `∏ xᵢ`.
   * Split the even and odd factors.
   * Bound each odd ratio with `x ≥ m`, multiply the inequalities (`Finset.prod_le_prod`), and
     clear denominators.
   * Work in `ℚ` and cast back.
4. **`noNewCycles_of_search`.**  The paper proof is in the docstring.  You need `amusical_neg`
   (negatives), the minimal period, Theorem A★ turned into `m ≤ cycleMinBound p e`, and
   `cycle_min_meet`.
   * The real-to-floor step: from `3^p (3m−1)^k ≤ 2^e (3m)^k` and the reverse, derive
     `(3m−1) · D ≤ k · max(2^e, 3^p)`.  Use `(1+u)^k ≥ 1 + ku` and `(1−u)^k ≥ 1 − ku` (Bernoulli).
     This is a cleaner route than logarithms.
   * The cycles of 1, 2, 4 and 44 are in `knownCycleMembers` (`amusical_small_cycles`,
     `amusical_cycle_fortyFour`).
5. **`cycleMinBound_31866`** (computational).  Prove the reduction lemma: if `2^e ≥ 2 · 3^p` or
   `3^p ≥ 2 · 2^e`, then `cycleMinBound p e ≤ p`.  Then check the remaining `e` (at most two per `p`)
   with a checker.  Measure on `P = 665`, `X = 65707` first.
6. **`amusical_noNewCycles_199`** (stretch, computational).  Use `noNewCycles_of_search` with
   `P = 199`, `X = 4964`, `H = 100`.  Write a `Bool` checker for `CycleMinSearch` with a soundness
   lemma, and measure on `X = 173`, `H = 6` first.  If it closes, also prove
   `Literature.AtkinNoShortCycles` from it.

Notes for the next lap go in `HANDOFF-amusical-cycles.md`.
