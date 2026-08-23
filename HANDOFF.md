# HANDOFF: the Front B dictionary 📖

**Objective**: make `CollatzMoonshot/FrontB/Dictionary.lean` sorry-free.  That file IS the
task - its module docstring carries the full plan, the two-layer structure, and the
hand-checked sanity anchors.  Nothing else in the repo is in scope for this run.

## The contract (also in the file - it wins if we drift)

- **Frozen**: `noNontrivialCycle_of_frontB` and `noNontrivialCycle_iff_frontB` keep their
  exact statements.  Guard by name.
- **Adjustable**: every lemma marked MILESTONE - restate, split, reorient, or replace them
  freely if a cleaner path appears.  They are scaffolding, not deliverables.
- **No new axioms.**  This is our own target (repo doctrine: our targets are never
  axioms).  Endgame check: `#print axioms noNontrivialCycle_iff_frontB` shows at most
  `[propext, Classical.choice, Quot.sound]`.
- Zero sorries anywhere in the file at the end; the treadmill's `--done-when` watches
  exactly this file.

## What is already proved and load-bearing (use, don't re-derive)

- `FrontB/Words.lean`: `numer` prepend recursion (the ONLY usable induction handle -
  do not fall back to the Σ-of-monomials form), `two_mul_numer_rot_false/true` (the exact
  rotation identity over ℤ - one orbit step = one word rotation; this is the engine of
  `member_identity`), `not_two_dvd_den`, `not_three_dvd_den`, append lemmas.
- `Conjecture.lean`: `OnCycle`, `NoNontrivialCycle`, `step_pos`, orbit lemmas.
- `FrontB/Threads.lean`: `IntegerCycle`, `IsTrivial`, `FrontB`.

## Working notes

- The suggested proof of `member_identity`: strengthen to an invariant along the orbit
  relating `tstep^[i] n` to `numer`/`den` of the i-th rotation of the trace, using that
  `traceWord (tstep n) m` relates to `rot (traceWord n (m+1))` on a cycle.  Expect to need
  a `traceWord`-vs-`rot` commuting lemma on cyclic words - state it as a new MILESTONE.
- Layer 2 (`step` ↔ `tstep`) is fiddly bookkeeping, not deep: in a `step`-cycle an odd
  member's successor `3n+1` is even.  Take the accelerated members to be the non-`3n+1`-
  intermediate members.
- `frontB_of_noNontrivialCycle` (the converse) is the harder half and is a MILESTONE, not
  a headline: realize an `IntegerCycle` word by `n' := (numer v / den v).toNat` and walk
  the word.  If it resists, prioritize finishing `noNontrivialCycle_of_frontB` cleanly -
  the iff headline needs both, but a lap that lands the forward direction sorry-free has
  earned its keep even if the converse rolls to the next lap.
- Commit green early and often; small commits per milestone.
