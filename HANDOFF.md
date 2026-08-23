# HANDOFF: the Front B dictionary 📖 — DONE (2026-08-23)

**Objective met.** `CollatzMoonshot/FrontB/Dictionary.lean` is sorry-free, both frozen
headlines (`noNontrivialCycle_of_frontB`, `noNontrivialCycle_iff_frontB`) are proved, and
`#print axioms noNontrivialCycle_iff_frontB` shows exactly
`[propext, Classical.choice, Quot.sound]`.  Full `lake build` green.

## What happened this lap

1. **The target as handed off was false.**  `IsTrivial v := numer v = den v` (member = 1)
   made `FrontB` refutably false: `[false, true]` - the trace of the trivial accelerated
   cycle rooted at `2` - is an `IntegerCycle` with `numer = 2`, `den = 1`.  The iff
   headline was therefore unprovable as stated.  Fix (in `Threads.lean`): `IsTrivial v :=
   numer v = den v ∨ numer v = 2 * den v` (member ∈ {1, 2} = the trivial `tstep`-cycle's
   membership).  All other uses of `IsTrivial` are opaque hypotheses, so nothing else moved.

2. **A cleaner Layer-1 engine than the suggested rotation-invariant route**: the
   unconditional iterate identity (`tstep_iterate_identity`, one induction over ℕ)
   `2^m · tstep^[m] n = 3^(ones v) · n + numer v`, `v = traceWord n m`.
   On a cycle it gives `member_identity` by `linear_combination`.  The rotation
   identities were still the per-step engine of the converse (`realize_head_false/true`,
   `realize_iterate`), via `rot = List.rotate 1` and `List.rotate_length`.

3. **Layer 2** is the `walk` lemma: chase a `step`-cycle with `tstep`, hit-or-overshoot
   invariant with the bound `d ≤ 2j` forcing a positive accelerated period; the only
   missable members are `3w+1`-intermediates of odd members, and an intermediate of an
   intermediate is parity-impossible.

## Consequence

Every theorem in `FrontB/Threads.lean` is now a genuine statement about Collatz on ℕ
(docstring warning there replaced).  Both fronts' boards remain: Front B open threads
(Compression ~55%, BoundedDen ~12%), Front A (`FrontA/`, Rigidity) untouched this lap.

## Next attack

- The hardest open obligation on the Front B board is **`Compression`**
  (`Threads.lean`): a nontrivial integral cycle has boundedly many circuits.  Nothing
  formal exists toward it; `FRONT-B-ROUTES.md` thread 1 has the prose.
- Uncommitted changes from a *previous* session sit in `Rigidity*`, `FrontA/`, README and
  notes files - not mine to judge; left uncommitted deliberately.
