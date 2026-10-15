# KICKOFF 2026-10-14: Lemma E, infinite orbits survive successor swaps (amusical, round 2)

Repo `collatz-moonshot-amusical-round2`: close every `sorry` in `CollatzMoonshot/AmusicalTailEvent.lean`.

## Ratified, do not change

`natPermOrbit`, `natPermOrbits`, `infiniteNatPermOrbits` and the three theorem statements.  Helpers go in
`CollatzMoonshot/AmusicalTailEvent/*.lean`.  No `native_decide`, no new axioms.  Lean lines ≤ 100
characters.  Do **not** edit `RESEARCH-*.md`.  **Commit after every proved target.**  Write notes to
disk as you go.  Look first at `AmusicalOddRewire/Glue.lean` and Mathlib's `Equiv.Perm.SameCycle`,
`Equiv.Perm.cycleOf`, `Equiv.Perm.SameCycle.exists_pow_eq` for reusable orbit machinery.

## Paper proof (Ren checked)

Write `τ = σ * swap a b` (so `τ a = σ b`, `τ b = σ a`, `τ = σ` elsewhere).  Orbits not meeting
`{a, b}` are unchanged (`τ = σ` on them, and they are `τ`-invariant).
* `a = b`: `τ = σ`.
* `a`, `b` on **different** `σ`-orbits `A ∋ a`, `B ∋ b`: `τ` has one orbit `A ∪ B` in their place
  (follow `a ↦ σ b ↦ … ↦ b ↦ σ a ↦ … ↦ a`, or the infinite analogue).  `A ∪ B` is infinite iff one of
  them is; if both are infinite, `A ∪ B` splits into two infinite `τ`-orbits instead: (past of `a`
  in `A`) + (future of `σ b` in `B`), and (past of `b` in `B`) + (future of `σ a` in `A`).  So the
  number of infinite orbits is unchanged and the orbit count drops by at most one.
* `a`, `b` on the **same** `σ`-orbit `A`: if `A` is a finite cycle it splits into two cycles.  If `A`
  is infinite (a chain, `ℤ`-indexed injective), say `b = σ^k a` with `k ≥ 1`: the points
  `σ a, …, b` form a `τ`-cycle (`b ↦ σ a`), and the rest of `A` is one infinite `τ`-orbit (`a ↦ σ b`
  glues the past of `a` to the future of `σ b`).  Again: infinite count unchanged, total count up by
  at most one.
Hence `encard` of infinite orbits is equal, and the set of orbits is infinite for `τ` iff for `σ`
(a change by at most one element preserves `Set.Infinite`).  The list version is induction on `l`
(`List.map_cons`, `List.prod_cons`, `mul_assoc`).  A route that may be shorter: work with orbits as
`SameCycle` classes and prove the bijection of infinite classes directly.

Notes for the next lap go in `HANDOFF-amusical-tailevent.md`.
