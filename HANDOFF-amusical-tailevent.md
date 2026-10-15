# HANDOFF — amusical-tailevent (2026-10-15)

**Objective COMPLETE.** `CollatzMoonshot/AmusicalTailEvent.lean` is sorry-free; the three ratified
statements and the three definitions are unchanged (diff removes only `sorry`s and `import Mathlib`).

Route: not the merge/split case analysis of the kickoff, but one stronger general statement in
`CollatzMoonshot/AmusicalTailEvent/Agree.lean`, for **any** two permutations of `ℕ` agreeing
outside a finite set `S`:

* `TailEvent.infinite_orbits_iff_of_agree`: a `σ`-orbit avoiding `S` is a `τ`-orbit
  (`orb_eq_of_agree`), so `orbits σ ⊆ orbits τ ∪ orb σ '' S` (`orbits_subset_of_agree`).
* `TailEvent.encard_infiniteOrbits_eq_of_agree`: infinite orbits are matched by forward tails.
  An infinite orbit is injective in forward time (`pow_injective_of_infinite`), so it leaves `S`
  for good (`exists_forward_avoid`); from such a point `τ` and `σ` iterate identically
  (`pow_eq_of_forward`).  The tail map is an injection into `τ`'s infinite orbits; symmetry gives
  `≤` both ways.
* `mul_swap_agree`: `σ * swap a b = σ` off `{a, b}`.  The list target is induction on `l`.

So Lemma E holds for any finitely supported perturbation, not only products of swaps.

Axioms: `propext`, `Classical.choice`, `Quot.sound`.  No `native_decide`.
`lake build CollatzMoonshot.AmusicalTailEvent` green (8707 jobs).

Next: nothing open in this objective's scope.
