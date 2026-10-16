# HANDOFF: amusical-trap (research §55)

Target: close every `sorry` in `CollatzMoonshot/AmusicalTrap.lean` (KICKOFF-2026-10-15-amusical-trap.md).

## Status 2026-10-16: done

All twelve ratified targets proved; `#print axioms` on the headlines
(`amusicalV_infinitelyManyInfiniteOrbits`, `amusical_visits_zero_three_five`, `signBlind_gate`)
shows `propext, Classical.choice, Quot.sound` only; `signCollatz_minus_cycle` uses no axioms.
Statements unchanged (diff against `ddc33d5` removes only `sorry`s and "Open" docstrings).
No `native_decide`, lines ≤ 100 chars.

* Trap section: `perm_pow_mem`, `perm_pow_succ_mem_image`, `perm_pow_eq_entry` (a natural power
  carrying a point of `C` to an entry point is trivial), then the three trap theorems.
* Theorem V: residue arithmetic is `unfold; split_ifs; omega`; entry points via
  `V((x−2)/3) = x` for `x ≡ 2 (mod 6)`; infinitude from `n ↦ 6n`
  (`Set.infinite_of_injective_forall_mem`).
* Avoidance: helpers `amusical_mod_eight_ne_four` (off `{0,3,5}`, `U` never hits `4 mod 8`),
  `amusical_odd_of_mod_eight`, `amusical_bound_of_odd`, `amusicalPerm_pow_eq_iterate`,
  `amusicalOrbit_finite_of_periodic`.  Bounded forward orbit ⇒ two iterates coincide ⇒ periodic.
* Sign-blind gate: invariant "odd and `≥ 4K + 3 + k`", `tendsto_atTop_mono`.
