# KICKOFF 2026-10-13: anti-Kohl and transient cones (amusical)

Repo `collatz-moonshot-amusical-antikohl`: close every `sorry` in `CollatzMoonshot/AmusicalAntiKohl.lean`.

## Ratified, do not change

All statements and definitions in that file, and the proved `kappaInv_kappa`, `kappa_kappaInv`,
`kappaPerm`, `kappa_cone`, `ctau_ctau`, `ctauPerm`, `sigmaTauPerm`, `sigmaTau_two_mod_four`.
`AntiKohlConjecture` is an open conjecture: it is a definition, not a target.  Everything else in the
repo is read-only.  Other treadmills own `AmusicalSeventh.lean`, `AmusicalGlobal.lean`, etc.; use their
statements, never edit them.  Helpers go in your own file or in `CollatzMoonshot/AmusicalAntiKohl/*.lean`.
No `native_decide`, no new axioms; `decide +kernel` is fine.  Lean lines ≤ 100 characters.

## Order and paper proofs (agent report antikohl.md; docstrings carry the outlines)

1. **`amusical_antiKohl_class`, `kappa_antiKohl_class`.**  Explicit `a b c` by residue,
   `unfold; split_ifs; omega` for `eqn`, and `padicValRat` lemmas for the slopes `3/2, 3/4` (`p = 3`)
   or `2, 2/3` (`p = 2`).
2. **`hFive_bijective`, `mixedPrime_single_orbit`.**
   * Give an explicit inverse.
   * Slopes: for `y = h x`, `σ y = h (x + 1)`; `x` and `x + 1` have opposite parity, so the slope is
     `(5/4)(6/5) = 3/2` or `(5/6)(4/5) = 2/3`.
   * Pick `a b c` on classes mod 30, checked by `decide` over the 30 residues if convenient.
   * Single orbit: `σ ^ n = h ∘ (· + n) ∘ h⁻¹`.
3. **`orbit_densityZero_of_transientCone`, `infinitelyManyOrbits_of_transientCone`.**  Pure
   combinatorics of counting in `[−X, X]`; see the docstring.
   * Upper density is subadditive, and a finite set has density 0.
   * For the class-tail clause: `{y ≡ r (mod M), N ≤ y ≤ X}` has about `X/M` points.
4. **`amusical_no_periodic_cone`.**  Strong connectivity of the residue graph mod `M`.  Paper proof
   in agent report seventh.md (T4), reproduced:
   * `U` and `U⁻¹` act on `ℤ₂ × ℤ₃` as the full shift.  From any class one reaches any other class
     by choosing digits.
   * Concretely, for residues `r, s` mod `M = 2^a 3^b M₀`, find `x ≡ r` and `t` with `Uᵗ x ≡ s`.
     Prescribe the forward itinerary (fixes `Uᵗ x mod 2^a`) and the backward one (fixes `x mod 3^b`).
     The branch maps act transitively on `ℤ/M₀`: `g_A⁻¹ g_B` is translation by `−2/3`.
   * Simpler self-contained routes are welcome, e.g. show that every class mod `M` reaches the class
     of `0` and that the class of `0` reaches every class.
   * Note `AmusicalGlobal.exists_many_returns` is a sibling target with the same transitivity
     input, owned by another treadmill.
5. **`atLeastSevenOrbits_of_antiKohl`.**
   * Argue by contradiction with `AmusicalAtLeastSevenOrbits`.  The negation gives that every
     nonnegative integer is on one of six orbits; use the existing lemmas in `AmusicalChains.lean`
     and `Obstructions/Amusical.lean`, e.g. `atLeastSeven_or_orbitEight_infinite`.
   * So the orbit of `8` contains every `y ≥ 112`.
6. **`kappa_orbit_densityZero`, `sigmaTau_orbit_densityZero`.**  These are the main grinds.  Apply
   Theorem T with the cones `odd ∪ 12ℤ` and `2 + 4ℤ`.  The cores are periodic sets; prove the
   density recursions by induction on `n` as in the docstrings.
   * κ backward core: `(5/12)(2/3)ⁿ`.
   * σ_τ forward core: `3ⁿ(2 + 4ℤ)`.
   * σ_τ backward core: `(1/2)(3/4)ⁿ⁻¹`.
   * Only "→ 0" is needed, so any upper bound with geometric decay suffices.  E.g. for the κ forward
     core, a crude bound by a contracting weighted sum works.
   * The agent's automaton scripts are not in the repo.  `scripts/amusical/cores.py` gives exact
     numerical targets for `n ≤ 8`.

Notes for the next lap go in `HANDOFF-amusical-antikohl.md`.
