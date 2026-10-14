# KICKOFF 2026-10-13: toward a seventh orbit (amusical)

Repo `collatz-moonshot-amusical-seventh`: close every `sorry` in
`CollatzMoonshot/AmusicalSeventh.lean`.  The four targets are independent; do the easy ones first
(`atLeastSeven_of_orbit8_not_cofinite`, then `rewire_single_orbit`), then
`amusical_pow_classUnion_invariant`, then `sparse_sweep` (the heaviest).

## Ratified, do not change

All statements in that file.  Everything else in the repo is read-only.  Helpers go in your own
file or `CollatzMoonshot/AmusicalSeventh/*.lean`.  No `native_decide`, no new axioms;
`decide +kernel` is fine.  Lean lines ≤ 100 characters.

## Paper proofs

The docstrings carry the proof sketches.  Fuller versions: agent report `seventh.md` (copied below
in outline) and `RESEARCH-2026-10-13-amusical-single-chain.md` §11.

1. **`atLeastSeven_of_orbit8_not_cofinite`.**  The infinite set minus the finite
   `knownCycleMembers` is nonempty; take `n` there.  Each known cycle is a finite set closed under
   `U` and `U⁻¹` (see the `cyc` helper inside `amusical_six_distinct_orbits`), so its orbits lie
   inside `knownCycleMembers` and differ from `amusicalOrbit n`; `amusicalOrbit n ≠ amusicalOrbit 8`
   since `n ∉ amusicalOrbit 8` and `n ∈ amusicalOrbit n`.  Build the 7-element Finset.
2. **`rewire_single_orbit`.**  Pure combinatorics.  Infinite orbit ⇒ for each `B` only finitely
   many times have value `≤ B` (injectivity of `j ↦ (σ^j) n`).  First crossing of `Y` forward (or
   backward) lands in `[Y, 2Y)` by `hstep`.  Enumerate infinite orbits (countable: index by their
   least element), choose for `k ≥ i` one forward and one backward cut of orbit `i` in
   `[4^k, 2·4^k)`; cuts below `N` number `O((log N)²)`.  The cut times are unbounded in both
   directions, so the segments between consecutive cuts are finite; the set of segments is
   countably infinite, enumerate it by `ℤ` (`Equiv` with `ℤ` via `Denumerable`), and define
   `τ (last s_z) = first s_{z+1}`, `τ = σ` elsewhere.  If there is at most one infinite orbit you
   may take `τ = σ` (handle as a separate case).  An alternative, simpler construction is welcome
   if it meets the same statement.
3. **`amusical_pow_classUnion_invariant`.**  Strong connectivity of the residue graph of `Uᵐ` mod
   `M`: show every class `r` reaches every class `s`.  CRT split `M = 2^i 3^j N`.  For a branch word
   `w` (symbols E/A/B) of length `L`, the integers following `w` form one class mod `2^{|w|}` and
   `U^L` is affine there with slope `3^L / 2^{|w|}`; images are classes mod `3^L` (exact cylinder
   transport is already proved in `AmusicalContinuousReversor/Cylinder.lean`; read it).  Mod `N`,
   the composed affine maps of words of length `≡ 0 (mod m)` generate a subgroup of the finite group
   `Aff(ℤ/N)` containing translations, hence transitive.  Then `h` (image equals itself) plus
   connectivity forces `R = ∅` or `R = univ`.
4. **`sparse_sweep`.**  Lemma W (window order is a residue condition for `n ≥ 2·324^L` mod `12^L`),
   Lemma T (Chernoff: the share of `n mod 12^L` whose window minimum is more than `K` steps away
   is `≤ 2 Σ_{i>K} ρ^i`, `ρ = 1/√6 + 1/√3`, via `P(S_i < 0) ≤ E e^{−S_i/2} = ρ^i` exactly over
   residues), and the proved separation `IsWindowMin.iterate_eq_of_isWindowMin`
   (`AmusicalChains.lean`).  Count: points below `X` with `|t| ≤ T` are `≤ 3√X + ε(K) X +
   (2K+1)((2T+2K+1)/(L−K+1) + 1)` with `L = ⌊log X / (2 log 324)⌋`; choose `K`, then `c`.

Notes for the next lap go in `HANDOFF-amusical-seventh.md`.
