# KICKOFF 2026-10-13: weakly sign-uniform no-gos (amusical)

Repo `collatz-moonshot-amusical-uniform`: close every `sorry` in `CollatzMoonshot/AmusicalUniform.lean`.

## Ratified, do not change

All statements and definitions in that file (`rcwaIterSlope`, `AmusicalTopologicallyTransitive`,
`delta`, `deltaInv`, `deltaPerm`).  Everything else in the repo is read-only.  Other treadmills own
`AmusicalAntiKohl.lean` (including `IsRCWA` and `amusical_no_periodic_cone`), `AmusicalSeventh.lean`,
`AmusicalWindowThree.lean`, `AmusicalGlobal.lean` and `AmusicalRewireRatio.lean`.  You may *use*
`amusical_no_periodic_cone` even while it is a `sorry` upstream.  Helpers go in
`CollatzMoonshot/AmusicalUniform/*.lean`.  No `native_decide`, no new axioms.  Lean lines ≤ 100
characters.

⚠️ **Resource rule.**  Never use `decide` or `decide +kernel` over more than a few thousand cases.  An
exhaustive check on 2026-10-13 held 16 GB for 2 h and starved every other box.  These proofs are
valuation, residue and affine-map arithmetic.

## Suggested order (easiest first)

1. **`delta_periodic`.**  Track `x` along its orbit with the invariant from the docstring.  Points
   `≡ 0 (mod 4)` are `4k` with `c = k + 2`; the dihedral steps multiply `c` by `3/2` or `2/3`, so the
   set of multiples of 4 met is inside `{u · 2ⁱ 3^(s−i)}`, which is finite.  Every point of the orbit is
   within two steps of a multiple of 4, or is one of the fixed points `−8`, `−7`.  An injective map on
   an orbit that stays inside a finite set is periodic (pigeonhole on `delta^[i] x`, then cancel
   using `deltaInv`).  Prove the per-step lemmas with `omega` case splits.
2. **`island_cycle_slope`.**  Paper proof in the docstring.  Work on the class `z + M ℤ` with `M` a
   multiple of every modulus involved (`m`, `m'`, and the denominators along the cycle), where every
   map is a single affine map.  Two affine maps agreeing on an infinite set have equal slopes.
   Multiply the slope identity over the cycle; the `ι`-slope factors telescope.
3. **`no_piecewiseAffine_reversor_of_valNonneg`.**  Model it on `no_piecewiseAffine_reversor` in
   `AmusicalReversal.lean`, which is the `p = 3` special case with the same cell-refinement trick
   (`Finite.exists_ne_map_eq_of_infinite`).  The valuation bound uses `padicValRat.mul` and
   `padicValRat.div`.
4. **`amusical_topologicallyTransitive`** (hardest).  Given `amusical_no_periodic_cone`, the residue
   graph mod `M` is strongly connected.  The real content is that a single orbit realizes a path.
   For `U` a direct route may be easier than the agent's general M3: `U^n` is affine on classes mod
   `4ⁿ` with slope `3ⁿ / 2^(e)`, and choosing the 2-adic digits of `x` (CRT with the class of `r`)
   steers `U^n x` modulo `M`.  Factor `M = 2^a 3^b M'` with `gcd(M', 6) = 1`.  If it does not close,
   leave a clean HANDOFF with the exact missing lemma.

Notes for the next lap go in `HANDOFF-amusical-uniform.md`.
