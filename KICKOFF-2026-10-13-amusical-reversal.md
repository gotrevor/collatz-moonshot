# KICKOFF 2026-10-13: time reversal (amusical) and the Gaussian relative

Two treadmill lanes share this kickoff.  Each owns ONE file; do not edit the other's.

* **Lane R** (repo `collatz-moonshot-amusical-reversal`): close every `sorry` in
  `CollatzMoonshot/AmusicalReversal.lean`.
* **Lane G** (repo `collatz-moonshot-amusical-gauss`): close every `sorry` in
  `CollatzMoonshot/GaussianRelative.lean`.  Lane G must not depend on Lane R's `sorry`s: if you
  need the "orbit meets `Fix` in at most two points" lemma, prove a local version in your own file
  from the proved `reversing_zpow_fixed`.

## Ratified, do not change

All statements in both files, `yOf`, `gaussH`, `conj`, `gaussPerm`, `conjPerm`, and the proved
`reversing_zpow_fixed`.  Everything in `Amusical.lean`, `AmusicalWindow.lean`,
`AmusicalConstant.lean`, `AmusicalBound.lean`, `Obstructions/Amusical.lean`, `Maze.lean`; other
treadmills own `AmusicalSpitzer.lean`, `AmusicalReturns.lean`, `AmusicalChains.lean`.  Helpers in
your own file or `CollatzMoonshot/AmusicalReversal/*.lean` (R), `CollatzMoonshot/GaussianRelative/*.lean`
(G).  No `native_decide`, no new axioms; `decide +kernel` is fine.

## Lane R: paper proofs

1. **`orbit_inter_fixedPoints_ncard_le_two`.**  If `σ^k x` and `σ^m x` are both fixed by `ι`,
   then (apply `reversing_zpow_fixed` at the base point `σ^k x`) `σ^(2(m−k)) x = x`.  Infinite
   orbit (injective `k ↦ σ^k x`): at most one fixed point.  Finite orbit of exact period `p`:
   fixed points sit at `k` with `2(m − k) ≡ 0 (mod p)`, i.e. at most two residues mod `p`.
2. **`infinitelyManyOrbits_iff_reversor`.**  `⇐`: if finitely many orbits on `ℕ`, the infinite
   set `{x ≥ 0 : ι x = x}` meets some orbit in `≥ 3` points (pigeonhole), contradicting item 1.
   `⇒`: choose a base point in each orbit of `ℤ` (the least `|x|` element, ties broken
   toward the nonnegative one; orbits never change sign since `U` preserves sign, and
   `U(−n) = −U(n)`), and define `ι (σ^k b) = σ^(−k) b`; well defined on cycles too; it is an
   involution, reverses `σ`, preserves sign, and fixes every base point, of which infinitely
   many are nonnegative.
3. **`no_piecewiseAffine_reversor`** (Theorem NR).  From `ι U ι⁻¹ = U⁻¹` get `ι U^ℓ = U^{−ℓ} ι`.
   `U^ℓ` is affine on residue classes mod `4^ℓ` with slope `3^ℓ/2^w` (proved machinery in
   `AmusicalWindow.lean`), `U^{−ℓ}` affine on classes mod `3^ℓ` with slope `2^{w'}/3^ℓ`.  Refine
   `ℤ` into the finitely many cells (piece of `n`, class of `n` mod `4^ℓ`, piece of `U^ℓ n`,
   class of `ι n` mod `3^ℓ`); some cell is infinite; a piece with slope `0` holds at most one
   point (`ι` injective), so on an infinite cell both composites are affine with nonzero slopes
   and agree on two points, hence have equal slopes; compare 3-adic valuations:
   `v₃(a_j/c_j) + ℓ = v₃(a_{j'}/c_{j'}) − ℓ`, impossible for `ℓ` larger than the maximum
   `|v₃|` over the finitely many pieces.

## Lane G: paper proofs

1. **`conj_gaussH_conj_gaussH`.**  The map is defined by 25 residue cases mod `π̄² ↔ 25`; for each
   case compute `H z` (exact division), then `conj (H z)`'s class, then `H` of that, then conj.
   Strategy: reduce to residues — write `z = (a, b)`, case on `(a + 7b) % 25` (25 cases, which
   determine `(a + 2b) % 5`), and in each case show the four exact divisions and the final
   equality by `omega` (all divisions are by the literals 5 or 25).  Independent numeric check:
   `tmp/amusical/gauss/check_H.py` in the main worktree (0 failures on `|a|,|b| ≤ 60`).
2. **`gauss_infinitely_many_orbits`.**  `conjPerm * gaussPerm * conjPerm = gaussPerm⁻¹` and
   `conjPerm * conjPerm = 1` from item 1.  Real integers `(n, 0)` are conj-fixed.  Each orbit
   contains at most two of them (local version of the two-point lemma via `reversing_zpow_fixed`),
   so the map `n ↦ orbit of (n, 0)` is at most 2-to-1 from an infinite set.

Notes for the next lap go in `HANDOFF-amusical-reversal.md` (R) or `HANDOFF-amusical-gauss.md` (G).
