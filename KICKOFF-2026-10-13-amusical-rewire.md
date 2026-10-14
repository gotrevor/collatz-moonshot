# KICKOFF 2026-10-13: bounded-ratio rewiring (amusical)

Repo `collatz-moonshot-amusical-rewire`: close the `sorry` in `CollatzMoonshot/AmusicalRewireRatio.lean`.

## Ratified, do not change

The statement of `exists_boundedRatio_rewire`.  Everything else in the repo is read-only; in
particular, `AmusicalSeventh.lean` (and its `rewire_single_orbit`) is owned by another treadmill.
Helpers go in `CollatzMoonshot/AmusicalRewireRatio/*.lean`.  No `native_decide`, no new axioms.
Lean lines ≤ 100 characters.

## Paper proof (agent report global.md §2; module docstring)

* **Degenerate cases.**  If `U` has at most one infinite orbit on `ℕ`, take `τ = U` restricted to
  `ℕ`.  It is a permutation of `ℕ`: use `amusical_nonneg` and its inverse, `amusicalPerm`.
* **Main case.**  Enumerate the infinite orbits by increasing minimum, `m_1 < m_2 < ⋯`.  The list
  may be finite, with at least two orbits; then freeze the multiplicity.
  * Choose `Y_k ≥ 8 Y_{k−1}` with `Y_k > m_k`, e.g. `Y_k = max(8 Y_{k−1}, m_k + 1)`.
* **Steps.**  For `c ≥ 0`, `U c ∈ [(3c − 1)/4, 3c/2]` and `U⁻¹ y ∈ [2y/3, (4y + 3)/3]`.  An
  infinite orbit tends to `+∞` in both directions, so every first passage exists.
* **Cuts and segments.**  As in the docstring.  Gluing the end of one segment to the start of the
  next always swaps one `U`-image at scale `k` for another, and every such image lies in
  `[(3Y_k − 1)/4, 2.25 Y_k + 2]`.  That gives `τ ≤ 3U + 3` and `U ≤ 3τ + 3`.
* **Count.**  At most `2k` changes at scale `k`, all `≥ Y_k ≥ 8^(k−1)`.  So the changes below `N`
  are at most `∑_{k ≤ log₈ N + 1} 2k ≤ C (log₂ N + 1)²`.
* **Formalization hint.**  Build `τ` as the successor map of an explicit `ℤ`-indexed enumeration
  of the union of infinite orbits.  The recursion `T_{k+1} = B_{1,k} · T_k · F_{1,k} · core_{k+1} ·
  B_{2,k} F_{2,k} ⋯ B_{k,k} F_{k,k}` nests `T_k` with a nonempty segment on each side, so it
  converges to a bi-infinite sequence.  Any equivalent bookkeeping is fine.  A cleaner
  construction with the same three conclusions is equally welcome.

Notes for the next lap go in `HANDOFF-amusical-rewire.md`.
