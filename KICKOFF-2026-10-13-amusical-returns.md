# KICKOFF 2026-10-13: returns, exits and residues (amusical witnesses)

Treadmill lane.  Target: close every `sorry` in `CollatzMoonshot/AmusicalReturns.lean`.  Done
when that file is sorry-free.  Four independent statements; land each as a green commit.

## Ratified, do not change

The four statements in `AmusicalReturns.lean` and `stepWeight`; everything in `Amusical.lean`,
`AmusicalWindow.lean`, `AmusicalConstant.lean`, `AmusicalBound.lean`, `AmusicalSpitzer.lean`
(another treadmill owns it), `Obstructions/Amusical.lean` and `Maze.lean`.  Helpers go in
`AmusicalReturns.lean` or `CollatzMoonshot/AmusicalReturns/*.lean`.  No `native_decide`, no new
axioms.  Reuse the residue-class machinery already proved in `AmusicalWindow.lean`
(`amusicalForwardWord`, affine iteration on classes mod `4^L`, CRT counting).

## Paper proofs

1. **`exists_large_nonOrbitMin`.**  Note `x ≡ 1 (mod 4^K)` forces the next `K` steps to be
   `4m+1 ↦ 3m+1`: if `x = 4^K t + 1` then `U^i x = 3^i 4^(K-i) t + 1`, so `U^K x = 3^K t + 1 < x`
   for `t ≥ 1`.  Given the class `c mod 2^k 3^l` and `T`: the first `k` forward steps of `n` are
   fixed by `n mod 4^k` (pick a lift of `c mod 2^k` to `mod 4^k`), and on that class
   `U^k n = (3^k n + d)/2^w` is affine.  Choose `n` by CRT (`mod 4^(k+K)` and `mod 3^l`) so that
   `U^k n ≡ 1 (mod 4^K)` and `n > T`.  Then `U^(k+K) n ≤ (3/4)^K U^k n + 1 ≤ (3/4)^K (3/2)^k n + O(1)`,
   below `n` once `K > 1.41 k` and `n` is large.  So `n` is not an orbit minimum.
2. **`exits_eq_strictMinima`.**  Orbits of positive integers stay positive.  An infinite orbit
   meeting `[1, X]` has a last forward visit there (values are distinct, so only finitely many
   are `≤ X`) and a strict minimum, which lies in `[1, X]`; a cycle has neither (a cycle point
   returns, and its minimum is not strict).  Map each exit to the strict minimum of its orbit;
   this is a bijection between the two filtered sets.
3. **`exists_denseLinearReturns_of_finitelyManyOrbits`.**  Copy the proof of
   `exists_linearlyRecurrent_of_finitelyManyOrbits` (`Amusical.lean`): it produces an orbit
   meeting `[0, X)` in `≥ εX` points for infinitely many `X`, at distinct times; at most
   `2T + 1` times have `|j| ≤ T`; take `T = εX/4` and filter.
4. **`return_defect_bound`.**  Even steps multiply by exactly `3/2`; odd steps from `z` multiply
   by `(3/4)(1 ± 1/(3z))`.  So `log(U^j x / x) = j log 3 − stepWeight·log 2 + Σ_odd log(1 ± 1/(3z_i))`,
   each term of absolute value `≤ 1/(3z_i − 1)` (use `|log(1+u)| ≤ |u|/(1−|u|)`).  The `z_i` are
   distinct integers `≥ 2` (the orbit is infinite, hence injective in time, and avoids the
   cycles `{0}, {1}` since `x ≥ 2`), so the sum is `≤ Σ_{z=2}^{j+1} 1/(3z−1)`, and
   `1/(3z−1) ≤ (1/3)(log(6z+1) − log(6z−5))`, which telescopes to `(1/3) log((6j+7)/7)`.

Notes for the next lap go in `HANDOFF-amusical-returns.md`.
