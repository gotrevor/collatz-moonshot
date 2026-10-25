# Kickoff 2026-10-25: prove `sliceCharDecay_of_pascalDampingDecay` (`CollatzMoonshot/Conjugacy/SliceSeven.lean`)

Branch `wip/conjugacy-slice7b` (worktree `~/src/collatz-moonshot-fourier`), from `ren/conjugacy-ladder` @ `22a9a7b` (SliceCharDecay carries `1 ≤ j`; its `j = a = 0` counterexample is fixed).  Context: research note §13; the edge's docstring and `SliceDecay.lean`'s module docstring carry the English proof.  `PascalDampingDecay` stays an open hypothesis (its proof is the tao-collatz Sec7P campaign); you prove only the edge.

## The proof, in steps

1. **Slice law formula.**  For `r ∈ levelSet j a`, let `t_1 < … < t_a` be the odd-step times of `r` in `[0, j)`.  Then `2^j · T^j r = 3^a r + Σ_k 3^{a−k} 2^{t_k}`, so mod `3^a`, `T^j r ≡ Σ_{m=1}^{a} 3^{m−1} 2^{−T_m}` with `T_m := j − t_{a+1−m} ∈ [1, j]` increasing.  `r ↦ {t_k}` is a bijection `levelSet j a ≃ a-subsets of [0, j)` (Terras: parity vectors of `r < 2^j` are all of `{0,1}^j`).  Look in `Digits.lean` (`onesSet`, `accWord`) and `Bridge3*.lean` before proving any of this from scratch.
2. **Gaps.**  A uniform `a`-subset of `[1, j]` is iid `Geom(p)` gaps `g_1, g_2, …` conditioned on `T_a ≤ j < T_{a+1}`, for every `p ∈ (0,1)`.  Its probability is exactly `P(Bin(j, p) = a)`.
3. **Pairing.**  Group gaps in pairs `(g_{2i+1}, g_{2i+2})`, `b_i` the pair sum.  Given every `b`, each pair is uniform over its `b_i − 1` splits, under the slice law as under iid `Geom(p)`.  Summing over splits gives `fPair` (sign: `sliceChar` uses `e(+·)`, `charZ` uses `e(−·)`; take norms, or replace `ξ` by `3^a − ξ mod 3^a`).  Odd `a` leaves one unpaired gap whose factor has norm `≤ 1`.
4. **Reweight.**  `∏‖fPair‖ ≥ 0` depends only on `b`.  So the slice average is `≤ E_{Pascal(p)}[∏‖fPair‖] / P(slice) = pascalDamping a p ξ' / P(Bin(j,p) = a)`.  The conditioning on `j < T_{a+1}` reweights by `(1−p)^{j−T_a} ≤ 1`.
5. **Choose `p = a/j`.**  The window `j ≤ 5a`, `5a ≤ 3j` gives `p ∈ [1/5, 3/5]`.  `a` is the mode of `Bin(j, a/j)`, so `P ≥ 1/(j+1)`.  No local limit theorem is needed.
6. **Assemble.**  Apply `h` at `A' := A + 1` (or more).  `‖sliceChar‖ / #slice ≤ C (j+1) a^{−A'}`, with `a ≥ j/5`; absorb the constants.

## Rules

- **Do not change any frozen statement**: `charZ`, `fPair`, `xArg`, `pascalWeight`, `pascalDamping`, `PascalDampingDecay`, the edge, and everything in `SliceDecay.lean` (personal-c5's file; read-only).  If one is false as stated, stop, write the counterexample into the handoff, and `box stuck`.  Do not weaken it silently.
- Helpers go in `SliceSeven.lean` or a new `Conjugacy/SliceSevenAux.lean`.  Leave every other module alone.
- No `axiom`, `native_decide` or `set_option maxHeartbeats` without a justification comment.
- Commit each green checkpoint on `wip/conjugacy-slice7b` with `git-safe`, by explicit path.  Keep `HANDOFF-2026-10-25-slice7.md` current.
- Report the mathematics, not the certificate.
