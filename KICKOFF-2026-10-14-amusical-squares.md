# KICKOFF 2026-10-14: square visits, prefix roots, AUT core (amusical, Codex ideation lap)

Repo `collatz-moonshot-amusical-squares`: close every `sorry` in `CollatzMoonshot/AmusicalSquares.lean`.
(Stacked on `wip/amusical-t1arith`; leave other files alone.)

## Ratified, do not change

`SquareReturnConfinement` (an OPEN hypothesis `Prop`: never prove or assume it outside a theorem's
hypotheses), `wordWeight`, `branchSign`, `prefixRoot`, and the four theorem statements.  Helpers go in
`CollatzMoonshot/AmusicalSquares/*.lean`.  No `native_decide`, no new axioms.  Lean lines ≤ 100
characters.  Do **not** edit `RESEARCH-*.md`.  **Commit after every proved target.**  Work order:
cylinder, kernel, SQG1, SRC ⇒ (a).  Write notes to disk as you go (never one giant response).

## Paper proofs (research §44; Ren checked)

1. **`amusicalInv_iterate_cylinder`.**  Induction on `k`.  `V = amusicalInv` is affine on residues mod
   3: `V(3m) = 2m`, `V(3m+1) = 4m+1`, `V(3m+2) = 4m+3`.  For `3^{k+1} n + r` with `r = 3q + ρ`,
   `0 ≤ ρ < 3`: `V(3^{k+1} n + r) = c (3^k n + q) + v_ρ` (`c ∈ {2, 4}`, `v_ρ ∈ {0, 1, 3}`), which is
   `3^k (c n) + r'` with `r' = c q + v_ρ`; reduce `r'` mod `3^k` (`r' = 3^k j + r''`) and apply the
   induction hypothesis at `n' = c n + j`.  Weights add (`1` or `2` per step) so `k ≤ a ≤ 2k`.  For
   `0 ≤ s < 2^a`: `s = V^k(r) ≥ 0` (`amusicalInv_nonneg`), and at `n = −1`,
   `V^k(r − 3^k) = s − 2^a < 0` because `V` maps negatives to negatives (`amusicalInv (−m) = −amusicalInv m`
   or `amusicalInv_neg`-style; prove from `amusical_neg` if missing).  Checked numerically (Ren, all
   `k ≤ 7`, 0 violations).
2. **`invariant_kernel_three_pow`.**  `f ∘ U^m = f` gives `f ∘ V^m = f` (apply at `V^m x`), so
   `f = f ∘ V^{mk}`.  Apply 1 with `k := m k`, `r`.
3. **`prefixRoot_eq_iff`.**  `prefixRoot w j − prefixRoot w i = −Σ_{i ≤ h < j} e_h 2^{a_h}/3^{h+1}`.
   (⇐) all `e_h = 0`.  (⇒) contrapositive: let `h*` be the largest `h ∈ [i, j)` with `e_h ≠ 0`.
   Multiply by `3^{h*+1}`: the `h*` term is `±2^{a_{h*}}`, prime to 3; every other nonzero term has
   `h < h*` and becomes `e_h 2^{a_h} 3^{h* − h}`, divisible by 3.  So the sum is `≢ 0 (mod 3)` as an
   integer, hence nonzero.  (Work with the integer `3^{j} × difference`, `padicValRat`, or `Int.emod`.)
   Checked by astra on all 9 840 words of length ≤ 8.
4. **`infinitelyManyOrbits_of_squareReturnConfinement`.**  By contradiction: finitely many orbits of
   `ℤ_{≥0}`.  For `H` large, the `H + 1` squares `q², q ≤ H`, lie on these orbits.  A finite orbit has
   boundedly many points.  On an infinite orbit (bi-infinite, injective, `amusicalPerm` powers), the
   square visits with root `≤ H` form a finite set of times `τ₁ < ⋯ < τ_k`.  Group times by `E`-only
   block (maximal runs of times joined by even inputs).  (i) If the visits meet `≥ 3` blocks: the
   earliest `τ₁`, the latest `τ_k` and a visit in a third block between them satisfy SRC's hypotheses
   (`x = U^{τ₁}`, distinctness from injectivity, an odd input between distinct blocks), so
   `τ_k − τ₁ ≤ C log(2+H)` and `k ≤ C log(2+H) + 1`.  (ii) Otherwise `≤ 2` blocks; inside one block the
   values are `y, 3y/2, 9y/4, …`, so at most `log_{3/2}(H²) + 1` of them are `≤ H²`.  So the orbits
   cover `O(log H)` squares while `H + 1` exist: contradiction for large `H`.

Notes for the next lap go in `HANDOFF-amusical-squares.md`.
