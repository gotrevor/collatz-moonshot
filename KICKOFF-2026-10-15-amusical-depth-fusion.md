# KICKOFF 2026-10-15: finite-depth fusion M1 (research §55)

Repo `collatz-moonshot-amusical-round2` (branch `wip/amusical-depth-fusion`): close the `sorry` in
`CollatzMoonshot/AmusicalDepthFusion.lean`.

## Ratified, do not change

`DisagreeAtDepth`, `maxDepth` and the statement of `exists_depthFusion`.  No `native_decide`, no
new axioms.  Lean lines ≤ 100 characters.  Do **not** edit `RESEARCH-*.md`.  Commit after each proved
lemma.  Notes as you go in `HANDOFF-amusical-depth-fusion.md`.  Helper lemmas welcome (above use).

## Paper proof (Ren)

Write `σ = amusicalNatPerm`, `D* = maxDepth D`.  Get `τ` from `exists_oddRewire F hF`
(`AmusicalOddRewire.lean`) for a budget `F` chosen below; its first three conjuncts are the first
three of the goal.  Its fourth gives `#{c < N : τ c ≠ σ c} ≤ F N` (stated with the `ℤ` cast against
`amusical`; `amusicalNatPerm_apply_cast` converts).

1. **Disagreement lives on a change point of the segment.**  If `DisagreeAtDepth τ d n`, there is
   `i : ℤ` with `|i| ≤ d` such that `c := (σ ^ i) n` satisfies `τ c ≠ σ c`.
   * Forward (`j ≥ 1`): take the least `t < j` with `τ ((σ^t) n) ≠ σ ((σ^t) n)`; before it
     `(τ^t) n = (σ^t) n` by induction.  `i = t`, `0 ≤ t ≤ d − 1`.
   * Backward (`j = −k`, `k ≥ 1`): take the least `t < k` with `τ⁻¹ y ≠ σ⁻¹ y` for
     `y = (σ^{-t}) n`.  Then `c := σ⁻¹ y = (σ^{-(t+1)}) n` has `σ c = y` and `τ c ≠ y`
     (otherwise `τ⁻¹ y = c = σ⁻¹ y`).  `i = −(t+1)`, `−d ≤ i ≤ −1`.
2. **Counting.**  Put `B X := 1 + max {(σ ^ i) n : n < X, |i| ≤ D* X}` (a finite max; e.g. a
   `Finset.sup` over `range X ×ˢ Icc (−D*) D*`).  For `n < X` disagreeing at depth `D n ≤ D* X`, step
   1 gives `(c, i)` with `c < B X`, `τ c ≠ σ c`, `|i| ≤ D* X`, and `n = (σ ^ (−i)) c`.  So
   `n ↦ (c, i)` is injective and
   `#{n < X : disagree} ≤ (2 D* X + 1) · #{c < B X : τ c ≠ σ c} ≤ (2 D* X + 1) · F (B X)`.
3. **Choice of `F`.**  Need `F → ∞` and, for all large `X`, `(2 D* X + 1) · F (B X) ≤ G X`.
   Let `q X := G X / (2 D* X + 1)` (ℕ division); `hG` with `C = 2k + 2` gives
   `∀ k, ∀ᶠ X, k ≤ q X`, i.e. `q → ∞`.  Set
   `F N := ⨅ over X with B X ≥ N` of `q X` — concretely, since `B` is monotone and unbounded
   (`B X ≥ X`, as `n` itself is a segment value with `i = 0`), use
   `F N := min {q X | X ≥ X₀ N}` where `X₀ N` is the least `X` with `B X ≥ N`; or any equivalent.
   A cleaner option: let `r X := inf_{Y ≥ X} q Y` (monotone, tends to ∞ because `q → ∞`) and
   `F N := r (X₀ N)` where `X₀ N := least X with N ≤ B X`, so `F (B X) = r (X₀ (B X)) ≤ r X ≤ q X`
   — careful, need `X₀ (B X) ≤ X`, true by minimality.  `F → ∞` since `X₀ N → ∞` (as `B` is finite
   valued at each `X`) and `r → ∞`.  The `∀ᶠ X` in the goal absorbs small `X`.

Any cleaner route is fine as long as the ratified statement is unchanged.
