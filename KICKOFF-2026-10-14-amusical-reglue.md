# KICKOFF 2026-10-14: sparse regluing, Theorem Π (amusical, fsarith)

Repo `collatz-moonshot-amusical-reglue`: close every `sorry` in `CollatzMoonshot/AmusicalReglue.lean`.
(This branch is stacked on `wip/amusical-ncentropy`; the `AmusicalNearCycleEntropy.lean` sorries
belong to another treadmill: leave that file alone.)

## Ratified, do not change

`PermFwdSurvivor`, `PermPeriodic`, `nChanged`, `bwdWeight` and the five theorem statements.  Everything
else is read-only (you may remove `private` from helpers, e.g. in `AmusicalOddRewire/Glue.lean`).
Helpers go in `CollatzMoonshot/AmusicalReglue/*.lean`.  No `native_decide`, no new axioms, no `decide`
over more than a few thousand cases.  Lean lines ≤ 100 characters.  Do **not** edit `RESEARCH-*.md`.
**Commit after every proved target.**  Order: `chernoff_duality`, `bwd_iter_affine`,
`lt_bwd_iter_iff`, then Theorem Π, then Π′.

## Paper proofs (agent "fsarith"; research §41; Ren checked every step)

1. **`chernoff_duality`.**  `(3/2)^{−(1−s)} = (2/3)(3/2)^s` and `(3/4)^{−(1−s)} = (4/3)(3/4)^s`
   (`Real.rpow_add`, `Real.rpow_neg`, positivity of the bases).  Then both sides are
   `(1/3)(3/2)^s + (2/3)(3/4)^s`.
2. **`bwd_iter_affine`.**  Write `V = amusicalNatPerm.symm`, `y_j = V^j m`.  One step:
   `3 V(y) = 2y` if `3 ∣ y`; `= 4y − 1` if `y ≡ 1`; `= 4y + 1` if `y ≡ 2 (mod 3)`
   (`V(3n) = 2n`, `V(3n+1) = 4n+1`, `V(3n+2) = 4n+3`; `amusicalNatPerm_symm_apply_cast` and
   `amusicalInv`).  With `a_i = 3^i y_i`: `a_{i+1} = 2^{c_i} a_i + 3^i e_i`, `c_i ∈ {1, 2}`,
   `|e_i| ≤ 1`.  So `E_{i+1} = 2^{c_i} E_i + 3^i e_i`, and by induction
   `|E_i| ≤ Σ_{j<i} 3^j 4^{i−1−j} < 4^i` (prove the sharper invariant `|E_i| ≤ 4^i − 3^i`:
   `4(4^i − 3^i) + 3^i = 4^{i+1} − 3^{i+1}`).  `bwdWeight m (i+1) = bwdWeight m i + c_i`.
   Checked numerically (Ren; `|E|/4^i ≤ 0.968`, and `< 3^i` fails, so the bound has teeth).
3. **`lt_bwd_iter_iff`.**  `3^i V^i m − 3^i m = (2^w − 3^i) m + E` with `|E| < 4^i < m`.  If
   `2^w > 3^i` the right side is `≥ m + E > 0`; if `2^w < 3^i` it is `≤ −m + E < 0`; `2^w = 3^i` is
   impossible for `i ≥ 1` (parity).
4. **`exists_reglue_sparseFS` (Theorem Π).**  Non-periodic points of `f` form *chains*: injective
   `ℤ`-indexed orbits (`j ↦ (f^j) x`), so each value occurs once and values tend to `∞` in both time
   directions.  (If `{PermPeriodic}` is finite, chains exist since `ℕ` is infinite.)
   * **Cuts.**  Choose a cut set `C` of chain points, unbounded in both time directions on every
     chain, sparse: at most `F X / 4` points `c` with `c < X` or `f c < X`.  (Enumerate chains by
     minimum; on chain `k` take, for each `j`, a point late in time with `c, f c ≥ H(k + j)` and one
     early in time likewise; `H` fast.)  Also a **spine** `y₁ < y₂ < ⋯` of chain points, with
     `f⁻¹ y_b`, `y_b` both cut, so `{y_b}` is a singleton piece; `y_b ≥ H'(b)` fast enough that
     `#{b : y_b < X} ≤ G X / 2` and the spine cuts fit in the `F` budget.
   * **Pieces** are the maximal finite `f`-time intervals of a chain between cuts (a cut point ends
     its piece).  They partition the chain points.  `μ(Q) = min Q`.
   * **Blocks.**  `B_b` = pieces with `y_b ≤ μ(Q) < y_{b+1}` (`B₁` also takes `μ < y₁`).  Each block
     is finite (disjoint pieces with `μ < Z` each contain a point `< Z`).  The spine piece is the
     unique piece of least minimum in `B_b`.
   * **The word.**  Each block lists its pieces in **decreasing** order of `μ`, each piece in
     `f`-time.  The bi-infinite word is `⋯ B₆ B₄ B₂ | B₁ B₃ B₅ ⋯`.  `π` = successor in the word on
     chain points, `π = f` on periodic points.
   * **(changes)** `π x ≠ f x` only if `x ∈ C`; `π⁻¹ y ≠ f⁻¹ y` only if `y ∈ f C`.  Sparse by choice.
   * **(one orbit)** every chain point occurs once in a bi-infinite word.
   * **(survivors)** A point of a non-spine piece of an odd block is followed, later in the same
     block, by a piece of smaller minimum: not a survivor.  A spine point `y_b` (`b` odd `≥ 3`) is a
     survivor (everything later lies in `B_{b'}`, `b' > b` odd, all `≥ y_{b'}`).  Every point of
     an even block is `≥ y₂ > y₁` and `y₁` comes later.  So survivors `⊆ {y_b} ∪ B₁ ∪ periodic`, the
     last two finite.
   A cleaner Lean route than building the word directly: build `π` as a *list-concatenation
   bijection* `ℤ ≃ chain points` from the block sequence; or reuse the cut-set reconnection machinery
   in `AmusicalOddRewire/Glue.lean` (`IsCutSet`, `exists_glue`) where it fits.
5. **`exists_reglue_sparseFS_amusical` (Π′).**  As Π for `f = amusicalNatPerm`, with every cut at an
   **odd** point, so `π (2m) = U (2m) = 3m`.  Odd points exist late and early on every chain:
   forward, an `E`-run from `x` lasts `v₂(x)` steps; backward, `V` increases only into odd values and
   backward values tend to `∞` (`exists_late_odd`, `exists_early_odd` in `AmusicalOddRewire`).
   Forward cuts: first odd `c` past the threshold (`U c ≥ (3c − 2)/4`, so `U c` is high too).  Spine:
   an odd chain point `c_b` and the previous odd point `c'_b`; cut both.  The spine piece
   `(U c'_b, …, c_b)` is a pure `E`-run, strictly increasing, with `≤ log₂ c_b + 1` points; its
   minimum `s_b = U c'_b` plays the role of `y_b`.  Survivors are `⊆` spine pieces `∪` finite, so
   `#FS(X) ≤ Σ_{s_b < X} (log₂ X + 1) + O(1) ≤ G X` for a fast spine.

Notes for the next lap go in `HANDOFF-amusical-reglue.md`.
