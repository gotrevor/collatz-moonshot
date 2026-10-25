# SliceCharDecay ⇒ BiasDecays via the Fourier expansion of least-residue parity 🎯

**Objective:** make `CollatzMoonshot/Conjugacy/SliceFourier.lean` sorry-free.  The headline
`biasDecays_of_sliceCharDecay (h : SliceCharDecay) : BiasDecays` must be axiom-clean
(`[propext, Classical.choice, Quot.sound]`).

**Frozen:** the statement of `biasDecays_of_sliceCharDecay`; every definition and statement in
`Ladder.lean`, `Bridge3.lean`, `SliceDecay.lean` (`BiasDecays`, `levelSet`, `levelSign`, `sliceChar`,
`SliceCharDecay`, `outOddSet`, ...).  In `Bridge3.lean` you MAY delete the word `private` on helpers
(`sum_levelSet_card`, `sum_out_levelSet_card`, `abs_levelSign_le_card`, `outOddSet_ratio_le`, ...) and
nothing else.  **Do not edit** `SliceSeven.lean`, `Fourier*.lean`, or any §12/§13 file (another
session owns them); importing them is fine.  Helpers go in `SliceFourier.lean` above the headline or
in a new `SliceFourierAux.lean`.  The suggested helper statements below may be changed if they are
false or awkward; they are a plan, not a contract.  No `native_decide`, no new `axiom`.
**Commit locally; do not push** (the operator pushes and opens the PR).

## Reuse
- `bias_eq_sum_levelSign`, and the slice split in `abs_bias_le_of_levelMixing` /
  `biasDecays_of_truncatedSyracMixing` (Bridge3.lean).  Copy that structure: slices with
  `j ≤ 4a ∧ a ≤ 11j/20` are bounded by the new per-slice estimate, the rest by `outOddSet`
  (`outOddSet_ratio_le`: tail ≤ 100·2^j/j).
- `card_levelSet_eq_choose`, `sliceChar_eq_subsetChar`, `tstep_iterate_lt_three_pow`, `charZ` (SliceSeven).
- `tstep_iterate_block` (FrontA/OrbitPacking): `T^m (s + q·2^m) = T^m s + q·3^{ones(traceWord s m)}`;
  `oddCount_add_mul_two_pow` (Bands.lean).

## The proof (all identities checked numerically by the operator)

Write `M = 3^a`, `e(x) = exp(2πix)`.

1. **Fourier identity.**  Define `gHat a ξ = (1/M) Σ_{y<M} (−1)^y e(−ξy/M)`.  For `r ∈ levelSet j a`,
   `T^j r < M` (`tstep_iterate_lt_three_pow`), so by orthogonality of characters mod `M`:
   `(levelSign j a : ℂ) = Σ_{ξ<M} gHat a ξ · sliceChar j a ξ`.
   (Degenerate `a = 0`: `M = 1`, `gHat = 1`, `sliceChar j 0 0 = 1 = levelSign j 0`.)
2. **Weights.**  `M` odd, so `gHat a ξ = 2/(M(1 + e(−ξ/M)))` and `‖gHat a ξ‖ = 1/(M|cos(πξ/M)|) ≤
   1/|2ξ − M|` (use `|cos(πx)| = |sin(π(½−x))| ≥ 2|½−x|`).  Hence
   - `Σ_{ξ<M} ‖gHat a ξ‖ ≤ 4(a+1)` (odd harmonic sum ≤ 1 + ½ ln M);
   - `Σ_{ξ<M, ξ≠0, 3^{K} ∣ ξ} ‖gHat a ξ‖ ≤ 3^{−K}·4(a+1)` (substitute `ξ = 3^K u`, `2ξ − M = 3^K(2u − 3^{a−K})`).
   - The `ξ = 0` term is `card/M`.
3. **Pascal recursion (checked for all j ≤ 9, all a, ξ including 0).**
   `sliceChar (j+1) (a+1) (3*ξ) = sliceChar j (a+1) (3*ξ) + sliceChar j a ξ`.
   Proof: split `r < 2^{j+1}` by parity.  Even `r = 2q`: `T r = q`, same odd count, gives the first
   term.  Odd `r = 2q+1`: `T r = 3q+2`; write `3q+2 = x + c·2^j` with `x = (3q+2) % 2^j`; `q ↦ x` is a
   bijection of `[0,2^j)` (3 is a unit mod 2^j); `T^j(3q+2) = T^j x + c·3^a` (`tstep_iterate_block`)
   and `e(3ξ·c·3^a/3^{a+1}) = e(ξc) = 1`.  Gives the second term.
4. **Sub-slice decomposition (checked j ≤ 12, 1 ≤ k < a).**  For `1 ≤ k ≤ a` (or `k < a`):
   `sliceChar j a (3^k * u) = Σ_{s ∈ Finset.Icc 1 j} (s−1).choose (k−1) · sliceChar (j−s) (a−k) u`.
   ⚠️ Sum over `Icc 1 j`, NOT `range (j+1)`: with ℕ subtraction the `s = 0` term is
   `C(0, k−1) = 1` at `k = 1`, a spurious term.  Proof: induction (on `k`, then `j`) from step 3 and
   Pascal's rule for `choose`.  Interpretation: `s` = the time just after the `k`-th odd step.
   The weights sum to `C(j,a)`: `Σ_s C(s−1,k−1)·C(j−s,a−k) = C(j,a)` (same induction with `ξ = 0`,
   or Vandermonde).
5. **Good and bad sub-slices.**  `SliceCharDecay` applies to `(j−s, a−k, u)` when `3 ∤ u`,
   `1 ≤ j−s`, `j−s ≤ 5(a−k)`, `5(a−k) ≤ 3(j−s)`.  For a slice in Bridge3's window
   (`j ≤ 4a`, `a ≤ 11j/20`) and `4k ≤ a`, the lower condition is automatic (`j−s ≤ j−k ≤ 4a−k ≤
   5(a−k)`), and the other two hold whenever `s ≤ m := j/12` (as `3j − 5a ≥ j/4`) and `j` is large.
   On good `s`, `j−s ≥ j/3` (large `j`), so `‖sliceChar‖ ≤ C·(j/3)^{−A}·C(j−s,a−k)`.
6. **NAMED concentration sub-lemma: `subslice_tail_le`** — the bad mass is tiny.
   `Σ_{s ∈ Icc (m+1) j} C(s−1,k−1)·C(j−s,a−k)` counts the `a`-subsets of `[1,j]` whose `k`-th
   element exceeds `m`, i.e. with fewer than `k` elements in `[1,m]`, so it is
   `Σ_{i<k} C(m,i)·C(j−m,a−i)`, the low terms of the Vandermonde sum
   `C(j,a) = Σ_i C(m,i)·C(j−m,a−i)`.  The consecutive-term ratio is
   `t_{i+1}/t_i = (m−i)(a−i)/((i+1)(j−m−a+i+1)) ≥ 2` for `i ≤ i₀ := j/1000` (as `a ≥ j/4`, `m = j/12`,
   and `j` large).  So for `k ≤ i₀`: bad mass `≤ k·2^{−(i₀−k)}·C(j,a)`.  Any super-polynomial bound
   `≤ ε/(a+1)·C(j,a)` (eventually in `j`, uniformly for `k ≤ K(j)`) suffices; pick the version that is
   easiest to prove.
7. **Per-slice bound.**  Take `A = 2` (from `h 2`), and `K = Nat.log 3 (j^2) + 1` (so `3^K > j²` and
   `K ≤ 2·log₃ j + 1 ≤ j/1000` eventually).  Split `ξ < M` by `ξ = 0`, `v₃(ξ) = k ≤ K`, and
   `3^{K+1} ∣ ξ, ξ ≠ 0` (trivial bound `‖sliceChar‖ ≤ card`).  Get
   `|levelSign j a| ≤ card·[3^{−a} + 4(a+1)·(C·(j/3)^{−2} + bad) + 3^{−K−1}·4(a+1)]`,
   and the bracket → 0 uniformly over the window, since `a ≤ j`.  (Note `a ≥ j/4 → ∞`, so `4k ≤ a`.)
   Suggested statement: `∀ ε > 0, ∀ᶠ j in atTop, ∀ a, j ≤ 4*a → a ≤ 11*j/20 →
   |(levelSign j a : ℝ)| ≤ ε * (levelSet j a).card`.
8. **Assemble** exactly as `biasDecays_of_truncatedSyracMixing`, with step 7 replacing `hslice`.

## Order of attack
3 → 4 (pure combinatorics, checkable at small values by `decide` sanity lemmas if useful) → 1 → 2 →
8 with 7 as a sorry'd lemma → 6 → 7.  Commit each green lemma.
