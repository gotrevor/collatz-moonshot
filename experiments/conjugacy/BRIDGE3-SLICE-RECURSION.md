# The slice family is closed under Tao's recursion (2026-10-24, personal-c5)

This supports research note §11, the 3-adic bridge.  The missing edge there is Tao's
Prop 1.17 ⇒ 1.14 (characteristic-function decay ⇒ fine-scale mixing) for the sliced law.  Tao's
deduction runs on the recursion of his Lemma 1.12.  The slices satisfy the same recursion, one
slice at a time.

Let `μ_{n,s}` be the law of `X_n = Σ_{k≤n} 3^{k−1} 2^{−T_k}` mod `3^n` given `T_n = s`, with the
gaps a uniform composition of `s` into `n` parts.  Then

    μ_{n,s} = Σ_{g=1}^{s−n+1} w_{n,s}(g) · (x ↦ 2^{−g}(1 + 3x))_* μ_{n−1, s−g},
    w_{n,s}(g) = C(s−g−1, n−2) / C(s−1, n−1).

The proof is to condition on the first gap: `X_n = 2^{−g₁}(1 + 3X′)`, with `X′` the slice
`(n−1, s−g₁)`.  `slice_recursion.py` checks it exactly for `n ≤ 5`, `s ∈ [n, n+6]`.

**Consequence for the edge.**  Tao's argument can run on the family indexed by `(n, s)`.  The
input it then needs is per-slice characteristic-function decay.  That equals the θ-uniform
twisted decay of §11 (`twisted_charfn.py`), since slicing is Fourier inversion in `θ`.  The
binomial weights `w_{n,s}` concentrate at `g ≈ s/n`, which is a tilted geometric law.  This is
where the entropy condition of §11 enters.

**On personal-2c's question** (does the twisted 1.17 imply `TwoAdicFreqDecay`?): not directly.
`TwoAdicFreqDecay` correlates the sign with a 2-adic character of the start `r`.  The twist
`e(θT_n)` sees only the total length.  A bridge would need a two-place statement: joint mixing of
the 3-adic Syracuse value with a 2-adic phase of the start.

## Sharpened: the twist is not needed, and Tao §7 transfers (2026-10-24, later)

**Correction to "slicing is Fourier inversion in θ".**  Inverting in `θ` at Tao's `p = 1/2` loses
a factor `1/P(slice) = 2^j / C(j,a)`, which is exponential once `a/j` leaves `1/2`.  The route that
works conditions on the pair sums instead.

**The pairing argument, on slices.**  Tao proves 1.17 by conditioning on the pair sums
`b_i = a_{2i−1} + a_{2i}` and bounding `|S_χ| ≤ E_b ∏_i |f(x_i, b_i)|` (tao-collatz
`Sec7/Reduction.lean`, `cexpect_pairing`).
1. Under a uniform `a`-subset of `[1, j]`, given every pair sum, each pair is uniform over its
   `b_i − 1` splits.  That is exactly the conditional law under iid `Geom(p)` gaps, for every `p`.
   So `|slice char| ≤ E_slice[∏ |f|]`, with Tao's own `f`.
2. `∏ |f| ≥ 0` is a function of `b`, so `E_slice[∏ |f|] ≤ E_{Pascal(p)}[∏ |f|] / P(slice)`.
   Taking `p = a/j` makes `P(slice) ≍ j^{−1/2}`, a polynomial loss.
3. So `SliceCharDecay` ⇐ Tao's white-encounter bound (Prop 7.3, `renewal_white_encounters`) with
   `Pascal(p)` pair sums, `p ≤ 3/5`.  Only the law of `b` changes: `P(b = 3) = 2p²(1−p)` and the
   drift is `1/p` per step.  Heuristic for the threshold: a walk of slope `1/p ≤ log₂ 3` can stay
   inside a black triangle, so the condition should be `p < 1/log₂ 3 ≈ 0.631`.  That is unproved.
4. The same step shows the twisted 1.17 of §11 is a corollary of Tao's bound: `e(θ T_n)` is
   `b`-measurable with modulus 1, so it drops out of `E_b ∏ |f|`.  This is consistent with the
   measured twisted sup (0.145 at n=5) sitting above the untwisted value (0.129) but under the same
   envelope.

**Measured** (`slice_charfn.py`, an exact DP over positions; checked against brute-force
iterates `T^j r` for every `j ≤ 12` and every `a`, zero mismatches).
`sup_{3∤ξ} |E_slice e(ξX/3^a)|`:

| j | ρ=0.35 | ρ=0.45 | ρ=0.5 | ρ=0.55 | ρ=0.6 | ρ=0.65 | ρ=0.75 (control) |
|---|---|---|---|---|---|---|---|
| 8 | 0.085 | 0.143 | 0.143 | 0.143 | 0.373 | 0.373 | 0.612 |
| 12 | 0.026 | 0.036 | 0.051 | 0.119 | 0.119 | 0.284 | 0.514 |
| 16 | 0.016 | 0.016 | 0.031 | 0.062 | 0.127 | 0.127 | 0.436 |
| 20 | 0.0053 | 0.0078 | 0.018 | 0.043 | 0.080 | 0.150 | - |
| 24 | 0.0018 | 0.0057 | 0.0078 | 0.022 | 0.055 | - | - |
| 28 | 0.0009 | 0.0037 | 0.0066 | - | - | - | - |

Decay is roughly `j^{−2.8}` at `ρ = 1/2` over this range.  The `ρ = 0.75` control does not decay.
The sup alone does not see the entropy cutoff: Parseval only forces `sup ≥ #slice^{−1/2}`.  The
cutoff enters at §6's Cauchy–Schwarz step (`osc ≤ √(3^a Σ_high |F|²)`), as in Tao's budget
`l log 2 + … < n log 3`.

**Lean.**  `CollatzMoonshot/Conjugacy/SliceDecay.lean` states `SliceCharDecay` (window
`1/5 ≤ a/j ≤ 3/5`) and the edge `truncatedSyracMixing_of_sliceCharDecay` (proof owed).

**Bug found in `TruncatedSyracMixing`** (Bridge3.lean as of fb00e85): it quantified over every
`a ≤ 11j/20`, including `a = 0`, where `3^m ≤ ε·3^a` forces `1 ≤ ε`.  So the node was false and
the edge from it vacuous.  Fixed by adding the lower cutoff `j ≤ 4a`.  The edge to `BiasDecays`
now also needs the lower binomial tail `Σ_{a < j/4} C(j,a) = o(2^j)`.
