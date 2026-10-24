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
