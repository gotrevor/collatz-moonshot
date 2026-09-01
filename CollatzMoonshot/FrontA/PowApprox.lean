/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.Basic

/-!
# Approximating powers of three from above by powers of two

One statement, isolated here because it is the entire non-elementary content of the unbounded
half of Rozier--Terracol 2026, Theorem 3.2 (`Assumed/Paradoxical.lean`):

> for every `M` and `N` there are `A > M` and `s` with `3 ^ A < 2 ^ s` and
> `(2 ^ s - 3 ^ A) * N ≤ 3 ^ A`.

In words: `2 ^ s` approximates `3 ^ A` **from above** to arbitrary *relative* precision `1/N`,
with `A` arbitrarily large.  This is exactly RT's "infinitely many left approximations
`3^a / 2^b < 1` of `1`", and it is classical: it says the fractional parts of `A · log₂ 3`
come arbitrarily close to `1`, which follows from the irrationality of `log₂ 3` (density of
`{A · log₂ 3}` in `[0,1]`; Dirichlet approximation plus a sign/power adjustment).

It is *much* weaker than the separation statement `FrontA.sep_two_three` already proved in this
repository — that one bounds `|2^m - 3^k|` from **below**, this one needs a matching family of
**good** approximations — so it is not obtainable from the Rhin-lite tower and gets its own node.

## Status

Disclosed `sorry`.  Attack plan (`PENDING_WORK.md`): mathlib's Dirichlet approximation
(`Real.exists_int_int_abs_mul_sub_le`) applied to `ξ = log₂ 3` gives `0 < q ≤ Q` and `p` with
`|q ξ - p| ≤ 1/(Q+1)`, i.e. `2 ^ p / 3 ^ q` within a factor `2 ^ (1/(Q+1))` of `1`.  Since `ξ` is
irrational the ratio is never `1`, so exactly one of two branches applies:
* `3 ^ q < 2 ^ p` — already the right side; raise to the power `u = ⌈(M+1)/q⌉` to push `A = u q`
  past `M`, which costs a factor `(1 + η) ^ u` and is absorbed by taking `Q` large.
* `2 ^ p < 3 ^ q` — take `u` maximal with `(3 ^ q / 2 ^ p) ^ u < 2`; then
  `2 ^ (u p + 1) / 3 ^ (u q)` lies in `(1, 3 ^ q / 2 ^ p]`, and `u` is automatically large.
-/

namespace CollatzMoonshot.FrontA

/-- **Powers of two approximate powers of three from above, to arbitrary relative precision,
infinitely often.**  For all `M N`, there are `A > M` and `s` with `3 ^ A < 2 ^ s` and
`(2 ^ s - 3 ^ A) * N ≤ 3 ^ A`.

Classical (density of `{A · log₂ 3}` mod `1`); disclosed here as the single open node behind the
unbounded half of Rozier--Terracol Theorem 3.2.  See the module docstring for the attack plan. -/
theorem two_pow_approx_three_pow_from_above (M N : ℕ) :
    ∃ A s : ℕ, M < A ∧ 3 ^ A < 2 ^ s ∧ (2 ^ s - 3 ^ A) * N ≤ 3 ^ A := by
  sorry

end CollatzMoonshot.FrontA
