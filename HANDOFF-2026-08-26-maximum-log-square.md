# HANDOFF 2026-08-26 — Rhin-lite maximum: log-square route isolated

- **Primary gate:** `sorry-free:CollatzMoonshot/FrontA/RhinLiteMaximum.lean` remains open; the file
  is intentionally not landed with proof debt.
- **Tree on entry:** clean, `main` ahead of `origin/main` by one commit.

## Concrete advance

Tested the prescribed squared-kernel maximum route against Lean 4.33 and narrowed the calculus
bridge to a smaller formulation that avoids differentiating either `abs` or the six huge powers.
Define

```text
L(x) = sum_i w_i log(Q_i(x)^2) - 2*1000*log(x).
```

At a nonzero interior maximizer of
`(Q1^705*Q2^551*Q3^449*Q4^109*Q5^39*Q6^54/x^1000)^2`, `L` has a local maximum. Its derivative is

```text
2 * (705/Q1 + 551/Q2 + 449/Q3 + 109*5/Q4
     + 39*(34*x-102)/Q5 + 54*(38*x-108)/Q6 - 1000/x).
```

Clearing the six nonzero factors and `x` is exactly the factored polynomial
`rhinLiteCriticalPolynomial`; the existing checked equality to `rhinLiteCriticalExplicit` then
feeds `rhinLiteCriticalRoot_exhaustive_positive`. This is smaller than structurally expanding the
derivative of the 2000-degree numerator and automatically handles every factor sign.

Lean experiments confirmed:

- continuity of the square on `[2,4]` works via `ContinuousOn.div` with positivity of `x` supplied
  explicitly (global `fun_prop` cannot infer the restricted-domain nonvanishing denominator);
- endpoint squares at `2` and `4` close by `norm_num` after unfolding weights;
- the square at `5/2` is strictly positive by `sq_pos_iff` and `norm_num`;
- `HasDerivAt.log (HasDerivAt.pow ... 2)` is the right primitive for each summand. The remaining
  elaboration issue is only normalizing pointwise function powers (`Pi.pow_apply`) and clearing the
  already available factor-nonzero hypotheses.

## Exact next attack

1. Land `rhinLiteKernel`, `rhinLiteKernelSq`, and `rhinLiteLogSq`.
2. Prove six small `HasDerivAt` lemmas separately. In each `convert ... using 1`, simplify with
   `Pi.pow_apply`, `id_eq`, `pow_one`, `one_mul`; use `funext; congr 1; ring` for function equality
   and `field_simp [hi]; ring` for the derivative equality.
3. Combine them additively and prove the cleared derivative equals
   `rhinLiteCriticalReal.eval x` using
   `rhinLiteCriticalPolynomial_eq_explicit`, evaluation/map simp, then `field_simp; ring`.
4. Obtain a maximizer from `isCompact_Icc.exists_isMaxOn`; compare against `5/2` to make it nonzero
   and against the zero endpoints to make it interior. On a small neighborhood where all factors
   and `x` remain nonzero, use `Real.exp_lt_exp` and the identity
   `exp (rhinLiteLogSq y) = rhinLiteKernelSq y` to transfer the maximum to `L`.
5. Apply `IsLocalMax.deriv_eq_zero`, root exhaustion, the existing local interval estimate, and
   square-root/nonnegativity arithmetic to bound the original arbitrary `x` by the maximizer.

## Verification

- `lake env lean CollatzMoonshot/FrontA/RhinLiteMaximum.lean` was repeatedly run on the scratch
  implementation. The stable foundational pieces above kernel-checked; the unlanded scratch still
  had the described derivative-normalization goals and the final compactness proof holes.
- No `sorry`, axiom, or incomplete source file was retained.

## Current blocker

No external blocker. The remaining work is hard-but-routine Lean calculus wiring, so this is a
`progress` checkpoint, not `box stuck`.
