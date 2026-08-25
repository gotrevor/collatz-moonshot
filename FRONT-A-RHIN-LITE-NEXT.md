# Front A treadmill: close the Rhin-lite remainder and integer-form layer

## Read first

Read `FRONT-A-RHIN-LITE.md` and these four modules completely:

- `CollatzMoonshot/FrontA/RhinLite.lean`
- `CollatzMoonshot/FrontA/RhinLiteCritical.lean`
- `CollatzMoonshot/FrontA/RhinLiteInterval.lean`
- `CollatzMoonshot/FrontA/Legendre.lean` (only its LCM/integer-form patterns)

The coefficient estimates, root exhaustion, and all seven local interval bounds are already
proved. Do not rebuild them, introduce Sturm theory, or optimize constants.

## Primary objective

Create `CollatzMoonshot/FrontA/RhinLiteMaximum.lean` and prove a global base-block estimate,
with a theorem equivalent to

```lean
theorem rhinLiteKernelAbs_div_pow_le_on_Icc {x : ℝ}
    (hx : x ∈ Set.Icc (2 : ℝ) 4) :
    rhinLiteKernelAbs x / x ^ rhinLiteScale ≤
      (9 / 40 : ℝ) ^ rhinLiteScale
```

No `sorry`, new axiom, weakened statement, or replacement by a definition is allowed.

### Recommended proof

1. Define the signed normalized kernel

   ```text
   K(x) = Q1(x)^705 Q2(x)^551 Q3(x)^449 Q4(x)^109
          Q5(x)^39 Q6(x)^54 / x^1000.
   ```

2. Work with `K(x)^2`, not `abs K`, so differentiability at factor zeros is automatic. Use the
   extreme-value theorem on `[2,4]`. The square vanishes at `2`, `3`, and `4`, and is nonzero at a
   convenient rational point, so a maximizing point is interior and has zero derivative.
3. Prove, without expanding the large powers, that a nonzero critical point of `K` satisfies
   `rhinLiteCriticalReal.eval x = 0`. Use logarithmic differentiation or factor the derivative
   structurally with `HasDerivAt.pow`; clear only the six nonzero factors and `x`. The checked bridge
   `rhinLiteCriticalPolynomial_eq_explicit` fixes the exact degree-eight polynomial.
4. Apply `rhinLiteCriticalRoot_exhaustive_positive` and finish with
   `rhinLiteKernelAbs_div_pow_le`.
5. Relate `|K x|` to `rhinLiteKernelAbs x / x^1000` for `x > 0`, and pass from the squared bound to
   the nonnegative bound.

Add small reusable calculus/factorization lemmas when they make the proof clearer. Keep large
finite arithmetic in the existing `native_decide` certificates.

## Second objective: lift to the actual even subsequence

In the same module, or a small follow-on module, define the original signed polynomial at parameter
`N = 2000t`, whose six exponents are `2*w_i*t`. Prove:

- its degree is exactly `2N`;
- its central coefficient is the coefficient already bounded in `RhinLite.lean` at parameter
  `2t`, hence lies between `17^N` and `18^N`;
- both normalized integrands on `[2,3]` and `[3,4]` are nonnegative and nonzero for `t > 0`;
- pointwise they are bounded by `(9/40)^N`, by raising the base theorem to `2t`;
- consequently each interval integral is positive and at most its interval length times
  `(9/40)^N` (the lengths are one).

Use exact identities; do not hide scaling mismatches behind new assumptions.

## Third objective if lap budget remains: exact integer log forms

Define the integer polynomial and prove the elementary monomial integral identity needed to expand

```text
∫_a^b H_N(x) / x^(N+1) dx,   (a,b)=(2,3) or (3,4).
```

The `x^N` term contributes the common central coefficient times `log(b/a)`; every other term is
rational with denominator dividing `|j-N|` and endpoint powers. Use `Nat.lcmUpto N` and the exact
2-/3-adic content balances of the denominator-1000 weights to clear these denominators. Land
theorem-grade statements giving integers `A₁,A₂,B` and an explicit positive integer clearing
factor `D_N` such that the two cleared integrals are

```text
A₁ + B * log(3/2),
A₂ + B * log(4/3),
```

with the same `B`, together with bounds obtained from the previous objective. Do not begin the
final simultaneous-approximation criterion until these identities are green.

## Acceptance gate

- The primary global `[2,4]` theorem is mandatory and sorry-free.
- Import every landed module in `CollatzMoonshot.lean`.
- `lake build` passes.
- `bash scripts/check-proof-debt.sh` still reports exactly the one pre-existing
  `PowSeparation.lean` sorry.
- Add the principal new theorem(s) to `scripts/AxiomAudit.lean`; no `sorryAx` or new math axiom may
  appear in their ledgers. `native_decide` artifacts and the ordinary trust base are allowed.
- Update `FRONT-A-RHIN-LITE.md`, `PENDING_WORK.md`, `STATUS.md`, and `DIRECTION.md` to say exactly what
  landed.
- Commit one coherent green checkpoint. Do not push.

If the global maximum proof exposes a genuinely false statement or a scaling error, stop and record
the exact counterexample/signpost rather than weakening the target.
