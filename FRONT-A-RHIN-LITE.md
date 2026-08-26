# Front A: an independent coarse Rhin re-derivation

## Objective

Prove some finite effective linear-independence measure for
`{1, log(3/2), log(4/3)}` from Rhin's six factors, rather than formalizing his optimized `7.616`
asymptotic or citing the explicit `13.3` proposition.  Any finite measure is enough for
`sep_two_three`: polynomial separation eventually dominates the exponentially weak
`2^(-k/3)` target, and the remaining finite range is decidable.

This route intentionally trades sharp constants for finite, rational certificates.

## The rationalized kernel

Use the nearby weights

```text
(w1,w2,w3,w4,w5,w6) / 1000 = (705,551,449,109,39,54) / 1000.
```

They satisfy the three exact constraints

```text
w1+w2+w3+w4+2w5+2w6       = 2000       (degree)
w2+2w3+2w4+3w5+4w6        = 2000       (v2 content after x -> 12x)
w1+w4+2w5+2w6              = 1000       (v3 content after x -> 12x).
```

Take only original indices `N = 2000t`.  The six exponents are then `2w_i t`, hence all even.
Consequences:

- the two integrands on `[2,3]` and `[3,4]` are nonnegative and not identically zero, so there is
  no cancellation/nonvanishing problem;
- the polynomial has degree exactly `2N`;
- the content balances put it in `(12,x)^N Z[x]`, which is exactly what clears the negative powers
  of the endpoints `2,3,4` after multiplying by `lcm(1,...,N)`.

## Completed, machine-checked coefficient step

`CollatzMoonshot/FrontA/RhinLite.lean` is sorry-free and proves, for the positive transform of the
six-factor polynomial at a 1000-index block scale,

```text
17^(1000t) <= [x^(1000t)] H_t(-x) <= 18^(1000t).
```

The lower bound chooses the single constant/linear contribution with selections

```text
(352,330,192,61,27,38),       sum = 1000,
```

proves binomial supermultiplicativity from Vandermonde, and then proves that this term lies below
the coefficient of the full product (including the positive quadratic terms).  The base inequality
`17^1000 <= T` is a finite `native_decide` certificate.

The upper bound evaluates the positive polynomial at the exact rational Cauchy radius `14/5`.
After clearing denominators, the only finite certificate is

```text
29^705 24^551 34^449 26^109 14072^39 14884^54
  <= 252^1000 5^891,
```

also checked by `native_decide`.  Positivity then gives the coefficient bound directly.  Thus no
central-limit theorem, saddle-point theorem, or two-sided coefficient asymptotic remains.

## Completed, machine-checked critical-point and local-interval step

Let `P(x) = product Q_i(x)^w_i`.  Although `P` has degree 2000, the numerator of the logarithmic
derivative of `P(x)/x^1000` is only degree eight:

```text
S(x) = x sum_i w_i Q_i'(x) product_(j != i) Q_j(x)
       - 1000 product_i Q_i(x)

coefficients ascending =
[-5971968000, 13269961728, -11385536256, 4171412736, -28892592,
 -519935532, 185301612, -27888891, 1615000].
```

`CollatzMoonshot/FrontA/RhinLite.lean` first proves that this factored definition equals the
displayed explicit polynomial. The exploratory script used exact rational Sturm arithmetic, but
the final Lean proof found a smaller route: `S` changes sign in each of the seven millionth
brackets

```text
[2.115103,2.115104]  [2.223243,2.223244]  [2.312512,2.312513]
[2.520895,2.520896]  [3.474818,3.474819]  [3.652359,3.652360]
[3.780897,3.780898].
```

and also changes sign on `[-3,-2]`. Thus the intermediate value theorem supplies eight distinct
real roots. Since `S` has degree exactly eight, those roots exhaust its entire real root set. This
argument is formalized in `CollatzMoonshot/FrontA/RhinLiteCritical.lean`; no Sturm theorem or
root-counting algorithm enters the trusted proof.

On each positive bracket, exact endpoint/vertex bounds for the six degree-at-most-two factors prove

```text
|P(x)| / x^1000 <= (9/40)^1000.
```

The worst certified bracket has per-index upper bound `0.221517435 < 0.225`; the total logarithmic
slack is `15.599`. `CollatzMoonshot/FrontA/RhinLiteInterval.lean` reflects rounded-up rational
factor bounds, proves all six pointwise estimates, and combines their weights with one finite
`native_decide` certificate. Its endpoint theorem is

```text
rhinLiteKernelAbs_div_pow_le:
  x in bracket_i -> |P(x)| / x^1000 <= (9/40)^1000.
```

`CollatzMoonshot/FrontA/RhinLiteMaximum.lean` completes the continuous maximum argument and
derivative factorization. It maximizes the square, transfers the maximum locally through
`sum_i w_i * log (Q_i(x)^2) - 2000*log x`, clears the six nonzero factors to `S`, applies root
exhaustion, and passes from the squared bound back to the nonnegative absolute kernel. Thus
`rhinLiteKernelAbs_div_pow_le_on_Icc` proves the target globally on `[2,4]` without differentiating
`abs` or expanding the large powers.

## What this yields when the remaining wiring is formalized

For `N=2000t`, let `B_N` be the central coefficient and `D_N=lcm(1,...,N)`.  The completed and
target estimates are

```text
17^N <= B_N <= 18^N,
0 < I_N(2,3), I_N(3,4) <= (9/40)^N,
D_N <= 4^N * exp(o(N)).
```

Hence the common integer denominator grows at most like `72^N exp(o(N))`, while both errors decay
like `(9/10)^N exp(o(N))`.  This gives a coarse but finite simultaneous linear-independence measure.
Sharp `7.616` constants are irrelevant.

The remaining Lean work is:

1. lift the completed base estimate to the even block subsequence (the exact assignment is
   `FRONT-A-RHIN-LITE-NEXT.md`);
2. instantiate polynomial-integral/LCM machinery and prove the two integer linear
   forms for `log(3/2)` and `log(4/3)`;
3. prove a coarse simultaneous-approximation criterion using the explicit lower/upper coefficient
   bands (cite the standard Q-linear independence of `1,log(3/2),log(4/3)` if convenient);
4. feed the resulting finite measure through `sep_of_linear_form_poly` and extend the finite check.

No published quantitative Rhin theorem is needed if these four steps close.

## Source correction discovered on this route

Wu 2003, Theorem 2 literally prints `gcd` both for the endpoint scale and for
`D_n = gcd(1,...,M)`.  Taken literally, the displayed integrality claim is false and `D_n` would
always be one, contradicting the stated positive exponential rate.  The proof requires common
multiples: `lcm(a_1,...,a_m)` and `lcm(1,...,M)`.  Rhin's own single-log discussion uses `ppcm`
(LCM), and the exact 2-/3-adic balances above independently confirm the `12=lcm(2,3,4)` reading.
