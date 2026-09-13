# The Q=2, L=6 prefix-admission relaxation has unbounded length

Date: 2026-09-13. **The bounded-length statement in the CURRENT DIRECTIVE is
false.** This is an all-parameter mathematical proof with an exact rational
certificate, not a new Lean theorem or an extrapolation from finite survivors.
Reproduce with `python3 experiments/prefix_admission_obstruction.py`; optional
`--json PATH` exports the certificate and every finite probe separately.

## Construction and relation to the old family

Keep X=TF, Y=TTF and A=XY from `short_run_obstruction.py`. Put

```
H = X Y^17,    C = A^2,    E = A^12 H,
w_j = C^j E = (XY)^(2j+12) X Y^17,       j >= 0.
k = 2j+12,
b = 2k+18 = 4j+42,
a = 3k+35 = 6j+71,
m = 5k+53 = 10j+113.
```

Here H names a word, not a head height. All maximal odd runs have length 1
or 2 and all even gaps have length 1, including the terminal gap. Thus Q=2
and m>=6 hold without any boundary merges. This is precisely the old family
`A^k XYY` with **15 extra Y blocks appended**, restricted to even k>=12.
The new content is its prefix-admission margin, not another positivity family.

**Primitivity in the literal FrontB.Powers sense.** Any proper Boolean-word
power exponent d>=2 would divide both a and m. But 5a-3m=16, while a and m
are odd. Hence d would be an odd divisor of 16, which forces d=1. This
argument covers arbitrary word roots, including those not aligned with runs
or macros. Since m=10j+113, lengths are unbounded. There are no exceptional
j>=0; we make no claim about the omitted k outside this parameterization.

## Rational cycle and all internal head inequalities

Use exactly the directive's coordinate z=x+1 and chronological composition:

```
f_(q,e)(z) = (3^q / 2^(q+e))*z + 1 - 2^(-e),
f_X(z) = 3z/4 + 1/2,     f_Y(z) = 9z/8 + 1/2,
f_A(z) = 27z/32 + 17/16, f_A(34/5) = 34/5.
```

The macros C and E preserve the common interval I=[34/5,225]. Their exact
endpoint certificate is:

| Macro | Slope | Lower endpoint image | Upper endpoint image |
|---|---|---|---|
| C=A^2 | 729/1024 | 34/5 | 166031/1024 |
| E=A^12 H | 3^71/2^113 | 47216795331893147/703687441776640 | 225 - 1171081197571096040226910222706003/2^113 |

Both slopes lie strictly between 0 and 1, and both displayed images are in
I, by exact integer comparisons checked in the script. Every internal prefix
map has positive slope. At input 34/5 each A has head slacks 24/5 and 8/5
and returns to 34/5. The final H starts with X, giving first slack 24/5
and next head 28/5; its first Y therefore has slack 8/5. All subsequent
Y heads strictly increase, since f_Y(z)-z=z/8+1/2>0 for positive z.
Consequently every internal odd-run head has z-2^q>=8/5 for every macro
input in I. Only macro boundaries must stay in I; internal heads need not.

For every j, induction shows f_E composed with f_C^j maps I into I. Its
slope is

```
R_j = (3^71/2^113)*(729/1024)^j in (0,3^71/2^113] < 1.
```

Write that map as R_j*z+S_j. Endpoint invariance implies
`(1-R_j)*(34/5) <= S_j <= (1-R_j)*225`, so its unique rational fixed
point z0=S_j/(1-R_j) is in I. Starting at z0, macro invariance and the
internal-prefix inequalities prove the required strict head inequalities
at every run. The final head returns to z0. This establishes every rational
cycle hypothesis of S2 for **all j**, using neither integer rotation nor a
global length/run bound.

## The new arithmetic: a uniform strict six-letter margin

Every w_j starts with TFTTFT, including j=0 because E starts with A^12.
Its six-letter numerator is 119 and odd count is 4. Hence

```
81*n+119 = 0 mod 64  iff  n = 57 mod 64;
r_6 = c_6 = 57.
```

In the fixed cycle, the input to the final E is in I. Monotonicity of E
therefore gives the stronger entry bound

```
z0 >= f_E(34/5) = 47216795331893147/703687441776640 > 58,
N/D - c_6 = z0-58 >= 6402923708848027/703687441776640 > 0.
```

Thus P_6 holds strictly for every j. The threshold N/D is between
approximately 66.099 and 224; these decimals are explanatory only.

There is also a direct integer certificate independent of the interval
margin. Let N_H=305184819419292989. Numerator append composition gives
`N_(A^k)=29*(32^k-27^k)/5` and `N=3^35*N_(A^k)+N_H*32^k`. Therefore

```
D = 2^53*32^k - 3^35*27^k > 0,
5*N = 2976838904967456448*32^k - 29*3^35*27^k,
5*(N-57*D) = 409787117366273728*32^k + 256*3^35*27^k > 0.
```

The numerator formula is integral because 32^k-27^k is divisible by 5.
The positivity of both coefficients in the last line proves the strict
filter margin for every k in our family. The script checks these formulas
against `numer_fast`, the existing integer cascade, and every cyclic head
identity; it does not replace the cascade with a second implementation.

For any proposed M, choose j with 10j+113>M. Then w_j is primitive, is in
S2, and satisfies P_6. This proves the negation of the displayed boundedness
statement with exactly Q=2 and L=6.

## Full admission remains a separate computation

For each finite probe compute

```
c_m = [-N*(3^a)^(-1)] mod 2^m,
full_margin = N-D*c_m.
```

The representative already exceeds 2 because it is 57 modulo 64. These
finite canonical starts are checked by their actual parity traces and by
`full_margin = 2^m*(iterate(c_m,m)-c_m)`. Independent bit lifting agrees for
j=0,1,2. All 36 tested j=0..32,64,128,256 have negative full margins.
**That is a finite observation, not an all-j full-rejection theorem.**
No full-admission conclusion is needed for the counterfamily certificate.

For example, j=0 has:

```
b=42, a=71, m=113,
N=642857412070573325457371070618206477,
D=2875127202089930453114276700182645,
c_6=57,
c_m=6994710001586550298511533155758905,
N-D*c_6=478975161551447289629857298707795712,
N-D*c_m=-20110680996291991360437370651614969804981345712360860261176466997248.
```

The script's optional JSON reports q,e,b,a,m,R, every z and head slack,
N,D,c_6,c_m, both margins and the primitivity witness separately for every
probe. It also retains 99 old-family run-head rotation controls at k=0..8;
all fail P_6. The initial search through macros with at most four blocks
finds 18 individually positive subcritical macros and no pair passing its
common-interval/lower-margin sufficient criterion. This search failure is
not a nonexistence proof. The fixed longer defect above settles the question,
so no further construction search is needed.

## Costume check and stopping scope

This is a padding of the known rational family. Its **new all-parameter
arithmetic certificate** shows that the fixed six-bit necessary filter does
not bound lengths, even for primitive Q=2 terminal-even words. P_6 checks
only the given entry prefix. It does not realize the remaining m-6 letters,
test all rotations, or turn the rational cycle into an integer cycle.

There is no Collatz counterexample, no refutation of restricted finiteness,
no result on odd-start versus unrestricted finiteness, and no claim about
arbitrary L. Full canonical admission is not assumed, and no global run or
length bound enters the argument. No literature-novelty claim is made.
The original 320 census controls and 2305/2313 remainders 7207/1375 with
opposite admission are preserved and rerun unchanged. This does not repeat
the complete census or extend its finite scope.

The assigned question is answered. Stop for altitude; do not increase L,
start a full-admission campaign, or formalize the already-settled positivity
certificate as unauthorized stretch work.
