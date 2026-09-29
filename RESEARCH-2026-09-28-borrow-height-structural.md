# Dyadic borrowing height: a sharp sieve, not an infinite obstruction

Consider a Q rule in the rational shortcut ledger, with input labels (c,d), output labels (u,b), and `r_x=2x/(3x+1)`:

\[
r_u r_b=r_c r_d,\qquad
D=u(3(c+d)+1)-3cd,\qquad Db=(3u+1)cd.
\]

The incumbent `borrowability_descent.py` establishes that 23 and 85 cannot be introduced by **two strictly smaller odd input labels**, even though they can be borrowed with larger inputs.  The present extension asks whether dyadic labels give a parametric version of that failure.  It does not find one.  The fixed-(C) question, whether all sufficiently large 3-free odd (u) admit a Q introduction with both inputs at most (Cu), remains open.

## Exact dyadic sieve

Put (u_j=(4^j-1)/3), (M=4^j), and (A=3c+1), (B=3d+1).  The label (u_j) is 3-free exactly when (3\nmid j), since (v_3(4^j-1)=1+v_3(j)).  Direct expansion gives

\[
3D=M(A+B-1)-AB.
\]

For odd (c,d,b), the equation (Db=Mcd) forces (v_2(D)=2j).  Since (A+B-1) is odd, comparison of the two terms above proves the following **necessary and exact valuation test**:

\[
v_2(D)=2j \quad\Longleftrightarrow\quad
v_2(3c+1)+v_2(3d+1)>2j.
\]

At equality (v_2(A)+v_2(B)=2j), the two odd quotients cancel modulo 2, so (v_2(D)>2j).  Below equality the product (AB) fixes a smaller valuation.  Above equality the first term fixes valuation (2j).  Passing this test does **not** imply (b) is integral: the remaining odd part of (D) must divide (Mcd).

The natural recursive split (c=u_i, d=u_{j-i}), (0<i<j), has an especially simple exact failure:

\[
D=M(c+d),\qquad b=\frac{cd}{c+d}.
\]

Here (c,d) are odd, so (cd) is odd and (c+d) is even.  Thus this split has no integral companion for **every** (j,i), regardless of whether the smaller labels happen to be 3-free.  Example: (j=4,i=2) gives (u=85,c=d=5,D=2560,b=5/2).

## Positive controls defeat the proposed family obstruction

The extended CLI enumerates 3-free odd (c,d\le H), uses the exact valuation test, then computes the unique possible companion (b=Mcd/D) without a height bound.  It checks the Q identity with rational arithmetic.  These are finite results, not induction:

| (j) | (u_j) | Bound (H) | Result |
|---:|---:|---:|---|
| 4 | 85 | 84 | Three valuation survivors, no Q rule |
| 4 | 85 | 212 | Least input height 197: \(\{149,197\}\leftrightarrow\{85,29353\}\) |
| 5 | 341 | 340 | 37 valuation survivors, no Q rule |
| 8 | 21845 | 21844 | Rule \(\{5461,7453\}\leftrightarrow\{3683,21845\}\) |

For (j=8), **both** input labels are smaller than (u_8), indeed their maximum is (7453<0.342u_8).  This single exact rule refutes the claim that all (u_j) obstruct two-smaller-input introduction.  The (j=4) positive rule shows why a companion bound is the wrong measure: its companion is 29353, but the two reusable inputs have maximum 197, about (2.318u_4).  The existing 23 obstruction has minimum 3-free input height 49, about (2.131\cdot23).

The extension keeps the original CLI and adds `dyadic J H` and `split J I`.  `borrowability_descent.py test` delegates to external pytest, and the new tests invoke the real CLI by subprocess with hand-computed rational identities and the (j=4,i=2) split.  The installed external pytest suite is run alongside the borrowing and family-profile suites.  Each test executes its real CLI by subprocess.

## Decision for the induction branch

The dyadic valuation test is a useful *search and exclusion sieve*, and the complementary split is an infinite negative lemma for one specific recursive construction.  Neither proves a growing input-height lower bound for (u_j), much less disproves a fixed (C).  The observed (u_8) rule makes an all-(u_j) obstruction false.  A valid structural attack would need to control the odd divisor (D/4^j) across every high-valuation input pair, or exhibit a genuinely mutual borrowing block with its complete Q rules; a larger census alone cannot decide that.
