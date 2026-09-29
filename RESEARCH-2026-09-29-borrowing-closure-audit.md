# Borrowing closure audit: the dyadic obstruction misses the needed inputs

The two symbolic rules in [the borrowing checkpoint](/Users/gotrevor/src/collatz-moonshot/RESEARCH-2026-09-28-nn-borrow-checkpoint.md) introduce auxiliary labels from smaller inputs $x,z$.  Their units were sought in the finite U2/U8/U13+Q palette, but that palette is a **self-imposed experimental restriction**, not a supply prerequisite for the 3-free catalytic route.  Applegate–Lagarias already implies that every finite 3-free catalyst is contained in some value-one word of arbitrary semigroup generators.  This audit records that route correction, while checking whether the earlier dyadic failure family intersects the four $x/z$ progressions.  It does not.

## Exact exclusion of the candidate dyadic obstruction

Let $u_j=(4^j-1)/3$, $j\ge1$.  The earlier study proves that the complementary split $u_i,u_{j-i}$ never has an integral Q companion, but the whole $u_j$ family is not obstructed: $\{5461,7453\}\leftrightarrow\{3683,21845\}$ introduces $u_8=21845$ from smaller inputs.  More decisively for the current recursion, $u_j$ cannot equal any required input in the two known supply subclasses:

| Required input | Fixed residue | Dyadic residues | Conclusion |
|---|---|---|---|
| $x_1(t)=3349+124032t$ | $21\pmod{128}$ | $u_1,u_2,u_3=1,5,21$; $u_j\equiv85\pmod{128}$ for $j\ge4$ | Only $j=3$ matches the residue, but $u_3=21<x_1(t)$ |
| $z_1(t)=785+29070t$ | $3\pmod{17}$ | $u_j\pmod{17}$ cycles $1,5,4,0$ | No match |
| $x_2(t)=3005+151680t$ | $61\pmod{128}$ | $1,5,21,85$ as above | No match |
| $z_2(t)=5635+284400t$ | $3\pmod{16}$ | $u_1=1$, and $u_j\equiv5\pmod{16}$ for $j\ge2$ | No match |

All four modulus claims follow by division of the displayed affine coefficients.  For example, $29070=17\cdot1710$, $785\equiv3\pmod{17}$, and $4^j\pmod{17}$ cycles $4,16,13,1$.  Since 3 is invertible modulo 17, $(4^j-1)/3\pmod{17}$ cycles $1,5,4,0$.  This proves an exact nonintersection, not a statement about the one-step borrowability of these progressions.  A different obstruction family could still intersect them.

## Strict-input Q moves have a decreasing companion

For $r_v=2v/(3v+1)$, $r_v$ is strictly increasing on positive $v$.  If a Q rule satisfies $r_u r_b=r_c r_d$ with $0<c,d<u$, then

\[
r_b=r_c\frac{r_d}{r_u}<r_c,\qquad
r_b=r_d\frac{r_c}{r_u}<r_d.
\]

Consequently **$b<\min(c,d)<u$**.  There is no hidden companion-height overshoot in a genuine two-smaller-input introduction.  Such rules could support a strong induction **inside the restricted palette**, if a finite seed set and covering collection were found.  The isolated $x/z$ rules do not close under their own inputs, and the 23 and 85 failures show that simple one-step induction needs exceptions.  None of this is an obstruction to unrestricted unit supply, which is already settled by Applegate–Lagarias for 3-free catalysts.

## What Applegate–Lagarias supplies, and what it does not

[Applegate and Lagarias, *The 3x+1 Semigroup*](https://arxiv.org/html/math/0411140), Theorem 1.1, proves that the semigroup $S=\langle 2,r_v: v\text{ positive odd}\rangle$ contains every positive rational whose reduced denominator is prime to 3.  For any odd 3-free $u$, $r_u^{-1}=(3u+1)/(2u)\in S$.  Multiplying its positive generator representation by $r_u$ gives **some** exact value-one word containing $u$, with no assumption that the Collatz orbit of $u$ descends.  Because denominators $3v+1$ are prime to 3 and a unit word has 3-adic valuation zero, every odd label in that word is automatically 3-free.

Their proof does contain a finite-base, growing induction: Lemma 2.1 handles all classes modulo 4096 except $-1$, Lemmas 2.2–2.3 use growing wild multipliers $m=(2^j+1)/3$ to move out of that exceptional class, and Lemma 3.2 uses a $q$-smooth residue construction to grow the wild-integer range.  The induction tracks the weak semigroup and wild semigroup together.  These multipliers and final words may use arbitrary generators $r_v$, so the proof does not establish closure of the **restricted U2/U8/U13+Q palette**.  That restriction is unnecessary for unit-supply existence.  Their decreasing *scalar* endpoint does not ensure the directed vertex balance or target-free termination needed by catalytic repair.  The semigroup theorem is a proven literature input, not presently a theorem in this repo's Lean development.

The $-1\pmod{2^j}$ obstruction in their §2 applies to their finite-list multiplier descent method; it should not be relabeled an infinite obstruction to quadratic two-smaller-input introduction.  The latter relation is a different closure operator, and the dyadic candidate fails to obstruct the four currently required input progressions.

## Research decision

The dyadic nonintegrality family cannot block the two symbolic rules, but neither a different infinite obstruction nor restricted-palette closure has been established.  More importantly, **restricted-palette closure should not gate the main route**.  For any finite catalyst $C$ of 3-free labels, the inverse of its scalar value has denominator prime to 3 and thus has an $S$ representation; concatenating it with $C$ gives a unit containing $C$.  Conversely, no value-one unit can contain a 3-divisible label because every generator has nonnegative 3-adic valuation.  The exact unrestricted borrowing criterion is therefore simply “all odd labels in $C$ are 3-free.”

Unrestricted units make any **known** same-value source $X$ and target $Y$ equivalent when their scalar is 3-free: choose a word $Z$ of value $1/\mathrm{value}(X)$, insert the unit $Y+Z$, then remove the unit $X+Z$.  That uses $Y$ itself and gives no target-free balanced output.  A meaningful sufficient repair architecture keeps the central Q/cubic relation and a **common** catalyst word fixed, using the semigroup theorem only to supply that word as a bookend.  Then central relation, vertex-balanced endpoint selection, and a well-founded rank are the live problems.  The restricted palette remains an optional computational control for concise explicit certificates, not a prerequisite for the main theorem.  See the [supply addendum](RESEARCH-2026-09-29-unrestricted-supply-addendum.md) for the full iff proof and the 3-divisible-sector caveat.
