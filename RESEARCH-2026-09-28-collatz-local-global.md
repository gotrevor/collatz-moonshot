# Local Q congruences versus an integer borrowing rule

The Q exchange condition for positive odd labels is (r_u r_b=r_c r_d), where (r_x=2x/(3x+1)).  For a **fixed** target (u), clearing denominators gives

\[
D(u,c,d)b=K(u,c,d),\qquad
D=u(3(c+d)+1)-3cd,\qquad K=(3u+1)cd.
\]

For (0<c,d<u), (D=u(3c+1)+3d(u-c)>0).  Positivity of the rational candidate (K/D) is therefore automatic, but its integrality is not.  The existing [borrowability-height note](RESEARCH-2026-09-28-borrowability-height.md) and `BorrowabilityHeight23.lean` show that (u=23) has **no** Q rule from two smaller positive odd input labels, even with an unbounded companion (b).  This note sharpens what finite congruences can and cannot infer from that case.

## Every prime separately has a legal-shape local witness

Two of the 66 input pairs give these rational solutions:

| (u) | (c,d) | (D) | (K) | unique (b=K/D) |
|---:|---:|---:|---:|---:|
| 23 | 1,1 | 158 | 70 | (35/79) |
| 23 | 13,17 | 1430 | 15470 | (119/11) |

Both input pairs are positive, odd, 3-free, and strictly below 23.  Both rational companions are positive; their numerators and denominators are odd and 3-free.  Their reduced denominators 79 and 11 are coprime.  Thus, for **each prime (p)**, at least one row supplies (b\in\mathbb Z_p) satisfying the exact polynomial Q equation.  At (p=2) and (p=3), either companion is even an appropriate unit.  Yet no common choice of the input pair has an integer companion.  This is a precise failure of the inference “a local witness at every prime implies one global borrowing exchange”: the existential choice of (c,d) can change with (p).

For any (k\ge1), the second row also has a solution to (1430b\equiv15470\pmod{6^k}), namely (b\equiv119\cdot11^{-1}\pmod{6^k}).  It is odd and 3-free modulo 6.  Arbitrarily deep 2- and 3-adic tuning therefore does not settle the odd-prime denominator 11.  This is **not** a failure of the Chinese remainder theorem; CRT combines compatible finite congruences exactly as promised.  The missing requirement is divisibility by the *full variable denominator* (D).

## One finite joint modulus detects the global failure

For any fixed (u) and finite input bound (H<u), let

\[
L_{u,H}=\operatorname{lcm}\{D(u,c,d):0<c\le d\le H,\ c,d\text{ odd}\}.
\]

For each candidate pair (D\mid L_{u,H}).  If (Db\equiv K\pmod{L_{u,H}}) for **one** pair and one integer residue (b), then (D\mid K), hence the unique rational companion (K/D) is already a positive integer.  Conversely, an integer companion satisfies the congruence.  Taking modulus (6L_{u,H}) and asking for a residue (b) coprime to 6 also detects whether that integer companion is odd and 3-free, because (b-K/D) is a multiple of (6L_{u,H}/D).  This is a finite-height equivalence, not a uniform modulus as (u\to\infty).

For (u=23,H=21), the exact 66-pair lcm is

```text
L = 1017756171880144140611619061363201779443467418094627786964547854600935879817724961792482574683138750
  = 2 · 5^4 · 7^3 · 11 · 13 · 17 · 19 · 29 · 31 · 37 · 41 · 47 · 53 · 61 · 67 · 71 · 73 · 79 · 89 · 97 · 101 · 103 · 107 · 109 · 113 · 131 · 137 · 149 · 211 · 277 · 373 · 409 · 421 · 541 · 607 · 613 · 643 · 661 · 673 · 709 · 733 · 739 · 751 · 757 · 769 · 787.
```

For every pair, (D\nmid K); since (D\mid L), the raw congruence (Db\equiv K\pmod L) has **no** solution with (c,d<23).  A greedy prime-power cover, not claimed minimal, gives a smaller blocking modulus recorded by the CLI.  The CLI checks every pair using the criterion (\gcd(D,N)\nmid K), without enumerating residues (b).

`experiments/borrowability_descent.py local-global-23` prints both witnesses, (L), its factorization, and the smaller cover.  Persistent subprocess tests cover the two rational identities, hand-derived factor exponents, and every smaller input pair.  Run `experiments/borrowability_descent.py test`.  The Lean statements are `each_prime_power_has_small_inputs_23` and `no_global_small_inputs_23` in [LocalGlobalBorrow23.lean](CollatzMoonshot/Obstructions/LocalGlobalBorrow23.lean).

**Research implication.**  An existential CRT construction can help only if it controls the denominator that its own chosen inputs create, or proves a parametric divisibility identity.  Local witnesses chosen independently at primes, or selected congruences without a sufficient divisibility guarantee, do not produce a legal Q rule for a fixed target.  The present argument says nothing against a future constructive family with a specific (c(u),d(u)) and a provably integral (K/D).
