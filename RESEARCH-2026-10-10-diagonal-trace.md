# Diagonal trace comparison: investigation of the arithmetic-spike target

2026-10-10, Opus (Ren), with Astra (Codex) refereeing.
These are paper calculations.  No Lean results yet, and no campaign launched.

## Target under review

Astra's proposal packet (private, §2):

    k(R) = floor(log_3 R / 4),   B_R = {odd n : sqrt R < n <= R},
    E(R) = sum_{n in B_R} (g(n) - rho_k(n))_+ / n  =  o(log R)?        (DiagonalTraceNoExcess)

Here g = delta·G_n·n·D_n is the canonical arithmetic trace, rho_k(n) = 3^k mu(n mod 3^k) is the full-Haar cylinder density of Tao's
stationary law, and D_n is the weighted first-hit density.  Source: Valbuena,
[collatz-two-coordinate-obstruction](https://github.com/x1xhlol/collatz-two-coordinate-obstruction), source-reviewed revision
`a7275d5` (paper statements and stated verification scope read; the Lean bundle was not replayed).

## The consumer composes (verified against the source text)

`tao-basin-densities.tex` thm:ct-raw-divergent-excess (line 2494) proves: an injective orbit rooted at odd u, 3 ∤ u, forces
`A(R) >= b log R` eventually for every `b < 1/lambda + eta(u)`, with `eta(u) > 0`.  Here `A(R) = sum_{odd N <= R} D_N` and lambda = log(4/3).
So an upper bound `limsup A(R)/log R <= 1/lambda` in the same normalization excludes divergence.  The packet's shell derivation supplies exactly that from
E(R) = o(log R): sum over B_R of rho_k/n = (1/4) log R + o(1), g >= delta·n·D_n, and iterated square-root shells.  Cycles are untouched.

## Kill control (Astra): no Haar/pointwise/semicontinuity proof, even of the capped stage

Let V be the units of Z_3, and let U ⊂ V be open, containing every positive unit integer, with Haar mass < 1/12.  Set c = 2/3 + |U| and
E' = (1_V + 1_U)/c.  E' is a bounded, normalized lsc density, uniformly positive on V, in every L^p, and rho_k(n) → E'(n) at every integer.
But E' = 2/c on every unit integer, so the shell excess is at least (1/(3c) − 1/4) log R, with coefficient > 7/36.  A cap at M = 3 changes nothing.
Any proof must use an identity that E' violates.

## The stationary identity (new here; exact)

Let P be the expanded inverse operator

    (P f)(x) = sum_{a >= 1, 2^a x ≡ 1 (mod 3)} 3·2^{-a} f((2^a x − 1)/3).

1. Write X = (1 + 3X')/2^a, X' ~ X, so mu = sum_a 2^{-a} (phi_a)_* mu with phi_a(x) = (1+3x)/2^a.  The Haar Jacobian of phi_a is 1/3, so E = PE a.e.
2. phi_a maps the depth-(k−1) cylinder of y affinely onto the depth-k cylinder of phi_a(y).  Hence **rho_k = P rho_{k−1} exactly** for k >= 1, with rho_0 ≡ 1.
   Check: rho_1 = (0, 1, 2) on residues (0, 1, 2) mod 3.  In code this is the same recursion as the packet's `syracuse_law`.
3. The source gives g = Pg at positive integers (eq:ct-critical-harmonic plus the vanishing dyadic remainder, lines 2574–2577).

Therefore, at every positive integer n and 0 <= j <= k,

    g(n) − rho_k(n) = P^j (g − rho_{k−j})(n),        in particular   g − rho_k = P^k (g − 1).

E' violates g = Pg at every integer n ≡ 2 (mod 3), so this is a canonical identity excluding the kill control, with the cylinder cutoff kept.
It holds for every P-harmonic g with the canonical rho_k = P^k 1, though, so it cannot tell which harmonic function g is.

**Shell form.**  For odd n the exponent is forced, a = v_2(3y+1), and 3·2^{-a}/n = 1/(y + 1/3).  So for every finite set I of odd integers,

    sum_{n in I} (P f)(n)/n = sum_{y odd, S(y) in I} f(y)/(y + 1/3)        (S = Syracuse map).

So nu(n) = g(n)/n is S-invariant up to the 1/3 correction, and the **signed** diagonal excess equals the harmonic mass of g − 1 over the
k-step Syracuse preimage of the shell.  All the difficulty sits in the positive part: (P^k(g − 1))_+(n) is a law-of-large-numbers question over
the depth-k inverse tree of n.

**Equivalence.**  Given the source's lower bound, the signed version of the target is the raw occupation asymptotic, A(R) ~ log R / lambda.
The positive-part target is that asymptotic plus a shell-averaged L^1 comparison, sum_{B_R} |g − rho_k|/n = o(log R).

## The cap split: what each half can see

`(g − rho)_+ <= (min(g,M) − rho)_+ + (g − M)_+` (`cap_split`, proved in the packet).

* **Capped stage vs divergence.**  The source's divergence witness is the first J_R ~ a log R / log(3/2) points of an injective orbit, each with
  g(u_j) >= delta u_j D_u / P_inf (linear spikes).  It contributes at most M J_R / sqrt R → 0 to the capped sum.  An injective orbit is visible to
  the capped stage only if, for infinitely many R, it has at least about (eps/M) sqrt(R) log R points in the shell.  So the capped stage is a
  "do integers sample min(E, M) fairly from above" statement.  It is blind to the known witness, and the kill control shows it still needs arithmetic.
* **Tail stage = lingering on heavy points.**
  - *Antichains are free.*  If no element of a finite set A lies on another's forward orbit, the first-hit basins are pairwise disjoint, and
    0 <= w_n <= 1_{B_n} gives sum_{n in A} D_n <= 1.
  - *In general,* sum_{n in S} D_n = log-mean over sources q of sum_{n in S ∩ orbit(q)} w_n(q).  So the tail says: the expected number of
    spike visits along one orbit's shell segment is o(log R) as M → ∞.
  - *Heaviness propagates forward.*  From the binary identity and g >= 0: for even n, g(n/2)/(n/2) >= g(n)/n; for odd n,
    g(Tn)/Tn >= (g(n)/n)(1 + 1/(3n))^{-1}.  So the superlevel sets of D are forward-closed up to the correction product.

  Charging spikes to disjoint first-hit basins therefore pays exactly for antichains.  The remainder is an orbit-lingering statement on a
  spike set the occupation itself defines.  The source's ladder clock bounds visits on a good event of density 1 − O(e(M)).  The bad event
  times its occupation is precisely the rare-path contribution, so the clock does not close it.

## Verdict (pending Astra's referee)

The target is correct as a consumer: it would exclude divergence, subject to the imported theorem.  It is equivalent, up to the L^1 upgrade,
to the raw occupation asymptotic.  The cap split is a correct separation:

* the bounded stage is free of the known divergence witness;
* the tail is lingering on heavy points.

Neither half has a mechanism yet, and basin disjointness gives no leverage beyond antichains.  **Recommendation: park §2** until a chain-side
resource appears, meaning an upper bound on expected shell occupation of a forward-closed heavy set that does not presuppose the occupation bound.
Subjective odds that the capped stage is provable with the source's machinery plus the identity above: 25%.  Odds for the tail: < 5%.

## Open questions passed to Astra

(A) Is step 2 exact at x ≡ 0 (mod 3) and in the depth-k a-sum?  (B) Is there a chain-side resource the antichain analysis misses?
(C) Does Astra accept the verdict?  Outcomes will be recorded in the next section.
