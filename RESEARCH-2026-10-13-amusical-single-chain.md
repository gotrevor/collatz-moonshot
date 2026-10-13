# Amusical permutation: looking for a single-chain mechanism (2026-10-13)

Target: `AmusicalInfinitelyManyOrbits` (Klamkin 1963, problem (a)).  Odds of settling it in
this lane: low, ~2-3%; it has been open for 63 years and resisted Venturini and Tavares.
This note maps why the obvious tools fail and what a mechanism would have to use.

## 1. U is a full shift on three symbols, restricted to the integers

Let `K = ℤ₂ × ℤ₃`.  Define `Û(a, b)` by reading the branch of `a` (even, `1 mod 4`, `3 mod 4`)
and applying the same rational affine map (`3x/2`, `(3x+1)/4`, `(3x-1)/4`) to both coordinates.

* On `ℤ₂`, each branch maps its clopen piece (measure `1/2, 1/4, 1/4`) homeomorphically onto
  `ℤ₂`, with contracting inverse branches.  So the forward branch sequence codes `ℤ₂`
  homeomorphically onto `{E, A, B}^ℕ`.
* The `ℤ₃` image of branch `E, A, B` lands in `0, 1, 2 mod 3` respectively
  (`even_iff_amusical_mod_three` is the integer case), so `Û` is invertible with inverse reading
  `b mod 3`; on `ℤ₃` the inverse branches `2m, 4m+1, 4m+3` are again a full three-branch coding.
* The future symbols of `(a, b)` depend only on `a` and the past symbols only on `b`.

So `(K, Û)` is topologically conjugate to the two-sided full shift on `{E, A, B}`, and `U` is
its restriction to the diagonal copy of `ℤ`, which is dense and invariant.  In this language:

* **Klamkin (a):** does the diagonal `ℤ` meet infinitely many shift orbits?
* **Orbit of 8:** is the point `ι(8)` aperiodic?
* **Periodic points:** a periodic word `w` of length `p` is the diagonal image of the rational
  fixed point `c_w / (2^|w| − 3^p)` (the same rational affine map on both coordinates), so the
  shift's periodic points are exactly a countable set of rationals with denominators prime to
  `6`, and the cycles of `U` are the periodic words whose rational is an integer
  (Böhm-Sontacchi for `U`).

This is very likely known in Lagarias's conjugacy language; I have not found it stated for the
permutation.  Not formalized (needs `ℤ_[p]` coding machinery).

## 2. Why density, measure and crossing arguments all balance (no-go)

Any argument that also applies to `ℕ` itself, which is a union of infinitely many orbits,
cannot prove there are infinitely many.  All the first-order tools are of that kind:

* **Haar balance.**  `E[1/slope] = (1/2·2/3 + 1/2·4/3)^N = 1`: the 2-adic Haar measure is
  exactly preserved, so Tavares's mass-conservation identity (`ψ = ω` for a bijection) balances
  for `ℕ`.  I checked a Rhin-quantified version of Tavares's Theorem 1: it fails because points
  where `U^N` decreases can drop by up to `(3/4)^N`, and that factor swamps the gain.
* **Conformal measures.**  A `U`-invariant set with residue densities defines a measure on `K`
  with the same Jacobian (`2/3` on `E`, `4/3` on `A, B`) as Haar.  Its density with respect to
  Haar is `Û`-invariant, so under ergodicity it is Haar: an invariant set's residue statistics
  cannot tell one orbit from many.
* **Level crossings.**  Below any level, the drift `+0.0589` per step is exactly paid for by
  up-crossing overshoots plus down-crossing undershoots (a telescoping identity), with about
  `X/6` entries into `[1, X]` in total.  This is consistent for any number of chains.

## 3. What single-chain-ness forces

If there are `k` orbits, all integers `≤ X` lie on `k` chains, so some chain visits at least
`X/k` of them.  Its visits below `X` span an index range of length at least `X/(2k)`.  Since a
chain is the orbit of its minimum `m` (one of finitely many seeds):

> **Finitely many orbits ⇒ some fixed seed `m` has `|U^j m| ≤ C|j|` for infinitely many `j`**
> (in fact for a positive fraction of the times at which it is below each level).

Contrapositive candidate node: if every aperiodic orbit escapes faster than linearly,
`|U^j m| / |j| → ∞` as `j → ±∞`, then infinitely many orbits.  The hypothesis concerns
individual orbits, the same kind of statement as `AmusicalOrbitOfEightInfinite`, only stronger.
So this route turns Klamkin (a) back into the orbit-of-8 wall.  Honest assessment: the
reduction is a pigeonhole, not a mechanism.

A linear-size return `U^j m ≤ Cj` is an approximate `S`-unit relation
`|3^j m + c_w| ≤ Cj · 2^n` with `n ≈ j log₂ 3`, where `c_w` is a signed sum of `~j` terms
`±3^a 2^b`.  Baker-type bounds handle few terms (Simons's m-cycles); here the number of terms
grows with `j`.

## 4. Levers worth a further look (odds of each yielding a real dent)

Test applied to each: does the argument also apply to `ℕ`?  If so it cannot work.


1. **Window minima, upper half (in progress, ~60%).**  `WindowMinDensity L` gives the
   unconditional upper bound `upper density(orbit minima) ≤ δ_L` for every `L`, so
   `≤ p_f · p_b ≈ 0.0498`.  Pure congruence counting; it bounds the number of orbits from
   *above*, not from below.
2. **Time asymmetry: dead (~1%, tested 2026-10-13).**  The drifts `0.0589` forward and `0.0566`
   backward measure the same steps under two densities (2-adic residues forward, 3-adic
   backward), and the Jacobian converts one into the other exactly.  Among integers up to `X`,
   multiples of `3` have share `1/3`; among integers up to `2X/3`, evens have share `1/2`; both
   counts are `X/3`.  The asymmetry balances on `ℕ`, so it cannot separate one chain from many.
3. **Rational height: dead as stated (~1%), with a by-product.**  `Û` preserves the denominator
   `q` of every `x ∈ ℤ_(6)`, so the rationals split into invariant layers `D_q = (1/q)·ℤ`.  On
   numerators, `D_q` carries the permutation `U_q(2n) = 3n`, `U_q(r) = (3r + q)/4` for
   `r ≡ q (mod 4)`, `U_q(r) = (3r − q)/4` for `r ≡ 3q (mod 4)`: the `qx+1`-style relatives of
   Collatz's permutation, with `U_1 = U`.  Every periodic shift word lives in the layer of its
   rational's denominator, a divisor of `2^|w| − 3^p`.  The denominator is the only invariant
   this structure supplies, and it is constant on the integers.
4. **Compare a solvable relative.**  Simons 2022 §5.4: for `P(a, b, c, d)` with `b | d`, there
   are provably infinitely many divergent orbits, because one residue class is forward-invariant
   with strict growth.  `U` has no forward-invariant class (both `×3/2` and `×3/4` branches
   reach every class).  Measuring how far `U` is from having an invariant "growth cone" might
   suggest a weaker invariant.

## Evidence on file

* `scripts/amusical/minima2.py`: orbit-minimum density `0.049957` on `1..10^6`.
* `scripts/amusical/survival.py`: random-walk prediction `p_f · p_b = 0.049780`.
* `scripts/amusical/window.py`: exact `δ_L` vs empirical, agreement to `~10^-4` for `L ≤ 20`.

## 5. The q-layers `U_q` (numerics 2026-10-13, `scripts/amusical/uq.py`, `cycle_heuristic.py`)

* **Cycles are Böhm-Sontacchi divisibility.**  A length-`p` branch word of weight `n`
  (`#evens + 2·#odds`) closes on the rational `c_w / (2^n − 3^p)`, which lives in the layer of
  its denominator.  When `q = |2^n − 3^p|` every such word closes in `D_q`, which explains the
  big same-length families: `139 = 3^7 − 2^11` (dozens of 7-cycles), `13 = 2^8 − 3^5` (5-cycles).
* **`q = 1`.**  The forced cycles need `2^n − 3^p = ±1`, which by Mihăilescu are only `{±1}` and
  `{±2, ±3}`.  The 5-cycle and the 12-cycle are accidental divisibility: `13 | c_w` and
  `7153 = 23·311 | c_w` respectively.
* **Divisibility heuristic.**  Counting each word as an integer cycle with probability
  `1/|2^n − 3^p|`, the expected number at length `p` peaks at exactly `p = 5` (1.38) and
  `p = 12` (1.24), the two observed accidental lengths.  The total is overcounted (≈ 9.8
  expected against 4 observed, both signs), because the model ignores that a new cycle needs
  elements beyond the searched range, which confines it to `|n log 2 − p log 3|` tiny (Simons's
  Λ).  The tail estimate is `≈ 0.02` expected cycles of length `≥ 200`: heuristic support for
  `AmusicalFinitelyManyCycles`, not for Klamkin (a).
* **Invariants.**  `gcd(r, q)` is `U_q`-invariant (`q` is prime to `3`), and so is the coset of
  `r` in `(ℤ/q)^× / ⟨2, 3⟩`, since every branch multiplies by `3/2` or `3/4` mod `q`.  These give
  finitely many invariant pieces per layer.  For `q = 1` the `±1` offsets destroy the coset
  invariant, and `D_q` contains the copy `q·ℤ` of `U`, so orbit counts for `U_q` bound those of
  `U` from above only: no lever for Klamkin (a) from this side.

## 6. Do orbit minima carry residue structure beyond windows?  No (2026-10-13)

The minima avoid `2, 16, 20, 34 (mod 36)`, but that is the 2-window condition (for
`n = 36k + 2`, `U^-2 n = 32k + 2 < n`).  The question that matters for certification: among
`L`-window minima, is being a *global* minimum correlated with the residue class?  A hidden
arithmetic rule would show as excess `χ²` that persists as `L` grows; a finite-window artifact
fades.  `scripts/amusical/minima_vs_window.py`, `n ≤ 10^6`, cycle members excluded (they are
window minima but never orbit minima, and dominated the first run):

| `L` | window minima | global/window | `χ²` mod 72 (df 15) | mod 864 (df 143) | mod 2592 (df 383) |
|---|---|---|---|---|---|
| 20 | 67550 | 0.740 | 62.1 | 285.6 | 537.6 |
| 40 | 56722 | 0.881 | 29.7 | 168.1 | 407.3 |
| 80 | 51685 | 0.967 | 16.2 | 117.6 | 336.4 |

The excess decays to nothing by `L = 80`.  At this resolution, global minima are
residue-independent beyond long-window conditions: they look exactly like the independent-walk
model of `AmusicalMinimaDensity`.  No congruence certifies a global minimum, matching the
theory: a residue class controls only finitely many steps, and survival past step `L` costs
about `1.5^-L` (Cramér root `θ = 1`).  Certifying individual minima runs into the orbit-of-8
wall.

## 7. Research-agent sweep (2026-10-13)

Four parallel agents; reports staged at `~/personal/tmp/amusical-agents/out/*.md` (session
scratch, not in the repo).  Outcomes, each recorded in `Maze.lean`:

* **Literature.**  No proof that any non-trivial residue-class-affine permutation has infinitely
  many orbits; every known proof uses finite order, fixed classes, class cycles, or a class union
  `S` with `σ(S) ⊊ S` (Simons §5.4).  For `U`, any class union with `U(S) ⊆ S` has `U(S) = S`
  (transition graph mod `M` strongly connected for `M ≤ 400`; the same checker flags Simons's
  example).  Lagarias 2003 (entry on Venturini 1992): for such permutations even the existence
  of one infinite orbit is open; for `U` this gives the dichotomy
  `amusicalInfinitelyManyOrbits_or_exists_infinite`.  Prior art to cite: Simons 2022 §5.1
  measured the minima ratio `.05X0` empirically, no formula; Conway 2013 App. 2 computes the
  `L = 1` local-minimum density.  Novelty of `c`, its derivation, `L ≥ 2` window densities and
  the shift conjugacy for `U`: not found (~75-85%).
* **Adelic.**  Each branch preserves `|·|_∞ |·|_2 |·|_3` (`amusical_branch_product_formula`),
  so `Û` preserves Haar on `ℝ × ℤ₂ × ℤ₃` with `ℤ` a covolume-1 lattice.  That restates mass
  conservation; almost every point drifts off both ways (no recurrence); the orbit-minimum set is
  a fundamental domain with positive measure and empty interior (congruences give only upper
  bounds); integers collapse to the fixed point of the solenoid quotient, so `×2 ×3` rigidity
  sees nothing.  Haar density of the minimum set `0.04978–0.04983`, matching `c`.
* **Diophantine.**  At a return the form `n log 2 − j log 3 + log(y/x)` is `O(log j)`
  (`return_defect_bound`), so Baker/Rhin gives nothing beyond cycles (Simons needs `y = x`); the
  sums have `≈ 0.585 j` terms, above any subspace-theorem rigidity threshold; a linear return
  needs `≥ 6.47 ln j` symbol runs (elementary), while real ones have `≈ 2j/3`.  Strong form of
  the reduction: `exists_denseLinearReturns_of_finitelyManyOrbits`, equivalent to positive upper
  density of one orbit.  Believed (~90%): each aperiodic orbit has finitely many linear returns
  (seeds 8, 14, 40, 64: last return with `C = 1000` at `j ≤ 197`).
* **Chains.**  No chain statistic separates finitely from infinitely many orbits: finite-step
  statistics (residues, windows, mass flow) agree in both worlds, and anything about two points
  sharing an orbit needs an all-time fact about one orbit.  Proved on paper, now treadmill targets
  in `AmusicalChains.lean`: window minima on one orbit are more than `L` steps apart; window
  densities are uniformly `≥ 1/36` (`fwdSurv, bwdSurv ≥ 1/6` via `g_L(s) ≥ 1 − e^{-s}`); hence
  finitely many orbits force an infinite orbit with `liminf |U^j x|/|j| = 0` (sublinear
  recurrence; with effective counting `U^j x ≤ C|j|/log|j|`, and under "only six orbits",
  `U^j 8 ≤ 360|j|/ln|j|` infinitely often).  New reopen condition `AtLeastLinearGrowth`, weaker
  than `NoLinearRecurrence`, with its implication to Klamkin (a) proved.  Also: excursion-forest
  roots are exactly the minima; no eventually periodic set closed under `U` and `U⁻¹` is a
  nontrivial separator (skew-product transitivity); "orbit of `8` has density `1`" contradicts
  nothing provable.  Computational: any sixth cycle has length `≥ 665` (float-based cut test;
  not formalized).

## 8. What U lacks: time reversal (2026-10-13, "relative" agent, checked)

All four §8 theorems (Gaussian orbits, NR, the reformulation, `reversing_zpow_fixed`) are
kernel-checked and axiom-clean as of 2026-10-13.

* **A relative where it works.**  `H` on `ℤ[i]` (`GaussianRelative.lean`): every piece
  multiplies by `π = 2+i` and divides by `π̄ = 2−i`, as `U` multiplies by `3` and divides by `2`.
  Haar-balanced, dissipative (drift `≈ 0.13` both ways), wild, no residue-class cycles, finitely
  many cycles per length, two-sided full-shift coding (so no growth cone), residue graph strongly
  connected at every tested modulus.  And `conj ∘ H ∘ conj = H⁻¹`, so every orbit meets
  `Fix(conj) = ℤ` at most twice: **infinitely many orbits, proved** (any `13` real integers lie in
  `≥ 7` orbits).  Independently checked: `scripts/amusical/gauss_check.py` (integral, injective,
  reversal identity on `|a|,|b| ≤ 60`; a perturbed constant fails exact division).
* **Theorem NR.**  No bijection of `ℤ` affine on finitely many pieces reverses `U`
  (`no_piecewiseAffine_reversor`): `ι U^ℓ = U^{−ℓ} ι` on an infinite cell forces
  `v₃(slope) + ℓ = v₃(slope') − ℓ`.  The unbalance of `U` sits on the primes `2, 3`, which no
  automorphism of `ℚ` exchanges; `ℤ[i]` hosts a split pair that conjugation swaps.
  The pieces may be *any* finite partition of `ℤ` (not just residue classes or intervals).
* **Exact reformulation.**  Klamkin (a) ⇔ some sign-preserving involution reverses `U` and has
  infinitely many nonnegative fixed points (`infinitelyManyOrbits_iff_reversor`): reversibility
  is the whole problem, and NR says the reversor cannot be piecewise affine.
* **Also from the agent:** `U`'s residue transition graph is strongly connected for every
  modulus, so every eventually periodic `U`-invariant subset of `ℕ` is finite or cofinite (a proof
  must use sets not definable in `(ℤ, +, <)`); the elliptic relative `G(z) = (πz + ρ)/π̄` (a
  discretised Pythagorean rotation) is also conj-reversible; a tame Haar-balanced no-cone map with
  exactly one orbit exists, so balance + no cone + mixed slopes cannot by themselves force
  infinitely many orbits; composing `U` with residue permutations creates a cone in `144/719`
  cases mod `6`, so the no-cone property is fragile.
