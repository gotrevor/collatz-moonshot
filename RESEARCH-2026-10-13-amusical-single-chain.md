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
  Haar is `Û`-invariant.  (Corrected 2026-10-13, §10: Haar on `ℤ₂ × ℤ₃` is conformal, not
  invariant, and `Û` is totally dissipative for it, with wandering set the formal orbit minima of
  measure `c`; so an invariant density may be any function of the wandering point and absolute
  continuity forces almost nothing.)  Either way an invariant set's residue statistics cannot
  tell one orbit from many.
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

## 9. Reversors determined by residues (2026-10-13, "reversor" agent, checked)

Lean: `AmusicalContinuousReversor.lean` (targets for a treadmill; Maze row "reversor determined by
residues").  A reversor `ι` (`ι ∘ U = U⁻¹ ∘ ι`) is `(2,3)`-adically continuous iff its step symbols
`stepSym (ι n)` depend only on `n mod 2^c₀ 3^d₀`; then it is determined by that finite table
(Lemma S) and equals flip ∘ a cellular automaton on the Matthews–Watts shift.

* **Theorem C (kernel-checked 2026-10-13, with A, A′ and Lemma S).**  No injective continuous reversor grows at most
  linearly.  Mechanism: the far-future step symbols of `ι n` are a window function of the past
  symbols of `n` (uniform on three letters), so the even-step frequency `q` is a fraction over a
  power of `3`, never `1/2`; along `L` disjoint windows the event densities are `ρ^L` vs `2^{−L}`
  with `ρ = max(q, 1−q) > 1/2`, contradicting injectivity plus `|ι n| ≤ C|n| + D`.  Corollaries
  (paper only): `|ι n|/|n| → ∞` on a set of lower density 1; a continuous reversing involution has
  a fixed set of density 0.  Breaks for `H` (both laws have powers of `5`; conjugation is an
  isometry), as it must.  Reproves the residue-class case of Theorem NR by a different mechanism.
* **Theorems A, A′ (and B, B′, paper only).**  Continuity for one prime alone, or with the other
  prime's dependence growing at rate `< 1/2` (B) or `< 1` (B′) digits per digit, forces a constant
  reversor.  B's `1/2` is sharp on `ℤ₂ × ℤ₃` (a non-constant semiconjugacy at exactly rate `1/2`),
  so arguments that also work on the full shift are exhausted: Q1 needs integrality.
* **Q1 (no bijective continuous reversor at all): believed ~93%, open**
  (`AmusicalNoContinuousReversor`).  Exact computation kills every window-`≤ 2` table; window-`3`
  survivors of the cycle test fail numerically on small integers.

## 10. Log-weighted balance and fat orbits (2026-10-13, "equidist" agent, checked)

Lean: `AmusicalLogBalance.lean` (all proved, axiom-clean).  Weight `n` by `1/n`: `W_N(S) = Σ_{n ∈ S, n ≤ N} 1/n`.

* **Exact balance (paper proof checked).**  For any union `S` of orbits in `ℕ_{>0}`,
  `W_N(S ∩ 2ℤ) = W_N(S)/2 + O(1)` and `W_N(S ∩ 3ℤ) = W_N(S)/3 + O(1)`.  Proof: `U` maps the evens
  of `S` onto the multiples of `3` with weight factor `2/3` and the odds onto the non-multiples
  with factor `4/3 + O(1/n²)`; cutoffs move by bounded log-factors; so with `e, o` the even and odd
  weights, `e + o = (2/3)e + (4/3)o + O(1)`, i.e. `e = o + O(1)`.
* **Reduction.**  If every orbit has upper log density `0`, Klamkin (a) holds (finitely many
  orbits partition `ℕ`, whose log density is `1`).  Stronger than the density-`0` reduction.
* **Correction to the brief.**  Haar on `ℤ₂ × ℤ₃` is not `Û`-invariant (evens, measure `1/2`,
  map onto `ℤ₂ × 3ℤ₃`, measure `1/3`); it is conformal with Jacobian `1/slope`, and `Û` is totally
  dissipative, with wandering set the formal two-sided orbit minima, of measure exactly `c ≈
  0.04978`: the conjectured density of orbit minima is the Haar measure of the wandering set.
  So the hoped "fat orbits equidistribute" theorem has no ergodic engine; a fat orbit only gets
  `ν(W) > 0`.  Unions of orbits are measurably not equidistributed (minimum `≡ 0 mod 4` union
  has `0.262` of its log weight on `0 mod 4`, model `0.2608`), but proving any such union
  non-equidistributed already proves a seventh orbit.  Odds this lane gives (a): `< 1%`.

## 11. Seventh orbit (2026-10-13, "seventh" agent, checked)

Lean: `AmusicalSeventh.lean` (targets).  A seventh orbit ⇔ no orbit of `U` is cofinite in `ℕ`.
No contradiction found from a cofinite orbit of `8`; believed `≥ 7` orbits at 99.5%, `14` an orbit
minimum at 99% (no meeting with the orbit of `8` for `|j| ≤ 6·10⁶`; both stay above `2⁸⁰⁰⁰`).

* **Sparse sweeping (unconditional).**  An infinite orbit visits `≤ ηX` numbers below `X` within
  any time window of length `2cX log X` (window minima are separated, and window order is a
  residue condition for `n ≥ 2·324^L`).  Under a cofinite orbit, `|t(n)| ≳ n log n` off density `η`.
* **Records (under H, paper only).**  Forward survivors are exactly the upper records of the time
  function, backward survivors the lower records; `8` is the only point that is both.
* **Cycle-like itinerary (under H, paper only).**  In one time direction the even-step frequency of
  `8`'s itinerary must be `log₂(4/3) ≈ 0.415` on infinitely many prefixes, the frequency of a
  cycle; such `2`-adic integers form a Haar-null set of dimension `≤ 0.9868`.  Ruling it out for
  `8` is a Collatz-type statement about one integer.
* **Residue transitivity.**  Every `Uᵐ` has a strongly connected residue graph, so no nontrivial
  union of classes is `Uᵐ`-invariant, and under H `t mod m` is never eventually periodic.
* **The barrier (rewiring).**  A permutation of `ℕ` with at-most-doubling steps can be changed on a
  density-`0` set so all infinite orbits fuse into one.  For `U` this keeps every
  finite-window statistic (density, log-density, window, crossing), so those cannot prove a
  seventh orbit.  Infinite-horizon statistics such as survival do change (§14); a proof
  needs the exact RCWA structure everywhere plus a global mechanism, and the only known global
  mechanism, reversal, is excluded (Theorem NR, Theorem C).

## 12. Statistical twins (2026-10-13, "twin" agent, checked)

Lean: `AmusicalTwin.lean` (all proved, axiom-clean).  No residue-class twin of `U` with finitely many orbits found; believed
none with all slopes `3/2^k` (~97%), but proving that is at least as hard as Klamkin (a), since
`U` is its own twin (a costume).

* **Perfect twins with other cycles.**  `W(2m) = 3m+α`, `W(4m+1) = 3m+β`, `W(4m+3) = 3m+γ`, with
  `α, β, γ` distinct mod 3, have exactly `U`'s cylinder laws and `δ_L` and the same full-shift
  coding; `W_{3,1,2}` has the 3-cycle `8 → 15 → 11`, `U` has none, so statistics do not fix the
  conjugacy class.
* **One-orbit splice (paper, `splice.py`).**  A bijection of `ℤ` with one orbit agreeing with `U`
  off `≤ 2 log₂(2Y+2) + #(cycles in [−Y, Y])` points of `[−Y, Y]` (sharper than the rewiring of
  §11).  So the no-go test is a theorem: only the exact arithmetic of `U` is left as a lever.
* **Positive drift is generic.**  For any residue-class bijection, Jensen on `E[1/slope] = 1`
  gives `E log|slope| ≥ 0`; with all slopes `3/2^k` the effective drift `log 3 − κ log 2` is
  strictly positive both ways, so the transience heuristic covers every such map.  Kohl's `ω`
  (one big orbit) escapes only through exact slope relations like `3 · (1/3) = 1`.

## 13. Escape and Theorem N (2026-10-13, "q1" agent, checked)

Lean: `AmusicalEscape.lean` (all proved, axiom-clean).  The question
whether `U` has a bijective reversor determined by residues is still open; credence that none
exists rises from ~93% to ~97%.

* **Escape (Lemma E).**  A non-periodic orbit leaves every bounded set, and `|U x| ≤ (3|x|+1)/2^b`,
  so forward it spends at most `log₂ 3` bits per step infinitely often; backward, at least
  `log₂ 3`.  Generic rates: forward `3/2 < log₂ 3`, backward `5/3 > log₂ 3`.
* **Theorem N.**  A balanced block code (every bijective residue reversor has one, by Lemma S(b)
  and Hedlund) sends a normal past to a future with even-step frequency `1/3`, i.e. `5/3` bits per
  step.  So `ι n` is periodic, and by injectivity so is `n`.  Hence one integer with a normal
  backward itinerary kills every residue reversor.  Normality of a single integer is open
  (Collatz-type), so this is a reduction.  The Gaussian relative passes, because its forward
  law is the conjugate of its backward law.
* **Window 3 is dead exactly (computer).**  No bijective reversor has `stepSym (ι n)` read off
  three consecutive itinerary symbols.  The sole inputs are surjectivity (Moore–Myhill) and the
  requirement that the nine integer cycles of length `≤ 14` map bijectively to cycles; it was
  cross-checked by SAT.  Re-derived independently (`scripts/amusical/w3check.py`: 24 partial
  rules, 216 completions, none surjective; orphans of length 4 or 5 in `w3certs.txt`).  Lean target:
  `AmusicalWindowThree.lean`.
* **Window 4: the exact tests run out.**  40 surjective (permutive) window-4 rules pass every
  exact cycle test.  All fail the numerical integrality probe, which is only evidence.  The
  homeomorphic case was not settled (SAT timed out).
* **Meta (wall).**  A finite set of non-periodic integers never certifies that a table fails,
  since every finite residue datum is CRT-consistent with integrality.  So exact kills beyond the
  cycle and surjectivity tests need a global mechanism or infinite-orbit input.

## 14. Global mechanisms (2026-10-13, "global" agent, checked)

Lean: `AmusicalGlobal.lean`, `AmusicalRewireRatio.lean` (targets).  No global mechanism found; a
seventh orbit stays open.  Every mechanism is a transversal, an infinite set meeting each orbit
at most `K` times (Klamkin (a) ⇔ one exists).

* **Theorem R (bounded-ratio rewiring).**  Some permutation `τ` of `ℕ` agrees with `U` except at
  `O(log² N)` points below `N`, has `τ/U ∈ [1/3, 3]` up to `+3`, and fuses all infinite orbits
  into one.  The construction cuts each orbit at first passage of scales `Y_{k+1} ≥ 8 Y_k`,
  then glues the segments at matching scales along an Eulerian trail.  This kills every
  *coarse-local* invariant: flux, rotation-number analogues, crossing counts, finite-depth
  Cartesian-tree and record statistics.
* **Kohl's mirror (Lemma K).**  `|x| ≤ 4^ℓ (|Uˡ x − x| + 1)` (tight).  So `U` has no translation
  piece, since `v₃` of every slope of `Uˡ` is `ℓ`; Kohl's one-orbit `ω` is built from such
  pieces.  The rewired `τ` obeys the same time separation (0 violations in 5855 pairs), so this
  does not bite.  The survivor is the "anti-Kohl" conjecture (~95%): an RCWA permutation whose
  slopes all have `v_p = 1` has no orbit containing a residue-class tail.
* **No residue-definable transversal (Proposition P).**  Every residue class has points whose
  forward orbit revisits the class `K + 1` times.
* **Survival (Proposition S).**  Survivor lower densities with `a + b > f_L + b_L − f_L b_L`
  (`≈ 0.397` in the limit) give Klamkin (a).  Survival is an infinite-horizon statistic, and
  rewiring changes it (FS density `0.213` for `U`, `0.056` for `τ`).  So it is the right
  statistic, but proving it means showing late drops are rare: the typicality wall.
* **Commuting maps.**  An orbit-moving map commuting with `U` would separate orbits, and Theorem
  C's law obstruction does not apply (both Bernoulli laws can be preserved).
  * The window-2 centralizer is exactly `0, ±1, ±id, ±U`; I re-derived this independently with
    `scripts/amusical/central_w2.py`.
  * Window 3 adds one exotic `±` pair, non-integral only numerically.
  * Believed (~85%): the continuous centralizer is `{0, ±1, ±Uʲ}`.

## 15. The anti-Kohl conjecture (2026-10-13, "antikohl" agent, checked)

Lean: `AmusicalAntiKohl.lean` (κ, τ and the cone identities proved; the rest are targets).  The
conjecture: an RCWA permutation whose slopes all have `v_p = 1` for one fixed prime `p` has no
orbit containing a class tail.  At `p = 3` it gives `U` a seventh orbit.  It is still open on
the residue-transitive core (`U`, the twins); credence ~93%.

* **Theorem T (elementary, any bijection).**  Take a cone `σS ⊆ S`.  If both the forward cores
  `σⁿS` and the never-entering sets `A_n` have density → 0, then every finite union of orbits has
  density 0.  The reason: an orbit lies in `σⁿS ∪ A_n` except for `2n` points.  For RCWA maps with
  periodic `S`, both sequences are exact periodic densities, so they can be checked.
* **Proved instances.**
  * `κ` (modulus 6, slopes 2, 2/3, `p = 2`): `d(A_n) = (5/12)(2/3)ⁿ`, forward rate `0.9196`.
  * `σ_τ = τ_{1(2),2(4)} ∘ U` (`p = 3`): forward core `3⁻ⁿ/4`, `d(A_n) = (1/2)(3/4)ⁿ⁻¹`.  I re-checked
    both by box counting (`scripts/amusical/cores.py`, exact match for `n ≤ 8`).
  * 31 of the 32 single class-transposition perturbations `π ∘ U` that have a cone, by an exact
    automaton (not re-derived).
* **The gate.**  `U` has no periodic cone: its residue graph mod `M` is strongly connected
  (`seventh.md` T4; `scripts/amusical/cone.py` for `M ≤ 200`).  So Theorem T is vacuous on `U`
  and on the 255 residue-transitive perturbations.
* **Boundaries.**
  * Valuation 1 at *some* prime on each piece is not enough: an RCWA conjugate of translation has
    slopes `3/2, 2/3` only and one orbit.
  * No RCWA conjugate of translation lies in the class, even with infinitely many pieces.
  * "`v_p = 1`" is equivalent to "`v_p ≥ 1`", by suspension.
* **Necessary condition for a counterexample.**  A positive-density orbit needs arbitrarily long
  windows whose slope product is within polynomial factors of 1.
* **Search.**  4,540 random members (`p = 2, 3, 5`) all show linearly growing orbit counts.
* **Literature.**  The conjecture does not appear in Kohl's thesis or the RCWA manual.

## 16. A residue-transitive member with infinitely many orbits (2026-10-13, "transitive" agent, checked)

Lean: `AmusicalPingPong.lean` (the abstract engine theorem and `U`'s Theorem L are targets).  This
is the first residue-transitive RCWA permutation in the anti-Kohl class with *provably*
infinitely many orbits.  The agent found no prior example (~80% that it is new).

* **`PP(0)`.**  Modulus `13300`, `9711` pieces, slopes `3/4, 3/2, 3, 21/5, 15, 75/7` (all `v₃ = 1`).
  * Four linear "engine" pieces run a two-counter ping-pong on `(v₅, v₇)`, with phase `x mod 19`.
  * Seeds (`v₅` odd, `7 ∤ x`, `x · 8^(v₅ x) ≡ 1 mod 19`) stay in the engine forever.  Seeds prime to
    `3` start distinct orbits, at density `2/399`.
  * No orbit contains a class tail (steering argument).
  * The filler pieces (slopes `3/2^d`) make the map a bijection that is residue-transitive at every
    modulus.  That proof is computer-assisted: four hand lemmas plus two exact finite checks.
* **My independent checks** (`scripts/amusical/pp57/`):
  * domains and images partition `ℤ` exactly;
  * strongly connected at 8 moduli the agent did not test (`13300 · {3, 8, 27, 5, 7, 19, 11, 13}`, up
    to `359100`), with teeth: `κ` is NOT strongly connected, `U` is;
  * Lemma E: 902 of 902 odd-`A` seeds stay in the engine for 120 steps, and 181 of 181 even-`A`
    controls leak.
  * Credence: infinitely many orbits ~97%; transitive at every modulus ~88%.
* **Why it cannot transfer to `U`** (agent Theorems L and M, paper proofs, not re-derived).
  * `U` is *weakly sign-uniform*: for each prime, its slopes never change valuation sign.
  * For such transitive maps no orbit stays in the linear pieces forever (Theorem L).
  * The Cesàro limit of `σ̂ⁿ_* Haar` has full support on `Ẑ` (Theorem M).  So there is no open cone
    (killing Theorem T in every variant) and no open transversal (Proposition P generalized).
  * Hence a certificate for `U` must have empty interior in `Ẑ`.  The example lives exactly where
    `U` does not: at primes (5 and 7) where slope valuations change sign.
* **Further no-gos.**
  * No coarse valuation clock exists for any member of the class.
  * Commuting RCWA maps of a transitive map are surjective.
  * The bounded-ratio rewiring (§14) extends to the whole class.
