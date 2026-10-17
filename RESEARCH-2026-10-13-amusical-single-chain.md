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

Lean: `AmusicalContinuousReversor.lean` (proved, axiom-clean; Maze row "reversor determined by
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

Lean: `AmusicalSeventh.lean` (proved, axiom-clean, 2026-10-14).  A seventh orbit ⇔ no orbit of `U` is cofinite in `ℕ`.
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

Lean: `AmusicalGlobal.lean`, `AmusicalRewireRatio.lean` (proved, axiom-clean).  No global mechanism found; a
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
  rewiring changes it (FS density `0.213` for `U`, `0.056` for `τ` at `N = 1500`; asymptotically
  `FS_τ` is exactly `U`'s orbit minima, density `≈ c`, §31).  So it is the right
  statistic, but proving it means showing late drops are rare: the typicality wall.
* **Commuting maps.**  An orbit-moving map commuting with `U` would separate orbits, and Theorem
  C's law obstruction does not apply (both Bernoulli laws can be preserved).
  * The window-2 centralizer is exactly `0, ±1, ±id, ±U`; I re-derived this independently with
    `scripts/amusical/central_w2.py`.
  * Window 3 adds one exotic `±` pair, non-integral only numerically.
  * Believed (~85%): the continuous centralizer is `{0, ±1, ±Uʲ}`.

## 15. The anti-Kohl conjecture (2026-10-13, "antikohl" agent, checked)

Lean: `AmusicalAntiKohl.lean`, every statement proved and axiom-clean (antikohl treadmill, 2026-10-14).  The
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

Lean: `AmusicalPingPong.lean` (engine theorem and `U`'s Theorem L proved, axiom-clean).  This
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

## 17. Weakly sign-uniform maps (2026-10-13, "uniform" agent, checked)

Lean: `AmusicalUniform.lean` (M4 for `U` and the `δ` bijection proved; NR_p, the Island Lemma,
M3 for `U` and `δ`'s finiteness are targets).  The question was whether a weakly sign-uniform (WSU),
residue-transitive map can have provably infinitely many orbits.  It is still open; the agent puts
≤ 10% on any known certificate type producing one.

* **Theorem NR_p.**  Suppose every slope has `v_p ≥ 0` at one prime `p` and `v_p` accumulates along
  orbits.  Then no piecewise-affine bijection reverses the map.  Being one-signed at `p` suffices;
  `v_p = 1` is not needed.  The Gaussian `H` escapes only because complex conjugation is semilinear.
  I hand-checked the proof (a valuation count on one infinite refined cell).
* **Island Lemma.**  A cycle mapped to itself by an RCWA reversor has slope product `±1`, so the map
  is the identity to order `2L` on a residue class and is not transitive.  I hand-checked it (the
  reversor slopes telescope).  It kills all 1400+ random involution-product candidates.
  * Conjecture B2 (~60%): no transitive RCWA map has an RCWA reversor fixing a class.
* **Theorem M3 / M4** (paper proof, not re-derived).  A WSU transitive map is topologically
  transitive on `Ẑ`.  So an orbit invariant takes equal values on any two classes where it is locally
  constant.  This kills every invariant built from finitely many valuations, leading digits or
  `S`-free parts, and all locally constant factor maps.
* **More no-gos (paper).**
  * An eventually periodic itinerary forces a cycle (Lemma EP).
  * RCWA factors inherit the full-support measure.
  * Each length has finitely many cycles.
  * Transitive maps with all slopes `±1` have finitely many orbits.
* **Side example `δ`.**  A product of two class-transposition involutions with slopes `2/3, 1, 3/2`.
  Every orbit is finite, with an explicit dihedral invariant.  It is strongly connected mod 12–48,
  96 and 108, but not mod 60, 72 or 144.
  * My check `scripts/amusical/delta_ren.py`: bijective on a window; 10003 finite cycles through
    `[−30000, 30000]`; SCC counts, with `U` strongly connected at every listed modulus as control.
  * Correction: the agent wrote "transitive up to 60"; it already fails at 60.
* **Still open: digit automata.**  These reduce to lacunary families `{α Qⁿ + β}`.  For `U` the powers
  `2ⁿ` share orbits only at `{2³, 2⁵}` and `{2⁴, 2⁹}`.  The agent's reading (~85%): WSU maps multiply by
  their primes and never divide them back out, so every surviving certificate needs Collatz-type
  control of single orbits.

## 18. No new cycles of length ≤ 31866 (2026-10-13, "cycles" agent, checked)

Lean: `AmusicalCycleBound.lean`, every statement proved and axiom-clean (2026-10-14).  Theorem 1
holds conditional on the external search certificate.  Theorem A★, the reduction, and the bound
computation (`cycleMinBound_31866`, one `decide +kernel`, 3.1 GB) are proved.  So is **Atkin 1966 in the
kernel** (`amusical_noNewCycles_199`): a `Bool` search checker, sound by `searchCheck_sound`.  Klamkin (b) and C4
stay open.

* **Theorem A★.**  A cycle's *minimum* is polynomially bounded by its length:
  `3^p (3m−1)^k ≤ 2^e (3m)^k ≤ 3^p (3m+1)^k`.  Its elements are not.  This replaces Collatz's
  "everything small converges" check, which `U` lacks.  I hand-checked it: the cycle product
  telescopes to `2^e ∏ 3x = 3^p ∏ (3x+d)`.
* **Theorem 1 (computer).**  Every periodic point of period `≤ 31866` is a known cycle member.
  Atkin 1966 had `< 200`, so this is 160× further.
  * The bound gives `m ≤ 167195612`.  I re-derived it exactly (`scripts/amusical/cycles/x0_ren.py`).
  * Agent search (`cyclemin.c`, lockstep `U`/`V` with meet-in-the-middle at `H = 15933`):
    0 cycles, 8.3 M survivors, 2.66·10¹¹ steps.
  * Independent re-run with my own forward-only GMP search (`fwd_ren.c`, a different algorithm and
    code), with teeth (finds 44 at period cap 12, misses it at 11): **confirmed**.  All of
    `[1, 167195612]` in 400 contiguous chunks, `1.12·10¹²` exact steps.  The only returns are
    1, 2, 4, 44; dips + survivors + returns = the range size (`logs/fwd_ren-summary.txt`).
  * `defs_teeth.py` checks the Lean definitions literally: `CycleMinSearch 173 6` is clean, and
    fails at 44 when 44 is not skipped.
* **Theorem 2 (computer + Rhin 1987 as quoted by Simons 2022).**  Every new cycle has at least 33
  local minima.
  * It uses Lemma R (`log₂ m ≥ (2p−e)(θ−1)/(θ^r−1)`, by chaining local minima) and the A′ bound
    `m ≤ 1 + r/|Λ|`.
  * Search to `2·10¹⁰`.
  * Simons 2022 had `m ≤ 2` complete.
  * Not in Lean: Rhin's bound is not yet a `Literature` Prop.
* **Structure.**
  * Cycle minima are `≡ 2, 4 (mod 6)`.
  * E-frequency `= 2 − θ ± 0.37/(m−1)`.
  * If `m > 0.57 p²`, then `p` is a multiple of a convergent denominator of `log₂ 3`.  This makes
    Shanks 1965 precise.
* **Gates.**
  * Bounding every element is exponential: only the minimum is polynomial.
  * "Every element of a long cycle is large" is out of reach, since nothing bounds a cycle's
    minimum from below except through its run count.  A cycle through 8 of length `10¹⁰⁰` is not
    excluded.  C4 credence ~3%.
* **Novelty** (agent, ~85%): the 31866 bound, the minimum-search method, and the `r ≤ 32` theorem.

## 19. Empty-interior certificates (2026-10-13, "emptyint" agent, checked)

Lean: `AmusicalFormalMin.lean` (Theorem F and the formal-walk counterexample proved, axiom-clean;
Proposition G1 is a target).  Every natural empty-interior candidate is either dead or stuck at the
per-orbit infinite-horizon wall (Proposition S, orbit of 8).  Agent: under 1% toward a seventh
orbit.

* **Formal minima `FM = ℤ ∩ (W₂ × W₃)`** (Theorem F, hand-checked).
  * At most one point per orbit; no periodic points; `FM = −FM`; meets every thin orbit exactly
    once; upper density `≤ c`.
  * Certifying one FM point proves its orbit infinite.
  * On `[1, 10⁶]`, FM equals the orbit minima exactly (49957 each).
  * The formal walk can mis-order near ties of `t log₂ 3`: `U¹² 31 = 30`, while `2¹⁹ < 3¹²` (proved
    by `decide`).
* **Proposition G (resolution gate, paper).**  If some orbit is infinite, every height
  `F(x mod M, ⌊log₂ x⌋)` with bounded cocycle is bounded.  The same holds for growing
  `M(s) | 2^∞3^∞N₀` with `M(s) ≤ 2^{s/10}`, and transversals defined by residues at resolution
  `2^{s/(10(K+1))}` are dead (G2′).
  * So a certificate must read `Ω(log x)` digits.
  * Open: a growing prime-to-6 modulus (needs a diameter bound for the affine action).
* **Archimedean invariant (paper identities).**
  * On thin orbits (`Σ 1/y < ∞`), `Q(O) = ∏(1 + χ₄(y)/(3y)) = L₊/L₋` is an orbit invariant.
  * `Δ = L₊ − L₋` depends on the itinerary alone, and `η = x/|Δ|` is a summable-cocycle height.
  * Teeth: `|Q_H| = 1` on conjugation-symmetric orbits of the Gaussian H (to 1e-14).
  * `Q = 1` for `U` would need an archimedean reversor, which Theorem NR excludes.
  * Separating orbits by `Q` is "no late return", the Proposition S wall again.
  * All 1002 orbits with minimum `≤ 2·10⁴` have distinct `Q`.
* **Dead.**
  * Tail and digit statistics: Kolmogorov 0-1, plus normality, which is believed but unprovable.
  * Weighted transversals `φ(x)/x`: alive, but weaker than `AtLeastLinearGrowth`.
* Consistency check: `E[m · W(O_m)] = 19.98`, against `1/c = 20.09`.

## 20. Late drops: the typicality wall pinned (2026-10-13, "survival" agent, checked)

Lean: `AmusicalLateDrops.lean`, all proved, axiom-clean (S′, Theorem LD, LD′, the calibration,
the tilt identity); reopen condition `AmusicalLateDropsSparse`.  Klamkin (a) is not
settled.  The wall is now one count: the integers that survive past the residue horizon
`T(X) ≈ log₃ X` and are undercut later.  Agent: under 1% toward settling (a).

* **Constants** (agent's are paper proofs; I re-derived them in
  `scripts/amusical/survival/consts_ren.py`, to 12 digits).
  * `p_f = 0.210136239317` and `p_b = 0.236891833789`, with `p_f p_b = 0.04977956 = c`.
  * Each equals `1/E[first strict ascent time]` (Feller XII.7).
  * Tilt duality `E_b e^{−θY} = E_f e^{−(1−θ)X}`, so both directions share the rate
    `ρ = 0.985597`.
* **Numerics** (agent, all `x ∈ [16, 2³¹)`).
  * FS `0.2101358`, BS `0.2368935`, minima `0.0497804`, all within `2·10⁻⁶` of the walk.
  * Beyond the provable horizon (`L = 20–200`), integers match the walk's late drops to 0.5%.
  * The twin `W_{3,1,2}` gives the same numbers.
* **Theorem LD.**  Late droppers below `(c − η)X` infinitely often give (a).
  * At the walk's rates it fires from depth `L = 23`, and at `K` times the walk's rates at a larger
    depth (`L = 50` for `K = 2.65`, `L = 100` for `K = 10.7`).
  * One-sided control fails: perfect forward typicality still needs backward survivors at
    `≥ 79%` of `p_b`.
* **U vs `τ`.**  Forward/backward window independence is proved; typicality beyond the horizon is
  open.  `τ` has `U`'s windows but maximal late drops.
* **New obstructions.**
  * In `ℤ₂` the survival set's boundary is the whole set, so equidistribution gives only the upper
    bound.
  * `U` climbs in both time directions, so Tao-style renewal fails.
  * The first-rise (Feller) route is killed by `τ`.
* **Calibration.**  A positive lower density of *strict* survivors would already exhibit an
  aperiodic orbit, which is open.

## 21. The `𝔽₂[t]` twin has infinitely many orbits (2026-10-13, "freeform" Fable agent, checked)

Lean: `AmusicalFunctionField.lean`, every statement proved and axiom-clean (Theorem F by the
fftwin treadmill, 2026-10-14).  This is the clean split of Klamkin (a) into a
Diophantine half and a dynamical half.

* **The twin.**  `(ℤ, 2, 3) → (𝔽₂[t], t, Q)` with `Q = t² + t + 1`.  Haar balance forces depths
  `(1, 2, 3, 3)`.
  * It is residue-transitive at 18 tested moduli.
  * Degrees change by exactly `+1, 0, −1`.
  * The forward and backward walks have the same law, so `p_f = p_b = 1/4` and the heuristic
    orbit-minimum density is exactly `1/16` (measured `0.06271`).
* **Theorem F (PROVED).**  For `p = 2^e ≥ 8`, `m = p/2`, `(t⁴+t³+1) t^m (t+1)^(m−3)` has exact
  period `p`, with itinerary `E^m B^m`.  So the twin has infinitely many cycles, hence orbits.
  * The proof never touches an infinite orbit.  Frobenius collapses the Böhm–Sontacchi
    denominator: `t^{2p} − Q^p = (t+1)^p`.
  * For `Q = t² + 1` the denominator is `1`, and every balanced word of length `2^e` closes.
  * I re-checked it independently (`scripts/amusical/twin/fftwin_ren.py`, own carry-less
    arithmetic): exact periods and itineraries for `p = 8 … 256`.  Teeth: `p = 10, 12, 14` and
    `s_E ≠ 0` do not close.
* **Heuristic exact in the limit.**  Cycles of length 8, 16, 32 number 9, 299 (exact) and about
  `2.76·10⁶`, against the heuristic `3.6`, `233`, `2.69·10⁶`.  The ratio tends to 1.
* **What fails over `ℤ`.**  `E^m B^m` closes at `2^m(4^m−3^m)/(9^m−8^m)`, an integer only at
  `m = 1` (`amusical_EmBm_not_integral`).  The missing identity `(a^m−b^m)/(a−b) = (a−b)^{m−1}` is
  smallness of `2^N − 3^p`, which Mihăilescu and Baker forbid.
  * Since cycles of `U` are believed finite (§5, §18), **any proof of Klamkin (a) must exhibit
    infinitely many infinite orbits**.
  * Every wall ports to the twin, and even "one infinite orbit exists" is open there.

## 22. Complexity of orbit counting; Theorem W (2026-10-13, "logic" Fable agent, checked in part)

Lean: `AmusicalLinearForever.lean`.  Theorem W is **proved, axiom-clean** (Ren's proof).

* **Theorem W.**  If some `x ≠ 0` has a forward orbit that only uses zero-offset pieces, then the
  points `u x` (`u ≡ 1 mod m`, prime to all slope primes) are distinct orbits.  So the map has
  infinitely many orbits.
  * This is the single mechanism behind every provable certificate so far: `PP(0)`'s engine in one
    line, and the reason certificates for `U` must have empty interior.
  * It is vacuous on `U`, because no orbit stays on `2n ↦ 3n` (Theorem L).
* **Complexity** (paper, not re-derived), for RCWA permutations given by tables:
  * "x ~ y" and "x periodic" are `Σ⁰₁`-complete;
  * "∃ infinite orbit" is `Σ⁰₂`-complete, and "all orbits finite" is `Π⁰₂`-complete;
  * "finitely many orbits" is `Π⁰₂`-hard, with the naive upper bound `Π⁰₃`.
  * The machinery: Morita reversible 2-counter machines as linear pieces, a Bennett wrapper, and a
    one-orbit "highway".
* **The gap `Σ⁰₂` / `Π⁰₃` is exactly universal *additive* (Collatz-like) computation, i.e. `U`'s
  class.**  Agent credence: 70% Π⁰₃-complete; 30% a genuine collapse, which would be a theorem
  about U-like maps.
* **Independence** (paper, "in principle", no table built).  There is an explicit computable RCWA
  permutation with one orbit iff `Con(ZFC)`.  The agent puts 90% on a `C₃` variant and 80% on a
  residue-transitive one.
* Lagarias's C4 fails non-trivially for some members of the class: sibling cycles of one length.

## 23. The twin's cycles are graded by `v₂(p)`; Frobenius is half an intertwiner (2026-10-13, "twin2" Fable agent, checked)

Lean: `AmusicalTwinDegree.lean`, every statement proved and axiom-clean (twindeg treadmill, 2026-10-14).
The agent did not find an infinite orbit of the twin.  It puts 99% on one existing and about 2% on
the twin's extras making one provable.

* **Theorem D (PROVED, paper; I checked the proof).**  A non-exceptional cycle of period
  `p = 2^v q`, `q` odd, has minimum degree `≤ 2^v + 2`.
  * D1: `deg(t^{2p} − Q^p) = 2p − 2^v`.  Frobenius reduces to `q` odd, where the `t^{2q}` terms
    cancel and the `t^{2q−1}` coefficient is `q ≡ 1`.
  * D2: at the minimum every term of `c_w` has degree `≤ 2p + 2`, since the degree walk `S_j ≥ 0`.
  * The walk `+1, 0, −1, −1` is exact except at `m = 0` in each class.  Those are exactly the four
    exceptional points `0, 1, 1 + t, Q` (two fixed points and the 3-cycle `t → Q → 1 + t`).
  * Tight up to one: Theorem F's cycles have minimum degree `p + 1` at `p = 2^e`.
  * I re-checked it independently (`scripts/amusical/twin/twinD_ren.py`, own code): D1 for
    `p ≤ 400`, and Theorem D on all `113` cycles through polynomials of degree `< 16` (periods 8,
    16, 20, 32, 48, 64).  Teeth: the bound without its `+ 2` fails on period 8.
* **Corollaries (PROVED from D).**  Each 2-adic class `v` holds at most `2^{2^v+3}` cycles, over
  all odd `q` together.  With Theorem F the valuations are unbounded, so the cycle structure is
  graded by `v₂(p)`.  A periodic polynomial of degree `d` has period `≥ (2d − 4)/3`.  Any odd
  balanced cycle passes through one of 11 polynomials of degree `≤ 3`, all followed above degree
  120 (agent's `census.c`), so such a cycle has period `≥ 236`.
* **Contrast with `ℤ`.**  Theorem A★ (§18) is stronger per period (a cycle minimum is `≤ p^C`) but
  has no uniformity in the odd part: `|2^N − 3^p|` grows with every `p`, while the twin's
  denominator sees only `v₂(p)`.
* **Frobenius on `E ∪ A` (PROVED).**  `U²(n²) = (Un)²` there, the one symmetry `ℤ` lacks (the
  window-2 centralizer of `U` is `0, ±1, ±id, ±U`, §14).  It fails on `B, C`, because the class read
  `n mod t³` forgets `n₂`, and Haar balance forces depth 3 for every `𝔽₂[t]` twin.
  * Numerically the orbits of `n` and `n²` decouple: `deg U^{2j}(n²) − 2 deg Uʲ(n)` spreads like two
    independent walks (sd 40 at `j = 400`).  For all 1313 periodic points inside degree 18 with
    period `≥ 3`, `x²` is not periodic.
  * **No class-wise constant repair (PROVED, my proof).**  The agent's §7 argument mixes up a depth
    (`n²` is in `A`, not `B`).  My route: `n = 0, 1` force `U²κ_E = κ_E` and `U²(1+κ_A) = 1+κ_A`.
    Such points have degree `≤ 5` by the period bound, and a search finds only `0, 1`.  Then
    `n = 1+t` and `n = Q` determine `κ_B, κ_C`, and all four candidates fail at `n = t`
    (`scripts/amusical/twin/classwise_ren.py`; teeth: the pure square passes on `E ∪ A`, fails on `B`).
  * Proposition M (PROVED): a self-similar point `z² + c ∈ orbit(z)` certifies an infinite orbit,
    given an intertwiner.  None exists here; the statement keeps the certificate shape.
* **Walls.**  Exact-height counting is a costume for the closing-word count
  `#{w : (t^{2p} − Q^p) | c_w}`, the twin's own Diophantine half.  Periodic points look t-adically
  and Q-adically dense (BELIEVED 85%: cycles inside degree 24 meet every cylinder of depth 6), so
  the twin's residue adversary is an actual polynomial.  In that respect the twin is harder than `ℤ`.

## 24. Kohl's determinant is the net crossing of `0` (2026-10-14, "bridge" Opus agent, checked in part)

Lean: `AmusicalCrossing.lean`, proved and axiom-clean.  The agent's question was whether operator
algebras, groupoids or self-similar groups give an invariant that (a) is computable from residues,
(b) separates `U` from `ω` and `τ`, and (c) bounds the orbit count.  Its answer for `U` is no.

* **Theorem I (PROVED, paper; three-line proof, read).**  For class-wise order-preserving `σ`,
  Kohl's `det σ = Σ b/(a m)` equals `#{x < 0 ≤ σx} − #{x ≥ 0 > σx}`.  That is the Fredholm index of
  `σ` compressed to `ℓ²(ℕ)`, and also Matui's index map.  Proof: canonical pieces
  `r + a k ↦ s + b(k + j)` give `det = Σ (s/b + j − r/a)`, and Rump's identity `Σ r/m = (n−1)/2`
  cancels the fractions.  Kohl had called det unintuitive, found by computer.
  * My check (`scripts/amusical/flux_ren.py`): Kohl's formula = brute-force flux on nine twins
    `W_{a,b,c}`.  Teeth: `U` gives 0, and a window missing the crossing misses it.
* **Corollary (PROVED; Lean `not_periodic_of_upCrossing`).**  `σ` has at least `|det σ|` infinite
  orbits, since a finite orbit carries no net flux.  This is a fourth certificate type, disjoint
  from reversal, Frobenius and Theorem W.
* **The statistical twin has an infinite orbit (PROVED; Lean `twinW_zero_not_periodic`).**  `twinW`
  (`AmusicalTwin.lean`: U's cylinder laws, densities and coding, plus a 3-cycle) maps `ℕ` into
  `ℕ ∖ {0}`, and its only crossing is `−2 ↦ 0`.  `W_{3k,1,2}` has at least `k` infinite orbits.
* **Silent on `U` (PROVED; Lean `amusical_no_crossing`).**  `U` preserves sign, so it has no
  crossing.  The agent also shows every residue-computable channel into `K_0 = ℤ[orbits]` is this
  index, and that traces and KMS states do not see orbits.
* **Literature check (2026-10-14, verifier agent, primary sources opened; `out/kohl-verify.md`).**
  * **Kohl's thesis §2.13 (p. 65) has 8 open questions** (verified).  The first two: is
    `RCWA(ℤ) ▷ ker sgn ▷ 1` a composition series, and are `ker sgn`, `ker det` simple?
  * **The groupoid input is published.**  Bruce–Kubota–Takeishi (arXiv 2407.01952, JFA 2026) study
    the `ax+b` groupoid on `Ẑ`: `H₀ = 0`, `H₁ = ℤ/2`, and `[[𝒢]]^ab = ℤ/2` with simple commutator
    subgroup (their Thm 5.7, via Matui Thm 4.16 and Li Cor. 6.14).  The bridge agent did not cite it.
  * **The one new step is `RCWA(ℤ) ≅ [[𝒢]]`.**  The verifier re-proved it by hand (~90%) and found
    no paper stating it (abstract-level search only).  With BKT it answers Kohl's question for
    `ker sgn` (~85%): the normal subgroups of `RCWA(ℤ)` are `1`, `ker sgn`, `RCWA(ℤ)`.  It would also
    settle Kohl's Conjecture 6.8 (Math. Z. 2010: `RCWA(ℤ)` is generated by tame elements), still a
    conjecture in RCWA manual 4.10.2.  The `ker det` case (~75%) needs `H₁(𝒢⁺) = ℤ`, not found in
    print.  `ker sgn = CT(ℤ)` is false: `CT(ℤ) < K̃⁺ ≤ ker det ≤ ker sgn`.
  * **Kohl's ω:** Kohl computed `det ω = 1` himself (thesis B.6, pp. 88–90) and states one infinite
    cycle plus 9 exceptional points without proof.  "ω has an infinite orbit" follows from Theorem I.
    "Only one" remains unproved.
  * **Lagarias #176 (verified quote, math/0309224 pp. 65–66):** the open problem is that *every*
    such permutation has an infinite orbit.  `twinW` meets the hypotheses, but its infinite orbit is
    trivial.  The determinant criterion covers only the easy nonzero-flux cases, so "settles an
    instance" overstates it.

## 25. The adelic space is a costume; one orbit can pass for `ℤ` (2026-10-14, "quasicrystal" Opus agent, checked in part)

Lean: `AmusicalAdelic.lean` (Proposition L in rational form, proved and axiom-clean).  The angle: `ℤ` as a
model set in `K = ℝ × ℤ₂ × ℤ₃`, with `U` extended to `Û` by its affine formulas.  Does a rigidity or
measure-classification property of `Û` force infinitely many orbits on the diagonal?  No.

* **Theorem M, Masquerade (PROVED by the agent; I read it but did not re-derive the construction).**
  Either `U` has infinitely many cycles, or for every `ε` one `Û`-orbit shadows `ι(ℤ ∖ 0)`.  It
  stays within `ε` off a density-0 set, has `o(X)` extra points per box, and agrees with `U` off
  `O(log² X)` places.  So every Haar, box-count, Delone or finite-window argument on `K` fails,
  unless it proves infinitely many cycles.  Unlike the rewired `τ` (§14), this is `Û`'s own
  dynamics.
  * Proof: Theorem R-style cuts (§14), glued by a new Steering Lemma (signed-sum covering plus
    approximation of `log₂ 3`).  The demo (`scratch-quasicrystal/masq.py`, the agent's): one orbit
    piece covers all 2980 non-periodic integers in `[1, 3000]` exactly once, with the same
    cylinder table.
  * It answers `adelic.md`'s open C7 (that agent had put 60% on yes).
* **Proposition L (PROVED; I checked it).**  A `Û`-invariant subgroup with a point of odd 2-adic
  coordinate contains `ι(ℤ)`, since `4Ûv − 3v = ±ι(1)`.  The invariant lattices are exactly
  `(1/q) ι(ℤ)`, `gcd(q, 6) = 1`.  So invariant subgroups give back Klamkin (a) for `U_q`, nothing more.
* **Corollary S_K (PROVED; I checked it).**  One orbit with the lattice's window statistics has
  forward plus backward survival density `≤ p_f + p_b − p_f p_b = 0.3972`.  The product `p_f p_b` is
  `c`, the orbit-minima density.  `ℤ` measures `0.4470` (§20).  So survival is exactly where the
  masquerade must fail, the §20 wall again.  The proof uses one strict minimum per orbit.
  * Open Q1 (agent: 50%): does some single orbit reach `0.3972`?  If so, Proposition S's threshold
    is sharp.

## 26. One-sided survival suffices; the single-orbit ceiling is `c` (2026-10-14, "q1sharp" Opus agent, checked in part)

Lean: `AmusicalSurvivorSeparation.lean`, proved and axiom-clean (Ren's proofs).  The agent answered
§25's Q1 negatively: the single-orbit survival ceiling is `c = p_f p_b ≈ 0.0498`, not `0.3972`.

* **Separation (PROVED; Lean `fwdSurvivor_three_separation`).**  If `n < n'` are forward survivors
  on one orbit and `3 ∣ n'`, then `3n ≤ 2n'`.  `n'` cannot precede `n`, and the step before `n'` is
  `U⁻¹ n' = 2n'/3`.  So **forward survivors divisible by 3 in `[X, 3X/2)` lie on distinct orbits**,
  each infinite (`fwdSurvivor_three_not_periodic`).
* **Reduction (PROVED; Lean `infinitelyManyOrbits_of_fwdSurvivors_three`).**  If such windows hold
  unboundedly many of them, i.e. `FS ∩ 3ℤ` is not `O(log X)`, Klamkin (a) holds.  Under finitely
  many orbits every multiple of 3 that survives a fixed window is a late dropper, except
  `O(log X)` of them.
* **Ceiling C1 (PROVED by the agent; re-derived unconditionally in §31).**  One orbit, or finitely many,
  with the lattice's window statistics has `FS ∪ BS` of upper density `≤ δ_L` for every `L`, hence
  `≤ c`.  The mechanism: a forward survivor whose backward window first drops at time `g` has
  `Vᵍ n` as the next lower survivor of its orbit, and Lemma K forces a height gap `≥ m'/4ᵍ − 1`.
  * Consequence (C2′): **`d_upper(FS) > c` implies Klamkin (a)**, which needs forward survivors at
    only `c/p_f = 23.7%` of their measured density.  This overturns §20's "one-sided control
    fails", which holds only for the S′ counting method.
  * At the walk's late-drop rates the fixed-depth version fires from window depth 3, where Theorem LD
    needs depth 23.
  * Sharpness: conditionally, a re-tuned masquerade makes every orbit minimum a forward survivor.
    Unconditionally the agent puts 85% on reaching `c`, leaning on Theorem M's accounting.
  * Checks (agent's, `scratch-q1sharp/`): the predecessor and separation lemmas have 0 failures on
    `[2⁸, 2²¹)`.  Teeth: a false `2ᵍ` strengthening of Lemma K is caught.
* **The wall is unchanged in kind.**  The rewired `τ` satisfies every hypothesis, so lower-bounding
  survival is still the typicality wall, now one-sided at 23.7%.

## 27. The additive side is closed; the twins are translates of layer maps (2026-10-14, "ringadd" Opus agent, checked in part)

Lean: `AmusicalAdditive.lean`, proved and axiom-clean.  Agent credence that any of this moves
Klamkin (a): under 1%.

* **Theorem T (PROVED by the agent; I checked the `q = ±1` family by hand).**  Every twin
  `W_{α,β,γ}` equals a layer map `U_q` (§5) plus `d = (α+β+γ−3)/3`, after a unique even
  translation, with `q = 3 − 2(γ−β)`.  Checked on all 6600 twins with offsets `|·| ≤ 15`.
  * So the §12 statistical twins are `Û + c` restricted to `(1/q)ℤ`, and Kohl's det of a twin is `d`.
  * `twinW x = U(x + 4) − 3`, i.e. `U + 1` conjugated by translation (Lean `twinW_eq_translate`).
  * Every det-0 twin contains a copy of `U`, so a det-0 twin with finitely many orbits would
    disprove Klamkin (a).
  * T4: `U` is the only residue-transitive twin with zero flux.  Every other transitive twin has a
    provably infinite orbit (§24).
  * T5: for every rational `c ≠ 0`, `Û + c` has infinitely many infinite orbits on `ℚ ∩ ℤ_(6)`,
    from flux on nested layers.  At `c = 0` this is open.
* **Carry cocycle (REFUTED as finitely valued; Lean `amusical_carry_unbounded`).**
  `U(x+y) − U(x) − U(y)` is unbounded (`6k + 1` at `x = y = 4k + 1`).  An additive Theorem W is
  vacuous, since the itinerary codes `ℤ₂` injectively.
* **Theorem G (PROVED by the agent).**  An automorphism of an infinite abelian group has infinitely
  many orbits.  So "U respects a group law on the non-periodic integers" is a costume for infinitely
  many infinite orbits.  On all of `ℤ` it is impossible by Lagrange (`|Fix U| = 3`, `|Fix U²| = 7`).
* **The `𝔽₂[t]` twin is additive on triples of one depth.**  Over `ℤ` an exact carry in `{0, ±1}`
  turns the twin's linear algebra into a knapsack problem, which only reorganises cycles.
* **Baker contrapositive (REFUTED).**  Along an orbit segment, `j log 3 − n log 2 = log(y/x) − S`
  with `S` the archimedean carry.  Proposition D: the relations that finitely many orbits forces
  are Dirichlet-sized (`|Λ| ≲ 1/J` at lag `≤ J`).  Every irrational satisfies these, so no lower
  bound for linear forms in `log 2, log 3` can contradict them.

## 28. Multiplicative symmetry reduces to 2-adic irrationality (2026-10-14, "ringunit" Opus agent, checked in part)

Lean: `AmusicalUnit.lean`, proved and axiom-clean, plus the wall's reopen condition
`AmusicalSharedSkeleton`.  Agent credence that this route proves Klamkin (a): under 1%.

* **Proposition T (PROVED by the agent).**  A map commuting with `U` along a forward orbit tail and
  asymptotically `×u` (`u ∉ ±2^ℤ3^ℤ`) moves that orbit to a different one.  Transport is free.
  * Such a map exists iff two integers share an infinite parity skeleton.  That happens iff an
    infinite, co-infinite sub-series of `x = −Σ χ₄(Uʲx) 2^{nⱼ}/3^{j+1}` sums to an integer.
    (Negation `z = −y` is the full series.)  Believed to have no solutions (~95%).
  * Search: no pair `y < z ≤ 2·10⁵` shares more than 34 skeleton steps (random model about 1.2 at
    34).  Teeth: a cross-layer search finds the allowed U-cycle / U_q-cycle matches, e.g.
    `q = 13 = 2⁸ − 3⁵` with the 5-cycle.
* **Theorem A (PROVED).**  An affine map `vy + e`, `v ∉ {0, ±1}`, commutes with `U` on at most one
  branch class.  New example (Lean `amusical_three_mul_sub_four`): `3y − 4` on `1 + 4ℤ`.
* **Proposition N (exact; Lean `two_mul_not_orbit_map` for `u = 2`).**  `×u` fails to map orbits to
  orbits for 12 tested `u`.  For `u = 2`: `22` and `29 = U⁻¹ 22` share an orbit, but `44` (12-cycle)
  and `58` do not.  For `u = 13` the same failure would already give a seventh orbit.
* **Theorem D (PROVED).**  "Every orbit meets the defect set finitely often" is circular: an infinite
  defect set already proves (a).  The forward-only version is the §17 wall.
* **Theorem U (PROVED).**  A `×u`-closed set of integers has closure with interior in `ℤ₂ × ℤ₃`, so
  formal minima are never multiplicatively closed.  Conjecture LF (implies (a)): `uᵏ x` hits formal
  minima at a ball's Haar rate.  Numerics beyond the residue horizon match within about 1σ in 8
  families (e.g. `5ᵏ · 8`: 0.245 vs 0.226).
* **Theorem A★_u, twisted cycles (PROVED, Baker as a literature Prop).**  If `Uᵗ x = u x`, the
  segment minimum is polynomial in `t`.  857 such returns for `x ≤ 2·10⁴`, `t ≤ 400`, with 0 bound
  violations.  The most frequent multiplier is `u = 79 ≈ 3³³/2⁴⁶`.

## 29. The deformation `Û + c` has a degenerate point at `c = 0` (2026-10-14, "deform" Opus agent, checked in part)

Lean: `AmusicalDeform.lean`, proved and axiom-clean (Ren's proofs).  Agent credence that this route
moves Klamkin (a): under 1%.

* **Prop R (PROVED; Lean `amusical_add_roots_distinct`).**  For an integer `d > 0`, `U + d` sends `ℕ`
  into `[d, ∞)`, since `U` preserves sign.  So `0, …, d − 1` lie on `d` pairwise distinct infinite
  orbits.  The agent adds that these are exactly the landing points of the `d` up-crossings (§24).
* **The degenerate point.**  At `d = 6^N → 0` in `ℤ₂ × ℤ₃` the itineraries agree with `U`'s for
  about `N/1.5` steps forward and `N` back.  Yet every point of `[0, 6^N)` is on its own infinite
  orbit, `U`'s 5-cycle included.  The cycle's branch word survives only when `13 | d`, at
  `4 + 862d/13 → ∞`.
  * Mechanism: `U`'s orbits solve `m = A_w(n)` (the Böhm–Sontacchi system).  Every `c ≠ 0` shifts
    them to `m − A_w(n) = c·P_w`, `P_w ≥ 1`, and the solution sets have no limit as `c → 0`.
  * Small denominators fuse orbits instead: at `c = 1/5` the points `0, 1, 2, 3, 8` and the 5-cycle
    lie on one orbit.  Real-small `c` isolates them (Lemma I: no short segment joins two integers).
* **Theorem A (PROVED by the agent).**  Forward agreement of `U + c` with `U` is exactly governed by
  `v₂(c)`, backward agreement by `v₃(c)`.  The real size of `c` never affects the itinerary.
* **Theorem Z (PROVED by the agent, new).**  On every periodic invariant piece, the flux of
  `U_Q + k` is `k` times the piece's density.  Flux is `c · Haar`, linear with no mode locking.  So
  no coset of `(ℤ/Q)^×/⟨2,3⟩` carries flux at `c = 0`.  Checked on 3850 pieces and every coset for
  `Q ≤ 400`.  Lemma P: every periodic invariant piece has period prime to 6.

## 30. Staircases: the `×2` multiplier, and why the survivor count is no easier than one (2026-10-14, "lfsep" Opus agent, checked in part)

Lean: `AmusicalStaircase.lean` (Lemma St, Ren's proof) and `AmusicalPowers.lean` (P3, P3′,
treadmill), proved and axiom-clean.  P3 needs no coprimality: `y` cancels.  Agent odds that this
settles (a): about 2%.

* **The correction.**  §26 reduced (a) to "`FS ∩ 3ℤ` is not `O(log X)`".  That bar is not low: a
  single positive forward survivor divisible by 3 already lies on an infinite orbit
  (`fwdSurvivor_three_not_periodic`), which is Conway's open question.  The weakness of the count is
  illusory.
* **Lemma St (PROVED; Lean `staircase_fwdSurvivor`).**  `U(2y) = 3y`, so `3ˢy`'s orbit contains the
  staircase `2^(s−b) 3^b y`.  A staircase point at or below the top's whole forward orbit is a forward
  survivor.
* **Theorem P3, Corollary P3′ (PROVED; Lean `powers_orbit_ne`, `infinitelyManyOrbits_of_powers_log`).**  With
  `X = 2^L y`, the orbits of `3ˢy` (`s < L`) with forward minimum `≥ 3X/2` are pairwise distinct
  and infinite.  If `U` had `r` infinite orbits, all but `O(r log S)` of `s ≤ S` would fall back: the
  orbit of `2ˢ` would return below `3 · 2^((1+η)s)` after climbing to `3ˢ`.
  * Measured (`s ≤ 3000`, `η = 0.01`): only `s = 4, 5, 6, 7, 10` fall back.  Under Haar balance `1/slope`
    is a martingale, so a drop by a factor `λ` has probability `≤ (4/3)/λ` (Doob).  Measured
    `λ · P(D ≥ λ)` lies in `0.87–1.22`.
* **Exact count (PROVED, checked for `X = 2⁶ … 2¹⁸`).**  The number of infinite orbits with minimum
  below `1.5X` equals the number of crossing rungs in `[X, 1.5X)`, bracketed by `FS ∩ 3ℤ ≤ orbits ≤ FS`
  per window.
* **Gates.**  `uᵏx` families with `u` prime to 6 never feed Sep3; they act only through formal minima
  (Conjecture LF, §28).  **Twin `τ_odd` (PROVED, unconditional in §33):** it agrees with `U` on every even
  number, has `U`'s statistics, satisfies Sep3 verbatim, and has one orbit.  Under it the powers of 3
  fall back almost always.  So any proof must use `U`'s odd branch at infinitely many high points.


## 31. The survivor ceiling is unconditional, and `τ` sits on it (2026-10-14, "c1verify" Opus agent, checked)

Lean: `AmusicalSurvivorCeiling.lean` (C2, C2′ and the backward mirror; treadmill), proved and
axiom-clean, over direction-generic packing lemmas in `AmusicalSurvivorCeiling/Packing.lean`.  An adversarial
re-derivation of §26's ceiling.  I checked P′, the gap step and the count by hand.

* **C2′ is unconditional (PROVED).**  `d_upper(FS) > c` implies Klamkin (a), with no statistical
  hypothesis on the hypothetical orbits.  Finitely many orbits partition `ℕ`, so their joint window
  statistics are `ℕ`'s, which are proved (`windowMinDensity`, `windowDensityLimit`).  The only
  `U`-specific input is Lemma K.  Any `L` works: `d_upper(FS) > δ₃ = 1/6` already gives (a).
* **Value-form proof.**  This version is shorter than §26's, with no time indices, no non-periodicity
  and no dyadic sums.
  * **P′.**  If `n' < n` are forward survivors on one orbit and `g` is `n`'s first backward drop,
    then `n' ≤ Vᵍ n`.  The `g = 1`, `3 ∣ n` case is `fwdSurvivor_three_separation`.
  * **Gap.**  Lemma K backward at `n`: `n ≤ 4^L (n − n' + 1)`.
  * **Count.**  On one orbit, forward survivors in `[X/M, X)` that fail the backward `L`-window are
    spaced `≥ X/(2M·4^L)` apart, so there are at most `8M·4^L + 1` of them.  Every other forward
    survivor there is an `L`-window minimum.  Summing over `r` orbits gives
    `#FS(X) ≤ #W_L(X) + X/M + r(8M·4^L + 1)`.
* **C1 (abstract `Û`-orbits)** holds under one explicit hypothesis on the chosen orbit: its
  `W_L` count is at most `δ_L`.  That is a property of the orbit, not the typicality wall.
* **Correction to §14 and q1sharp: `FS_τ` does not tend to `0`.**
  * For `x ≤ N` in `U`-orbit `k`, `FS_τ(x) ⇔ FS_U(x) ∧ x < m_{k+1}`, where `m_{k+1}` is the next orbit
    minimum.  The agent validated this with symmetric difference 0 on the explicit chains
    (`τ` at `N = 1500` and `6000`, `τ_odd` at `3000`).
  * By that rule, `FS_τ = Min_U` exactly on every block `[2¹³, 2²³)`, at density `0.0491–0.0509`.
  * §14's `0.056` is a small-`N` excess: 9–10 points, all below 600.
  * So `τ` and `τ_odd` sit **on** the ceiling, and `c` is sharp for any window-plus-Lemma-K
    argument (BELIEVED 90%; `d(Min_U) = c` is itself unproved).
* **No-go test.**
  * Kohl's `ω` and the zigzag lack Lemma K (`|3ᵍ − 2^a| ≥ 1`), which is exactly the input they miss.
  * The statistical twins satisfy Lemma K with a constant, so C2 transfers to them.  `W_{3,1,2}`
    measures `FS ≈ 0.21`, so C2′ predicts infinitely many orbits, in line with §12.
* **Checks (agent's, `scratch-c1verify/`).**  P′, Lemma K on every link, and the chaining step: 0
  failures on `[2⁸, 2²²)`.  Per-orbit packing maximum is `≤ 7` (bounds 9–8193).  Four deliberately
  false variants fire.  A false first-pass "Lemma K failure" was a 128-bit overflow, rechecked
  exactly.
* **Where the wall now sits.**  (a) follows from proving `FS` has upper density above `c`, i.e. that
  forward survivors (measured `0.21`) are not almost all late droppers.  That is the same Π₁
  typicality as §20, with the target 4.2× below the measurement.

## 32. Conjecture LF has no joint content; the two primes decouple (2026-10-14, "lfprobe" Opus agent, checked in part)

Lean: `AmusicalDecouple.lean` (Lemma D, Corollary MD, `not_formalMin_of_three_dvd`,
`infinitelyManyOrbits_of_ray`; treadmill), all four proved and axiom-clean.  Lemma D is
`Decouple.tendsto_cnt_iInter_inter` (`AmusicalDecouple/Density.lean`); the window periodicity
behind MD is `Decouple.evPer_fwdWin` / `evPer_bwdWin` (`AmusicalDecouple/Windows.lean`).  Agent odds that this lane moves (a): under 1%.

* **Lemma D (PROVED; I checked it).**  Suppose `A_L` are eventually periodic with power-of-2 periods
  and `B_L` with power-of-3 periods.  If `⋂ A_L` and `⋂ B_L` have the limit densities `α` and `β`
  of their windows, then `⋂ A_L ∩ ⋂ B_L` has density `αβ`.  Only CRT is used.
* **Corollary MD.**  The conjectured orbit-minimum density `c = p_f p_b` follows from two one-prime
  statements: forward survivors have density `p_f`, and backward survivors have density `p_b`.
  * §20 proves the windows are independent, and Lemma D carries that independence to the infinite
    horizon.
  * With §31, `d(FS) > c` alone gives (a).  Equality `d(FS) = p_f` would also pin `d(Min) = c`.
* **LF ⇐ LF₂ ∧ LF₃ on sub-rays.**  LF₂ says forward survivors fall along the ray at the Haar rate,
  and LF₃ says the same for backward survivors.  So LF has no joint 2-adic/3-adic content.
  * ×2×3 rigidity (Furstenberg, Rudolph–Johnson, Host, BLMV) has nothing to grip.  Here `×u` is a
    zero-entropy isometry of `ℤ₂ × ℤ₃`.
  * Gate: **zero-entropy isometry, so rigidity is vacuous.**
* **Anatomy: LF = MDE + SRE.**
  * MDE is equidistribution of the middle digits of `uᵏx`, the same family as Erdős's
    ternary-digits problem and Mahler's 3/2 problem.
  * SRE is a summable rare-event statement about late drops, the shape of §30's PD.
  * Three equivalent forms (PROVED): LF, late drops along the ray being negligible, and the window
    rates being uniform in depth.
* **Theorem LH (PROVED).**  LF holds up to horizon `log₁₂ k`, a full period of `k ↦ uᵏ mod 12^t`.
  Korobov-type bounds improve only the constant (BELIEVED 75%).
* **Proposition Z (PROVED).**  A single formal-minimum hit on a ray proves an aperiodic orbit, which
  is Conway's question, so no positive lower bound is in reach.  Infinitely many hits give (a)
  through `formalMin_unique`.
* **`FM ∩ 3ℤ = ∅` (PROVED, one line).**  `V(3m) = 2m` is even.  The two known routes to (a), formal
  minima and Sep3/staircases, therefore use disjoint witnesses.
* **Cleanest open "weak LF".**  Infinitely many forward survivors on a single ray.  Proposition Z
  does not block it, but no route to it is known.  Infinitely many forward survivors in `ℕ` is
  unconditional and trivial.
* **Numerics (agent's, `scratch-lfprobe/`).**  `β` is computed exactly by period averages, and the
  control reproduces `p_f`, `p_b` to 12 digits.  This corrects ringunit's Monte Carlo value:
  `β(5, 8) = 0.23488`, not `0.226`.  Over 21 rays × 20000 members the pooled z-score is `+0.13`.
  `β ± 5%` is rejected at `|z| ≈ 4–5`.  Only 0.3–1.1% of decisions needed digits beyond the
  member's own, but a beyond-the-digits test (walks to 150 nats) also matches.
* **No-go test.**  The LF analogue is false for `τ`, `ω` and `τ_odd`, since each has finitely many
  orbit minima.  So no proof of LF can be a statistic.

## 33. The tail threshold: rewiring off any set short of whole tails fuses the chains (2026-10-14, "oddbranch" Opus agent, checked)

Lean: `AmusicalOddRewire.lean` (Theorem TT, T1★, and Sep3 for any `τ` with `τ(2m) = 3m`),
proved and axiom-clean (GL as a cut-set-parameterized copy of the §14 construction).  Maze row "odd-branch agreement off a sparse set".  I checked TT by hand.

* **Gluing lemma GL (PROVED, re-derived).**  Take any family of chains, each meeting `S` at
  unboundedly late and early times.  Rewiring only at cut points in `S ∩ [Y_k, ∞)` fuses the whole
  family into one chain.
  * At most `2k` points change at stage `k`, and junctions pair cut points of the same stage.
  * The construction is §14's trail with the cut predicate as a parameter.  It needs none of
    Theorem R's ratio bookkeeping, which is where §30's 10% doubt lay.
* **Theorem TT (PROVED, new).**  The following are equivalent, for every `S`:
  * every permutation agreeing with `U` off `S` has infinitely many infinite orbits;
  * infinitely many chains have an `S`-free forward tail, or infinitely many have an `S`-free
    backward tail.

  Proof of ⇐: an `S`-free tail stays a `τ`-ray, and disjoint forward rays never share an orbit.
  Proof of ⇒: glue the remaining chains by GL.  So a proof of (a) that consults `U` only off `S`
  is the same thing as a proof that infinitely many whole tails avoid `S`.
* **T1★ (PROVED; settles §30's `τ_odd`).**  Take `S` = the odd numbers.  No tail is `S`-free:
  forward, an `E`-run from `x` lasts `v₂(x)` steps; backward, every increase of `V` lands on
  `4q + 1` or `4q + 3`.  So for every `F → ∞` there is a `τ` that:
  * has `τ(2m) = 3m` and keeps `U`'s cycles;
  * changes at most `F(N)` points below `N`;
  * has one chain.

  It keeps Sep3, Lemma St, P3, and every window and residue statistic.  It does not keep Lemma K's
  time separation or any Π₁ statement (FS density, PD, the orbit of 8).
* **NG★ (PROVED as a dichotomy).**  Either (I) infinitely many chains each have a tail avoiding some
  class `1 mod 6^k`, or (II) for every `F → ∞` some `τ` with finitely many chains satisfies all of:
  * agrees with `U` on evens and on `3 mod 4`;
  * agrees with `U` mod 3 everywhere, so it follows the branch-residue rule exactly;
  * has `τ − U → 0` in `ℤ₂` and `ℤ₃`, so its boundary map is `Û` itself.

  (I) would itself give (a).  It is believed false (99%): 25 chains walked to `2^1500` hit `A_k` at
  the model rates `8^{−k}` forward and `(2/9)·…` backward.  So no local-to-global statement about
  `Û` can prove (a).
* **Lever (Part B).**
  * **Information, not size.**  A rewiring set chosen blind to the orbits fuses them for certain at
    `p_n = 1/ln ln n` (PROVED).  It is believed harmless below about `p_n = 1/ln² n`.  The believed
    threshold is `Σ p_n/n = ∞` (80%; 20 chains walked to `2^3000`).
  * "Affine on all odds" pins `τ` to `{U, W_{0,2,1}}`, so it proves nothing for `U` that it does
    not also prove for the twin.
  * The staircase's first odd point controls only `O(log s)` steps.
  * No perturbation of `U` is small at `∞`, 2 and 3 at once.  The 2/3-adic side is proved, the
    bounded side is a conjecture (65%).
* **Where the wall sits.**  Any proof must use `U` exactly along entire forward (or backward) tails
  of infinitely many chains.  That is a survival-type, Π₁ statement: exactly §31's `d(FS) > c`.

## 34. Forward survivors on a ray reduce to the powers of 2 (2026-10-14, "rayfs" Opus agent, checked)

Lean: `AmusicalRay.lean`, proved and axiom-clean (treadmill).  I checked DE, M2 and Corollary H by
hand.  No explicit ray is settled.

* **Odd rays are dead (PROVED).**  Odd `y > 1` has `U y < y`, so `5ᵏ` and every other odd ray hold
  no forward survivor past their first member.
* **Lemma IS and Corollary H (PROVED).**  On a staircase `2^(s−b) 3^b y` the forward survivors form
  an initial segment.  So infinitely many 3-smooth forward survivors is the same as infinitely many
  forward survivors among the `2ˢ` (Ray(2)).
* **Theorem DE (PROVED).**  Every step has `U y + 1 ≥ ¾(y + 1)`.  So after the climb
  `2ˢ ↦ 3ˢ`, the orbit needs more than `1.41 s` further steps to come back below `2ˢ`.  It uses up
  every binary digit of `3ˢ` first, so Ray(2) is a pure late-drop question with no middle-digit
  half (§32's SRE without MDE).
* **M2 (PROVED).**  Infinitely many powers of 2 that are orbit minima give (a).  `2ˢ` is the best ray
  for this route, since 2 is a primitive root mod `3^L`.  Measured backward-survivor rate: `0.3576`
  (predicted `0.3553`).
* **Conjecture P2 (BELIEVED 90%).**  Every `2ˢ` is a forward survivor.  It is a single Π⁰₁
  sentence implying Ray(2).
  * All `s ≤ 3000` pass a walk proxy (escape at `2⁹⁰ · 3ˢ`).  The proxy cannot certify a single
    survivor.
  * The Haar model expects `0.78` failures in total, a prior of 0.43 for none.
* **Gate: witness confinement.**  The injectivity pigeonhole is REFUTED.
  * First-drop witnesses never collide for ratios `≥ 4/3`.
  * Forward-minimum witnesses collide only by sharing an orbit, and nothing proved limits sharing.
  * A world with every `2ˢ` in the backward half of one orbit is consistent with every proved
    lemma.
* **Saturation (PROVED).**  For any infinite `S`, the forward orbits of `S` hold infinitely many
  survivors.  The ray question is exactly the removal of that saturation.

## 35. The ladder is quantized; near-cycle sparsity drops the threshold to 0 (2026-10-14, "fsfloor" Opus agent, checked)

Lean: `AmusicalNearCycle.lean` (SQ, Sep3 mirror, NC′), proved and axiom-clean (treadmill).  I
checked SQ and NC by hand.
No unconditional floor above `c` was found; agent odds that this moves (a): about 3%.

* **Theorem V (PROVED): renormalization is empty.**  Under finitely many orbits, every staircase
  source set has `O(log X)` elements.  These are `FS ∩ 3ℤ`, and `BS ∩ odd` via a new Sep3 mirror,
  `4n ≤ 3n' + 1`.  So no recursive inequality on `d(FS ∩ 2^a 3^b ℤ)` exists, and `τ_odd`, sitting
  at density `c`, already solves the record-ratio recursion.
* **Theorem SQ (PROVED): the ladder is quantized.**  Take a rung `n` (a forward survivor, not its
  orbit's minimum), its depth `g`, and `p = Vᵍ n`.
  * Each step is `x ↦ (3x + e)/2^d`, and odd steps sit at intermediate points `> n`.  So
    `log₂ (n/p) = gθ − a + O(g/n)` (`θ = log₂ 3`): the carry is `≤ g/(3n − 1)`, not `O(log g)`.
  * Since `n/p ∈ (1, 3/2]`, forward-survivor depths lie in the Sturmian set
    `{g : {gθ} ≤ θ − 1} = {1, 2, 4, 6, 7, 9, 11, 12, …}`.  Backward-survivor depths lie in the
    complement `{1, 3, 5, 8, 10, 13, …}`.  The two sets share only `g = 1`.
  * Checked on all of `[1, 2²³)`: `2.9 · 10⁶` cases, 0 off-spectrum, and two false variants fire.
  * `τ` and `τ_odd` break SQ on 35–43% of their rungs, where Lemma K never caught them.  **But SQ
    is not U-specific (§36):** it holds on every real `Û`-orbit, including the one-orbit masquerade.
    `τ` breaks it only because its glue arrows are not `Û`-arrows.
* **`τ` splits the ceiling.**  `BS_τ ≈ 0` and `FS_τ = c`.  So no inequality between `d(FS)` and
  `d(BS)` can come from window statistics, Lemma K or the even branch.
* **Theorem BK (PROVED, with Rhin's bound as a hypothesis Prop).**  Under finitely many orbits,
  shallow rungs (depth `≤ G`) number `O(r G¹⁴)` per block, against Lemma K's `O(r 4^G)`.
* **Theorem NC′ (PROVED, elementary): the sharpest conditional.**  (a) follows from
  `d_upper(FS) > 0` together with "near-cycle starts have density 0 for every `D`".
  * A `D`-near-cycle start is a `p` whose forward orbit first re-enters `[0, p + D]` inside
    `(p, p + D]`.
  * Proof: under `r` orbits, the rungs of one orbit in a block `(Y, 2Y]` telescope to `∏ ρ ≤ 3`, so
    few have gap `> D`.  Every other rung's predecessor is a near-cycle start, injectively.
  * The near-cycle hypothesis is a density version of "no new cycles".  By SQ and Rhin a near-cycle
    needs return time `g ≳ (p/D)^{1/14.3}`.  It is BELIEVED (97%): per-block counts fall to 0, and
    return times are exactly the SQ depths (12, 53, 359).
  * The remaining wall, `d_upper(FS) > 0`, is threshold-free but still Conway-hard: one unit of it
    already exhibits an infinite orbit.

## 36. SQ is a property of `Û`, so rung constraints cannot lower the ceiling (2026-10-14, "sqceiling" Opus agent, checked)

Maze row "rung constraints lower the survivor ceiling below `c`".  Agent odds that this moves (a):
under 1%.  The question was whether SQ (§35) forces the finite-orbit forward-survivor ceiling
below `c`.  The answer is no.

* **Transfer (PROVED; I checked it).**  SQ's proof uses only the real affine branches
  `x ↦ (3x + e)/2^d` and the ladder's order.  So SQ and its mirror hold on every real `Û`-orbit, with
  the integer proofs unchanged.  So do the quantized Kraft sum, BK, P′, Lemma K, Sep3 and NC.
* **The masquerade satisfies SQ.**  §25's masquerade is one real `Û`-orbit with FS density `≈ c`.
  SQ holds on 161 of its 161 rungs, with `a = ⌊gθ⌋` exactly and median depth 31 980.
  * `τ` breaks SQ only because its glue arrows are not `Û`-arrows (`τ/U ∈ [1/3, 3]`).  That shifts
    `{gθ}`, and has nothing to do with `τ` having one chain.
  * **Correction to §35:** SQ does not separate `U` from single-orbit models.  The no-go test for
    rung properties should use the masquerade, not `τ`.
* **Sharpness (PROVED, resting on q1sharp's C3‴, 85%).**  Over finitely many real `Û`-orbits with
  lattice window statistics, the largest possible FS density is exactly `c`.  So no combination of
  rung constraints lowers the ceiling.
  * Kraft is an identity along each ladder.  Window minima are close together: 99.9% of `W₂₄`
    points have another within 80 below.
* **What could lower it.**  Only diagonal, integer-specific inputs: near-cycle sparsity (NC₀, §35),
  late-drop rarity, or FS typicality.  Each is Π₁ or Σ₁ in kind.
* **Smaller results.**
  * **UF (PROVED, no Lemma K).**  Under finitely many orbits, almost every forward survivor has a
    bounded backward undershoot `n − pred(n)`.  As a route to (a) it is weaker than BK.
  * **Q (PROVED).**  `U`'s relative undershoot clusters at `1 − 2^⌊gθ⌋/3^g`.  At `2²⁰`, 0 of 42 170
    rungs have undershoot `≤ 512`.
  * Four statistical twins (one of them `U`) satisfy SQ, with 0 off-spectrum among about 10 500
    rungs each.  The Gaussian `H` has a degenerate spectrum.

## 37. Near-cycles: a linear law, and survivors counted by near-cycles (2026-10-14, "ncnull" Opus agent, checked in part)

Lean: `AmusicalNearCycleLaw.lean` (T1, T2, NCU and the LIN corollary), proved and axiom-clean
(treadmill).  I checked NCU and
T1–T2 by hand.  NC₀ (near-cycle starts have density 0) is **not** proved.  Agent odds that this moves
(a): about 2%.

* **T1 and T2 (PROVED).**  A near-cycle start satisfies the cycle equation with a defect,
  `(3^g − 2^a) p = 2^a d − C_w` with `0 < d ≤ D`.  So each return time `g` carries finitely many
  starts, and `NC_D` is finite exactly when its return times are bounded.  Lemma K forces
  `3^g ≳ Y/D`.
* **NCU (PROVED; strengthens NC′).**  With `N` orbits,
  `#FS ∩ (Y, 2Y] ≤ N(1 + 2Y/D) + #(NC_D ∩ (Y, 2Y))`.
  * On one orbit the block's survivors are `pred`-linked (P′).  A gap `≤ D` makes the lower end a
    near-cycle start, and fewer than `Y/D` gaps exceed `D`.
* **The linear law (Conjecture LIN, BELIEVED 85%).**  `NC_D` looks finite, with `#NC_D ≈ κ D`.
  * `κ = E[1/(2^{M⁺} − 1)] ≈ 5.07`, where `M⁺` is the lowest positive level the log-height walk
    reaches before it first goes `≤ 0`.
  * Measured `#NC_D / D = 5.049, 5.066, 5.069` at `D = 2¹², 2¹⁴, 2¹⁶` (all `p < 2²⁶`).  The exact
    model gives `κ ∈ [5.068, 5.079]`.
  * A deep hunt in `[2²⁶, 2³²)` found 6 starts where the model predicts 4.4, all at return time 665.
    Each excursion uses 1054 binary digits of a 31-bit start, so the model holds far past the
    residue horizon.
  * The backward map gives `κ_b ≈ 4.07`, matching its model.  Four twins give the same `κ`.
  * **LB (PROVED):** `liminf #NC_D / D ≥ κ`, with per-depth constants matching the data to 4 digits.
* **Consequence.**  Under LIN, NCU with `D ≈ √Y` makes `#FS ∩ (Y, 2Y] = O(√Y)` under finitely many
  orbits.  So (a) ⇐ LIN ∧ (forward survivors are not `O(√Y)` per block).  The measured density is
  `0.21`.  The second hypothesis is still Π₁ and Conway-hard, but its required size is now tiny.
* **Collatz contrast (PROVED, given Terras).**  NC₀ is a theorem for the Collatz map.  It fails to
  transfer to `U` at exactly one step: depth-`G` survivors keep density `p_f ≈ 0.21 > 0`.
* **Gates.**
  * Residue counting over words reaches only depths `g ≲ log₃ Y`, which Lemma K already empties.
  * Tao-type 3-adic mixing (Tao 2019, Prop 1.14): `U`'s version holds exactly, but only inside the
    horizon.  Tao gets past the horizon by repeating at ever smaller heights, which needs orbits
    to drift down; `U` and `V` both drift up.

## 38. Run-bounded near-cycles: the cycle method proves the linear law stratum by stratum (2026-10-14, "ncbaker" Opus agent, checked in part)

Lean: `AmusicalNearCycleRuns.lean` (MR I, MR II, MR-P with Rhin as a hypothesis `Prop`), proved
and axiom-clean (treadmill).
I checked MR (I) and (II) by hand.  The linear-law theorems L1/Lm are the agent's (PROVED, not yet
re-derived by me).  Agent odds that this moves (a): about 2%.

* **Theorem MR (PROVED, elementary).**  A near-cycle start `p` (return time `g`, `m` `E`-runs,
  `Λ = g ln 3 − a ln 2`) satisfies:
  * **(I)** `−m < pΛ < D + m`.  Along an odd run, `z − 1 ≥ (4/3)(z' − 1)`, so a run ending at `X`
    adds `< 1/(X − 1)` to the carry.
  * **(II)** `(2 − θ)g − 1 < #E ≤ log₂p · (θ^m − 1)/(θ − 1)`.  The upper bound uses `2^{a_j} ∣ x_j`,
    the one integrality input and the one a real `Û`-orbit lacks.
* **MR-P (PROVED, Rhin as a `Prop`).**  `max NC_D^(≤m) ≤ D (C θ^m log D)^13.3`.  This is LIN's
  location clause on each run stratum.
  * Starts with `m ≤ μ log₂ p`, `μ < 0.113`, satisfy `p ≤ D^{1/(1 − μ/0.113) + o(1)}`.
  * Any effective irrationality measure of `log₂ 3` suffices in place of Rhin's constant.
* **The linear law on every stratum (L1, Lm; PROVED, Rhin as a `Prop`).**
  `#NC_D^(≤m) = κ_{≤m} D + O_m(D^{θ/2+ε})`.
  * For one run, `κ₁ = 2.736351…` has a closed series.  The exhaustive count at `D = 2¹⁶` is
    `179 332` against `179 329.5`, and the error never exceeds 12 for `D ≤ 2¹⁶`.
  * Counting works past the residue horizon because `E`-runs are rigid (one residue class each).
    Mixed A/B odd runs are the only free bits, and prefix balance caps them at 1.41× the `E`-mass
    before them.
* **Equivalences (PROVED).**
  * LIN's density clause holds iff runs are tight, i.e. iff
    `#{p ∈ NC_D : runs > 0.4 √(log₂ D)} = o(D)`.
  * `NC_D` is finite iff its run counts are bounded.
* **Computer theorem C1 (exhaustive, exact arithmetic).**  The 1-near-cycle starts with at most 32
  runs are exactly `2, 4, 6, 10, 88, 112`.  This is the `D = 1` sibling of §18's no-new-cycle bound.
  * `m ≤ 5` needs only `p ≤ 5869`, so it is kernel-checkable.
  * Complete lists: `D ≤ 256` with up to 24 runs, and `D ≤ 2¹⁶` with up to 15 runs (`322 417`
    starts, 97% of `NC_{2¹⁶}`).
* **Where the method stops.**  The measured run count is about `g/4.1`, against a proved floor of
  about `log g`.  For example, the `g = 665` starts have 151–169 runs and a floor of 4.  What is
  left of LIN lies beyond the residue horizon and has too much entropy for this counting.  It is no
  easier than LIN (85%).

## 39. The basin identity, and an order-theoretic no-go for "LIN ⇒ many survivors" (2026-10-14, "basin" Opus agent, checked)

Maze row "basin counting: near-cycle sparsity forces many survivors".  I checked the identity and
Theorem G's construction.  Agent odds that this route moves (a): under 1%.

* **The identity (PROVED; Ren's observation, agent-verified).**  `fmin(n)` = the minimum of the
  forward orbit of `n` is a forward survivor, and `FS = Fix(fmin)`.  The basin of `m` is
  `{Vˢ m : s < g(m)}`, its backward excursion above `m`.  So `X = Σ_{m ∈ FS} #(basin(m) ∩ [0, X))`,
  i.e. `#FS(X) = X / (mean basin size)`.  It is only a change of variables.
* **Dictionary (PROVED).**  Basins are the trees of the first-drop forest.  A node's children are
  its backward record lows, and `NC^f_D`, `NC^b_D` are exactly the short gaps in each value-sorted
  family.  This held on 12.6M children with 0 mismatches and reproduces `κ ≈ 5.05`, `κ_b ≈ 4.05`.
* **The per-basin link is REFUTED on `U`.**  "A basin visiting `[m, X)` `k` times holds `≳ k`
  near-cycle starts" fails.  `U`'s 10 largest finite basins below `2²⁴` (`≥ 200` visits each) hold
  no `NC_256` start.  Basin sizes have an exponential tail (mean 4.76, max 268).  About 54% of
  `[0, 2²⁴)` lies on backward rays of orbit minima.
* **Theorem G (PROVED; order-theoretic no-go).**  There is a permutation `σ` of `ℕ` with:
  * exactly one orbit;
  * every near-cycle set `NC_D` finite, forward and backward (LIN's qualitative content);
  * forward survivors `o(√X)`, even `(log X)²`;
  * step ratios tending to 1.

  The construction lists a spine `s_b` and finite chunks `C_r` above each spine point, spread
  `K_b → ∞` apart, so close pairs are finite while the forward survivors are the spine.  The basin
  identity, the first-drop forest, NCU and P′ all hold for `σ`.  So "LIN ⇒ `#FS ≠ O(√Y)`" cannot
  come from order structure.  It must use `U`'s arithmetic along whole excursions (T1
  integrality), which is §37's gate, now shown to bind the survivor half as well.
* **Where the one-orbit models escape.**  `τ`, `τ_odd` and the masquerade break LIN: their
  near-cycle counts grow with `N` (`τ`: 41 → 88 at `D = 4`), while `U`'s stay flat at 17.  `σ`
  escapes the other way, through sparse survivors.  A one-orbit `U` under LIN would have to look
  like `σ`.

## 40. Stopped prefixes: run tightness at a logarithmic threshold, and the method's ceiling (2026-10-14, "ncentropy" Opus agent, checked)

Pushes §38's run-stratum method from `m ≲ 0.4√log₂D` runs to `m ≤ log₂D/40`.  I checked §2 of the
report (every lemma and exponent).  Lean: `AmusicalNearCycleEntropy.lean` (P2′, NB, the pattern
count, Chernoff, RT-low; proved, axiom-clean, verified 2026-10-14).  Agent odds that this moves (a): about 2%, unchanged.

* **The fix.**  Count each excursion only up to its `τ`-th `E`-step, not over its whole parity
  pattern.  Pattern entropy is then paid on `O(log D)` steps, and Lemma R's `θ^m` blow-up enters
  once, through the location bound.
* **P2′ (PROVED, elementary).**  At an interior local minimum after `A` `E`-steps, `B` odd steps
  and `j` completed runs: `B ln(4/3) < A ln(3/2) + j/(p + D)`, so `B < 1.41 A + 3.48`.  Checked on
  `D = 64` (0 violations; tightening by 0.05 gives violations) and by the agent on 860 242 minima.
* **NB (PROVED).**  The fair-coin mass of `E`/`O` patterns that start with `E`, end at their
  `τ`-th `E` and use `≤ k` `E`-runs is `Σ_{j<k} C(τ−1, j)/2^τ`, a binomial tail (coins "the run
  stops after this `E`").  Checked exactly for `τ ≤ 7`.
* **RT-low (PROVED, no Rhin).**  Near-cycle starts `p ≤ D(log₂D)^14` with `g > 0.61 log₂D` and
  `≤ log₂D/40` runs number `O(D^0.87)`.
* **RT-log (PROVED, Rhin as Prop).**  The same above `D(log₂D)^14` at `O(D^0.956)`, via MR-P's
  location bound `P(m, D) = D^{1 + 8.84μ + o(1)}`.  Hence `#{p ∈ NC_D : m(p) ≤ log₂D/40} = κD + o(D)`.
* **EQ-log (PROVED, Rhin).**  LIN-density ⟺ near-cycles with `> log₂D/40` runs are `o(D)` ⟺
  near-cycles with `g > G(D)` are `o(D)`, for any `G → ∞` with `G ≤ 0.95 log₃D`.  The last form,
  **beyond-horizon negligibility (BHN)**, is all that is left open of LIN-density.  39.8% of
  `NC_{2¹⁶}` lies beyond `log₃D`.
* **Ceiling (PROVED, about the method).**  No count built from residues, stopped prefixes and a
  location bound passes `m ≈ 0.131 log₂D = ((2−θ)/(2θ)) log₂D`, even granting LIN's location clause.
  Rhin gives `μ₀ = 0.0326`; irrationality exponent 2 would give 0.081.
* **Prefix typicality (measured).**  Deep near-cycles (`g ≥ 40`, 39 973 starts at `D = 2¹⁶`) have
  prefixes that look like Haar integers (run-count ratios 0.45–1.44 of random), so refining prefix
  events cannot help.
* **The exponential-sum lead is REFUTED as a route.**  Beyond the horizon the count is the
  congruence `C_w ≡ 2^a d (mod 3^g − 2^a)`; even square-root cancellation only stretches the horizon
  to `1.28 log₂D`.  Past that, BHN needs a pointwise Diophantine argument: the Simons–de Weger wall
  with a defect.
* **Park the stratum method.**  Cheap follow-up: RT-log for the backward map (85% verbatim).

## 41. Sparse regluing: forward-survivor density is a gluing artifact (2026-10-14, "fsarith" Opus agent, checked)

Asked for an arithmetic mechanism forcing many forward survivors; found a no-go instead.  I checked
Theorem Π and Π′ by hand.  Maze row "arithmetic of basins … forces many survivors".  Lean:
`AmusicalReglue.lean` (Π, Π′, Lemma BW, Chernoff duality; proved, axiom-clean, verified 2026-10-14).  Agent odds that this moves
(a): about 1%.

* **Theorem Π (PROVED).**  Let `f` permute `ℕ` with finitely many periodic points, and `F, G → ∞`.
  Some `π` differs from `f` (and `π⁻¹` from `f⁻¹`) at `≤ F(X)` points below `X`, keeps `f`'s
  cycles, merges all infinite orbits into one, and has `#FS_π(X) ≤ G(X)`.  Cut every chain at
  sparse high points; group the pieces into finite blocks by their minimum along a sparse spine of
  singleton pieces; traverse each block in **decreasing** order of piece minimum, blocks laid out
  `⋯ B₆ B₄ B₂ | B₁ B₃ B₅ ⋯`.  Only the spine survives.
* **Π′ (PROVED).**  For `U` every cut can be odd, so `π(2m) = 3m`: Sep3, Lemma St and every
  window/residue statistic survive.
* **Corollary.**  No property of `U` that is robust to sparse modification implies any FS lower
  bound beyond "infinitely many": not `d_lower(FS) > 0`, not `d_upper(FS) > c`, not
  `#FS ∩ (Y, 2Y] ≠ O(√Y)`.  That closes 2-adic/3-adic measure of basin sizes and congruence
  structure of basins.  It is §33's TT with survivors in place of orbit count, and `π` (not
  Theorem G's `σ`) is the right foil: it keeps `U`'s windows and even branch.
* **Gluing order reaches both corners (measured).**  The same pieces in increasing order (`τ`'s
  order, §31) give dense FS (37 718 below `2²⁰`) and dense near-cycles; in decreasing order FS is
  the 5 spine points and near-cycle counts look linear in `D` (`NC_256`: 1 786 against `U`'s
  1 275), stable as the cut height rises.
* **Conjecture Π-LIN (70%).**  `π` in decreasing order inherits LIN.  Then "LIN ⇒ (a)" has no proof
  from LIN plus sparse-robust properties: what remains is `U`'s exactness along entire tails.
  (§43: the forward half holds as measured; the backward half fails, and the repaired `π_β` is the
  right foil.)
* **Conjecture M (60%).**  §25's Steering Lemma realizes the decreasing order with real `Û`-arrows,
  giving one real `Û`-orbit with SQ on every rung and FS density 0.  Then integrality (T1/T2) is the
  only input left.
* **Lead 1 numbers.**  Model basin tails are exponential, `P(t ≤ g < ∞) ≤ ρᵗ/(1−ρ)`,
  `ρ = 0.985597` (forward and backward share `ρ`: Chernoff duality).  Finite basins longer than the
  horizon carry 16–18.5% of `[0, X)` at `X = 2²⁰ … 2²⁴`; a survivor floor needs this mass and no Haar
  argument reaches it.

## 42. T1 integrality is the 2-adic code at the endpoints (2026-10-14, "t1arith" Opus agent, checked)

Asked for an arithmetic invariant of whole excursions that `U` has and Theorem G's `σ` lacks.  None
is cheaper than (a).  I checked R, LOC, DIV and Proposition H.  Maze row "T1 integrality …".  Lean:
`AmusicalExcursionCode.lean` (proved, axiom-clean, verified 2026-10-14).  Agent odds that this moves (a): under 1%.

* **Theorem R (PROVED).**  On the class of a word `w`, `2^a(U^g p − p) = Δ(p − x*_w)`, with
  `x*_w = −C_w/Δ` the word's periodic rational.  So `d ≡ C_w 2^{−a} ≡ C_w 3^{−g} (mod Δ)`, and the
  depth-`g` starts with word `w` are the integers of `w`'s class mod `2^a` in the window
  `(x*_w, x*_w + 2^a D/Δ]`.  `C_w mod Δ` is the 2-adic code shifted by `x*_w`, with no digit
  structure beyond it: the T1 count is §37's beyond-horizon count again.  Checked exactly on all
  4941 starts of `NC_{1024}` below `2¹⁸` and on four `g = 665` hits; word-first counts match direct
  counts for every `g ≤ 12`.
* **Theorem LOC (PROVED).**  Exactly one of `3x/2`, `(3x ± 1)/4` is an integer, namely `U x`.  So an
  integer endpoint of an excursion forces every intermediate step to be a `U`-branch, and a self-map
  built from `U`'s branches is `U`.  "Integrality along whole excursions" is stepwise agreement with
  `U`.  The only integrality input anywhere in §35–§38 is MR(II)'s E-run rigidity `2^{a_j} ∣ x_j`.
* **Theorem DIV (PROVED).**  `gcd(C_w, Δ) = gcd(d, Δ)`.  Every near-cycle is a 2-adic shadow of a
  cycle of a layer map `U_q`, `q ∣ Δ_g`; a genuine cycle word carries no near-cycle with `d < Δ`.  No
  counting leverage.
* **Barriers (PROVED).**  Beyond some depth the expected count per depth is below 1, so LIN's
  finiteness clause has the logical shape of "no new cycles" (B1).  Parseval: a typical Fourier
  coefficient is `≳ 2^{0.78g}` against a main term `≤ D·2^{−0.0209g}`, so no second-moment or
  sum-over-words argument reaches LIN (B2).
* **Proposition H (PROVED via NCU).**  A property `X` that `U` has and that excludes every
  finitely-many-orbit, LIN-sparse model with `O(√Y)` survivors per block gives LIN ⇒ (a).  So the
  requested separating theorem *is* (a) modulo LIN.
* **Proposition BO and Conjecture G′ (65%).**  T2, SQ, MR(I) and Lemma K hold for every
  bounded-offset map `x ↦ (3x + e_x)/2^{w_x}`, `|e_x| ≤ E`; MR(II) does not.  G′: some bounded-offset
  permutation has one orbit, every `NC_D` finite and `o(√X)` survivors.  If G′ fails, there is a
  real-affine route to (a) mod LIN, the one live positive possibility (35%).

## 43. Π-LIN: the backward half fails, and interleaving repairs it (2026-10-14, "pilin" Opus agent, checked)

Stress test of §41's Conjecture Π-LIN.  I checked Theorem MG and the `π_β` construction.  Agent odds
that this moves (a): unchanged (no mechanism).

* **Control.**  fsarith's table reproduces exactly; pure `π` near-cycles are always `U` near-cycles
  (0 violations in 35 runs).
* **Theorem MG (PROVED).**  In the decreasing-order `π`, if consecutive pieces `Q, Q'` of a block have
  `μ(Q) − μ(Q') ≤ D`, then `μ(Q')` is a backward `D`-near-cycle start: the backward scan leaves `Q'`
  (all `> μ'`) and enters `Q`, which contains `μ ≤ μ' + D`.  Pigeonhole: `#NC^{π,b}_D ∩ [0, X) ≥
  M(X) − X/D − O(blocks)`, `M` = piece minima.
* **So the backward half of Π-LIN fails whenever chain minima have positive density.**  Measured:
  `U`'s orbit minima have density `0.0499 = p_f·p_b` (to 0.3%), and `NC^{π,b}_16` grows like
  `0.0256·N` (27 082 / 107 425 / 430 401 at `N = 2²⁰ / 2²² / 2²⁴`; predicted 0.0255).  Positive
  density of chain minima already implies (a), so this is exactly the world in which a foil is needed.
  fsarith measured only the forward direction.
* **The forward half holds (measured; CONJECTURE 80%).**  Forward junction near-cycles are all
  "ladder proximity" events, frozen as `N` grows ×16 and the cut height goes `2²³ → 2²⁸`.  A deep hunt
  (835k junctions below `2²⁴`, ladders to `2⁷⁰`) gives `κ_J ≈ 1.70` forward, `≈ 3.0` backward.  The
  ladders are glued at matching scale; re-pairing at scale ratio `≥ 4.7` makes counts grow like `log N`.
* **Theorem Πβ (PROVED).**  Deal each block's pieces round-robin into `β_b → ∞` sub-blocks, each closed
  by its own odd spine (`≢ 0 mod 3`, so both cuts are odd), spines below the block and decreasing.
  Then `π_β` has one infinite orbit, `π(2m) = 3m`, sparse changes, and one survivor per block;
  consecutive minima in a sub-block differ by `≥ β_b`, so min-gap events vanish for every fixed `D`.
  Measured: backward `NC_256` freezes at 838 / 856 / 862.
* **Π-LIN for `π_β` ⟺ LIN for `U` ∧ LP** (Conjecture LP, 75%: ladder events at each `D` are
  finite).  A greedy dealing (Lemma G) gives `NC^π_D ⊆ NC^U_D ∪ (finite)` in both directions under a
  "non-lingering" hypothesis NL (ladders at scale `s` shorter than `s^{1−ε}`; Haar-trivial, unproved),
  at the cost of changes `O(X^{1−ε})`.
* **"Rewiring must pay in near-cycles" is not a mechanism.**  The decreasing order pays
  `0.0499·P(gap ≤ D)·X` backward near-cycles, but interleaving removes them with no change to FS.
  fsarith's no-go survives with `π_β`, conditional on LP: no proof of "LIN ⇒ many survivors" can use
  only LIN plus sparse-robust properties of `U`.

## 44. Two ideation laps: eight new mechanisms, one survivor (2026-10-14, Codex "astra" and Fable xhigh, checked in part)

Two independent laps (Codex `gpt-6-astra` xhigh; Fable xhigh), each told to read the Maze and §1–§39
first and propose four mechanisms not already tried.  One survives.  Lean: `AmusicalSquares.lean`
(SRC ⇒ (a), SQG1, canonical cylinder, AUT core; proved, axiom-clean, verified 2026-10-14).

* **Square-return confinement (SRC; OPEN, astra).**  Three square visits with roots `≤ H`, in three
  distinct `E`-only blocks of one orbit segment, lie within `C log(2 + H)` steps.
  * **SRC ⇒ (a) (PROVED; I checked).**  Each infinite orbit then holds `O(log H)` of the `H` squares
    `≤ H²`, so finitely many orbits cannot cover them.
  * **SQG1 (PROVED).**  The prefix roots `−B_j/A_j = −Σ_{h<j} e_h 2^{a_h}/3^{h+1}` coincide iff every
    branch between is `E` (the last odd branch has the unique least 3-adic valuation).  So `k` square
    visits in distinct blocks give a multiquadratic curve of genus `1 + (k − 3)2^{k−2}` (SQG2).
  * **Killer.**  Uniformity in the varying word: Siegel/Faltings bound each fixed curve, not the
    family.  Bounded sample: 35 qualifying triples, worst `t/log(2+H) = 17.8`.  A probe ("srcprobe") is
    testing the weakest confinement that still gives (a).  Odds: 1% to move (a).
* **AUT (PROVED; I checked).**  A binary-automatic `U^m`-invariant colouring of `ℕ` is eventually
  constant.  `V^k` maps the cylinder `3^k n + r` onto `2^a n + s` (`0 ≤ s < 2^a`), so the `3^m`-kernel
  lies in the 2-kernel; Cobham then gives eventual periodicity, and strong connectivity (§11) makes it
  constant.  The route "finitely many orbits ⇒ automatic orbits" (REG) is equivalent to (a) for `U`: a
  costume.
* **ESS (PROVED, astra).**  On `ℓ²(ℕ, (n+1)^{−s})` every `λ` on the unit circle is in the Fredholm
  essential spectrum of the permutation operator (Weyl sequences on balanced words `a_j = ⌊jθ⌋`).  This
  kills weighted Fredholm-index counting of orbits.
* **Killed (astra).**  An auxiliary-prime affine expander / large sieve: the averaged branch walk is not
  `U` mod `p`, and exact integer cylinders violate the needed mixing.
* **Killed (Fable).**  Each dies on one of three faces of one wall: one point, costume, beyond-horizon.
  * *Two-place Mahler series.*  `U^j m = 3^j(m + S_j)/2^{b_j}`, `S_j = Σ_{i<j} d_i 2^{b_i}/3^{i+1}`.  The
    series converges 2-adically to `−m` for every orbit, and in `ℝ` to `L₊ − m` iff the orbit is thin
    (a costume of late returns).  The real approximation exponent by `3^j` denominators is about 0.05
    (Ridout needs `> 1`), and the 2-adic target `−m` is rational.  This closes S-unit, subspace and
    Mahler routes.
  * *Complexity shape.*  A `Σ₁` separation certificate for `U` is an orbit invariant (costume), so (a)
    stays `Π⁰₃`-shaped.  Independence is at most 5%, and `U` hosts no computation (Theorem L).
  * *Kakutani first-return permutation of `[1, X)`.*  Its path count *is* the orbit count: 4 995 paths
    at `X = 10⁵`, equal to the orbit minima below `10⁵`.
  * *Chain-word repetition forcing.*  The forced repeat length equals the integer's bit length; the
    staircase `2^K` attains it.
* **Synthesis (Fable).**  Every proved inequality about `U` is an inequality about the real affine
  cocycle of `Û`, and every unproved one is `Π₁` about integers beyond depth `log X`.  A proof of (a)
  needs a statement false for the masquerade and true for `ℤ`.

## 45. Conjecture G′ holds in a stronger form: block-swap maps keep every proved invariant (2026-10-14, "gprime" Opus agent, checked in part)

Settles the direction §42 left open, conditional on one extension lemma.  I checked the family and
the elementary lemmas.  Lean: `AmusicalSwap.lean` (`ampSwap` bijective, even branch, offset,
no-swap = `U`, CT1, spine bound; proved, axiom-clean, verified 2026-10-14).  Agent odds that this
moves (a): under 1%; it closes a route and opens none.

* **The family `F_L` (PROVED).**  Keep `π(2m) = 3m`; for each `n`, map the odd numbers of
  `[4nL, 4nL + 4L)` bijectively onto the non-multiples of 3 in `[3nL, 3nL + 3L)` (both have `2L`
  elements).  Every choice is a permutation with offset `|e| ≤ 12L − 3` and exactly `U`'s `E`-runs, so
  it satisfies MR(II) as well as T2, SQ, MR(I) and Lemma K.  `U` is the member whose block transitions
  are all increasing.  For `L = 1` this is "`U` with the targets of `4n+1`, `4n+3` optionally swapped"
  (`|e| ≤ 5`).
* **CT (PROVED).**  `NC_D` starts are exactly the short edges (`≤ D`) of the chain's Cartesian tree.
* **HB (PROVED).**  For any bounded-offset bijection, every dyadic block is crossed by `≥ 0.0536 Y`
  separate orbit segments; this follows from bijectivity alone and bounds passes, not orbits.  So
  no mass-conservation obstruction exists.
* **Measured.**  A lazy builder in `F_2` (`|π − U| ≤ 4`, offset `≤ 17`) produced one chain covering
  `[10³, 10⁵)`, with no near-cycle violations at `D(y) = 0.2 y^0.6` and FS = 15 (the spine; `U` has
  about 21 000).  Its controls reproduce `U`'s `NC_D` exactly (6 / 20 / 78 / 324 / 1 275).
* **EXT ⇒ G′ (PROVED, EXT as hypothesis).**  Given the extension lemma EXT (85%, measured), some
  `π ∈ F_2` has one infinite orbit, every `NC_D` finite and `#FS = O(log X)`.  With the ratio
  version (70%), `#NC_D ≤ D/δ + O(1)`.
* **Consequence.**  Under EXT, Proposition H fails even with MR(II) included.  So "LIN ⇒ many
  survivors" cannot come from the §35–§38 toolkit.  Inside `F_L`, `U` is singled out only by
  increasing block transitions, and by TT a proof must use that law along entire tails: the Π₁ wall
  again.  `L = 1` is open (the builder sticks at 1215 with the gap filter).

## 46. Square-return confinement: probably true, Π⁰₁, and out of reach of curve geometry (2026-10-14, "srcprobe" Opus agent, checked in part)

Probe of §44's SRC.  I checked Claim W and the implication chain.  Agent odds that this moves (a):
under 0.5%.

* **Hunt (measured).**  Exact walks from every square start up to `10¹⁶` (values below `2¹⁶⁰`; every
  triple starts at a square, so this is complete for triples in that range): **22 qualifying triple
  endpoints in all, none with `H > 863`**, the same 22 as at `H = 10⁴`.  The worst ratio stays
  `29² → 10² → 13²` (`t/ln(2+H) = 17.76`, 61 steps), so `SRC_C` with `C = 17.77` holds to `H = 10⁸`.
* **Pairs (measured).**  Two-block square pairs grow like `≈ 29 ln H` (479 at `H = 10⁸`), including a
  Pell family `15² → 13², 209² → 181², …` (one `A`-step each).  A heuristic with decay rate
  `I = 0.014508` predicts `≈ 35 ln H` pairs and finitely many triples; `U` is more confined than the
  model on every statistic.  Pairs are genus 0 and recur; triples are genus `≥ 1` and finite in all
  data.
* **Weakest sufficient confinement (PROVED).**  FT ⇒ `SRC_C` ⇒ TSC (`t ≤ f(H)`, `liminf f/H = 0`) ⇒
  WSC ⇒ (a′) ⇒ (a), where (a′) says the squares meet infinitely many orbits; `ARC_C ⇒ SRC_{2C}`.  For
  fixed `C`, `SRC_C` and `ARC_C` are **Π⁰₁** statements.
* **Claim W (PROVED): the geometry is vacuous.**  Once `t > 2 log₂ H` the word has consumed more bits
  than `x₀ ≤ H²` has, so each word-curve carries at most one relevant integral point.  Siegel,
  Faltings, uniform Mordell and Bombieri–Pila count points; SRC is about whether such points
  *exist*.  SQG1 is only the block clause, and Lemma K bounds `t` from below.  SRC constrains
  `t > 17.76 ln H`, about six times past the residue horizon `1.82 ln H`: the §42 wall.
* **Foil (conditional).**  If G′ (§45) holds with offsets prime to 3 (55%), a one-orbit model keeps
  SQG1, SQG2 and Lemma K while every confinement fails.
* **Credences.**  SRC true 85%; FT true 80%.

## 47. Where the lane stands: one wall, six foils (2026-10-14, Ren)

A map of §30–§46, so the next session starts here rather than re-deriving it.

**The wall.**  Every route ends at a Π₁ statement about integers beyond the residue horizon
(`depth > log X`).  Every *proved* inequality about `U` is an inequality about the real affine cocycle
of `Û` (Fable, §44).  A proof of (a) must use `U`'s exact branch law along entire tails (TT, §33),
and the only statements known to separate `ℤ` from the masquerade are the survivor densities
themselves.

**Sharpest conditionals (all Lean-proved).**
* (a) ⇐ `d_upper(FS) > c` (C2′, §31).
* (a) ⇐ `d(FS) > 0 ∧ NC₀` (NC′, §35).
* (a) ⇐ LIN `∧ #FS ∩ (Y, 2Y] ≠ O(√Y)` (§37).
* (a) ⇐ SRC, a Π⁰₁ hypothesis with `C = 17.77` unrefuted to `H = 10⁸` (§44, §46).

**The foils: each keeps a class of proved invariants and fails (a)'s conclusion.**

| foil | keeps | breaks | § |
|---|---|---|---|
| `σ` (Theorem G) | order facts, NCU, basin identity, LIN's finiteness | windows, even branch | 39 |
| `τ`, `τ_odd` | windows, residues, even branch | LIN | 14, 33 |
| masquerade (real `Û`-orbit) | SQ, Lemma K, every window statistic | integrality | 25, 36 |
| `π`, `π_β` (Theorem Π, Πβ) | sparse-robust properties, even branch, LIN (mod LP) | FS density | 41, 43 |
| `F_L` block-swap (G′, mod EXT) | MR(II), T2, SQ, MR(I), Lemma K | increasing block law | 45 |
| `U + 6^N` (deformation) | `U` for `~N` steps | everything far out | 29 |

**Open statements, with credences.**  LIN 85% (its open core is BHN, §40); LP 75% (§43); EXT 85%
(§45); SRC 85% (§46); NC₀ (§35) open; (a) itself open since 1963.

**What would move it.**  A statement that is false for the masquerade and for every `F_L` member
with a non-increasing block law, and true for `ℤ`, about whole tails.  Nothing in §1–§46 is such a
statement.  Odds that this lane settles (a): about 1%.  Its standing output is the Lean-certified
map of why each tool fails.

## 48. Ideation round 2, gated by the Maze pre-flight: 42 candidates, no survivor, two theorems (2026-10-14, Codex "astra" and Fable xhigh, checked in part)

Both laps ran under the Maze §0 pre-flight and an effort bar (at least 15 candidates from at least 5
areas, one targeted repair per gate failure, four probed seriously).  Together: 42 candidates, every
one blocked by a named gate question, almost all by question 1 (the beyond-horizon wall).  No
candidate passes question 3 with any input other than "`U` is exactly `U`", which is TT (§33).
Reports: `newroutes2-astra.md`, `newroutes2-fable.md`.

* **Theorem Z (PROVED on paper; astra, confirmed by the adversarial "zverify" agent, ~97%).**
  Let `𝒜` be the `*`-algebra of finite sums of operators mapping a full arithmetic progression
  affinely onto another (positive slopes) on `ℓ²(ℤ)`.  If `S ∈ 𝒜` commutes with `U` and `S*S = I`,
  then `SS* = I`.  zverify's simpler proof: `‖S δ_n‖²` and `‖S* δ_m‖²` are `U`-invariant (from
  `PS = SP`, `P` unitary) and agree with periodic functions off a finite set, so they are constant
  (residue transitivity, §11); a germ argument at `0` makes the two constants equal; then `I − SS*`
  is a positive element of `𝒜` with finite support, hence `0`.  So no finite arithmetic isometry
  certificate can count orbits by an index.  No counterexample in five commutant dictionaries up to
  1.03M terms (the commutant was always the Laurent polynomials in `P` the dictionary could
  express).  `𝒜` is the dense core of Cuntz's `ax + b` ring algebra; nearest literature Mori
  (arXiv 2411.08084, 2508.05713); novelty ~70%.  Lean: the arithmetic core, "a periodic
  `U`-invariant function on `ℤ` is constant" (also with invariance only off a finite window),
  `AmusicalPeriodicInvariant.lean` (proved, axiom-clean, verified 2026-10-14).
* **Lemma E (PROVED, Fable; Ren checked).**  A successor swap `σ ↦ σ ∘ (a b)` never changes the
  number of infinite orbits of a permutation of `ℕ` and changes the total orbit count by at most
  one.  So "infinitely many orbits" is a tail event in any perturbation family of `U`, with
  probability `0` or `1`.  Lean: `AmusicalTailEvent.lean` (proved, axiom-clean, verified 2026-10-14).
* **Measured (Fable).**  In the monotone family `U ∘ s_E` (swap the targets of `2n` and `4n+1` for
  `n ∈ E`; every member has `|π − U| ≤ 1`), random `E` of every density `p ∈ [0, 1]` keeps the
  orbit-start density at `c ≈ 0.05`.  (a)-like behaviour is generic; only adversarial `E` (EXT-type,
  §45) kills it.  `U` is the unique map in both this family and `F_L`.
* **Other kills, one line each.**  Transport energy (no monotone link to orbit count); ordered
  strands and induced returns (the first order lemma is false: an infinite family of two-step
  inversions); signed distortion (temporal discrepancy uncontrolled); powers of 3 with p-adic Baker
  on periodic runs (the start bound `C log s` is sharp, the tail is beyond the horizon); late
  droppers as reduced periodic points (an identity only); a two-sided horizon from the peak (92% of
  late droppers stay past the peak's digit budget).
* **Reading.**  The gate worked: both laps spent their probes on candidates that had passed it.  The
  wall did not move.

## 49. Ideation round 3, hunting the separating statement: no survivor, three obstructions (2026-10-14, Codex "astra", Ren checked)

Target: a statement `P` about whole tails that `U` satisfies and every foil violates (§47).
15 candidates from seven areas, a repair per failure, four attacks probed; no survivor.  Report:
`newroutes3-astra.md`.

* **T1–T3 (endpoint transfer, paper proofs, Ren checked).**  No `P` invariant under finite changes
  can reject every non-increasing `F_L`: a single swapped block is a finite change of `U`.  For
  independent swap bits with rates `p_b`: if `Σ p_b < ∞` the random map is almost surely a finite
  change of `U`, so "(a) almost surely" is *equivalent* to (a) for `U` (Lemma E, §48); if
  `Σ p_b = ∞`, `U`'s pattern is null and an almost-sure theorem says nothing about it.  No nontrivial
  closed or open tail event exists in the pattern topology (each finite-change class is dense).  So
  randomization plus a 0–1 law cannot transfer (a) to `U` without an exact endpoint comparison.
* **Monotone coupling fails on `U` itself (Lean).**  "A swap never lowers finite-horizon survival"
  is false both ways: swapping block 42 lifts `100` from a drop at time 5 to 64 steps above it;
  swapping block 49 drops `104`, 64 steps above under `U`, to `85` at time 20.  The averaged Russo
  derivative over starts has both signs too.  Frozen and fresh-coin exploration differ already from
  `1` (total variation 5/8), and injective `U`-prefixes revisit a block's partner with either parity.
* **L1, positive loop correlation fails on `U` itself (Lean, Ren checked).**  Two switches whose
  sources interleave on one orbit (`a, c, b, d`) give loop counts `C, C+1, C+1, C`, breaking the
  log-supermodularity FKG needs.  On `37 → 28 → 42 → 63 → 47 → 35 → 26 → 39 → 29 → 22 → 33 → 25`,
  block 9's sources sit at times 0, 7 and block 8's at 5, 10: swapping 9 closes a 7-cycle, 8 a
  5-cycle, both rethread one segment.  Increasing *spatial* block order does not give the needed
  *temporal* non-interleaving.
* **O1, O2 (operator certificates, standard arguments, Ren checked).**  A compact perturbation of a
  unitary that is an isometry is onto, so decaying nonperiodic corrections to a commuting unitary
  cannot give a proper isometry.  Approximate commutation does not certify: for one bilateral chain
  there are proper isometries with `‖PS − SP‖ ≤ π/K` (piecewise doubling on `K` cells).  What is left
  is an exact, noncompact, effectively specified commuting isometry, with no construction in sight.
* **Lean.**  `AmusicalLoopInterleave.lean`: the L1 witness and both pivots, by `decide`, axiom-free
  (verified 2026-10-14).  Maze rows 64–65 (loop-weighted comparison: refuted; tail-event transfer:
  costume).
* **Reading.**  Three rounds, ~120 candidates, one boundary.  Round 4 drops the repair posture and
  hunts a dictionary to a foreign world (Trevor: "Langlands-level thinking leap").

## 50. Theorem R, a Langlands-style dictionary that is a costume, and round 3's second lap (2026-10-14, "extprove" and "pcancel" Opus agents, Codex "astra" round 4, Fable round 3; Ren checked in part)

* **Theorem R (PROVED, extprove; Ren checked Lemmas F, R and the assembly, ~85%).**  For every
  `L ≥ 72` some `π ∈ F_L` has exactly one infinite orbit, finitely many cycles, and
  `#FS(X) = O(log X)`.  Construction: gprime's spine, then a climb that always routes to the arc of the
  lowest unvisited value, taking only *safe* arcs.  The unused-arc digraph is balanced except at the
  current node (out − in = 1), and an infinite Fleury lemma says at most one arc out of it can strand
  a finite set.  Interval maps `U(I) ≈ 4I/3`, `D(I) ≈ 8I/9` grow whenever the route lingers (zero gain
  forces `3 ∣ a`, at most `v₃(a)` times), so every unvisited value stays reachable.  Every point of the
  climb is followed by the spine's start, so `FS ⊆ spine ∪ (finite)`.  **Consequence:** bounded offset,
  exact E-runs (MR(II)), T2, SQ, MR(I), Lemma K and `U`'s parity word cannot force survivor density
  on a one-orbit map.  This was measured before; it is now unconditional (Maze row "bounded-offset real-affine maps").
* **EXT (§45) is the wrong target as worded** (proved: a good prefix whose two lowest reachable holes
  are within `D` is a dead end); the reduction to G′ needs only one good infinite climb (EXT\*).
  Theorem NF (proved): near the frontier every hole is an even non-multiple of 3, filled only as a
  strict valley, so near-frontier CT3 is an order condition.  Open core BSL (CT3-legal routing just
  above the frontier, 80%): at `D = 0.001y` the filter rejects an option at `6.5·10⁻⁵` of choice steps,
  never below two legal options.  One chain covers `[10³, 10⁶)` (55.7M points, offset ≤ 17, FS = 22,
  no near-cycles at that scale).  gprime's scale `D = 0.2y^{0.6}` breaks past `10⁵`.  G′ 90%.
* **Itinerary hull (astra round 4; pcancel).**  Round 4 hunted a dictionary to a foreign world
  (Trevor: "Langlands-level thinking leap"); 12 worlds, two developed.  Code each integer by its
  two-sided branch word `c_n(k) = U^{k+1}(n) mod 3 ∈ F₃` (pcancel's D1: the branch label *is* `U(x)` mod
  3) and let `M_U = Σ R c_n`, `R = F₃[t, t⁻¹]`, discrete.  Proved: finitely many orbits ⇒ `M_U` finitely
  generated (so non-f.g. ⇒ (a)), equivalently its compact dual is expansive; f.g. is label-independent
  and invariant under finite surgery; infinitely many cycles ⇒ non-f.g.; no `R`-relations on one or
  two points.  But with no relations (NR, 90%; exact `F₃` elimination finds none for `n ≤ 1000` in
  degree 0, `n ≤ 500` in degree ≤ 2, `n ≤ 60` in degree ≤ 12), `M_U ≅ (cycle torsion) ⊕ R^{#infinite
  orbits}`, so non-f.g. ⇔ (a): a **costume**.  NR itself is a whole-tail Π₁ statement.  The one
  non-costume mechanism, periodic cancellation among aperiodic codes, is unsupported (3%).
* **Pants cover (astra round 4).**  With monodromies `U` and `n ↦ n+1`, `U`-orbits are the components
  over one marked boundary circle (proved), and the surface has infinite genus from explicit embedded
  handles using only the even branch (proved).  `n ↦ n+1` alone also gives infinite genus with one
  orbit, so genus is no lever; the marked-boundary count is a costume.
* **Fable round 3 (17 candidates, no survivor).**  Two genuine separating statements with `P ⇒ (a)`
  proved, both blocked at Q1: transient cores of the minimum-ray set (via Theorem T; core mass decays
  `0.465 → 0.0014` over 200 steps) and "every orbit holds finitely many powers of 2" (only
  `U¹²(8) = 32`, `U⁴¹(16) = 512` up to 200 steps, Ren checked).  Late survival is, pattern by pattern, a
  signed-sumset (Littlewood–Offord) problem: anti-concentration saves `√m`, BHN needs `2^{−3m}`.  The
  random swap family `F_1` is Haar-typical two-sidedly at every swap density.
* **Reading.**  The foreign-world leap produced faithful dictionaries, but each far-side target was
  equivalent to (a) once the dictionary's kernel was understood.  The leap that would count needs a
  far side whose *tools* see integrality along whole tails.

## 51. Round 4, second lap: (a) is the one fully ramified point, and ⟨n + 1, U⟩ is non-amenable (2026-10-14, Fable xhigh; Ren checked Theorem N)

Fable's leap built two dictionaries that turn out to be one object, seen at its special and generic
points.  Report: `newroutes4-fable.md` (12 worlds, 8 fields).

* **D1, the two-prime Thompson groupoid.**  Let `𝒢` be the `ax + b` germ groupoid on `ℤ₂ × ℤ₃`, whose
  topological full group is a two-prime Thompson group `V_{2,3}`; `Û` (`U` on `ℤ₂ × ℤ₃`) is a coupled
  baker's map in it.  The integers form the one `𝒢`-orbit with full isotropy `⟨2, 3⟩ ≅ ℤ²`, and (a) says
  the `Û`-subgroupoid has infinite index *at that point*.  **Theorem R (paper, 100%):** at every point
  with trivial isotropy the index is infinite (translates `x + c` lie on distinct `Û`-orbits); also for
  mismatched integer pairs `(n, n + d)`.  So the masquerade is the generic fibre, which explains why it
  copies every windowed statistic.  **Theorem C (95%):** the isotropy characters give slope-twisted
  Koopman operators whose spectra see exactly the cycle data and nothing of the infinite orbits.
  Measured: 12 sub-layers `U_q` each have orbit-start density `c = 0.0499 ± 0.0005` (control `U²` at
  `1.79c`).
* **D2, the Schreier graph of `Γ = ⟨T, U⟩ ≤ Sym(ℤ)`, `T n = n + 1`.**  (a) says the double-coset set
  `⟨U⟩ \ Γ / Stab(0)` is infinite.  **Theorem N (PROVED, Lean):** no finitely additive probability mean
  on `ℤ` is invariant under both `T` and `U`, since `T`-invariance forces mass `1/2` on the evens and
  `1/3` on the multiples of 3, and `U` maps one onto the other.  So `Γ` acts non-amenably; Fable also
  gives an isoperimetric bound `|∂F| ≥ |F|/6` and two ends (paper).  Novelty ~60% (the RCWA literature
  may have it).  Its Benjamini–Schramm limit is D1's random generic point (Lemma BS, 95%).
* **Reading (70%).**  (a) is a statement about the single fully ramified fibre of a groupoid; every
  quasi-invariant, local or K-theoretic structure is built on the generic fibre, and Theorem N says
  averaging over `ℤ` in the way `T` allows cannot see `U` at all.  What *can* see the special fibre is
  the lattice `ℤ[1/6] ⊂ ℝ × ℚ₂ × ℚ₃` itself, which is round 5's brief.
* **Lean.**  `AmusicalNoMean.lean`: `amusical_image_even`, `no_translation_amusical_invariant_mean`
  (proved, axiom-clean, verified 2026-10-15).  Maze row "dictionaries to groupoids, Schreier graphs,
  itinerary modules, covers" (costume).

## 52. Round 5, far sides that consume integrality: they see cycles, not infinite orbits (2026-10-15, Codex "astra" and Fable xhigh; Ren checked in part)

Brief: a foreign world whose theorem takes integrality (or the diagonal `ℤ[1/6] ⊂ ℝ × ℚ₂ × ℚ₃`) as a
hypothesis with teeth and concludes finiteness.  28 worlds across both laps, four developed; no
survivor.  Reports: `newroutes5-astra.md`, `newroutes5-fable.md`.

* **Rays and S-units (both laps).**  The *rays* `R_m = {2^m, 3·2^{m−1}, …, 3^m}` are the maximal
  S-integer segments of orbits; an orbit enters a ray only at `2^m` and leaves only at `3^m`.  A
  *join* `U^k(3^m) = 2^{m′}` is the S-unit equation `2^x − 3^y = C_w` for the prefix word `w`.  Fable's
  ray-join map `σ_J` is a partial injection, and "`σ_J` has infinitely many orbits" implies (a)
  (strictly stronger, not a costume).  Joins known: `27 → 32` (9 steps) and `81 → 512` (37 steps), Ren
  checked; none from `3^m`, `5 ≤ m ≤ 200`, within 20 000 steps.  **Conjecture J (60%):** `σ_J` is defined
  only on `{1, 2, 3, 4}`, which implies (a).
  * **Theorem J (Fable, paper, given Ellison 1970/71 Thm 3, opened).**  No join from `3^m` within
    `2.1m` steps, past the residue horizon `1.06m` (about `3.8m` with Rhin's measure, cited secondhand).
    Via Lemma BJ: `|2^x/3^y − 1| ≤ Q_k` from the two-place series.
  * **Corollary P (Fable, given Bennett 2001 Thm 1.1, opened).**  At most two rays share a (word,
    depth); exactly one for both known joins.  So the 2-adic adversary is beaten on an infinite class.
  * **ESS transfers (astra, paper).**  Ray returns with boundedly many odd steps inject into
    nondegenerate S-unit solutions, so Evertse–Schlickewei–Schmidt bounds them uniformly, but the
    whole theorem applies verbatim to every `F_L`, finite-orbit foil included.  The residual is the
    late-return wall: "the orbit of `3^m` never dips late".
* **`p`-adic interpolation (astra, paper).**  A continuous 2-adic interpolation in time of a sampled
  `U`-orbit forces periodicity; a restricted-analytic one forces it constant; a 5-adic repair loses
  2-integrality.  Adelic quotient descent fails, `U` has no o-minimal real extension, and polarized
  heights do not normalize.
* **Mahler `Z`-numbers (Fable).**  Mahler's `0.7 = log₂ φ` and Flatto's `0.585` reproduced exactly; the
  transplant to `U` sees only cycles (nontrivial real shadows occur only over cycles; cycle elements
  `≤ X` of bounded ratio number `≤ C X^{0.9868}`), and survivors have no entropy deficit (Haar plateau
  `0.2101`, matching the measured FS density `0.213`, §14).
* **Side entries (Fable).**  `Û` lowers 3-denominators by one, and (a) is equivalent to infinitely many
  orbits of the inverse branch system on `ℤ[1/3]`; every orbit indicator has the unit circle as a
  natural boundary, and `Σ_{n ∈ O(8)} 2^{−n} ∈ ℚ` ⟺ `O(8)` is finite or cofinite (Pólya–Carlson; corrected
  in §53 from Fable's "exactly one infinite orbit", which needs `O(8)` infinite and finitely many
  cycles, both open).
* **Reading.**  Every far side that consumes integrality and reaches `U` sees *closed* Diophantine
  equations, which are cycles; infinite orbits are open equations.  Conjecture J is the cleanest new
  target: a statement about S-unit equations along one explicit family of orbits, with the first
  `2.1m` steps proved.
* **Lean.**  `AmusicalRayJoin.lean`: both known joins (`decide`, axiom-free) and Theorem J in the form
  "no join within `2m − 2` steps", from the hypothesis `EllisonBound` (proved, axiom-clean, verified
  2026-10-15).  Maze row "S-unit equations along rays" (`beyondHorizon`).

## 53. Round 6 and the Conjecture J attack: the early half of J is settled, infinite orbits stay open (2026-10-15, "jattack" Opus agent, Codex "astra" and Fable xhigh round 6; Ren checked in part)

* **Theorem T (jattack, paper + exact computation, 92%).**  For every `m ≥ 5` and `1 ≤ k < 3.818m`,
  `U^k(3^m)` is not a power of 2 (Ellison gave `2.107m`).  Large `m` via Rhin's measure
  `|u₀ + u₁ log 2 + u₂ log 3| ≥ H^{−13.3}` (Rhin 1987, Prop. (7), opened); `m ≤ 7·10⁴` by per-`m` bounds and
  exact search.  The dip form of Lemma BJ holds without its side condition.
* **Theorem S (jattack, paper + table; Ren checked the descent, 95%).**  The constant is sharp for
  `F₁`: for every `m ≥ 5` some `π ∈ F₁` joins `3^m` to a power of 2 by step `log_{4/3}(3^m) − 8.4`
  (always take the odd image, so `x′ ≤ (3x+5)/4`, values stay odd, and each block is decided once;
  a computed table finishes below 2000).  So `c* = log_{4/3} 3 = 3.8188` is the exact ceiling of any
  argument that also holds on `F_L`; the early-join question is solved at the level of `F_L`.
* **What is left of Conjecture J (65%).**  Late joins.  The only `U`-only lever found: a join just past
  `c*m` forces `3^m mod 4^{0.79m}` into a 2-adic set of measure `2^{−Ω(m)}`, an Erdős-type digit
  problem.  Finite certificates on small orbits cannot reach `k ~ m²`.  Search: no join for
  `5 ≤ m ≤ 400` within `10⁶` steps, `m ≤ 20 000` within `4m` (Ren spot-checked `m ≤ 60` to `20 000`).
  Since Conjecture J implies (a), the late half is at least as hard as (a); parked as a named target.
* **Round 6 brief: make infinite orbits closed objects.**  28 worlds across both laps; no survivor.
  * **Ends and monodromy (Fable, Theorem E/M, paper).**  An infinite orbit whose signed harmonic sums
    converge has two real ends `ξ±(n)` (limits of `2^{b_k} x_k / 3^k` and its backward analogue), with
    `ξ±(Un) = (3/2^{s(n)}) ξ±(n)`, so `ξ±` mod `⟨2, 3⟩` and the monodromy
    `ρ(O) = ξ₊/ξ₋ = ∏_{x ∈ O} (1 + ε(x)/(3x))` are orbit invariants; a cycle has `S`-unit monodromy
    `2^b/3^p` (Ren checked the telescoping).  This is the brief's "cycle at infinity", but it is a
    real limit, an invariant of the real-affine cocycle shared by the masquerade and Theorem R's
    one-orbit member: a costume.  `ρ(8) = 0.96532989759365964906…`; `ρ` separates 256 of 257 orbit
    representatives `≤ 5000`; no infinite orbit has `S`-unit monodromy of height `≤ 80`.
  * **Limits of cycles (astra, paper).**  Finite completions agreeing with every internal `U`-arrow on
    `[0, N)` can have normalized cycle counts tending to any value in `[0, 1/6]`, all converging to
    `U`; `U` has no nontrivial congruence quotient; first returns and finite-to-one quotients cannot
    make an infinite orbit periodic.
  * **Correction (astra).**  The §52 rationality criterion needed two open hypotheses; fixed there.
* **Reading.**  Six rounds, ~230 candidates.  Integrality-blind tools see the generic fibre;
  integrality-consuming tools see closed equations; the one attempt to close infinite orbits (real
  ends) closed them in `ℝ`, where integrality is gone.  The reopen condition is still §47's.

## 54. Normal and disjunctive itineraries (2026-10-15, "normal" Opus agent and the "crossreview" agent; Ren checked)

Trevor's question: if `U` runs to infinity, is its step sequence normal or disjunctive, and can
normal numbers be built from these orbits?  Report: `normal.md`; cross-lane context: `crossreview.md`.

* **No itinerary is base-3 normal (PROVED, Lean).**  `not_tendsto_evenFrequency_third`: for every
  positive integer, the even-label frequency of its forward itinerary does not tend to `1/3`.  An
  aperiodic orbit with even-frequency below `2 − log₂ 3 = log₂(4/3) ≈ 0.415` spends more than
  `log₂ 3` bits per step and falls (`periodic_of_evenFrequency_lt`, already in the repo); a cycle at
  exactly `1/3` would need its odd elements to average below about 3.8 (the step ratios multiply to
  1 around a cycle), leaving only `{1}` and `{2, 3}`.  The agent's Theorem A adds the liminf and
  backward forms: forward `liminf E⁺/K ≥ κ ≥ limsup E⁻/K` on any infinite orbit (paper, 95%).
* **The right normality is one-sided.**  Forward cylinders are classes mod `2^{W(w)}` (Haar on `ℤ₂`
  pushes to `Bernoulli(½, ¼, ¼)`); backward ones are classes mod `3^k` (uniform).  Forward normal ⟺
  the orbit equidistributes in `ℤ₂`; disjunctive ⟺ it is dense in `ℤ₂` (paper, 95%).  Both open.
  Measured on 8's orbit to `10⁷` steps: forward even-frequency `0.4998`, backward `0.3335`, every
  forward word to length 10 present by step `7.88M` (prediction `7.87M`).
* **Positive claims are blocked.**  An eventually periodic itinerary is a cycle, so "the itinerary
  real of 8 is irrational" is exactly "8's orbit is infinite" (costume); every positive statement
  about a single-orbit real implies that orbit is infinite.  The number of `n ≤ X` whose forward
  itinerary avoids a label is `≤ 6X^{log₂ φ}` (Mahler's exponent; paper, 90%), so even "8 hits 3 mod
  4 infinitely often" is a Mahler-type single-orbit problem.
* **Antihydra (cross-lane).**  Antihydra is Mahler's map `x ↦ ⌊3x/2⌋ + (x mod 2)` from 7, shifted by
  1 (Ren checked `10⁴` steps); it never halts ⟺ `#odd − N/2 ≤ N/6` for every `N`.  Equidistribution of
  `{ζ(3/2)^k}` alone gives only "the counter → ∞"; an effective discrepancy bound would be needed.
  The rounding-choice foils, the gate theorem and the exact ceiling of rounding-blind arguments are
  now in Lean in `collatz-cryptid` (`Antihydra/Foils.lean`), with Bigfoot's parity clock and engine
  census (`Bigfoot/Clock.lean`, `Census.lean`: BBf #323 and BB(2,5) Hydra walk the same orbit
  `H^n(3)`, as the two halves of one equidistribution statement).
* **Lean.**  `AmusicalNotNormal.lean` (proved, axiom-clean, verified 2026-10-15).

## 55. Changing the question: five reframes (2026-10-15, five Opus agents; Ren checked)

Trevor's prompt: get unstuck by changing the question, not by another route to (a).  Five laps:
solved cousins (`reframe-census.md`), the family's phase diagram (`reframe-phase.md`), a barrier
outline (`reframe-barrier.md`), a Tao-style almost-all theorem (`reframe-tao.md`), and
undecidability for `{2,3}`-slope permutations (`reframe-undec.md`).  None moves (a) (each `< 1%`);
each finds the §47 wall from a new side, and three give cheap new theorems.

* **A one-swap neighbour of `U` is solvable (Theorem V, paper; Ren checked).**  `V` is `U` with the
  targets of `0 (2)` and `3 (8)` swapped: `V(2k) = 6k + 2`, `V(4k+1) = 3k+1`, `V(8k+3) = 3k`,
  `V(8k+7) = 6k+5`.  The evens are a trap (`V(2ℤ) = 2 + 6ℤ ⊊ 2ℤ`), so each orbit enters them at most
  once, at a point `≡ 0, 4 (mod 6)` with no even preimage; those entry points have density `1/3`,
  so `V` has infinitely many infinite orbits.  Ren re-ran bijectivity and the entry census to
  `2^16`.  In general a residue set `C` with `σ(C) ⊊ C` gives `≥ (d(C) − d(σC))·X` infinite orbits
  meeting `[0, X)` (trap theorem, paper, 97%).
* **Phase diagram.**  In the family of class-wise order-preserving bijections `mj + r ↦ nj + s`,
  members are finite-order, trapped (solvable as above), or on the wall.  Across the 120 pairings of
  `U`'s refined partitions one bit decides: the even branch's image parity.  Even image: 48
  solvable members at density exactly `1/3`; odd image: 48 wall members at `≈ 0.130`; `0 (3)` (`U`'s
  choice): 24 wall members at `≈ 0.050`.  Conjecture B (70%): the boundary is whether some branch
  fails to map onto `ℤ_p`, which is what a trap needs.  Every branch of `U` is onto `ℤ₂`, and the
  whole two-prime ratio family `×q/p` stays on the wall (orbit-start density `c(U) = 0.049780`, 54
  members within 0.7%).  Neighbouring a solvable member does not help: the odd-image members are
  one swap from `V` and as hard as `U`.
* **Avoidance (paper; Ren proved the mod-8 case).**  Every infinite orbit visits `{0, 3, 5} (mod 8)`
  infinitely often going forward.  Proof: avoiding it, odds `≡ 1, 7 (mod 8)` map to odds and
  `4 → {2, 6} → odd`, so the tail is eventually all `3/4`-steps and bounded.  Karp max-cycle-mean
  certificates (Yolcu–Aaronson–Heule style) give 13 five-class sets mod 16 forward and five
  four-class sets mod 9 backward; no set of `≤ 3` classes works mod 16 or mod 9.  Integrality-blind,
  so it says where infinite orbits go, not whether they exist.
* **Barrier outline.**  A method class is the fibre of maps it cannot tell from `U`; a barrier is a
  member with the opposite answer.  Fifteen rows (Theorems R, S, N, Z, Π, the Antihydra gate, ...),
  all keeping `U`'s cycles, so they bar "infinitely many infinite orbits", not (a) via cycles.
  M1 (paper sketch, 80%): for depth `D` and budget `G` with `G/D* → ∞` there is a `τ` with `U`'s
  cycles and at most one infinite orbit that agrees with `U` to depth `D` off `≤ G(X)` points; TT
  is the infinite-depth case.  Two walls, not one: fusion (finite vs infinite depth) and the
  residue horizon (sharp ceilings `c* = log_{4/3} 3`, Antihydra's frozen `E_k`).  The idea is
  Conway's (2013 Appendix 1: "the number obtained by applying µ a million times to 8 might just be the same
  as ..."; Ren opened it) and Tao's (2019 Remark 1.4; opened); the exact iff, sharp constants and
  Lean proofs are ours.  Cheapest new barrier: sign-blind Collatz (odd `x ↦ (3x ± 1)/2`): exactly one
  choice is odd, so the always-odd member diverges, and the all-minus member has the cycle
  `5 → 7 → 10` (Ren checked).
* **Tao does not transfer.**  `1/x` is an exact martingale in both time directions (forward
  `½·⅔ + ½·4⁄3 = 1`, backward `⅓·3⁄2 + ⅔·¾ = 1`; Ren checked), so by Ville `P(min < n/K) ≤ 1/K`;
  measured `K·P ≈ 0.87` forward, `0.84` backward on `[2²⁰, 2²¹)`.  Tao's conclusion is false for
  `U`; the right analogue ("almost every orbit minimum `≥ n/f(n)`") implies (a) and is the late-drop
  wall.  Theorem R's `τ` differs from `U` at `O(log² N)` points, so no log-density statement about
  the first `C log n` steps separates them (the M1 corollary at `D = C log n`).
* **Undecidability next door (Theorem C, paper, 75%).**  A reversible counter-machine engine runs
  with every slope in `2^ℤ 3^ℤ = ⟨3/2, 3/4⟩` (the group of `U`'s slopes), the control state in
  `dlog₃(n mod 5^j)`.  In that family orbit counting is `Σ⁰₂/Π⁰₂`-hard, same-orbit is
  `Σ⁰₁`-complete, and some member's orbit count is ZFC-independent.  Ren re-ran the `r = 5` toy
  (`106,667` engine points, 0 unfaithful, 0 collisions; a broken engine fails `26,667`); full
  bijectivity at `r = 25` is unchecked.  Hardness needs valuation moves of both signs, which
  `U`'s slopes `3^a/2^b` (`a, b ≥ 0`) forbid: a second description of the §47 wall.  (a) is `Π⁰₃`.
* **Census.**  About 40 solved cousins fall into 14 mechanisms needing one of eight properties
  (contraction, branching inverse, cone, flux, low complexity, carry-free, algebraic multiplier,
  reversor); `U` has none usable for (a).  Nearest provable siblings: 32 of the 287 one-transposition
  edits `τ ∘ U` (cone), `U + d`, `PP(0)`, the `F₂[t]` twin, Kohl's ω.  Unprobed reframe: the
  "Wythoff amusical permutation" `W(2k) = ⌊kφ²⌋`, `W(2k−1) = ⌊kφ⌋` (`U` is the same pattern with the
  Beatty-type pair `3, 3/2`).
* **Cheap Lean targets.**  Trap theorem (~60 lines) and Theorem V (~150); mod-8 avoidance; sign-blind
  Collatz gate; M1.  Prior-art check first: Kohl's tame/wild theory and Thompson-group dynamics.
* **Lean.**  `AmusicalTrap.lean` (proved, axiom-clean, verified 2026-10-15): the trap theorem
  (`infinitelyManyInfiniteOrbits_of_trap`), Theorem V (`amusicalV_infinitelyManyInfiniteOrbits`,
  with `amusicalV_eq_amusical` off the two swapped classes and `amusicalV_entry_iff`), mod-8
  avoidance (`amusical_visits_zero_three_five`), and the sign-blind Collatz gate
  (`signBlind_gate`, `signCollatz_minus_cycle`).  M1 is proved too: `AmusicalDepthFusion.lean`
  (`exists_depthFusion`, axiom-clean, verified 2026-10-15), built on the odd rewire; a
  disagreement at depth `d` at `n` is a change of `τ` on `U`'s own segment `U^i n`, `|i| ≤ d`, in
  either time direction, so no budget on `τ⁻¹` is needed.
* **Prior art (`priorart-trap.md`; Ren checked the quotes in the source text).**  The trap mechanism
  is folklore: Simons 2022 (arXiv 2205.10582) §5.4 proves one instance (`P(2,6,5,3)`, divergent
  trajectories with minima `3, 9, 15, …`, exactly `C ∖ σC`), and Kohl ("Graph theoretical criteria
  for the wildness of rcwa permutations", Lemma 3.4) takes the same `σ(S) ⊊ S` hypothesis to
  conclude wildness.  The density form, Theorem V as an example (no OEIS hit), and avoidance for
  `U` look new (65-75%); avoidance is Yolcu–Aaronson–Heule's method (arXiv 2105.14697) moved to `U`.
  Finite order ⟺ tame on `ℕ` is Kohl's (Math. Z. 2010 §6).  The sign-blind gate's substance is
  folklore (Guy 1986, Isbell's game "Beanstalk"; the `3x − 1` cycles are classical).

## 56. Theorem C on ℤ, and the Wythoff family through U (2026-10-15, two Opus agents; Ren checked)

Follow-ups to §55.  Reports: `undec-r25.md`, `wythoff.md`.

* **Theorem C survives on ℤ after three repairs (85%, was 75%).**  The full `r = 25` map (engine,
  sink pairing, highway, every other class) was built for three reversible machines: one total
  (`M_H`), one divergent from `C₁ = 0` (`M_inf`), one divergent only when `2^20 ∣ n` (`M_late`).
  Bijectivity is exact, not sampled: domain and image classes each partition `ℤ` (up to 2001
  pieces, modulus up to `25·2^20·3^37`, every slope positive in `2^ℤ3^ℤ`); inverses built two ways
  agree on `[−10^6, 10^6]` plus 20,000 large points.  Orbit counts: `M_H` one orbit, `M_inf`
  `81, 801, 8001, 80001` for `X = 10^3 … 10^6`, `M_late` one orbit until its engine wakes past
  `2^20`.  Seven broken variants fail.  Ren re-ran the proof, window and orbit checks
  (`X ≤ 10^4`): identical.  Repairs to §55: the non-engine set must contain all of `5ℤ`, not just
  `25ℤ`; a forward-divergent source must be paired with a backward-divergent sink (the mirror chain,
  as in `logic.md`), or the map is not onto; the prediction is `{1, ∞}` orbits, not `{2, ∞}`, since
  `0` sits on the highway.  **The ℕ form is doubtful (40%):** the proposed ℕ highway is not RCWA
  (`1 ↦ 0` is a one-point exception), and a fix needs a finite-orbit RCWA permutation of ℕ running to
  `+∞` at both ends.  Remaining gap to a paper proof: a uniform reversible-machine lemma (finite runs
  restore counters, no garbage configuration on a cycle or bi-infinite chain, divergent sources
  mirrored, divergence ⟺ non-totality); likely via Kari–Ollinger 2008, 2–4 pages, 75%.
* **The Wythoff amusical permutation is on the same wall (80%).**  `W(2k) = ⌊kφ²⌋`,
  `W(2k−1) = ⌊kφ⌋` is OEIS A072061 (Kimberling).  Orbit-start density `0.025632` at `10^7` against
  the i.i.d. prediction `0.025583`, about half `U`'s, since its drift is about half (`0.0287` forward,
  `0.0281` backward).  Seven cycles, all with minimum `≤ 12` (Ren recomputed four); the other
  pairing has cycles of lengths 2, 7, 9, 16, 25, the (semi)convergents of `log 2 / log φ`, the
  same `2^t ≈ φ^c` mechanism as `U`'s 5- and 12-cycles.  One step is Fibonacci-automatic; orbits are
  not (orbit-start subword complexity matches random).
* **`U` is an interior point of a real family.**  In `W_α` (Beatty pairs `α, α/(α−1)`), `W_α → U` as
  `α → 3⁺` and `→ U(x − 2) + 2` as `α → 3⁻`; the predicted start density is continuous through 3
  and matches 26 of 29 irrational members within 0.5%.  Pisot or not makes no difference (Mignosi's
  dichotomy does not transfer, 80%).  The phase changes only at rational `α = p/q` with `p` even
  (75%); at `α = 2j` the evens are a trap (`2k ↦ 2jk`), so these are solved by the §55 trap theorem
  (densities `1/4, 1/3, 3/8` at `α = 4, 6, 8`; Ren checked `α = 4`).  For irrational `α` there is
  no proper invariant residue set (95%).  One loose thread: at `α = 2√m`, `W²` is nearly linear
  (`W²(n) ∈ {2n − 1, 2n − 2}` after two even steps for `2√2`), breaking the coin-flip model
  (`χ²/dof ≈ 490`) and shifting the density 1-3%, but with no trap.
* **A 20-year-old twin of Conway's 8.**  The `α = 2 + √2` member is OEIS A094077; Brockhaus (2006,
  A117149) lists its cycles `{1}, {2, 3}, {14, 23, 16, 27, 19}` and conjectures that the orbit of 4
  is not periodic.  The census reproduces those cycles; the orbit of 4 passes `4·2^24` both ways.

## 57. Theorem C closed on ℤ (paper): the reversible-machine lemma (2026-10-16, Opus agent; Ren checked)

Report: `undec-lemma.md`.  **Theorem C(1), ℤ form (paper, 90%).**  There is a computable `e ↦ σ_e`,
each `σ_e` an RCWA permutation of `ℤ` with every slope positive in `2^ℤ3^ℤ = ⟨3/2, 3/4⟩`, with one
orbit if `φ_e` is total and infinitely many otherwise.  Totality is `Π⁰₂`-complete, so on this
family "finitely many orbits" is `Π⁰₂`-hard.  Same-orbit is `Σ⁰₁`-complete via the highway alone
(88%); some member has a ZFC-independent orbit count (85%).  The ℕ form stays at 40% (§56).

* **The chain.**  Restart machine (A) → Bennett history wrapper in Morita normal form (H) → Gödel
  compile to 2 counters (G) → Kari–Ollinger forward/backward doubling through the highway (D).
  New is **Lemma M**: in a *structured* reversible machine (off a boundary set, every loop is a
  simple cycle whose lap moves the counters with both signs; boundary states halt unless guarded),
  every run infinite in either direction meets the boundary infinitely often, so garbage
  configurations never need state-by-state analysis.  Kari–Ollinger (MFCS 2008, opened) assert
  without proof that Morita's 2-counter conversion "preserves mortality status"; M + G prove it at
  every configuration.
* **Checks.**  A 10-state structured machine with ~50% garbage configurations, doubled to 20
  states, through the §56 pipeline: exact bijection (7,565 pieces); census of 32,000
  configurations with 0 cycles and 0 bi-infinite chains; orbit counts 1 (total) and 111, 1,075
  (divergent) as predicted.  The H + G compile (61 → 519 states) has 0 reversibility overlaps,
  the loop condition on all 153 cycles, 0 faithfulness failures in 6,588 junk configurations (Ren
  re-ran `lemma_hg.py`: PASS).  A first compile was not reversible (76 overlaps) and was fixed by
  compiling from Morita normal form.  Teeth: a dropped guard shows at the orbit level (77, 771
  junk cycles); a dropped clock and a permuted `τ` show at the census level only (their orbit-level
  effects sit beyond the windows checked).
* **Remaining.**  Morita's 2017 book for prior art (not opened); Lemma G's gadget bookkeeping at
  referee level (~2 pages); one compiled instance end to end (needs `r = 5^5`).

## 58. Theorem C in Lean: status, and Morita's book on the machine format (2026-10-16, Ren)

* **In Lean (axiom-clean, verified 2026-10-16 by `#print axioms`).**  Lemma P for `r = 25`
  (`RcwaEngine.lean`) and for every `r = 5^j` (`RcwaEngineGen.lean`): a linear piece with slope
  `2^{Nδ₁} 3^{Nδ₂ + s' − s}` moves the phase-coded state and both counters and fixes the junk.
  Completion and Lemma M, abstract (`RcwaMachine.lean`): `#orbits = 1 + #cuts` under (H1) and
  (H2) (`card_orbits`), and a structured machine's infinite runs meet the boundary infinitely
  often (`visits_boundary`, `visits_boundary_backward`).  Same-orbit (`RcwaSameOrbit.lean`): for a
  `Valid` reversible guarded-rule 2-counter machine and a source `c`, the completed permutation
  `σ` (an exact RCWA table, every slope in `2^ℤ3^ℤ`) has `enc c` and its highway successor in
  one cycle iff the machine halts from `c` (`sameCycle_enc_iff`); the reduction is computable
  (`computable_reduce`), so same-orbit is not computable (`not_computable_sameCycle`) **given**
  the hypothesis Prop `HaltingUndecidable`.
* **The one hypothesis.**  `HaltingUndecidable`: halting from a source is undecidable for `Valid`
  machines in the file's format.  Not yet in Lean: the orbit-count `Π⁰₂` layer (Lemmas A and D
  as theorems about `σ`'s orbit count).
* **Morita 2017, §9.2 (read for the model, `papers/2017-morita-theory-of-reversible-computing.pdf`).**
  Morita's counter machine (Def. 9.1-9.3) is a set of quadruples: a counter test `[p, i, Z|P, q]`
  or a count rule `[p, i, −|0|+, q]`, with a decrement allowed only from a positive counter.  Each
  quadruple is one `Rule` of ours (the test on counter `i`, `any` on the other, no move; or `any`
  tests and the move on counter `i`), and his syntactic determinism and reversibility (Def. 9.2:
  distinct rules sharing a source, resp. a target, are tests of one counter with opposite symbols)
  imply our semantic `Deterministic` and `Reversible`.  So his RCM(2) format sits inside ours.
  The constructions to transcribe are explicit quadruple lists: Lemma 9.2 (state-degeneration
  degree 2), Lemma 9.3 (history counter `k + 1`, one bit per irreversible merge), Lemma 9.4
  (Bennett: forward, copy, inverse quadruples `(δ′)⁻¹`), Lemma 9.7 (RCM(k) → RCM(2) through
  `∏ pᵢ^{nᵢ}`, with `pᵢ + 10` rules per count rule and `3pᵢ + 3` per test pair), and Theorem 9.2.
  Every correctness statement there is about runs from encoded inputs `(q₀, ∏ pᵢ^{mᵢ}, 0)`; the
  book does not treat other configurations.  The all-configuration clauses of `Valid` (no
  bi-infinite run anywhere, every finite run from any source ends at its paired sink) therefore
  rest on Lemmas M, H, G (§57), as `HaltingUndecidable`'s docstring says.  The format question
  is settled in our favor; the residual risk is in those lemmas' paper proofs.  `HaltingUndecidable`
  for this format: 92% (was 88%).
* **Route to an unconditional theorem.**  Mathlib has `ComputablePred.halting_problem` and
  `Turing.PartrecToTM2.tr_eval` (partial recursive codes run on a stack machine `TM2`).  Chain:
  `TM2` → Morita CM(k) (each stack a base-`b` numeral, push and pop by multiply and divide with a
  scratch counter) → Lemmas 9.3/9.4 (reversible, normal form) → Lemma 9.7 (two counters) →
  Kari–Ollinger doubling → `Valid` (Lemmas M, H, G).  That discharges `HaltingUndecidable` and
  makes `not_computable_sameCycle` hypothesis-free.

## 59. Theorem C hypothesis-free in Lean; the Wythoff family's even-numerator phase and a solved irrational line (2026-10-16, two Opus agents; Ren checked in part)

Reports: `wythoff-evenp.md`, `wythoff-2sqrtm.md`.

* **Theorem C in Lean, closed (axiom-clean, verified 2026-10-16 by `#print axioms`).**  The route
  of §58 is done: `HaltingUndecidable` is discharged and the `Π⁰₂` layer is in.  Headlines:
  `RcwaHalting.not_computable_sameCycle'`, `RcwaTotality.orbit_count_family'`, `oneOrbit_not_re'`,
  `oneOrbit_not_coRE'`, `not_computable_oneOrbit'`, `not_computable_finiteOrbits'`, and
  `RcwaOrbitCount.exists_table_iff_mortal` (one orbit iff the machine is mortal, else infinitely
  many).  Each depends only on `propext`, `Classical.choice`, `Quot.sound`.
* **Rational `W_{p/q±}` with `p` even: the itinerary is an exact Markov chain (Theorem M, 95%).**
  Every branch of an even-`p` member sends its domain onto one residue class mod `p`, of fixed
  parity, so the parity of `W(n)` is a function of the piece of `n`, and fresh randomness enters
  only through the odd moduli `q` and `R = p − q`.  The forward and backward parity itineraries
  are two-state Markov chains, independent given the parity of `x` (dependent without it); for odd
  `p` the same argument gives the i.i.d. law.  **Lemma 1 (99%)**: the involution `t ↦ q − t`
  pairs the even-branch images by opposite parity, leaving one unpaired piece (`t = 0`, image 0, on
  `+`; `t = q`, image `p − 1`, on `−`), so `P(E → E) = ½ ± 1/(2q)`.  Ren re-ran `cylinders.py`:
  every cylinder density is exact and Markov (128/128 for `10/3+`), and the i.i.d. law matches 0.
* **The density is the Markov survival constant `c_M`, not `c(r)` (CONJ 90%; `≤` PROVED 90%).**
  46 runs (23 values of `r`, both sides, `X = 10⁷`) match `c_M` with rms `z = 0.32`; the 28
  non-absorbing even-`p` runs miss the i.i.d. `c(r)` by `|z| ≥ 58`.  Examples: `10/3+` 0.099483
  (`10⁸`) vs 0.099478; `12/5−` 0.009493 vs 0.009493.  Ren's `ratc 10 3 −1 10⁷`: 0.049010 vs
  0.048961.  This settles §56's open integer `−` deficits (`4−`: 0.03733 at `10⁸` vs `c_M`
  0.037335).  **The ceiling** (90%): orbit minima have upper density `≤ c_M` for every rational
  member, via a depth-`L` two-sided test of density `P_L ↓ c_M`; so `W_{4−}` sits at
  `≤ 0.03734`, a third of `c(4) = 0.1088`.  **Prop. D** (97%): `+` over-weights the expanding
  branch in both time directions and `−` under-weights it, so the drift excess has the sign of the
  measured density excess (the density ordering itself is computed, not proved).
* **Where the traps are (Theorem T, 99% at the parity level).**  A parity class is absorbing iff
  the side is `+` and `q = 1` (Theorem E) or `R = 1`.  The second is Theorem E again:
  **Theorem E′** (100%, Ren paper-checked) `W_{2j/(2j−1)+}(n) = W_{2j+}(n + 1) − 1`, so that member
  has no finite orbit and density `½ − 1/p`.  Every other even-`p` member checked is
  residue-transitive at all moduli `M ≤ 600` (CONJ 85% at every `M`), so the §55 trap theorem has
  nothing to act on and these are wall phase.  The refinement of Conjecture B: a branch not onto
  `ℤ₂` gives a solvable member only when it makes a parity class absorbing; otherwise it reweights
  the masquerade constant, which still predicts the density to 0.1%.
* **The 2√m anomaly is 2-adic (CONJ 80%).**  Across 21 irrational members, the itinerary law
  departs from i.i.d. exactly when some composite slope over a nonempty word is rational with odd
  denominator (for quadratic `α`: `(α/2)²`, `(β/2)²` or `αβ/4`).  Even denominators (`√6`, `√10`,
  `√7`, `3 + √3`) show nothing, and a neighbour of `2√2` with `(α/2)² = 2·(2001/2000)²` shows
  nothing.  The same criterion reproduces the rational phase line (`p` even iff `α/2 ∈ ℤ_(2)`).
  Exact identities: on even-even steps `W²(n) = ⌊(α/2)²n − (α/2){kα}⌋` (for `2√2`,
  `{2n − 1, 2n − 2}`), and even runs are affine, `W^{2j}(n) − 2 = 2^j(n − 2)` for `2√2`, with
  length `O(log n)` by Liouville for `√m` (85%), so no cone.  A corrected model (exact 10 + 10
  window, order-6/8 Markov tails) predicts every one of 18 members within 0.3%, where i.i.d. was
  1-3% off; `c(2√2) = 0.03763 ± 0.00006`.
* **Theorem F: a solved irrational line (100%, Ren paper-proved the identity).**  For integer
  `r ≥ 2`, `α_r = 2r + 2√(r² − r)` and `β` its conjugate have `αβ = 4r`, so an even `n` with
  `W(n)` odd has `W²(n) = r·n` exactly.  Then even points increase along forward orbits, odd points
  above 1 decrease, and no two odd points follow an even one.  So `{1}` is the only finite orbit,
  every other orbit runs to `∞` both ways, its minimum is its first even point, and the minima
  number `d_r X + O(log X)` with `d_r = (r − 1 + √(r² − r))/(4r)` (`(1 + √2)/8` at `r = 2`).
  The partner `2r − 2√(r² − r)` has no finite orbit at all, same `d_r`.  Ren's independent check
  (`thmF.py`): 0 identity failures for `r = 2, 3, 5`, the monotonicity claim fails 9,999 times on
  `2√2` (teeth); orbit-minimum counts 60,356 vs 60,355.34 (`r = 2`) and 74,158 vs 74,158.16
  (`r = 3`).  These members sit at `α ≈ 4r − 1`, and their density `d_r` is not `c(α_r)`: the
  irrational line is not one phase.
* **For `U`.**  Nothing transfers to (a) (under 1%).  `U` has odd `p`, where Theorem M is the
  known i.i.d. law and the ceiling is the known `0.04978`.  Every composite slope of `U` has
  `v₂ = −a − 2b < 0`, so it sits strictly inside the generic side of the 2-adic criterion, and the
  `W² = r·n` mechanism of Theorem F needs a two-step slope in `ℤ_{≥2}`, where `U`'s are `9/4`,
  `9/8`, `9/16`.
* **Next.**  Lean: the rational layer (maps, Lemma 1, Theorems T, E, E′, M as finite-depth
  cylinder counts, Prop. D) and Theorem F claims 1-3 plus the exact count `A(X) − B(X)`.  Open:
  the density ordering `c_M⁻ < c(r) < c_M⁺`; residue-transitivity at every modulus; the 2-adic
  criterion at all word lengths; a parity-preserving `W³ = r·n` (e.g. the cubic `α = 2∛2`) for
  more Theorem F members.

## 60. The Wythoff family's 2-adic criterion, and a two-parameter solved family (2026-10-16, two Opus agents; Ren checked in part)

Reports: `wythoff-2adic.md`, `wythoff-solvable.md`.  Notation: `x = α/2`, `y = β/2`.

* **The 2-adic criterion, corrected (95%).**  The forward parity itinerary of `W_α` (irrational `α`)
  is i.i.d. at every depth iff `x` is *not* integral over `ℤ_(2)`, i.e. `x` is transcendental or
  its minimal polynomial has a coefficient with even denominator.  The mechanism is a fresh-digit
  lemma: step `j` is a fair coin given the past iff the prefix slope `Λ_j` lies outside the
  `ℤ_(2)`-span of `1, Λ_1, …, Λ_{j−1}` (Pontryagin duality on the hull `ℤ/M × T^d`).  The "if"
  direction is one valuation line: at a prime over 2 where `v(x) < 0`, also `v(y) < 0` (Ren
  checked the three cases), so the `v(Λ_j)` strictly decrease.  §59's wording (some composite
  slope rational with odd denominator) is sufficient but not necessary: `α = 1 + √5` has no
  rational composite, yet on even-even steps `W²(n) = W(n) + n − 1`, so `P(E | EE) = 0`.
* **"Only if".**  At depth 2 for every `α` (97%), with a closed form; for quadratic `α` the full
  iff (i.i.d. ⟺ `Tr x` or `N x` has even denominator), reproducing the third-parity law of §59 and
  2√2's `P(E | OE) = 1 − 1/(4 − √2) = 0.61327`.  For degree `D ≥ 3` a defect always sits at step
  `D` of `E^D`; it is proved `≠ ½` for `2∛2` and the plastic member, CONJ 90% in general.  The
  backward and joint laws carry no new arithmetic: a transfer lemma writes them through forward
  cylinder densities.  `U` (`x = 3/2`, `v₂ = −1`) is in the free class at every depth; these are
  natural-density statistics and do not see the orbit of 8.
* **Theorem K, an even trap (Ren checked).**  If `x² = bx + c` with `b, c ∈ ℤ` and conjugate
  `x′ ∈ (0, 1)` (`1 ≤ −c ≤ b − 2`), then on even-even steps `W²(n) = b·W(n) + c·n` exactly
  (`2lx = b·W(n) + c·n + {kα}x′`), so two consecutive evens stay even forever and there are at
  least `(¼)(1 − 2/α)X` infinite orbits meeting `[1, X]`; the measured entry density sits on
  that bound (`3 + √5`, `4 + 2√3`).  Ren's `thmK.py`: 0 failures on five members; teeth `x′ < 0`
  and `x′ > 1` fail.
* **Theorem G: Theorem F is one row of a solved family (97%, Ren checked the identity).**  For
  `m ≥ 0`, `r ≥ 2`, let `x ∈ (½, ¾)` be the root of `x^{m+1} − 2rx + r`, `β = 2x`,
  `α = 2x/(2x − 1)`.  The slope of the word `E Oᵐ` is `x^{m+1}/(2x − 1) = r`, and the floor error
  stays below 1, so `W^{m+1}(n) = r·n` on that word; odd runs after an even point have length
  `≤ m`.  So `{1}` is the only finite orbit, every other orbit runs to `∞` both ways, the minimum
  is the even `y` with `m + 1` odd predecessors, and the minima have density
  `(α − 2)/(2αβᵐ)`; the mirror has no finite orbit, same density.  Row `m = 0` is Theorems E and
  E′, row `m = 1` is Theorem F.  Ren's `thmGY.py`: 0 identity failures on `(m, r) = (1, 2)`,
  `(2, 2)`, `(2, 3)`, `(3, 2)` (`α` up to 28.8), runs bounded by `m`; teeth `r + 1` fails.
* **Theorem Y, a sporadic cubic (95%, Ren checked).**  `x³ + x² + 3x − 2 = 0`, `α ≈ 20.2623`.  No
  composite slope is an integer; instead on `E O³` the exact recurrence
  `W⁴(n) = 4n + W³(n) − W²(n)` holds, which is even, and the same classification follows.  Minima
  density `3/10 + x/8 + x²/10 ≈ 0.393408`; Ren measured 0.39335 at `2·10⁴`.
* **The engine is a monotone-potential lemma (Lemma P, 100%).**  If points off `S` strictly
  decrease (fixed points aside) and the first return to `S` strictly increases within bounded
  time, then the finite orbits are the fixed points, every other orbit is bi-infinite and runs to
  `∞`, and the minima are the points of `S` not in the return image.  For `W_α` with `α > 2`,
  `S` must be the evens, and the hypotheses hold iff odd runs after an even point are bounded by
  some `J` whose word slope exceeds 1.  For algebraic-integer `x` this reduces to a finite
  piecewise-affine phase automaton (90%).  Exact scans (about 280,000 roots: quadratics to height
  30, cubics to 9, monic quartics to 12, monic quintics to 5) find exactly the G members, Y and
  their mirrors (CONJ 60%: the rest is a finite sporadic set; CONJ 75%: solvable ⇒ `x` an
  algebraic integer).
* **The `r = 1` edge.**  The multinacci members (`x = 1/ψ_m`) have every point of `E Oᵐ` on an
  `(m + 1)`-cycle: infinitely many cycles.  At `α = 3 + √5` the set `{2k : {kφ} < ½}` is a
  W-invariant trap cut out by a Bohr set rather than a residue class; cycle minima have density
  `¼`, infinite-orbit minima `1/(4φ)`.
* **Near `U`.**  On `2 < α < 3 + √5` every irrational member fails Lemma P's hypotheses (85%); the
  only solvable member there is the rational `α = 4`.  `2∛2` is only approximate (`W³ = 2n − c`,
  `c ∈ {1, 2, 3}` on `EEE`, but the first return to the evens fails monotonicity at 25% of
  evens).  Nothing here bears on (a) (under 1%).
* **Which Theorem K members are fully solved (90% + computed).**  With `D = 2b + 4c − 1`, the
  even-odd two-step slope is `c/D + ((b + 2c)/D)·c₀`.  `D = −1` (`b = −2c`) is Theorem F;
  `D = 1, c = −1` is `3 + √5` (the Bohr-set trap above, minima exactly on K's entry bound).  Every
  other member fails Lemma P: `D = 1, c ≤ −2` (`5 + √17`, `7 + √37`) forces even-odd-odd and then
  unbounded odd runs, and `|D| ≥ 3` (`4 + 2√3` and six others) has odd runs of 14-20 after an even
  point.  K alone still gives every orbit meeting the trap a unique entry point and a strict rise;
  a census of 12 members (minima `≤ 2·10⁴`) finds every orbit a cycle (`{1}` and at most nine
  4-cycles) or a trap orbit (CONJ 70% in general; the gap is a Z-number-type question).
* **The degree-`d` trap identity (proved).**  If `A = α/2` is an algebraic integer with minimal
  polynomial `P` and `Q(t) = P(t)/(t − A)`, then on `d` consecutive even steps
  `W^d = Σ p_j W^j` exactly iff every non-leading coefficient of `Q` is `≤ 0` and `Q(1) > 0`.
  20 cubic members show 0 failures (Ren checked `A³ = 3A² − 1`, `α ≈ 5.7588`: `W³(n) = 3W²(n) − n`
  on 7,503 even-even-even points, 0 failures); eight cubics violating the condition fail.  None of
  the 20 is fully solved: the first return to the evens fails monotonicity at about 12.5%.

## 61. Which Wythoff members are solvable: algebraic integers, an automaton, and the G line as the minimal class (2026-10-16, Opus agent; Ren checked in part)

Report: `wythoff-classify.md`.  Here `x = min(α, β)/2`, the slope of the descending branch (`β/2`
for `α > 2`, as in Theorem G).  "Solvable" means Lemma P's hypotheses hold with `S` = evens: odd
runs after an even point are bounded and the first return to the evens increases.  In Lean on
main (`daf38cf`): Lemma P, Theorems G, K, Y and the golden member (§60, `docs/notes`).

* **Solvable ⇒ `x` is an algebraic integer (Theorem A, 95%).**  For `i ≥ 2`, step `i` of a run is
  deterministic exactly when `x` is integral of degree `≤ i`.  Otherwise, by the fresh-digit lemma
  of §60, the step continues with probability `½`, or `(N₀ ± 1)/(2N₀)` with `N₀` odd `≥ 3` when `x`
  is 2-integral but not integral; never below `1/3`, so runs of every length have positive
  density.  Transcendental `α` included.  So §60's CONJ 75% is now a theorem, and no 2-integral
  non-integral `x` is solvable.  Ren re-ran `thmA.py`: identical (`4 + 2√3` and `2√2` step ratios
  inside `[1/3, 2/3]` and `[3/7, 4/7]`; G(2,2) and Y have no runs past their bound).
* **The run as an automaton (Theorem N, 97%).**  For algebraic-integer `x` with minimal polynomial
  `P`, `Q = P/(t − x)`, a run's continuation is decided by the parity of `⌊Φ(g)⌋`, where `Φ` is
  linear in the free phases with the coefficients of `Q`: the other conjugates drive the run.
  0 mismatches against exact `W` on 70,000 runs (Ren re-ran `validate.py`: identical).
* **The G line is the minimal-run class (Theorem O, 95%).**  A run never reaches length `d`
  (`d = deg x`) iff `P = t^d − 2rt + r`.  **Theorem Q (92%):** the only solvable irrational
  quadratics are Theorem F's; `3 + √5` is the cycle boundary.  **Proposition F (93%):** if a
  periodic even-digit sequence of `Q` is reachable through the first step, runs are unbounded; the
  period-1 case is an explicit inequality in `Q(1)`, `Q(0)`, `2x − 1`, which certifies 91% of the
  unbounded cubics of height `≤ 8` and never fires on a bounded member.  CONJ (75%): bounded runs
  need every other conjugate outside the unit disk (0 of 2,985 roots with a conjugate inside are
  bounded).
* **Scans.**  Exhaustive cubics to height 100, quartics to 25, quintics to 10, sextics to 5, plus
  random samples (cubic height 1000, quartic 100) and families with `x → ½`: about 7 million
  roots.  Survivors are exactly the G line, Y, their mirrors and the multinacci boundary; the G
  members predicted outside every scanned range (`G(2, 60)`, `G(4, 40)`, `G(9, 2)`) pass exact
  checks to `10⁵`.  CONJ 60%: the solvable set is exactly these; CONJ 75%: the sporadic set is
  finite.
* **Y's mirror (92%).**  No finite orbit; every orbit tends to `∞` both ways; minima are the odd
  `y` with four even predecessors, at Y's density (786,810 vs `dX = 786,815.6` at `2·10⁶`).
* **A 7-cycle member (Ren checked).**  For `x³ − x² + 2x − 1 = 0` (`α ≈ 8.1592`),
  `x⁷ = (2x − 1)²`, so the word `E O E O⁴` has composite slope `x⁷/(2x − 1)² = 1`, and `W⁷(n) = n`
  on it: 9.4% of evens lie on 7-cycles.  Ren's independent check: `x⁷ − (2x − 1)² = 0` to 90
  digits, and `W⁷(n) = n` on all 9,427 hits among the first `10⁵` evens.
* **For `U`.**  `x = 3/4` takes a fresh 2-adic digit at every step, so no identity-potential
  classification of `U` exists for any `S`.  That rules out one method only; under 1% that this
  moves (a).

## 62. No residue trap on the rational line: Theorem RT (2026-10-16, Opus agent; Ren checked)

Report: `wythoff-transitive.md`.  `W_{p/q±}` is *residue-transitive mod `M`* when the digraph on
`ℤ/M` with an edge `a → b` whenever some `n ≡ a` has `W(n) ≡ b` is strongly connected.

* **Theorem RT (92%).**  For `p ≥ 3`, `gcd(p, q) = 1`, `R = p − q`, `W_{p/q±}` is
  residue-transitive mod every `M ≥ 2`, except the absorbing members of Theorem T (`p` even, side
  `+`, `q = 1` or `R = 1`), which are transitive exactly at the odd `M`.  This covers odd `p`, so
  `U = W_3` has no proper invariant residue set at any modulus.  At `p = 2` the statement fails
  (the `−` map is the swap `2k ↔ 2k − 1`, not transitive at even `M ≥ 4`), so §59's CONJ 85%
  needs `p ≥ 4`.
* **Proof shape.**  A window formula, `W(2y) = (py − j)/q` with `j` the unique element of a window
  of `q` consecutive integers with `j ≡ py (mod q)` (and the same with `R` on the odd branch),
  drives every step.  Base case `M = 2^e M₀`, `gcd(M₀, 2pqR) = 1`: the residue digraph carries
  the stationary law `φ × uniform` (`φ` the forward parity chain's), which has full support exactly
  when the chain is not absorbing, so every edge lies on a cycle and weak connectivity (step by
  `1/q`) gives strong connectivity.  Then prime by prime: Lemma D lifts powers of 2 when `4 | p`
  through `W⁻¹` (which expands 2-adically), Lemma B adds the odd primes of `p` (where `W⁻¹`
  expands), Lemma A adds the primes of `qR` (where `W` expands; a routing argument through
  parities).  The 8% reserve is Lemma A's valuation bookkeeping.
* **Checks.**  The agent's scan (`transitive.py 300 24`): 113,046 (member, `M`) pairs, all
  `p ≤ 24`, both sides, `M ≤ 300` plus mixed prime powers to 6000, 0 mismatches with the
  prediction; the 22 absorbing members fail at every even `M` and pass at every odd `M`.  Ren's
  independent checker (built on the Lean `wythoff` definition): 4,136 pairs (`p ≤ 12`, `M ≤ 48`),
  0 mismatches; `U` transitive for `M ≤ 40`; the `p = 2` swap fails exactly at even `M ≥ 4`.  Ren
  re-ran the exact proof-step checks (`steps.py`): identical.
* **What it buys.**  For non-absorbing members there is no eventually periodic `C` with
  `W(C) ⊆ C`, on `ℤ` or `ℕ⁺`, so the §55 trap theorem has nothing to act on: along the rational
  line, "solvable by a periodic trap" is equivalent to "parity chain absorbing".  It says nothing
  about whether infinite orbits exist, and leaves non-periodic routes open (Bohr-set traps as at
  `3 + √5`, Lemma P potentials, conjugacies).  Under 1% that this moves (a).
* **Side answer to §59's question on `4 | p`.**  The 2-adic contraction does show at moduli `2^e`,
  `e ≥ 2`: `φ × uniform` is not stationary there (0 of 752 exact checks); transitivity survives
  because Lemma D goes through `W⁻¹`.

## 63. Bounded runs force a Pisot-dual slope: Theorem N3 (2026-10-16, Opus agent; Ren checked)

Report: `wythoff-pisot.md`.  Notation as in §61: `x = min(α, β)/2`, `P` its minimal polynomial,
`Q = P/(t − x) = Σ q_k t^k`, `q̃_0 = q_0 + 2a_0`.  In Lean on main since §62: Theorem RT
(`WythoffResidue`, #65) and the degree-`d` even trap (`WythoffTrapDegree`, #64).

* **Theorem N3 (92%).**  If `x ∈ (1/2, 1)` is an algebraic integer with some other conjugate in
  the closed unit disk, runs after up-points reach every length with positive density, on both
  sides, so `W_α` is not solvable.  With Theorem A: **bounded runs ⇒ `x` is an algebraic integer
  whose other conjugates all lie in `|z| > 1`**; for a unit, `1/x` is a Pisot number in `(1, 2)`.
  The unit-circle case is included.  §61's CONJ 75% is now a theorem.  The converse fails
  (`x³ + 2x − 2`: all other conjugates at `|z| = 1.61`, runs unbounded).
* **Proof shape.**  In half-scale `ε = G/2` the run criterion of §61 reads: some `ε ∈ (0, ½)^n`
  makes the standard rows `R_i = Σ q_k ε_{i+k}` (`i ≥ 1`) and the top row
  `T = R_0 + 2a_0 ε_0` integers.  (1) The constant `γ = (1 − x)/|P(1)| < ½` is always a fixed
  point, with every row `Q(1)γ = ±1`.  (2) A conjugate with `|x_s| ≤ 1` gives the homogeneous
  direction `c_i = Re(x_s^i)`, with `c_0 = 1` and `|c_i| < 1` for `i ≥ 1` (on the circle because
  `x_s` is not a root of unity).  Sliding `γ + κc_i` puts `ε_0` on `{0, ½}`, where `T` is
  automatically an integer, and keeps every later entry strictly inside.  (3) A compensating
  homogeneous perturbation on indices `≥ 1` (it exists because `q_0 = −a_0/x ≠ 0`) moves `ε_0`
  inside while keeping `T` integral.  The 8% reserve is the imported run criterion (§61, 95-97%).
  Ren paper-checked steps (1)-(3): `P(1) = (1 − x)Q(1)`, real `q_k` keep `Re` homogeneous, both
  `κ` cases land strictly inside, and the perturbation coefficient is `Re(−ω q_0/x_r)`.
* **Checks.**  120-digit certificates succeed on 6 members, including the Salem-type
  `x⁴ − x³ − x² − x + 1`, and fail on all 5 bounded members tried (teeth).  The population
  certificate succeeds on 616 of 616 roots with a non-expanding conjugate and fails on 501 of 501
  without.  Ren re-ran `n3cert.py`, `popcert.py 3 6` (byte-identical) and `pairchain.py`.  Ren's
  independent check (own `W` from mpmath roots, guarded 400-bit floors, every up-point to
  `3·10⁵`): maximum run grows `8 → 11 → 14` on the Salem-type member, `9 → 17` and `8 → 19` on two
  cubics with a conjugate inside the disk, and stays at 2 on G(2, 2) and 4 on `x³ + x − 1`.
* **Toward CONJ C′ (sporadic set finite; still 75%).**  Bounded runs now give Mahler measure
  `M(P) = |a_0|/x < 2|a_0|`, so `|a_k| < 2·C(d, k)·|a_0|` and each `(d, a_0)` admits finitely
  many members (92%).  For solvable members, `2^d P(1/2)` odd gives
  `J + 1 < log(2·3^{d−1}|a_0|)/log(1/x_d*)`, with `x_d*` the root of `t^d = 2t − 1` in `(½, 1)`
  (95%).  Together these make an exhaustive list complete within its box (COMPUTED): cubics with
  `|a_0| ≤ 40` give exactly G(2, 2..40) and Y; quartics with `|a_0| ≤ 8`, exactly G(3, 2..8);
  quintics with `|a_0| ≤ 2`, exactly G(4, 2).  Missing for C′: a degree bound, and an `|a_0|`
  bound off the G line.  CONJ C (solvable set = G line, Y, mirrors) 65%.
* **§62's question on `U`'s 120 partition pairings.**  The 48 TRAP pairings are exactly the 48
  with an absorbing parity chain (144 of 144 with the S4 family).  Absorbing is equivalent to
  `0(2) ↦ 2(6)` or `4(6)`.  Non-absorbing ⇒ no trap is computed to `M = 48`, not proved.
* **For `U`.**  `x = 3/4` is not an algebraic integer, so N3 adds nothing beyond Theorem A.
  Under 1% that this moves (a).

## 64. The sporadic set is finite in each degree (2026-10-17, Opus agent; Ren checked in part)

Report: `wythoff-finite.md`.  Notation of §61 and §63; `q̃_0 = q_0 + 2a_0 = a_0(2x − 1)/x`,
`N = 2^d P(½)` (odd).  In Lean on main since §63: Theorem N3 (`WythoffPisot`, #68) and the run
criterion from Weyl (`WythoffRunCriterion`, #69), so N3's headline is conditional on Weyl alone.

* **Lemma U\* (same confidence as the run criterion).**  If `|q̃_0| > 1`, runs are unbounded:
  the constant tail `ε_i = 1 − x` has every standard row `= P(1)`, and the top row needs an
  integer strictly between `q̃_0/2` and `q̃_0`.  So bounded ⇒ `|q̃_0| < 1`, i.e.
  `x < |a_0|/(2|a_0| − 1)`, and `1 ≤ |N| < 3^{d−1}`.  This explains the unbounded member
  `x³ + 2x − 2` of §63 (`|q̃_0| = 1.41`, every other conjugate at `1.61`).  Ren's checks: the
  whole G line (`d ≤ 10`, `r ≤ 1000`, proved solvable in Lean) has `|q̃_0| ≤ 0.586`, and Y,
  tribonacci, `x³ + x − 1`, `x³ − x² + 2x − 1` are all below 1; Ren's exact `W` on `x³ + 2x − 2`
  gives maximum runs `8 → 15` up to `3·10⁵`.
* **Theorem C′(d) (80% given the run criterion, N3, B2; about 70% end to end).**  For each
  degree `d`, only finitely many solvable members lie off the G line `t^d − 2rt + r` (mirrors
  included).  Not effective.  Proof shape: (1) *Lemma FL*: bounded runs make a lattice translate
  miss the cube `(0, ½)^{n+1}`, so the flatness theorem gives a bounded integer `v` with `v·h_j`
  nearly integral (`h_j` the complete symmetric functions of the `1/x_s`).  (2) *Theorem L*: as
  `|a_0| → ∞` every other conjugate escapes to `∞` or converges to a root of unity (the limit
  `h_j` have polynomially bounded denominators, so `1/Σh_jz^j` has no zero in any open `p`-adic
  unit disk, hence lies in `ℤ[z]`; then Kronecker).  (3) *Case A*, a conjugate near a root of
  unity: sliding a periodic orbit along it with `ε_0` on the grid `(1/(2a_0))ℤ` (Lemma SG) gives
  runs of length about `log|a_0|/log|x_s|`, far past B2's cap `(1 + o(1))log₂|a_0|`.  (4)
  *Case B*, all escape: `P = E + a_0(1 − 2t)` with finitely many `E`, and only `E = t^d` passes
  the limit of Theorem O's sum test (Lemma O∞); every other `E` has unbounded runs for large
  `|a_0|` by a tracking construction (Lemma T).  The weakest step is Theorem L (85%).  Ren
  paper-checked U\*, the half-point identity, Lemma O∞, FL step 1 and Theorem L's `p`-adic and
  Kronecker steps; Case A's periodic orbit and Case B's uniformity are the agent's.
* **Units reduce to a Pisot statement.**  A solvable unit of degree `d` would make `1/x` a Pisot
  number of degree `d` in `(ψ_d, 2)`, `ψ_d` the `d`-bonacci number.  CONJ P (90%): there is
  none.  COMPUTED: none for `d ≤ 7` (the `d = 6` Salem number `1.98779` is excluded by N3; control
  windows find `ψ_d`, Amara's limit points and other Pisot numbers), and none among 1,789 regular
  Pisot numbers of degree up to 35.  For non-units nothing bounds `d`; by C′(d), CONJ C′ is now
  equivalent to a degree bound.
* **Complete lists (COMPUTED).**  Cubics `|a_0| ≤ 1000`: exactly G(2, 2..1000) and Y (4.0
  million candidate roots).  Quartics `|a_0| ≤ 20`: exactly G(3, 2..20).  Quintics `|a_0| ≤ 8`:
  exactly G(4, 2..8).  Sextics `|a_0| ≤ 3`: exactly G(5, 2..3).  Ren re-ran `checks.py`
  (identical) and the cubic `|a_0| ≤ 40` enumeration (the same 40 survivors, = §63's list).
* **Status.**  CONJ C′ 85% (was 75%); CONJ C (solvable set = G line, Y, mirrors) 75% (was 65%).
  The bounded-but-not-solvable residue off the G line looks cyclotomic (a conjugate near a root
  of unity), as Theorem L predicts.  For `U`: nothing new (`x = 3/4` is not an algebraic
  integer).  Under 1% that this moves (a).

## 65. The solvable cubic members are G(2, r), Y and their mirrors (2026-10-17, Opus agent; Ren checked)

Report: `wythoff-cubic.md`.  A cubic member is `P = t³ + bt² + a₁t + A` (`A = a₀`), other roots
`y, z`, `h_j` the complete symmetric functions of `1/y, 1/z`.  In Lean on main since §64:
Lemma U\*, Corollaries U1-U2, Lemma SG and Lemma O∞ (`WythoffUStar`, #71).

* **Classification (92% given the run criterion, N3, U\*/U2; about 80% end to end).**  A cubic
  member is solvable iff it is G(2, r) = `t³ − 2rt + r` (`r ≥ 2`), Y = `t³ + t² + 3t − 2`, or a
  mirror.  "If" is Theorems G and Y (in Lean).  For `|a₀| ≥ 800` "only if" is Theorem C3, proved
  with a finite interval-arithmetic check; for `|a₀| < 800` it is computed, by two independent
  pipelines that agree member by member.
* **Exact setup.**  Under bounded runs, U2 gives `N = 8P(½)` odd with `|N| ≤ 7`, and every
  cubic member is a triple `(A, b, N)`: `P = (1 − 2t)(A − bt/2) + t³ + ((N − 1)/4)t`.  Then
  `h₁ = (b + x)x/A`, `h_j = h₁h_{j−1} + (x/A)h_{j−2}`, `q̃₀ = N/(4 − 2h₁ + e₂)`.
* **Proof shape of Theorem C3.**  *Lemma K:* adding `(Δ/q₀)h_{j−i}` to a period-1 or -2 base orbit
  at indices `1..j` keeps every standard row integral (only `R_j` moves, by `Δ`) and shifts the
  top-row quantity by exactly `−Δh_j`; if the points `{−Δh_j}` fill the top-row window, runs are
  unbounded.  *Proposition R:* at level 1 this fails only if `h₁` is within `O(1/|A|)` of `p/q`
  with `q ≤ 12` (gap bounds for arithmetic progressions mod 1); then `h_n ≈ (p/q)^n` fills at a
  level `n ≤ 4` unless `q = 1`.  `q = 1` leaves `p = 0` (small `|b|`: five shapes, each with an
  explicit Lemma T ball for all `|A| ≥ 800`, and the sixth shape `(b, N) = (0, 1)` is exactly the G
  line) or `p = ±1` (a conjugate within `2/|A|` of `±1`: Lemma SG gives runs of length `≥ 3543` at
  `|A| = 800`, against a solvability cap of `13.6`).  All bounds are monotone in `|A|`.
* **Ren's checks.**  Paper: the triple form (I1), `h₁`, `e₂`, the recursion, `q̃₀` via H½, and
  Lemma K's row and top-row shifts.  Re-ran `effective.py 800` (0 failures, identical) and
  `effective.py 750` (fails at `p/q = −10/11, −9/11`: the teeth), and `percert.py 201 1000`
  (3,839,200 candidates; uncertified = exactly the 800 G members).  Ren's independent certificate
  code (U\*, Lemma K to level 6 with the full `Δ` range, Lemma SG, a brute-force Lemma T; every
  certificate an explicit sequence verified at 60 digits): at `A = 800, −801, 1234, −2000` every
  off-G candidate is certified (≈ 28,000 candidates after the N3 and U\* windows), and the G
  member stays uncertified.
* **CONJ P (units; still 90%).**  Partial: if `θ ∈ (ψ_d, 2)` is a Parry number, its Parry
  polynomial has degree `≥ d + 1`, so CONJ P holds whenever that polynomial is irreducible, and in
  general it is a cofactor-degree bound.  The degree-6 Salem number `1.98779` lies in `(ψ₆, 2)`, so
  any proof must use the Pisot hypothesis.
* **Status.**  The cubic case of CONJ C is settled at the confidence above.  CONJ C′ stays 85%
  (degree bound open).  Next: the same method for quartics (`h₂` enters `q̃₀`).  For `U`: nothing
  new.  Under 1% that this moves (a).

## 66. The solvable quartic members are G(3, r) and their mirrors (2026-10-17, Opus agent; Ren checked)

Report: `wythoff-quartic.md`.  A quartic member is `P = t⁴ + b₃t³ + b₂t² + a₁t + A`; under
bounded runs U2 gives `N = 16P(½)` odd with `|N| < 27`, so a member is a quadruple
`(A, b₃, b₂, N)`.  `B(z) = Q(z)/q₀ = 1 − h₁z + e₂z² − e₃z³`, with `h₁ = q₁x/A`, `e₂ = −q₂x/A`,
`e₃ = x/A`.

* **Classification (88% given the run criterion, N3, U\*/U2, B2, Theorems O/M, Lemmas T and SG;
  about 75% end to end).**  A quartic member is solvable iff it is G(3, r) = `t⁴ − 2rt + r`
  (`r ≥ 2`) or a mirror: there is no quartic sporadic member.  For `|a₀| ≥ 650` this is Theorem
  C4, proved with one monotone interval-arithmetic check (`effective4.py 650`); for `|a₀| < 650`
  it is computed: complete enumeration (`|a₀| ≤ 250`: 180,884,390 candidates; `251-649`:
  2,980,166,430), with automaton witnesses and explicit certificates agreeing on `|a₀| ≤ 250` and
  on the 2,042 members of the 13 class boxes the interval route leaves open in `251-649`.
* **Proof shape of Theorem C4.**  The two-dimensional version of §65.  Multi-row perturbations
  shift the top-row quantity by `−Σ Δ_j h_j` (Lemma K\*), so bounded runs force every `h_j` within
  `O(1/|A|)` of rationals whose denominators have lcm at most `1/ℓ ≤ 37` (Lemma AP-rel: one
  level's progression spreads around the lcm grid of the others).  The region `|x_s| > 1` is
  exactly Jury's test on `z³B(1/z)` (Lemma R4).  Near eight of the nine Kronecker points of
  `(h₁, e₂)` a conjugate sits near the unit circle, and Lemma SG kills a whole neighbourhood
  (certified by a Jury test on `B(Yz)`).  The ninth, `(0, 0)`, leaves 22 shapes `(b₃, b₂, N)`: 21
  get explicit Lemma T balls, and the 22nd is the G line.  Teeth: the same check fails at
  `|a₀| = 620` (1 class) and `600` (2 classes), each the predicted class.
* **Cancellation classes.**  The only obstruction between 250 and 650: `h₁ ≈ ±1/q`, `h₂ ≈ 0`,
  `e₃ ≈ h₁³` at `|A| ≈ q³/2` (`q = 8, 9, 10`), where `P ≈ (t − ½)(t − q)(t² + q²)`.  Gap arguments
  are borderline there; all 96 members get explicit infinite sequences.
* **Ren's checks.**  Paper: the quadruple form, `B(z)` and its coefficients, Lemma R4's reduction
  to Jury's conditions (`a₂ = −h₁`, `a₁ = e₂`, `a₀ = −e₃`).  Re-ran `effective4.py 650` (0
  failures) and `620` (1 failure, the teeth).  Ren's independent degree-`d` certificate code (U\*,
  Lemma K to level 6, SG, Lemma T; every certificate an explicit sequence verified at 60 digits):
  all 96 cancellation members certified; 300 + 300 uniformly random N3-passing candidates at
  `A = 650` and `A = −651` all certified; of 150 random members from the hardest residue (the 956
  that needed the agent's exhaustive row search), 146 certified directly and the other 4 by an
  exhaustive Lemma T scan; G(3, 200) and G(3, 650) never certified.
* **Status.**  CONJ C at degrees 3 and 4 is settled at the confidences above (§65, §66): the only
  sporadic solvable member through degree 4 is Y (and its mirror).  CONJ C′ stays 85% (a degree
  bound is still open).  CONJ (65%): at degree 5 the exhaustive row search, not gap bounds, is
  the certificate that scales.  For `U`: nothing new.  Under 1% that this moves (a).

## 67. Quintic members: solvable ⇒ G(4, r) for |a₀| ≥ 45,000 and in the computed ranges (2026-10-17, Opus agent; Ren checked)

Report: `wythoff-quintic.md`.  The §65/§66 method at degree 5: `N = 32P(½)` odd, `|N| ≤ 79`,
`B(z) = Q(z)/q₀` of degree 4, three-dimensional residual analysis in `(h₁, h₂, h₃)`.

* **Theorem C5 (85% given the run criterion, N3, U\*/U2, B2, Theorems O/M, Lemmas T and SG;
  about 70% end to end).**  Every quintic member with `|a₀| ≥ 45,000` off the G line
  `t⁵ − 2rt + r` (and its mirror) is unsolvable.  One uniform interval-arithmetic class tree
  (`effective5.py 45000`, every odd `|N| ≤ 79`).  New tools: a Schur-Cohn reduction of the
  degree-4 stability region to a cubic Jury test (Lemma R5), SG applied to whole boxes intersected
  with stability at the SG radius (Lemma SGJ\*), which removes every non-origin Kronecker class,
  and the identity `Ψ = −Σ h_m R_m` for bounded sequences with integral rows (Lemma Ψ).  The G
  shape is refused a Lemma T ball at every rung.  Teeth: the tree at 44,000 fails on exactly one
  class, the predicted cancellation class `h₁ ≈ −1/17`.
* **Computed.**  `|a₀| ≤ 50`: complete enumeration (148,764,512 candidates), automaton witnesses
  and certificates (ending in an integer-program head search) each leave exactly G(4, 2..50).
  `1,200 ≤ |a₀| < 45,000`: trees at 5,000, 2,500 and 1,200 fail only on explicit boxes, and all 523
  members inside them get explicit infinite feasible sequences (80 digits).  **Open: `51 ≤ |a₀|
  < 1,200`** (projected about 6 hours on 8 processes to reach 100 by enumeration; further tree
  rungs at 600, 300, 150 are the cheaper route, with a likely stall below about 100).
* **Obstruction families.**  Quintic cancellation classes: `h ≈ (±1/q, 0, 0, 0)` at
  `|A| ≈ q⁴/2`, `A < 0`, `P ≈ (t − ½)(t⁵ ± q⁵)/(t ± q)`; in the exact model `Ψ = u(ε₅ − R₁)`, the
  reachable set is a half-grid and the window sits beside an integer, so gap arguments cannot close
  below `q ≈ 1/(2ℓ) ≈ 16`, which is why `A(5) ≈ 17⁴/2`.  All 162 members in `[2,500, 45,000)` are
  certified.  A second family near `|A| ≈ 1,200-2,500`, at the cusp where three conjugates
  coalesce near `−1.58`, is probably an artefact of the box method (CONJ 70%); its 255 members are
  certified.
* **Ren's checks.**  Re-ran the tree at 45,000 (48 jobs, 0 failures) and 44,000 (one job, one
  failing class: the teeth).  Ren's independent certificate code (sped up with float prefilters;
  every certificate an explicit sequence verified at 60 digits): 100 + 100 uniformly random
  N3-passing candidates at `A = 45,000` and `−45,001` all certified; 200 members of a family built
  to sit near Theorem L's limit shapes, `P = t⁵ + E(t) + r(1 − 2t)K(t)` with `K` a product of
  cyclotomic factors, `E` small and `|r| ∈ [45,000, 60,000]` (the region where Lemma SGJ\* does
  the work), all certified by U\* or Lemma K, independently of SGJ\*; G(4, 45,000) and
  G(4, 50,000) never certified.
* **Status.**  Through degree 4 the solvable set is settled (§65, §66); at degree 5 the only gap
  is `51 ≤ |a₀| < 1,200`, where no non-G member is known.  CONJ C′ stays 85%.  For `U`: nothing
  new.  Under 1% that this moves (a).
