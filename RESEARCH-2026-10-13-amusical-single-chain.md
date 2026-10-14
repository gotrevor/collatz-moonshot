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
  rewiring changes it (FS density `0.213` for `U`, `0.056` for `τ`).  So it is the right
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

