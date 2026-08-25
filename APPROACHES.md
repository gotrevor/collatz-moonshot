# The Approach Map 🌀

*The three most likely routes to a proof of the Collatz conjecture, the barriers any route must survive, and the combinations the field may have overlooked.*

> AI-assisted strategy sketch, drafted by Claude (“Ren”) from a 2026-07-20 planning session with Trevor. It is a
> strategy sketch, not settled mathematics.  Confidence levels are calibrated opinions,
> not literature facts.

## Why this repo 🌙

The target is the root conjecture itself: every positive integer's Collatz orbit reaches 1.
Not been done.  Will require new math.  This repo is the strategy layer - the map of
approaches, the barrier analysis, and (eventually) the Lean vocabulary skeleton that turns
each approach into pinned, checkable statements.

We start from an unusual seat:

- **[tao-collatz](https://github.com/gotrevor/tao-collatz)** - our complete, axiom-clean
  formalization of Tao 2019 (*almost all orbits attain almost bounded values*), the
  frontier statistical result.  Its fine-scale mixing machinery (Prop 1.14) is a
  quantitative equidistribution input no other formal development has.
- **collatz-cryptid** (a separate private predecessor, not included here) - the looking-glass repo: cycle
  effectivity hub (`Effectivity.lean`: `|2^L − 3^n| ≤ R(e)`), the Erdős/carry bridge
  (`Carry.lean`, `CarryProcess.lean`, the odometer avalanche), the Sturmian/Cobham
  panel (`Sturmian.lean`), the Furstenberg-stiffness axiom, and the BB/generalized-Collatz
  classification (`Classification.lean`).

## The design constraints - a creativity filter 🚧

Three barriers.  An approach that does not answer all three is dead on arrival.

### 1. The 3x−1 barrier (statistics cannot finish)

A purely statistical/drift argument applies verbatim to the 3x−1 map, which has honest
nontrivial cycles (5 and 17).  So statistics alone can never prove "every orbit reaches 1."
(Recorded in collatz-cryptid; see also the arithmetical-hierarchy analysis there: the
divergence half of Collatz is genuinely Π⁰₂-shaped.)

**The underappreciated corollary: the proof will almost certainly be TWO proofs.**

- An ergodic/statistical/structural argument killing **divergence** - where 3x+1 and 3x−1
  genuinely behave alike, and both are believed divergence-free.
- An **arithmetic** argument killing cycles - where the +1 vs −1 distinction lives, and
  where Baker-type methods already see the difference.

Most attack sketches in the literature try to do both halves with one tool.  That is a
mistake, and recognizing the split is itself a piece of strategy the field underuses.

### 2. The qualitative density barrier (a.e. ≠ all)

Tao's method proves logarithmic density 1, and no constant-tightening crosses to "all n"
(settled with Trevor 2026-07-18, ~95%).  The exceptional set is density-zero but scattered
across all scales - it is not an initial segment, so "verify below X, prove the rest"
cannot work.  Whatever kills divergence must see **individual orbits**, not measures of
sets.

### 3. Conway's undecidability (there is no *general* method)

Generalized Collatz maps are Turing-complete: Conway 1972 simulates any Minsky (counter)
machine by a rational game, even with all `b_i = 0`, and his COROLLARY is that no algorithm
decides, **given** such a `g` **and** a starting `n`, whether some `g^k(n) = 1`.  Kurtz-Simon
2007 strengthen this to the universally quantified version ("does `g` reach 1 from *every*
`x`?") and show that problem is **Pi^0_2-complete**.  (Note: it is the *totality* question that
is Pi^0_2-complete; the halting-style question is only Sigma^0_1.)

WARNING: **this is a heuristic filter, not a barrier theorem, and the primary sources say so
themselves.**  Both results quantify over `g`: they deny a *uniform* method for the family.
Neither says anything about the single instance `3n+1`, whose truth value is determinate and
whose ZFC-provability is untouched.  Conway, in the 1972 paper itself:

> "Of course, particular games of this type can still have predictable properties, so that
> (for instance) **our theorem says nothing about the Collatz game.**  But it does prohibit any
> general solution to games of this type, and also shows that there exist special cases for
> which the prediction problem is unsolvable."

And Kurtz-Simon describe their own contribution as "a good heuristic explanation for the
apparent difficulty of the problem."

**What it licenses**: "no method uniform across generalized Collatz maps can work."
**What it does NOT license**: "any proof must consume 3n+1-specific structure."  The second is
a good design instinct and we go on using it, but it is *our* heuristic, not Conway's theorem.
Do not price a route down for failing this filter - doing so once wrongly penalised the
transducer / certificate-search lane, whose matrix interpretations consume the actual
coefficients and so pass the filter anyway.

**Sub-question RESOLVED (2026-08-22, ~85%): yes - undecidable instances CAN have negative
drift**, so "Collatz has negative drift" does not move 3n+1 out of the undecidable family's
shadow.  Shrink-prime padding argument:

Given Conway's `g` (modulus `P`, multipliers `a_i`, simulation states and multipliers all
smooth over the machine's finite prime set `S0`), pick fresh primes `Q_1 < ... < Q_t`
outside `S0` and coprime to `P`.  New modulus `P' = P*Q_1*...*Q_t`; on a residue class
divisible by some `Q_j` (least such `j`) set `g'(n) = n/Q_j`; elsewhere `g' = g`.  Then:
(a) *simulation untouched* - every orbit from a start state `2^k` is `S0`-smooth, so no
shrink rule ever fires on it, and `(g', 2^k)` answers exactly as `(g, 2^k)`: the instance
problem stays undecidable; (b) *drift goes negative* - the class-averaged
`log GM = delta_t*A - (shrink mass)`, where `A` is `g`'s old average and
`delta_t = prod(1 - 1/Q_j)`.  Since the tail of `sum 1/p` over primes diverges, `delta_t -> 0`
(Mertens), while the shrink mass stays bounded away from 0 (at least `(log Q_1)/Q_1`), so for
`t` large the geometric mean is `< 1` - indeed arbitrarily small.

Two honest caveats.  (1) This kills the *class-averaged* drift filter (the naive/Collatz-
heuristic notion).  A *visit-weighted* drift hypothesis is a different, dynamical condition -
but that can't be read off the map's syntax, so it is useless as a decidability criterion
(checking it is as hard as the dynamics).  (2) Scope is Conway's instance form (given `g`
and `n`).  For the Kurtz-Simon forall-form: their Theorem 2.3
(verified from the draft, 2026-08-22) converts `M` into `M'` with `M` total iff `M'` halts
from EVERY configuration - and the non-totality witness is a clean configuration encoding,
smooth over the machine's primes, hence coprime to the shrink primes.  So padded garbage
funnels to `Q`-free numbers and the reduction closes.  ✅ 2026-08-23: the published Sec. 3
(read from the published chapter via institutional access; summary in `papers/kurtz-simon-2007-gcp-summary.md`)
verifies every joint: universal totality handles garbage configurations, and the
impossible-residue rule (`a_r = 1/m`, strictly decreasing) handles invalid integers - both
compose with the shrink primes (~97%; residual = not machine-checked).  💡 Bonus: the KS
construction already carries built-in contraction (every impossible residue gets `1/m`), so
the canonical undecidable instances are plausibly negative-drift even without padding.  Not yet machine-checked; the argument is elementary enough that Lean-ing it
would be a pleasant afternoon, not a campaign.

Related: Conway 2013 ("unsettleable") in `papers/2013-conway-unsettleable-summary.md` - the
folklore overstates that one in exactly the same direction.

## Approach 1 - Measure rigidity: the ×2×3 route 🏔️

**Most likely, ~40% conditional on Collatz being solved at all.**

**Core move**: treat a counterexample as a witness that manufactures an impossible object.
A divergent orbit has an orbit-closure in ℤ₂; averaging gives an invariant measure for the
Syracuse map.  Collatz secretly intertwines mod-2 structure (the halvings) with ×3
structure (the odd step) - exactly the setting of Furstenberg's ×2×3 phenomenon, where
Rudolph-Johnson says a jointly invariant measure with positive entropy must be Lebesgue.

The division of labor is what makes the architecture coherent:

- Lebesgue measure is not concentrated on one orbit → rigidity kills **divergence**.
- Atomic invariant measures are exactly **cycles** → handed off to transcendence methods
  (Approach 3), which distinguish +1 from −1.

Note how cleanly this passes the 3x−1 test: rigidity *permits* atomic measures, 3x−1's
cycles are atomic, and only the arithmetic half sees the sign.  Most sketches fail this
test; this one is built around it.

**The new math needed**:

1. An **intertwining theorem** upgrading Syracuse-invariance to genuine
   ×2,×3-semigroup structure.  The Syracuse map is a skew product over the 2-adic
   odometer, not the ×2×3 action itself - this gap is where 90 years of failure hides.
2. Either an **entropy-generation theorem** (a divergent orbit forces positive entropy
   into its limit measures), or **zero-entropy rigidity** - which is the open heart of
   Furstenberg's ×2×3 conjecture itself.

**Honest reading**: Collatz may be Furstenberg-hard.  But partial rigidity should still
yield real waypoint theorems ("no divergent orbit of positive Banach density", exotic-
measure exclusions), each formalizable.

**Our assets**: the formalized fine-scale mixing in tao-collatz; the
`furstenbergStiffness` axiom in collatz-cryptid already names the digit-level version of
the needed rigidity.

## Approach 2 - Symbolic dynamics + transducers: the Cobham route 🤖

**~25% conditional.**

**Core move**: the Bernstein-Lagarias conjugacy makes Collatz-on-ℤ₂ literally the shift
map on parity vectors; the conjecture becomes a statement about where ℕ sits inside ℤ₂
under that conjugacy.  Meanwhile ×3 is a finite-state transducer in base 2 and ÷2 is the
shift, so orbits are iterated transducer compositions.

Cobham's theorem is the automata-world form of "2 and 3 do not share digit structure."
We already proved one panel of this seam ourselves: the leading base-3 digit of 2ⁿ is
Sturmian, hence non-automatic (`Sturmian.lean`, Cobham applied).

**The bet**: a **Cobham theorem for iterated transducers** - no finite machine can track
both the ×3 and ÷2 structure of an orbit unless the orbit is eventually trivial.  A
divergent orbit must sustain near-critical odd-step density (shortcut threshold
`log 2 / log 3 ≈ 0.6309`) often enough to defeat every tail-descent argument - a highly
structured infinite word.  The exact quantifiers are subtler than "above the threshold
forever" because an escaping orbit may still make temporary descents; see
`FRONT-A-ROUTES.md`.  Transducer rigidity is the right kind of hammer for "structured
forever is impossible."

**The second wing - machine-found certificates**: Yolcu-Aaronson-Heule recast Collatz as
string-rewriting termination and SAT-searched matrix interpretations.  They failed at
small certificate sizes, but the ceiling is compute and certificate-class richness, not
insight: weighted automata, SOS-over-parity-features, neural-guided search - all
kernel-checkable in Lean afterward.  For the two-front architecture the clean target is a
**repeat-or-descend** certificate: a repeat is handed to Front B rather than treated as
certificate failure.  This is the one approach where the fleet is a
genuine force multiplier rather than a spectator.  It passes the 3x−1 test by nature:
a certificate is an instance-specific object; the certificate *is* the +1-specific input.

## Approach 3 - Analytic-algebraic: transfer operators + effective transcendence 🧮

**~20% conditional.**

**Core move**: revive two dormant literatures with modern tools.

**Cycles**: a nontrivial cycle forces |k·log 3 − n·log 2| to be absurdly small - a Baker
linear form.  Baker plus the continued fraction of log₂3 already kills cycles with few
circuits (Steiner 1977 for 1-cycles; Simons-de Weger 2005 out to 68 circuits; extended
since - verify the exact frontier before citing it).  But transcendence is the **closer,
not the opener**.  Baker, effective irrationality measures, S-unit lower bounds, and abc
all bound `D = 2^k - 3^x` from below.  `Assumed/ABC.lean` makes this direction explicit:
abc gives `2^k ≤ C · D²`.  Such bounds exclude short cycles but cannot finish the front.

The missing opener is an integrality/word theorem that compresses an integral cycle to
boundedly many circuits, bounds `D` from above, or supplies another exact finite
classification.  Then Baker/subspace machinery and finite checking close.  The live and
killed versions of this program are separated in `FRONT-B-ROUTES.md` and
`FrontB/Threads.lean`; the earlier claim that abc or an effective S-unit input alone
finishes cycles was wrong.

**Divergence**: Berg-Meinardus proved Collatz equivalent to a uniqueness statement for
solutions of an explicit functional equation for holomorphic functions on the unit disk,
and Wirsching built the corresponding transfer operator.  Nobody has seriously attacked
that operator with modern thermodynamic formalism, nuclear-operator determinants, or -
the creative part - **rigorous computer-assisted spectral bounds**, Feigenbaum-style
interval arithmetic, certified in Lean.  A spectral gap on the right Banach space is a
checkable, finite object.  This route has the best "old math re-armed with new compute"
profile, and the +1 sits explicitly in the functional-equation coefficients (3x−1 test
passed).

## Overlooked combinations 💡

### A. The 2⊥3 master rigidity trinity

Baker (archimedean/quantitative form), Furstenberg ×2×3 (ergodic form), and Cobham
(automata form) are **three shadows of one fact** - the multiplicative independence of
2 and 3.  Nobody has built the transfer principles between the three forms and then
attacked Collatz from whichever is strongest.  A "grand 2-3 rigidity" statement with all
three as corollaries would likely take Collatz with it.  Long-term, this is the
unification to bet on - and each pairwise transfer principle is a publishable theorem on
its own.

### B. Marry Tao 2019 to Tao 2020 (forward × backward)

The forward result (a.e. orbit dips - Tao 2019, formalized by us) and the backward
result (Syracuse equidistribution ⟹ density of Collatz **preimages** - Tao 2020) have
never been combined.  Krasikov-Lagarias's backward-tree count (≫ x^0.84) sits in the same
unused corner.  The missing piece is a **saturation theorem**: backward-tree density plus
invariance forcing totality.  That missing piece is itself a rigidity claim, so this
folds into Approach 1 - but with concrete, already-proven inputs on both sides, which is
exactly what a rigidity program wants as its first consumers.

**Strengthened 2026-08-22:** raw backward density is not enough.  If all those preimages
enter one fixed divergent seed `d`, then their orbit minima are at most `d`, so they are
eventually Tao-good for every `f(n) → ∞`.  Saturation must be **floor-preserving**: amplify
moving tails whose forward floors tend to infinity and control every intermediate value
on each backward branch.  The exact contradiction target and its Lean consumption theorem
now live in `FRONT-A-ROUTES.md` and `FrontA/Threads.lean`.

### C. The carry thesis, with a control experiment 🧬

The polynomial Collatz analogue over 𝔽₂[x] is **solved** (Hicks-Mullen-Yucas-Zavislak,
Amer. Math. Monthly 2008).  The ingredient that dies in function fields is the **carry**:
degree is an ultrametric height, addition never propagates.  Our own carry work landed in
the same place from the other side - carries are the magnitude↔digit coupling object
(`Carry.lean`: digit-2 ⟺ carry state; `CarryProcess.lean`: Kummer conservation, the
closed telescoped identity, the odometer avalanche `1^k 0 ↦ 0^k 1`), and the Erdős seam
map (collatz-cryptid `notes/27`) concluded that a crossing bridge would *be* Furstenberg
rigidity at digit altitude.

**The program nobody is running**: axiomatize exactly what the archimedean carry process
adds, prove function-field Collatz inside that framework as the calibration case, then
identify the minimal carry-rigidity statement the integer case needs.  We hold
Lean-verified carry infrastructure that, as far as we know, no one else has.

### D. The Goodstein hedge 🪜

Maybe 90 years of failure is telling us something.  Collatz is Π⁰₂ - the same logical
shape as Goodstein, and we proved PA ⊬ Goodstein (goodstein-independence).  The program:
hunt for a natural well-ordering hiding in the parity-vector tree whose termination ⟺
convergence, à la hydra ↔ ε₀.  If Collatz encodes a proof-theoretic ordinal, that both
*explains* the failure and *is* the proof strategy: prove it by transfinite induction in
a stronger system, then prove PA-independence as a bonus theorem.  Falsifiable,
publishable in pieces, and home turf.  (Adjacent: the BB bridge - Antihydra and the
collatz-cryptid holdouts show Collatz-like problems are precisely the frontier of
small-machine hardness.  A nonstandard-model/compactness reformulation of "no divergent
orbit" is a cheap side-door worth one exploratory session.)

## Honest odds 📊

- Any of these resolving Collatz within 20 years: **~10%** (consistent with the ~5-10%
  prior recorded in collatz-cryptid).
- Conditional on a solution existing in that window: rigidity family ~40%, symbolic/
  certificate ~25%, analytic-algebraic ~20%, something else ~15%.
- The waypoints are real mathematics regardless: partial rigidity theorems, a
  transducer-Cobham theorem, a certified spectral gap, Baker's theorem in mathlib (a
  mega-contribution useful far beyond Collatz).

## The formalization program - first moves 🛠️

The collatz-cryptid looking-glass method, scaled up: **state the right Props in Lean to
see the territory.**  A `CollatzProgram/` vocabulary layer:

1. **Rigidity vocabulary** (the keystone lane): invariant measures on ℤ₂ under the
   Syracuse map; the ×2,×3-semigroup action; the Rudolph-Johnson statement (none of this
   is in mathlib); the pinned intertwining conjecture.
2. **Wiring theorems, provable now**: `rigidity + no-cycles ⟹ Collatz`, the two-proof
   decomposition made formal.  Each pinned statement is a checkable claim about what
   would suffice.
3. **Conjugacy layer**: Bernstein-Lagarias `Q`, the parity-vector shift, the transducer
   presentation of ×3.
4. **Spectral layer**: Wirsching's operator as a Lean object; the spectral-gap statement
   as the pinned target for computer-assisted bounds.
5. **Carry layer**: port/extend the collatz-cryptid carry results; state the
   function-field calibration theorem and the minimal carry-rigidity conjecture.

**Recommended opening lane**: ×2×3 rigidity - the intertwining theorem is the one piece
that is both genuinely new and plausibly within reach as a statement-plus-partial-proof,
and it is the keystone every combination above leans on.

## References 📚

Verify exact frontiers before citing externally; entries here are orientation, not a
bibliography of record.

- T. Tao, *Almost all orbits of the Collatz map attain almost bounded values*, 2019,
  arXiv:1909.03562.  (Formalized: gotrevor/tao-collatz.)
- T. Tao, *Equidistribution of Syracuse random variables and density of Collatz
  preimages*, 2020 (blog/companion).
- D. Rudolph, *×2 and ×3 invariant measures and entropy*, Ergodic Theory Dynam.
  Systems, 1990; A. Johnson's ×p,×q extension, 1992.
- D. Bernstein, J. Lagarias, *The 3x+1 conjugacy map*, Canad. J. Math., 1996 (also
  Bernstein's 1994 non-iterative 2-adic statement).
- E. Yolcu, S. Aaronson, M. Heule, *An automated approach to the Collatz conjecture*,
  CADE-28, 2021.
- L. Berg, G. Meinardus, *Functional equations connected with the Collatz problem*,
  Results Math., 1994 (+ 1995 follow-up).
- G. Wirsching, *The Dynamical System Generated by the 3n+1 Function*, Springer LNM
  1681, 1998.
- R. Steiner, *A theorem on the Syracuse problem*, 1977; J. Simons, B. de Weger,
  *Theoretical and computational bounds for m-cycles of the 3n+1 problem*, Acta Arith.,
  2005 (frontier extended since - check before citing).
- I. Krasikov, J. Lagarias, *Bounds for the 3x+1 problem using difference inequalities*,
  Acta Arith., 2003.
- K. Hicks, G. Mullen, J. Yucas, R. Zavislak, *A polynomial analogue of the 3N+1
  problem*, Amer. Math. Monthly, 2008.
- J. Conway, *Unpredictable iterations*, 1972 (local copy + summary in
  collatz-cryptid `papers/`).
- S. Kurtz, J. Simon, *The undecidability of the generalized Collatz problem*, TAMC,
  2007.
- J. Lagarias, *The 3x+1 problem and its generalizations*, Amer. Math. Monthly, 1985.
- C. Terras, 1976 / C. Everett, 1977 - density-one finite stopping time.
