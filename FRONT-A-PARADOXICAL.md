# Front A: paradoxical finite trajectories

## Status and purpose

**LIVE PROJECT (2026-08-24).** This is the experiment-first continuation of the completed
parity-reconstruction pull. It studies the exact place where multiplicative drift loses
information: a finite shortcut-Collatz segment can have coefficient below `1` and still
finish at or above its start because the additive remainder is large enough.

These objects are attractive because they are finite and exactly enumerable, and because
published work connects an infinite-stopping-time orbit to infinitely many of them. They are
not known to be easy: global finiteness of paradoxical segments is stronger than Collatz.
The aim here is to discover internal structure, not rename the open problem.

## Primary sources and what may be cited

1. Olivier Rozier and Claude Terracol, *Paradoxical behavior in Collatz sequences*,
   Discrete Mathematics 349 (2026), 115167; arXiv v5:
   <https://arxiv.org/html/2502.00948v5>.
   Relevant results are Theorem 2.4 (remainder extremals), Theorem 3.2 and Corollary 3.3
   (infinite stopping time produces infinitely many paradoxical sequences; finite totality
   implies Collatz), Theorem 4.2 / Corollary 4.3 (harmonic-mean constraint), and Appendix A
   (the one-odd-block exclusion). Their Conjecture 6.1, no paradoxical start above `4614`,
   is explicitly stronger than Collatz and must remain labeled conjectural.
2. Tong Niu, *Parity vectors and paradoxical sequences in the accelerated Collatz map*,
   arXiv:2605.13886 (2026): <https://arxiv.org/abs/2605.13886>.
   It gives sharp finite parity-vector counts, an analytic fixed-length paradoxical count,
   and bounded-length density zero. Its continued-fraction classification of the observed
   paradoxical ratios is a numerical observation/conjecture, not a theorem.

Local source notes are in `papers/rozier-terracol-2026-paradoxical-summary.md` and
`papers/niu-2026-parity-vectors-summary.md`. Read the primary paper before relying on a
formula. Per repo policy, a published theorem may be represented by a narrowly stated,
provenance-documented axiom rather than re-formalized; the repo's target may not be assumed.

## Exact object in repository notation

Use `FrontB.tstep`, `traceWord`, `ones`, `numer`, and
`FrontB.tstep_iterate_identity`. For a start `n` and positive length `m`, set

```text
v = traceWord n m,
a = ones(v),
y = tstep^[m] n,
p = 3^a,
d = 2^m - p.
```

The identity already proved in the repository is

```text
2^m y = p n + numer(v).
```

Define a **paradoxical** segment by

```text
2 < n,   0 < m,   p < 2^m,   n ≤ y.
```

It is **acyclic paradoxical** when `n < y`; equality is the cyclic case. Since `p < 2^m`,
the endpoint condition is equivalent, using exact natural-number arithmetic, to

```text
d n ≤ numer(v).                                      (P)
```

The exact slack is even better:

```text
numer(v) - d n = 2^m (y - n).                        (S)
```

For a fixed word, realizing starts lie in its unique residue class modulo `2^m`, while (P)
bounds them by `floor(numer(v)/d)`. Thus every fixed word has a finite, explicitly enumerable
set of paradoxical starts. This word criterion is the computational kernel; use integers,
not floating point comparisons of logarithms.

## Strength audit: the precise Front-A connection

Rozier--Terracol Theorem 3.2 starts with an integer `n ≥ 2` of infinite shortcut stopping
time (`tstep^[j] n ≥ n` for every `j`) and constructs infinitely many paradoxical segments
starting at integers `2^k n`. The proof uses infinitely many left approximations
`3^a/2^b < 1` arbitrarily close to `1`.

For this repository's Front A, the intended derived wiring is:

```text
FiniteAcyclicParadoxical  →  NoDivergentOrbit.
```

A divergent standard-step orbit is nonrepeating, has a least orbit value/tail with infinite
stopping time, and the constructed segments cannot close cyclically; the standard/shortcut
iterate bridge then yields infinitely many **acyclic** paradoxical pairs. This last sentence
is a derived Front-A specialization of the paper and must be proved carefully in Lean or
stated as an explicitly sourced intermediate—not smuggled into a definition.

Mandatory caveats:

- `FiniteAcyclicParadoxical` is a sufficient condition for Front A, not known equivalent to
  it. Even if every orbit converges, infinitely many different finite paradoxical segments
  may in principle exist.
- The source's finiteness conjecture is stronger than the full Collatz conjecture. Calling
  the wiring a reduction to an easier problem would be misleading.
- Proving the published implication, reproducing a table, or verifying a larger finite range
  is BASELINE. The new mathematics must constrain an infinite family or falsify a published
  conjectural pattern.

## Mandated project

### A. Source lock and exact reproduction (cap: one lap)

Create `experiments/paradoxical.py` using exact integers.

- Implement the direct orbit definition and the equivalent word criterion (P); cross-check
  them exhaustively at small depths and on every reported example used.
- Reproduce the basic example `7 → 8` after 8 shortcut steps, and enough published
  fixed-length counts/pairs to catch convention errors (length, inclusion of the last term,
  trivial-cycle exclusions, and cyclic versus acyclic).
- Implement the realizing residue and the exact per-word candidate interval. Cross-check the
  analytic fixed-length count from Niu rather than inventing a second convention.
- Record exact inputs, command lines, bounds, and checksums/counts. A reproduction mismatch is
  valuable only after deciding whether it is a bug, a convention mismatch, or a source error.

Stop polishing the census once the source lock is established.

### B. Discovery search (the bulk of the project)

Search on words and exact candidates, not only by iterating starts. Preserve the smallest
counterexample to every tested claim.

1. Build a branch-and-bound enumerator. For a partial word and a remaining length/ones
   budget, derive exact upper and lower bounds on `numer` using the Rozier--Terracol
   majorization extremals. Prune a branch only with a proved integer inequality showing (P)
   is impossible for every completion.
2. Measure structure that can become a theorem: number of odd blocks/local maxima,
   prefix-one sums (dominance profile), deficit `d`, slack (S), endpoint gap, realizing
   residue, minimum orbit term, and harmonic sum/mean of the odd terms.
3. Attack at least one infinite family beyond the source's one-odd-block result. Preferred
   targets are a complete two-odd-block classification, or a parameterized exclusion under
   an explicit dominance/gap hypothesis. First falsify the candidate exhaustively.
4. Independently test Niu's continued-fraction pattern with exact rational arithmetic:
   reduce `a/m`, classify it against left convergents, semiconvergents, and the stated
   adjacent mediants of `log_3 2`, and push beyond the paper's reported search in whichever
   axis the exact enumerator genuinely extends. A verified smallest counterexample is a
   worthwhile novel result; finite confirmation is only evidence.
5. Seek a reusable pruning theorem rather than raw speed. A good output has the form “every
   completion of prefixes in class `C` fails (P)” or “any paradoxical word with property `X`
   must have approximation error / harmonic budget in interval `I`,” with all quantifiers and
   constants explicit.

Do not choose a conjecture because the initial data makes it look clean. Use held-out depths,
adversarial boundary cases, and a second implementation for any putatively new statement.

### C. Lean kernel and literature wiring

Add `CollatzMoonshot/FrontA/Paradoxical.lean` only after the conventions are locked.

- Define `Paradoxical n m` and `AcyclicParadoxical n m` transparently in the notation above.
- Prove the equivalence with (P), the exact slack identity (S), and the finite candidate bound
  for a fixed word/start residue.
- Represent Rozier--Terracol Theorem 3.2 by a narrow theorem-grade axiom in
  `CollatzMoonshot/Assumed/Paradoxical.lean` if formalizing its continued-fraction proof is
  not nearly free. State the paper's actual hypothesis and conclusion; do not package
  `NoDivergentOrbit` into the axiom.
- Prove the standard-step/shortcut/minimum bridge and the Front-A consumption theorem
  `finite_acyclicParadoxical_imp_noDivergent`. Keep its `#print axioms` ledger explicit.
- Formalize a discovery result only if it is depth-independent or closes a parameterized
  infinite class. `native_decide` is allowed for finite certificate tables. Do not spend the
  project formalizing published routine counts.
- Import the module from `CollatzMoonshot.lean`, run the targeted and full builds, and print
  axioms for every headline added.

### D. Required end-of-project classification

- **GO:** a new infinite-family theorem, a rigorous new pruning/certificate mechanism, or a
  verified counterexample to the continued-fraction conjectural pattern. State exactly what
  is new relative to both sources and pin the next theorem.
- **PROMISING EVIDENCE:** a stable, independently checked pattern survived materially beyond
  the source data but lacks an infinite proof. Preserve code/data and write the smallest
  precise conjecture; do not claim a Collatz advance.
- **BASELINE:** source reproduction + known wiring + routine Lean only. Land it cleanly and
  stop; do not manufacture more vocabulary.
- **KILL/REDIRECT:** the chosen structural pattern fails. Preserve the minimal exact
  counterexample and say what, specifically, it rules out.

At the end, update `DIRECTION.md`, `STATUS.md`, `PENDING_WORK.md`, and a new handoff. Commit
coherent green checkpoints. Never claim global finiteness, Front A, W1′, or Collatz from a
finite search.

---

## RESULTS — end-of-project classification (2026-08-24)

**Classification: PROMISING EVIDENCE.**

### Delivered (all builds green, ledgers audited)

**A. Source lock** (`experiments/paradoxical.py`, exact integers). Cross-checked exhaustively:
the iterate identity `2^m y = 3^a n + numer`, the two `numer` definitions, criterion **(P)**
`d·n ≤ numer ⇔ n ≤ y`, slack **(S)** `numer − d·n = 2^m(y−n)`, and the `7→8` example (8
shortcut steps). Paradoxical-start census `n ≤ 200000`: ratios `5/8, 17/27, 29/46`, all left
convergents/semiconvergents of `log₃2` — consistent with Niu, **no counterexample in range**
(finite confirmation, not a falsification).

**B. Discovery — the ≥ 3 odd-blocks restriction.** Every acyclic paradoxical word has at least
three odd blocks. Verified two independent ways: (i) word/residue enumerator — all `≤2`-block
front-normalized words to length 30, two-block words to length 38, **zero** admit a paradoxical
start; (ii) an independent orbit-based verifier (no `numer`, no residue reconstruction) over
*all* window lengths — min odd-block count = 3 for starts `≤ 100000`. This strictly generalizes
Rozier–Terracol Appendix A (single odd block only).

**C. Lean kernel + wiring** (`FrontA/Paradoxical.lean`, `Assumed/Paradoxical.lean`).
Sorry-free: `Paradoxical`/`AcyclicParadoxical`, `slack_identity`, `paradoxical_criterion`,
`acyclicParadoxical_criterion`, `numer_singleBlock`/`numer_twoBlock`, and **RT Appendix A**
(`headBlock_not_acyclicParadoxical`). The Front-A consumption
`finite_acyclicParadoxical_imp_noDivergent : FiniteAcyclicParadoxical → NoDivergentOrbit` is
machine-checked with ledger `[propext, Classical.choice, Quot.sound, rozier_terracol_3_2]` —
the entire divergence→infinite-acyclic bridge (running minimum, shortcut embedding, acyclicity
via the standard↔shortcut peak invariant) is discharged sorry-free. The RT axiom is the
faithful constructive form (unbounded `2^k n` starts).

### What is new vs. the two sources

- Rozier–Terracol prove only the single-odd-block exclusion (Appendix A). The **≥ 3 odd-blocks**
  restriction (in particular the *two*-block exclusion) is new, exhaustively verified well
  beyond the sources, and now backed by the proved `numer` closed forms and the 2-adic
  foundational lemma `headBlock_dvd_succ` (`[T]^b` head ⇒ `2^b ∣ n+1`).
- Niu's continued-fraction pattern is **not** falsified: every observed ratio in range is in the
  CF family. This is corroboration, not a new theorem.

### Why not GO, and the precise open conjecture

The general ≥ 3-blocks theorem is **not** proved. The interior two-block exclusion
(`le_two_blocks_not_acyclicParadoxical`, the sole disclosed `src/` sorry) reduces, via criterion
(P) and `numer_twoBlock`, to a lower bound on the realizing start `n`. The 2-adic half is proved
(`headBlock_dvd_succ`); the obstruction is the **joint 2-adic/3-adic residue constraint**
`3^b ∣ 2^c X + 1` on the interior odd value `X = x_{b+c} ≥ 2^d − 1` — simple 2-adic propagated
bounds are provably insufficient (tested: 318–1457 `(b,c,d,e)` violations). This is a genuine
deep sub-problem to be narrowed lap by lap, not cleared in one.

**Smallest precise conjecture (held out for the next attack):** for every front-normalized
two-block word `[T]^b[F]^c[T]^d[F]^e` with `3^{b+d} < 2^{b+c+d+e}`, the least realizing start
`n` satisfies `(2^{b+c+d+e} − 3^{b+d})·n ≥ 3^d(3^b−2^b) + 2^{b+c}(3^d−2^d)`, equivalently
`tstep^{[b+c+d+e]} n ≤ n`.

### Crux status addendum (2026-08-25, effective-separation lap)

The two-block crux `le_two_blocks_not_acyclicParadoxical` is machine-checked modulo the single deep
input `sep_two_three` (`3^(3k) ≤ (2^m−3^k)^3·2^k`, i.e. `|2^m−3^k| ≥ 3^k·2^(−k/3)` near-critical).
This lap built, in `FrontA/PowSeparation.lean`, a **complete sorry-free elementary reduction of the
general-`k` crux to the effective separation at continued-fraction convergent denominators of
`log₂3`** (capstone `sep_of_bracket`; engine `denom_ge_of_between`, `theta_dist_lower`,
`linForm_dist_lower`; wiring `sep_of_logb_gap`, `linear_form_eq_logb`; `irrational_logb_two_three`
and the `2^a⋛3^b ⇄ a/b⋛log₂3` bridge).  Everything is axiom-free beyond the trust base; only
`sep_two_three` is the disclosed `sorry`.

**Independently corroborated (an Aristotle attempt and the local analysis):** the residual
core is irreducibly **Baker / effective linear forms in two logarithms** — the following alternative
routes are *refuted*, not merely unattempted:
- **Continued fractions alone**: at `k = qₙ` the target is *equivalent* to an upper bound on the
  next partial quotient `qₙ₊₁ ≲ 2^(qₙ/3)`; each finite convergent check is itself an instance of the
  target, giving no purchase on later partial quotients.
- **Elementary `|2^p−3^q| ≥ 1`**: yields only the base-3 bound `‖qₙθ‖ ≥ c·3^(−qₙ)`; the needed
  base-`2^{1/3}` improvement is exactly the Baker gap.
- **Padé / hypergeometric for `√(1−z)`**: caps at `2^m−3^k ≳ 2^(m/2)` (exponent `< 1/2` uniformly),
  short of the required `2^(0.790·m)`.
- **Combining one-dimensional irrationality measures of `log 2`, `log 3`**: the determinant argument
  closes only when `(μ₁−1)(μ₂−1) < 1`, impossible since each `μ ≥ 2`; genuinely *simultaneous*
  approximation (Baker) is unavoidable.

`sep_two_three` verified exactly for every near-critical `k < 500` (both here and independently).
The classification is unchanged (**PROMISING EVIDENCE**): the crux remains open behind a precisely
pinned, independently-corroborated Baker input; a cited effective-linear-forms axiom stays BASELINE.

### Caveats honored

No claim of global finiteness, Front A, W1′, or Collatz from any finite search. The consumption
wiring is a conditional reduction whose hypothesis (`FiniteAcyclicParadoxical`, i.e. RT
Conjecture 6.1) is *stronger* than Collatz — BASELINE plumbing, explicitly labeled, not an
easier route.
