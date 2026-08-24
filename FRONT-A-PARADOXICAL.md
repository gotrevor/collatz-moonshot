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
