# Handoff: post-prefix altitude review — cycle-exclusion edge selected

Date: 2026-09-13. Branch: `main`. Starting HEAD: `3a3e838`; clean worktree.
**Assigned review complete. No proof work started.** Read DIRECTION.md's
CURRENT DIRECTIVE first; it outranks the historical assignments below it.
Only documentation changed. No push, subagents, or Aristotle submission.

## Concrete advance and reconciliation

Read the durable treadmill AGENTS.md and review.md first. The kickoff's
direction-only scope overrides review.md's generic instruction to implement
a proof attack in the same lap. No focus-repository AGENTS.md or CLAUDE files
were present. Searched the read-only reference corpus and read its
`axiom-clean-not-statement-faithful.md` note. Read the current direction,
status/pending ledgers, named obstruction proof/handoff and preceding altitude
context; then checked the actual source definitions and cycle consumers.

`git log --oneline bc4158e..HEAD` contains only `3a3e838`. It settles the
six-letter question with `(XY)^(2j+12) X Y^17`, primitive and P_6-admitting
for every j≥0, by an exact positive-coefficient formula for N−57D.
It changes no Lean source. The previous directive is answered, not stalled.
Rational positivity and the six-letter relaxation are both refuted; the new
directive prohibits all further finite-prefix filters, without misreporting
the two examples as a proved theorem for arbitrary L.

The operator additionally reports independently host-verified full rejection
of every member, with canonical n0 of about m bits. The committed obstruction
proof explicitly only claims finite full-rejection checks at 36 parameters.
DIRECTION/STATUS/PENDING now record both evidence levels without pretending
that this review reproduced the host's universal proof. Its report is accepted
as current context; no further work on that finished question is assigned.

The decisive source finding is that `AcyclicParadoxical` forbids equal endpoints
but **allows interior repeats**. The existing cycle consistency anchor gives
only non-strict `Paradoxical` period multiples. No checked-in theorem was found
for odd-start acyclic finiteness excluding cycles or for unrestricted acyclic
finiteness implying Conjecture. That is a concrete missing graph edge, with
existing period-count, cycle-subcriticality and power-domination APIs.

## ONE chosen objective, first attack, acceptance

Let `O={p : ℕ×ℕ | p.1%2=1 ∧ FrontA.AcyclicParadoxical p.1 p.2}`.
**Next lap:** prove `O.Finite → NoNontrivialCycle` and its direct consumer
`FiniteAcyclicParadoxical → Conjecture`, using the existing divergence closer.
These remain targets, not new theorems produced by this review.

The load-bearing intermediate is:

```
∀ n L, 2<n → n%2=1 → 0<L → T^[L] n=n →
  {m : ℕ | FrontA.AcyclicParadoxical n m}.Infinite.
```

**First attack:** for this odd periodic n, set a=ones(traceWord n L), A=3^a,
B=2^L, J=3*A. Try `j↦(n,L*(J+j)+1)`. Establish its exact endpoint T(n)>n,
odd count `(J+j)*a+1`, inequality `3*A^(J+j)<2*B^(J+j)`, and injectivity.
The proposed base estimate is the existing `const_mul_pow_lt_pow` with c=3.
No primitivity or minimum-period assumption is needed. This is an injection
into O, not a finite-to-one even-start reduction.

Then use `FrontB.tstep_cycle_of_step_cycle` to extract an odd periodic member
above 2 from a nontrivial standard cycle. That theorem can return a related
member with `n=3*n'+1`, not only the original member; handle both cases and
the transfer to an odd member. Rule out entering the trivial shortcut cycle.
The full source API is in `Assumed/Paradoxical.lean` and `FrontB/Dictionary.lean`.

**Acceptance:** kernel-checked infinite strict-witness theorem, odd-start
cycle-exclusion edge and its direct unrestricted-finiteness→Collatz corollary;
all on the standard trust base. No new axiom, sorry, CST assumption, or native
certificate is needed in the proposed route. Preserve the original predicates
and existing audits, run the real full gate, update the source's strength
caveat faithfully, commit and stop. A genuine intermediate witness theorem is
progress but not completion of the consumer. A failed map must be recorded
with its exact failed obligation, not sold as refuting the finiteness implication.

## Ranking and costume check

Selected candidate (vi), revealed by reconciliation: high chance of a new
formal edge with moderate graph value. It determines whether the odd-start
root already carries Front B; the direct unrestricted corollary would make
its role as a sufficient condition for full Collatz explicit. This is elementary
cycle repetition, not a claim of new literature-level number theory.

Second: O.Finite→U.Finite, high potential but no replacement finite-to-one map
with target membership and finite fibers. The 18@8→9@7 control refutes only
the naive deletion map. Third: stronger trajectory constraints, calibrated
against the harmonic-mean theorem, CST and its verified range, and the 4614
conjecture. Fourth: coarse discrepancy, presently without a useful error scale.
DIRECTION preserves the exact W(m,a), dyadic bins and strict admission sums.
Fixed-circuit transport and further filter/census work are not selected.

Re-read the primary Rozier–Terracol v5 source, especially Definitions 1.1–1.2,
Theorem 4.2/Corollary 4.3, Corollary 5.4 and Conjecture 6.1. The concise sourced
calibration is in DIRECTION. In particular U.Finite is not literally the
numerical 4614 conjecture. No new literature proof was ported or axiom added.

The costume check is strict: finiteness counts **pairs**, not distinct starts;
equal-endpoint period multiples alone do not work; repeated interior states
are allowed. The extra odd step must be real trajectory data. No unbounded-start
claim, simple-path condition, even-prefix bound, or primitive-word restriction
may be substituted. O.Finite and U.Finite remain open hypotheses. Proving this
edge would neither prove them nor resolve O.Finite→U.Finite. It would sharpen
the graph, not supply a uniform Collatz mechanism or revive Front B compression.

## Verification actually run

1. `python3 experiments/prefix_admission_obstruction.py` — PASS: existing
   all-parameter interval and integer-margin certificates, 99 old-family
   rotation controls, existing short-macro check and 36 finite full-admission
   probes. No new search was written, no census expanded.
2. `bash scripts/check-fixed-block-bound.sh` — PASS: real full `lake build`,
   **8771 jobs**, six existing axiom audits, final **FORMALIZE-TIER GREEN**.
   Composition uses the standard trust triple; the length results retain the
   eleven explicitly disclosed native certificates. The gate was unchanged.
3. `lake env lean --stdin` with `import CollatzMoonshot` and `#print axioms`
   for `conjecture_iff_split`, `finite_acyclicParadoxical_imp_noDivergent`,
   `subcritical_of_tstep_cycle`, `ones_traceWord_mul_of_cycle`,
   `const_mul_pow_lt_pow`, `FrontB.tstep_cycle_of_step_cycle`, and
   `infinite_paradoxical_of_tstep_cycle` — exit 0. All dependencies lie within
   `[propext, Classical.choice, Quot.sound]`; period counts omit choice.
   These are existing declarations, not Lean probes of the proposed new proof.
4. `git diff --check` — clean before commit; the staged scope is DIRECTION.md,
   STATUS.md, PENDING_WORK.md and this handoff only.

No blocker remains for this review. The next attack is specified above and
belongs to the next lap. Commit the green documentation checkpoint on `main`,
call `box done` for the completed altitude objective, then stop. No `box stuck`
or operator decision is appropriate.
