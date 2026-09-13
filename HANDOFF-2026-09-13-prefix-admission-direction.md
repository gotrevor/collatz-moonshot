# Handoff: post-obstruction altitude — six-letter admission selected

Date: 2026-09-13. Branch: `main`. Starting HEAD: `882c787`; clean worktree.
This was an altitude review, **not a proof lap**. The assigned deliverable is
the rewritten CURRENT DIRECTIVE in `DIRECTION.md`, this handoff, and aligned
status/pending pointers. No Lean source, experiment, fixture, dependency,
build configuration, theorem statement or trust assumption was changed.

## Reconciliation and concrete advance

Read the durable treadmill `AGENTS.md` and `review.md`; the kickoff's explicit
direction-only scope overrides review.md's default instruction to start the
selected proof attack in this lap. No local/ancestor repository AGENTS or
CLAUDE files were present. No subagents or external messages were used.
Read the current directive, newest handoff, obstruction proof, current
STATUS/PENDING records, A2 audit and the relevant source interfaces. Searched
the read-only reference corpus and read the statement-faithfulness and
closed-form-validation notes before reviewing the claims.

The full log since `5bdea84` contains two commits:

- `972c772`: census docstring reconciliation, including 9/46 minimum observed
  run ratio and first front-normalized rung after 3 being 7 at length 27.
- `882c787`: all-k primitive rational counterfamily `(TF TTF)^k (TF TTF TTF)`.
  The shared invariant interval certifies Q=2, joint slack at least 8/5 and
  R≤243/256; 5a−3m=1 certifies primitivity. Every member fails integer admission
  because TFTTFT forces n≡57 mod64 whereas N/D≤421/13. The operator supplied
  independent host verification; this review reran the checked-in certificate.

The old directive's rational M_Q is therefore **ANSWERED/FALSE**. The new
directive records that closure and fixes the precise next arithmetic question.
This is a direction advance; it adds no mathematical theorem or new refutation.
Rung 3, A2 and fixed-b Campaign B remain closed.

Source audit preserved the graph: `AcyclicParadoxical` is strict shortcut
endpoint growth, not absence of repeated states; `FiniteAcyclicParadoxical`
quantifies all start/length pairs. The existing implication from this finite
set to `NoDivergentOrbit` is proved. The fixed-b theorem concerns odd starts
and allows a terminal odd run. Global odd-start finiteness and its edge to
unrestricted finiteness remain open. The 18@8 → 9@7 control refutes the naive
even-prefix stripping map only. Both Collatz fronts remain open.

## Chosen objective and first attack

**Choose candidate (i): Q=2, L=6 prefix-admission boundedness.** It ranks first
by medium-high probability of a certified obstruction/family times high
diagnostic magnitude. The finite-to-one edge ranks second; coarse actual
residue discrepancy ranks third; formalizing the completed family or a known
fixed-circuit transport has lower new-mathematics value. DIRECTION specifies
the deferred distribution population and threshold rather than invoking
independence of the exact numerator and residue.

The population S2 is primitive words
`T^q_0 F^e_0 ... T^q_(b−1) F^e_(b−1)`, with all q,e in {1,2}, length m≥6,
R=3^a/2^m<1, and the unique rational affine cycle satisfying z_i>2^q_i at
every run head. All even gaps, including the terminal one, are positive.
There is no bound on total run count, length or fixed-point height.

For the first six letters u, let
`r_6=[−numer(u)*(3^ones(u))^(-1)] mod64` and let c_6 be the least n>2 in
that residue class. With full-word N=numer(v), D=2^m−3^a>0, the filter is
**P_6(v): D*c_6<N**. It tests the given entry head, not every rotation.
The exact question is `∃M, ∀v∈S2, P_6(v) → |v|≤M`.
The previous family fails this filter and hence does not decide the question.

**First attack next lap:** check run-head rotations and bounded prefix/defect
changes of the known family as baseline controls; then search two short block
macros (initially at most four blocks each) preserving a common rational
interval with a six-letter residue below the full fixed-point threshold.
Reuse the existing cascade and obstruction experiment; compute every internal
joint slack, N,D,c_6,full canonical c_m and both margins separately. Seek an
all-parameter primitive repeated/defect family. No such search was started here.

## Acceptance criterion and costume check

An explicit unbounded primitive family in S2∩P_6, certified for all parameters
by exact formulas or an interval/recurrence argument, refutes the proposed
fixed-filter bound. Finite survivors alone do not. Alternatively, prove an
explicit M, or a uniform large-length inequality D*c_6≥N with finite remainder,
for **all** S2, not just the chosen macro ansatz; kernel-check a claimed green
theorem. A useful intermediate green node/edge proves a needed arithmetic
inequality. Predicate encoding, finite search failure, fixed-b reruns and
replayed positivity do not complete the question.

P_6 is necessary for full admission, which is D*c_m<N, but does not enforce
the remaining parity letters. A family surviving P_6 need not admit any
integer segment; it would refute this relaxation, not Collatz or restricted
finiteness. Conversely a bound here yields finiteness only for actual words
in the specified primitive Q=2, terminal-even population. Other run lengths,
proper powers, terminal-odd words and the even-start edge remain outside it.
No global run/length bound on admitting words is an allowed input.

If a rotation/padding of the known family settles the question, identify it
honestly: only its all-parameter prefix-margin certificate is new. Stop when
the specified question is settled; do not increase L or claim a general
finite-prefix obstruction. No literature novelty is asserted by this review.

## Exact verification this lap

1. `python3 experiments/short_run_obstruction.py` — PASS: existing rational
   interval certificate and 36 exact finite probes k=0..32,64,128,256, with
   cyclic slacks, closed forms, literal primitivity, residues and rejection.
   The all-k induction remains the mathematical proof in the checked-in note.
2. `bash scripts/check-fixed-block-bound.sh` — real full `lean-green` gate;
   **8771 jobs, final line `✅ FORMALIZE-TIER GREEN`**. Six existing declarations
   axiom-audited. Composition has the standard triple; length/nonvacuity
   results retain the eleven explicitly allowed inherited native certificates;
   boundary controls have no axioms. No new trust debt.
3. `git diff --check` — clean before commit. Reviewed the final diff to ensure
   the changed paths are only DIRECTION, STATUS, PENDING_WORK and this handoff.

No new Lean probes, construction searches, complete census, A2 regression run,
or new theorem verification is claimed in this direction-only lap. The sources
and old control witnesses were inspected; only the existing certificate was rerun.

## Blocker, next action, stop

No blocker remains for this altitude deliverable. The chosen S2∩P_6 question
is unresolved and belongs to the next lap; its first attack is above. A failed
bounded macro search would be a mathematical checkpoint, not an operator
blocker. Do not reopen the answered rational M_Q question.

Commit the green documentation checkpoint on `main`, never push, then call
`box done "Altitude directive reconciled through 882c787; selected exactly Q=2, L=6 prefix-admission boundedness with acceptance and costume checks; no proof work started"`.
Stop. No `box stuck`, operator ask or stretch proof campaign is appropriate.
