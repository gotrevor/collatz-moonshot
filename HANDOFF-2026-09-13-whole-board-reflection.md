# Handoff: whole-board reflection complete — awaiting a new idea

Date: 2026-09-13. Branch: `main`. Starting HEAD: `6a33554`.
Scope: operator-requested architecture review, documentation, verification and
commit only. No proof work, new experiments, subagents, Aristotle jobs or push.

## Decision and concrete advance

**No current bounded objective on either front clears the probability times
magnitude of NEW mathematics bar.** `DIRECTION.md` is rewritten to say so,
state the full-admission obstruction precisely, and require concrete new
mathematical evidence before reopening. The ranking is not a proof queue.

Reconciled all 17 commits in `5a54acc..6a33554`, rather than treating host
censuses and altitude reviews as additional proof advances. Baseline `5a54acc`
is the September 8 rung-3 closure. A2, arbitrary-block composition and fixed-b
Campaign B, both obstruction families, and the cycle-exclusion edge are all
complete. Campaign B's fixed-run theorem is about Front A's strict segments;
it is not the cycle front. Its mechanism extends the Simons–de Weger pincer,
with no uniform-in-b consequence.

Read the durable treadmill AGENTS.md and reflection.md first. No repository
AGENTS.md or CLAUDE.md/CLAUDE.local.md was found in the focus tree/ancestor
instruction search. Searched the read-only Lean reference corpus and read its
Collatz iterate-identity note. The explicit operator prohibition on proof work
takes precedence over reflection.md's generic implementation instruction.

Source reconciliation covered STATUS/PENDING history, recent handoffs,
FRONT-A-ROUTES, FRONT-B-ROUTES, APPROACHES, the actual FrontA/FrontB thread
predicates, the root imports, cycle/power APIs, paradoxical definitions and
closers, fixed-run implementation, invariant-measure definitions, harmonic
obstruction signature, and named axiom sites including retired wip routes.
Reopened the primary RT v5, Simons–de Weger v1.44 and Tao sources linked in
DIRECTION, checking the relevant statements rather than relying on old odds.

The architectural findings:

- U.Finite implies full Collatz, with O.Finite already excluding nontrivial
  cycles. Both inputs and the O.Finite→U.Finite edge remain open. Strict
  unequal endpoints do not prevent repeated interior cycle traversals.
- Full admission is `D*c_m<N`, where c_m is the least integer above 2 in the
  full realizing residue class. Every uniform route must consume that actual
  trajectory information. The certified P_6 survival and finite full-rejection
  probes are distinguished from the operator's broader obstruction context;
  no arbitrary-L kernel theorem is invented. All fixed-prefix follow-ups stay retired.
- RT's harmonic condition is relevant but known; no stronger trajectory
  estimate is specified. CST and 4614 are destination conjectures, not inputs.
  The even-start bridge has no finite-to-one map. W1'/Furstenberg lacks the
  arithmetic intertwining. Tao amplification lacks harmonic mass and packing
  at moving floors. Primitive compression lacks a preserving reduction.
- **Additional source mismatch found:** `FrontB.CountingGivesFinite` counts
  all nontrivial integral words. For any member v, `wpow v (j+1)` supplies
  distinct members, since its length is `(j+1)*v.length>0` and the existing
  power lemmas preserve integrality and nontriviality. Thus the written
  predicate is equivalent to FrontB, and `FinitenessIsNotEmptiness` is
  impossible as typed. Its weaker intended population would be primitive
  cycles. This is a mathematical audit deduction, not a new Lean theorem.
- `LadderCompletes` also has full FrontB strength: instantiate its bound with
  the primitive word's own circuit count, then use primitive roots. An
  unspecified compression/denominator bound plus fixed-C finiteness does not
  automatically eliminate the finite survivors. Known exclusions must actually
  cover them. DIRECTION overrides the older route-map overclaims.

None of these graph/accounting repairs is advertised as literature-new
arithmetic, and formalizing them is not assigned as a substitute next lap.

## Files changed

- `DIRECTION.md`: full replacement, with commit reconciliation, exact semantic
  graph, evidence boundaries, ranked whole board, statement audit, trust and
  reopening conditions. Historical directives remain in git/dated handoffs.
- `STATUS.md`, `PENDING_WORK.md`: current state is awaiting a new idea, with
  this handoff as baton; older assignments explicitly historical.
- `FRONT-A-ROUTES.md`, `FRONT-B-ROUTES.md`: short current pointers preventing
  the old priority lists from restarting retired work; Front B pointer also
  flags the counting population mismatch.
- This handoff. No Lean source, build configuration, gate, theorem statement,
  certificate table, or experiment implementation changed.

## Exact verification actually run

1. `bash scripts/check-fixed-block-bound.sh` — real full `lake build`,
   **8771 jobs; FORMALIZE-TIER GREEN**. Its six-declaration audit is unchanged.
   Composition uses the standard triple; the fixed-b length headline inherits
   the existing eleven explicitly allowlisted Rhin-lite native certificates.
2. The following separate graph gate — **8771 jobs; FORMALIZE-TIER GREEN**;
   each of its six declarations reports only `propext`, `Classical.choice`,
   `Quot.sound`:

   ```sh
   ~/personal/bin/lean-green ~/src/collatz-moonshot \
     --axioms CollatzMoonshot.conjecture_iff_split \
     --axioms CollatzMoonshot.infinite_acyclicParadoxical_of_odd_tstep_cycle \
     --axioms CollatzMoonshot.finite_odd_acyclicParadoxical_imp_noNontrivialCycle \
     --axioms CollatzMoonshot.finite_acyclicParadoxical_imp_conjecture \
     --axioms CollatzMoonshot.finite_acyclicParadoxical_imp_noDivergent \
     --axioms CollatzMoonshot.Furstenberg.isClosed_invariant_finite_or_univ
   ```

3. Direct W1' audit — **exit 0, exact trust triple**:

   ```sh
   lake env lean --stdin <<'LEAN'
   import CollatzMoonshot
   #print axioms CollatzMoonshot.parityRigidityW1'_imp_noDivergent
   LEAN
   ```

   **Reporting diagnostic, resolved without changing any gate:** the first
   version of step 2 included this apostrophe-containing declaration as a
   seventh `--axioms` argument. Its full build succeeded and the other six
   audits passed, but lean-green returned RED / “not found / did not elaborate”
   for W1'. Inspection of `parse_axiom_blocks` in the read-only gate showed
   its declaration-name regex uses `[^']+`, so the internal apostrophe prevents
   parsing. The direct Lean output above establishes the actual result. Step 2
   was then rerun with the six parseable declarations and ended GREEN. This
   is not a proof failure or an added trust allowance.
4. `python3 experiments/short_run_obstruction.py` — PASS: existing universal
   interval/positivity/primitivity/prefix-rejection certificate and 36 exact
   finite probes through k=256.
5. `python3 experiments/prefix_admission_obstruction.py` — PASS: existing
   universal P_6 margin, interval and primitivity certificate; 99 old-family
   rotation controls and 36 finite full-admission probes. All sampled full
   margins are negative; no universal full-rejection theorem was produced.
6. `bash scripts/check-proof-debt.sh` — **0 disclosed sorries** in its
   advertised default-source scan. Source searches also checked the remaining
   named axiom sites and retired wip files; no proof debt was moved or hidden.
7. `git diff --check` — clean. Final diff is documentation only.

The existing full `scripts/AxiomAudit.lean` ledger was read, not rerun in its
entirety. No census expansion or new theorem probe was run. Verification was
not spent on publish-tier warnings.

## Current blocker, next action, and stopping semantics

The mathematics remains open; the obstacle is the absence of a specified new
mechanism controlling small canonical integer trajectories (Front A), or a
uniform primitive integral-cycle restriction (Front B). The known relaxations
and fixed-run machinery do not provide either. This is not an operator ask or
an impossible external condition.

**Next highest-value action: await a new mathematical idea, not another
execution lap from the old board.** A future proposal must name its exact
bounded statement, evidenced first attack, acceptance criterion, and costume
check. An O→U proposal specifically needs the actual finite-to-one map; another
“normalization” intention does not qualify. No prospective proof work has been
started here. The reopening criteria in DIRECTION are not an implicit assignment.

The assigned reflection objective is complete. Commit this green checkpoint
and call `box done "Whole-board reflection complete: no bounded objective clears the new-mathematics bar; awaiting a new idea"`.
Do not call `box stuck`, and do not claim either Collatz front complete.
