# Handoff: Campaign A2 complete — retain the descent remainder

Date: 2026-09-13. Branch: `main`. No push. Operator scope: A2 only; B was not started.

## Concrete advance and campaign decision

**Stopped: A2 success, not a mathematical stuck claim.** The exact trunk-only proposal
is refuted, its corrected criterion is proved, the null-model law is audited and proved
about its model, and every candidate excursion node is classified. The detailed durable
record is `EXCURSION-AUDIT-2026-09-13.md`; the next campaign is B architecture lap 1.

New default-build module `CollatzMoonshot/FrontA/Excursion.lean`:

- `trunk_slack_identity`: for `n -> t -> y` with prefix length k / odd count j and
  suffix length l / odd count b,
  `3^j 2^l (y-n) = 3^j N_climb + 2^l N_descent - (2^(k+l)-3^(j+b))t`.
- `trunk_acyclic_criterion` and `trunk_equality_criterion`: exact strict and equality
  endpoint tests. They work at any cut, including a genuine orbit minimum.
- `trunk_depth_data_insufficient`: **2305 and 2313**, both odd, have the same minimum
  103 after 14 steps with 6 odd steps, and the same 32-step climb to 2308. Both total
  words have 29 odd steps and are subcritical. Only 2305 admits. The different prefix
  numerators 7207 and 1375 cross the exact threshold. This rules out any admission
  criterion on `(t,climb,k,j,D)` alone for individual preimages.
- `trunk_climb_one_step_control`: `(n,m)=(91,46)` reaches minimum 61 at step 45,
  then 92. Its trunk excursion is 92/61, refuting the concrete unit-coefficient
  sqrt(m) and m lower bounds, without pretending to refute all asymptotic rates.

The audit proves the numerator sum by its generating-function recurrence, the maximum
by adjacent swaps, the binomial identity, and an explicit Chebyshev relative-error
bound. Together with **already-proved** `sep_two_three`, the maximum formula actually
shows clipping is absent at *every* valid subcritical pair (five small near-window
pairs handled directly). It follows that `2δR→1`; the odd-residue rounding error gives
`2δR_odd→1` too. This is mathematical proof + exact-probe evidence, not a Lean limit
theorem. Do not upgrade that evidence tier in the next lap.

The model does not predict the census: the actual realizing residue determines the
word and hence its numerator. Cross-word correlations alone would not change the
expected count; the missing input is the correct conditional residue/numerator law.
The old assertion that trunk clusters are independent is removed. The rounding
comment is corrected from strict positivity to nonnegativity at saturation.

New exact probe `experiments/paradoxical_excursion_audit.py` checks 15,300 general cuts
and all A1 table rows by scanning odd starts through 5000: 4,19,101,0,155,41 hits at
m=8,27,46,54,65,73, with every stated trunk and start extreme reproduced. Dropping
N_descent loses 61 of these 320 hits, including all 41 at m=73. This is a table audit,
**not a rerun of the complete A1 bounds X(m)**. It verifies every hit converges; the
kickoff's hitting-time range 58–95 was too narrow (m=65 reaches 112, m=73 reaches 106).

## Route boundary / current blocker

There is no remaining A2 obligation. The surviving implication is
`C_trunk >= C_end > 2δn/a`. To obtain a lower bound g(m) by this route requires
`n >= a*g(m)/(2δ)` on the admitting segments. A global bound `τ(n)<=C log n`
would give exponential trunk growth using the existing polynomial separation, but
already assumes quantitative global Collatz. Finite verification supplies no such rate.
An unbounded excursion law even for *strict* AcyclicParadoxical segments would also
exclude nontrivial cycles: repeat a period, then end above the cycle minimum. Strict
endpoint growth is not a no-repetition hypothesis. A lower excursion bound alone
does not exclude divergent orbits without a separate upper bound.

The classification table retains open rate conjectures as open, and distinguishes
length-boundedness (equivalent to finiteness in the same quantifier scope) from a new
decomposition. It does not transfer front-normalized finiteness to unrestricted
`FiniteAcyclicParadoxical` without a bridge. No claim about Collatz itself is closed.

## Verification actually run

1. `lake env lean CollatzMoonshot/FrontA/Excursion.lean` — green during iteration.
2. `~/personal/bin/lean-green ~/src/collatz-moonshot --target CollatzMoonshot.FrontA.Excursion
   --import CollatzMoonshot.FrontA.Excursion` with separate `--axioms` arguments for
   the first four declarations above — FORMALIZE-tier GREEN, 8727 jobs.
3. **Final real full gate** (after adding the fifth theorem and root import):

   ```sh
   ~/personal/bin/lean-green ~/src/collatz-moonshot \
     --axioms CollatzMoonshot.FrontA.trunk_slack_identity \
     --axioms CollatzMoonshot.FrontA.trunk_acyclic_criterion \
     --axioms CollatzMoonshot.FrontA.trunk_equality_criterion \
     --axioms CollatzMoonshot.FrontA.trunk_depth_data_insufficient \
     --axioms CollatzMoonshot.FrontA.trunk_climb_one_step_control
   ```

   **8767 jobs, FORMALIZE-TIER GREEN.** All five ledgers are exactly
   `[propext, Classical.choice, Quot.sound]`. No new axiom, native certificate or sorry.
   `scripts/AxiomAudit.lean` now also lists all five; the full script was not separately
   rerun this lap because the final gate directly audited those declarations.
4. `python3 experiments/paradoxical_excursion_audit.py` — all exact controls pass,
   including convergence of all hits, swap/max/min/sum identities, clipping/rounding
   boundary tests and asymptotic relative-error checks at m=100,200,400,800.
5. `python3 experiments/paradoxical_random_model.py --selftest` and `--table` — pass;
   table enumeration also checks all 5,311,735 words at (27,17).
6. `python3 experiments/paradoxical_block_distribution.py --selftest` and `--controls`
   — pass, including the 7→8, single-block, and balanced-word negative controls.
7. `bash scripts/check-proof-debt.sh` — 0 disclosed sorries in its advertised scope.
8. `git diff --check` — clean.

## Next highest-value attack

Follow the **Campaign B** section of `KICKOFF-2026-09-13-excursion-campaign.md`:
derive the arbitrary-block integer cascade from the head-block identities, identify
what the two-/three-block contractions consume, and test one proposed uniform
composition inequality on b=4,5 and the shared-trunk controls. Keep all dependence
on block count, lengths, odd count, D and prefix remainders visible. No implementation
tranche without a surviving new inequality; B has a two-architecture-lap stopping rule.
`DIRECTION.md` remains deliberately untouched and stale; rung 3 is complete.
