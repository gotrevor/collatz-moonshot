# Handoff: odd-start cycle-exclusion edge PROVED

Date: 2026-09-13. Branch: `main`. Starting HEAD: `e6cb096`. Bounded objective
of the CURRENT DIRECTIVE executed in full; no push, no subagents, no Aristotle.

## What landed (`CollatzMoonshot/Assumed/Paradoxical.lean`, new final section)

All `#print axioms` = `[propext, Classical.choice, Quot.sound]` (checked via
`import CollatzMoonshot` + `#print axioms` after the build). No sorry, no CST or
cycle axiom, no new native certificate.

1. `infinite_acyclicParadoxical_of_odd_tstep_cycle`:
   `2 < n → n % 2 = 1 → 0 < L → tstep^[L] n = n → {m | AcyclicParadoxical n m}.Infinite`.
   Witness map `j ↦ L*(J+j)+1` with `J = 3*3^a`, `a = ones (traceWord n L)`.
   Obligations discharged: endpoint `tstep n > n` (`tstep_odd_gt`); count
   `(J+j)*a + 1` (`traceWord_add` at the fixed point, last letter `true`);
   subcriticality `3*A^(J+j) < 2*B^(J+j)` from `const_mul_pow_lt_pow hA1 hAB 3`
   times `A^j ≤ B^j`; injectivity from `L > 0`. Nothing in the proposed map failed.
2. `FiniteOddAcyclicParadoxical : Prop := {p | p.1 % 2 = 1 ∧ AcyclicParadoxical p.1 p.2}.Finite`
   and `finite_odd_acyclicParadoxical_imp_noNontrivialCycle : FiniteOddAcyclicParadoxical → NoNontrivialCycle`.
   Helpers: `tstep_iterate_pos`, `tstep_iterate_all_even` (`tstep^[i] n * 2^i = n` when
   the first `i` members are even), `exists_odd_of_tstep_cycle`, `tstep_iterate_one`.
   Related-member case: the dictionary's `n'` (with `n = n'` or `n = 3n'+1`) is
   replaced by an odd member `m = tstep^[i] n'` of the same period; if `m = 1`,
   `n' = tstep^[p-i] 1 ∈ {1,2}` and `step_member_trivial` yields `n ∈ {1,2,4}`
   (trivial 1↔2 shortcut cycle excluded explicitly); else `m > 2` and (1) makes O
   infinite. The cycle minimum is never used.
3. `finite_acyclicParadoxical_imp_conjecture : FiniteAcyclicParadoxical → Conjecture`
   via `finiteOdd_of_finiteAcyclicParadoxical` (O ⊆ U), the existing
   `finite_acyclicParadoxical_imp_noDivergent`, and `conjecture_iff_split`.

Module docstring caveat rewritten: U.Finite is at least as strong as full Collatz
(now machine-checked), related to but not identified with Rozier–Terracol
Conjecture 6.1's numerical 4614 cutoff.

## Verification run

- `lake build`: Build completed successfully (8771 jobs); only pre-existing
  deprecation warnings.
- `bash scripts/check-fixed-block-bound.sh`: FORMALIZE-TIER GREEN; the six
  existing axiom audits unchanged.
- `#print axioms` on the three new theorems: trust triple only.

## What remains open (unchanged)

O.Finite, U.Finite, O.Finite→U.Finite, both unconditional fronts, ParityRigidityW1'.
The next bounded objective must be set by an altitude review; deferred ranking
in DIRECTION.md stands (finite-to-one even-start bridge second).
