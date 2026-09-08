# Handoff: rung 3 window node closed

**Date**: 2026-09-08 · **Branch**: `main` · nothing pushed — host pushes.

## Objective and result

The `KICKOFF-2026-09-07-rung3.md` window-node target is complete:

- `FrontA.threeBlock_window_infeasible` is proved;
- `FrontA.threeBlock_gap_of_long` and
  `FrontA.threeBlock_not_acyclicParadoxical_of_long` are proved;
- `scripts/check-proof-debt.sh` reports zero disclosed sorries.

Do not overstate the result: the proved word theorem excludes lengths outside `{5,8,16,27}`.
The separate ten-tuple realizing-residue rejection at lengths `5,16,27` remains to formalize
before claiming the literal length-8 classification.

## Concrete advance

1. Parameterized the three relaxed inequalities by a deficit scale
   `2^m ≤ 2^t (2^m-3^k)` and proved the sharp closure
   `threeBlock_scaled_k_bound : k ≤ 6t+5`.  The load-bearing comparison is
   `3^5 ≤ 2^8`; the proof treats `d < t+2` and `t+2 ≤ d` separately.
2. Derived a pure-Nat polynomial deficit bound from `rhinLite_log23_measure`, bounded its
   explicit constant by `2^52905`, and proved the polynomial bootstrap
   `threeBlock_polynomial_k_lt : k < 492276`.
3. Extended `RhinLiteSep.lean` with the next convergent bracket and
   `sep_strong_492276 : 3^k ≤ (2^m-3^k)·2^25`.  The lower comparison
   `2^780239 < 3^492276` is `decide +kernel`.  The 5-million-digit upper comparison
   `3^10781274 < 2^17087915` hit Lean's `LEAN_NAT_MAX_SIZE` kernel cap and is the sole new
   `native_decide` power certificate.
4. Applied the sharp closure at scale `t=26` to get `k ≤ 161`.  A kernel-checked finite
   certificate over only `(k,m)` improves the scale to `t=8`, so the closure gives `k ≤ 53`;
   the elementary `3^k ≤ 4^k` bound then gives `m ≤ 106`.
5. Added one shared pruned native certificate `threeBlock_residual_cert` covering both residual
   regimes (`m ≤ 27` or the near-critical window).  It indexes by `(k,m)` first, then derives
   `f = k-b-d` and `g = m-k-c-e`, avoiding the six-dimensional rectangular enumeration.
6. Added the new key theorems to `scripts/AxiomAudit.lean` and refreshed source/status prose.

## Verification actually run

- `taskset -c 0-3 lake build CollatzMoonshot.FrontA.ThreeBlock` — green after the unified
  certificate (8727 jobs; target rebuilt in 65s).
- `taskset -c 0-3 lake build` — green after the final consolidation (8766 jobs;
  `ThreeBlock` rebuilt in 61s).
- `bash scripts/check-proof-debt.sh` — `0 disclosed sorries`.
- `taskset -c 0-3 lake env lean scripts/AxiomAudit.lean` — green; inspected the ledgers for
  `sep_strong_492276`, `threeBlock_window_infeasible`, `threeBlock_gap_of_long`, and
  `threeBlock_not_acyclicParadoxical_of_long`.
- `git diff --check` — clean after the documentation refresh.

## Trust ledger

There is no `sorryAx` and no new literature axiom.  The rung-3 closer inherits the existing
Rhin-lite native certificates and adds two native artifacts:

- `pow_cert_10781274._native.native_decide.ax_1_1` (kernel numeral-cap fallback);
- `threeBlock_residual_cert._native.native_decide.ax_1_1` (bounded exhaustive census).

The small aggregate scale certificate and all other new numeric comparisons use `decide +kernel`.

## Current blocker and next attack

There is no blocker for the assigned window node.  The next highest-value rung-3 attack is the
exceptional finite tail: encode the ten host-verified tuples at `m ∈ {5,16,27}` and reject each
by its true realizing residue, then state the literal “three odd blocks implies length 8” theorem.
The tuple list and host verification route are recorded in `experiments/rung3_census.py` and the
2026-09-02 handoffs.
