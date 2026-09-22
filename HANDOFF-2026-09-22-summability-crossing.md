# HANDOFF: summability / crossing bridge (KICKOFF-2026-09-22-summability-crossing.md)

Task-specific handoff for the operator-authorized bounded objective.  Read the
kickoff file and `RESEARCH-2026-09-22-packing-shadow.md` first.

## Done (green, sorry-free, in `src/`)

`CollatzMoonshot/FrontA/OrbitPacking.lean` (kickoff item 1, counting half):

* `traceWord_add_mul`, `traceWord_mod` — the length-`m` parity trace depends only
  on the start mod `2^m` (converse of the pre-existing `traceWord_eq_imp_modEq`).
* `tstep_iterate_block` — `tstep^[m] (s + q*2^m) = tstep^[m] s + q*3^(ones (traceWord s m))`.
* `weightSum_le` — `∑_{s<2^m} 2^(ones (traceWord s m)) ≤ 3^m`, from a one-step
  injection (`t ↦ (3t+2) mod 2^k`), not from the exact binomial count.
* `IterateSeparated`, `fiber_card_le`, `block_card_le` — an iterate-separated set
  meets `[q*2^m,(q+1)*2^m)` in `≤ (m+1)*3^(3m/5) + 3^m/2^(3m/5+1)` elements.

`CollatzMoonshot/FrontA/OrbitSummability.lean` (kickoff items 1-3):

* `not_diverges_of_tstep_repeat`, `tstep_time_injective`,
  `iterateSeparated_orbitSet` — a divergent orbit's value set is iterate-separated.
* `packNat`, `packReal`, `packNat_div_le`, `summable_packReal`, `recipBound`,
  `sum_inv_le`, `sum_inv_orbit_le` — `∑_{j<k} 1/y_j ≤ recipBound`, an absolute
  constant, along any divergent orbit.
* `traceWord_succ_append`, `ones_traceWord_append`, `two_pow_mul_iterate_le` —
  `2^k * y_k ≤ 3^(r_k) * n * exp(S_k/3)` (bounded multiplicative +1 correction).
* `iterate_le_coefficient` — `y_k ≤ (3^(r_k)/2^k) * (n * exp(recipBound/3))`.

### Design choices worth keeping

* Shells are taken in steps of five, `[2^(5t), 2^(5t+5))`, which is contained in
  the single aligned block `[0, 2^(5t+5))` with `3*(5t+5)/5 = 3t+3` exact.  No
  union of blocks, and no interval-to-block reduction (the paper's eq. (4)).
* Bad-word weight is `2`, not the paper's `3/2`: `(1+2) < 2*2^(3/5)` still holds
  and `2^ones` keeps the whole combinatorial argument inside `ℕ`.
* Only `Σ 1/y_j` bounded is needed, never the uniform tail `B(F)` of the paper's
  §3 — that was for the §4/§7 remainder discussion, which is out of scope here.

`CollatzMoonshot/FrontA/CrossingEquivalence.lean` (kickoff item 4, COMPLETE):

* `ones_traceWord_add` — odd-step counts split at any time `k`.
* `exists_floor_tstep`, `exists_tail_min`, `exists_ballot_forever` — a divergent
  orbit has arbitrarily late values `x ≥ 2` with `2^m ≤ 3^(ones (traceWord x m))`
  for every `m`.
* `noDivergentOrbit_of_crossingExists` (forward).
* `exists_tstep_repeat_of_not_diverges`, `pow_ones_lt_of_cycle`,
  `ones_traceWord_period`, `crossingExists_of_noDivergentOrbit` (reverse).
* `crossingExists_iff_noDivergentOrbit` — the headline equivalence, plus an
  `Audit` section with `#guard_msgs`-pinned `#print axioms` for
  `block_card_le`, `sum_inv_orbit_le` and the equivalence: each is exactly
  `[propext, Classical.choice, Quot.sound]`.

## ALL FOUR KICKOFF ITEMS ARE DONE.  Historical next-leaf notes follow.

## Old next leaf (kickoff item 4) — now discharged

1. `divergence_coefficient_tendsto`: from `iterate_le_coefficient` plus
   `y_k → ∞` (divergence), conclude `b_k = 3^(r_k)/2^k → ∞` along a divergent
   orbit.  Needs: `Diverges n → ∀ M, ∃ K, ∀ k ≥ K, M ≤ tstep^[k] n`?  NOTE the
   repo's `Diverges` is `∀ M, ∃ k, M ≤ step^[k] n`, i.e. unbounded, NOT
   tendsto.  So `b_k` need not tend to infinity; what IS available is
   `limsup b_k = ∞`, which is **not enough** for the tail-minimum argument as
   the paper states it.  Two options:
   (a) upgrade: on a divergent orbit `{k : y_k ≤ M}` is finite for each `M`
       (values are distinct, so only finitely many indices can land in `[1,M]`),
       hence `y_k → ∞` genuinely.  THIS WORKS and is cheap — use
       `tstep_time_injective` to injectively map `{k : y_k ≤ M}` into `[1,M]`.
   (b) avoid the limit entirely.
   Take (a).  DONE via `exists_floor_of_diverges` (already in `Rigidity/Drift`)
   lifted to `tstep` by `exists_step_count`; no new injectivity argument needed.
2. `b` attains a minimum on every tail `{k ≥ j}` (since `b_k → ∞` and `b` is
   positive), giving `k_j ≥ j` with `b_{k_j+t} ≥ b_{k_j}` for all `t`, i.e.
   `2^t ≤ 3^(ones (traceWord y_{k_j} t))` for all `t` — exactly
   `¬ ∃ m, 3^(ones (traceWord y_{k_j} m)) < 2^m` with `y_{k_j} ≥ 2`.
   Needs the trace-shift lemma `traceWord (tstep^[k] n) t` vs
   `ones (traceWord n (k+t)) - ones (traceWord n k)` — prove
   `ones (traceWord n (k+t)) = ones (traceWord n k) + ones (traceWord (tstep^[k] n) t)`
   by induction (companion of `traceWord_succ_append`).
   Conclusion: `CrossingExists → NoDivergentOrbit`.
3. Reverse: `NoDivergentOrbit → CrossingExists`.  Bounded orbit ⇒ repeat ⇒
   `tstep^[p] x = x` for some `p ≥ 1`, `x ≥ 1`.  On that cycle the exact
   identity gives `2^p * x = 3^(ones v) * x + numer v` with `numer v > 0`
   (some step is odd, else the cycle strictly decreases), so `3^(ones v) < 2^p`,
   and iterating the period drives the prefix coefficient below 1 from ANY
   start that reaches the cycle.  Must handle the preperiod: the coefficient of
   `traceWord n (a + j*p)` is `3^(r_a + j*ones v)/2^(a+j*p)` → 0.
   Do NOT assume `NoNontrivialCycle`; positive cycles stay allowed.
4. Audit file with `#print axioms` for `sum_inv_orbit_le` and the final
   equivalence.

## Verification

`lake build` green at each commit; no `sorry`, no new axioms in either module.
