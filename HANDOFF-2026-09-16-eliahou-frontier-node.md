# Handoff — DIRECTION node 4 complete: Eliahou's method at the `2^68` frontier

Branch `main`, `lake build` green (8775 jobs), `src/` sorry-free, nothing pushed.
Assignment: `DIRECTION.md` attended override 2026-09-16 00:25 EDT, node 4.
Closed in one lap; **no leaf left open** (the `log_two_bounds_26` /
`log_three_bounds_26` fallback the directive authorised was not needed).

## What landed

`CollatzMoonshot/FrontB/EliahouFrontier.lean` (new, imported from the root; `FrontB/Eliahou.lean`
and `Assumed/Cycles.lean` are untouched apart from a docstring mention in the latter).

```
theorem odd_members_ge_of_two_pow_68 :
  ∀ n m, 1 ≤ n → 0 < m → step^[m] n = n →
    (n = 1 ∨ n = 2 ∨ n = 4) ∨
      72057431991 ≤ ((Finset.range m).filter (fun i => step^[i] n % 2 = 1)).card

theorem min_cycle_length_two_pow_68 :
  ∀ n m, 1 ≤ n → 0 < m → step^[m] n = n →
    (n = 1 ∨ n = 2 ∨ n = 4) ∨ 186265759595 ≤ m
```

Both ledgers are exactly what DIRECTION demanded:

```
[propext, Classical.choice, Quot.sound,
 CollatzMoonshot.Assumed.collatz_verified_up_to_two_pow_68]
```

**No `native_decide` axiom at all** — a strict improvement on node 3, whose three
big-integer certificates are now not used on this path.

## Route

Node 3's `FrontB.Eliahou` already exposes everything cycle-side abstractly, so the
only new work was replacing the certificates by real analysis.

1. **Certified logs.** `Real.abs_log_sub_add_sum_range_le` at `x = 1/2`, `n = 90`
   (`|S₂ − log 2| ≤ 2^{-90}`) and at `x = 1/3`, `n = 58`
   (`|S₃ − log(3/2)| ≤ (3/2)·3^{-59}`).  The finite rational sums evaluate with
   plain `norm_num [Finset.sum_range_succ]` in ~2 s each — no chunking, no
   `maxRecDepth` bump needed.  Result: `log 2` and `log (3/2)` pinned to 30 decimals
   (`log_two_bounds_26`, `log_three_halves_bounds_26`).
2. **Never form `log 3` from a separate series.**  `log 3 = log 2 + log(3/2)`
   (`log_three_eq`), so the two cleared inequalities become inequalities in
   `log 2` and `log(3/2)` only, and the two error bars never compound badly:
   * `key_lower` : `103768467013 · log 2 < 65470613321 · log 3`
     ⇔ `38297853692 · log 2 < 65470613321 · log(3/2)`, margin `4.61·10⁻¹²`;
   * `key_upper` : `6586818670 · log(3 + 2^{-68}) < 10439860591 · log 2`,
     via `3 + 2^{-68} = 3(1 + 1/(3·2^{68}))` and `log(1+t) ≤ t`
     (`Real.log_le_sub_one_of_pos`), margin `2.68·10⁻¹²`.
   Margins vs the `10⁻²⁷` truncation error scaled by `~6.5·10^10` ⇒ 15 orders of slack.
   **Gotcha:** the directive's suggested `log(1+1/(3·2^68)) ≤ 2^{-70}` is FALSE
   (`2^{-70} = 1/(4·2^{68}) < 1/(3·2^{68})`); keep the exact `1/(3·2^68)`.  It still
   clears with `2.68·10⁻¹²` to spare.
3. **Cycle → rational inequalities.** `lower_ineq` / `upper_ineq` turn
   `3^a < 2^e` and `2^e·(2^68)^a ≤ (3·2^68+1)^a` into
   `103768467013·a < e·65470613321` and `e·6586818670 < 10439860591·a`
   by taking `Real.log`, multiplying by `key_lower`/`key_upper`, and cancelling
   `log 2 > 0`.  Nothing here touches a big numeral.
4. **Farey step.** `FrontB.Eliahou.farey_denominator_bound` (unchanged) with
   `65470613321·10439860591 − 103768467013·6586818670 = 1` gives
   `a ≥ 65470613321 + 6586818670 = 72057431991`; then `e·65470613321 > 103768467013·a`
   with that `a` is enough for `omega` to conclude `e ≥ 114208327604` (all linear in
   `a, e` with literal coefficients — no manual `Nat.lt_of_mul_lt_mul_right` chain).
   `a + e = m` from `card_oddS_add_card_evenS`, giving `186265759595`.
5. `cycle_inputs` factors the `a ≥ 1` / `3^a < 2^e` / min-term extraction that node 3
   had inlined in `min_cycle_length`.

## Provenance

This is Eliahou 1993 §3's method at the repo's `2^68` frontier, **not** Hercher 2023
Cor. 29: Hercher's `1.375·10¹¹` needs a residue-class computation on top of the
continued fraction, and the pure Farey step at his `X₀ = 2075·2^60` gives the same
`72057431991`.  `Assumed.hercher_odd_members_bound` stays a citation axiom, and
`frontier_min_cycle_length` still stands on it alone.

## Next steps (unassigned)

1. `Assumed.hercher_odd_members_bound` is the only remaining cycle-front citation
   axiom.  With node 4 in hand, the missing pieces are exactly (b) an effective
   lower bound on `|e log 2 − a log 3|` (Baker / Rhin — note `FrontA` already has
   Rhin-lite machinery) and (c) Hercher's circuit counting.  Piece (a), the product
   identity and the Farey/real bridge, is now fully kernel-checked and reusable:
   `EliahouFrontier.lower_ineq`/`upper_ineq` are stated for arbitrary `a, e` and
   the log bounds are reusable to 30 decimals.
2. The standing "awaiting a new mechanism" pause (`PENDING_WORK.md`) otherwise resumes.

## Checkpoint (end of lap, 2026-09-16)

* Branch `main`; HEAD `9d3fbd6` (this checkpoint's own commit follows it).
* `lake build` green, 8775 jobs, via the pre-commit hook on `9d3fbd6`.
* `src/` sorry-free; working tree clean; nothing pushed (the host pushes).
* `box done --green` signalled and accepted — the treadmill does not relaunch.
* `DIRECTION.md`'s node 4 was the only assignment this run had, and it is complete
  with no open leaf.  The "awaiting a new mechanism" pause above it is again the
  standing position; `PENDING_WORK.md` is unchanged and still accurate.

### Exact next steps, none of them currently assigned

1. `Assumed.hercher_odd_members_bound` — the last cycle-front citation axiom.
   Kernel-ready inputs now: `Eliahou.step_prod_identity`, `three_pow_lt_two_pow`,
   `two_pow_mul_pow_le`, `two_pow_68_lt_orbit`, `farey_denominator_bound`, plus
   this lap's `EliahouFrontier.{log_two_bounds_26, log_three_halves_bounds_26,
   lower_ineq, upper_ineq}` (the last two stated for arbitrary `a, e`).  Missing:
   an effective lower bound on `|e log 2 − a log 3|` (Baker, or the repo's own
   FrontA Rhin-lite machinery) and Hercher's circuit counting.
2. Pushing the frontier bound further is now purely a matter of a wider Farey pair
   plus more Taylor terms — mechanical, no new mathematics, do it only on request.
3. The standing open problem (turning the trajectory dip `x_min < a/(3Λ)` into an
   admission constraint on `D·c_m < N`) is unchanged and untouched by this lap.
