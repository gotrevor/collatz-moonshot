# Handoff — DIRECTION node 3 complete: the Eliahou citation axiom is a theorem

Branch `main`, HEAD `073b0d2`, working tree clean, `lake build` green (8774 jobs),
`src/` sorry-free.  Assignment: `DIRECTION.md` attended override 2026-09-16 00:10 EDT,
node 3.  Nodes 1–2 of the 23:58 override were already done (`8510836`, `2a1478b`).

## What landed

`CollatzMoonshot/FrontB/Eliahou.lean` (new, imported from the root and from
`Assumed/Cycles.lean`).  `Assumed.eliahou_min_cycle_length` is now a `theorem`
with the identical statement, defined as `FrontB.Eliahou.min_cycle_length`.

```
#print axioms CollatzMoonshot.Assumed.eliahou_min_cycle_length
[propext, Classical.choice, Quot.sound,
 CollatzMoonshot.Assumed.collatz_verified_up_to_two_pow_68,
 CollatzMoonshot.FrontB.Eliahou.two_pow_lt_three_pow_big._native.native_decide.ax_1_1,
 CollatzMoonshot.FrontB.Eliahou.two_pow_lt_three_pow_cert._native.native_decide.ax_1_1,
 CollatzMoonshot.FrontB.Eliahou.upper_convergent_cert._native.native_decide.ax_1_1]
```

Exactly the list DIRECTION asked for.  Downstream users build unchanged;
`frontier_min_cycle_length` still stands on `hercher_odd_members_bound` only.

## Route actually taken (differs from the DIRECTION sketch — simpler)

DIRECTION's route went through `tstep`, `FrontA.TrunkBound.tstep_iterate_prod_identity`,
and a `step`↔`tstep` period translation (its step 3).  **That translation is
unnecessary.**  The plain map carries its own product identity:

    step_prod_identity (n m) :
      2 ^ #(evenS n m) * step^[m] n * ∏ i ∈ oddS n m, step^[i] n
        = n * ∏ i ∈ oddS n m, (3 * step^[i] n + 1)

(`oddS`/`evenS` are the odd/even index sets in `range m`; one induction — an odd
step multiplies both sides by `3x+1`, an even step eats a `2`).  Because
`#oddS + #evenS = m` definitionally-by-induction, the period bookkeeping
`m = a + e` is free, and `a = 10781274`, `e = 17087915` are exactly Eliahou's odd
count and shortcut length.  No `Fin L` structure, no `tstep`, no reals anywhere.

From the cycle form `2^e ∏ x_i = ∏ (3x_i+1)`:
* `three_pow_lt_two_pow` : `3^a < 2^e` (each factor `3x_i+1 > 3x_i`, `a ≥ 1`);
* `two_pow_mul_pow_le`   : `2^e · x^a ≤ (3x+1)^a` for any lower bound `x ≤ x_i`;
* `two_pow_68_lt_orbit`  : every orbit member of a nontrivial cycle exceeds `2^68`
  (straight from `collatz_verified_up_to_two_pow_68` + `eq_trivial_of_onCycle_of_reachesOne`;
  we do NOT import `Conditional.lean`, which would be an import cycle).

## The Farey step — the one place a choice mattered

DIRECTION's arithmetic note (the `2^40` vs `2^68` cutoff) is right that
`17087915/10781274` is NOT inside `(log₂3, log₂(3+2^−68))`; it sits ~`1.7·10⁻¹⁵`
above `log₂3` while the interval is only ~`1.6·10⁻²¹` wide.  That makes the job
*easier*, not harder: pick the two **consecutive convergents of `log₂3` that
straddle the whole interval**,

    c₁ = 16785921/10590737 < log₂3 < e/a < log₂(3+2^−68) < 301994/190537 = c₂,

which are Farey neighbours (`10590737·301994 = 16785921·190537 + 1`) with
denominator sum `10590737 + 190537 = 10781274` — Eliahou's odd count on the nose.
`farey_denominator_bound` (pure arithmetic: `a = q₁(a p₂ − e q₂) + q₂(e q₁ − a p₁)`)
then gives `a ≥ 10781274` directly, and `3^a < 2^e` with `2^17087914 < 3^10781274`
gives `e ≥ 17087915`.  Sum: `27869189`.

**The upside of using `c₂ = 301994/190537` rather than `17087915/10781274` as the
upper neighbour is that the big certificate has exponent 190537, not 10781274** —
`(3·2^68+1)^190537` is ~1.3·10⁷ bits instead of ~7.4·10⁸.  All three certificates
`native_decide` in well under a second.

Certificates (hand-verified first in Python with exact integers, then in-kernel):
* `two_pow_lt_three_pow_cert : 2^16785921 < 3^10590737`
* `upper_convergent_cert : (3·2^68+1)^190537 < 2^(301994 + 68·190537)`
* `two_pow_lt_three_pow_big : 2^17087914 < 3^10781274`

## Gotcha worth remembering

`Nat.pow_le_pow_right (h : 0 < n) (h : i ≤ j) : n^i ≤ n^j` makes the **kernel
try to evaluate the numeral** when the exponent is a large literal:
`(kernel) the kernel refused to evaluate 'Nat.pow' … maximum numeral size`.
`pow_le_pow_right₀ (by norm_num) h` proves the same goal with no kernel
evaluation.  `Nat.pow_lt_pow_left`, `Nat.pow_le_pow_left` and
`Nat.pow_lt_pow_iff_right` are all fine at these sizes.  Likewise never let
`omega`/`norm_num` see a hypothesis containing `2^17087914` — chain `le_trans`
by hand instead.

## Standing position

The "awaiting a new mechanism" directive resumes.  Nothing here claims new
mathematics: it is the 1993 published bound, formalized, with the repo's own
`2^68` verification frontier in place of Eliahou's `2^40`.  The remaining
citation axiom in `Assumed/Cycles.lean` is `hercher_odd_members_bound`
(Hercher 2023 Cor. 29) — a genuinely harder target (Baker linear forms), and the
obvious next node if anyone wants one.
