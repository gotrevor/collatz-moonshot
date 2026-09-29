# Handoff: bounded unit size forces bounded label support

**Checkpoint 2026-09-29.**  Branch `main`, HEAD `491463c` ("Prove the rational
product label bound and its value-one unit corollary").  Root `lake build`
green (pre-commit hook verified, 8814 jobs).  Scoped objective
`sorry-free:CollatzMoonshot/Obstructions/UnitSupportBound.lean` is **met**;
`box done --green` signalled.  Working tree still carries other agents'
uncommitted experiment/notes files — not mine, left untouched.

`CollatzMoonshot/Obstructions/UnitSupportBound.lean` is complete, green, and
axiom-clean (`propext, Classical.choice, Quot.sound` only).  No `sorry`, no new
cited axiom.  The two frozen statements and `productLabelBound` are unchanged.

## What is proved

`rational_product_labels_bounded`: if `a * ∏ u = b * ∏ (3u+1)` for a list `xs`
of positive labels, with `0 < b ≤ B`, then every label is at most
`productLabelBound xs.length B`.  `unit_labels_bounded` is the `b = B = 1`
corollary: a positive value-one word with `q` odd edges has all labels bounded
by `productLabelBound q 1`.

## How

Everything stays in ℕ; the rational statement `a/b = ∏(3 + 1/u) > 3^q` is used
only through its cleared-denominator shadows.

* `pow_mul_prod_lt`: for nonempty positive `xs`, `3^q * ∏u < ∏(3u+1)`.  Hence
  `b * 3^q < a`, so `a ≥ b*3^q + 1`, so `b*(3^q*P) + P ≤ b*Q` — the exact
  integral form of `a/b - 3^q ≥ 1/b`.
* `prod_excess_le`: with `v ≤ u` for all labels,
  `v*Q ≤ v*(3^q*P) + q*(4^q*P)` — the integral form of the telescoping bound
  `∏(3+1/u) - 3^q ≤ q*4^q/v`.  Its inductive core is `excess_step`, which needs
  only `v ≤ u`, `3^n ≤ 4^n` and `3u+1 ≤ 4u`; the loose `4^q` is what removes
  all predecessor arithmetic.
* Multiplying the first by `v` and the second by `b` cancels the common
  `v*b*3^q*P` and leaves `v*P ≤ b*q*4^q*P`, so `v ≤ q*4^q*B = m`.
* Erasing a least label (`List.perm_cons_erase`, so both `P` and `Q` factor at
  once) reproduces the same hypothesis with `a' = a*v`, `b' = b*(3v+1) ≤
  B*(3m+1)`, and the induction on length closes against the `max` in
  `productLabelBound`.

Sorting is not used; `exists_min_mem` plus `List.erase` was enough.

## What this means for the research line

The content is a genuine obstruction, not plumbing: **unbounded auxiliary
labels require unbounded unit size.**  Any construction that tries to realize a
value-one (unit) word by reaching for ever larger labels `u` while holding the
odd-edge count `q` fixed is impossible — for each `q` the label support lives in
a finite set, so the search for exact positive units at a given `q` is a finite
problem, and any repair scheme that needs an unbounded label to close a deficit
is thereby refuted at fixed `q`.  Conversely the only way to escape the bound is
to let `q` grow, and the bound's growth in `q` is where the real question sits.

The intentionally coarse `4^q` makes `productLabelBound` far too large to
enumerate directly, and that is the honest next research step: replace the
`q*4^q*B` excess estimate by the true `∏(3+1/u) - 3^q` asymptotics (the excess
is `3^q * (∑ 1/(3u) + O(...))`, so the truth is nearer `3^q * q / v`, giving
`v ≲ 3^q q B` after the same cancellation, and sharper still with the real
minimum rather than a uniform `v`).  That is what would turn this finiteness
statement into an effective search bound.  Do **not** spend the next lap
micro-optimizing the current recursion's constants; the payoff is in the
analytic estimate, not in the list plumbing, which is finished.

## Exact next steps (for whoever picks this up)

1. Nothing is owed on this module: it is sorry-free and axiom-clean, and both
   frozen statements are unchanged from the kickoff.  Re-audit by diffing the
   two theorem signatures and `productLabelBound` against
   `KICKOFF-2026-09-28-unit-support-bound.md` if you want the check.
2. The open research step is the analytic sharpening described above: replace
   `prod_excess_le`'s `q*4^q` by the true excess `3^q*(∑ 1/(3u) + …)`, yielding
   `v ≲ 3^q*q*B` after the identical cancellation in `bounded_aux`.  Only
   `prod_excess_le` and `excess_step` would change; `pow_mul_prod_lt` and the
   erase/induction skeleton are reusable verbatim.
3. Do not spend a lap tightening `productLabelBound`'s constants.  Per
   `DIRECTION.md`, the repo's standing objective is the run-count gap on
   first-crossing near-cycles, which this module does not touch and which no
   current directive authorizes a proof lap on.
