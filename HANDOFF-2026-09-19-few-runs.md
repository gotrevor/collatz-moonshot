# HANDOFF 2026-09-19 — stopping-time correctness on first crossings with ≤ 4 odd runs

Bounded helper per the 2026-09-19 (evening) override in `DIRECTION.md` (three-lap budget;
finished in one).  **No successor lap.**

## Checkpoint
* Branch `main`; `lake build` green, 8782 jobs (pre-commit hook re-verified).  Not pushed.
* New files only: `CollatzMoonshot/FrontA/FirstCrossingFewRuns.lean`, its root import line
  (`CollatzMoonshot.lean` line 61), and this handoff.  No existing theorem or definition
  touched; `DIRECTION.md`, `STATUS.md`, `PENDING_WORK.md` and the experiments untouched.

## What landed (all seven frozen targets, verbatim; no `sorry`, no new axiom)
```
theorem last_false_of_at {n m} (h : At n m) : (traceWord n m).getLast? = some false
theorem two_pow_lt_two_mul_three_pow {n m} (h : At n m) (hK : 1 ≤ ones (traceWord n m)) :
    2 ^ m < 2 * 3 ^ ones (traceWord n m)
theorem exists_blockWord_oddRunCount_pos (v) (hhead : v.head? = some true)
    (hlast : v.getLast? = some false) :
    ∃ L, (∀ p ∈ L, 0 < p.1 ∧ 0 < p.2) ∧ v = blockWord L ∧ L.length = oddRunCount v
noncomputable def logTwoThree : ℝ := Real.log 3 / Real.log 2
theorem one_lt_logTwoThree / logTwoThree_lt (< 159/100)
noncomputable def geomS : ℕ → ℝ | 0 => 0 | r+1 => 1 + logTwoThree * geomS r
theorem geomS_four_le (≤ 914/100) / geomS_mono / geomS_nonneg
theorem two_pow_ones_le_rpow (L) (n) (hn : 1 ≤ n) (hpos) (hword) :
    (2:ℝ) ^ ones (blockWord L) ≤ ((n:ℝ)+1) ^ geomS L.length
theorem gap_mul_le_fifteen {n m} (hn : n % 2 = 1) (h : At n m) (hsurv : n ≤ tstep^[m] n)
    (hr : oddRunCount (traceWord n m) ≤ 4) :
    (2^m - 3^ones (traceWord n m)) * n ≤ 15 * 3^ones (traceWord n m)
theorem descends_of_oddRunCount_le_four (hv : CSTVerified) {n m} (hn : 2 ≤ n)
    (h : At n m) (hr : oddRunCount (traceWord n m) ≤ 4) : tstep^[m] n < n
```
Supporting lemmas introduced on the way (all sorry-free): `oddRunCount_blockWord`,
`succ_pow_sub_le`, `rpow_two_logTwoThree` (`2^log₂3 = 3`), `pow_rpow_logTwoThree`,
`succ_le_rpow_of_block`, `descends_of_even`, and the explicit logarithm ledger
`log_three_le`, `log_fifteen_le`, `log_492276_le`, `log_396_div_5_le`, `log_six_le`,
`log_rhinLiteSepC_ge` (`log (1/rhinLiteSepC) ≤ 27203`).

`#print axioms descends_of_oddRunCount_le_four` = `propext, Classical.choice, Quot.sound`
plus exactly the twelve inherited Rhin-lite `native_decide` certificates already carried by
`sep_two_three` / `descends_of_twoRun`.  Nothing beyond the allow-listed ledger.

## Mathematical content
A two-sided squeeze on `K = ones (traceWord n m)`, the number of odd steps, for an odd start
that survives its first crossing with `r ≤ 4` maximal odd runs.

*Lower side* (new, the real content of the lap).  `last_false_of_at` plus
`exists_blockWord_oddRunCount_pos` put the crossing word in block normal form with **both**
components of every block positive.  Along a block `(q, e)` with `e ≥ 1`, the segment identity
`2^(q+e) x' + 2^q = 3^q (n+1)` gives `2^q ∣ n+1` (coprimality), hence `2^q ≤ n+1`, and
`x' ≤ 3^q (n+1) / 2^(q+1)`.  Writing `3^q = (2^q)^θ` with `θ = log₂3` turns `3^q/2^q` into
`(2^q)^(θ-1) ≤ (n+1)^(θ-1)`, so `x' + 1 ≤ (n+1)^θ` (the `+1` is absorbed because
`(n+1)^θ ≥ 2`).  Iterating down the block list telescopes to
`2^K ≤ (n+1)^(geomS r)`, `geomS r = 1 + θ + … + θ^(r-1)`, and `geomS 4 ≤ 9.14`.  In logs:
`log (n+1) ≥ K · log 2 / 9.14 ≥ 0.0758 K`.  This is the step where the exponent must be
irrational, which is why the whole side is carried in `ℝ` with `rpow`.

*Upper side*.  `gap_mul_pow_le` (the integer Simons–de Weger Lemma 4 from
`FirstCrossingRuns`) with `(n+1)^r - n^r ≤ 15 n^(r-1)` for `r ≤ 4` gives `D·n ≤ 15·3^K`,
`D = 2^m - 3^K`.  The crossing window `3^K < 2^m < 2·3^K` (the second inequality is
`two_pow_lt_two_mul_three_pow`, from the final even letter) feeds
`rhinLite_log23_measure`, and `log t ≤ t - 1` converts the measure into
`rhinLiteSepC / K^436 ≤ D/3^K ≤ 15/n`, i.e.
`log n ≤ log 15 + 436 log K + log(1/rhinLiteSepC) ≤ 2.72 + 436 log K + 27203`.

*Collision*.  `ones_ge_of_survives` forces `K ≥ 492276`.  With
`log K ≤ log 492276 + K/492276 - 1 ≤ 13.11 + K/492276 - 1` (concavity) the upper side reads
`log n ≤ 32485.7 + 0.000886 K`, while the lower side reads
`0.693147 K ≤ 9.14 (log 2 + log n)`.  Together `0.685 K ≤ 296926`, i.e. `K ≤ 433435`,
against `K ≥ 492276`.  The margin is about 12 %, so the argument survives `r = 4` but
`geomS 5 ≤ 15.6` would already break it: the threshold is `geomS r ≲ 10.8`, i.e. `r ≤ 4`
exactly.  **That is the frontier this lap reached**: pushing to `r = 5` needs either a
better `log(1/rhinLiteSepC)` (currently `27203`, dominated by `6000·log(396/5)`) or a
sharper `ones_ge_of_survives` threshold, not a better telescoping.

The even-start case is separate and trivial: an even start has an even first letter, so its
first crossing has length `1` and `tstep n = n/2 < n` (`descends_of_even`).

This does **not** prove CST.  It is the `r ≤ 4` instance of `StoppingCorrect`, conditional on
the numerically verified range `CSTVerified` (Rozier–Terracol Cor. 5.4).  The genuinely open
inputs to `FirstCrossing.conjecture_of_stoppingCorrect_and_crossingExists` remain
`StoppingCorrect` (now known for `r ≤ 4`) and `CrossingExists`.

## Exact next steps (only under a NEW attended override)
1. Nothing pending from this lap; all seven frozen targets are proved and axiom-clean.
   Do not fall through to an older dated override in `DIRECTION.md`.
2. The quantitative frontier: `descends_of_oddRunCount_le_four` closes exactly while
   `geomS r · (0.000886·9.14 ... )` keeps `0.693147 - 9.14·0.000886·(geomS r / 9.14)`
   positive and `9.14 → geomS r` keeps `K ≤ 492276` unreachable.  Concretely the constraint is
   `geomS r ≤ 0.693147 · 492276 / (0.6932 + 32485.7 + 0.000886·492276) ≈ 10.36`;
   `geomS 5 ≈ 15.1` fails.  Two independent levers: (a) shrink `log(1/rhinLiteSepC)` —
   the `(396/5)^6000` factor in `rhinLiteSepC` is the whole cost, and any improvement of the
   Rhin-lite construction's block bound moves `r` up by roughly one per factor `e^3000`;
   (b) raise the `492276` threshold in `ones_ge_of_survives`, which is linear in the win.
   Neither is free, and both are genuine mathematics rather than bookkeeping.
3. A structurally different route to all `r` at once would need the run-start floor `xᵢ ≥ n`
   replaced by a growing floor, which is what the `FirstCrossingRuns` note already flags.

## Final checkpoint
* Branch: `main`.  HEAD of this lap: `9df2d8d` "Prove stopping-time correctness on first
  crossings with at most four odd runs".  Lap commits, in order:
  `2120f8d` (skeleton, seven named `sorry` leaves) → `582ce6a` (targets 1, 2, 3, 4, 6) →
  `51d191d` (target 5, the real telescoping) → `9df2d8d` (target 7, the headline).
  Working tree clean; `box done --green` signalled and the treadmill will not relaunch.
* `lake build`: green, 8782 jobs (pre-commit hook re-verified on every commit).  Not pushed;
  the host pushes.
* Files this lap: `CollatzMoonshot/FrontA/FirstCrossingFewRuns.lean` (new),
  `CollatzMoonshot.lean` (one import line), this handoff.  Nothing else touched.
