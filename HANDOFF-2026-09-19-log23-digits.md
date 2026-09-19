# HANDOFF 2026-09-19 — verified log₂3 digits; brackets by rational arithmetic; r ≤ 50

Bounded helper per the 2026-09-19 (night) override in `DIRECTION.md` (three-lap budget;
finished in one).  **No successor lap.**

## Checkpoint
* Branch `main`; `lake build` green, 8784 jobs (pre-commit hook re-verified on every commit).
  Not pushed.
* New files only: `CollatzMoonshot/FrontA/LogTwoThreeDigits.lean`, its root import line
  (`CollatzMoonshot.lean` line 62, after FirstCrossingFewRuns), and this handoff.  No existing
  theorem or definition touched; `DIRECTION.md`, `STATUS.md`, `PENDING_WORK.md` and the
  experiments untouched.
* Lap commits, in order: `3d202d3` (skeleton, ten named `sorry` leaves) →
  `0234db1` (targets 1–5) → `85203d8` (targets 6–9, the headline).

## What landed (all nine frozen targets, verbatim; no `sorry`, no new axiom)
```
theorem log_two_bounds        -- 44 verified digits of log 2
theorem log_three_bounds      -- 44 verified digits of log 3
theorem logTwoThree_bounds    -- the quotient
theorem two_pow_lt_three_pow_of_lt / three_pow_lt_two_pow_of_lt
theorem sep_strong_6e15 (k m) (hk : 0 < k) (hklt : k < 6234549927241963) (h1 : 3^k < 2^m) :
    3 ^ k ≤ (2 ^ m - 3 ^ k) * 2 ^ 58
theorem succ_pow_sub_le_runs (n r) (hn : 2*r*r ≤ n) (hr : 1 ≤ r) :
    (n + 1) ^ r - n ^ r ≤ (r + 1) * n ^ (r - 1)
theorem gap_mul_le_runs_succ  -- D * n ≤ (r+1) * 3^K
theorem ones_ge_of_survives_6e15 (hv : CSTVerified) … (hr : oddRunCount ≤ 96) :
    6234549927241963 ≤ ones (traceWord n m)
theorem descends_of_oddRunCount_le_fifty (hv : CSTVerified) {n m} (hn : 2 ≤ n)
    (h : At n m) (hr : oddRunCount (traceWord n m) ≤ 50) : tstep^[m] n < n
```
Supporting lemmas (all sorry-free): `sq_mul_succ_pow_le`, `geomS_mul_sub_one`,
`geomS_fifty_le`, `log_fiftyone_le`, `log_K0_le`.

## Axiom ledger
* `#print axioms sep_strong_6e15` = `propext, Classical.choice, Quot.sound`.  **No
  `native_decide` at all**, and in particular no `pow_cert_10781274` — that is the whole point
  of the module.
* `#print axioms descends_of_oddRunCount_le_fifty` = the standard three plus exactly the
  **eleven** inherited Rhin-lite certificates (`rhinLiteI₁_ratio_base`,
  `rhinLiteRootLeft_ge_three`, `rhinLite_boundProduct_certificate(_tight)`,
  `rhinLite_cauchy_radius_certificate`, `rhinLite_critical_sign_change`,
  `rhinLite_factorBound_nonneg`, `rhinLite_positiveRootLeft`, `rhinLite_rootBracket_lt`,
  `rhinLite_rootBrackets_separated`, `seventeen_pow_scale_le_rhinLiteBlockTerm`).
  `descends_of_oddRunCount_le_four` carries twelve; the twelfth was `pow_cert_10781274`,
  reached through `sep_strong_492276` inside `ones_ge_of_survives`.  The new route drops it.

## Mathematical content

**1. Digits, and why DIRECTION's route for `log 3` had to be changed.**  The frozen route was
"prove `log_two_bounds`, then `log 3 = log 2 + log(3/2)` and combine".  That loses
`U₂ − log 2 ≈ 1.56·10⁻⁴⁵` to the rounding of the `log 2` bound, on top of the two Taylor
remainders; the frozen upper digit `…749057` has only `2.2·10⁻⁴⁵` of slack, so the combination
does not close (it fails by a hair — the *exact* obstruction is `U₃ − U₂ = L₃ − L₂`, so the
rounded windows leave no room at all).  `log_three_bounds` therefore re-derives both Taylor
bounds and keeps **both remainders symbolic** until one final `linarith`:
`log 3 ≤ S₂ + S₃ + r₂ + r₃` with `r₂ = 2⁻¹⁵⁰ ≈ 7.0·10⁻⁴⁶`, `r₃ = (1/3)⁹⁷·(3/2) ≈ 2.4·10⁻⁴⁶`,
total `< 10⁻⁴⁵`, against `1.22·10⁻⁴⁴` of available margin.  The frozen *statement* is
unchanged; only the route is.  Both rational sums (`range 150` at `x = 1/2`, `range 96` at
`x = 1/3`) evaluate under `simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num`
in a few seconds each with `maxRecDepth 100000`.

**2. Why a bracket by digits is unboundedly better than a bracket by power comparison.**
`sep_strong_of_bracket_nat` needs four certified inequalities `2^a < 3^b`.  Certified by
`native_decide` these are comparisons of numerals with `b·log₂3` bits: `pow_cert_10781274`
already compares five-million-digit integers, and the *next* convergent is out of reach.
Certified by 44 digits they are comparisons of 16-digit integers against 45-digit ones, i.e.
`norm_num`, at **any** denominator up to ~`10⁴³`.  The convergent/semiconvergent quadruple used
here sits at `b + d = 6234549927241963` with `j = 58`, all four hypotheses `norm_num`-checked.

**3. The scaled Bernoulli, which is the real new lemma.**  The `r ≤ 4` file used
`(n+1)^r − n^r ≤ 15 n^(r−1)` by `interval_cases`; a constant is hopeless for general `r`.  The
clean statement is `(n+1)^r − n^r ≤ (r+1)n^(r−1)` under `2r² ≤ n`, but the obvious induction
`n(n+1)^r ≤ (n + r + 1)n^r` **fails**: the step needs `c_{r+1} ≥ 1 + c_r + c_r/n`, and
`c_r = r+1` misses by exactly `(r+1)/n`.  Scaling by `n²` instead fixes it: with
`c_r = r + r²/n`, i.e.
```
n² (n+1)^r ≤ (n² + r n + r²) n^r              (2r² ≤ n)
```
the inductive step reduces to `r² ≤ (r+1)n`, which `2r² ≤ n` gives with room to spare, and
every quantity stays a natural number.  Dividing back by `n²` and using `rn + r² ≤ (r+1)n`
(again from `r² ≤ n`) gives the target.  This is `sq_mul_succ_pow_le`.

**4. The threshold jump, and where the factor comes from.**  `ones_ge_of_survives` routes
through `small_start_of_not_descending` (`3·D·n ≤ K·3^K`), whose factor `K` is fatal at the new
scale: `3n ≤ K·2^58` with `K < 6.2·10¹⁵` only bounds `n` by `1.5·10³³`, far outside the
verified range.  Target 7 (`D·n ≤ (r+1)3^K`) has **no** `K` factor, so with `r ≤ 96`
`n ≤ 97·2^58 = 27958346486716039168 < 2.8·10¹⁹` lands exactly inside Rozier–Terracol's
verified range.  That `97·2^58 < 28·10^18` is tight to 0.15 % and is what fixes `96` as the
run-count hypothesis in target 8.  The cost is the side condition `2r² ≤ n`, discharged by
observing that `n < 2·96² = 18432` is itself inside the verified range.

**5. The pincer.**  `geomS r·(θ−1) = θ^r − 1` (`geomS_mul_sub_one`, `linear_combination θ·ih`)
with `1.58 < θ ≤ 1.59` gives `geomS 50 ≤ (1.59⁵⁰ − 1)/0.58 ≤ 2.03·10¹⁰ ≤ 2.1·10¹⁰`.  Then
* upper: `log n ≤ log 51 + 436 log K + 27203 ≤ 4.16 + 436(35.4 + K/K₀) + 27203`, using
  `log K₀ ≤ 36.4` (`log_K0_le`, via `log t ≤ t − 1` at `t = K₀/(3·2⁵¹) ≈ 0.9229`) and concavity;
* lower: `K log 2 ≤ geomS 50 · log(n+1) ≤ 2.1·10¹⁰ (log 2 + log n)`.

Together `(0.6931 − 0.00147) K ≤ 8.955·10¹⁴`, i.e. `K ≤ 1.295·10¹⁵`, against
`K ≥ 6.2345·10¹⁵`.  Margin factor ≈ 4.8.

## The frontier this lap reached
The binding constraint is now `geomS r ≲ K₀ · log 2 / (geomS-side constant)`, which with the
present ledger reads `geomS r ≤ 1.0·10¹¹`, i.e. `θ^r ≲ 6·10¹⁰`, i.e. **`r ≤ 53`**.  Three
observations for whoever picks this up:

1. Raising `r` further is now **logarithmic in the bracket scale, not exponential in
   certificate cost**.  The digits certify brackets at any denominator up to ~`10⁴³`; a
   convergent of `log₂3` near `10^D` gives `j ≈ log₂(2·10^D)` and threshold `K₀ ≈ 10^D`, so
   the pincer's slack grows like `D·log 10` while `geomS r` grows like `r·log θ`.  Very
   roughly `r_max ≈ 1.5 D + 3`.  Getting `r ≤ 100` needs a convergent near `10^65`, which is
   past the 44-digit bracket; **more digits is the cheap lever** — `log_two_bounds` at
   `range 400` and `log_three_bounds` at `range 260` would give ~120 digits at the same cost
   structure, and the only other input is a convergent table of `log₂3`, pure host arithmetic.
2. `log(1/rhinLiteSepC) ≤ 27203` is still dominated by `6000·log(396/5)` and is now the
   *subdominant* term (it contributes `436·log K₀ ≈ 15.4·10³` against `27.2·10³`); improving
   it buys a bounded amount, unlike (1).
3. Every `r` at once still needs the structural change the `FirstCrossingRuns` note flags:
   the run-start floor `xᵢ ≥ n` replaced by a growing floor.  Nothing in this lap touches that.

This does **not** prove CST.  It is the `r ≤ 50` instance of `StoppingCorrect`, conditional on
`CSTVerified` (Rozier–Terracol Cor. 5.4).  The genuinely open inputs to
`FirstCrossing.conjecture_of_stoppingCorrect_and_crossingExists` remain `StoppingCorrect`
(now known for `r ≤ 50`) and `CrossingExists`.

## Exact next steps (only under a NEW attended override)
Nothing pending from this lap; all nine frozen targets are proved and axiom-clean.  Do not fall
through to an older dated override in `DIRECTION.md`.  The one concrete, bounded follow-up is
item (1) above: more Taylor terms plus a deeper convergent, which is mechanical given this
module and moves `r` to roughly `1.5·(digits)/1` — genuine but incremental; it does not
approach the structural obstruction.

## Final checkpoint
* Branch: `main`.  Lap commits, in order:
  `3d202d3` (compiling skeleton, ten named `sorry` leaves) →
  `0234db1` (targets 1–5: verified digits, brackets, `sep_strong_6e15`) →
  `85203d8` (targets 6–9: scaled Bernoulli, raised threshold, the headline) →
  `56e9287` (handoff) → this commit, which is the lap HEAD (`git log -1` on `main`).
* `lake build`: green, 8784 jobs, re-verified by the pre-commit hook on every commit.
  Not pushed; the host pushes.
* Working tree clean.  `box done --green` signalled; the treadmill will not relaunch.
* Files this lap: `CollatzMoonshot/FrontA/LogTwoThreeDigits.lean` (new),
  `CollatzMoonshot.lean` (one import line, 62), this handoff.  Nothing else touched —
  `DIRECTION.md`, `STATUS.md`, `PENDING_WORK.md` and `experiments/` are untouched, as the
  override required.
* `src/` sorry count contributed by this lap: 0.
