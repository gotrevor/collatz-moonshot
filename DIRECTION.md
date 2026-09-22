# DIRECTION — collatz-moonshot

## Standing objective after 2026-09-19 (Fable): the run-count gap on first-crossing near-cycles

All three 2026-09-19 helper overrides below are COMPLETE (`182e2ca`, `39c7949`, `5b21804`); none
authorizes a successor.  The first-crossing route now stands as follows (details: README proof
status, STATUS 2026-09-19 entry, personal KB leaves `collatz-near-cycle-few-runs-2026-09-19.md`
and `collatz-avenues-blueprint-2026-09-19.md`):

- A `StoppingCorrect` failure is a **near-cycle**: `D·n + 2^m·E = numer`, `3E < a`, and with `r`
  odd runs `E ≤ r` (about); `E = 0` is the cycle case.  Simons–de Weger's `m`-cycle pincer
  transfers verbatim, giving CST on ≤ 68 runs on paper and ≤ 50 runs in Lean
  (`Assumed.stoppingCorrect_of_oddRunCount_le_fifty`, one named computation axiom).  The ladder
  STOPS at fifty by decision: the remaining rungs to 68 are Rhin's published exponent, not new
  mathematics.
- The exact reach of every two-log pincer is **logarithmically many runs**: a near-cycle with `K`
  odd steps has `r ≳ 2.17·ln K` runs (SdW Lemma 14 transferred).  Collatz needs `r ≥ ε·K`; a
  typical word has `r ≈ K/2`.  Everything between is new mathematics.

**Node (run-count gap).**  `∀ n m, 2 ≤ n → At n m → n ≤ tstep^[m] n → f(ones) ≤ oddRunCount`
with `f(K) = ε·K`.  Proved: `f = 2.17·ln K − O(ln ln K)` (paper).  Probe: over first-crossing
words, the least `r/K` among near-misses (`experiments/parity_reconstruction.py near-cycle`, extend
with `runs`); a few-run near-miss refutes any proposed intermediate `f`.  What a mechanism must do:
turn the ballot structure of a first-crossing word into a lower bound on its reconstruction residue
that grows faster than any polynomial in `m`, uniformly over words with `r ≥ εK` runs.  The
function-field case shows what that looks like when carries are absent.

Retired the same day, with reasons in the blueprint leaf: coalescence / smaller-start reduction
(measured, zero gain at the stopping-time records); polynomial-frequency Fourier majorants;
run-merging as a descent on `r` (the offset shifts by `(2^{l₁}−1)·2^{k₁}·(3^{k₂}−2^{k₂})`);
"CST ⇐ polynomial stopping-time bound" (true via `survivor_ones_pow_ge`, circular); automatic-set /
Cobham angle; Christoffel-word residue signatures (probed, none); "extremal words are the dangerous
ones" (probed, false); Hercher 2023 transfer (checked, does not: his 68 → 91 gain is the
orbit-merging lemma, which needs a closed orbit and a convergence frontier; paper reach stays 68).
Ballot-coalescence rigidity ("two ballot words of one shape never coalesce", and the one-sided
"a ballot numerator is least in its class"): **refuted** 2026-09-19 at lengths 34 and 29
(`experiments/parity_reconstruction.py ballot-walk 34 4`, `ballot-nonmin 29 0`, anchors by direct
iteration) - the zero-collision count to length 30 was a small-length artifact; the minimality
lever (the least CST failure has no prefix that is the smaller-numerator member of a ballot pair)
stands and is thin by counting.
🛑 **No lap without a mechanism for the gap node.**  `CrossingExists`
(the Π₂, symbolic half) has no lever on the board at all.

**2026-09-22 (Fable) - goal audit and mechanism search, no lap.**  Detail:
`RESEARCH-2026-09-22-mechanism-search.md`.  (i) The node above is the few-run exclusion made
uniform; it does **not** imply CST.  `StoppingCorrect ⟺ N_ε ∧ C_ε` where `C_ε` = *no survivor
with `r ≥ εK` runs*, and `C_ε` contains the many-circuit cycle problem (a cycle's minimum is a
survivor with `E = 0`) plus the "orbit below a cycle" shape.  The honest frozen node is `C_ε`.
(ii) The run-to-run admission equations carry exactly **one** congruence (Cramer, det `= D`;
integrality of `(N − 2ᵐE)/D` already forces the residue class): multiplying run bounds loses
magnitude only.  Round A is closed - do not re-open it with different run bookkeeping.
(iii) New control: under `5n+1` the starts `13, 17` (cycles) and `5` (`m = 274`, `K = 118`,
`39` runs, `E = 8`) are first-crossing survivors, so any `C_ε` mechanism valid for every odd
multiplier is false; it must consume the ballot entropy deficit or the verified range
(`experiments/sibling_survivors.py`).  For `3n−1` there is no survivor at all (`N < 0`), so
the sign control for CST is vacuous; the sign control for `CrossingExists` is `3n−1`, `n = 5`.
(iv) Retired with reasons: minimal-counterexample suffix constraints (all run starts lie above
the least failure - circular); ballot-residue discrepancy (needs exact count `0`, every
counting bound stops at error `≳ √|B_m|`).  (v) Lean, axiom-clean: `at_primitive` (a
first-crossing word is never a proper power), `overshoot_modEq` (`3ᴷE ≡ N (mod D)`), in
`FrontA/FirstCrossingResidue.lean`.  The gate below stands unchanged.

## Attended operator override: 2026-09-19 (Fable, night) - verified log₂3 digits, and r ≤ 50

Standing authorization (Trevor, 2026-09-19: "keep planning in parallel with the grind").  Opus-low
helper, **at most three laps**.  Create `CollatzMoonshot/FrontA/LogTwoThreeDigits.lean` importing
`CollatzMoonshot.FrontA.FirstCrossingFewRuns`.  Do not change any existing theorem or definition.
Your only files are this module, its root import line (after FirstCrossingFewRuns), and a short
dated handoff `HANDOFF-2026-09-19-log23-digits.md`.  Do not edit DIRECTION or experiments.  No
successor task.  **Commit a compiling skeleton with named `sorry` leaves first.**  `.lake/build`
is warm (host built `7005730`); never `lake exe cache get`.

Namespace `CollatzMoonshot.FrontA.FirstCrossing`, `open CollatzMoonshot CollatzMoonshot.FrontB`.
Purpose: the repo certifies brackets `2^a < 3^b` by power comparison, which dies at the numeral
cap (`pow_cert_10781274` is a 5-million-digit `native_decide`).  Forty-four verified digits of
`log 2` and `log 3` certify the same brackets by rational arithmetic at ANY scale.  With the
bracket at denominators ~6·10¹⁵ the pincer of `descends_of_oddRunCount_le_four` extends to fifty runs.

Available: everything in FewRuns (`geomS`, `geomS_mono`, `geomS_nonneg`, `logTwoThree`,
`two_pow_ones_le_rpow`, `exists_blockWord_oddRunCount_pos`, `last_false_of_at`,
`two_pow_lt_two_mul_three_pow`, `descends_of_even`, the log ledger incl. `log_rhinLiteSepC_ge`),
`gap_mul_pow_le` (Runs), `sep_strong_of_bracket_nat` and `lt_logb_two_three_iff` /
`logb_two_three_lt_iff` (RhinLiteSep; note `Real.logb 2 3 = Real.log 3 / Real.log 2 = logTwoThree`
by `Real.logb`), `rhinLite_log23_measure`.  Mathlib: `Real.abs_log_sub_add_sum_range_le`
(`|x| < 1 → |(∑ i ∈ range n, x^(i+1)/(i+1)) + log (1 - x)| ≤ |x|^(n+1)/(1 - |x|)`),
`Real.log_div`, `Finset.sum_range_succ`, `norm_num`.

Freeze these targets exactly:

1. `theorem log_two_bounds :
       (69314718055994530941723212145817656807550013 : ℝ) / 10 ^ 44 < Real.log 2 ∧
       Real.log 2 < (69314718055994530941723212145817656807550015 : ℝ) / 10 ^ 44`
   Route: `Real.log 2 = -Real.log (1 - 1/2)`; apply `Real.abs_log_sub_add_sum_range_le` with
   `x = 1/2`, `n = 150` (remainder ≤ 2^(-150) < 10^(-45)); the partial sum is a rational, evaluate it
   with `simp only [Finset.sum_range_succ, Finset.sum_range_zero]` then `norm_num` (if `norm_num`
   is slow, split the sum into blocks of 25 with `Finset.sum_range_add`-style lemmas, or prove
   the rational value with `decide`-free `norm_num` on each block).  Then `abs_lt` and `linarith`.

2. `theorem log_three_bounds :
       (109861228866810969139524523692252570464749055 : ℝ) / 10 ^ 44 < Real.log 3 ∧
       Real.log 3 < (109861228866810969139524523692252570464749057 : ℝ) / 10 ^ 44`
   Route: `Real.log 3 = Real.log 2 + Real.log (3/2)` and `Real.log (3/2) = -Real.log (1 - 1/3)`,
   `x = 1/3`, `n = 96` (remainder ≤ (1/3)^97·(3/2) < 10^(-45)); combine with target 1.

3. `theorem logTwoThree_bounds :
       (109861228866810969139524523692252570464749055 : ℝ) / 69314718055994530941723212145817656807550015
         < logTwoThree ∧
       logTwoThree < (109861228866810969139524523692252570464749057 : ℝ) / 69314718055994530941723212145817656807550013`
   (quotients of the bounds; `div_lt_div_iff`, both logs positive.)

4. `theorem two_pow_lt_three_pow_of_lt {a b : ℕ} (hb : 0 < b)
       (h : (a : ℝ) / b < (109861228866810969139524523692252570464749055 : ℝ) / 69314718055994530941723212145817656807550015) :
       2 ^ a < 3 ^ b`
   and
   `theorem three_pow_lt_two_pow_of_lt {c d : ℕ} (hd : 0 < d)
       (h : (109861228866810969139524523692252570464749057 : ℝ) / 69314718055994530941723212145817656807550013 < (c : ℝ) / d) :
       3 ^ d < 2 ^ c`
   via targets 3 and `lt_logb_two_three_iff` / `logb_two_three_lt_iff` (unfold `Real.logb`).

5. The bracket at the 6·10¹⁵ scale (consecutive convergents of log₂3; all four hypotheses of
   `sep_strong_of_bracket_nat` verified on the host by exact rational arithmetic 2026-09-19):
     outer lower  a/b   = 766512153894657 / 483615324366283
     outer upper  c/d   = 9115015689657667 / 5750934602875680      (b·c = a·d + 1)
     inner lower  a'/b' = 9881527843552324 / 6234549927241963
     inner upper  c'/d' = 206745572560704147 / 130441933147714940
     j = 58                                                     (2·max(b',d') ≤ 2^58)
   `theorem sep_strong_6e15 (k m : ℕ) (hk : 0 < k) (hklt : k < 6234549927241963)
       (h1 : 3 ^ k < 2 ^ m) : 3 ^ k ≤ (2 ^ m - 3 ^ k) * 2 ^ 58`
   by `sep_strong_of_bracket_nat k m 766512153894657 483615324366283 9115015689657667 5750934602875680
   9881527843552324 6234549927241963 206745572560704147 130441933147714940 58 …`, the four power
   inequalities from target 4 (the rational comparisons are `norm_num`), `huni`/`hin1`/`hin2`/`hg1`/`hg2`
   by `norm_num`.  Note `b + d = 6234549927241963`.

6. `theorem succ_pow_sub_le_runs (n r : ℕ) (hn : 2 * r * r ≤ n) (hr : 1 ≤ r) :
       (n + 1) ^ r - n ^ r ≤ (r + 1) * n ^ (r - 1)`
   Route: `(n+1)^r - n^r ≤ r·(n+1)^(r-1)` (telescoping / `Nat.sub_le` of the binomial), and the
   Bernoulli-type `(n+1)^k · (n+1-k) ≤ n^k · (n+1)` for `k ≤ n+1` (induction on k), so with
   `k = r-1 ≤ (n+1)/2`: `(n+1)^(r-1) ≤ n^(r-1) · (n+1)/(n+1-(r-1)) ≤ n^(r-1)·(1 + 2(r-1)/n)`, and
   `r·(1 + 2(r-1)/n) ≤ r + 1` when `2r(r-1) ≤ n`.  Any correct route is fine.

7. `theorem gap_mul_le_runs_succ {n m : ℕ} (hn : n % 2 = 1) (h : At n m) (hsurv : n ≤ tstep^[m] n)
       (hbig : 2 * oddRunCount (traceWord n m) * oddRunCount (traceWord n m) ≤ n) :
       (2 ^ m - 3 ^ ones (traceWord n m)) * n ≤ (oddRunCount (traceWord n m) + 1) * 3 ^ ones (traceWord n m)`
   from `gap_mul_pow_le` and target 6 (r ≥ 1 since the word starts odd), cancelling `n^(r-1)`.

8. `theorem ones_ge_of_survives_6e15 (hv : CSTVerified) {n m : ℕ} (hn : 2 ≤ n) (h : At n m)
       (hsurv : n ≤ tstep^[m] n) (hr : oddRunCount (traceWord n m) ≤ 96) :
       6234549927241963 ≤ ones (traceWord n m)`
   Route: n odd (else descent by `descends_of_even`), K := ones ≥ 1.  If `K < 6234549927241963`:
   `sep_strong_6e15` gives `3^K ≤ D·2^58`; `n ≥ 2·96² = 18432` holds because otherwise `hv`
   applies directly (n ≤ 28·10¹⁸); target 7 gives `D·n ≤ 97·3^K ≤ 97·D·2^58`, so
   `n ≤ 97·2^58 = 27958346486716039168 < 28·10^18`, and `hv` forces descent.  Contradiction.

9. `theorem descends_of_oddRunCount_le_fifty (hv : CSTVerified) {n m : ℕ} (hn : 2 ≤ n)
       (h : At n m) (hr : oddRunCount (traceWord n m) ≤ 50) : tstep^[m] n < n`
   Same pincer as `descends_of_oddRunCount_le_four`, with: K ≥ 6234549927241963 (target 8);
   upper bound `D·n ≤ 51·3^K` (target 7) hence `(n:ℝ) ≤ 51·K^436 / rhinLiteSepC` via
   `rhinLite_log23_measure` and `Real.log_le_sub_one_of_pos`; lower bound
   `K·log 2 ≤ geomS 50 · log (n+1)` with `geomS 50 ≤ (159/100)^50 / (59/100) < 2.1·10^10`
   (prove `geomS r ≤ logTwoThree^r / (logTwoThree - 1)` by induction, or bound term by term).
   Numerics: `log (n+1) ≥ K·0.6931/(2.1·10^10) ≥ 3.3·10^(-11)·K ≥ 2.05·10^5` at `K = 6.23·10^15`,
   while `log n ≤ log 51 + 436·log K + 27203 ≤ 3.94 + 436·36.4 + 27203 < 43100`; use the concavity
   step `log K ≤ log K₀ + (K - K₀)/K₀` at `K₀ = 6234549927241963` (`log K₀ ≤ 36.37`) and
   `log (n+1) ≤ log 2 + log n`, exactly as in the r ≤ 4 proof.  Margin is a factor ~5; do not tune.

Build the module and the root, run `#print axioms descends_of_oddRunCount_le_fifty` (expect the
standard three plus the inherited Rhin-lite `native_decide` certificates and NO `pow_cert_10781274`
- the point of the module is that this bracket uses no power certificate; report the ledger),
commit, then `box done --green`.  If a frozen statement is false, report the counterexample; do not
weaken it.  This gives `StoppingCorrect` on all first crossings with at most fifty odd runs, modulo
the explicit verification hypothesis.  It does NOT prove CST.

## Attended operator override: 2026-09-19 (Fable, evening) - few-run stopping-time helper, r ≤ 4

Trevor's standing authorization for this campaign ("carry on & keep on trucking", 2026-09-19);
Opus-low helper, **at most three laps**.  Create `CollatzMoonshot/FrontA/FirstCrossingFewRuns.lean`
importing `CollatzMoonshot.FrontA.FirstCrossingRuns` (which brings FirstCrossingTwoRun,
FirstCrossingOneRun, FirstCrossing, FixedBlocks, OneCircuit; `RhinLiteSep` is reachable through
FirstCrossing → Paradoxical).  Do not change any existing theorem or definition.  Your only files
are this module, its line in `CollatzMoonshot.lean` (after the FirstCrossingRuns import), and a
short dated handoff `HANDOFF-2026-09-19-few-runs.md`.  Do not edit DIRECTION or experiments.  No
successor task.  **Commit a compiling skeleton with named `sorry` leaves first.**  `.lake/build`
is warm (host built `04869eb`); never `lake exe cache get`.

Namespace `CollatzMoonshot.FrontA.FirstCrossing`, `open CollatzMoonshot CollatzMoonshot.FrontB`.
Available: `At`, `numerator_bound`, `prefix_supercritical_trace`, `take_traceWord`
(FirstCrossing); `traceWord_add`, `ones_replicate_false'` (OneRun); `CSTVerified`,
`ones_ge_of_survives`, `iterate_ge_of_prefix_supercritical`, `run_true`, `run_false`
(TwoRun); `run_product_bound`, `gap_mul_pow_le`, `blockWord_cons_length` (Runs);
`exists_blockWord_oddRunCount`, `segment_identity_of_word`, `oddRunCount` (FixedBlocks /
ThreeBlock); `rhinLite_log23_measure (k m) (hk : 1 ≤ k) (h1 : 3^k < 2^m) (h2 : 2^m < 2*3^k) :
rhinLiteSepC / k^436 ≤ m * Real.log 2 - k * Real.log 3`, `rhinLiteSepC_pos`, and
`rhinLiteSepC = 1 / (2 * ((396/5 : ℝ)^6000 * 6^436))` (RhinLiteSep).  Mathlib:
`Real.log_two_lt_d9`, `Real.log_two_gt_d9`, `Real.add_one_le_exp`, `Real.log_le_sub_one_of_pos`,
`Real.rpow_natCast`, `Real.rpow_le_rpow_left_iff`, `Real.rpow_mul`, `Real.log_lt_log`.

Freeze these targets exactly (add any helper lemmas you like):

1. `theorem last_false_of_at {n m : ℕ} (h : At n m) : (traceWord n m).getLast? = some false`
   Route: m ≥ 1; `traceWord n m = traceWord n (m-1) ++ [decide (tstep^[m-1] n % 2 = 1)]` by
   `traceWord_add` with second argument 1.  If the last letter were `true`, `ones = ones(prefix)+1`
   and the prefix condition `h.2.1 (m-1)` gives `2^(m-1) ≤ 3^ones(prefix)`, so
   `2^m ≤ 2·3^ones(prefix) < 3^(ones(prefix)+1)`, against `h.2.2`.

2. `theorem two_pow_lt_two_mul_three_pow {n m : ℕ} (h : At n m) :
       2 ^ m < 2 * 3 ^ ones (traceWord n m)`
   From 1 and `h.2.1 (m-1)`: `2^(m-1) ≤ 3^K` with K = ones of the whole word (the last letter is
   even), strict because `3^K` is odd and `m ≥ 1` (if `2^(m-1) = 3^K` then K = 0 and m = 1, but
   then `2^m < 2` fails... handle K = 0 separately: then the word is all-even and m = 1, giving
   `2 < 2·1`? — no: K = 0 forces m = 1 and the claim reads `2 < 2`, FALSE).  So freeze with the
   extra hypothesis `(hK : 1 ≤ ones (traceWord n m))`.

3. `theorem exists_blockWord_oddRunCount_pos (v : List Bool) (hhead : v.head? = some true)
       (hlast : v.getLast? = some false) :
       ∃ L : List (ℕ × ℕ), (∀ p ∈ L, 0 < p.1 ∧ 0 < p.2) ∧ v = blockWord L ∧
         L.length = oddRunCount v`
   Copy the proof of `exists_blockWord_oddRunCount` (FixedBlocks.lean:42); the `r = []` branch
   (word `1^q`) contradicts `hlast`; in the recursive branch `s.getLast? = v.getLast?` because
   `s ≠ []` (`List.getLast?_append`).

4. `noncomputable def logTwoThree : ℝ := Real.log 3 / Real.log 2`
   `theorem one_lt_logTwoThree : 1 < logTwoThree` and
   `theorem logTwoThree_lt : logTwoThree < 159 / 100`   (from `(3:ℝ)^100 < 2^159` by `norm_num`,
   `Real.log_lt_log`, `Real.log_pow`).
   `def geomS : ℕ → ℝ | 0 => 0 | r + 1 => 1 + logTwoThree * geomS r`
   `theorem geomS_four_le : geomS 4 ≤ 914 / 100` and `theorem geomS_mono : Monotone geomS`.

5. `theorem two_pow_ones_le_rpow (L : List (ℕ × ℕ)) : ∀ n : ℕ, 1 ≤ n →
       (∀ p ∈ L, 0 < p.1 ∧ 0 < p.2) → traceWord n (blockWord L).length = blockWord L →
       (2 : ℝ) ^ ones (blockWord L) ≤ ((n : ℝ) + 1) ^ geomS L.length`
   (real power `^` with real exponent).  Induction on L generalizing n.  Head block `(q, e)`,
   `x' := tstep^[q+e] n`, from `segment_identity_of_word`: `2^(q+e) x' + 2^q = 3^q (n+1)`, so
   `2^q ∣ 3^q (n+1)` hence `2^q ∣ n+1` (`Nat.Coprime.pow`), so `(2:ℝ)^q ≤ n+1`; and
   `x' ≤ 3^q (n+1) / 2^(q+1)` (e ≥ 1).  Since `(3:ℝ)^q = (2^q)^logTwoThree`
   (`Real.rpow_def_of_pos`, `Real.rpow_natCast`), `3^q / 2^q = (2^q)^(logTwoThree-1) ≤ (n+1)^(logTwoThree-1)`,
   so `x' ≤ (n+1)^logTwoThree / 2` and `x' + 1 ≤ (n+1)^logTwoThree` (as `(n+1)^logTwoThree ≥ 2`).
   Induction hypothesis at `x'`, then `((x'+1))^(geomS r') ≤ ((n+1)^logTwoThree)^(geomS r') = (n+1)^(logTwoThree * geomS r')`
   (`Real.rpow_le_rpow`, `Real.rpow_mul`, `geomS r' ≥ 0`), and `2^(q + K') ≤ (n+1)^(1 + logTwoThree * geomS r')`.

6. `theorem gap_mul_le_fifteen {n m : ℕ} (hn : n % 2 = 1) (h : At n m) (hsurv : n ≤ tstep^[m] n)
       (hr : oddRunCount (traceWord n m) ≤ 4) :
       (2 ^ m - 3 ^ ones (traceWord n m)) * n ≤ 15 * 3 ^ ones (traceWord n m)`
   From `gap_mul_pow_le` and, for r = 1, 2, 3, 4 (r ≥ 1 as the word starts odd),
   `(n+1)^r - n^r ≤ 15 * n^(r-1)` for n ≥ 1 (`interval_cases` on r, then `nlinarith`/`ring_nf`),
   cancelling `n^(r-1) > 0`.

7. `theorem descends_of_oddRunCount_le_four (hv : CSTVerified) {n m : ℕ} (hn : 2 ≤ n)
       (h : At n m) (hr : oddRunCount (traceWord n m) ≤ 4) : tstep^[m] n < n`
   Even n: the first letter is false, so `h.2.1 1` fails unless m = 1, and then
   `2 * tstep n = n` gives descent (factor this as `descends_of_even`).  Odd n, by contradiction
   `n ≤ y`.  K := ones ≥ 492276 by `ones_ge_of_survives`.
   Upper: `gap_mul_le_fifteen` gives `D n ≤ 15 · 3^K`; `rhinLite_log23_measure K m` (window from 2)
   gives `rhinLiteSepC / K^436 ≤ m log 2 − K log 3 = Real.log ((2^m : ℝ) / 3^K) ≤ 2^m/3^K − 1 = D/3^K ≤ 15/n`,
   so `(n : ℝ) ≤ 15 * K^436 / rhinLiteSepC`.
   Lower: targets 1, 3, 5 give `(2:ℝ)^K ≤ (n+1)^(geomS r) ≤ (n+1)^(geomS 4)` (geomS_mono, n+1 ≥ 1), so
   `K * Real.log 2 ≤ geomS 4 * Real.log (n+1) ≤ 9.14 * Real.log (n+1)`.
   Numerics (all in ℝ, with `Real.log_two_gt_d9`, `Real.log_two_lt_d9`; bound
   `Real.log (396/5) ≤ 6 * Real.log 2 + Real.log (1.2375) ≤ 6 * 0.6932 + 0.2375` via
   `Real.log_le_sub_one_of_pos`; `Real.log 6 ≤ Real.log 2 + Real.log 3`, `Real.log 3 ≤ Real.log 2 + 0.5`):
   `Real.log (1 / rhinLiteSepC) ≤ 27203`.  Then from the lower bound
   `Real.log (n+1) ≥ K * 0.6931 / 9.14 ≥ 0.07583 K`, and from the upper bound
   `Real.log n ≤ Real.log 15 + 436 * Real.log K + 27203`.  Use the concavity step
   `Real.log K ≤ Real.log 492276 + (K − 492276) / 492276` (from `Real.log_le_sub_one_of_pos` applied
   to `K / 492276`), and `Real.log 492276 ≤ 13.11`, `Real.log 15 ≤ 2.71`, to get
   `Real.log n ≤ 5716 + 2.71 + 27203 + 0.000886 (K − 492276) < 0.07583 K ≤ Real.log (n+1)` for
   every `K ≥ 492276` — but `Real.log n < Real.log (n+1)` is not a contradiction by itself, so
   compare the upper bound against `Real.log (n+1) ≤ Real.log (2n) = Real.log 2 + Real.log n`:
   `0.07583 K ≤ Real.log (n+1) ≤ 0.6932 + Real.log n ≤ 0.6932 + 32922 + 0.000886 (K − 492276)`,
   i.e. `0.0749 K ≤ 32487`, false for `K ≥ 492276` (LHS ≥ 36871).  `nlinarith`/`linarith` with these
   explicit real facts closes it.

Build the module and the root, run `#print axioms descends_of_oddRunCount_le_four` (expect the
standard three plus the inherited Rhin-lite `native_decide` certificates and nothing else), commit,
then `box done --green`.  If a frozen statement is false, report the mathematical counterexample;
do not weaken it - except target 2, whose hypothesis is stated above.  This gives
`StoppingCorrect` on all first crossings with at most four odd runs, modulo the explicit
verification hypothesis.  It does NOT prove CST.

## Attended operator override: 2026-09-19 (Fable) - two-run stopping-time helper

Trevor authorized this run ("proceed per your best judgement", 2026-09-19 evening); Opus-low
helper, **at most two laps**.  Create `CollatzMoonshot/FrontA/FirstCrossingTwoRun.lean`,
importing `CollatzMoonshot.FrontA.FirstCrossingOneRun` (which already imports FirstCrossing and
OneCircuit).  Do not change any existing theorem or definition.  Your only files are this new
module, its line in `CollatzMoonshot.lean` (after the OneRun import), and a short dated handoff
`HANDOFF-2026-09-19-two-run.md`.  Do not edit DIRECTION or experiments.  No successor task.

**Commit a compiling skeleton with named `sorry` leaves first**, then fill them; a lap that has
committed nothing when it dies loses the hour.  Before any build, `.lake/build` is already warm
(host built `220e2f1`); do not `lake exe cache get`.

Namespace `CollatzMoonshot.FrontA.FirstCrossing`, `open CollatzMoonshot CollatzMoonshot.FrontB`.
Reuse from `FirstCrossingOneRun.lean`: `traceWord_add`, `ones_replicate_false'`,
`overshoot_identity`, `two_pow_le_gap`; from `FirstCrossing.lean`: `At`, `numerator_bound`,
`small_start_of_not_descending`, `prefix_supercritical_trace`, `take_traceWord`; from
`RhinLiteSep.lean`: `sep_two_three` (3^(3k) ≤ (2^m − 3^k)^3 · 2^k for 6 ≤ k, 3^k < 2^m < 2·3^k)
and `sep_strong_492276` (3^k ≤ (2^m − 3^k)·2^25 for 0 < k < 492276, 3^k < 2^m).

Freeze these targets exactly:

1. `def CSTVerified : Prop := ∀ n m, 2 ≤ n → n ≤ 28 * 10 ^ 18 → At n m → tstep^[m] n < n`
   A `def` hypothesis in the style of `SteinerOneCircuit`, NOT an axiom.  Provenance for the
   docstring: Rozier–Terracol, arXiv 2502.00948v5, Corollary 5.4 (t(n) = τ(n) for 2 ≤ n ≤ 2.8·10^19).

2. `theorem ones_ge_of_survives (hv : CSTVerified) {n m : ℕ} (hn : 2 ≤ n) (h : At n m)
       (hsurv : n ≤ tstep^[m] n) : 492276 ≤ ones (traceWord n m)`
   Route: put a := ones, D := 2^m − 3^a.  If a = 0 then `numer = 0` (`numer_eq_zero_of_ones_eq_zero`),
   the iterate identity gives `2^m * y = n` with m ≥ 1, so y < n, contradiction.  For 1 ≤ a < 492276,
   `sep_strong_492276` gives `3^a ≤ D * 2^25`; `small_start_of_not_descending` gives
   `3 * D * n ≤ a * 3^a ≤ a * D * 2^25`, so `3 n ≤ a * 2^25 < 492276 * 2^25`, hence
   `n ≤ 28 * 10^18`, and `hv` yields descent, contradiction.

3. `def twoRunWord (k₁ l₁ k₂ l₂ : ℕ) : List Bool :=
      List.replicate k₁ true ++ List.replicate l₁ false ++ List.replicate k₂ true ++ List.replicate l₂ false`

4. `theorem iterate_ge_of_prefix_supercritical {n j : ℕ}
       (hp : 2 ^ j ≤ 3 ^ ones (traceWord n j)) : n ≤ tstep^[j] n`
   From the iterate identity: `2^j * y = 3^a n + N ≥ 2^j n`.

5. `theorem descends_of_twoRun (hv : CSTVerified) {n m k₁ l₁ k₂ l₂ : ℕ} (hn : 2 ≤ n)
       (h : At n m) (hw : traceWord n m = twoRunWord k₁ l₁ k₂ l₂) : tstep^[m] n < n`

Proof route for 5 (every step is exact ℕ arithmetic; K := k₁ + k₂, L := l₁ + l₂, m = K + L):
  - Degenerate shapes: if k₂ = 0 or l₁ = 0 the word is a one-run word (`oneCircuitWord`), use
    `descends_of_oneRun` (for l₁ = 0 the word is `1^(k₁+k₂) 0^l₂`; rewrite with `List.replicate_add`).
    If k₁ = 0 the word starts even: as in `descends_of_oneRun`'s a = 0 branch the first crossing is
    m = 1 and n descends; or argue `At n m` with first letter false forces m = 1 (prefix j = 1 needs
    2 ≤ 3^0).  l₂ ≥ 1 because the last letter of a crossing word is false (3^K < 2^m fails otherwise).
  - Main case k₁, l₁, k₂, l₂ ≥ 1.  By contradiction assume `n ≤ y`, y := tstep^[m] n.
    Split the trace twice with `traceWord_add` and `List.append_inj` (as in OneRun):
      prefix 1^k₁ from n; suffix 0^l₁ from x₀' := tstep^[k₁] n; then 1^k₂ from x₁ := tstep^[k₁+l₁] n;
      then 0^l₂ from tstep^[k₂] x₁.
    Exact chain facts, each by the OneRun prefix/suffix pattern:
      (c1) n + 1 = 2^k₁ * a₀      (c2) tstep^[k₁] n + 1 = 3^k₁ * a₀
      (c3) 2^l₁ * x₁ = tstep^[k₁] n
      (c4) x₁ + 1 = 2^k₂ * a₁     (c5) tstep^[k₂] x₁ + 1 = 3^k₂ * a₁
      (c6) 2^l₂ * y = tstep^[k₂] x₁
    Also x₁ ≥ n by target 4 at j = k₁ + l₁ (a proper prefix, so `h.2.1` supplies the hypothesis),
    and K ≥ 492276 by target 2 (`ones (twoRunWord …) = K`).
    Upper bound on n: multiply (c2)(c3) and (c5)(c6):
      3^K * (n+1) * (x₁+1) = 2^K * (2^l₁ x₁ + 1) * (2^l₂ y + 1) ≥ 2^(K+L) * x₁ * y ≥ 2^(K+L) * x₁ * n.
    Multiply by n and use n * (x₁ + 1) ≤ (n + 1) * x₁ (this is x₁ ≥ n), cancel x₁ > 0:
      2^(K+L) * n^2 ≤ 3^K * (n+1)^2,  so  D * n^2 ≤ 3^K * (2n+1)  and  D * n < 3 * 3^K.
    `sep_two_three` at k = K, m = K + L (hypotheses: K ≥ 6, 3^K < 2^m from `h.2.2`, and
    2^m < 2 * 3^K from the proper prefix of length m − 1, which has K ones: 2^(m-1) ≤ 3^K, strict
    because 3^K is odd) gives 3^(3K) ≤ D^3 * 2^K, hence  n^3 < 27 * 2^K  and  (n+1)^3 < 2^(K+8).
    Lower bounds: (c1) gives 2^k₁ ≤ n + 1, so 2^(3k₁) < 2^(K+8), i.e. 3k₁ < K + 8.
    From (c3) with l₁ ≥ 1, x₁ ≤ tstep^[k₁] n / 2 < 3^k₁ * a₀, so with (c4): 2^k₂ ≤ x₁ + 1 ≤ 3^k₁ * a₀,
    and multiplying by 2^k₁ with (c1): 2^K ≤ 3^k₁ * (n + 1).  Cube: 2^(3K) ≤ 3^(3k₁) * (n+1)^3
    < 2^(5k₁) * 2^(K+8) (since 27 < 32), so 3K < 5k₁ + K + 8, i.e. 2K < 5k₁ + 8.
    Combine 3k₁ < K + 8 and 2K < 5k₁ + 8: 6K < 15k₁ + 24 < 5K + 64, so K < 64, contradicting K ≥ 492276.
    Exponent comparisons use `Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)` after `← pow_mul`,
    `← pow_add`; `Nat.pow_lt_pow_left` for cubing; `omega` on the final linear facts.

Build the module and the root, run `#print axioms descends_of_twoRun` (expect the standard three
plus the Rhin-lite `native_decide` certificates, nothing else), commit, then `box done --green`.
If a frozen statement is false, report the mathematical counterexample; do not weaken it.
This gives the two-run instance of `StoppingCorrect` modulo the explicit verification hypothesis.
It does NOT prove CST.

## Attended session note: 2026-09-19 (Fable) - one-run stopping-time correctness LANDED

Commit `220e2f1`, host build green.  `FrontA/FirstCrossingOneRun.lean` proves the overshoot
identity at a first crossing (`D·n + 2^m·(y−n) = numer`, `3(y−n) < a`), the one-run instance of
`StoppingCorrect` (`stoppingCorrect_oneRun`), and discharges `SteinerOneCircuit` from
`sep_two_three`.  `experiments/parity_reconstruction.py near-cycle N` is the exact control.
Research rationale and the Simons–de Weger transfer route: personal KB leaf
`collatz-near-cycle-few-runs-2026-09-19.md`.  No successor lap is authorized by this note;
`StoppingCorrect` and `CrossingExists` remain open.

## Attended operator override: 2026-09-19 - residue-swap helper COMPLETE

Completed at `2ab0926`, handoff checkpoint `a946b7c`.  All three frozen targets
below are proved with their original statements.  The parent checked the source
and added exhaustive exact controls to the existing parity-reconstruction probe.
No successor lap is authorized here; do not fall through to older overrides.
StoppingCorrect and CrossingExists remain open.  Follow-up analysis is recorded
in the KB leaf `moonshot-resonance-residue-swaps-2026-09-19.md`.

Original bounded directive, retained for provenance:

Trevor requested continuation and permits Opus-low helpers.  One bounded lap only.
Create `CollatzMoonshot/FrontA/FirstCrossingSwaps.lean`, importing FirstCrossing.
Do not change any existing theorem or definition.  Parent owns the experiment script;
your only files are this new module, its root import, and your short dated handoff.
Do not edit DIRECTION or experiments.  No successor task and no Aristotle.

Freeze these mathematical targets (namespace FirstCrossing, open FrontB):

1. `numer_adjacent_swap (u w : List Bool)`:
   `numer (u ++ [false,true] ++ w) = numer (u ++ [true,false] ++ w) +
      2 ^ u.length * 3 ^ ones w`.
2. `residue_adjacent_swap {x y m : Nat} (u w : List Bool)` with
   `hx : traceWord x m = u ++ [true,false] ++ w` and
   `hy : traceWord y m = u ++ [false,true] ++ w`:
   `3 ^ (ones u + 1) * y + 2 ^ u.length ≡
      3 ^ (ones u + 1) * x [MOD 2 ^ m]`.
   This is suffix-independent, with no first-crossing assumption needed.
3. Define `NumeratorAntitoneResidue : Prop` as
   `∀ x y m : Nat, 2 ≤ x → 2 ≤ y → x < 2^m → y < 2^m →
       At x m → At y m →
       numer (traceWord x m) ≤ numer (traceWord y m) → y ≤ x`.
   Prove `numeratorAntitoneResidue_false : ¬ NumeratorAntitoneResidue`.
   Hand-checked anchor: x=95,y=175,m=8, words 11111000 and 11110100,
   numerators 211 and 227; both first-crossing, but 175>95.

Proof route: induct on u for the numerator swap; both suffixes have equal odd counts.
Subtract the two affine iterate identities modulo 2^m; use the numerator swap,
factor 3^(ones w), and cancel this unit.  Reuse the Nat.ModEq cancellation pattern
in ParityReconstruction.traceWord_eq_imp_modEq.  The remaining expression is exactly
the frozen residue identity, with the displayed orientation (plus 2^len u on y).

Build, inspect dependencies of the three named results, commit, then `box done --green`.
If a frozen target fails, report the mathematical counterexample; do not weaken it.
This gives local residue transport and refutes monotonicity.  It does NOT prove CST.

## Attended operator override: 2026-09-18 - first-crossing helper COMPLETE

Completed at `94076e2`, handoff checkpoint `792fee0`, with a successful host build.
`FirstCrossingCycles.noNontrivialCycle_of_stoppingCorrect` has the frozen target.
No successor lap is authorized by this directive; do not fall through to an old
dated override below.  The two open inputs remain `StoppingCorrect` and `CrossingExists`.
The parent also proved the first-crossing numerator bound in `FirstCrossing.lean`
and added exact first-crossing geometry/null-baseline diagnostics to
`experiments/parity_reconstruction.py first-crossing 501`.
Research rationale and next gate: the 2026-09-18 headline blueprint and
`moonshot-first-crossing-carry-audit-2026-09-18.md` in the personal KB project leaves.

Original bounded task, preserved for provenance:

Trevor authorized Opus-low helpers in this session.  This is a bounded formalization task,
not permission to attack CST or the Collatz conjecture.  Parent Ren owns the analytic work
outside this repository and will not edit this tree during the helper lap.

**Frozen inputs:** `FrontA.FirstCrossing.At`, `StoppingCorrect`, `CrossingExists` and all
statements in `FrontA/FirstCrossing.lean`.  Do not change their definitions or statements.

**Single target**, in new `CollatzMoonshot/FrontA/FirstCrossingCycles.lean`:

```lean
namespace CollatzMoonshot.FrontA.FirstCrossing
theorem noNontrivialCycle_of_stoppingCorrect
    (h : StoppingCorrect) : CollatzMoonshot.NoNontrivialCycle := by
  -- prove; do not weaken the statement
end CollatzMoonshot.FrontA.FirstCrossing
```

Proof route: a nontrivial cycle has an orbit minimum greater than 2 in shortcut
coordinates.  Its full period is subcritical by the affine identity and positive numerator.
`exists_first_crossing` supplies a first crossing there; `h` gives a descent below
the minimum, contradiction.  Reuse the existing cycle/minimum and map-dictionary lemmas.

Scope: the new module, its root import, and a short dated handoff.  Do not modify other
research modules, old open nodes, citation axioms, or this override.  If the proof exposes a
missing hypothesis, explain it rather than changing the target.  A finite counterexample
would also settle this task, but no empirical check substitutes for the general implication.

Build and check the named theorem's dependencies, commit the completed proof, then
`box done --green`.  One lap only; do not select a successor.  Report the mathematical
implication and any genuine blocker, not a sorry-count metric.

## Attended operator override: 2026-09-16 00:25 EDT — NODE 4, the Eliahou bound at OUR frontier (ACTIVE for this run only; nodes 1–3 DONE at `073b0d2`, host-verified, pushed)

Operator: Ren, unattended overnight run authorized by Trevor 2026-09-15.  Engine: Opus/low.
Branch `main`.  Same lane (formalizing a known method at a new parameter; no new mechanism).
Hard stop: host kills laps at 05:25 EDT - skeleton with named `sorry` leaves first.  Reconcile
with `git log` and `HANDOFF-2026-09-16-eliahou-axiom-discharged.md` before acting.

🎯 **Node 4.**  Node 3's `FrontB.Eliahou` machinery, re-run with the Farey pair that straddles the
interval `(log₂3, log₂(3 + 2^{−68}))` instead of the 1993 pair.  Host computation
(`mpmath`, 60 digits, Stern–Brocot walk, 2026-09-16 00:20):

```
c₁ = 103768467013 / 65470613321  <  log₂ 3  <  e/a  <  log₂(3 + 2^{−68})  <  c₂ = 10439860591 / 6586818670
65470613321·10439860591 − 103768467013·6586818670 = 1        (Farey neighbours)
q₁ + q₂ = 72057431991 ;  the least-denominator fraction inside is 114208327604 / 72057431991
log₂3 − c₁ ≈ 1.02·10⁻²² ;  c₂ − log₂(3+2^{−68}) ≈ 5.88·10⁻²² ;  interval width ≈ 1.63·10⁻²¹
72057431991 · log₂3 = 114208327603.99999999999205…  (so e ≥ 114208327604 once a ≥ 72057431991)
```

**Target theorems** (new module `CollatzMoonshot/FrontB/EliahouFrontier.lean`, importing
`FrontB.Eliahou`; leave `Assumed/Cycles.lean` alone except to mention the result in its docstring):

```
theorem odd_members_ge_of_two_pow_68 : ∀ n m, 1 ≤ n → 0 < m → step^[m] n = n →
    (n = 1 ∨ n = 2 ∨ n = 4) ∨ 72057431991 ≤ ((Finset.range m).filter (fun i => step^[i] n % 2 = 1)).card
theorem min_cycle_length_two_pow_68 : ∀ n m, 1 ≤ n → 0 < m → step^[m] n = n →
    (n = 1 ∨ n = 2 ∨ n = 4) ∨ 186265759595 ≤ m          -- 114208327604 + 72057431991
```

Ledger must be exactly `[propext, Classical.choice, Quot.sound,
collatz_verified_up_to_two_pow_68]` - **no big-power `native_decide`**: the node-3 certificates
`2^p < 3^q` are infeasible here (`q ≈ 6.5·10¹⁰` means ~10¹¹-bit numbers).  Replace them by
**certified real bounds on `log 2` and `log 3`** to ~26 significant digits:

- `Real.abs_log_sub_add_sum_range_le (h : |x| < 1) (n) : |∑_{i<n} x^{i+1}/(i+1) + log(1−x)| ≤ |x|^{n+1}/(1−|x|)`
  (mathlib, `Analysis/SpecialFunctions/Log/Deriv.lean:217`).  `log 2 = −log(1 − 1/2)` with `n = 90`
  (error `≤ 2^{−90}·2 < 10⁻²⁶`); `log 3 = log 2 + log(3/2)`, `log(3/2) = −log(1 − 1/3)` with `n = 58`
  (error `≤ 3^{−59}·(3/2) < 10⁻²⁷`).  Evaluate the finite rational sums with `norm_num`
  (rationals with ~30-digit denominators; if `norm_num` is slow, `decide`-free `Rat` arithmetic
  via `norm_num [Finset.sum_range_succ]` in chunks, or state the partial sum as a literal
  `p/q` and prove `∑ = p/q` by `norm_num`).  Reference values: `ln 2 =
  0.69314718055994530941723212145817657`, `ln 3 = 1.0986122886681096913952452369225257`.
- From the bounds: `c₁ < log₂3` ⇔ `103768467013 · log 2 < 65470613321 · log 3` (margin
  `≈ 1.0·10⁻²² · 65470613321 · log 2 ≈ 4.6·10⁻¹²` in absolute terms - comfortable), and
  `log₂(3 + 2^{−68}) < c₂` ⇔ `6586818670 · (log 3 + log(1 + 1/(3·2^{68}))) < 10439860591 · log 2`,
  using `log(1+x) ≤ x` (`Real.log_le_sub_one_of_pos`) and `1/(3·2^{68}) < 10⁻²⁰`.
- The cycle side is already abstract in `FrontB.Eliahou`: `3^a < 2^e` gives `a log 3 < e log 2`
  (`Real.log_lt_log` after casting), and `2^e · x^a ≤ (3x+1)^a` with `2^{68} < x` gives
  `e log 2 ≤ a log(3 + 1/x) ≤ a log(3 + 2^{−68})`.  So `c₁ < e/a < c₂` in `ℝ`, and
  `farey_denominator_bound` (node 3) gives `a ≥ 72057431991`; then `e > a·c₁ ≥ 72057431991·c₁`,
  which exceeds `114208327603` (check: `72057431991 · 103768467013 / 65470613321 =
  114208327603.9999999999847…` - the margin is `1.5·10⁻¹¹`, so prove `114208327603 < a·c₁`
  as an exact rational inequality with `norm_num`, never with floats).  Reuse node 3's
  `step_prod_identity`, `three_pow_lt_two_pow`, `two_pow_mul_pow_le`, `two_pow_68_lt_orbit`.
- Docstring: this is Eliahou's 1993 method at the repo's own `2^{68}` frontier; it is **not**
  Hercher 2023 Cor. 29 (`1.375·10¹¹` odd members needs his residue-class computation on top of
  the continued fraction - the pure Farey step at `X₀ = 2075·2^{60}` gives the same `72057431991`,
  host-checked), so `hercher_odd_members_bound` stays a citation axiom.  Cite Eliahou §3.
- `(7,8)`-style control: none needed; instead a kernel/`norm_num` check that the two Farey
  fractions really are neighbours (`b·c − a·d = 1`).

**Rules.**  One writer per file; no new axioms; no experiments, no push; no board-row work.
Review laps rank the open leaves of this node only.  If the 26-digit series bounds resist
`norm_num` within one lap, commit the skeleton with the two log bounds as named `sorry` leaves
(`log_two_bounds_26`, `log_three_bounds_26`) and everything else closed, and say so.

## Attended operator override: 2026-09-16 00:10 EDT — NODE 3, discharge the Eliahou citation axiom (ACTIVE for this run only; Nodes 1–2 of the 23:58 override are DONE at `2a1478b`/`8510836`, host-verified trust triple, pushed)

Operator: Ren, unattended overnight run authorized by Trevor 2026-09-15.  Engine: Opus/low.
Branch `main`.  Same lane as the 23:58 override (formalizing a known result; no new
mechanism, nothing toward `U.Finite`); the "awaiting a new mechanism" pause otherwise stands.
Hard stop: the host kills every lap by 05:25 EDT - **commit a compiling skeleton with named
`sorry` leaves first**, then close leaves; `box done --green` is the exit while a leaf is open,
`box done` once `src/` is sorry-free again.  Reconcile with `git log` and the newest
`HANDOFF-*.md` before acting.

🎯 **Node 3 - turn `Assumed.eliahou_min_cycle_length` (`CollatzMoonshot/Assumed/Cycles.lean`)
from an `axiom` into a `theorem` with the SAME statement**, standing only on
`collatz_verified_up_to_two_pow_68` (already consumed by
`Conditional.two_pow_68_lt_of_onCycle_nontrivial`) plus the trust triple and, if needed, a
`native_decide` certificate for one big power comparison (disclose it in the docstring; the
Rhin-lite allow-list pattern in `scripts/check-fixed-block-bound.sh` is the model).

**Reference implementation, read-only:** `papers/eliahou-collatz-bounds-tangentstorm/`
(untracked; see its `PROVENANCE.md` - no license, so read for structure and lemma names and
write our own proofs; cite it in the module docstring as "structure follows tangentstorm's
Lean 4.28 formalization, edited by Aristotle").  Its headline `eliahou_bound {L} (c :
CollatzCycle L) (hmin : 2^40 < c.minElem) (hk : 0 < c.numOdd) : 17087915 ≤ L` is stated for the
compressed map `collatzComp` = our `tstep`, over a `Fin L`-indexed cycle structure.  Its
`Sandwich.lean` (ratio bounds) is 113 lines, `ProductFormula.lean` 133, `ContinuedFractions.lean`
211 (Farey pair bound + certified convergent facts `3^10781274 < 2^17087915` via
`native_decide`), `Defs.lean` 126.

**Route, in order (new module `CollatzMoonshot/FrontB/Eliahou.lean`; import it from the
root; keep `Assumed/Cycles.lean`'s docstring, change `axiom` → `theorem … := Eliahou.…`):**
1. **Product identity on a `tstep`-cycle** - we already have
   `FrontA.TrunkBound.tstep_iterate_prod_identity : 2^m·x_m·∏_I 3x_i = 3^a·n·∏_I(3x_i+1)`;
   with `x_m = n` and `n > 0` it gives `2^m ∏_I 3x_i = 3^a ∏_I (3x_i+1)`, i.e. Eliahou's
   `∏_{odd} (3 + 1/x_i) = 2^m`.  No `Fin L` cycle structure needed: index by
   `oddSteps n m` exactly as `TrunkBound`/`HarmonicMean` do.
2. **Sandwich** (Eliahou Thm 2.1): with `x_min = segMin n m` (all cycle elements `≥ x_min`)
   `2^m ≤ (3 + 1/x_min)^a` (this is `min_term_inequality_le` at `x = x_min`, already proved for
   `n ≤ x_m`), and `3^a < 2^m` (strict, from the product identity since every factor
   `3x_i+1 > 3x_i`; equality is impossible for `a ≥ 1`).  So `a·log₂3 < m < a·log₂(3 + 1/x_min)`.
3. **Cycle elements are big**: for a `step`-cycle `n` not in `{1,2,4}`, EVERY element exceeds
   `2^68` - `Conditional.two_pow_68_lt_of_onCycle_nontrivial` gives it for `n`; apply it to each
   element (each is on the same cycle).  Then translate `step`-cycle ↔ `tstep`-cycle: a
   `step`-period `m_s` with `k₁` odd steps is a `tstep`-period `L = m_s − k₁` with the same odd
   elements (each odd `step` is followed by a halving); prove the relation you need
   (`step^[m_s] n = n → ∃ L a, tstep^[L] n = n ∧ a = ones (traceWord n L) ∧ m_s = L + a`).
   `Basic.lean`/`Conjecture.lean` may already have pieces - grep `tstep`, `OnCycle` first.
4. **The Farey/convergent step** (Eliahou §3, the reference's `ContinuedFractions.lean`):
   any fraction `L/a` with `log₂3 < L/a < log₂(3 + 2^{−40})` has `L ≥ 17087915` (and then
   `a ≥ 10781274`, since `a > L/log₂(3+1/x_min)`; hand-checked 2026-09-16 with mpmath at 40
   digits: `17087915/10781274` lies in the interval, `17087915/log₂(3+2^{−40}) − 10781274 ≈
   −3·10⁻⁶` (so with a `2^{40}` cutoff the integer bound holds only because `a` is an integer
   exceeding `10781273.999997`), while `17087915/log₂(3+2^{−68}) − 10781274 ≈ +1.1·10⁻⁸ > 0`.
   **Use the `2^{68}` cutoff we actually have** (`x_min > 2^{68}`), and certify the convergent
   facts with exact integer arithmetic, never floats).
   Ingredients: two convergent facts as big-integer inequalities (`3^{10781274} < 2^{17087915}`,
   and the upper one with `(3·2^{40}+1)^{a}` vs `2^{L}·2^{40a}`), `native_decide` allowed;
   the Farey-pair lemma (`b·c − a·d = 1` ⇒ any `p/q` strictly between `a/b` and `c/d` has
   `q ≥ b + d`) - elementary, prove in the kernel.
5. **Assemble**: `eliahou_min_cycle_length` as a theorem: `m_s = L + a ≥ 17087915 + 10781274 =
   27869189`.  Then `#print axioms` must show `[propext, Classical.choice, Quot.sound,
   collatz_verified_up_to_two_pow_68]` plus at most the named `native_decide` certificate(s).
   Record the exact axiom list in the docstring and the handoff.  Downstream users of the old
   axiom (`grep -rn eliahou_min_cycle_length`) must still build unchanged.

**Rules.**  One writer per file; no edits to `Assumed/Computation.lean`; no new axioms; no
experiments, no Aristotle, no push (host pushes); no work on any board row.  A review lap ranks
the open leaves of this node only.  If step 4's convergent facts do not certify within one lap
(the powers have ~10⁷ bits; `native_decide` on `Nat.pow` with `Nat.blt` should be seconds via
GMP, but measure), fall back to leaving step 4 as ONE named `sorry` leaf `farey_convergent_bound`
with everything else closed, and say so.

## Attended operator override: 2026-09-15 23:58 EDT — operator-assigned BOUNDED FORMALIZATION node (ACTIVE for this run only; the "awaiting a new mechanism" pause below otherwise stands)

Operator: Ren, unattended overnight run authorized by Trevor 2026-09-15.  Engine: Opus/low.
Branch `main`.  This is the Lean "formalizing known results" lane (rank 10 of the board below),
assigned separately as the reflection permits; it claims **no new mechanism** and nothing here is
a step toward `U.Finite`.  Hard stop: the host kills every lap by 05:25 EDT 2026-09-16 - **commit a
compiling skeleton with named `sorry` leaves before every hard step**.  Read this addendum, the
newest `HANDOFF-*.md`, then `git log`; reconcile before acting.  Finish with `box done` (the repo
is sorry-free; keep it so at every commit, or use `box done --green` if a skeleton leaf is open).

🎯 **Node 1 - Front B statement hygiene, as theorems** (`FrontB/Threads.lean`, small).  The
reflection found two labels that are Front B in costume; make the kernel say so:
- `countingGivesFinite_iff_frontB : CountingGivesFinite ↔ FrontB` (forward: a counterexample `v`
  gives the distinct family `wpow v (j+1)`, all integral and nontrivial by `integerCycle_wpow_iff`
  / `isTrivial_wpow_iff`, lengths `(j+1)·|v|` by `length_wpow`, so the set is infinite; backward:
  empty is finite).  Then `not_finitenessIsNotEmptiness : ¬ FinitenessIsNotEmptiness`.
- `ladderCompletes_iff_frontB : LadderCompletes ↔ FrontB` (forward: take `C := circuits` of the
  primitive root from `exists_primitive_root`; backward: FrontB makes every integral cycle trivial).
- Then add the honest **primitive-population** predicate `PrimitiveCountingGivesFinite :=
  {v | Primitive v ∧ IntegerCycle v ∧ ¬IsTrivial v}.Finite` with a docstring saying it is the
  population Simons–de Weger/Hercher count, and do NOT claim any implication from it to FrontB.
  Fix the two docstrings the reflection called false.  `#print axioms` on each.

🎯 **Node 2 - Rozier–Terracol Theorem 4.2, the all-terms harmonic-mean half**
(`FrontA/TrunkBound.lean` has the easy min-term half; put this in a new
`FrontA/HarmonicMean.lean` importing it).  With `I = oddSteps n m`, `a = |I|`,
`x_i = tstep^[i] n`, `H := ∑_{i∈I} 1/x_i` (so the harmonic mean is `h = a/H`):
- `prod_le_pow_harmonic : ∏_{i∈I} (3x_i+1)/(3x_i) ≤ (1 + H/(3a))^a` for `a ≥ 1` - AM–GM with
  equal weights `1/a` on the factors `1 + 1/(3x_i)` (mathlib
  `Real.geom_mean_le_arith_mean_weighted`, or `Real.inner_le_nnorm_mul_nnorm`-free routes via
  `Real.add_pow_le_pow_mul_pow_of_sq_le_sq` are NOT needed; the weighted AM–GM is the tool).
- `harmonic_mean_inequality : n < x_m → (2:ℝ)^m < (3 + H/a)^a`, from
  `tstep_iterate_prod_identity` exactly as `min_term_inequality` was derived, with the product
  bound above in place of the min-term bound.  This is RT 4.2's `log 2/log(3+1/h) ≤ a/m`.
- Corollary under `3^a < 2^m` (`AcyclicParadoxical`), with `Λ = m log 2 − a log 3 > 0` and
  `h = a/H`: `2^(m/a) < 3 + H/a`, and `2^(m/a) − 3 = 3(exp(Λ/a) − 1) ≥ 3Λ/a`, so
  `harmonicMean_lt_of_subcritical : h < a/(3Λ)` - the same bound `TrunkBound` proves for `x_min`,
  now for the harmonic mean of ALL odd terms (`x_min ≤ h` is the trivial comparison; prove it).
  Add the `(7,8)` control (`H = 1/7+1/11+1/17+1/13+1/5`, `a = 5`, `m = 8`) as `TrunkBound` did.
- Docstring: "hard half of RT Theorem 4.2 (harmonic-mean form); no novelty claimed."

**Rules.**  Trust triple only (`[propext, Classical.choice, Quot.sound]`); the Rhin-lite natives
may be inherited only by a corollary that says so in its docstring.  No new experiments, no
Aristotle, no push (host pushes), no changes to `DIRECTION.md` below this addendum, no work on
any board row.  When both nodes are green and audited (`bash scripts/check-fixed-block-bound.sh`
still FORMALIZE-TIER GREEN), write the handoff and `box done`.  A review lap ranks the open leaves
of these two nodes only.

## CURRENT DIRECTIVE — awaiting a new idea; no execution lap selected

Set by the **2026-09-13 whole-repository reflection**, reconciled through
`6a33554`, from baseline `5a54acc`. This supersedes all older assignments and
rankings in handoffs, route maps, source docstrings, and PENDING_WORK history.

*History note (2026-09-13, operator-assigned bounded node):* `FrontA/TrunkBound.lean` formalizes the easy min-term half of Rozier–Terracol Theorem 4.2 (every paradoxical segment dips below `a/(3Λ)`; Rhin-lite corollary `x_min < a^437/(3c)+a`); the awaiting-a-new-mechanism pause otherwise stands. See `HANDOFF-2026-09-13-trunk-bound.md`.

**Nothing currently on Front A or Front B clears the bar of probability times
magnitude of NEW mathematics for a bounded objective.** Do not launch another
proof lap from the deferred list. This is a judgment about the presently
specified mechanisms, not an impossibility theorem or a claim that Collatz is
unprovable. The completed campaign remains green and useful.

The operator explicitly requested reflection and documentation only. That
instruction overrides reflection.md's generic instruction to implement a proof
step afterward. No Lean proof, new experiment, or Aristotle job is part of this
lap. Its deliverable is this reconciled decision and the verification/handoff.

## What the completed laps actually bought

The git range contains 17 commits after the baseline, including host experiment
commits and direction reviews; it is not 17 independent proof advances.
`5a54acc` itself is dated September 8 and closes the front-normalized rung-3
classification at length 8. It is the settled baseline for this review.

| Commits | Reconciled result | Limit on what follows |
|---|---|---|
| `f8fa4a5`, `cf8d748`, `56304ac`, `5ea1b38`, `9b5dc54` | Rung, word-model, and orbit censuses; recorded length sweep 2..80 has hits at 8,27,46,65,73. | Finite data; a cluster on the trajectory of 27 is not a universal theorem. |
| `26c49b9`, `c3aba74` | Campaign A2: exact trunk slack/criterion, 2305/2313 obstruction, and null-model audit. | Prefix remainder cannot be dropped. The proved model law is not a distribution law for admitted integer traces. |
| `529ccef`, `4a12a68` | Arbitrary-block cascade, rational envelope, and explicit fixed-run length bound. | Complete for each fixed b, not uniform in b. “Campaign B” here is work on Front A, not a proof of the cycle front. |
| `9ae73a3`, `972c772` | Further fixed four-block empty censuses and corrected census commentary (minimum observed run ratio 9/46; first populated rung after 3 is 7). | No global run-density law; no new theorem from editing the summary. |
| `5bdea84`, `882c787` | Rational short-run positivity question selected, then refuted by a primitive Q=2 family at unbounded length. | Rational positivity does not imply integer admission. |
| `bc4158e`, `3a3e838` | Six-letter admission question selected, then refuted by a padded primitive Q=2 family. | The certified filter is exactly P_6; full admission remains separate. |
| `e6cb096`, `6a33554` | Odd-start strict cycle-witness edge selected, then proved; unrestricted pair finiteness now implies Collatz. | New formal dependency information, not a proof of either finiteness hypothesis. |

The fixed-b theorem is

```
odd n ∧ AcyclicParadoxical n m ∧ oddRunCount(traceWord n m) ≤ b
  → m < 4*((2^b−1)*(b+53342))^2+b.
```

It includes a terminal odd run without adding a trajectory step. The rational
small-vertex argument and repeated squaring produce the factor `2^b−1`; the
existing polynomial 2/3 separation closes the feedback. This is a meaningful
extension to strict segments, but its mechanism is the Simons–de Weger pincer
on a new object. Their fixed-circuit finiteness combines an elementary upper
bound with logarithmic-form separation; its rate deteriorates with circuit
count. It is not a source of uniform compression. Source availability is
resolved. [Simons–de Weger v1.44, Theorem 3, Lemmas 7/12, §8](https://deweger.net/papers/%5B35a%5DSidW-3n%2B1-v1.44%5B2010%5D.pdf).

Do not confuse the benefits: rung classification and fixed-b formalization
advance restricted structure; the obstruction families eliminate relaxations;
cycle repetition clarifies the graph. None supplies the remaining uniform
integer-trajectory input. Another known specialization does not inherit novelty
from having a fresh theorem name.

## Exact statement and dependency graph

`Conjecture` means every positive integer reaches 1 under the standard map
`step`; `NoDivergentOrbit` excludes unbounded positive orbits;
`NoNontrivialCycle` permits only 1,2,4 on positive standard cycles.
Their conjunction is equivalent to Conjecture by `conjecture_iff_split`.
Paradoxical segments instead use the shortcut map `tstep`.

```
AcyclicParadoxical n m :=
  n>2 ∧ m>0 ∧ 3^ones(traceWord n m)<2^m ∧ n<tstep^[m] n
U := {(n,m) | AcyclicParadoxical n m}
O := {(n,m) ∈ U | n is odd}
```

“Acyclic” means strictly unequal endpoints. Interior repetitions are allowed.
The sets count pairs, not distinct starts, primitive words, first returns, or
segments before first descent. These distinctions are load-bearing.

The default build proves:

- `U.Finite → NoDivergentOrbit`.
- `U.Finite → O.Finite → NoNontrivialCycle`.
- Hence `U.Finite → Conjecture`.
- An odd shortcut periodic member n>2 produces infinitely many lengths in O,
  by repeating its period and appending one odd step. Infinitely many starts
  are neither needed nor claimed.
- `ParityRigidityW1' → NoDivergentOrbit`; also
  `RepeatOrDescendCertificate ↔ NoDivergentOrbit`.
- `NoNontrivialCycle ↔ FrontB` in the integral-word dictionary.

All these displayed edges are trust-base clean. **Still open:** O.Finite,
U.Finite, O.Finite→U.Finite, both unconditional fronts, W1', compression and
the other research predicates. `Conjecture → U.Finite` is not supplied by
this graph. Pointwise termination does not supply a uniform pair bound.

The old “Front A only” reading of paradoxical finiteness is now decisively
wrong: even O.Finite carries cycle exclusion. A uniform bound on odd-start
run count, together with fixed-b finiteness, repackages O.Finite; a uniform
length bound does likewise (finitely many words, each with finitely many
starts below its threshold). Neither is a harmless auxiliary assumption.

## Standing obstruction: full admission is the missing information

For a Boolean word v of length m with a ones, put `N=numer(v)` and
`D=2^m−3^a>0`. Its full realizing residue and least allowed start are

```
r_m = [−N*(3^a)^(-1)] mod 2^m
c_m = min {n ∈ ℕ | n>2 and n≡r_m mod 2^m}.
```

A word admits a strict paradoxical start exactly when `D*c_m<N`. All its
admitting starts are the representatives n>2 in that residue class with
`D*n<N`. Keep the least-above-2 correction when r_m≤2. In contrast, the
rational affine fixed point is `N/D`; positivity of it and of every internal
head does not realize the word as a small integer trajectory. For an actual
integer cycle the endpoint equality instead requires `D*n=N`.

`882c787` certifies `(XY)^k XYY`, X=TF, Y=TTF, with bounded run lengths,
primitivity and all rational head slacks positive, for unbounded k. Its common
six-bit residue is 57, above N/D. `3a3e838` certifies
`(XY)^(2j+12) X Y^17`, j≥0, at lengths 10j+113, with the same positivity and
primitivity and now `D*57<N`. Thus even that necessary entry test admits an
unbounded family. Both are mathematical all-parameter arguments with exact
rational scripts, not new Lean theorems.

Evidence boundary: the checked-in second certificate proves P_6 survival,
not an arbitrary-L theorem. Its full-admission rejection check covers 36
parameters. Prior operator context additionally reports universal full
rejection with canonical starts of about m bits; no corresponding universal
proof artifact was added to this repository. The current operator treats
finite-prefix relaxations as exhausted. **All fixed finite-prefix follow-ups
remain retired**, without relabeling the P_6 certificate as a theorem for every
L. Neither that retirement nor these examples refutes every symbolic proof.

At fixed (m,a,N) the full residue is deterministic. A uniform argument must
therefore consume trajectory-side information: the actual small start and
all its parity/carry compatibility. This can be expressed symbolically, but
cannot be replaced by rational head positivity, a fixed-prefix test, or an
independent random-residue model. A2's exact trunk criterion already shows why
retaining only the minimum and subsequent climb loses decisive information.

## Whole-board ranking: all below the bounded-objective bar

This is an ordinal ranking of present research prospects, **not a work queue**.
“High magnitude” means a new mechanism would matter; it does not make an
unspecified mechanism a bounded task. Historical 40%, 55%, and 70% route odds
are conditional speculation about eventual solutions, not success probabilities
for the next lap. They have no scheduling authority.

| Rank | Candidate | Probability × magnitude of NEW mathematics in a bounded lap | Decision / missing deliverable |
|---|---|---|---|
| 1 | Front A: a new trajectory constraint beyond RT's harmonic-mean condition | Low for an unconditional strengthening × high; high for a faithful port × negligible new mathematics | No proposed extra inequality controls admission or couples the mean to length/start strongly enough. Do not assign the port. |
| 2 | O.Finite → U.Finite | Unassessable without a specified map (treat as low) × substantial graph value | No map with target membership and finite fibers is known here. “Normalize even starts” is not an objective. |
| 3 | Coefficient stopping time (CST), or a genuinely new restricted obstruction to its failure | Low × high; known equivalence/verification ports have high probability but low new content | No fresh restricted class and mechanism are specified. Global CST is an open cycle-excluding conjecture. |
| 4 | Carry/transducer or repeat-or-descend certificate | Very low at present × very high | No state space with a proved sound transition invariant and a surviving descent/recurrence certificate. The interface alone is exactly Front A. |
| 5 | W1' parity rigidity / Furstenberg intertwining | Very low × very high | No arithmetic transfer from a positive integer orbit to the joint ×2,×3 action, nor applicable entropy input. The conditional consumer is already complete. |
| 6 | Tao forward/backward saturation; pointwise harmonic growth and packing | Very low × very high | Need actual high-floor harmonic mass AND control of overlap across moving seeds. Neither follows from the completed subharmonic certificates. |
| 7 | Front B primitive compression, bounded denominator, or a new Knight-type identity class | Very low × high | No transformation preserving integrality/nontriviality while reducing complexity, and no new identity class. Fixed-circuit finiteness does not bound circuit count. |
| 8 | Numerator/residue discrepancy or cycle counting | Very low at the useful error scale × high | No estimate reaching an integer exclusion threshold; mean behavior is not enough. Exact conditioning leaves no randomness. |
| 9 | The 4614 cutoff, U.Finite itself, global start/length/run bounds | No credible bounded attack × very high | These are destination conjectures, not reductions. Increasing a census cannot prove their universal quantifiers. |
| 10 | More fixed rungs, sharper fixed-b constants, cycle transport, standard certificate/axiom ports, converse wiring | Often high × little or no new mathematics | Valuable formalization under a separately requested objective, but below this operator's bar. |

RT Theorem 4.2 says `1−C≤E/n≤((3+1/h)^a−3^a)/2^m`, where h is the
harmonic mean of the actual odd terms, C=3^a/2^m and E=N/2^m.
Its upper bound is a product/AM–GM
estimate. It gives a necessary condition, not control of h as the trajectory
varies. CST is `t(n)=τ(n)` for n≥2, including infinite values; equivalently a
paradoxical segment contains an earlier value below its start. Conjecture 6.1
excludes all paradoxical starts above 4614. Those conjectures must not be
assumed as known constraints. [Rozier–Terracol v5, §§1,4,6](https://arxiv.org/html/2502.00948v5).

For rank 2, even-prefix deletion sends the actual 18@8 witness to 9@7,
which is not subcritical. Reanchoring at a minimum does not repair coefficient
control automatically, and forgetting prefix depth does not prove finite
fibers. A real proposal must specify a map `f:U\E→O` for an explicitly finite
exception set E (possibly empty), prove membership for every input, and bound
or otherwise prove each fiber finite. No such map is supplied by this review.
If proved, this would make O.Finite sufficient for full Collatz through the
existing U edge; it still would not prove O.Finite.

For ranks 4–6, distinguish three inputs that an umbrella “rigidity certificate”
can conceal. Pure 2-adic invariant measures are not constrained by positivity
of the original integer: the existing negative-cycle witness defeats the
unconditioned parity claim. Topological Furstenberg rigidity is already proved
in this repo; it supplies neither the missing arithmetic intertwining nor a
measure entropy theorem. W1' uses standard-map threshold `log 2/log 6`, not
the shortcut threshold `log 2/log 3`. Its expected converse is finite-measure
calibration, still only a pinned target here, not new rigidity. W1 without the
prime is stronger and would also exclude nontrivial positive cycles.

Tao's result concerns orbit minima for logarithmically almost all starts.
A large backward basin entering one fixed seed d has orbitMin≤d and is
eventually Tao-good. The existing `mem_taoGood_of_reachesValue` formalizes the
failure of that amplification argument. A useful replacement needs moving
high floors and a positive logarithmic-density contradiction.
[Tao, Almost all orbits attain almost bounded values](https://arxiv.org/abs/1909.03562).
The exponent-4/5 renewal/stopping pipeline is complete; another exponent below
1 does not provide the harmonic budget. The harmonic obstruction excludes the
specified five-floor, constant-lift certificate scheme; it is not a theorem
against every enriched state space. Escaping that scheme without a proposed
invariant, or merely porting a larger table, is not a bounded new idea.

## Front B statement audit: do not trust obsolete labels

Reading `FrontB/Threads.lean` and `Powers.lean` exposes two residual mismatches.
These are source-grounded mathematical deductions recorded here, **not new
kernel theorems or proof assignments**:

1. `CountingGivesFinite` currently counts **all** nontrivial integral words,
   not primitive cycles. If v is one such word, `wpow v (j+1)` remains integral
   and nontrivial by `integerCycle_wpow_iff` and `isTrivial_wpow_iff`.
   `length_wpow` gives length `(j+1)*v.length`; v is nonempty, so the words
   are distinct. Thus that literal finiteness predicate implies FrontB, whose
   converse makes the set empty. `FinitenessIsNotEmptiness`, currently defined
   as this predicate AND `¬FrontB`, is consequently impossible. The comment
   that this is a weaker counting conclusion is false for the written type.
   Finiteness without emptiness is the appropriate warning for **primitive
   cycles** (or cycles modulo powers), a different population.
2. `LadderCompletes` universally quantifies over every circuit bound C.
   Set C to the primitive word's own circuit count and use primitive-root
   decomposition to see that it too is equivalent to FrontB. Fixed-C
   finiteness does not give fixed-C exclusion, let alone this whole ladder.

`NaiveCompression` and `NaiveBoundedDen` already have their power-degeneracy
proofs. Primitive `Compression` avoids that particular defect, but its unknown
constant does not finish the front: one still needs to exclude the finitely
many survivors up to that constant. A bound ≤91 closes only through the named
Hercher citation. The earlier route-map assertion that *any* bounded denominator
or circuit count automatically dies against a known lower bound overclaims.
A bound must be explicit and within verified exclusions, or the survivors
must be eliminated independently. No kernel theorem here says otherwise.

Other board entries have not acquired a mechanism overnight: rotation gcd
harvesting is already killed by unit-multiple equivalence; logarithmic-form
and abc lower bounds alone lack the upper bound/exclusion input; sign-blind
cycle arguments must survive the negative-cycle falsification harness;
sum-product, zero-entropy classification, function-field carry transport,
Cobham rigidity, and independence/Goodstein analogies have no specified
load-bearing lemma. Importing entropy definitions, translating citations, or
formalizing the two accounting corrections above does not clear the novelty
bar. Leave their formal interfaces unchanged in this documentation-only lap.

## Trust, verification, and reopening condition

The default source has zero disclosed sorries. The fixed-b headline inherits
eleven existing Rhin-lite native certificates; it is not bare-trust-base-only.
The new cycle witness and both finiteness edges use exactly `propext`,
`Classical.choice`, `Quot.sound`. RT 3.2, power approximation, and topological
Furstenberg are proved, despite historical file names under Assumed.

Named citation debt remains: Tao, Eliahou/Hercher bounds and computations,
Baker bounded difference; abc is an explicitly conjectural input to conditional
results. Historical Rhin axiom routes in `wip/` are retired and not root
imports. Cited axioms are debt, not permanent mathematical destinations;
discharging them still does not create the missing uniform mechanism.

The handoff records the real full build, fixed-b audit, trust-only graph audit,
existing obstruction certificates, and proof-debt check. No new arithmetic
claim was kernel-proved in this reflection.

**Standing state: awaiting a new idea. No next proof lap is authorized by this
file.** Reopen only when a proposal names an exact bounded statement, a first
attack with concrete mathematical evidence, the new information it consumes,
an acceptance test, and a costume check against the obstructions above.
For the even-start edge the actual finite-to-one map is mandatory. For a
uniform Front-A route the small integer trajectory must be load-bearing.
For Front B the proposal must go beyond fixed-circuit finiteness and preserve
the correct primitive/integral population. These are admission criteria for a
future idea, not assignments to search each row in turn.

The reflection objective is complete. Use `box done` after the green commit,
not `box stuck`: absence of a promising current idea is not an impossible
external condition or a request for an operator decision. Do not resume the
completed cycle edge, enlarge a prefix filter, or substitute routine
formalization merely to keep the treadmill moving.

Newest checkpoint: `HANDOFF-2026-09-13-whole-board-reflection.md`.
Earlier directions remain recoverable in git and dated handoffs.
