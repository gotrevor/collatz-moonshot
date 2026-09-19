# HANDOFF 2026-09-19 — stopping-time correctness on two-run words

Bounded helper per the 2026-09-19 override in `DIRECTION.md` (two-lap budget; finished in one).
**No successor lap.**

## Checkpoint
* Branch `main`; `lake build` green, 8780 jobs (pre-commit hook re-verified).  Not pushed.
* New files only: `CollatzMoonshot/FrontA/FirstCrossingTwoRun.lean`, its root import line
  (`CollatzMoonshot.lean` line 59), and this handoff.  No existing theorem or definition
  touched; `DIRECTION.md` and the experiments untouched.

## What landed (all five frozen targets, verbatim)
```
def CSTVerified : Prop := ∀ n m, 2 ≤ n → n ≤ 28 * 10 ^ 18 → At n m → tstep^[m] n < n
theorem ones_ge_of_survives (hv : CSTVerified) {n m} (hn : 2 ≤ n) (h : At n m)
    (hsurv : n ≤ tstep^[m] n) : 492276 ≤ ones (traceWord n m)
def twoRunWord (k₁ l₁ k₂ l₂ : ℕ) : List Bool
theorem iterate_ge_of_prefix_supercritical {n j}
    (hp : 2 ^ j ≤ 3 ^ ones (traceWord n j)) : n ≤ tstep^[j] n
theorem descends_of_twoRun (hv : CSTVerified) {n m k₁ l₁ k₂ l₂} (hn : 2 ≤ n)
    (h : At n m) (hw : traceWord n m = twoRunWord k₁ l₁ k₂ l₂) : tstep^[m] n < n
```
Plus three reusable helpers introduced on the way (not in the freeze, all sorry-free):
`run_false` (`z = 2^b · tstep^[b] z` on an all-even run), `run_true`
(`∃ s ≥ 1, z + 1 = 2^a s ∧ tstep^[a] z + 1 = 3^a s` on an all-odd run), and
`traceWord_of_append_singleton` (trace of the prefix that drops one final letter).

No `sorry`, no new axiom, no new `native_decide`.
`#print axioms descends_of_twoRun` = `propext, Classical.choice, Quot.sound` plus exactly the
eleven inherited Rhin-lite `native_decide` certificates (`pow_cert_10781274`,
`rhinLiteI₁_ratio_base`, `rhinLiteRootLeft_ge_three`, `rhinLite_boundProduct_certificate`,
`rhinLite_boundProduct_certificate_tight`, `rhinLite_cauchy_radius_certificate`,
`rhinLite_critical_sign_change`, `rhinLite_factorBound_nonneg`,
`rhinLite_positiveRootLeft`, `rhinLite_rootBracket_lt`, and the one further `pow_cert`),
i.e. nothing beyond the allow-listed ledger that `sep_two_three` / `sep_strong_492276`
already carry.

## Mathematical content
The proof is a two-sided squeeze on `K = k₁ + k₂`, the number of odd steps.

*Lower side* (`ones_ge_of_survives`, independent of the word shape): if `n ≥ 2` survives its
first crossing with `1 ≤ a < 492276` ones, `sep_strong_492276` gives `3^a ≤ D·2^25`
(`D = 2^m − 3^a`), and `small_start_of_not_descending` gives `3·D·n ≤ a·3^a ≤ a·D·2^25`,
so `3n < 492276·2^25 ≈ 1.65·10^13` and `n` lands inside the Rozier–Terracol verified range,
where `CSTVerified` forces descent.  The `a = 0` branch is the all-even word, where the
iterate identity reads `2^m·y = n` with `m ≥ 1`.

*Upper side*: in the main case all four blocks are nonempty, the run identities give
`3^k₁(n+1) = 2^k₁(2^l₁ x₁ + 1)` and `3^k₂(x₁+1) = 2^k₂(2^l₂ y + 1)`.  Multiplying and
dropping the two `+1`s, `3^K(n+1)(x₁+1) ≥ 2^m x₁ y ≥ 2^m x₁ n`; the middle point satisfies
`x₁ ≥ n` (its prefix is supercritical), which turns `n(x₁+1) ≤ (n+1)x₁` and cancels `x₁`:
`2^m n² ≤ 3^K (n+1)²`, hence `D·n ≤ 3·3^K`.  The near-critical window
`3^K < 2^m < 2·3^K` (the proper prefix of length `m−1` plus a parity argument for
strictness) lets `sep_two_three` cube this into `n³ ≤ 27·2^K`, so `(n+1)³ < 2^(K+8)`.
Two lower bounds now bite: `2^k₁ ≤ n+1` gives `3k₁ < K + 8`, and
`2^K ≤ 3^k₁(n+1)` (from `2^k₂ ≤ x₁ + 1 ≤ 3^k₁ a₀`, which uses `l₁ ≥ 1`) cubes with
`27 < 32` to `2K < 5k₁ + 8`.  Together `K < 64` — against `K ≥ 492276`.

Degenerate shapes: `k₂ = 0` and `l₁ = 0` collapse the word to `oneCircuitWord` and reuse
`descends_of_oneRun`; `k₁ = 0` (with `l₁, k₂ ≥ 1`) is vacuous because the length-one prefix
would have to satisfy `2 ≤ 3^0`; `l₂ ≥ 1` because a crossing word ending in `true` would give
`2^m ≤ 2·3^(K−1) < 3^K`.

This does **not** prove CST: it is the two-run instance of `StoppingCorrect`, conditional on
the numerically verified range.  The genuinely open inputs to
`FirstCrossing.conjecture_of_stoppingCorrect_and_crossingExists` remain `StoppingCorrect`
(now known on one-run and two-run words) and `CrossingExists`.

## Exact next steps (only under a NEW attended override)
1. Nothing pending from this lap; all five frozen targets are proved and axiom-clean.
   Do not fall through to an older dated override in `DIRECTION.md`.
2. The obvious successor is the `r`-run word `1^k₁ 0^l₁ … 1^k_r 0^l_r`.  The same telescoping
   product gives `3^K ∏(x_{i}+1) = 2^K ∏(2^{l_i} x_i + 1)` with every `x_i ≥ n`, hence
   `2^m n^r ≤ 3^K (n+1)^r` and `D·n ≤ r·3^K`; `sep_two_three` then yields `n³ ≤ r³·2^K`
   and `(n+1)³ < r³·2^(K+3)`.  The lower bound generalizes to `2^K ≤ 3^(K−k_r)·(n+1)^{r−1}`,
   so the squeeze closes only while `r` is `o(K)` — the constant `64` becomes a function of
   `r`.  Quantifying that threshold (is `r ≤ c·K/log K` enough?) is the real next question,
   and it is where the two-run argument stops being free.
