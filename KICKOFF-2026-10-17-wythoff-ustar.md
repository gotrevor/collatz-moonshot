# KICKOFF 2026-10-17: Lemma U\* (|q̃_0| > 1 gives unbounded runs), Lemma H½, Lemma SG, Lemma O∞

Repo `collatz-moonshot`, branch `wip/wythoff-ustar` (cut from `origin/main` after PR #69 merged).  Close every `sorry` in one
new file:

| file | content | sorries |
|---|---|---|
| `CollatzMoonshot/WythoffUStar.lean` | the `q̃_0` identity; Lemma U\* in automaton form, its headline conditional on Weyl, Corollary U1; Lemma H½ and Corollary U2; Lemma SG (slide to the grid); Lemma O∞ (the G-shaped limit) | 5 |

23 theorems, 18 already proved, so closing the 5 open leaves closes the file.  The open leaves
are `qTilde_mul_prod_eq` (Lemma H½), `abs_two_pow_aeval_half_lt`,
`one_lt_three_pow_mul_abs_qTilde`, `u2_of_boundedRuns` (Corollary U2), and `oInf` (Lemma O∞).
Lemma U\* (automaton form and headline), Corollary U1 and Lemma SG are already sorry-free
(`#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`).

**The base files are proved** (sorry-free on `main`): `WythoffAutomaton` (`xOf`, `synDiv`,
`coeff_zero_eq_synDiv`, `sum_coeff_mul_eq_synDiv`), `WythoffGeneral` (`wy`,
`WeylEquidistributionMulti`), `WythoffPisot` (`stdRow`, `topRow`, `RunSystem`, `n3_runSystem`,
`two_pow_mul_aeval_half_odd`, `abs_aeval_half_ge`, `two_mul_sub_one_gt` and its helpers
`norm_multiset_prod_sub`, `prod_norm_half_sub_le`, `eval_ofReal_map`) and
`WythoffRunCriterion` (`runCriterion_of_weyl`, `n3_infinite_runs_of_weyl`).  Use them freely;
**do not edit them** (put helpers in the new file).  Imports: `Mathlib`,
`CollatzMoonshot.WythoffRunCriterion`.

Sources: `~/personal/tmp/amusical-agents/out/wythoff-finite.md` (§2 Lemma H½, Lemma U\* with
Corollaries U1 and U2, Lemma SG; §3.3 Lemma O∞), notation from `wythoff-classify.md` §1 and
`wythoff-pisot.md`.  The module docstring carries the paper proofs.

**Setup.**  `x ∈ (1/2, 1)` is a root of a monic `P = t^d + ⋯ + a_0 ∈ ℤ[t]`;
`q_k = synDiv P x k`; `qTilde P x = q_0 + 2a_0` (`q̃_0`, the top-row coefficient of `ε_0`).
`ustarSeq e0 x i = if i = 0 then e0 else 1 − x`.  `BoundedRuns α`: some `J` such that only
finitely many positive even `u` have `W^1 u, …, W^{J+1} u` all odd (Ren strengthened the
corollaries by ratifying this "off a finite set" form) (no earlier file has a bounded-runs
predicate).  The other conjugates are `(P.map (Int.castRingHom ℂ)).roots.erase (x : ℂ)`, as in
`WythoffPisot.two_mul_sub_one_gt`.

## Ratified, do not change

Every definition and theorem statement in the file:

* **Definitions:** `qTilde`, `ustarSeq`, `BoundedRuns`.
* **`q̃_0` identity:** `qTilde_eq_mul`, `qTilde_eq`, `not_irrational_of_abs_qTilde`,
  `irrational_of_irreducible` (all proved).
* **Lemma U\*:** `ustarSeq_zero`, `ustarSeq_of_ne`, `exists_int_eq_mul_one_sub`,
  `stdRow_ustarSeq`, `topRow_ustarSeq`, `ustar_runSystem`, `ustar_runSystem_of_irrational`
  (all proved).
* **Headline and U1:** `ustar_infinite_runs_of_weyl`, `abs_qTilde_lt_one_of_boundedRuns`,
  `lt_of_abs_qTilde_lt_one`, `xOf_lt_of_boundedRuns` (all proved).
* **H½ and U2:** `qTilde_mul_prod_eq`, `abs_two_pow_aeval_half_lt`,
  `one_lt_three_pow_mul_abs_qTilde`, `u2_of_boundedRuns` (open).
* **SG:** `sg_runSystem`, `sg_runSystem_conj` (proved).
* **O∞:** `synDiv_half_zero` (proved); `oInf` (open).

`WeylEquidistributionMulti` stays a hypothesis of the headline theorems (it is the one
prior-report input of `runCriterion_of_weyl`).  Do not prove it here and do not turn it into an
`axiom`.

## Rules

No `native_decide`, no axioms, no `maxHeartbeats` bumps.  Lean lines ≤ 100 characters.  **Never
change a ratified statement**; if one looks false, stop, record the counterexample in the
handoff and ask.  Commit after each proved lemma, and relabel its docstring `(drafted, NN%)` →
`(proved)`.  Notes as you go in `HANDOFF-wythoff-ustar.md`.  Helper lemmas and definitions are
welcome (above their first use).  Build with `lake build CollatzMoonshot.WythoffUStar`.

## Truth checks already run

`tmp/drafter-ustar/check.py` (gitignored; copy of
`~/personal/tmp/amusical-agents/out/wythoff-ustar-lean/check.py`; uv script, run directly, about
10 s, output `check.out`; `quick` mode smaller).  mpmath at 60 digits, exact Fractions for O∞,
scipy LP for run-system infeasibility.  Python mirrors of `synDiv`, `qTilde`, `stdRow`, `topRow`,
`RunSystem`, `ustarSeq`, `xOf`, `wy`.  Population: 672 roots in `(1/2, 1)` of irreducible monic
quadratics (`H ≤ 12`), cubics (`H ≤ 6`) and quartics (`H ≤ 3`).  **71 checks (35 teeth), 0
failures:**

* *`q̃_0` identity* on every population root; `|q̃_0|` never within `0.02` of `1` or `2`; the
  excluded values are realized exactly by the rational `x = a_0/(2a_0 − s)`.
* *U\*.*  The integer recipe on 3 801 values of `q ∈ [−20, 20]`.  On `x³ + 2x − 2`
  (`x = 0.7709`, `q̃_0 = −1.4057`): `stdRow_ustarSeq`, `topRow_ustarSeq`, `RunSystem` at every
  `n ≤ 60`, and classify's automaton run from it has length `≥ 60`.  `ustar_runSystem` on all 420
  population roots with `|q̃_0| > 1` at `n = 40`.
* *Headline / U1.*  On `W_α` for `x³ + 2x − 2` (40-digit floors, uncertified) the max run after
  even `u ≤ 2·10⁵` grows past `d`; `|q̃_0| < 1 ⟺ x < |a_0|/(2|a_0| − 1)` on the population;
  U1's bound holds on 36 G members and Y.
* *H½* on 1 552 real roots (monic, `a_0 ≠ 0`, `d = 2..5`); *U2* on the 7 bounded members and on
  every all-outside population root.
* *SG.*  `sg_runSystem_conj` on 970 (root, conjugate `‖z‖ ≥ 1`) pairs with `γ` the Lemma 1
  fixed point and `g` the nearest grid point; never certifies `n > J` on a bounded member; 107
  synthetic pure-real instances.
* *O∞* exhaustively for `d = 1..7` (`e_k ∈ [−3, 3]`, `[−2, 2]` for `d ≥ 6`; 21 551 polynomials):
  only `E = t^d` passes; `synDiv_half_zero` on all of them.
* **Teeth** (each must fail and does): wrong `q̃_0` variants `a_0(2x + 1)/x` and
  `(2x − 1)q_0`; no admissible `e0` at `q = ±2, ±1, 0.9, −0.5`; the wrong top-row variant
  `P(1) + a_0 − q̃_0e0`; `e0` off the recipe; **every G member (36) and Y has `|q̃_0| < 1`**
  (max `0.586`), so U\* does not apply, and G(2,2), Y, G(3,2), G(1,2) are LP-infeasible at
  `n = J + 1`; U1's bound fails on every `|q̃_0| > 1` root; G(2,2) and Y stay at max run `J` on
  `W_α`; H½ with `2^d` in place of `2^{d−1}`, and with `a_0 = 0`; U2's upper bound without
  `|q̃_0| < 1` (some all-outside roots have `|N| ≥ 3^{d−1}`); U2's lower bound without `hconj`
  (`t³ − 6t² + t + 1`: `9|q̃_0| = 0.97`); SG past its bound (the box breaks), and with `g` off
  the grid (the top row breaks); O∞ with `Σ ≤ 5/2` (`E = t² + t`), without `c_k ≥ 0`
  (`E = t² − 3t`); `synDiv_half_zero` with `E(0) ≠ 0`.

## Paper proofs (one per open sorry)

* **`qTilde_mul_prod_eq`** (120; finite §2 Lemma H½).  Copy the factorization block of
  `two_mul_sub_one_gt`: `Pc = P.map (Int.castRingHom ℂ)`,
  `prod_multiset_X_sub_C_of_monic_of_roots_card_eq`, `hroots : Pc.roots = x ::ₘ S`, and
  `eval c Pc = (c − x)·∏_{s∈S}(c − s)` (now without norms; `eval_multiset_prod`).  At `c = 0`:
  `a_0 = (−x)·∏(−s)` (`e3`-style cast).  Every `s ∈ S` is nonzero (else `a_0 = 0`) and
  `x ≠ 0`.  At `c = 1/2`: `∏(1/2 − s) = ∏(−s)·∏(1 − 1/(2s))` (`Multiset.prod_map_mul` after
  `1/2 − s = (−s)(1 − 1/(2s))`, `field_simp` per factor).  `qTilde_eq_mul` with
  `q_0 = −a_0/x = ∏(−s)` (cast to `ℂ`) gives `q̃_0 = (1 − 2x)∏(−s)`.  So
  `q̃_0∏(1 − 1/(2s)) = (1 − 2x)∏(1/2 − s) = 2P(1/2)`; then `2^{d−1}·2 = 2^d` (`d ≥ 1`: a monic
  `P` with a root is not constant).
* **`abs_two_pow_aeval_half_lt`** (80).  `a_0 ≠ 0` as in `run_bound_B2`.  Take norms in
  `qTilde_mul_prod_eq`: `|N| = |q̃_0|·2^{d−1}·∏‖1 − 1/(2s)‖`.  Each
  `‖1 − 1/(2s)‖ ≤ 1 + 1/(2‖s‖) < 3/2` (an induction like `prod_norm_half_sub_le`, giving
  `∏ ≤ (3/2)^{d−1}`, `card S = d − 1`).  With `|q̃_0| < 1`: `|N| < 2^{d−1}(3/2)^{d−1} = 3^{d−1}`
  (strict because `2^{d−1}∏ ≥ 0`, and if `∏ = 0` then `N = 0`, contradicting oddness).
* **`one_lt_three_pow_mul_abs_qTilde`** (60).  Same norms: `1 ≤ |N|` (`abs_aeval_half_ge`
  times `2^d`) and `|N| ≤ |q̃_0|·2^{d−1}∏‖1 − 1/(2s)‖`.  Use the strict per-factor bound and
  `card S = d − 1 ≥ 1` to get `∏ < (3/2)^{d−1}` (`Multiset.prod_lt_prod_of_nonempty` or an
  induction), and `q̃_0 ≠ 0` (else `N = 0`).
* **`u2_of_boundedRuns`** (80).  Lower bound: `abs_aeval_half_ge` multiplied by `2^d`.  Upper:
  build `hconj`.  For `z ∈ S`: `z` is a root (`Multiset.mem_of_mem_erase`, `mem_roots`), and
  `z ≠ x` because the roots are `Nodup` (`P` irreducible over `ℚ` in characteristic 0 is
  separable: `Irreducible.separable` on `P.map (algebraMap ℤ ℚ)` via Gauss, then
  `Polynomial.nodup_roots` for the map to `ℂ`; then `Multiset.Nodup.mem_erase_iff`).  If
  `‖z‖ ≤ 1`, `n3_infinite_runs_of_weyl` at `n = J + 1` gives an infinite set, contradicting
  `BoundedRuns` (a finite set).  Then `abs_qTilde_lt_one_of_boundedRuns` and `abs_two_pow_aeval_half_lt`.
* **`oInf`** (150; finite §3.3).  Work with integers.  For `k < d` set
  `m_k = Σ_{j∈Ioc k d} e_j·2^{d−j}` (`e_j = E.coeff j`); show
  `2^{d−k−1}·synDiv E (1/2) k = m_k` (termwise `2^{d−k−1}(1/2)^{j−k−1} = 2^{d−j}`) and
  `m_k` odd (split off `j = d`, `Monic.coeff_natDegree`, as in `two_pow_mul_aeval_half_odd`).
  From `hc`: `m_k ≥ 1`.  From `hsum` times `2^{d−1}`: `Σ_{k<d} 2^k m_k ≤ 2^d`.  With
  `Σ_{k<d} 2^k = 2^d − 1` (`Nat.geomSum_eq` or induction): `Σ 2^k(m_k − 1) ≤ 1`, each term even
  and `≥ 0`, so every `m_k = 1` (`Finset.sum_eq_zero_iff_of_nonneg` after showing the sum is
  `0`).  Then `m_{k−1} − m_k = e_k·2^{d−k} = 0` for `1 ≤ k < d`
  (`Finset.sum_Ioc_succ_top`-style split), so `e_k = 0`.  Conclude by `Polynomial.ext`:
  `coeff 0 = 0 = hE0`, `coeff k = 0` for `0 < k < d`, `coeff d = 1`, `coeff j = 0` for `j > d`
  (`coeff_eq_zero_of_natDegree_lt`); `coeff_X_pow`.

**Order of attack:** `qTilde_mul_prod_eq` (the factorization is reused) →
`one_lt_three_pow_mul_abs_qTilde` → `abs_two_pow_aeval_half_lt` → `u2_of_boundedRuns` →
`oInf` (independent; can go first if the multiset work stalls).

Rough total: 400-500 lines.

**Stop condition.**  `CollatzMoonshot/WythoffUStar.lean` sorry-free;
`lake build CollatzMoonshot.WythoffUStar` green with no warnings; `#print axioms` on every
declaration shows at most `propext`, `Classical.choice`, `Quot.sound`.

**Out of scope (later layers):** Lemma T (tracking) and Lemma FL (flatness, needs the flatness
theorem); Theorem L (Kronecker step) and Theorem C′(d); Lemma G and the census criteria FP1, H1;
Corollary B; the mirror side (classify Theorem M); the degree bound (finite §4).
