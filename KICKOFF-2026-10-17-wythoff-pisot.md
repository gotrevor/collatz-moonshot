# KICKOFF 2026-10-17: Theorem N3 (bounded Wythoff runs force a Pisot-dual slope) and Lemma B2

Repo `collatz-moonshot`, branch `wip/wythoff-pisot-m` (cut from `origin/main` after PR #67 merged).  Close every `sorry` in one
new file:

| file | content | sorries |
|---|---|---|
| `CollatzMoonshot/WythoffPisot.lean` | the run system; Lemma 1 (the fixed point `γ = (1 − x)/\|P(1)\|`); roots of unity and the homogeneous direction `Re(z^i)`; the N3 core (boundary sequence + perturbation); Theorem N3 in automaton form; the headline conditional on `RunCriterion`; Lemma B2 | 7 |

30 theorems, 17 already proved and 6 more assembled from the 7 open leaves, so closing the 7
closes the file.  The open leaves are `pow_ne_one_of_irreducible`,
`eval_one_ne_zero_of_irreducible`, `coeff_zero_ne_zero_of_irreducible`,
`sum_synDiv_mul_pow_eq_zero`, `perturb`, `two_pow_mul_aeval_half_odd`, `two_mul_sub_one_gt`.

**The base files are proved** (sorry-free on `main`): `WythoffAutomaton` (`xOf`,
`synDiv`, `coeff_succ_eq_synDiv`, `coeff_zero_eq_synDiv`, `sum_coeff_mul_eq_synDiv`, Theorem N)
and `WythoffGeneral` (`wy`, `WeylEquidistributionMulti`).  Use them freely; **do not edit them**
(put helpers in the new file).  Imports: `Mathlib`, `CollatzMoonshot.WythoffAutomaton`.

Sources: `~/personal/tmp/amusical-agents/out/wythoff-pisot.md` (§1 the run criterion, §2
Lemma 1 and Theorem N3, §3 Lemma B2), notation from `wythoff-classify.md` §1-§2.  The module
docstring carries the paper proof.

**Setup.**  `x ∈ (1/2, 1)` is a root of a monic `P = t^d + ⋯ + a_0 ∈ ℤ[t]`;
`q_k = synDiv P x k` are the coefficients of `Q = P/(t − x)` (`q_{d−1} = 1`); `q̃_0 = q_0 + 2a_0`.
`stdRow q d ε i = Σ_{k<d} q_k ε_{i+k}`, `topRow q d a0 ε = (q_0 + 2a_0)ε_0 + Σ_{1≤k<d} q_k ε_k`.
`RunSystem q d a0 n ε`: `ε_i ∈ (0, 1/2)` for `i < n`, the top row is an integer, and `R_i` is
an integer for `1 ≤ i`, `i + d ≤ n` (half-scale `ε = G/2` of classify's zonotope criterion).
`fixGamma P x = (1 − x)/|P(1)|`; `boundarySeq γ c i = γ + κc_i`, `κ = −γ` if `γ ≤ 1/4`, else
`1/2 − γ`.

## Ratified, do not change

Every definition and theorem statement in the file:

* **Definitions:** `stdRow`, `topRow`, `RunSystem`, `fixGamma`, `boundarySeq`, `RunCriterion`.
* **Rows:** `topRow_eq_stdRow_add`, `stdRow_add_smul`, `stdRow_const`, `RunSystem.mono` (all
  proved).
* **Lemma 1:** `eval_one_eq_mul_sum_synDiv`, `sum_synDiv_mul_fixGamma`, `fixGamma_mem`,
  `stdRow_fixGamma` (all proved).
* **Roots of unity:** `abs_re_pow_lt_one_of_norm_lt`, `abs_re_lt_one_of_norm_le_of_sq_ne_one`,
  `abs_re_pow_lt_one_of_norm_le`, `synDiv_zero_ne_zero` (proved); `pow_ne_one_of_irreducible`,
  `eval_one_ne_zero_of_irreducible`, `coeff_zero_ne_zero_of_irreducible`,
  `sum_synDiv_mul_pow_eq_zero` (open); `stdRow_re_pow` (assembled).
* **Core:** `boundarySeq_zero`, `boundarySeq_mem`, `stdRow_boundarySeq`, `n3_boundary`
  (proved); `perturb` (open); `n3_core` (assembled).
* **Theorem N3:** `n3_runSystem` (assembled).
* **Headline:** `xOf_mem` (proved); `n3_infinite_runs` (assembled).
* **Lemma B2:** `two_pow_mul_aeval_half_odd`, `two_mul_sub_one_gt` (open);
  `abs_aeval_half_ge`, `run_bound_B2` (assembled).

`RunCriterion` is a **prior-report hypothesis** (the sufficiency half of `wythoff-classify`'s
zonotope criterion with Theorem N4, PROVED 95-97% there).  It stays a hypothesis of
`n3_infinite_runs`.  Do not prove it here and do not turn it into an `axiom`; it is expected
to follow from `WythoffAutomaton` + `WeylEquidistributionMulti` in a later layer.
`WeylEquidistributionMulti` is not used in this file.

## Rules

No `native_decide`, no axioms, no `maxHeartbeats` bumps.  Lean lines ≤ 100 characters.  **Never
change a ratified statement**; if one looks false, stop, record the counterexample in the
handoff and ask.  Commit after each proved lemma, and relabel its docstring `(drafted, NN%)` →
`(proved)`.  Notes as you go in `HANDOFF-wythoff-pisot.md`.  Helper lemmas and definitions are
welcome (above their first use).  Build with `lake build CollatzMoonshot.WythoffPisot`.

## Truth checks already run

`tmp/drafter-pisot/check.py` (gitignored; copy of
`~/personal/tmp/amusical-agents/out/wythoff-pisot-lean/check.py`; uv script, run directly, 27 s,
output `check.out`; `quick` mode 16 s).  mpmath at 120 digits, exact Fractions for B2's parity,
scipy LP with integer row enumeration for run-system feasibility.  Python mirrors of `synDiv`,
`stdRow`, `topRow`, `RunSystem`, `fixGamma`, `boundarySeq`, `xOf`, `wy`.  **218 checks (33 teeth), 0
failures:**

* *Lemma 1* on the 6 N3 members, 7 bounded members and random roots; `fixGamma_mem` everywhere.
* *Roots of unity.*  `|Re z^i| < 1` on random `‖z‖ < 1`, on `e^{iπ√2}` and on the Salem
  member's unit-circle conjugate (max `0.99999995` over `i < 2·10⁴`); the bridge on all 6
  members; `P(1) ≠ 0`, `a_0 ≠ 0` on every monic irreducible of degree 2-4 at height ≤ 3 / 2;
  `Q(z) = 0` and `R_i(Re z^i) = 0` for every conjugate of every member.
* *Core and N3.*  For every conjugate `‖z‖ ≤ 1` of the 6 members (`n3cert`'s list: three class-N
  cubics, two real-inside quartics, the Salem quartic): every hypothesis of `n3_core`, every
  conclusion of the boundary lemmas, and the `perturb` construction (with `b = c`) satisfies
  `RunSystem` at `n = 60`; classify's automaton run from it has length `≥ 60`.  40 synthetic
  instances (random real `q` from roots in the disk, `d ≤ 6`, random `a_0`) at `n = 40`.  The
  population (irreducible cubics `H ≤ 4`, quartics `H ≤ 2`): every root with a conjugate in the
  closed disk passes at `n = 30` (63 roots).  LP: each member's run system is feasible at
  `n = d, d+1, d+2`.
* *Headline.*  `xOf_mem` on random `α > 2`; on `W_α` itself (40-digit floors, uncertified) the
  max run after even `u` grows for an N3 member and the Salem member.
* *B2.*  Parity on every monic `P` of degree 1-6 (height 3, or 1 for degrees 5-6); the gap and
  the run bound on G(m, r) (`m ≤ 4`, `r ≤ 10`, `J = m`) and Y (`J = 3`); the gap on every root
  in `(1/2, 1)` with all other conjugates outside the disk (cubics `H ≤ 8`, quartics `H ≤ 3`).
* **Teeth** (each must fail and does): `fixGamma_mem` at `x = 0.382` (`γ = 0.618`) and at
  `P(1) = 0`; `e^{2πi/5}` (`|Re z^5| = 1`); `‖z‖ = 1.01`; `w = −1`; the bridge for `t² + t + 1`
  (no root in `(0, 1)`) and for the reducible `(t² + t + 1)(t² + t − 1)`; degree 1 (`t − 1`,
  `t`); `Q(x) = P'(x) ≠ 0` (so `z ≠ x` matters).  **Bounded members** G(2,2), Y, G(3,2),
  G(1,2), `x³ + x − 1`, tribonacci, plastic: every conjugate has `‖z‖ > 1`, fails `|c_i| < 1` at
  some `i ≤ 3`, and its boundary sequence leaves `(0, 1/2)`; and N3's conclusion itself fails:
  the run system is LP-infeasible at `n = J + 1` (G(2,2): 3, Y: 4, G(3,2): 4, G(1,2): 2).  On
  `W_α`, G(2,2) and Y stay at max run `J`.  B2: non-monic `2t − 1`; `J = 40` for G(2,2) violates
  the run bound; some roots with a conjugate in the disk violate the gap bound.

## Paper proofs (one per open sorry)

* **`pow_ne_one_of_irreducible`** (40; pisot §2 step 1).  `z` is integral (`P` monic).
  `P = minpoly ℤ z` (`minpoly.eq_of_irreducible_of_monic hirr hz hP`).  If `z^m = 1`, then
  `minpoly ℤ z ∣ X^m − 1` (`minpoly.isIntegrallyClosed_dvd`), so `aeval x (X^m − 1) = 0`,
  `x^m = 1`, contradicting `pow_lt_one₀` (`0 < x < 1`, `m ≠ 0`).
* **`eval_one_ne_zero_of_irreducible`** (40; pisot §2 step 1, "`±1` is not a root").
  `P.eval 1 = 0` gives `X − C 1 ∣ P` (`Polynomial.dvd_iff_isRoot`); write
  `P = (X − C 1) * R`; `Irreducible.isUnit_or_isUnit`: `X − C 1` is not a unit (degree 1), so
  `R` is a unit, `natDegree R = 0` (`Polynomial.natDegree_eq_zero_of_isUnit`), and
  `natDegree P = 1` (`natDegree_mul`, `X_sub_C_ne_zero`), contradicting `hd`.
* **`coeff_zero_ne_zero_of_irreducible`** (30).  Same with `X ∣ P ↔ P.coeff 0 = 0`
  (`Polynomial.X_dvd_iff`).
* **`sum_synDiv_mul_pow_eq_zero`** (60; pisot §2 step 1).  Prove the complex identity
  `aeval z P = (z − x)·Σ_{k<d} q_k z^k` by the proof of `sum_coeff_mul_eq_synDiv` over `ℂ`
  (`aeval_eq_sum_range`; the casts of `coeff_succ_eq_synDiv` and `coeff_zero_eq_synDiv` via
  `Complex.ofReal`), or apply `sum_coeff_mul_eq_synDiv` to `w_j = Re(z^j)` and to
  `w_j = Im(z^j)` and recombine with `Complex.ext`.  Then cancel `z − x ≠ 0`.
* **`perturb`** (100; pisot §2 step 3).  `σ = 1` if `e_0 ≤ 1/4` else `−1`;
  `ε δ i = if i = 0 then e_0 + σδ else e_i + λ(δ) b_i`, `λ(δ) = −σq̃_0δ/S_b`.  Rows: for `i ≥ 1`
  every index `i + k ≥ 1`, so `stdRow q d (ε δ) i = stdRow q d e i + λ·stdRow q d b i`
  (`stdRow_add_smul` after `Finset.sum_congr` with `if_neg`); the top row moves by
  `σq̃_0δ + λS_b = 0` (`topRow`, `Finset.sum_congr` on `Ico 1 d`, `field_simp`).  Box: avoid an
  explicit minimum, use filters: each condition `0 < ε δ i < 1/2` (`i < n`) holds eventually in
  `𝓝[>] 0` (for `i = 0` since `e_0 ∈ [0, 1/2]` and `σ` points inward; for `i ≥ 1` since
  `ε δ i → e_i ∈ (0, 1/2)`, `Filter.Tendsto.eventually` with `Ioo_mem_nhds`); combine with
  `Filter.eventually_all_finset` over `Finset.range n`, then `Filter.Eventually.exists`.
* **`two_pow_mul_aeval_half_odd`** (50; pisot §3 B2).  `m = Σ_{j ≤ d} a_j 2^{d−j}`
  (`aeval_eq_sum_range`, `Finset.mul_sum`, `2^d·(1/2)^j = 2^{d−j}` for `j ≤ d`).
  `Finset.sum_range_succ` splits off `a_d = 1` (`Monic.coeff_natDegree`); every other term is
  `2·(a_j 2^{d−j−1})`, so `m = 2s + 1`.
* **`two_mul_sub_one_gt`** (150; pisot §3 B2).  Over `ℂ`, `P.map = ∏_{r ∈ roots}(X − C r)`
  (`Polynomial.eq_prod_roots_of_monic_of_splits_id`, `IsAlgClosed.splits`); `x ∈ roots`
  (`mem_roots`, `aeval` = `eval ∘ map`), so `roots = x ::ₘ roots.erase x`
  (`Multiset.cons_erase`), and `card (roots.erase x) = d − 1` (`splits_iff_card_roots`).
  Evaluate at `1/2` and at `0`: `|P(1/2)| = |1/2 − x|·∏|1/2 − z_s|` and `|a_0| = x·∏|z_s|`
  (`Multiset.prod_map_mul`, norms of products).  Each `|1/2 − z_s| ≤ 1/2 + |z_s| < (3/2)|z_s|`;
  the product over a nonempty multiset (`d ≥ 2`) is strictly smaller
  (`Multiset.prod_lt_prod_of_nonempty`, or induction on the multiset).  So
  `|P(1/2)| < (x − 1/2)·(3/2)^{d−1}·|a_0|/x < (x − 1/2)·(3/2)^{d−1}·2|a_0|`, and with
  `abs_aeval_half_ge`, `2^{−d} < (x − 1/2)·(3/2)^{d−1}·2|a_0|`, i.e.
  `2x − 1 > 1/(2·3^{d−1}|a_0|)`.  (`a_0 ≠ 0` as in `run_bound_B2`'s proof.)

**Order of attack:** `perturb` (the only new mechanism; it closes `n3_core`) →
`sum_synDiv_mul_pow_eq_zero` → the three irreducibility lemmas (these close `n3_runSystem` and
`n3_infinite_runs`) → `two_pow_mul_aeval_half_odd` → `two_mul_sub_one_gt`.  If time is short,
the first five are the headline (Theorem N3).

Rough total: 450-550 lines.

**Stop condition.**  `CollatzMoonshot/WythoffPisot.lean` sorry-free;
`lake build CollatzMoonshot.WythoffPisot` green with no warnings; `#print axioms` on every
declaration shows at most `propext`, `Classical.choice`, `Quot.sound`.

**Out of scope (later layers):** proving `RunCriterion` (needs Theorem N4's uniform law of the
fresh phases from `WeylEquidistributionMulti`, plus the zonotope openness argument); the mirror
side (classify Theorem M); Proposition B1 (Mahler bound `M(P) = |a_0|/x < 2|a_0|`) and the
complete `(d, |a_0|)` lists; the U pairings (pisot §4).
