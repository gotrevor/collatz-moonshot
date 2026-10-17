# KICKOFF 2026-10-16: the Wythoff run automaton (Theorems N, O), Y's mirror, and the plastic 7-cycles

Repo `collatz-moonshot`, branch `wip/wythoff-mirrorY` (cut from `origin/main` at `daf38cf`).
Close every `sorry` in three new files (46 statements):

| file | content | sorries |
|---|---|---|
| `CollatzMoonshot/WythoffAutomaton.lean` | Theorem N (the run automaton of an algebraic member, any monic `P ∈ ℤ[t]`), Lemma N0, Theorem O (the first-row condition holds iff `P = t^d − 2rt + r`) | 19 |
| `CollatzMoonshot/WythoffMirrorY.lean` | Theorem Y′: Lemma P for Y's mirror `W_β`, `β = 2x ≈ 1.0519`: recurrence on `O E³`, no finite orbit, both escapes, minima, exact count, density | 15 |
| `CollatzMoonshot/WythoffSeven.lean` | the plastic member `x³ − x² + 2x − 1`: `W⁷ = n` on the cylinder `E O E O⁴`, period exactly 7, infinitely many 7-cycles (unconditional) | 12 |

**The base files are proved** (on `main`, sorry-free): `WythoffGeneral` (`wy`, branches,
`wy_pos_iff`, `wy_one`, `wy_lt_of_even`, `wy_lt_of_odd`, Weyl hypotheses), `MonotonePotential`
(Lemma P), `AmusicalTrap`, `WythoffLine` (Theorem G; its mirror section §Mirror is the template
for Y′ §3), `WythoffSporadic` (Theorem Y; its polygon lemmas are reused verbatim by Y′).  Use them
freely; **do not edit them** (put helpers in the new files).  Imports: `Automaton` imports
`WythoffGeneral`; `MirrorY` imports `AmusicalTrap`, `MonotonePotential`, `WythoffGeneral`,
`WythoffSporadic`; `Seven` imports `WythoffGeneral`.  Do not add imports between the three new
files (in particular prove `wy_alphaP_eoo` directly, not via `WythoffAutomaton`), so each closes
independently.

Sources: `~/personal/tmp/amusical-agents/out/wythoff-classify.md` (§1 Theorem N, §3.1 Theorem O,
§4 Theorems M and Y′, §7 (3) the plastic member) and its scripts in
`~/personal/tmp/amusical-agents/out/wythoff-classify/` (`validate.py`, `ymirror.py`,
`plastic.py`; uv scripts, run directly).  Each new file's module docstring carries the paper proof.

**Setup.**  `wy α n = ⌊(n/2)α⌋` (`n` even), `⌈((n+1)/2)β⌉ − 1` (`n` odd), `β = α/(α − 1)`.
*Automaton:* `xOf α = β/2`; `P : ℤ[X]` monic with `aeval (xOf α) P = 0`;
`synDiv P x k = Σ_{k<j≤d} a_j x^{j−k−1}` (the coefficients of `P/(t − x)`); phases
`oddPhase α v = (W v + 1) − x(v + 1)` (`[0, 1)` on odds), `evenPhase α n = (W n + 1) − (α/2)n`
(`(0, 1]` on evens); `autoPhi`, `autoPhi0` the automaton values `Φ`, `Φ₀`; `gPoly d r = t^d − 2rt + r`;
`FirstRowCond P x` = `q̃₀ ≥ 0 ∧ q_k ≥ 0 (1 ≤ k ≤ d−2) ∧ q̃₀ + Σ q_k ≤ 1`, `q̃₀ = q₀ + 2a₀`.
*Y′:* `ymPerm = wyPerm betaY`, `W′(2k) = ⌊2kx⌋`, `W′(2k − 1) = ⌈kα⌉ − 1` (`betaY_div_sub_one`);
mirror phases `ymF1 s = (W′ s + 1) − (α/2)(s + 1)` (`[0, 1)`), `ymFeven v = (W′ v + 1) − xv`
(`(0, 1]`), which play exactly the roles of `yF1`, `yFodd`.
*Seven:* `pRoot ≈ 0.5698402910` (`Classical.choose`, pinned by `pRoot_spec` + `pRoot_unique`),
`alphaP = 2x/(2x − 1) ≈ 8.1592`, `betaP = 2x`; `A = α/2 = 2x² − x + 4`, `Ax = x² + 2`;
`sevenCyl` = even `n` with parities `O, E, O, O, O, O` at `W(n), …, W⁶(n)`.

## Ratified, do not change

Every definition and theorem statement in the three files:

* **WythoffAutomaton:** `xOf`, `synDiv`, `oddPhase`, `evenPhase`, `autoPhi`, `autoPhi0`,
  `gPoly`, `FirstRowCond`; `synDiv_natDegree_sub_one`, `synDiv_of_le` (proved),
  `coeff_succ_eq_synDiv`, `coeff_zero_eq_synDiv`, `wy_add_one_eq_ceil`, `oddPhase_mem`,
  `evenPhase_mem`, `xOf_div_two_mul_sub_one`, `sum_coeff_iterate_eq`, `sum_coeff_iterate_eq_ceil`,
  `sum_coeff_iterate_eq_floor_add_one`, `iterate_odd_iff_autoPhi`, `first_step_eq_ceil`,
  `first_step_odd_iff`, `monic_gPoly`, `natDegree_gPoly`, `synDiv_gPoly`, `thmO`,
  `firstRowCond_gPoly`, `thmO_iff`.
* **WythoffMirrorY:** `ymPerm`, `ymF1`, `ymFeven`; `one_lt_betaY` (proved), `betaY_lt_two`
  (proved), `betaY_div_sub_one` (proved), `ymPerm_apply` (proved), `ymF1_mem`, `ymFeven_mem`,
  `wy_betaY_iterate_three_phase`, `wy_betaY_iterate_four_phase`, `wy_betaY_iterate_three_sub_mem`,
  `wy_betaY_iterate_four_eq`, `exists_odd_iterate_Ym`, `le_wy_betaY_iterate_of_even_run`,
  `hyp_ymPerm`, `returnMap_ymPerm_ge`, `permOrbit_ymPerm_infinite` (proved from `hyp_ymPerm`),
  `tendsto_ymPerm_pow` (ditto), `tendsto_ymPerm_pow_neg` (ditto), `isOrbitMin_ymPerm_iff`,
  `minCount_ymPerm_add`, `minCount_ymPerm_ge`, `ymPerm_infinitelyManyInfiniteOrbits`,
  `tendsto_minCount_ymPerm`.
* **WythoffSeven:** `pRoot`, `alphaP`, `betaP`, `sevenCyl`; `exists_pRoot`, `pCubic_lt`,
  `pRoot_spec`, `pRoot_unique`, `pRoot_bounds`, `pCubic_ne_zero_rat`, `natDegree_pCubic`,
  `irreducible_pCubic`, `irrational_pRoot`, `linearIndependent_pRoot`, `pRoot_pow_seven`,
  `pRoot_mul_eq_one`, `alphaP_div_sub_one`, `half_alphaP_eq`, `alphaP_cubic`, `alphaP_mem`,
  `irrational_alphaP` (all proved); `wy_alphaP_eoo`, `wy_alphaP_iterate_three_sub_mem`,
  `wy_alphaP_iterate_four_eq`, `wy_alphaP_iterate_five_eq`, `wy_alphaP_iterate_six_eq`,
  `wy_alphaP_iterate_seven_eq`, `minimalPeriod_alphaP_of_cyl`, `minimalPeriod_alphaP_twenty`,
  `exists_simultaneous_approx`, `infinite_simultaneous_approx`,
  `twenty_add_two_mul_mem_sevenCyl`, `infinite_minimalPeriod_seven`.

`WeylEquidistributionMulti` (in `WythoffGeneral`) is a **literature hypothesis**; it stays a
hypothesis of `tendsto_minCount_ymPerm` only.  Do not prove it and do not turn it into an
`axiom`.  Everything else is unconditional, **including the infinitude of 7-cycles** (Dirichlet
pigeonhole, not Weyl).

## Rules

No `native_decide`, no axioms, no `maxHeartbeats` bumps.  Lean lines ≤ 100 characters.  **Never
change a ratified statement**; if one looks false, stop, record the counterexample in the
handoff and ask.  Commit after each proved lemma.  Notes as you go in `HANDOFF-wythoff-classify.md`.
Helper lemmas and definitions are welcome (above their first use).  Build with
`lake build CollatzMoonshot.WythoffAutomaton CollatzMoonshot.WythoffMirrorY CollatzMoonshot.WythoffSeven`.

## Truth checks already run

`tmp/drafter-classify/check.py` (gitignored; uv script, run `./check.py`, 56 s, output
`check.out`; `quick` mode 14 s).  Every algebraic constant is a 400-bit certified interval,
derived from the root exactly as the Lean definitions derive it (`α → β = α/(α − 1) → xOf = β/2`);
every floor/ceiling certified (both ends agree); phases are Fraction intervals; the Python `W`
mirrors Lean's `wy` on all of `ℤ` (`⌈·⌉ − 1` on odds, so `W(−1) = −1`).  **70 checks (14 teeth),
0 failures:**

* *Theorem N.*  On `u ∈ [−3000, 3000]` (all parities, negatives included) for nine members:
  G(2,2), G(3,2), G(1,3), Y, plastic, a quartic, `5 + √17`, the non-minimal `P = (t + 1)·Y`, and
  Y's **mirror side** (`xOf = α_Y/2`, `P = t³ − 11t² + 9t − 2`): the algebra identity, the
  ceiling form, the floor form, the parity iff, the first-step identity and its parity iff.
  Known answers: N(2) for G(2,2) gives left side `1` and `W³ = 2n` on `E O O`; for Y it gives
  `Φ₀ = yPhase3(yF1, yFodd)` and left side `W³ + 2n − W + W² + 1`.  N0, phase ranges, and the
  synthetic-division identities exactly (Fractions, 300 random `P`, `x`).  The boundary
  `n = −1` (`G = 0` exactly) is handled exactly.
* *Theorem O.*  **Every** certified root in `(1/2, 1)` of **every** monic `P ∈ ℤ[t]` of degree
  2-5 at heights 30 / 11 / 5 / 3 (8 883 roots, reducible `P` included): `FirstRowCond` holds iff
  `P = gPoly d r`, `r ≥ 1` (22 = 22, 0 mismatches; equality cases decided by exact gcd).
  Converse for `d ≤ 10`, `r ≤ 40`; `synDiv_gPoly` exactly.  G(2,2) passes, Y fails.
* *Y′.*  Phase ranges and both phase identities on `s ∈ [−20001, 20000] ∪ [10⁶, 10⁶ + 4000]`
  (all parities); `t ∈ {−1, 0, 1}` on `O E E`; the recurrence on all 17 242 `O E³` points of
  `[−2·10⁵, 2·10⁵]`; runs ≤ 3; `4s ≤ 3W′^{j+1}(s)` on every even prefix (min `R′(s)/s = 1.4731`
  at `s = 93`); `pos_iff`, (H1); `isOrbitMin_ymPerm_iff` = brute force on `[1, 2·10⁴]` (7 872
  minima, no finite orbit); `minCount_ymPerm_add` and `_ge` at every `X ≤ 6000`; census
  **786 810** minima `≤ 2·10⁶` (the research note's number; `dX = 786 815.6`).
* *Seven.*  Root, bounds, `x⁷ = (2x − 1)²`, `x(x² − x + 2) = 1`, `A = 2x² − x + 4`,
  `Ax = x² + 2`, the `α` cubic, `alphaP_mem`; every label lemma under exactly its own
  hypotheses on all even `n ∈ [−2·10⁵, 2·10⁵]` (`K₃ ∈ {±1}` on 30 489 `E O E O` points, …,
  `W⁷ = n` on all 18 867 cylinder points); **9 427** hits among the first `10⁵` evens (the
  note's number); the path of `20`; the translation lemma's certified margins (`≥ 0.12997` at
  `n = 20`, error coefficient `≤ 10.16`) and its conclusion on all 30 `q ≤ 3·10⁵` with
  `‖qA‖, ‖qAx‖ < 1/200`; simultaneous approximation for `Q ≤ 40`.
* **Teeth** (each must fail and does): Theorem N with the phase sign flipped (Y's `yFodd`
  convention); Theorem N (2) without the `2a₀ G_E` shift; Theorem N with a polynomial not
  vanishing at `x`; Theorem O without the sum condition (842 non-G roots pass); Theorem O with
  `q₀` for `q̃₀`; Theorem O with `2 ≤ r` (the multinacci `t³ − 2t + 1`, `t⁴ − 2t + 1` satisfy the
  condition with `r = 1`); Y′ recurrence with `+1`; Y′ minimum test with 3 predecessors (592
  mismatches); the label lemmas without `h₃`, `h₄`, `h₆`; the 7-cycle identity on the other
  slope-1 cylinder `E O³ E O²` (there `W⁷ = n − 1`, 0/658); the perturbed cubic
  `x³ − x² + 2x − 1.001` (1/316); the translation lemma at tolerance `1/5` (384 failures).

## Paper proofs

### §1 WythoffAutomaton: synthetic division and phases (≈ 200 lines)

* **`synDiv_natDegree_sub_one`** (15): `Finset.Ioc (d−1) d = {d}`, `Monic.coeff_natDegree`.
* **`coeff_succ_eq_synDiv`** (40): `k ≥ d`: both sides `0` (`coeff_eq_zero_of_natDegree_lt`,
  `synDiv_of_le`).  `k < d`: `Finset.Ioc k d = insert (k + 1) (Ioc (k + 1) d)`
  (`Finset.Ioc_insert_left` or `Finset.sum_Ioc_succ_top`-style), `x · x^{j−k−2} = x^{j−k−1}`
  (`Finset.mul_sum`, `pow_succ`, natural subtraction `j − k − 1 = (j − (k + 1) − 1) + 1`).
* **`coeff_zero_eq_synDiv`** (30): `aeval_eq_sum_range`, `Finset.sum_range_succ'`, factor `x`.
* **N0, `oddPhase_mem`, `evenPhase_mem`** (50): `v = 2k − 1`, `wy_two_mul_sub_one`,
  `xOf α · 2k = k β`; `Int.le_ceil`, `Int.ceil_lt_add_one`; `wy_two_mul`, `Int.floor_le`,
  `Int.lt_floor_add_one`.  **`xOf_div_two_mul_sub_one`** (15): `field_simp` with `α − 1 ≠ 0`.

### §2 WythoffAutomaton: Theorem N (≈ 350 lines)

* **`sum_coeff_iterate_eq`** (80).  `oddPhase α (W^k u) = w_{k+1} − x w_k` by unfolding
  (`Function.iterate_succ_apply'`).  `Σ_{k<d} q_k (w_{k+1} − x w_k) = Σ_{k<d} q_k w_{k+1} −
  x Σ_{k<d} q_k w_k`; reindex the first sum (`Finset.sum_range_succ'`/`sum_range_succ`), use
  `a_{j} = q_{j−1} − x q_j` (`coeff_succ_eq_synDiv`, `q_d = 0`) and `a_0 = −x q_0`.
* **`sum_coeff_iterate_eq_ceil`** (50).  Split off `k = d − 1` from the right side
  (`Finset.sum_range_succ` at `d = (d − 1) + 1`), `q_{d−1} = 1`; the integer `N` (cast) equals
  `Φ + G` with `G ∈ [0, 1)` (`oddPhase_mem`): `Int.ceil_eq_iff`.
* **`sum_coeff_iterate_eq_floor_add_one`** (40).  `Int.ceil_eq_floor_add_one_iff_notMem`
  (or `Int.floor_eq_iff`): if `Φ = z ∈ ℤ` then `G = N − z ∈ ℤ ∩ [0, 1)`, `G = 0`, so
  `x(v + 1) = W v + 1`; `hirr.intCast_mul` with `v + 1 ≠ 0`.
* **`iterate_odd_iff_autoPhi`** (60).  Reduce the integer sum mod 2: for `j < d`,
  `2 ∣ W^j u + 1`; `a_d = 1` (`Monic.coeff_natDegree`); `Finset.sum_range_succ`,
  `Int.emod_emod_of_dvd`, `Finset.dvd_sum`; then `omega` on `N % 2`.
* **`first_step_eq_ceil`** (90).  Real algebra: with `w_0 := n/(2x − 1)` (a real), `x w_0 = (α/2)n`
  so `evenPhase α n = w_1 − x w_0`, and `a_0 w_0 = a_0(2(w_1 − G_E) − n)` (`1/(2x − 1) = α − 1`).
  Run the telescoping of `sum_coeff_iterate_eq` with `w_0` real (state a general helper: for any
  real sequence `w` and `G_{k+1} := w_{k+1} − x w_k`, `Σ_j a_j w_j = Σ_k q_k G_{k+1}`; then both
  N(1) and N(2) are instances).  Move `−2a_0 G_E` into `Φ₀`; the last phase is `oddPhase` of the
  odd point `W^{d−1} n` (`d ≥ 2`), in `[0, 1)`.
* **`first_step_odd_iff`** (40).  As `iterate_odd_iff_autoPhi`, with `n`, `2a_0 w_1` even.

### §3 WythoffAutomaton: Theorem O (≈ 350 lines)

* **`monic_gPoly`, `natDegree_gPoly`** (20): `monicity!`, `compute_degree!` (`d ≥ 2`).
* **`synDiv_gPoly`** (60).  `coeff_gPoly`: `coeff_X_pow`, `coeff_C_mul_X`, `coeff_C`; the sum
  over `Ioc k d` has the single nonzero term `j = d` for `1 ≤ k < d` and `j ∈ {1, d}` at `k = 0`.
* **`thmO`** (200).  Module docstring.  Steps: (i) all of `q̃₀, q_1..q_{d−2}` in `[0, 1]`
  (sum ≤ 1, all ≥ 0; `Finset.single_le_sum`); (ii) for `2 ≤ k ≤ d − 1`,
  `a_k = q_{k−1} − x q_k ∈ [−x, 1]` hence `∈ {0, 1}`; `a_k = 1` gives `q_{k−1} = 1`, all other
  terms `0` (`Finset.sum_eq_single`-style), and then `a_{d−1} = q_{d−2} − x ∉ ℤ`; so `a_k = 0`;
  (iii) downward induction `q_k = x^{d−1−k}` (`k ≥ 1`); (iv) `q̃₀ = a_0(2x − 1)/x` gives
  `a_0 ≥ 0`, and `a_1 + 2a_0 ∈ (−1, 1)` gives `a_1 = −2a_0`; `a_0 ≠ 0` (else `x^d = 0`);
  (v) `Polynomial.ext`: coefficients of `P` and `gPoly d a_0` agree (`j > d`: both `0`).
  Work with `a_k : ℤ` and cast; integer squeezes by `Int.cast_lt` + `omega`.
* **`firstRowCond_gPoly`** (60), **`thmO_iff`** (10).

### §4 WythoffMirrorY: the recurrence (≈ 350 lines)

Theorem M is the dictionary `n ↦ −(s + 1)`, `W^i n + 1 ↦ −W′^i s`, `(yF1, yFodd) ↦ (ymF1, ymFeven)`.
* **`ymF1_mem`, `ymFeven_mem`** (40) as `yF1_mem`, `yFodd_mem` (`betaY_div_sub_one`).
* **`wy_betaY_iterate_three_phase`, `_four_phase`** (80): copy `wy_iterate_three_phase` /
  `_four_phase`: unfold, `s + 1 = 2k`, `linear_combination` with `g_mul_alphaY` and
  `yRoot_spec.2.2` (`check.py` confirms the exact identities, all parities).
* **`wy_betaY_iterate_three_sub_mem`** (40), **`wy_betaY_iterate_four_eq`** (80, docstring:
  `t = ±1`, `u = 2 − t` via `yPhase4_sub`, `yPhase4_of_one`, `yPhase4_of_neg_one`),
  **`exists_odd_iterate_Ym`** (20).
* **`le_wy_betaY_iterate_of_even_run`** (120): mirror sandwich as `WythoffLine.run_sandwich_mirror`
  (`v_1 ≥ A(s + 1) − 1`, `v_{i+1} > x v_i − 1`), `c_3 = A x³ > 1.474` from `yRoot_bounds`,
  `alphaY_bounds`; `s ≥ 5` by `nlinarith`; `s ∈ {1, 3}` by explicit floors
  (`W′(1) = ⌈α⌉ − 1 = 20`, `W′(20) = ⌊10β⌋ = 10`, `W′(10) = 5`; `W′(3) = 40`, `W′(40) = 21`).

### §5 WythoffMirrorY: classification, counts, density (≈ 700 lines)

* **`hyp_ymPerm`** (60), **`returnMap_ymPerm_ge`** (30), **`isOrbitMin_ymPerm_iff`** (15),
  **`minCount_ymPerm_add`** (25), **`minCount_ymPerm_ge`** (50),
  **`ymPerm_infinitelyManyInfiniteOrbits`** (30): copy `WythoffLine` §Mirror
  (`hyp_gmPerm`, …, `gmPerm_infinitelyManyInfiniteOrbits`) with `T = 4` and slope `4/3`
  (`#{odd s ≥ 1 : 4s ≤ 3X} = ⌊(3X + 4)/8⌋`).
* **`tendsto_minCount_ymPerm`** (450; last).  Copy Y's §Density (`yPh`, `yWord`,
  `yPh_mem_yWord`, `returnTime_yPerm_eq_iff`, `yReturn_bound`, `tendsto_returnCount_yPerm`) for
  `s = 2k − 1`: the phases are `({k c₀}, {k c₁})` again, and under Theorem M the mirror
  cylinders `O Eʲ` are Y's `E Oʲ` cylinders (same polygons), so the same `yVol j`, the same
  slopes `αxʲ/2` (now on `s + 1`), and `densityY_sum_eq` closes it.  Reuse Y's density lemmas
  where they are stated on abstract phases; a shared "cylinder density ⇒ minCount density"
  helper would serve Y, Y′ and G.

### §6 WythoffSeven (≈ 900 lines)

* **`wy_alphaP_eoo`** (80).  `W v + 1 = Av + G_E`, `W² v + 1 = x(W v + 1) + G′`,
  `W³ v + 1 = x(W² v + 1) + G″` (`G_E ∈ (0, 1]`, `G′, G″ ∈ [0, 1)`); with `A(2x − 1) = x` and the
  cubic, `W³ v − W² v + v = −(1 − x)(x G_E + G′) + G″ ∈ (−1, 1)`.
* **Labels** (`wy_alphaP_iterate_three_sub_mem` 150, `four_eq` 70, `five_eq` 30, `six_eq` 70,
  `seven_eq` 70): module docstring.  `K₃` needs the torus coordinates `ψ₀ = {kA}`,
  `ψ₁ = {kAx}` (`n = 2k`; `W n` odd iff `ψ₀ ≥ 1/2`, then `G_1 = 2 − 2ψ₀`; `W² n + 1 =
  2⌊kAx⌋ + ⌈2ψ₁ + xG_1⌉`), as in Y's `wy_two_mul_phase` / `wy_wy_two_mul_odd_iff`.  The later
  labels need only the box bounds and the recursion `K_{i+1} = xK_i + (xε_i − ε_{i+1}) + x − 1 +
  h_{i+1}` (`verify7.py` confirms the formula to `10⁻⁴⁵` and the ranges).
* **`minimalPeriod_alphaP_of_cyl`** (40): `Function.minimalPeriod_eq_prime` /
  `IsPeriodicPt.minimalPeriod_dvd` with `Nat.Prime 7` and `W n ≠ n` (parity).
* **`minimalPeriod_alphaP_twenty`** (80): seven explicit floors from `alphaP_mem`,
  `pRoot_bounds` (`Int.floor_eq_iff`, `Int.ceil_eq_iff`; e.g. `⌈94β⌉ = 108` from
  `94·1.1396805 = 107.13`), or `twenty_add_two_mul_mem_sevenCyl` at `q = 0`.
* **`exists_simultaneous_approx`** (120): pigeonhole, `Finset.exists_ne_map_eq_of_card_lt_of_maps_to`
  on `q ∈ [0, Q²]` ↦ `(⌊Q{qθ₁}⌋, ⌊Q{qθ₂}⌋) ∈ [0, Q)²`; difference `q − q′` (WLOG `q > q′`).
* **`infinite_simultaneous_approx`** (60): `Set.infinite_of_not_bddAbove` or by contradiction
  with a finite set's positive minimum (`Irrational.ne_int`-type facts for `qθ₁`).
* **`twenty_add_two_mul_mem_sevenCyl`** (200): docstring (translation; seven steps, each
  `⌊y + D + e⌋ = ⌊y⌋ + D` from a margin; `check.py` certifies the margins and the `10.16`
  coefficient).
* **`infinite_minimalPeriod_seven`** (30).

**Order of attack:** §1 → §2 (Theorem N is the engine; N(1) and N(2) via one real-sequence
helper) → §3 (Theorem O, the headline classification statement) → §6 labels and the 7-cycle
identity (a new, self-contained mechanism) → §6 infinitude → §4 → §5 except density → the Y′
density last.  If time is short, §1-§3 and §6 through `minimalPeriod_alphaP_twenty` are the
headline.

Rough total: 2,800-3,300 lines (Automaton ≈ 900, Y′ ≈ 1,050 of which density ≈ 450,
Seven ≈ 900).

**Out of scope (later layers):** Theorem A (needs the 2-adic Lemma 2 and the Weyl hull),
Theorem Q's unboundedness half, the zonotope criterion, Proposition F, the dynamical reading of
Theorem O ("runs never reach length `d`", needs Theorem N (4)'s uniform law), and the density of
the 7-cycle cylinder (an explicit polygon area in the `(ψ₀, ψ₁)` torus; measured `0.09427` of
the evens).
