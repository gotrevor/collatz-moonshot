# KICKOFF 2026-10-16: Theorem Y (sporadic cubic) and the golden member `α = 3 + √5`

Repo `collatz-moonshot` (branch `wip/wythoff-Y`, cut from `wip/wythoff-solvable` at `2769ba3`).
Close every `sorry` in two new files (52 statements):

| file | content | sorries |
|---|---|---|
| `CollatzMoonshot/WythoffSporadic.lean` | Theorem Y: `x³ + x² + 3x − 2`, the recurrence `W⁴ = 4n + W³ − W²` on `E O³` (phases + polygon), classification via Lemma P, count, density | 27 |
| `CollatzMoonshot/WythoffGolden.lean` | `α = 3 + √5 = alphaK 3 (−1)`: 3-cycles, the Sturmian trap `S′`, classification via Lemma P with `Φ` = the cycles, explicit minima, counts, densities | 25 |

**The four base files are being proved elsewhere.**  `MonotonePotential`, `WythoffGeneral`,
`WythoffCone`, `WythoffLine` are ratified-but-unproved (kickoff
`KICKOFF-2026-10-16-wythoff-solvable.md`, a separate treadmill on `wip/wythoff-solvable`); their
proofs will be merged in later.  **Use their statements as black boxes and do not edit them** (not
even to add a helper: put helpers in the new files).  In particular Lemma P
(`MonotonePotential`), `wy_pos_iff`, `wy_one`, `wy_lt_of_odd`, `lt_wy_of_even`,
`wy_two_mul(_sub_one)`, `coneSet_trap` and `wkPerm_infinitelyManyInfiniteOrbits` are available as
stated.  Expect their `sorry` warnings in your build output; only the two new files count.

Imports: `Mathlib`, `CollatzMoonshot.AmusicalTrap` (proved: `permOrbit`,
`InfinitelyManyInfiniteOrbits`), `MonotonePotential`, `WythoffGeneral` (both files) and
`WythoffCone` (Golden only).  Do not import `WythoffLine` or `WythoffQuadratic`; if you want
`WythoffLine`'s sandwich, reprove it for `alphaY` / `alphaK 3 (−1)` here.  Do not edit
`AmusicalTrap.lean` or any other existing file.

Sources: `~/personal/tmp/amusical-agents/out/wythoff-solvable.md` §4 (b3) (Theorem Y), §4 (b4)
and §9 (`3 + √5`); scripts `~/personal/tmp/amusical-agents/out/wythoff-solvable/` (`thmY.py`,
`ycert.py`, `trap35.py`).  Each new file's module docstring carries the full paper proof.

**Setup.**  `wy α n = ⌊(n/2)α⌋` (`n` even), `⌈((n+1)/2)β⌉ − 1` (`n` odd), `β = α/(α − 1)`.
*Y:* `yRoot` is the unique real root `x ≈ 0.5259574806` of `x³ + x² + 3x − 2` (`Classical.choose`,
pinned by `yRoot_spec` + `yRoot_unique`), `alphaY = 2x/(2x − 1) ≈ 20.26227`, `betaY = 2x`,
`yPerm = wyPerm alphaY`.  Phases: `yF1 n = (n/2)α − W n` (`∈ [0, 1)`), `yFodd v = x(v + 1) − W v`
(`∈ (0, 1]` for odd `v`); `yPhase3 = Δ′`, `yPhase4 t = Δ_t` (affine in the phases).
*Golden:* `goldPerm = wkPerm 3 (−1) _ _` (`α = 3 + √5 = 2 + 2φ`), `goldCycles = {z | W³ z = z}`,
`S′ = coneSet 3 (−1)`; `φ` is Mathlib's `Real.goldenRatio` (`open scoped goldenRatio`).

## Ratified, do not change

Every definition and theorem statement in the two files:

* **WythoffSporadic:** `yRoot`, `alphaY`, `betaY`, `yPhase3`, `yPhase4`, `yF1`, `yFodd`, `yPerm`,
  `densityY`; `yRoot_spec`, `yRoot_unique`, `yRoot_bounds`, `irrational_yRoot`,
  `linearIndependent_yRoot`, `alphaY_div_sub_one` (proved), `alphaY_cubic` (proved), `alphaY_mem`
  (proved), `one_lt_alphaY` (proved), `irrational_alphaY`, `yPhase3_mem`, `yPhase4_of_one`,
  `yPhase4_of_neg_one`, `yPhase4_sub` (proved), `yF1_mem`, `yFodd_mem`,
  `wy_iterate_three_phase`, `wy_iterate_four_phase`, `wy_iterate_three_sub_mem`,
  `wy_iterate_four_eq`, `exists_even_iterate_Y`, `le_wy_iterate_of_odd_run_Y`, `yPerm_apply`
  (proved), `hyp_yPerm`, `returnMap_yPerm_ge`, `permOrbit_yPerm_finite_iff`, `tendsto_yPerm_pow`,
  `tendsto_yPerm_pow_neg`, `isOrbitMin_yPerm_iff`, `minCount_yPerm_add`, `minCount_yPerm_ge`,
  `yPerm_infinitelyManyInfiniteOrbits`, `densityY_minpoly` (proved), `tendsto_minCount_yPerm`.
* **WythoffGolden:** `goldPerm`, `goldCycles`, `goldCycleMinCount`, `goldInfMinCount`;
  `alphaK_three_neg_one` (proved), `alphaK_three_neg_one_eq_gold` (proved), `goldPerm_apply`
  (proved), `wy_gold_two_mul`, `wy_gold_two_mul_even_iff`, `wy_gold_odd_of_odd`,
  `wy_gold_iterate_three`, `isOrbitMin_of_cycle_gold`, `goldCycleEvens_infinite`,
  `mem_coneSet_gold_iff`, `goldPerm_mapsTo_coneSet` (proved), `fract_gold_image`,
  `mem_image_coneSet_gold_iff`, `mem_goldCycles_iff`, `hyp_goldPerm`,
  `permOrbit_goldPerm_finite_iff`, `tendsto_goldPerm_pow`, `tendsto_goldPerm_pow_neg`,
  `exists_mem_orbit_mem_coneSet_gold`, `goldPerm_trichotomy`, `isOrbitMin_goldPerm_iff_pred`,
  `isOrbitMin_and_infinite_iff`, `isOrbitMin_and_finite_iff`, `isOrbitMin_goldPerm_iff`,
  `mem_coneEntry_gold_iff`, `goldPerm_infinitelyManyInfiniteOrbits` (proved),
  `minCount_goldPerm_eq`, `tendsto_goldCycleMinCount`, `tendsto_goldInfMinCount`,
  `tendsto_minCount_goldPerm`.

`WeylEquidistribution` and `WeylEquidistributionMulti` (in `WythoffGeneral`) are **literature
hypotheses**; they stay hypotheses of `tendsto_minCount_yPerm` and the three golden densities.  Do
not prove them and do not turn them into `axiom`s.  Everything else is unconditional, including
`linearIndependent_yRoot` (`deg x = 3`), so Y's density has no `hind` hypothesis, unlike G's.

## Rules

No `native_decide`, no axioms, no `maxHeartbeats` bumps.  Lean lines ≤ 100 characters.  **Never
change a ratified statement**; if one looks false, stop, record the counterexample in the
handoff and ask.  Commit after each proved lemma.  Notes as you go in `HANDOFF-wythoff-Y.md`.
Helper lemmas and definitions are welcome (above their first use).  Build with
`lake build CollatzMoonshot.WythoffSporadic CollatzMoonshot.WythoffGolden`.

## Truth checks already run

`tmp/drafter-Y/check.py` (gitignored; `python3 check.py`, 10 s, output `check.out`; `quick` mode
1 s).  Theorem Y: `x` isolated to a 384-bit integer interval by exact bisection, every floor
certified (both ends agree; odd-branch products certified non-integer).  Golden: exact `isqrt`
arithmetic in `ℚ(√5)`.  The Python `W` mirrors Lean's `wy` (`n // 2`, `(n + 1) // 2`, `% 2`,
`⌈·⌉ − 1` on the odd branch, all of `ℤ`).  **76 checks, 0 failures:**

* *Known-answer controls.*  Y: the Lemma P census at `X = 2·10⁶` is **786 811** minima besides
  `1` (the research note's number), and brute-force minima `1 < y ≤ 2·10⁴` number **7 867** (the
  note's).  Golden: the `isqrt` map equals the certified-interval map (`x = 1/φ`) pointwise on
  `[−10⁵, 10⁵]`; infinite-orbit minima `≤ 10⁶`: **154 509** (the note's), 3-cycle minima
  `250 000` (`≈ X/4`).
* *Y.*  Root, bounds, `α³ − 22α² + 36α − 16`, `densityY_minpoly`, closed form of `d` against
  `1/2 − (1/2)Σ P_j/c_j`; the polygon vertex values at both ends of the `x`-interval plus 20 000
  random rational phase points; `wy_iterate_three_phase` / `_four_phase` exactly (Fractions),
  **all parities**, `n ∈ [−3000, 3000] ∪ [10⁶, 10⁶ + 4000]`; `yF1_mem`, `yFodd_mem`; the
  recurrence on all 17 242 `E O³` points of `[−2·10⁵, 2·10⁵]` (negatives included); `t = ±1`,
  `u = t`; run bound; `4s ≤ 3R(s)` (min `R(s)/s = 1.4722` at `s = 72`) on every prefix of every
  run; (H1), `pos_iff`, bijectivity window; `isOrbitMin_yPerm_iff` = brute force for
  `1 < y ≤ 2·10⁴`; `minCount_yPerm_add` at every `X ≤ 6000` (Lean-faithful brute minima);
  `minCount_yPerm_ge` at every `X ≤ 2·10⁶`.
* *Golden.*  `wy_gold_two_mul`, parity iff, EO ⇒ EOO and `W³ = n` on all `E O` points of
  `[−2·10⁵, 2·10⁵]`; `S′` = Bohr set; `W(S′)` = `{2k : {kφ} < 1/(2φ²)}` on `[1, 4·10⁴]`;
  `fract_gold_image` exactly in `ℚ(√5)`; `Hyp` (desc, ret with `T = 1`, `mem_fix_iff`); positive
  `Φ` = `{1}` ∪ 3-cycles; all four minimum characterisations = brute force for `y ≤ 2·10⁴`;
  `mem_coneEntry_gold_iff`; `minCount_goldPerm_eq` at every `X ≤ 2·10⁴`; densities.
* **Teeth** (each must fail and does): the polygon lemma with `f₁ ≤ 1` closed (exact
  counterexample `f = (1, 1, 1, 1)`: `t = −1`, `u = −2`); return slope `3/2` (4303 failures);
  minimum test with 3 predecessors (582 mismatches); count without the `+1`; a Theorem-E-type
  density; perturbed cubic `x³ + x² + 3x − 2.001` (6258/6258 failures); recurrence with signs
  swapped; run bound 2; golden trap at threshold `0.6`; `Hyp` with `Φ = {1}`; minimum threshold
  `1/φ²`; image threshold `1/φ²`; the 3-cycle law for the neighbouring cone member
  `alphaK 4 (−2)`; infinite-orbit density `1/4`.

## Paper proofs

### §1 WythoffSporadic: root and parameters (≈ 200 lines)

* **`yRoot_spec`** (30).  IVT on `[1/2, 3/5]` (`F(1/2) = −1/8`, `F(3/5) = 0.176`), `dif_pos`.
* **`yRoot_unique`** (30).  `F(y) − F(x) = (y − x)(y² + xy + x² + y + x + 3)`, second factor
  `> 0` (`nlinarith`).  **`yRoot_bounds`** (20): `F` increasing, `norm_num` at the endpoints.
* **`irrational_yRoot`** (40).  Rational root theorem for the monic cubic, or: `x = p/q` in
  lowest terms gives `q ∣ p³`, so `q = 1`, and no integer lies in `(1/2, 3/5)`.
* **`linearIndependent_yRoot`** (60).  Irreducibility (no rational root of a cubic) ⇒
  `minpoly ℚ x` has degree 3 ⇒ `1, x, x²` independent (`minpoly.degree_le_of_ne_zero`, or
  `Fintype.linearIndependent_iff` and a degree argument).  **`irrational_alphaY`** (15).

### §2 WythoffSporadic: the polygon and the recurrence (≈ 450 lines)

* **Polygon lemmas** (150 total).  `yPhase3_mem`, `yPhase4_of_one`, `yPhase4_of_neg_one`: affine
  in `(f₁, f₂)` with coefficients polynomial in `x`; each bound is a Farkas certificate
  (docstrings give the multipliers) whose constant is positive by `yRoot_bounds`.  In Lean:
  `nlinarith` with the box constraints, their products with `x − 0.52595748` and
  `0.52595749 − x`, and the polygon constraint; or substitute the certificate explicitly.  The
  only tight point is `Δ_{−1}(1, 1) = −1`, excluded by `f₁ < 1` (use strict monotonicity in `f₁`).
* **`yF1_mem`, `yFodd_mem`** (40).  `Int.floor_le`, `Int.lt_floor_add_one`; for the odd branch
  `wy_two_mul_sub_one` and `alphaY_div_sub_one` (`jβ = x(v + 1)` for `v = 2j − 1`), then
  `Int.le_ceil`, `Int.ceil_lt_add_one`.
* **`wy_iterate_three_phase`, `wy_iterate_four_phase`** (80).  Pure algebra: unfold, write
  `n = 2k`, `(n/2 : ℤ) = k`, `alphaY = 2x/(2x − 1)`, `field_simp`, `linear_combination` with
  the cubic (the residual is a multiple of `n·(x³ + x² + 3x − 2)`).  No parity hypothesis.
* **`wy_iterate_three_sub_mem`** (40).  The integer `t` equals `Δ′ − f₃ ∈ (−2, 2)`.
* **`wy_iterate_four_eq`** (60).  `t` is odd (`W, W²` odd), so `t = ±1`; `u = Δ_t − f₄` via
  `yPhase4_sub`; `u ∈ (t − 1, t + 1)` by the polygon lemmas and `f₄ ∈ (0, 1]`, so `u = t`;
  `omega`/`linarith` to eliminate `t`.
* **`exists_even_iterate_Y`** (20).
* **`le_wy_iterate_of_odd_run_Y`** (120).  Sandwich helper (as `WythoffLine`'s `run_sandwich`):
  `y₁ = An`, `y_{i+1} = x(Wⁱn + 1)`; `W n = ⌊y₁⌋ > y₁ − 1`, odd steps `W^{i+1} = ⌈y_{i+1}⌉ − 1 ≥
  y_{i+1} − 1`, and `y_{i+1} ≥ x·yᵢ` — so `W^{j+1}(n) > c_j n − 1` with `c_j = A xʲ ≥ A x³ > 1.47`
  (`yRoot_bounds`).  `n ≥ 8`: `1.47n − 1 ≥ 4n/3`.  `n ∈ {2, 4, 6}`: `W(n) = 20, 40, 60`.

### §3 WythoffSporadic: classification and counts via Lemma P (≈ 300 lines)

As `WythoffLine` §6 (kickoff `wythoff-solvable` §6), with `T = 4` and slope `4/3`:
* **`hyp_yPerm`** (70).  `pos_iff` = `wy_pos_iff`; `mem_fix_iff` for `{1}` from `wy_one` and
  injectivity; `desc` = `wy_lt_of_odd` (`alphaY_mem`); `ret`: `τ` = 1 + the least `j` with
  `W^{j+1}` even (`exists_even_iterate_Y`, `Nat.find`), `τ ≤ 4`, `s < 4s/3 ≤ W^τ s`.
* **`returnMap_yPerm_ge`** (30) via `returnTime_spec`.  **Instances** (15 each):
  `permOrbit_yPerm_finite_iff`, `tendsto_yPerm_pow(_neg)`, `isOrbitMin_yPerm_iff`.
* **`minCount_yPerm_add`** (40), **`minCount_yPerm_ge`** (50: `#{k ≥ 1 : 8k ≤ 3X} = ⌊3X/8⌋`),
  **`yPerm_infinitelyManyInfiniteOrbits`** (30).

### §4 WythoffSporadic: density (≈ 500 lines; last, hardest)

* **`tendsto_minCount_yPerm`.**  `minCount = 1 + X/2 − Σ_{j ≤ 3} #{even s : word E Oʲ,
  R(s) ≤ X}`; on word `j`, `R(s) = c_j s + O(1)` (sandwich).  The word of `n = 2k` is a function
  of `(f₁, f₂)`, i.e. of `({k c_0}, {k c_1})` through a measure-preserving piecewise-affine map
  (`f₁ = {2kc_0}`; the parity of `W n` is `[{kc_0} ≥ 1/2]`, and on `E O` the next phase is
  `{k c_1 + affine(f₁)}`); the cylinders are polygons (null frontier).
  `WeylEquidistributionMulti` with `d = 2`, `θ = (c_0, c_1)`, independent by
  `linearIndependent_yRoot` (times `2x − 1`: `2x − 1, x, x²`), gives
  `P = (1/2, 1/4, 1/(4(1 + x)), x/(4(1 + x)))` (areas `|R_a| + |R_b| = x/(1 + x)` of the `E O O`
  square), and `d = 1/2 − (1/2)Σ P_j/c_j = densityY` (`field_simp` + the cubic).  Consider
  sharing the Weyl-to-counting bookkeeping with `WythoffLine.tendsto_minCount_gPerm` once that is
  proved (a general "cylinder density ⇒ minCount density" helper would serve both).

### §5 WythoffGolden: branch, 3-cycles, trap (≈ 600 lines)

* **`wy_gold_two_mul`, `wy_gold_two_mul_even_iff`** (50).  `wy_two_mul`,
  `alphaK_three_neg_one_eq_gold`, `Int.floor_intCast_add`; `⌊2y⌋ = 2⌊y⌋ + ⌊2{y}⌋`.
* **`wy_gold_odd_of_odd`** (120).  Module docstring: `j = k + ⌊kφ⌋ + 1 ≠ 0`,
  `W(v) = ⌊2jφ⌋ − 2j` (`wy_two_mul_sub_one`, `β = 2(φ − 1)`, `jβ ∉ ℤ` by
  `goldenRatio_irrational`), `{jφ} = {u(2 − φ) + φ} ≥ 0.809` (`goldenRatio_sq`,
  `Int.fract_eq_iff`).
* **`wy_gold_iterate_three`** (100).  Sandwich with `x = 1/φ = φ − 1`: `c_2 = 1`, `x + x² = 1`.
* **`isOrbitMin_of_cycle_gold`** (40), **`goldCycleEvens_infinite`** (80: the three-consecutive-`k`
  argument, `Set.infinite_of_not_bddAbove`).
* **`mem_coneSet_gold_iff`** (30), **`fract_gold_image`** (80), **`mem_image_coneSet_gold_iff`**
  (120: `⊇` constructs `k = ⌈k′/φ²⌉`).

### §6 WythoffGolden: classification and counts (≈ 900 lines)

* **`mem_goldCycles_iff`** (100), **`hyp_goldPerm`** (60), **`permOrbit_goldPerm_finite_iff`**
  (40: `x ∈ Φ` ⇒ orbit ⊆ `{x, W x, W² x}`; else `permOrbit_infinite`), **`tendsto_*`** (15
  each), **`exists_mem_orbit_mem_coneSet_gold`** (40), **`goldPerm_trichotomy`** (80).
* **Minima** (250): `isOrbitMin_goldPerm_iff_pred` (`isOrbitMin_iff` with `T = 1`,
  `zpow_neg_one`), then `isOrbitMin_and_infinite_iff` (`S′ ∖ W(S′)` via the two Bohr lemmas),
  `isOrbitMin_and_finite_iff`, `isOrbitMin_goldPerm_iff`, `mem_coneEntry_gold_iff`.
* **`minCount_goldPerm_eq`** (80).  `Finset.card` bijection `k ↦ 2k` plus the point `1`.
* **Densities** (250).  1D `WeylEquidistribution` with `θ = φ` at `N = ⌊X/2⌋` on `[1/2, 1)` and
  `[1/(2φ²), 1/2)`; `(N : ℝ)/X → 1/2`; the `+1` is `o(X)`.

**Order of attack:** §1 → §2 (the headline: a cubic member solved by a recurrence, via a
polygon certificate) → §3 → §5 → §6 except densities → §4 and the golden densities.  If time is
short, §2 + §3 and §5 + the golden minima are the headline; densities are last.

Rough total: 2,900-3,400 lines (Y ≈ 1,450, golden ≈ 1,500; densities ≈ 750 of it).

**Out of scope (later layers):** Y's mirror (`α ≈ 1.0519`; same density, COMPUTED only in the
research note, no proof written); the m ≥ 3 multinacci members (densities are polytope volumes
in the dependent phase torus, open); §9's degree-`d` trap identity and the `D = ±1` dictionary.
