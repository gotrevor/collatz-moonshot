# KICKOFF 2026-10-16: Lemma P, Theorems A′/K and Theorem G: the solvable Wythoff members

Repo `collatz-moonshot` (branch `wip/wythoff-solvable`, cut from `main` at `e734e06`).  Close
every `sorry` in four new files (80 statements):

| file | content | sorries |
|---|---|---|
| `CollatzMoonshot/MonotonePotential.lean` | Lemma P, abstract (orbit classification from a monotone potential) | 18 |
| `CollatzMoonshot/WythoffGeneral.lean` | `wy α` on `ℤ` for every real `α > 1`, bijection, steps; Weyl literature `Prop`s | 8 |
| `CollatzMoonshot/WythoffCone.lean` | Theorem A′ (EE identity), cone/anticone, Theorem K (trap, infinitely many infinite orbits) | 17 |
| `CollatzMoonshot/WythoffLine.lean` | Theorem G for all `m ≥ 0`, `r ≥ 2`: root, identity, classification, count, density; mirror | 37 |

Imports: `Mathlib`, `CollatzMoonshot.AmusicalTrap` (proved: `permOrbit`,
`InfinitelyManyInfiniteOrbits`, `infinitelyManyInfiniteOrbits_of_trap`), and each other
(`General` → `Cone`; `MonotonePotential` + `General` → `Line`).  It does **not** depend on
`WythoffQuadratic.lean` (Theorem F, proved in parallel on `wip/wythoff-thmF`, not on main); do not
import it.  Do not edit `AmusicalTrap.lean` or any other existing file.

Sources: `~/personal/tmp/amusical-agents/out/wythoff-solvable.md` (§1 Lemma P, §2 Theorem G,
§4(b4) the `3+√5` multinacci member), `~/personal/tmp/amusical-agents/out/wythoff-2adic.md` (§3
Theorem A′, Theorem K).  Style model: `WythoffQuadratic.lean` + `KICKOFF-2026-10-16-wythoff-thmF.md`
on `wip/wythoff-thmF` (Theorem F is the `m = 1` row of Theorem G and the `(b, c) = (2r, −r)`
point of Theorem K; its proofs transfer).

**Setup.**  `wy α n = ⌊(n/2)α⌋` (`n` even), `⌈((n+1)/2)β⌉ − 1` (`n` odd), `β = α/(α − 1)`.  With
`beattySeq'` on the odd branch, Rayleigh (`compl_beattySeq`, `Real.HolderConjugate.conjExponent`)
makes it a permutation of `ℤ` for **every** `α > 1`, rational or not.
*Cone:* `alphaK b c = b + √(b² + 4c)`, `x = α/2`, `x² = bx + c`, conjugate `x′ = b − x`.
*Line:* `gRoot m r` is the root `x ∈ (1/2, 3/4)` of `x^{m+1} − 2rx + r` (`Classical.choose`, pinned
by `gRoot_spec` + `gRoot_unique`), `alphaG = 2x/(2x − 1) = 2r/xᵐ`, `betaG = 2x`;
`gPerm = wyPerm alphaG`, mirror `gmPerm = wyPerm betaG`.

## Ratified, do not change

Every definition and theorem statement in the four files:

* **MonotonePotential:** `Hyp`, `IsOrbitMin`, `returnTime`, `returnMap`, `minCount`,
  `minCountOff`, `setCount`, `returnCount`; `permOrbit_subset_pos`, `permOrbit_subset_compl`,
  `returnTime_spec`, `returnMap_pos_not_mem`, `returnMap_injOn`, `exists_mem_orbit_mem`,
  `permOrbit_infinite`, `permOrbit_eq_singleton_of_fixed`, `permOrbit_finite_iff`,
  `tendsto_pow`, `tendsto_pow_neg`, `exists_isOrbitMin`, `isOrbitMin_iff`,
  `isOrbitMin_iff_returnMap`, `isOrbitMin_of_fixed`, `minCountOff_add_returnCount`,
  `minCount_add_returnCount`, `infinitelyManyInfiniteOrbits_of_minima`.
* **WythoffGeneral:** `wy`, `wyPerm`, `WeylEquidistribution`, `WeylEquidistributionMulti`;
  `wy_two_mul`, `wy_two_mul_sub_one`, `holderConjugate`, `wyPerm_apply` (these four proved),
  `wy_bijective`, `wy_pos_iff`, `wy_two_mul_sub_one_eq_floor`, `wy_one`, `lt_wy_of_even`,
  `wy_lt_of_odd`, `wy_lt_of_even`, `lt_wy_of_odd`.
* **WythoffCone:** `alphaK`, `wkPerm`, `coneSet`, `coneEntryCount`; `wy_wy_of_even_even`,
  `alphaK_half_sq`, `alphaK_two_mul_neg`, `three_lt_alphaK_cone`, `one_lt_alphaK_cone` (proved),
  `conj_mem_Ioo_cone`, `irrational_alphaK_cone`, `wkPerm_apply` (proved),
  `wy_wy_of_even_even_cone`, `coneSet_trap`, `wy_iterate_add_two_of_mem_coneSet`,
  `mem_coneEntry_iff`, `coneEntry_infinite`, `wkPerm_infinitelyManyInfiniteOrbits`,
  `tendsto_coneEntryCount`, `one_lt_alphaK_anticone`, `conj_mem_Ioo_anticone`,
  `irrational_alphaK_anticone`, `wy_wy_of_even_even_anticone`.
* **WythoffLine:** `gRoot`, `alphaG`, `betaG`, `gPerm`, `gmPerm`; `gRoot_spec`, `gRoot_unique`,
  `irrational_gRoot`, `gRoot_zero`, `alphaG_eq`, `alphaG_pow`, `four_le_alphaG`, `one_lt_alphaG`
  (proved), `one_lt_betaG_lt`, `one_lt_betaG` (proved), `alphaG_div_sub_one`, `betaG_div_sub_one`,
  `alphaG_zero`, `alphaG_one`, `gPerm_apply`, `gmPerm_apply` (proved), `wy_iterate_eq_of_odd_run`,
  `exists_even_iterate`, `le_wy_iterate_of_odd_run`, `wy_iterate_eq_of_even_run_mirror`,
  `hyp_gPerm`, `returnMap_gPerm_ge`, `permOrbit_gPerm_finite_iff`, `tendsto_gPerm_pow`,
  `tendsto_gPerm_pow_neg`, `isOrbitMin_gPerm_iff`, `minCount_gPerm_add`, `minCount_gPerm_ge`,
  `gPerm_infinitelyManyInfiniteOrbits`, `densityG_eq`, `tendsto_minCount_gPerm`, `hyp_gmPerm`,
  `returnMap_gmPerm_ge`, `permOrbit_gmPerm_infinite`, `tendsto_gmPerm_pow`,
  `tendsto_gmPerm_pow_neg`, `isOrbitMin_gmPerm_iff`, `minCount_gmPerm_add`, `minCount_gmPerm_ge`,
  `gmPerm_infinitelyManyInfiniteOrbits`, `tendsto_minCount_gmPerm`.

`WeylEquidistribution` and `WeylEquidistributionMulti` are **literature hypotheses** (Bohl,
Sierpiński, Weyl; the multidimensional one with the standard Jordan-measurable extension,
Kuipers-Niederreiter Ch. 1 §6).  They stay hypotheses of `tendsto_coneEntryCount`,
`tendsto_minCount_gPerm`, `tendsto_minCount_gmPerm`; do not prove them and do not turn them into
`axiom`s.  The `hind` hypothesis (`deg x = m + 1`) of the two G densities is a genuine
hypothesis (irreducibility is CONJ 90% in general; Eisenstein at any `p ∥ r`).  Everything else
is unconditional, including both `InfinitelyManyInfiniteOrbits` conclusions of the cone and the
line.

## Rules

No `native_decide`, no axioms, no `maxHeartbeats` bumps.  Lean lines ≤ 100 characters.  **Never
change a ratified statement**; if one looks false, stop, record the counterexample in the
handoff and ask.  Commit after each proved lemma.  Notes as you go in
`HANDOFF-wythoff-solvable.md`.  Helper lemmas and definitions are welcome (above their first use).
Build with `lake build CollatzMoonshot.WythoffLine` (pulls in the other three) or per file.
Gotcha (this Mathlib pin): `Finset.Icc` on `ℤ` in a *computable* `def` fails to compile; the
counting `def`s here are `noncomputable` with `open Classical in`, so this does not bite.

## Truth checks already run

`tmp/drafter-solvable/check.py` (gitignored; `python3 check.py`, 12 s, output `check.out`;
`quick` mode 5 s).  Exact integer arithmetic: every constant is a certified 384-bit interval,
every floor certified, the odd branch certified non-integer; rational members exact.  The Python
`W` mirrors Lean's `wy` (`n // 2`, `(n + 1) // 2`, `% 2`).  **420 checks, 0 failures:**

* *Known-answer controls.*  `G(1,2)` built by root isolation equals `K(4,−2)` built by `isqrt`
  pointwise on `[−10⁵, 10⁵]` (and `G(1,3) = K(6,−3)` on `[−5·10⁴, 5·10⁴]`); the Theorem F
  density at `X = 3·10⁵` is `0.3017800` (count 90534), equal to the thmF drafter's `0.301780`.
* *General.*  Bijectivity and `pos_iff` on windows for 21 members incl. rational `α = 2, 3, 7/2,
  4, 3/2` and all mirrors; the four step lemmas; `wy_one`.
* *Lemma P* on 17 instances (G and mirror for `(m,r) ∈ {(0,2),(0,3),(1,2),(1,3),(2,2),(2,3),
  (3,2),(4,2)}`, plus `3+√5` with `Φ` = its 3-cycles, a **non-fixed invariant** `Φ`): `Hyp` on
  `[−2·10⁴, 2·10⁴]`; orbit windows (both tails pass `x·2²⁴`) for `x ≤ 1500-3000`: finite orbits
  exactly `Φ`, `isOrbitMin_iff`, `isOrbitMin_iff_returnMap`, `returnMap_injOn`, and both count
  identities at **every** `X ≤ 1500-3000`.
* *Theorem G.*  Root facts and `alphaG_eq/pow/div`, `densityG_eq` to `10⁻⁶⁰`; `alphaG_one`
  against `2r + 2√(r² − r)`; the identity on every even `n ∈ [−N, N]` (`N` up to `10⁵`, 1562-50001
  instances per member, 0 failures), negatives included; `le_wy_iterate_of_odd_run`,
  `exists_even_iterate`, `returnMap ≥ rs`, `minCount_gPerm_ge` at every `X`; the mirror identity
  (all odd `n`), `R′(s) ≥ r(s + 1) − 1`, `minCount_gmPerm_ge`.  Densities (characterisation
  count): `G(1,2)` `0.301780`/`0.301777` (main/mirror) vs `d = 0.301777` at `3·10⁵`; `G(2,2)`
  `0.367437`/`0.367420` vs `0.367460` at `3·10⁵`; `G(3,2)` `0.41846`/`0.41838` vs `0.41842` at
  `10⁵`; `G(0,2)` exact.
* *Theorems A′/K.*  A′ on every EE point `k ∈ [−5·10⁴, 5·10⁴]` for 10 cone, 7 anticone and 6
  other members (`2√2`, `2√3`, `1+√13`, `1+√21`, `−1+√13`, `2+2√5`), with `⌊x′{kα}⌋` certified:
  0 failures; cone identity 0 failures; anticone identity (`k ≠ 0`) 0 failures; the cone/anticone
  discriminant is never a square for `b < 80`; trap on `[1, 4·10⁴]`, the recurrence, and
  `mem_coneEntry_iff` against the forward image `W(T)` on `[1, 2·10⁴]`: 0; entry densities at
  `2·10⁵`: `0.154505, 0.183020, 0.176775, 0.195195, 0.202255` vs `(1 − 2/α)/4` to `≤ 7·10⁻⁶`.
* **Teeth** (each must fail and does): the floor (not `⌈·⌉ − 1`) odd branch collides on `ℤ`
  (irrational and rational `α`); a perturbed root `x³ − 4x + 2.001` breaks the identity (4988
  of 4993 EOO points); the mirror identity without `−1`; the run bound `m − 1` (EOO occurs);
  the minimum test with `T − 1` predecessors (22-376 mismatches per member); the count without
  the `#Φ` term (off at every `X`, Theorem F's lesson); the count with the one-step image `W(S)`
  in place of `R(S)`; Theorem A′ with `x` in place of `x′`; the cone identity on anticone and
  non-cone members, the anticone identity on cone members; the trap for `1 + √5`.

## Paper proofs

### §1 WythoffGeneral (≈ 300 lines)

* **`wy_bijective`** (110).  As `WythoffQuadratic.wq_bijective`: the even branch `k ↦ ⌊kα⌋` is
  `beattySeq α`, the odd branch `k ↦ ⌈kβ⌉ − 1` is `beattySeq' β`; both strictly increasing in
  `k` (`α, β > 1`: `⌊(k+1)α⌋ ≥ ⌊kα + 1⌋`, `Int.floor_mono` / `Int.ceil_mono` plus strictness from
  the slope `> 1`); no cross collision and joint surjectivity from
  `compl_beattySeq (holderConjugate hα)`.
* **`wy_pos_iff`** (40).  `n = 2k` or `2k − 1`.  `k ≥ 1`: `⌊kα⌋ ≥ ⌊k⌋ = k`, `kβ > 1` so
  `⌈kβ⌉ ≥ 2`.  `k = 0`: `0`, `−1`.  `k < 0`: `kα < 0` so `⌊kα⌋ ≤ −1`; `kβ < 0` so `⌈kβ⌉ ≤ 0`.
* **`wy_two_mul_sub_one_eq_floor`** (25).  `β = 1 + 1/(α − 1)` is irrational, so `kβ ∉ ℤ` for
  `k ≠ 0` and `⌈kβ⌉ = ⌊kβ⌋ + 1` (`Int.ceil_eq_iff`, `Irrational.ne_int`).
* **Steps** (25 each).  `wy_one`: `1 < β ≤ 2`.  `lt_wy_of_even` (`α ≥ 3`): `⌊kα⌋ ≥ 3k`.
  `wy_lt_of_odd` (`α ≥ 3` ⇒ `β ≤ 3/2`): `jβ ≤ 2j − 1` for `j ≥ 2`, so `⌈jβ⌉ − 1 ≤ 2j − 2`.
  `wy_lt_of_even` (`α < 2`): `⌊kα⌋ ≤ kα < 2k`.  `lt_wy_of_odd` (`1 < α < 2` ⇒ `β > 2`):
  `⌈kβ⌉ ≥ 2k + 1`.

### §2 MonotonePotential, Lemma P (≈ 900 lines; the reusable core)

Notation `x_t = (σ ^ t) x`, `t : ℤ`; `permOrbit σ x = range (t ↦ x_t)`.  Useful first helpers:
`σ ^ (n : ℕ)` vs `zpow`, positivity along the orbit (`pos_iff` both ways, `Int.induction_on`),
and orbit-avoids-`Φ` (`mem_fix_iff` both ways).

* **`permOrbit_subset_pos`, `permOrbit_subset_compl`** (20 each).
* **`returnTime_spec`** (40).  Unfold the `dite`; (H2)'s `τ` witnesses existence;
  `Nat.find_min'` gives `returnTime ≤ τ`, and the intermediate-`∉ S` clause of (H2) forces
  equality (`Nat.find_spec` lands in `S`, so it cannot be `< τ`).
* **`returnMap_pos_not_mem`** (10).  `s < R(s)` and the two orbit helpers.
* **`returnMap_injOn`** (40).  `R(s) = R(s') = y`, `τ(s) < τ(s')`: then
  `s = σ^{τ(s') − τ(s)} s'` (apply `(σ ^ τ(s))⁻¹`) is an intermediate point of `s'`'s return,
  yet `s ∈ S`.
* **Key helper: forward `S`-visits** (80).  For `s ∈ S ∖ Φ`, `s > 0`, define `sₖ = Rᵏ(s)`
  (well-defined by `returnTime_spec` + `returnMap_pos_not_mem`), `sₖ ≥ s + k`, and every point
  `σ^i s` with `Σ_{l<k} τ(s_l) ≤ i` lies `≥ s_k` (intermediate points decrease to the next
  visit by (H1)).  Gives `tendsto_pow` and the forward half of "every point `> y*`".
* **`exists_mem_orbit_mem`** (50).  Otherwise every forward point is positive, off `S ∪ Φ`, so
  `σ^(n+1) x < σ^n x` for all `n`: an infinite strictly decreasing sequence in `ℕ⁺`
  (`StrictAnti` + `Nat`-valued bound, or `WellFounded`).
* **`permOrbit_infinite`** (30).  The forward `S`-visits are strictly increasing, hence pairwise
  distinct orbit points.  **`permOrbit_eq_singleton_of_fixed`** (15), **`permOrbit_finite_iff`**
  (15).
* **First `S`-visit `y*`** (100).  The set of times `t` with `x_t ∈ S` is nonempty and bounded
  below: if `t < t'` are consecutive visits then `x_t < x_{t'}` (first return), so going
  backward the visited values strictly decrease in `ℕ⁺`; at most `x_{t₀}` visits before `t₀`.
  Let `t*` be the least visit time.  Before `t*` every point is off `S ∪ Φ`, so read backward
  the values strictly increase (`desc`): `x_{t* − n} ≥ y* + n`.  Gives `tendsto_pow_neg` (80)
  and, with the forward helper, `exists_isOrbitMin` (`y*`, 40).
* **`isOrbitMin_iff`** (100).  `→`: a minimum is `y*` (every other point exceeds `y*`), which is
  in `S` with all predecessors off `S`.  `←`: if `x ∈ S` has `T` predecessors off `S` but
  `x ≠ y*`, the last visit `s'` before `x` has `R(s') = x` at distance `τ(s') ≤ T`
  (`returnTime_spec`): contradiction.  So `x = y*`.
* **`isOrbitMin_iff_returnMap`** (60).  Same, phrased with `R`: `x = R(s')` iff `x` has an
  earlier `S`-visit.  **`isOrbitMin_of_fixed`** (10).
* **`minCountOff_add_returnCount`** (150).  Filter of `minCountOff` =
  `((S ∖ Φ) ∩ [1, X]) \ image R F` with `F` the `returnCount` filter (`R(s) ≤ X` ⇒ `s < X`;
  `isOrbitMin_iff_returnMap`); `image R F ⊆ (S ∖ Φ) ∩ [1, X]`; `Finset.card_sdiff`,
  `Finset.card_image_of_injOn` (`returnMap_injOn`).
* **`minCount_add_returnCount`** (40).  Minima in `[1, X]` = `Φ ∩ [1, X]` ⊔ off-`Φ` minima
  (`isOrbitMin_of_fixed`); `Finset.filter_or`, disjoint union.
* **`infinitelyManyInfiniteOrbits_of_minima`** (40).  `permOrbit` is injective on minima (two
  minima of one orbit are `≤` each other); image of an infinite set; each orbit infinite.

### §3 WythoffCone (≈ 750 lines)

* **`wy_wy_of_even_even`** (50).  `wy_two_mul`; write `W(2k) = 2j`, `f = kα − 2j ∈ [0, 1)`
  (`Int.fract`); `W(2j) = ⌊jα⌋` and `jα = (kα − f)·(α/2) = b·2j + 2kc + f(b − α/2)` using
  `(α/2)² = b(α/2) + c`; `Int.floor_intCast_add`.
* **`alphaK_half_sq`** (10, `Real.sq_sqrt`), **`alphaK_two_mul_neg`** (15:
  `√(4r² − 4r) = 2√(r² − r)`).
* **`three_lt_alphaK_cone`, `conj_mem_Ioo_cone`** (40).  `b ≥ 3`; `(b − 2)² < b² + 4c < b²` gives
  `b − 2 < √D < b` (`Real.lt_sqrt`, `Real.sqrt_lt'`).  Anticone mirror: `b < √D < b + 2`.
* **`irrational_alphaK_cone/_anticone`** (50).  `irrational_sqrt_intCast_iff` /
  `irrational_sqrt_natCast_iff` (`D > 0`); a square root `s` would satisfy `b − 2 < s < b`, so
  `s = b − 1`, and `(b − 1)² = b² + 4c` gives `1 − 2b ≡ 0 (mod 4)`; `omega`.
* **`wy_wy_of_even_even_cone`** (20).  A′ with `⌊x′f⌋ = 0` (`0 ≤ x′f < 1`).
  **`wy_wy_of_even_even_anticone`** (30).  `f > 0` (`kα ∉ ℤ`, `k ≠ 0`), `−1 < x′f < 0`.
* **`coneSet_trap`** (20), **`wy_iterate_add_two_of_mem_coneSet`** (40, induction on `j` with the
  trap), **`mem_coneEntry_iff`** (40: `Equiv.symm_apply_eq`, `wy_pos_iff`).
* **`coneEntry_infinite`** (200).  By contradiction: if the entry set `E` is finite, every
  `t ∈ T` is `Wʲ(e)` for some `e ∈ E` (backward from `t` inside `T` the values strictly decrease,
  `lt_wy_of_even`, so the backward orbit leaves `T`, and its last `T`-point is an entry); on `T`,
  `W(t) ≥ (3/2)t − 1 ≥ (5/4)t` for `t ≥ 4`, so `#(T ∩ [1, X]) ≤ |E|·(log_{5/4} X + 2)`.  Lower
  bound: `T` is syndetic.  Dirichlet (`Real.exists_int_int_abs_mul_sub_le`) gives `q ≥ 1` with
  `δ = |qα/2 − p| ∈ (0, 1/4)` (`> 0` by irrationality); along `k, k + q, k + 2q, …` the phase
  `{kα/2}` moves monotonically by `δ` mod 1, so within `⌈1/δ⌉ + 1` steps it lies in `[0, 1/2)`,
  i.e. `⌊kα⌋` even.  So `#(T ∩ [1, X]) ≥ X/(2q(⌈1/δ⌉ + 1)) − 1`, linear, contradiction.
* **`wkPerm_infinitelyManyInfiniteOrbits`** (20).  `infinitelyManyInfiniteOrbits_of_trap`.
* **`tendsto_coneEntryCount`** (200).  `coneEntryCount = #(T ∩ [1, X]) − #(W(T) ∩ [1, X])`
  (`W(T) ⊆ T`).  `#(T ∩ [1, X]) = #{k ≤ X/2 : {k·α/2} ∈ [0, 1/2)}`, Weyl with `θ = α/2` →
  `X/4`.  `#(W(T) ∩ [1, X]) = #{k ≥ 1 : ⌊kα⌋ even, ⌊kα⌋ ≤ X}` (`W` injective on `T`) and
  `⌊kα⌋ ≤ X ⟺ k ≤ (X + 1)/α` up to one term → `X/(2α)`.  Limit `1/4 − 1/(2α)`.

### §4 WythoffLine: root and parameters (≈ 300 lines)

* **`gRoot_spec`** (40).  IVT (`intermediate_value_Ioo'` or `IsPreconnected.intermediate_value`)
  on `F(t) = t^{m+1} − r(2t − 1)`, `F(1/2) > 0`, `F(3/4) < 0` (`(3/4)^{m+1} ≤ 3/4 < r/2`), then
  unfold `gRoot` (`dif_pos`, `Classical.choose_spec`).
* **`gRoot_unique`** (50).  Two roots `y₁ < y₂` in `(1/2, 1)`: `F` convex (`ConvexOn.pow` +
  affine), `F(y₁) = F(y₂) = 0 > F(1) = 1 − r` contradicts convexity on `[y₁, 1]` (`y₂` strictly
  between).  Or: `F(1/2) > 0 = F(y₁)`, so by convexity `F < 0` on `(y₁, 1]`.
* **`irrational_gRoot`** (40).  A rational root `p/q` (lowest terms) of a monic integer
  polynomial has `q = 1` (`p^{m+1} = q(…)`, coprimality); an integer is not in `(1/2, 3/4)`.
* **`gRoot_zero`** (15) via `gRoot_unique`.  **`alphaG_eq`, `alphaG_pow`, `alphaG_div_sub_one`,
  `betaG_div_sub_one`, `alphaG_zero`** (60 total, `field_simp` with `x^{m+1} = r(2x − 1)`).
  **`four_le_alphaG`** (20: `xᵐ ≤ 1`).  **`one_lt_betaG_lt`** (5).
* **`alphaG_one`** (40).  `y = r − √(r² − r)` solves `y² = r(2y − 1)` and lies in `(1/2, 3/4)`
  (as `WythoffQuadratic.sqrt_radicand_gt/lt`); `gRoot_unique`; then `2r/y`.

### §5 WythoffLine: the identities (≈ 350 lines)

**Sandwich** (module docstring): put `y₁ = An` (`A = α/2`), `y_{i+1} = x(Wⁱn + 1)`.  The even
step is `⌊y₁⌋`, the odd steps `⌈y_{i+1}⌉ − 1` (`wy_two_mul_sub_one` with `(v + 1)/2·β = x(v + 1)`).
Then `x·y₁ < y₂ ≤ x·y₁ + x` and `x·yᵢ ≤ y_{i+1} < x·yᵢ + x`, so
`c_j n < y_{j+1} ≤ c_j n + Σ_{l=1}^{j} xˡ`.  **No irrationality is needed**: at `j = m`,
`rn < y_{m+1} < rn + 1`, so `⌈y_{m+1}⌉ − 1 = rn` (`Int.ceil_eq_iff`).

* **Helper `run_sandwich`** (120).  State and prove the two-sided bound by induction on `j`
  (`Function.iterate_succ_apply'`), as reals, for `n` even with `W¹..Wʲ` odd.
* **`wy_iterate_eq_of_odd_run`** (40).  `j = m`; `Σ_{l=1}^{m} xˡ < 1` from
  `x(1 − xᵐ) < 1 − x ⟺ 2x − 1 < x^{m+1}` (geometric sum, `r ≥ 2`).  `m = 0` separately:
  `⌊n·r⌋ = rn` via `alphaG_zero`.
* **`exists_even_iterate`** (20).  If `W¹..Wᵐ` are odd, `W^{m+1} = rn` is even; else take the
  first even one.
* **`le_wy_iterate_of_odd_run`** (30).  `c_j = r x^{j−m} ≥ r`, `n > 0`.
* **`wy_iterate_eq_of_even_run_mirror`** (100).  Same sandwich: `v₁ = ⌈kα⌉ − 1 ∈ [y − 1, y)`,
  `y = A(n + 1)`, even steps `xv − 1 < ⌊xv⌋ ≤ xv`; `r(n + 1) − 2 < v_{m+1} < r(n + 1)`.

### §6 WythoffLine: classification and counts via Lemma P (≈ 400 lines)

* **`hyp_gPerm`** (60).  `pos_iff`: `wy_pos_iff`.  `mem_fix_iff` for `{1}`: `W(1) = 1` and
  injectivity.  `desc`: `wy_lt_of_odd` (`α ≥ 4`; `z ∉ evens ∪ {1}` means odd `≥ 3`).  `ret`:
  let `τ − 1` be the number of odd points before the first even one (`exists_even_iterate`,
  `Nat.find`), `τ ≤ m + 1`, and `s < rs ≤ W^τ(s)` (`le_wy_iterate_of_odd_run`).
* **`returnMap_gPerm_ge`** (30).  `returnTime_spec` identifies `returnMap` with that `W^τ(s)`.
* **`permOrbit_gPerm_finite_iff`, `tendsto_gPerm_pow(_neg)`, `isOrbitMin_gPerm_iff`** (15 each).
  Lemma P instances; translate `{n | n % 2 = 0}` membership.
* **`minCount_gPerm_add`** (40).  `minCount_add_returnCount`; `setCount {1} X = 1`
  (`X ≥ 1`), `setCount (evens \ {1}) X = X/2` (`Int.card_filter_Icc`-style counting, or a
  bijection with `Finset.Icc 1 (X/2)`, `k ↦ 2k`).
* **`minCount_gPerm_ge`** (50).  `returnCount ≤ #{even s ∈ [1, X] : rs ≤ X} = X/(2r)`.
* **`gPerm_infinitelyManyInfiniteOrbits`** (30).  `minCount_gPerm_ge` is unbounded (`r ≥ 2`), so
  the minima `> 1` are infinite; `infinitelyManyInfiniteOrbits_of_minima`.
* **Mirror** (150): `hyp_gmPerm` (`Φ = ∅`; `desc` is `wy_lt_of_even`, `β < 3/2`; `ret` via the
  mirror sandwich at `j ≤ m`, which gives `R′(s) ≥ r(s + 1) − 1 > s`), then the same instances;
  `minCount_gmPerm_add` with `setCount ∅ = 0` and `#odds ∩ [1, X] = (X + 1)/2`;
  `minCount_gmPerm_ge` with `R′(s) ≥ r(s + 1) − 1`.

### §7 Densities (≈ 700 lines; last, hardest)

* **`densityG_eq`** (20).  `α = 2r/xᵐ`, `β = 2x`, `field_simp`.
* **`tendsto_minCount_gPerm`** (450).  From `minCount_gPerm_add`,
  `minCount = 1 + X/2 − Σ_{j ≤ m} #{even s : word E Oʲ, R(s) ≤ X}`.  On word `j`,
  `R(s) = c_j s + O(1)` (sandwich), so the `j`-th term is `D_j X/c_j + o(X)` once the word
  frequency `D_j` exists.  Frequencies: with `n = 2k`, the parity of `Wⁱ(n)` along the run is
  `[{φ_{i−1}} ≥ 1/2]` with `φ_0 = {k c_0}`, `φ_i = {k c_i + h_i(φ_0, …, φ_{i−1})}`,
  `h_i` piecewise affine; the map `({kc_0}, …, {kc_{m−1}}) ↦ (φ_0, …, φ_{m−1})` is a triangular
  measure-preserving bijection of `[0, 1)ᵐ`, so each word cylinder is (the preimage of) a box,
  a set with Lebesgue-null frontier.  `WeylEquidistributionMulti` with `θ_i = c_i`, independent
  by `hind` (multiply by `2x − 1`), gives `D_j = 2^{−j−2}` (`j < m`), `D_m = 2^{−m−1}`;
  `d = 1/2 − Σ_j D_j/c_j = β^{−m}/2 − 1/(αβᵐ) = (α − 2)/(2αβᵐ)`.  Consider first proving the
  `m ≤ 1` cases (no or one phase) to shake out the bookkeeping.
* **`tendsto_minCount_gmPerm`** (200).  Same phases, parities swapped.

**Order of attack:** §1 → §2 (Lemma P is the reusable core; it also re-proves Theorem F's
classification in one line) → §3 except `coneEntry_infinite`/density → §4 → §5 → §6 (the
headline: an infinite family of irrational members, every degree `m + 1`, with complete orbit
classification) → `coneEntry_infinite` → §7.  If time is short, §5 + §6 for general `m` are the
headline, and §2 is what makes §6 short.

Rough total: 3,000-3,800 lines (§7 ≈ 700 of it).

**Out of scope (later layers):** Theorem Y (sporadic cubic `x³ + x² + 3x − 2`), the `3+√5`
Sturmian-trap classification, research note `wythoff-solvable` §9 addendum (degree-`d` trap
identity on `E^d`, the `D = ±1` dictionary for K members).
