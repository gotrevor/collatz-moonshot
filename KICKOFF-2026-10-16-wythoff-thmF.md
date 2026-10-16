# KICKOFF 2026-10-16: Theorem F, the quadratic Wythoff members `α = 2r + 2√(r² − r)` are solved

Repo `collatz-moonshot-amusical-zcore` (branch `wip/wythoff-thmF`): close every `sorry` in
`CollatzMoonshot/WythoffQuadratic.lean` (51 statements).  It imports only `Mathlib` and
`CollatzMoonshot/AmusicalTrap.lean` (proved: `permOrbit`, `InfinitelyManyInfiniteOrbits`,
`infinitelyManyInfiniteOrbits_of_trap`).  Do not edit `AmusicalTrap.lean`, `Amusical.lean` or
any other existing file.  It does **not** depend on `WythoffRational*.lean` (proved in parallel
elsewhere, not on main); do not import it.

Sources: research note `~/personal/tmp/amusical-agents/out/wythoff-2sqrtm.md` (§1 Theorem D, §4
Theorem F and its proof), `~/personal/tmp/amusical-agents/out/wythoff.md` §1 (the family
`W_α(2k) = ⌊kα⌋`, `W_α(2k−1) = ⌊kβ⌋`, `β = α/(α−1)`).  Ren's independent checks
`~/personal/tmp/ren-wythoff/thmF.py`, `thmF_count2.py`.

**Setup.**  `r ≥ 2`, `m = r² − r` (never a square: `(r−1)² < m < r²`), `α = 2r + 2√m`,
`β = 2r − 2√m = α/(α − 1) ∈ (1, 6/5)`, `α + β = αβ = 4r`.  `s(k) := sfl r k = ⌊2k√m⌋`
(computable: `Nat.sqrt (4k²m)` for `k ≥ 0`, `−Nat.sqrt (4k²m) − 1` for `k < 0`).  On all of `ℤ`:
`W(2k) = 2rk + s(k) = ⌊kα⌋`, `W(2k − 1) = 2rk − s(k) − 1 = ⌈kβ⌉ − 1` (`= ⌊kβ⌋` for `k ≠ 0`).
The ceiling on the odd branch is what makes `W` a permutation of `ℤ` (with `⌊0·β⌋` both `W(0)`
and `W(−1)` would be `0`).  Partner `W'` (`α ↔ β`): `W'(2k) = 2rk − s(k) − 1`,
`W'(2k − 1) = 2rk + s(k)`, i.e. `W' = W ∘ (2k ↔ 2k − 1)`.

## Ratified, do not change

Every definition and theorem statement in `WythoffQuadratic.lean`:
definitions `sqrtPart`, `sfl`, `wq`, `wqp`, `alphaQ`, `betaQ`, `wqPerm`, `wqpPerm`, `IsEntry`,
`countA`, `countB`, `minCount`, `SflOddDensityHalf`, `IsEntryP`, `countAP`, `countBP`,
`minCountP`; theorems
`wq_two_mul`, `wq_two_mul_sub_one`, `wqp_two_mul`, `wqp_two_mul_sub_one`, `wqp_eq_wq`,
`irrational_sqrt`, `alphaQ_add_betaQ`, `alphaQ_mul_betaQ`, `one_lt_betaQ_lt`,
`alphaQ_holderConjugate`, `sfl_eq_floor`, `wq_two_mul_eq_floor`, `wq_two_mul_sub_one_eq_ceil`,
`wq_two_mul_sub_one_eq_floor`, `wqp_two_mul_eq_floor`, `wqp_two_mul_sub_one_eq_floor`,
`wq_bijective`, `wqPerm_apply` (proved, `rfl`), `wq_pos_iff`, `wqp_bijective`, `wqpPerm_apply`
(proved, `rfl`), `wqp_pos_iff`, `wq_wq_of_odd`, `wqp_wqp_of_even`, `wq_one`,
`wq_two_mul_bounds`, `wq_two_mul_sub_one_bounds`, `wqp_bounds`, `isEntry_iff`,
`permOrbit_subset_pos`, `permOrbit_wqPerm_one`, `existsUnique_isEntry_mem_orbit`,
`isEntry_lt_of_mem_orbit`, `permOrbit_wqPerm_infinite`, `tendsto_wqPerm_pow`,
`tendsto_wqPerm_pow_neg`, `isOrbitMin_iff`, `permOrbit_bijOn`,
`wqPerm_infinitelyManyInfiniteOrbits`, `minCount_add_countB`, `minCount_ge`, `minCount_le`,
`tendsto_minCount`, `isEntryP_iff`, `existsUnique_isEntryP_mem_orbit`,
`isEntryP_lt_of_mem_orbit`, `permOrbit_wqpPerm_infinite`, `tendsto_wqpPerm_pow`,
`tendsto_wqpPerm_pow_neg`, `isOrbitMinP_iff`, `wqpPerm_infinitelyManyInfiniteOrbits`,
`minCountP_add_countBP`, `tendsto_minCountP`.

`SflOddDensityHalf` is a **literature hypothesis** (equidistribution of `k√m` mod 1: Bohl,
Sierpiński, Weyl; not in Mathlib).  It stays a hypothesis of `tendsto_minCount` /
`tendsto_minCountP`; do not prove it and do not turn it into an `axiom`.  Everything else is
unconditional.

No `native_decide`, no axioms, no `maxHeartbeats` bumps.  Lean lines ≤ 100 characters.  Do
**not** edit `RESEARCH-*.md`.  Commit after each proved lemma.  Notes as you go in
`HANDOFF-wythoff-thmF.md`.  Helper lemmas and definitions are welcome (put them above their
first use).  Any cleaner route is fine as long as the ratified statements are unchanged.  Build
with `lake build CollatzMoonshot.WythoffQuadratic`.

⚠️ **Gotcha (this Mathlib pin):** `Finset.Icc (a : ℤ) b` in a *computable* `def` fails to compile
(the instance goes through the noncomputable `Int.instConditionallyCompleteLinearOrder`).  That is
why `countA`/`countB`/`countAP`/`countBP` index over `Finset.Icc 1 X : Finset ℕ` with casts; in
proofs, `Finset.Icc` on `ℤ` is fine.

**Order of attack:** §1 → §2 → §3 → §4 (the core: Theorem F classification; its last item
needs `minCount_ge` from §5) → §5 → §6 (skeleton reuse for the partner).  If time is short,
§4 alone is the headline (first irrational member of the family with a formal complete orbit
classification).

**Truth checks already run** (`tmp/drafter-thmF/check.py`, output `check.out`, 15 s; an exact
Python mirror of `sfl`/`wq`/`wqp`, Lean `#eval` agrees on samples, `tmp/drafter-thmF/E.lean`):
for `r = 2..6`: bridges against 80-digit `Decimal` floors/ceilings for `|k| ≤ 3000` (0 failures);
bijectivity and `pos_iff` of `wq`, `wqp` on `[−60000, 60000] → [−20000, 20000]` (0);
`wqp_eq_wq` (0); Theorem D and partner D for `|k| ≤ 10⁵` (0 of 200,001 hits each); all step
bounds for `k ≤ 10⁵` (0); orbit classification by orbit **windows** (40 steps each way, minimum
found without using the entry criterion) for `x ≤ 3000`: unique entry point per orbit, it is the
minimum, backward tail odd and strictly increasing, forward even points increasing, `isEntry_iff`
predecessor form (0); same for the partner (0); exact counts `1 + A − B` and `A′ − B′` against
the window minima for `X ≤ 4000` (0), `minCount_ge`/`minCount_le` bounds (0); density at
`X = 3·10⁵`: `0.301780` vs `d_2 = 0.301777`, `0.370800` vs `d_3 = 0.370791`; `sfl` odd frequency
`0.49999` at `N = 2·10⁵`.  **Teeth** (each fails as it must): `r = 1` (square `m`) breaks
`sfl_eq_floor` (50 failures); the floor (not ceiling) odd branch collides at `0`; Theorem D with
`√(r² − r + 1)` fails 9,999 times; the entry criterion without the second-predecessor clause
misclassifies 249 points; the note's literal count `A(X) − B(X)` (omitting the orbit `{1}`) is off
by one at every `X` (so the ratified count is `1 + A − B`).

## Paper proofs (Ren)

### §1 Branches and the real bridge (≈ 330 lines)

* **`wq_two_mul`, `wq_two_mul_sub_one`, `wqp_two_mul`, `wqp_two_mul_sub_one`** (5 each).
  `unfold wq; rw [if_pos (by omega)]`, `(2 * k) / 2 = k` and `(2 * k - 1 + 1) / 2 = k` by `omega`;
  `push_cast; ring`.
* **`wqp_eq_wq`** (15).  Split on `n % 2`; `n = 2k` gives `wq (2k − 1)`, `n = 2k − 1` gives
  `wq (2k)`; the branch formulas.
* **`irrational_sqrt`** (25).  `(r : ℝ)^2 − r = ((r^2 − r : ℕ) : ℝ)` (`Nat.cast_sub`,
  `r ≤ r^2`); `irrational_sqrt_natCast_iff`; not a square since `(r−1)² < r² − r < r²`
  (`Nat.not_exists_sq'` or direct: `t² = r² − r` forces `r − 1 < t < r`).
* **`alphaQ_add_betaQ`** (3), **`alphaQ_mul_betaQ`** (10): `ring_nf`, `Real.sq_sqrt` (the radicand
  is `≥ 0` for every natural `r`: `r ≤ r²`).
* **`one_lt_betaQ_lt`** (30).  `β = 2r − 2√m`; `β > 1 ⇔ √m < r − 1/2 ⇔ m < r² − r + 1/4` ✓;
  `β < 6/5 ⇔ √m > r − 3/5 ⇔ r² − r > r² − 6r/5 + 9/25 ⇔ r/5 > 9/25` ✓ (`Real.lt_sqrt`,
  `Real.sqrt_lt'`, `nlinarith`).
* **`alphaQ_holderConjugate`** (20).  `⟨_, α > 0, β > 0⟩` with `α⁻¹ + β⁻¹ = (α + β)/(αβ) = 1`.
* **`sfl_eq_floor`** (50).  `Int.floor_eq_iff`.  For `k ≥ 0`: `2k√m = √(4k²m)` and
  `Real.floor_real_sqrt_eq_nat_sqrt`.  For `k < 0`: `2k√m = −√(4k²m)`, `Int.floor_neg`, and
  `⌈y⌉ = ⌊y⌋ + 1` because `y = 2|k|√m` is irrational (`Irrational.intCast_mul`, `Irrational.ne_int`;
  `Int.ceil_eq_iff` with strict inequalities).
* **`wq_two_mul_eq_floor`** (20).  `kα = 2rk + 2k√m`, `Int.floor_int_add`, `sfl_eq_floor`.
* **`wq_two_mul_sub_one_eq_ceil`** (25).  `kβ = 2rk − 2k√m`, `Int.ceil_add_int`, `Int.ceil_neg`,
  `sfl_eq_floor`.  **`wq_two_mul_sub_one_eq_floor`** (25): for `k ≠ 0`, `kβ ∉ ℤ` so
  `⌈kβ⌉ − 1 = ⌊kβ⌋`.  **`wqp_*_eq_floor`** (10 each): `wqp_two_mul(_sub_one)` + the above.

### §2 Bijectivity (≈ 200 lines)

* **`wq_bijective`** (120).  *Injective:* the two branches are strictly increasing in `k`
  (`k ↦ ⌊kα⌋`, `k ↦ ⌈kβ⌉ − 1` with `α, β > 1`; or integer route: `s(k+1) ≥ s(k) + 2r − 2` since
  `⌊2(k+1)√m⌋ ≥ ⌊2k√m⌋ + ⌊2√m⌋`, so even values step by `≥ 4r − 2` and odd values by
  `2r − (s(k+1) − s(k)) ≥ 1`, using `s(k+1) − s(k) ≤ ⌈2√m⌉ = 2r − 1`), and no even-branch value
  equals an odd-branch value (`compl_beattySeq`: `{beattySeq α k}ᶜ = {beattySeq' β k}`).
  *Surjective:* `compl_beattySeq alphaQ_holderConjugate` again: every `n` is `beattySeq α k` or
  `beattySeq' β k`.  Rewrite with `wq_two_mul_eq_floor`, `wq_two_mul_sub_one_eq_ceil`.
* **`wq_pos_iff`** (40).  `n = 2k` or `2k − 1`; `k ≥ 1`: `W(2k) ≥ (4r − 2)k > 0`, `W(2k−1) ≥ k`
  (`wq_two_mul_bounds`, `wq_two_mul_sub_one_bounds`: prove those first, they are integer-only).
  `k = 0`: `W(0) = 0`, `W(−1) = −1`.  `k < 0`: `s(k) = −sqrtPart − 1 < 0` gives `W(2k) < 0`, and
  `W(2k − 1) ≤ −1 ⇔ sqrtPart r k ≤ 2r|k| − 1 ⇔ 4k²m < (2r|k|)²` ✓.
* **`wqp_bijective`** (15): `wqp_eq_wq` and the involution `n ↦ if n even then n − 1 else n + 1`.
  **`wqp_pos_iff`** (20): same, the involution preserves positivity.

### §3 Theorem D and the one-step bounds (≈ 250 lines)

* **`wq_wq_of_odd`** (80).  `k = 0` is excluded (`W(0) = 0` is even).  *Real route:* `W(2k) =
  ⌊kα⌋ = kα − f`, `f = {kα} ∈ (0, 1)` (irrational), `= 2j − 1` with `j = (W(2k) + 1)/2`;
  `W(2j − 1) = ⌈jβ⌉ − 1` and `jβ = (kα − f + 1)β/2 = 2rk + (1 − f)β/2` (`αβ = 4r`), with
  `0 < (1 − f)β/2 < 1` (`β < 2`), so `⌈jβ⌉ = 2rk + 1`.  *Integer route:* with `s = s(k)`,
  `s² < 4k²m < (s + 1)²` (signs as per `k`), the claim is `s(j) = 2mk + rs + r − 1` for
  `2j = 2rk + s + 1`, i.e. `T² < (2rk + s + 1)²m < (T + 1)²` with `T = 2mk + rs + r − 1` —
  expand and `nlinarith` from the two hypotheses (`m = r² − r`).  Either works; the real route
  reuses §1.
* **`wqp_wqp_of_even`** (60).  `W'(2k − 1) = ⌊kα⌋ = kα − f = 2j`, `W'(2j) = ⌈jβ⌉ − 1` (valid for
  all `j`, `wq_two_mul_sub_one_eq_ceil` via `wqp_two_mul`) and `jβ = 2rk − fβ/2`, so
  `⌈jβ⌉ = 2rk`.  `k = 0` needs no case split but is degenerate: `W'(−1) = 0`, `W'(0) = −1`.
* **`wq_one`** (10).  `s(1) = Nat.sqrt (4m) = 2r − 2` since `(2r − 2)² ≤ 4r² − 4r < (2r − 1)²`
  (`Nat.sqrt_eq'`-style: `Nat.sqrt_le'`, `Nat.lt_succ_sqrt'`, or `Nat.sqrt_add_eq'`).
* **`wq_two_mul_bounds`** (40).  `(2r − 2)k ≤ s(k) < 2rk` for `k ≥ 1`: `((2r−2)k)² ≤ 4k²m <
  (2rk)²`, `Nat.le_sqrt'`, `Nat.sqrt_lt'`.
* **`wq_two_mul_sub_one_bounds`** (40).  `W(2j − 1) = 2rj − s(j) − 1`; `j ≤` it iff
  `s(j) ≤ (2r − 1)j − 1`, i.e. `4j²m < ((2r − 1)j)²` (`= 4r²j² − 4rj² + j²` ✓ strict);
  `< 2j − 1` for `j ≥ 2` iff `s(j) ≥ (2r − 2)j + 1`, i.e. `((2r − 2)j + 1)² ≤ 4j²m`; expanding,
  `4(r−1)²j² + 4(r−1)j + 1 ≤ 4(r² − r)j² ⇔ 4(r−1)j + 1 ≤ 4(r − 1)j²`, true for `j ≥ 2`, `r ≥ 2`.
* **`wqp_bounds`** (30).  `W'(2k) = 2rk − s(k) − 1 ∈ [k, 2k)` and `W'(2k − 1) = 2rk + s(k) >
  2k − 1`: the same square comparisons.

### §4 Theorem F: orbit classification (≈ 600 lines; the core)

Write `σ = wqPerm r hr`, `x_t = (σ ^ t) x` for `t : ℤ`.  Facts used: (a) for `y > 0` even,
`σ y > y` (`wq_two_mul_bounds`); (b) for `y` even with `σ y` odd, `σ² y = r y` (Theorem D,
`r y = 2rk`); (c) for `y ≥ 3` odd, `σ y < y`, and `σ 1 = 1` (`wq_one`); positivity is preserved
(`wq_pos_iff`).

* **Helper: the "after an even point" invariant** (80).  For `e > 0` even, every
  `y = (σ ^ n) e`, `n ≥ 1`, satisfies `P(y)`: `(y even ∧ y > e) ∨ (y odd ∧ ∃ z even, e ≤ z,
  σ z = y)`, and in both cases `y > e` (an odd `y = σ z ≥ (4r−2)z/2 > z`).  Induction on `n` using
  (a), (b).  Potential: `φ(y) = y` (even) / `z` (odd); `φ` strictly increases every two steps,
  so `(σ ^ n) e ≥ e + ⌊n/2⌋`.
* **Helper: the odd backward tail** (40).  If `y > 0` and `σ⁻¹ y` is odd then `σ⁻¹ y > y` unless
  `y = 1` (`σ⁻¹ 1 = 1`).  So a run of odd points read backward strictly increases.
* **`isEntry_iff`** (60).  `σ⁻¹ y` odd `⇔ ∃ j, wq (2j − 1) = y`.  If `σ⁻¹ y = 2j − 1` and
  `σ⁻² y = 2k` is even then Theorem D gives `y = 2rk` with `W(2k) = 2j − 1` odd; conversely
  `y = 2rk`, `W(2k)` odd gives `σ⁻¹ y = W(2k)`, `σ⁻² y = 2k` even.  `Equiv.symm_apply_eq`.
* **`permOrbit_subset_pos`** (15).  `zpow` induction / `Int.induction_on` with `wq_pos_iff`
  both ways.  **`permOrbit_wqPerm_one`** (15): `σ 1 = 1` so `σ ^ j 1 = 1` (`zpow` of a fixed
  point: `Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self`).
* **`existsUnique_isEntry_mem_orbit`** (150).  `x > 1` so no `x_t = 1` (else `x = 1`).  *Some
  `x_t` is even:* otherwise all forward points are odd and `≥ 3`, strictly decreasing in `ℕ⁺`
  (c), impossible.  *The even times are bounded below:* fix an even time `t₀`; by the invariant
  all even `x_t` with `t < t₀` are `< x_{t₀}`, pairwise distinct (each later one is larger), and
  positive: finitely many.  Let `t*` be the least even time, `e = x_{t*}`.  `x_{t*−1}`, `x_{t*−2}`
  are odd, so `IsEntry e` (`isEntry_iff`).  *Uniqueness:* another entry `x_{t'}` has `t' > t*`;
  `x_{t'−1}` is odd and, by the invariant applied from `e` (`t' − 1 ≥ t*`, and `t' − 1 ≠ t*`
  since `x_{t*}` is even), its predecessor `x_{t'−2}` is even: not an entry.
  Express everything with `permOrbit` membership: `y ∈ permOrbit σ x ↔ ∃ t, (σ ^ t) x = y`.
* **`isEntry_lt_of_mem_orbit`** (60).  `y = (σ ^ t) e`.  `t > 0`: the invariant.  `t < 0`: every
  point before `e` is odd.  Otherwise let `x_u` (`u < 0`) be an even point; the invariant from
  `x_u` covers `σ⁻¹ e` (time `−1 ≥ u`, and `−1 ≠ u` because `σ⁻¹ e` is odd), so `σ⁻¹ e` has an
  even predecessor, contradicting `σ⁻² e` odd (`isEntry_iff`).  Read backward, the odd points
  strictly increase from `σ⁻¹ e > e` (odd-backward-tail helper; `σ⁻¹ e ≠ 1` as `σ 1 = 1 ≠ e`).
* **`permOrbit_wqPerm_infinite`** (20).  The forward orbit from `e` is unbounded (`≥ e + ⌊n/2⌋`).
* **`tendsto_wqPerm_pow`** (30).  `x = x_0`, `e = x_{t*}`; for `n ≥ t*`,
  `x_n ≥ e + ⌊(n − t*)/2⌋` (invariant), so `tendsto_atTop_mono'` + `tendsto` of `n/2`.
* **`tendsto_wqPerm_pow_neg`** (30).  For `n > −t*`, the points `x_{−n}` are in the odd backward
  tail, strictly increasing in `n`: `x_{−n} ≥ n − C`.
* **`isOrbitMin_iff`** (40).  `→`: `x = 1`, or `x > 1` and the entry `e` of its orbit satisfies
  `x ≤ e < (everything else)`, so `x = e`.  `←`: `permOrbit_wqPerm_one` / `isEntry_lt_of_mem_orbit`.
* **`permOrbit_bijOn`** (50).  Maps to: `1 > 0`, entries are `> 0`.  Injective: two minima of
  one orbit are equal (`le_antisymm`, as in `amusicalInfinitelyManyOrbits_of_minima`;
  `permOrbit` equality via the `amusicalOrbit_eq_of_mem` argument).  Surjective: `x = 1` or the
  unique entry `e` of `x`'s orbit, `permOrbit σ e = permOrbit σ x`.
* **`wqPerm_infinitelyManyInfiniteOrbits`** (40).  The entries are infinitely many: `minCount_ge`
  (§5, so prove `minCount_add_countB` and `minCount_ge` before this one) makes
  `#{orbit minima ≤ X} ≥ X/12`, unbounded.  Then either the trap theorem with
  `C = 2ℤ ∪ σ(2ℤ)` (`σ C ⊆ C` by (b) for every `k ∈ ℤ`; `C ∖ σ C` restricted to `ℕ⁺` is the
  entry set, via `isEntry_iff`), or `permOrbit_bijOn` (injective on entries) plus
  `permOrbit_wqPerm_infinite`.

**Suggested shared skeleton (helps §6 halve its cost):** state the classification once for an
abstract `σ : Equiv.Perm ℤ` preserving `ℕ⁺` with a decidable class `E` (`E` = evens for `W`,
odds for `W'`) and hypotheses: `E y → y < σ y`; `E y → ¬E (σ y) → E (σ² y) ∧ y < σ² y`;
`¬E y → σ y ≤ y` with equality only at a fixed point.  Instantiate twice.

### §5 Counting (≈ 550 lines)

* **`minCount_add_countB`** (200).  By `isOrbitMin_iff`, the filter in `minCount` is
  `{1} ∪ {y ∈ [1, X] : IsEntry y}` (disjoint: `1` is odd).  Let `Aset = {y ∈ [1, X] : y even,
  ∃ j, W(2j − 1) = y}`, the image of `countA`'s filter under the injective `j ↦ W(2j − 1)` (`j ≤ X`
  suffices since `W(2j − 1) ≥ j`; `j ≥ 1` since `y > 0`).  Let `Bset = {2rk : k ∈ countB's
  filter}` (injective `k ↦ 2rk`).  `Bset ⊆ Aset` (`2rk = W(W(2k))`, `W(2k)` odd, Theorem D) and
  `entries ≤ X = Aset ∖ Bset` by the definition of `IsEntry`.  `Finset.card_sdiff`,
  `Finset.card_image_of_injOn`.
* **`minCount_ge`** (120).  `A(X) = #{even y ∈ [1, X]} − #{even y ∈ [1, X] in the α-range}`:
  every positive `y` is `W(2k)` or `W(2j − 1)` with `k, j ≥ 1` (bijectivity + `wq_pos_iff`), not
  both.  `#{k ≥ 1 : W(2k) ≤ X} ≤ ⌊X/(4r − 2)⌋` (`wq_two_mul_bounds`), `B(X) ≤ #{k ≥ 1 : 2rk ≤ X}
  = ⌊X/2r⌋`.  Combine with `minCount_add_countB` (`X ≥ 1`).
* **`minCount_le`** (30).  Minima other than `1` are entries, hence even: inject into
  `{1} ∪ evens ≤ X`.
* **`tendsto_minCount`** (200).  `W(2j − 1)` even `⇔ s(j)` odd; `W(2k)` odd `⇔ s(k)` odd.  So
  `B(X) = #{k ≤ ⌊X/2r⌋ : s(k) odd}` and `A(X) = #{j ≤ J(X) : s(j) odd}` with
  `J(X) = #{j ≥ 1 : W(2j − 1) ≤ X}` (`W(2j − 1)` increasing in `j`), `jβ − 1 ≤ W(2j − 1) ≤ jβ`
  gives `|J(X) − X/β| ≤ 2`.  The hypothesis composed with `J(X) → ∞` and `⌊X/2r⌋ → ∞`
  (`Tendsto.comp`), times `J(X)/X → 1/β`, `⌊X/2r⌋/X → 1/(2r)`:
  `minCount/X → 1/(2β) − 1/(4r) = (α − 2)/(8r) = (r − 1 + √m)/(4r)` (`1/β = α/(4r)`).

### §6 The partner `W'` (≈ 450 lines with the skeleton, ≈ 800 without)

Parities swap.  Facts: (a′) odd `y > 0`: `σ' y > y` (`wqp_bounds`); (b′) odd `y` with `σ' y`
even: `σ'² y = r(y + 1) − 1 > y` and odd (`wqp_wqp_of_even`); (c′) even `y > 0`: `σ' y < y`
(no fixed point at all).  So no orbit in `ℕ⁺` is all-even (strictly decreasing), every orbit has
a first odd point, which is the unique partner entry (odd, two even predecessors) and the
minimum; both tails go to `∞`.
* **`isEntryP_iff`** (60), **`existsUnique_isEntryP_mem_orbit`**, **`isEntryP_lt_of_mem_orbit`**,
  **`permOrbit_wqpPerm_infinite`**, **`tendsto_wqpPerm_pow(_neg)`**, **`isOrbitMinP_iff`**,
  **`wqpPerm_infinitelyManyInfiniteOrbits`**: as §4 (skeleton instance with `E` = odds).
  Infinitely many: `minCountP ≥ ⌊X/2⌋ − ⌊X/(4r − 2)⌋ − ⌊X/2r⌋` (same argument; checked).
* **`minCountP_add_countBP`** (150).  Minima in `[1, X]` = partner entries (no `{1}`): odd
  `y = W'(2k)` (`A′`) minus `y = 2rj − 1` with `W'(2j − 1)` even (`B′`, Theorem D′).
* **`tendsto_minCountP`** (120).  `W'(2k)` odd `⇔ s(k)` even; `W'(2j − 1)` even `⇔ s(j)` even;
  the density of even `s` is `1 − 1/2` from the hypothesis; same `d_r`.

Rough total: 2,300-2,900 lines.  Largest: §4 (and §6 if the skeleton is skipped), then the
Finset bookkeeping of §5.
