# KICKOFF 2026-10-16: the rational Wythoff maps `W_{p/q±}`: Lemma 1, Theorems T, E, E′, M, Prop D

Repo `collatz-moonshot-amusical-round2` (branch `wip/wythoff-rational`): close every `sorry` in
`CollatzMoonshot/WythoffRational.lean` (36 lemmas) and `CollatzMoonshot/WythoffRationalMarkov.lean`
(8 lemmas).  Both import only Mathlib and `AmusicalTrap.lean` (proved; reuse its
`permOrbit`, `InfinitelyManyInfiniteOrbits`, `infinitelyManyInfiniteOrbits_of_trap`,
`permOrbit_injOn_entry`, `permOrbit_infinite_of_entry`).  Do not edit `AmusicalTrap.lean` or
`Amusical.lean`.

Sources: research notes `~/personal/tmp/amusical-agents/out/wythoff-evenp.md` (§1 Lemma 1, §2
Theorem M, §4 Prop D, Theorem T, Theorem E′) and `out/wythoff.md` (§1 definitions, §4 Theorem E).
The note works on `ℕ⁺`; the Lean works on **all of `ℤ`** with the same floor formulas, where every
branch is *exactly* affine (no edge pieces, no "up to finitely many `x`"), the map is a permutation
preserving `ℕ⁺`, and `AmusicalTrap`'s orbit notions apply as they are.

## Ratified, do not change

Every definition and theorem statement in both files.

* `WythoffRational`: `Side`, `wythoff`, `wythoffInv`, `wythoffPerm`, `fwdEven`, `bwdEven`,
  `fwdProb`, `bwdProb`, `evenPerm`, `entrySet`, `mirrorPerm`, `fwdStat`, `bwdStat`, `fwdDrift`,
  `iidFwdDrift`, `bwdDrift`, `iidBwdDrift`.
  * §1 maps: `wythoffInv_wythoff`, `wythoff_wythoffInv`, `wythoff_pos_iff`, `wythoff_bijOn_pos`.
  * §2 floors: `wythoff_plus_two_mul`, `wythoff_plus_two_mul_sub_one`, `wythoff_minus_two_mul`,
    `wythoff_minus_two_mul_sub_one`.
  * §3 pieces: `wythoff_add_even`, `wythoff_add_odd`, `wythoff_parity_periodic`.
  * §4 Lemma 1: `card_even_image_even`, `card_even_image_odd`.
  * §5 Theorem T: `parityClass_invariant_iff`, `absorbing_iff`.
  * §6 Theorem E: `evenPerm_two_mul`, `evenPerm_two_mul_sub_one`, `permOrbit_evenPerm_one`,
    `evenPerm_entry_iff`, `existsUnique_entry_mem_orbit`, `entry_le_of_mem_orbit`,
    `permOrbit_evenPerm_infinite`, `isOrbitMin_iff`, `permOrbit_bijOn`, `card_orbitMin_le`,
    `evenPerm_infinitelyManyInfiniteOrbits`.
  * §7 Theorem E′: `mirrorPerm_apply`, `permOrbit_mirrorPerm`, `permOrbit_mirrorPerm_infinite`,
    `mirror_isOrbitMin_iff`, `mirror_existsUnique`, `mirrorPerm_infinitelyManyInfiniteOrbits`.
  * §8 Prop D: `fwdStat_stationary`, `bwdStat_stationary`, `propD_plus`, `propD_minus`.
* `WythoffRationalMarkov`: `wordWeight`, `fwdItin`, `bwdItin`, `cylCount`, `markovPeriod`,
  `iidPeriod`, `iidBwd`; theorems `fwdItin_periodic`, `bwdItin_periodic`, `cylCount_eq`,
  `cylCount_fwd`, `cylCount_bwd`, `cylCount_condIndep`, `tenThirds_dependent`,
  `cylCount_eq_odd`.

No `native_decide`, no axioms, no `maxHeartbeats` bumps.  Lean lines ≤ 100 characters.  Do
**not** edit `RESEARCH-*.md`.  Commit after each proved lemma (or tight group).  Notes as you go
in `HANDOFF-wythoff-rational.md`.  Helper lemmas and definitions are welcome (above their first
use; a shared helper section at the top of each file is fine).  Any cleaner route is fine as long
as the ratified statements are unchanged.  If a ratified statement turns out false, stop that
lemma, write the counterexample in the HANDOFF, and move on; do not weaken it yourself.

**Order of attack:** §3 and §1 first (everything rests on them), then §2, §4, §5, §7's
`mirrorPerm_apply`, §6, the rest of §7, §8; then the Markov file (M0 helpers, periodicity, M1-M4).

## Truth checks already run

`tmp/drafter-wythoff/check.py`, `check2.py`, `check3.py` (outputs `check*.out`; each run < 2 s).
They mirror the Lean definitions exactly (Python `//`, `%` = `Int.ediv`, `Int.emod` for positive
divisors), and `tmp/drafter-wythoff/Eval.lean` (`lake env lean`) confirms the Lean `wythoff`,
`wythoffInv` values equal the Python ones on `[-10, 10]` for `10/3±` and `8/1+`, and that
`cylCount` equals the Theorem M formula on sample cylinders (`10/3−` at `a = −777`, `12/5+`,
`7/2+` odd).

* Bijection (explicit inverse both ways) and `0 < W n ↔ 0 < n` on `[-600, 600]`, **every**
  `0 < q < p ≤ 25`, coprime or not; Beatty floor/ceil bridge for `k ∈ [-300, 300]`, `p ≤ 20`.
* Piece shifts for all `n ∈ [-60, 60]`, `|m| ≤ 5`, `p ≤ 25`.
* Lemma 1 for every even `p ≤ 60`, coprime `q`, both sides.
* Theorem T (map form) for every coprime `p ≤ 30` (odd `p` included), both sides; chain form for
  even `p ≤ 60`.
* Theorem E: for `j = 2..6`, every `x ∈ [2, 400)`: ±80 iterates, no return, exactly one point of
  `E`, and it is the minimum; `x` is a minimum iff `x ∈ E`; the count formula for `X ≤ 500`.
* Theorem E′ on `[-10⁴, 10⁴]` for `j = 1..7`, plus the orbit-min and uniqueness consequences.
* Theorem M (joint): 15 hand-picked members at random windows `a ∈ [-10⁶, 10⁶]` (incl. `2/1±`,
  `4/1±`, `L = 0` and `L' = 0`), plus a sweep of **414** (member, side, `L`, `L'`) cases (all even
  `p ≤ 14`, `L + L' ≤ 3`, windows `k·P`, `k ≤ 3`).  Odd `p`: 6 members + a sweep of 216 cases.
  Periodicity lemmas on random points.  Conditional independence, `10/3+` counts `37, 115, 63`.
* Prop D: stationarity and strict drift ordering for every coprime `p ∈ [3, 40)`, `q ≠ R`.

**Teeth** (each fails as it must): the `+` inverse used on the `−` side; the odd-branch shift with
`2q`; Lemma 1 for odd `p` and for non-coprime `(p, q)`; Theorem T without the `R = 1` disjunct;
Theorem E with `E = 2ℕ ∖ 4ℕ` at `j = 4`; E′ on the `−` side and for `10/7` vs `10/3`; Theorem M
with the i.i.d. law (0 of the cylinders), with the `−` chain on the `+` side, on a window that
is too short (`P/qR`) or not a multiple (`P + 2`); periodicity with one factor fewer; the odd-`p`
law with backward `(½, ½)`; unconditional independence (violated on 16/16 word pairs); Prop D with
the `−` sign flipped.

## Paper proofs (Ren)

Notation: `R := p − q` (as an integer, `(p : ℤ) − q`).  `σ := wythoffPerm s hq hqp`, so
`σ n = wythoff s p q n`, `σ⁻¹ m = wythoffInv s p q m` (`rfl` after unfolding).

### M0. Shared helpers (≈ 80 lines)

* `ediv_eq_iff (hd : 0 < d) : a / d = m ↔ m * d ≤ a ∧ a < m * d + d` from
  `Int.le_ediv_iff_mul_le` and `Int.ediv_lt_iff_lt_mul` (core `Init`).  This one lemma, plus
  `nlinarith`/`linarith` with `p, q` as variables, does most of §1-§3; `omega` cannot see
  products `k * p`.
* Parity casts: `((n : ℤ) : ZMod 2) = 0 ↔ n % 2 = 0`, `= 1 ↔ n % 2 = 1`
  (`ZMod.intCast_zmod_eq_zero_iff_dvd`, `Int.emod_two_eq_zero_or_one`); `∀ e : ZMod 2, e = 0 ∨
  e = 1` (`decide`).
* Arithmetic of the parameters: `Even p → Nat.Coprime p q → Odd q` (`Nat.Coprime.odd_of_left`
  after `Nat.Coprime.coprime_dvd_left` with `2 ∣ p`); `Nat.Coprime p (p - q)`
  (`Nat.coprime_self_sub_right`); hence `R` odd too.

### §1 The maps (≈ 170 lines)

* **`wythoffInv_wythoff`** (70).  Case `s`, then `n % 2`.  `+`, `n = 2k`: `m := kp / q`, so
  `mq ≤ kp < mq + q`.  Then `kp ≥ mq` and `(k−1)p = kp − p < mq + q − p < mq`, so
  `(mq + p − 1)/p = k` (`ediv_eq_iff`), and `kp − mq < q` takes the even branch: `2k`.  `+`, `n =
  2k − 1`: `m := (kp − 1)/R`, so `mR < kp ≤ (m+1)R`.  `K := m + 1 − k` has `Kp = (m+1)p − kp ∈
  [mq + q, mq + p)`, so `(mq + p − 1)/p = K` and `Kp − mq ≥ q`: odd branch, `2(m + 1 − K) − 1 =
  2k − 1`.  `−` side: same with `m := (kp − 1)/q` (`mq < kp ≤ mq + q`, `mq/p + 1 = k`) and `m :=
  kp / R` (`mR ≤ kp < (m+1)R`, `K := m + 1 − k`, `Kp ∈ (mq + q, mq + p]`).  Normalize the
  parities first: `(2k) % 2 = 0`, `(2k)/2 = k`, `(2k − 1) % 2 = 1`, `(2k − 1 + 1)/2 = k` (`omega`);
  write odd `n` as `2k − 1` with `k := (n + 1)/2`.
* **`wythoff_wythoffInv`** (60).  `+`: `k := (mq + p − 1)/p`, so `mq ≤ kp < mq + p`.  If `kp − mq
  < q`, `W(2k) = kp / q = m` (`mq ≤ kp < mq + q`).  Else `K := m + 1 − k`, `Kp ∈ (mR, (m+1)R]`, so
  `W(2K − 1) = (Kp − 1)/R = m`.  `−`: `k := mq/p + 1`, `mq < kp ≤ mq + p`; branch `kp − mq ≤ q`
  gives `(kp − 1)/q = m`; else `Kp ∈ [mR, (m+1)R)`, `Kp / R = m`.
* **`wythoff_pos_iff`** (30).  `n = 2k`: `kp / q > 0 ↔ k > 0` (`p > q`: `k ≥ 1 → kp ≥ p > q`;
  `k ≤ 0 → kp ≤ 0`); `(kp − 1)/q` likewise (`k ≥ 1 → kp − 1 ≥ p − 1 ≥ q`).  Odd branch with
  `R ≤ p − 1`.
* **`wythoff_bijOn_pos`** (15).  `(wythoffPerm s hq hqp).bijective` restricted: `Set.BijOn` from
  `MapsTo` (`wythoff_pos_iff`), `InjOn` (injective), `SurjOn` (`wythoffInv` and `pos_iff` of
  `wythoff_wythoffInv`).

### §2 Floor/ceil bridge (≈ 60 lines)

`Rat.floor_intCast_div_natCast` (`⌊(n : ℚ)/d⌋ = n / d`) and `Rat.ceil_intCast_div_natCast`
(`⌈n/d⌉ = −((−n)/d)`), after rewriting `((p : ℚ) − q) = ((p − q : ℕ) : ℚ)` (`Nat.cast_sub`) and
`(k * p / q : ℚ) = ((k * p : ℤ) : ℚ) / (q : ℕ)` (`push_cast`).  For the ceilings: `−((−a)/d) − 1 =
(a − 1)/d` for `d > 0` (via `ediv_eq_iff` on both sides, or `Int.neg_ediv`-style lemmas).

### §3 Pieces (≈ 60 lines)

* **`wythoff_add_even`** (20).  `n + 2qm` is even, `(n + 2qm)/2 = n/2 + qm` (`omega` after
  `n = 2k`), and `(n/2 + qm)·p / q = (n/2)·p / q + pm` (`Int.add_mul_ediv_left` after ring_nf to
  `a + q * (p * m)`); `−` side the same with `− 1` inside.
* **`wythoff_add_odd`** (20).  `((n + 2Rm) + 1)/2 = (n+1)/2 + Rm`, then the same with divisor `R`.
* **`wythoff_parity_periodic`** (20).  `n` even: `wythoff_add_even` with `m' := R·m`, `W n + p R m`;
  `n` odd: `wythoff_add_odd` with `m' := q m`.  `p` even kills `p·(…)` in `ZMod 2`
  (`(Even.mul_right hp _)` and `ZMod.intCast_eq_zero_iff_even`-style cast lemmas, or `push_cast`
  + `ZMod.natCast_self_eq_zero` after writing `p = 2 p'`).

### §4 Lemma 1 (≈ 140 lines)

* **`card_even_image_even`** (80).  Let `g t := W(2t)` for `t ∈ range q`.  `+`: `g t = tp / q`; `−`:
  `g t = (tp − 1)/q`.  For `1 ≤ t ≤ q − 1`, `q ∤ tp` (coprime: `Nat.Coprime.dvd_of_dvd_mul_right`),
  so `(tp − 1)/q = tp / q` and `g(q − t) = p − 1 − g t` (from `(q − t)p = pq − tp`, `ediv_eq_iff`,
  and `tp mod q ≥ 1`).  `p` even makes the involution `t ↦ q − t` on `Icc 1 (q−1)` swap parities, and
  `q` odd means no fixed point.  So `#{t ∈ [1, q−1] : g t even} = #{… odd}` (`Finset.card_nbij'`
  with `i = j = (q − ·)`), and they sum to `q − 1` (`Finset.card_filter_add_card_filter_not`).
  Hence `(q−1)/2` from `[1, q−1]`; `t = 0` adds `g 0 = 0` (even) on `+`, `g 0 = −1` (odd) on `−`.
  Write `range q = {0} ∪ Icc 1 (q−1)` (`Finset.range_eq_Ico`, `Finset.Ico_insert_succ_left` or
  `Finset.range_succ`-style splitting).  Final arithmetic with `q = 2a + 1`: `omega`.
* **`card_even_image_odd`** (60).  Same with `h u := W(2u + 1)`, `k := u + 1 ∈ [1, R]`; `+`:
  `h = (kp − 1)/R`, `−`: `h = kp / R`.  `R ∤ kp` for `1 ≤ k ≤ R − 1` (`Nat.coprime_self_sub_right`).
  Involution `k ↦ R − k` on `[1, R−1]`.  The extra index `k = R`: `+` gives `(Rp − 1)/R = p − 1`
  (odd), `−` gives `Rp / R = p` (even).  Hence `(R−1)/2` resp. `(R+1)/2`.

### §5 Theorem T (≈ 170 lines)

* **`parityClass_invariant_iff`** (110).  (←) `+`, `q = 1`: `W(2k) = kp` is even, so `e = 0`.  `+`,
  `R = 1`: `W(2k − 1) = kp − 1` is odd, `e = 1`.  (→) Given invariant class `e`.  If `p` is odd:
  for even `n`, `W(n + 2q) = W n + p` (`wythoff_add_even`, `m = 1`) has the other parity, so the
  class `0` is not invariant; for odd `n`, `W(n + 2R) = W n + p`, so neither is `1`.  So `p` is
  even.  If `e = 0`: every `W(2t)`, `t < q`, is even, so the Lemma 1 count is `q`, i.e.
  `(q+1)/2 = q` on `+` (so `q = 1`) and `(q−1)/2 = q` on `−` (impossible, `q ≥ 1`).  If `e = 1`:
  every `W(2u+1)` is odd, the count is `0`: `(R−1)/2 = 0` on `+` (so `R = 1`, `R` odd), `(R+1)/2 =
  0` on `−` (impossible).  Use `Finset.filter_true_of_mem` / `Finset.filter_false_of_mem` to turn
  "all even" into the count.
* **`absorbing_iff`** (60).  `q` and `R` odd (M0).  Diagonal entries: `fwdProb 0 0 = fwdEven 0`,
  `fwdProb 1 1 = 1 − fwdEven 1`, `bwdProb 0 0 = bwdEven 0`, `bwdProb 1 1 = 1 − bwdEven 1`.  `+`:
  `(q+1)/(2q) = 1 ↔ q = 1`, `1 − (R−1)/(2R) = 1 ↔ R = 1`, `(q+1)/p = 1 ↔ R = 1`, `1 − (q−1)/p = 1 ↔
  q = 1`.  `−`: `(q−1)/(2q) < 1`, `1 − (R+1)/(2R) < 1`, `(q−1)/p < 1`, `1 − (q+1)/p < 1`.
  `div_eq_one_iff_eq` (denominators `≠ 0`), `field_simp`, then cast back with `exact_mod_cast` /
  `omega`.

### §6 Theorem E (≈ 330 lines)

`σ := evenPerm j _`, `p = 2j`, `q = 1`, `R = 2j − 1`.  `C := {y | y % 2 = 0}`.

* **`evenPerm_two_mul`** (10), **`evenPerm_two_mul_sub_one`** (20).  Unfold; `(k·2j − 1)/(2j −
  1) = ((2j − 1)k + (k − 1))/(2j − 1) = k + (k − 1)/(2j − 1)` (`Int.add_mul_ediv_left`).  Watch the
  casts `((2 * j : ℕ) : ℤ) − ((1 : ℕ) : ℤ)`.
* **`permOrbit_evenPerm_one`** (15).  `σ 1 = 1` (`evenPerm_two_mul_sub_one` at `k = 1`), then
  `Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self`.
* **`evenPerm_entry_iff`** (30).  `σ(C) ⊆ 2jℤ` (`evenPerm_two_mul`) and `2jk = σ(2k)`; for `x > 0`
  even, `x ∉ σ(C) ↔ ¬ 2j ∣ x`.
* *Facts* (helpers, 60): (a) `σ(C) ⊆ C`, so `C` is a trap; `entrySet j ⊆ C \ σ(C)`.  (b) For odd
  `y ≥ 3`: `1 ≤ σ y < y` (`k + (k−1)/(2j−1) < 2k − 1` for `k ≥ 2`, `j ≥ 2`).  (c) For odd `m > 1`,
  `σ⁻¹ m` is odd (an even preimage would make `m` even) and `> m` (by (b) applied to `σ⁻¹ m`,
  which is `≠ 1` since `σ 1 = 1 ≠ m`).  (d) For `k > 0`, `σ⁻¹(2jk) = 2k`.  (e) For `y > 0` even,
  `σ y = jy > y`.  (f) Orbits of positive points are positive (`wythoff_pos_iff`).
* **`existsUnique_entry_mem_orbit`** (70).  *Uniqueness:* `AmusicalTrap.permOrbit_injOn_entry`
  with `C`; two entry points in the same orbit have equal orbits (`permOrbit` of a member equals
  the orbit; prove `y ∈ permOrbit σ x → permOrbit σ y = permOrbit σ x` as a helper).
  *Existence:* strong induction.  If `x` is odd (`x > 1`), the forward iterates stay odd and
  strictly decrease (b) while odd, never reaching `1` (`σ⁻¹ 1 = 1`), so some iterate is even
  (induction on `x`, `Nat.strong_induction_on` on `x.toNat`).  If `x` is even and `2j ∣ x`,
  `σ⁻¹ x = x/j` is a smaller positive even (d); descend until `2j ∤`, which is a point of `E`.
* **`entry_le_of_mem_orbit`** (50).  Every point of the orbit is `σ^z e`.  `z ≥ 0`: `σ^z e` is even
  and `≥ e` (e), induction.  `z < 0`: `σ⁻¹ e` is odd (`e ∉ σ(C)`) and `> e` (`σ⁻¹ e ≠ 1`, (b));
  then (c) by induction.  `Int.induction_on` or split `z = n` / `z = −(n+1)`.
* **`permOrbit_evenPerm_infinite`** (10).  The orbit contains its entry point `e`; `permOrbit_eq`
  helper + `AmusicalTrap.permOrbit_infinite_of_entry`.
* **`isOrbitMin_iff`** (25).  (→) `x = 1` or `x > 1`; in the latter case the entry point `e`
  satisfies `e ≤ x` (`entry_le_of_mem_orbit`) and `x ≤ e`, so `x = e`.  (←) `x = 1`:
  `permOrbit_evenPerm_one`.  `x ∈ E`: `entry_le_of_mem_orbit` with `e = x`.
* **`permOrbit_bijOn`** (40).  `MapsTo`: points of `{1} ∪ E` are positive.  `InjOn`: `{1}`'s orbit
  is `{1}`, distinct points of `E` are on distinct orbits (uniqueness above).  `SurjOn`: an orbit
  through `x > 0` is that of `1` (if `x = 1`) or of its entry point.
* **`card_orbitMin_le`** (50).  Transfer to `ℕ`: the filter is the image of `{1} ∪ {x ∈ Ioc 0 X |
  2 ∣ x ∧ ¬ 2j ∣ x}` under `Nat.cast` (or prove card equality by `Finset.card_bij`).  Then
  `Nat.Ioc_filter_dvd_card_eq_div` for `2` and `2j` (`2j ∣ x → 2 ∣ x`, so subtract), plus `1`
  for `x = 1` (odd, so disjoint).
* **`evenPerm_infinitelyManyInfiniteOrbits`** (25).  As `amusicalV_infinitelyManyInfiniteOrbits`:
  `infinitelyManyInfiniteOrbits_of_trap σ` (a), entry points `2jn + 2` (`n : ℕ`, injective;
  `j ≥ 2` so `2jn + 2 ≢ 0 (mod 2j)`), with `evenPerm_entry_iff`.

### §7 Theorem E′ (≈ 150 lines)

* **`mirrorPerm_apply`** (30).  `q = 2j − 1` so `R = 1`.  Odd `n = 2k − 1`: LHS `(k·2j − 1)/1 =
  2jk − 1`, RHS `σ(2k) − 1 = 2jk − 1`.  Even `n = 2k`: LHS `k·2j / (2j − 1) = k + k/(2j − 1)`
  (`2jk = (2j−1)k + k`); RHS `σ(2(k+1) − 1) − 1 = (k + 1) + k/(2j − 1) − 1`
  (`evenPerm_two_mul_sub_one`).  Casts: `((2 * j - 1 : ℕ) : ℤ) = 2 * j − 1` (`Nat.cast_sub`,
  `1 ≤ 2j`).
* **`permOrbit_mirrorPerm`** (40).  `(mirrorPerm ^ z) x = (σ ^ z)(x + 1) − 1` for all `z : ℤ`:
  `mirrorPerm = (Equiv.addRight 1).trans (σ.trans (Equiv.addRight (−1)))` (ext +
  `mirrorPerm_apply`), and conjugation commutes with `zpow` (`MulAut.conj` / `map_zpow`, or
  induction with `zpow_add_one`, `zpow_sub_one`).  Then `Set.range` rewriting.
* **`permOrbit_mirrorPerm_infinite`** (15).  `x + 1 > 1`; image of an infinite set under the
  injective `(· − 1)` (`Set.Infinite.image`).
* **`mirror_isOrbitMin_iff`** (25), **`mirror_existsUnique`** (25).  Transport §6 through
  `permOrbit_mirrorPerm`: `y ∈ orbit' x ↔ y + 1 ∈ orbit (x + 1)`; `x + 1 ≥ 2`, so `x + 1 ≠ 1`.
* **`mirrorPerm_infinitelyManyInfiniteOrbits`** (20).  Either the trap theorem with `C = {y | y % 2
  = 1}` (σ′ maps odds to odds: `σ′(2k − 1) = 2jk − 1`; entry points `2jn + 1`), or transport the
  §6 conclusion.  The trap route is shorter.

### §8 Prop D (≈ 150 lines)

* **`fwdStat_stationary`**, **`bwdStat_stationary`** (25 each).  `cases s`, unfold, `field_simp`,
  `ring`.  Denominators: `2qR − q − R = q(R − 1) + R(q − 1) > 0` when `p ≥ 3` (not both `q = R =
  1`); `2q`, `2R`, `p − 2`, `p`, `p + 2` positive.
* **`propD_plus`**, **`propD_minus`** (50 each).  Key identity: `fwdDrift − iidFwdDrift =
  (π − ½)(log(r/2) − log(s/2)) = (π − ½)·log(R/q)` (`Real.log_div`, positivity of all arguments),
  with `π⁺ − ½ = (R − q)/(2(2qR − q − R))`, `π⁻ − ½ = (q − R)/(2(2qR + q + R))`.  Backward:
  `bwdDrift − iidBwdDrift = (π_b − q/p)·(log(2/r) − log(2/s)) = (π_b − q/p)·log(q/R)`, `π_b⁺ − q/p =
  (q − R)/(p(p − 2))`, `π_b⁻ − q/p = (R − q)/(p(p + 2))`.  Split `q < R` / `R < q` (`hne`);
  `Real.log_pos` (`1 < R/q`) or `Real.log_neg` (`0 < R/q < 1`); `mul_pos` /
  `mul_pos_of_neg_of_neg`.  Push the `ℚ → ℝ` casts of `fwdStat` first (`push_cast`).

### Markov file (≈ 750 lines)

* **AP lemma** (helper, 60).  For `g : ℤ → ℕ` periodic mod `M > 0` and `u` coprime to `M`:
  `∑ i ∈ range M, g (c + u i) = ∑ i ∈ range M, g i`.  Proof: `i ↦ (c + u i : ZMod M)` is a bijection
  (`ZMod.unitOfCoprime`, `Equiv.sum_comp`), and `g` factors through `ZMod M`.  Also the window
  lemma: for `g` periodic mod `P`, the sum over `[a, a + kP)` is `k ·` the sum over `[0, P)`
  (shift-invariance of a one-period sum, then `Finset.range_add` blocks).  Counts are sums of
  indicator functions (`Finset.card_filter`).
* **`fwdItin_periodic`** (40).  Induction on `L` generalizing `x`, `m`.  `fwdItin x (L+1) = (W x)
  :: fwdItin (W x) L` (helper: `List.range_succ_eq_map`, `Function.iterate_succ_apply`).  `W(x +
  2(qR)^{L+1} m) = W x + p·R·(qR)^L m` (even `x`; `wythoff_add_even` with multiplier `R (qR)^L m`)
  or `W x + p·q·(qR)^L m` (odd `x`).  The head parity is unchanged (`p` even), and the shift is
  `2 (qR)^L · ((p/2) R m)`, so the IH applies.
* **`bwdItin_periodic`** (60).  Helper `wythoffInv_add`: `W⁻¹(m + p y) = W⁻¹ m + 2Q y` with `Q = q`
  if `W⁻¹ m` is even, `R` if odd (apply `W` to the right side with `wythoff_add_even/odd` and use
  injectivity).  Then the same induction: the shift `2(p/2)^{L+1} y = p (p/2)^L y` turns into
  `2Q (p/2)^L y = 2 (p/2)^L (Q y)`.
* **M1, forward count** (150).  Claim: over `[0, 2(qR)^L)`, `#{x ≡ e, fwdItin x L = f} = (qR)^L ·
  wordWeight F e f`.  Induction on `f = g :: w`.  For `e = 0` write `x = 2t + 2q m'`, `t < q`, `m'
  < R (qR)^{L−1}` (a `Finset` product decomposition, `Nat.divModEquiv`-style), so `W x = W(2t) + p
  m'`.  The head condition is `W(2t) ≡ g` (`p` even).  For fixed `t`, `m' ↦ fwdItin (W(2t) + p m')
  w` is periodic in `m'` with period `(qR)^{L−1}` (`fwdItin_periodic`), and on one period the AP
  lemma with `u = p/2` (coprime to `qR`: M0) over the classes `≡ W(2t) (mod 2)` gives the
  `L − 1` count for state `g`.  The `R` periods give a factor `R`.  Summing over `t` gives
  `#{t < q : W(2t) ≡ g} · R · (qR)^{L−1} · wordWeight F g w`, and Lemma 1 turns
  `#{t < q : W(2t) ≡ g}/q` into `F(0 → g)`.  `e = 1` symmetric (`x = 2u + 1 + 2R m'`).
* **M2, backward count** (150).  Over `[0, 2(p/2)^L)`, `#{m ≡ e, bwdItin m L = b} = (p/2)^L ·
  wordWeight B e b`.  Write `m = c + p y`, `c < p`, `y < (p/2)^{L−1}`; `W⁻¹ m = W⁻¹ c + 2Q y`
  (`wythoffInv_add`); `m ≡ c (mod 2)`.  The AP lemma with `u = Q` (odd, coprime to `p/2`) gives
  the `L − 1` count.  The one-step count `#{c < p : c ≡ e, W⁻¹ c even}` is `(q+1)/2` (`+`, `e =
  0`), `(q−1)/2` (`+`, `e = 1`), `(q−1)/2` (`−`, `e = 0`), `(q+1)/2` (`−`, `e = 1`).  *Direct
  route:* by the definition of `wythoffInv`, `W⁻¹ c` is even iff `v < q` with `v := (−cq) mod p`
  (`+`), resp. `1 ≤ v' ≤ q` with `v' := p − (cq mod p)` (`−`).  `c ↦ v` is a bijection of `[0, p)`
  (`q` a unit mod `p`), and `v ≡ c (mod 2)` (`p` even, `q` odd).  Count the `v ∈ [0, q)` (resp.
  `[1, q]`) of parity `e`.  *Alternative:* the image residues `W(2t) mod p`, `W(2u + 1) mod p`
  form a complete system mod `p`, then Lemma 1.
* **`cylCount_eq`** (100).  Window lemma reduces to `a = 0`, `N = P := 2AB`, `A = (qR)^L`, `B =
  (p/2)^{L'}`.  Write `x = u + 2A i`, `u < 2A`, `i < B`.  The forward condition depends only on
  `u` (`fwdItin_periodic`).  For fixed `u`, the AP lemma with multiplier `A` (coprime to `B`)
  turns the backward condition summed over `i` into the M2 count over `[0, 2B)` in the class of
  `u mod 2`.  So the joint count is (M1 count) · (M2 count) `= A F · B B_w = (P/2) F B_w`.
* **`cylCount_fwd`**, **`cylCount_bwd`** (10 each).  `cylCount_eq` with `[]`; `wordWeight _ _ [] = 1`.
* **`cylCount_condIndep`** (40).  Four instances of `cylCount_eq` (`markovPeriod p q L 0 ∣
  markovPeriod p q L L'` etc.: `Dvd.intro`), multiply in `ℚ`, `exact_mod_cast`.
* **`tenThirds_dependent`** (40).  `210 = markovPeriod 10 3 1 1`, `42 ∣ 210`, `10 ∣ 210`; six
  instances of `cylCount_eq` (`Nat.Coprime 10 3` by `norm_num`/`decide`), then `norm_num
  [wordWeight, fwdProb, fwdEven, bwdProb, bwdEven]` gives `37, 115, 63` and `37·210 ≠ 115·63`.  Cast
  the goal to `ℚ` first (`Nat.cast_injective`).  Do **not** `decide` the counts.
* **`cylCount_eq_odd`** (120).  Same skeleton.  Forward: the head condition `W(2t) + p m' ≡ g`
  fixes `m' mod 2` (`p` odd), so every step costs `½` and the next period gains a factor `2`
  (period `2^{L+1}(qR)^L`); use the AP lemma with `u = p` (coprime to `2qR`).  Backward:
  `wythoffInv_add` still holds, `2Q` is a unit mod `p`, period `p^{L'}`; the one-step count is
  `#{c < p : W⁻¹ c even} = q` (`c ↦ (−cq) mod p` bijective, no parity restriction).  Joint:
  `2^{L+1}(qR)^L` and `p^{L'}` are coprime.

Rough total: 2,000-2,300 lines.  Largest: Theorem M (M1, M2, joint), then §6.  Theorem C of the
note (the density ceiling `≤ c_M`) is deliberately not ratified: it needs natural densities,
`W^t x = e^{S_t} x + O_L(1)` bounds and Markov-walk survival limits (≈ 800+ lines on top).
