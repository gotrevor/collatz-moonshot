# KICKOFF 2026-10-16: the degree-d trap identity on `E^d` and the cubic trap member `A³ = 3A² − 1`

Repo `collatz-moonshot` (branch `wip/wythoff-trapd`, cut from `main` at `daf38cf`).  Close every
`sorry` in one new file (10 statements):

| file | content | sorries |
|---|---|---|
| `CollatzMoonshot/WythoffTrapDegree.lean` | synthetic division, the degree-`d` identity on `E^d`, the trap `T_d`, infinitely many infinite orbits (Weyl-conditional), `d = 2` consistency, the cubic member | 10 |

Imports: `Mathlib`, `CollatzMoonshot.AmusicalTrap` (proved: `InfinitelyManyInfiniteOrbits`,
`infinitelyManyInfiniteOrbits_of_trap`), `CollatzMoonshot.WythoffGeneral` (`wy`, `wyPerm`,
`wy_two_mul`, `wy_pos_iff`, `WeylEquidistributionMulti`), `CollatzMoonshot.WythoffCone`
(`alphaK`, `coneSet`; `coneEntry_infinite` is the style model for the entry argument).  Do not
edit any existing file except appending to `CollatzMoonshot.lean` (already done).

Source: `~/personal/tmp/amusical-agents/out/wythoff-solvable.md` §9, "The cubic (and degree-d)
analogue" (scripts `kcubic.py`, `kcubic_teeth.py` in `out/wythoff-solvable/`).

**Setup.**  `α` real, `A = α/2`, `W = wy α`; on an even point `W(v) = ⌊A v⌋` (`wy_of_even`).
Coefficients `p : ℕ → ℤ` with `A^d = Σ_{j<d} p_j A^j` (hypothesis `hP`; `p j` for `j ≥ d` is
unused).  `quotCoeff A d p k = q_k = A^{d−1−k} − Σ_{k<j<d} p_j A^{j−k−1}` are the coefficients of
`Q(t) = (P(t) − P(A))/(t − A)`, `P(t) = t^d − Σ_{j<d} p_j t^j` (`sub_mul_sum_quotCoeff`).
`ePhase α n i = A·Wⁱ(n) − W^{i+1}(n)` (the phase `f_{i+1}`).  `trapSetD α d = {n > 0 : Wⁱ(n)
even for i < d}`.  Cubic member: `cRoot ∈ (14/5, 29/10)` with `A³ = 3A² − 1` (`Classical.choose`,
pinned by `cRoot_spec` + `cRoot_unique` above 2), `alphaC = 2·cRoot ≈ 5.7587705`, `cubicP =
(−1, 0, 3)`, `cubicPerm = wyPerm alphaC`.

**Encoding choice.**  `p : ℕ → ℤ` with `Finset.range`/`Finset.Ioo` sums (no `Fin d` casts) and
`Q` by explicit coefficients rather than `P /ₘ (X − C A)` in `ℝ[X]`: the identity is then a
finite sum the proof unfolds directly, and `sub_mul_sum_quotCoeff` certifies the coefficients.
The Weyl theorem is stated at degree `d + 1` so that `hind : LinearIndependent ℚ fun i : Fin
(d + 1) => A^i` matches `WeylEquidistributionMulti`'s `Fin.cons 1 θ` with `θ : Fin d → ℝ`
without a `Fin (d − 1 + 1)` cast.

## Ratified, do not change

Every definition and theorem statement in the file:

* **Definitions:** `quotCoeff`, `ePhase`, `trapSetD`, `cRoot`, `alphaC`, `cubicP`, `cubicPerm`.
* **Synthetic division:** `sub_mul_sum_quotCoeff`, `quotCoeff_last` (proved), `quotCoeff_rec`,
  `mul_quotCoeff_zero`, `phase_identity`.
* **Identity and trap:** `wy_of_even`, `ePhase_eq_fract`, `ePhase_mem` (proved),
  `wy_iterate_eq_floor`, `wy_iterate_eq_of_trap`, `trapSetD_trap`,
  `wy_iterate_add_of_mem_trapSetD`, `trapSetD_entry_infinite`,
  `wyPerm_infinitelyManyInfiniteOrbits_of_trapD` (proved from the two before it).
* **`d = 2`:** `quotCoeff_two`, `trapSetD_two_alphaK` (proved), `wy_iterate_two_eq_floor`.
* **Cubic:** `exists_cRoot`, `cRoot_spec`, `cRoot_unique`, `alphaC_half`, `two_lt_alphaC`,
  `cubicPerm_apply`, `alphaC_pow`, `quotCoeff_cubic`, `quotCoeff_cubic_signs`,
  `cCubic_ne_zero_rat`, `natDegree_cCubic`, `linearIndependent_cRoot` (all proved),
  `wy_iterate_three_cubic`, `cubicSet_trap`, `cubicPerm_infinitelyManyInfiniteOrbits` (proved
  from the general sorried statements; they close automatically).

`WeylEquidistributionMulti` is a **literature hypothesis** (Weyl 1916 with the standard
Jordan-measurable extension, Kuipers-Niederreiter Ch. 1 §6): it stays a hypothesis of
`trapSetD_entry_infinite` and its two consumers; do not prove it and do not turn it into an
`axiom`.  `hind` (`deg A = d + 1`) is a genuine hypothesis (discharged for the cubic by
`linearIndependent_cRoot`).  Everything else is unconditional, for **every real `α`** and
**every `n ∈ ℤ`** (negatives included) in the identities.

## Rules

No `native_decide`, no axioms, no `maxHeartbeats` bumps.  Lean lines ≤ 100 characters.  **Never
change a ratified statement**; if one looks false, stop, record the counterexample in the
handoff and ask.  Commit after each proved lemma.  Notes as you go in `HANDOFF-wythoff-trapd.md`.
Helper lemmas and definitions are welcome (above their first use).  Build with
`lake build CollatzMoonshot.WythoffTrapDegree`.  Prove `wy_iterate_two_eq_floor` **from**
`wy_iterate_eq_floor` (not by citing `WythoffCone.wy_wy_of_even_even`): it is a consistency check
of the general statement.

## Truth checks already run

`tmp/drafter-trapd/check.py` (gitignored; `./check.py`, 10 s, output `check.out`; `quick` mode
2 s).  `A` is a certified 400-bit isolating interval; every floor/ceil of `W` is certified (both
ends agree) or the script aborts; the identity's floor term is evaluated in 130-digit `Decimal`
with a `10⁻⁶⁰` floor-safety margin; the Python `W` mirrors Lean's `wy` (`n % 2`, `n // 2`,
`(n + 1) // 2`, odd branch `⌈kβ⌉ − 1`).  **14 793 checks, 0 failures:**

* *Algebra (exact rationals, 2000 random `d ≤ 7`, `p`, `A`, `t`, `v`).*  `sub_mul_sum_quotCoeff`,
  `phase_identity`, `quotCoeff_rec`, `mul_quotCoeff_zero`, `quotCoeff_last`, `quotCoeff_two`,
  `quotCoeff_cubic`.
* *Known-answer controls.*  The scan `|p_j| ≤ 6` with `q_k ≤ 0`, `Q(1) > 0`, no rational root
  finds exactly the research note's **20** cubic members, smallest `α = 5.758770`.  At `d = 2`
  the general formula, Theorem A′'s `⌊(b − A){kα}⌋` (computed independently) and the direct
  `W²` agree on all 50 001 EE points of `|k| ≤ 5·10⁴` for `3 + √5`, `4 + 2√3` (cone, where K's
  exact `W² = bW + cn` also holds) and `1 + √5` (anticone).
* *General identity.*  On every `E^d` point of `[−10⁵, 10⁵]` (`[−5·10⁴, 5·10⁴]` for `d = 4`) for
  the 20 cubic members and 5 quartic members (`|p_j| ≤ 4`, e.g. `A⁴ = 4A³ − 2`): identity,
  exact form, `W^d` even (trap): 0 failures; `ePhase ∈ [0, 1)` asserted throughout.  The
  identity *with floor* also holds (0 failures) on every violating member below.
* *Cubic member.*  Root in `(14/5, 29/10)`, the only root `> 2` (others `0.6527`, `−0.5321`), no
  rational root; `q = (A² − 3A, A − 3, 1) = (−0.3473, −0.1206, 1)`, `Q(1) = 0.5321`;
  `W³ = 3W² − n` on all 75 000 EEE points of `[−3·10⁵, 3·10⁵]`; trap on `T_3 ∩ [1, 10⁵]`; the
  recurrence along the trap for 7 steps from 300 points.  *Weyl-conditional support:*
  `#T_3 ∩ [1, 3·10⁵]/X = 0.12499` (box count `1/8`) and entry points `0.08158/unit` against
  `2^{−3}(1 − 2/α) = 0.08159`; for two more cubics and two quartics the entry density matches
  `2^{−d}(1 − 2/α)` to `≤ 6·10⁻⁵`.
* **Teeth** (each must fail and does): `A³ = 3A² + A − 2` (`A′ + A″ < 0`) floors `{−1, 0}`,
  exact form fails at 1119 points, trap broken at 561; `A³ = 3A² − 3` (`q ≤ 0` but
  `Q(1) = −0.65 < 0`) floors `{0, +1}`, so the `Q(1)` hypothesis is needed; `A³ = 3A² + A − 1`,
  `3A² + 2A − 3` likewise; `2∛2` floors exactly `{−1, −2, −3}` (research note §4); dropping the
  floor term fails on all of these; the flipped sign `⌊+Σ q f⌋` fails on every one of the 25
  trap members; `quotCoeff` with exponent `j − k` (off by one) breaks `phase_identity` (1445 of
  2000) and the identity (12 503 failures on `A³ = 6A² − 4`).

## Paper proofs

### §1 Synthetic division (≈ 120 lines)

* **`quotCoeff_rec`** (25).  `k + 1 < d`: `Ioo k d = insert (k + 1) (Ioo (k + 1) d)`
  (`Finset.Ioo_insert_left` / `Nat.Ioo_succ_left`-style, or `Finset.sum_Ioo_...`); the `j = k + 1`
  term is `p_{k+1} A⁰`; `A·A^{j−k−2} = A^{j−k−1}` for `j ≥ k + 2` (`pow_succ`, `omega` on the
  exponents); `A·A^{d−2−k} = A^{d−1−k}`.
* **`mul_quotCoeff_zero`** (25).  `range d = insert 0 (Ioo 0 d)` for `d ≥ 1`; same computation.
* **`phase_identity`** (60).  Expand `Σ_{i<d} q_i (A v_i − v_{i+1}) = Σ_{i<d} A q_i v_i −
  Σ_{i<d} q_i v_{i+1}`; shift the second sum (`Finset.sum_range_succ'` /
  `Finset.sum_range_succ`) to `Σ_{1≤i<d} q_{i−1} v_i + q_{d−1} v_d`; termwise
  `A q_i − q_{i−1} = p_i` (`quotCoeff_rec` at `k = i − 1`), `A q_0 = P(A) + p_0`
  (`mul_quotCoeff_zero`), `q_{d−1} = 1` (`quotCoeff_last`).  `d = 0`: both sides `v_0`.  An
  alternative is induction-free `Finset.sum_bij` bookkeeping; whichever is shorter.
* **`sub_mul_sum_quotCoeff`** (10).  `phase_identity` with `v i = tⁱ`:
  `A tⁱ − t^{i+1} = −(t − A)tⁱ`, `Finset.mul_sum`.

### §2 The identity and the trap (≈ 180 lines)

* **`wy_iterate_eq_floor`** (50).  `d = 0` contradicts `hP` (`1 = 0`).  For `d ≥ 1` put
  `v i = ((wy α)^[i] n : ℝ)`; `phase_identity (α/2) d p v` with `hP` kills the `v 0` term; the
  summand `A v_i − v_{i+1}` is `ePhase α n i` by definition; split `range d = range (d − 1) ∪
  {d − 1}` (`Finset.sum_range_succ` after `d = (d − 1) + 1`), `quotCoeff_last`.  So
  `(W^d n − Σ p_j W^j n : ℝ) = X − f` with `f = ePhase α n (d − 1) ∈ [0, 1)` (`ePhase_mem`,
  `hE (d − 1)`); `Int.floor_eq_iff` (`⌊X⌋ = m` iff `m ≤ X < m + 1`) with `m` the integer, cast via
  `push_cast`.
* **`wy_iterate_eq_of_trap`** (50).  Show `⌊X⌋ = 0`, `X = Σ_{i<d−1} (−q_i) f_{i+1}`.  `X ≥ 0`:
  `Finset.sum_nonneg`, `mul_nonneg` (`hq`, `ePhase_mem`).  `X < 1`: if `d − 1 = 0` then `X = 0`.
  Else let `F = (range (d − 1)).sup' … f < 1`; `X ≤ F·Σ_{i<d−1}(−q_i)`
  (`Finset.sum_le_sum`, `mul_le_mul_of_nonneg_left`) and `Σ_{i<d−1}(−q_i) = 1 − Q(1) ≤ 1`
  (`Finset.sum_range_succ` at `d − 1`, `quotCoeff_last`, `hQ`), so `X ≤ F·(1 − Q(1)) ≤ F < 1`
  (`F ≥ 0`).  Then `wy_iterate_eq_floor`, `add_zero`.
* **`trapSetD_trap`** (30).  `n ∈ T_d`: `W n > 0` (`wy_pos_iff hα`).  For `i < d`:
  `(wy α)^[i] (wy α n) = (wy α)^[i + 1] n` (`Function.iterate_succ_apply`); if `i + 1 < d` it is
  `hE`; if `i + 1 = d`, `wy_iterate_eq_of_trap` gives `Σ_{j<d} p_j W^j n`, a sum of multiples of
  evens (`Finset.dvd_sum`, `Int.emod_emod_of_dvd`/`Int.even_iff`; `omega` per term).
* **`wy_iterate_add_of_mem_trapSetD`** (25).  `(wy α)^[j] n ∈ T_d` (induction with
  `trapSetD_trap`; `wyPerm_apply`), then `wy_iterate_eq_of_trap` at that point,
  `Function.iterate_add_apply` (`(wy α)^[j + i] n = (wy α)^[i] ((wy α)^[j] n)` after
  `add_comm`).
* **`wy_iterate_two_eq_floor`** (30).  `wy_iterate_eq_floor (d := 2) (p := fun j => if j = 0
  then c else b)` (`hP` from `hx`, `Finset.sum_range_succ`); `quotCoeff_two`; `ePhase α (2k) 0 =
  Int.fract (α/2·(2k)) = Int.fract (kα)` (`ePhase_eq_fract`, `ring_nf`);
  `−(A − b)f = (b − A)f`.

### §3 Entry points via Weyl (≈ 400 lines; hardest, last)

**`trapSetD_entry_infinite`.**  Write `D = d + 1` (the degree), `A = α/2 > 1`.

1. *Box ⇒ trap membership* (100).  For `k ≥ 1` put `N_i = ⌊k Aⁱ⌋`, `φ_i = {k Aⁱ}` (`i ≥ 1`),
   `φ_0 = 0`, `N_0 = k`, `ψ_i = φ_i − A φ_{i−1}`.  If `0 ≤ ψ_i < 1/2` for `1 ≤ i ≤ d` then
   `Wⁱ(2k) = 2N_i` for `i ≤ d`: by induction, `W(2N_{i−1}) = ⌊2A N_{i−1}⌋` (`wy_two_mul`) and
   `A N_{i−1} = k Aⁱ − A φ_{i−1} = N_i + ψ_i`, so `⌊2(N_i + ψ_i)⌋ = 2N_i`.  Hence `2k ∈ T_D`.
   Box: `B = Π_{i<d} [L_i, L_i + η)` in the coordinates `θ_i = A^{i+1}` (`i : Fin d`),
   `L_0 = 0`, `L_{i+1} = A(L_i + η)`; with `η = 1/(2(A + 2)^{d+1})` every `L_i + η < 1` and every
   `ψ ∈ [0, (A + 1)η) ⊆ [0, 1/2)`.  (Any explicit box with these two properties works; a cube
   `[c_i, c_i + η)` with `c_i = A(A + 2)^{i−1}·η`-type centres is fine too.)
2. *Weyl* (80).  `hW d θ` with `θ i = A^{(i:ℕ)+1}`: the `Fin.cons 1 θ` independence is `hind`
   after `Fin.cons` = `fun i : Fin (d + 1) => A^i` (`funext`, `Fin.cases`, `Fin.cons_zero`,
   `Fin.cons_succ`).  `B` is measurable (`MeasurableSet.univ_pi`, `measurableSet_Ico`); its
   frontier is null (`frontier_pi`-type lemma, or `frontier ⊆ closure \ interior` of a box =
   finite union of hyperplane slabs, each `volume = 0` via `Real.volume_singleton` and
   `MeasureTheory.Measure.pi`); `volume (B ∩ [0,1)^d) = η^d` (`Real.volume_pi_Ico` /
   `MeasureTheory.Measure.pi_pi`).  Conclude `#{k ≤ K : φ(k) ∈ B}/K → η^d > 0`, hence
   `#(T_D ∩ [1, X]) ≥ (η^d/4)·X` for all large `X` (`k ≤ X/2`).  `WythoffSporadic` has
   working measurable/frontier/volume code for planar sets (`volume_frontier_yWord`).
3. *Finite entry set ⇒ `O(log X)`* (180).  As `WythoffCone.coneEntry_infinite`: on `T_D`,
   `W(t) ≥ ⌊kα⌋ ≥ 2k = t` and `W(t) ≥ At − 1`, so `W(t) ≥ ((A + 1)/2)·t` once `t ≥ t₀ =
   2/(A − 1)`.  If the entry set `E` is finite, every `t ∈ T_D` with `t ≥ t₀` is `Wʲ(e)` for some
   `e ∈ E ∪ (T_D ∩ [1, t₀])` (backward inside `T_D` the values do not increase; strong induction
   as in `exists_entry`, with the finitely many small points as extra seeds).  Each seed's forward
   orbit has at most `log_{(A+1)/2}(X) + C` points `≤ X`, so `#(T_D ∩ [1, X]) ≤ C′ log X`,
   contradicting step 2.  Bookkeeping as in `coneEntry_infinite`: with `S` seeds, step 2 gives
   `X ≥ t₀` with more than `S·(log_{(A+1)/2} 2 + 1)` points of `T_D` in `[X, 2X)`, but each seed's
   orbit has at most `log_{(A+1)/2} 2 + 1` points there (consecutive points grow by `≥ (A+1)/2`).

`wyPerm_infinitelyManyInfiniteOrbits_of_trapD` and the cubic corollary then close by the proofs
already in the file.

**Order of attack:** §1 (`quotCoeff_rec`, `mul_quotCoeff_zero`, `phase_identity`,
`sub_mul_sum_quotCoeff`) → §2 (`wy_iterate_eq_floor`, `wy_iterate_eq_of_trap`,
`trapSetD_trap`; this closes the cubic identity and trap, the headline unconditional results) →
`wy_iterate_add_of_mem_trapSetD`, `wy_iterate_two_eq_floor` → §3.  If time is short, §1 + §2 are
the deliverable; §3 is the only conditional piece.

Rough total: 650-850 lines (§3 ≈ 400 of it).

**Out of scope (later layers):** an unconditional entry-point theorem (the trap set is a model
set whose window has nonempty interior, hence relatively dense; or, for the cubic, a syndetic
argument along the Pisot traces `N_j = Tr Aʲ`, whose phase drift is ∝ `(1, A′)` in the
`ψ`-coordinates); the entry density `2^{−d}(1 − 2/α)` (needs the shear volume of the full parity
region, not just a sub-box); the `D = ±1` dictionary for K members (research note §9).
