/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.AmusicalTrap
import CollatzMoonshot.MonotonePotential
import CollatzMoonshot.WythoffGeneral
import CollatzMoonshot.WythoffSporadic

/-!
# Theorem Y′: the mirror of the sporadic cubic member

Research note `wythoff-classify`, §4.  Let `x ≈ 0.5259574806` be the real root of
`x³ + x² + 3x − 2` (`WythoffSporadic.yRoot`) and let `W′ = W_{β}` with `β = 2x ≈ 1.0519150`
(`betaY`), the mirror of Theorem Y's `W_α`, `α = 2x/(2x − 1) ≈ 20.26227` (`alphaY`).  Since
`β/(β − 1) = α`, `W′(2k) = ⌊2kx⌋` (`v ↦ ⌊xv⌋` on evens, a descent) and
`W′(2k − 1) = ⌈kα⌉ − 1` (`s ↦ ⌈A(s + 1)⌉ − 1`, `A = α/2`, an ascent).

1. **Recurrence** (`wy_betaY_iterate_four_eq`).  If `s` is odd and `W′(s), W′²(s), W′³(s)` are
   even, then `W′⁴(s) = 4(s + 1) + W′³(s) − W′²(s) − 1`, for every `s ∈ ℤ`.  The right side is
   odd, so after an odd point at most three even points follow (`exists_odd_iterate_Ym`).
2. **Classification** (Lemma P, `MonotonePotential`, with `S` = odds, `Φ = ∅`, `T = 4`).
   `W′` has **no finite orbit in `ℕ⁺`**; every orbit tends to `∞` both ways; its minimum is the
   unique odd `y` with `W′⁻¹(y), …, W′⁻⁴(y)` all even.
3. **Count.**  `#{minima ≤ X} + #{odd s ≤ X : R′(s) ≤ X} = ⌈X/2⌉` exactly, and
   `R′(s) ≥ 4s/3`, so `#{minima ≤ X} ≥ ⌈X/2⌉ − ⌊(3X + 4)/8⌋`: infinitely many infinite
   orbits.
4. **Density** (conditional on two-dimensional Weyl equidistribution): the same
   `d = 3/10 + x/8 + x²/10 ≈ 0.39340781` as Theorem Y (`WythoffSporadic.densityY`).

**Proof of the recurrence: Theorem M (main/mirror identity).**  For odd `s` put `m = s + 1`
(even), `v_i = W′^i(s)`, and the mirror phases (`ymF1`, `ymFeven`)
`a = (v_1 + 1) − Am ∈ [0, 1)` (`v_1 = ⌈Am⌉ − 1`) and, for even `v`,
`b(v) = (W′(v) + 1) − xv ∈ (0, 1]` (`W′(v) = ⌊xv⌋`).  Then `(−m; −v_1, −v_2, …)` obeys the
recurrences of Theorem Y's main run `(n; W(n) + 1, W²(n) + 1, …)` with the **same** phase
symbols: main `w_1 = An + 1 − f₁`, `w′ = xw + 1 − f(·)`; mirror `−v_1 = A(−m) + 1 − a`,
`−v′ = x(−v) + 1 − b(v)`.  Hence every phase identity of `WythoffSporadic` transfers verbatim
(`wy_betaY_iterate_three_phase`, `wy_betaY_iterate_four_phase`), with `(f₁, f₂, f₃, f₄)`
replaced by `(a, b(v_1), b(v_2), b(v_3))`, which lie in the same box `[0, 1) × (0, 1]³`.  So the
polygon lemmas `yPhase3_mem`, `yPhase4_of_one`, `yPhase4_of_neg_one`, `yPhase4_sub` apply
unchanged, and Theorem Y's recurrence `w_4 = 4n + w_3 − w_2 + 1` becomes
`−v_4 = −4m − v_3 + v_2 + 1`.  The run laws, `J = 3` and the return slopes `c_j = A xʲ` agree
with Theorem Y's.

**(H2).**  The mirror sandwich: `v_1 ≥ A(s + 1) − 1`, `v_{i+1} > x v_i − 1`, so
`W′^{j+1}(s) > c_j(s + 1) − (1 + x + ⋯ + xʲ) ≥ 1.474(s + 1) − 1.95 ≥ 4s/3` for `s ≥ 5`; `s = 1, 3`
directly (`W′(1) = 20, W′(20) = 10, W′(10) = 5`; `W′(3) = 40, W′(40) = 21`).  Measured:
`min R′(s)/s = 1.4731` at `s = 93`.

Truth checks: `tmp/drafter-classify/check.py` (certified 400-bit interval arithmetic; census
786 810 minima `≤ 2·10⁶`, the research note's number; 4-level test = brute force on
`y ≤ 2·10⁴`, the 3-level test fails).
-/

namespace CollatzMoonshot.WythoffMirrorY

open CollatzMoonshot.WythoffGeneral CollatzMoonshot.MonotonePotential
open CollatzMoonshot.WythoffSporadic
open CollatzMoonshot.AmusicalTrap (permOrbit InfinitelyManyInfiniteOrbits)
open Filter Topology

/-! ## The mirror parameter -/

/-- **(proved).**  `β = 2x > 1` (`yRoot_spec`). -/
theorem one_lt_betaY : 1 < betaY := by
  unfold betaY; linarith [yRoot_spec.1]

/-- **(proved).**  `β < 2`. -/
theorem betaY_lt_two : betaY < 2 := by
  unfold betaY; linarith [yRoot_spec.2.1]

/-- **(proved).**  `β/(β − 1) = α` (definitional). -/
theorem betaY_div_sub_one : betaY / (betaY - 1) = alphaY := by
  unfold betaY alphaY; rfl

/-- `W_β` for Theorem Y′, as a permutation of `ℤ`. -/
noncomputable def ymPerm : Equiv.Perm ℤ :=
  wyPerm betaY one_lt_betaY

theorem ymPerm_apply (n : ℤ) : ymPerm n = wy betaY n := rfl

/-! ## The mirror phases -/

/-- The first (ascending) mirror phase `a = (W′(s) + 1) − (α/2)(s + 1)` (in `[0, 1)` for odd
`s`); it plays the role of `yF1`. -/
noncomputable def ymF1 (s : ℤ) : ℝ :=
  (wy betaY s : ℝ) + 1 - alphaY / 2 * ((s : ℝ) + 1)

/-- The descending mirror phase `b(v) = (W′(v) + 1) − xv` (in `(0, 1]` for even `v`); it plays
the role of `yFodd`. -/
noncomputable def ymFeven (v : ℤ) : ℝ :=
  (wy betaY v : ℝ) + 1 - yRoot * v

/-- **(drafted, 99%).**  For odd `s`, `0 ≤ a < 1`.  Paper proof: `s = 2k − 1`,
`W′(s) = ⌈kα⌉ − 1` (`wy_two_mul_sub_one`, `betaY_div_sub_one`) and `(α/2)(s + 1) = kα`;
`Int.le_ceil`, `Int.ceil_lt_add_one`. -/
theorem ymF1_mem {s : ℤ} (hs : s % 2 = 1) : 0 ≤ ymF1 s ∧ ymF1 s < 1 := by
  sorry

/-- **(drafted, 99%).**  For even `v`, `0 < b(v) ≤ 1` (`W′(2k) = ⌊2kx⌋`, `Int.floor_le`,
`Int.lt_floor_add_one`). -/
theorem ymFeven_mem {v : ℤ} (hv : v % 2 = 0) : 0 < ymFeven v ∧ ymFeven v ≤ 1 := by
  sorry

/-! ## Theorem Y′ (1): the recurrence on `O E³` -/

/-- **(drafted, 98%; algebra, any parities).**  For odd `s`:
`W′³ = −2(s + 1) + W′ − W′² − 1 − Δ′(a, b(W′ s)) + b(W′² s)`.  Paper proof: Theorem M (module
docstring) applied to `wy_iterate_three_phase`; directly, unfold and `linear_combination` with
`g_mul_alphaY` (`(1 − x − x²) α = 4`), exactly as there. -/
theorem wy_betaY_iterate_three_phase {s : ℤ} (hs : s % 2 = 1) :
    (((wy betaY)^[3] s : ℤ) : ℝ) =
      -2 * ((s : ℝ) + 1) + wy betaY s - (wy betaY)^[2] s - 1 -
        yPhase3 (ymF1 s) (ymFeven (wy betaY s)) + ymFeven ((wy betaY)^[2] s) := by
  sorry

/-- **(drafted, 98%; algebra, any parities).**  For odd `s`:
`W′⁴ = 2(s + 1) + W′ − 2W′² − 4 + g a + (2 + x²) b₂ + x b₃ + b₄` with `b_i` the descending phases
at `W′ s, W′² s, W′³ s` and `g = 1 − x − x²`.  Paper proof: Theorem M applied to
`wy_iterate_four_phase` (`linear_combination` with `g_mul_alphaY` and the cubic). -/
theorem wy_betaY_iterate_four_phase {s : ℤ} (hs : s % 2 = 1) :
    (((wy betaY)^[4] s : ℤ) : ℝ) =
      2 * ((s : ℝ) + 1) + wy betaY s - 2 * (wy betaY)^[2] s - 4 +
        (1 - yRoot - yRoot ^ 2) * ymF1 s + (2 + yRoot ^ 2) * ymFeven (wy betaY s) +
        yRoot * ymFeven ((wy betaY)^[2] s) + ymFeven ((wy betaY)^[3] s) := by
  sorry

/-- **(drafted, 98%).**  On `O E E`, `W′³(s) − (−2(s + 1) + W′(s) − W′²(s) − 1) ∈ {−1, 0, 1}`,
for every `s ∈ ℤ`.  Paper proof: it is the integer `b(W′² s) − Δ′`, with `Δ′ ∈ (−1, 2)`
(`yPhase3_mem`, `ymF1_mem`, `ymFeven_mem`) and `b ∈ (0, 1]`. -/
theorem wy_betaY_iterate_three_sub_mem {s : ℤ} (hs : s % 2 = 1) (h₁ : wy betaY s % 2 = 0)
    (h₂ : (wy betaY)^[2] s % 2 = 0) :
    (wy betaY)^[3] s - (-2 * (s + 1) + wy betaY s - (wy betaY)^[2] s - 1) ∈
      ({-1, 0, 1} : Set ℤ) := by
  sorry

/-- **(drafted, 95%; Theorem Y′ (1)).**  If `s` is odd and `W′(s), W′²(s), W′³(s)` are even,
then `W′⁴(s) = 4(s + 1) + W′³(s) − W′²(s) − 1`; for every `s ∈ ℤ`.  Paper proof: as
`wy_iterate_four_eq`.  `t := Δ′(a, b₂) − b₃ = −(W′³ − (−2(s + 1) + W′ − W′² − 1))`
(`wy_betaY_iterate_three_phase`) is odd (`W′, W′², s + 1` even, `W′³` even), so `t = ±1`
(`wy_betaY_iterate_three_sub_mem`).  `u := W′⁴ − (2(s + 1) + W′ − 2W′² − 4) = 2 − Δ_t + b₄`
(`wy_betaY_iterate_four_phase`, `yPhase4_sub` with `b₃ = Δ′ − t`).  `t = 1`: `Δ′ ≥ 1`,
`Δ_1 ∈ (1, 2)` (`yPhase4_of_one`), `u = 1`; `t = −1`: `Δ′ ≤ 0`, `a < 1`, `Δ_{−1} ∈ (−1, 0)`
(`yPhase4_of_neg_one`), `u = 3`.  So `u = 2 − t`; eliminate `t`.  (Main/mirror dictionary:
`n ↦ −(s + 1)`, `W^i n + 1 ↦ −W′^i s`, `(f₁, f(·)) ↦ (a, b(·))`.) -/
theorem wy_betaY_iterate_four_eq {s : ℤ} (hs : s % 2 = 1)
    (heven : ∀ i : ℕ, 1 ≤ i → i ≤ 3 → (wy betaY)^[i] s % 2 = 0) :
    (wy betaY)^[4] s = 4 * (s + 1) + (wy betaY)^[3] s - (wy betaY)^[2] s - 1 := by
  sorry

/-- **(drafted, 95%; Theorem Y′ (1), runs).**  After an odd point at most three even points
follow: some `W′^{j+1}(s)`, `j ≤ 3`, is odd.  Paper proof: `wy_betaY_iterate_four_eq`. -/
theorem exists_odd_iterate_Ym {s : ℤ} (hs : s % 2 = 1) :
    ∃ j ≤ 3, (wy betaY)^[j + 1] s % 2 = 1 := by
  sorry

/-- **(drafted, 96%; the (H2) input).**  For `s > 0` odd, `j ≤ 3`, and `W′(s), …, W′ʲ(s)` even:
`4s ≤ 3·W′^{j+1}(s)`.  Paper proof: module docstring (mirror sandwich; `s ∈ {1, 3}` by direct
evaluation with `yRoot_bounds`, `alphaY_bounds`). -/
theorem le_wy_betaY_iterate_of_even_run {s : ℤ} (hs0 : 0 < s) (hs : s % 2 = 1) {j : ℕ}
    (hj : j ≤ 3) (heven : ∀ i : ℕ, 1 ≤ i → i ≤ j → (wy betaY)^[i] s % 2 = 0) :
    4 * s ≤ 3 * (wy betaY)^[j + 1] s := by
  sorry

/-! ## Theorem Y′ (2)-(4): classification, count, density -/

/-- **(drafted, 96%; Theorem Y′ (2)).**  Lemma P applies with `S` = odds, `Φ = ∅`, `T = 4`.
Paper proof: `pos_iff` is `wy_pos_iff`; `mem_fix_iff` is trivial; (H1) is `wy_lt_of_even`
(`β < 2`); (H2): by `exists_odd_iterate_Ym` the first return word is `O Eʲ`, `j ≤ 3`
(`Nat.find`), and `R′(s) ≥ 4s/3 > s` by `le_wy_betaY_iterate_of_even_run`. -/
theorem hyp_ymPerm : Hyp ymPerm {n | n % 2 = 1} ∅ 4 := by
  sorry

/-- **(drafted, 96%).**  The first return to the odds at least multiplies by `4/3`. -/
theorem returnMap_ymPerm_ge {s : ℤ} (hs0 : 0 < s) (hs : s % 2 = 1) :
    4 * s ≤ 3 * returnMap ymPerm {n | n % 2 = 1} s := by
  sorry

/-- **(proved from `hyp_ymPerm`; Theorem Y′ (2)).**  No finite orbit in `ℕ⁺`
(`permOrbit_infinite`). -/
theorem permOrbit_ymPerm_infinite {x : ℤ} (hx : 0 < x) : (permOrbit ymPerm x).Infinite := by
  exact permOrbit_infinite hyp_ymPerm hx (Set.notMem_empty x)

/-- **(proved from `hyp_ymPerm`; Theorem Y′ (2), forward escape).** -/
theorem tendsto_ymPerm_pow {x : ℤ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => (ymPerm ^ n) x) atTop atTop :=
  tendsto_pow hyp_ymPerm hx (Set.notMem_empty x)

/-- **(proved from `hyp_ymPerm`; Theorem Y′ (2), backward escape).** -/
theorem tendsto_ymPerm_pow_neg {x : ℤ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => (ymPerm ^ (-(n : ℤ))) x) atTop atTop :=
  tendsto_pow_neg hyp_ymPerm hx (Set.notMem_empty x)

/-- **(drafted, 96%; Theorem Y′ (2), minima).**  For `x > 0`: `x` is the minimum of its orbit
iff `x` is odd and its four predecessors are even (`isOrbitMin_iff`, `T = 4`).  (Three
predecessors do not suffice: 592 mismatches with brute force for `y ≤ 2·10⁴`.) -/
theorem isOrbitMin_ymPerm_iff {x : ℤ} (hx : 0 < x) :
    IsOrbitMin ymPerm x ↔
      x % 2 = 1 ∧ ∀ i : ℕ, 1 ≤ i → i ≤ 4 → (ymPerm ^ (-(i : ℤ))) x % 2 = 0 := by
  sorry

/-- **(drafted, 96%; Theorem Y′ (3), exact count).**
`#{minima ≤ X} + #{odd s ∈ [1, X] : R′(s) ≤ X} = ⌈X/2⌉` (no `Φ` term).  Paper proof:
`minCount_add_returnCount` with `Φ = ∅`, as `WythoffLine.minCount_gmPerm_add`. -/
theorem minCount_ymPerm_add (X : ℕ) :
    minCount ymPerm X + returnCount ymPerm {n | n % 2 = 1} ∅ X = (X + 1) / 2 := by
  sorry

/-- **(drafted, 96%; Theorem Y′ (3), unconditional lower bound).**
`#{minima ≤ X} ≥ ⌈X/2⌉ − ⌊(3X + 4)/8⌋`.  Paper proof: `R′(s) ≤ X` forces `4s ≤ 3X`
(`returnMap_ymPerm_ge`), and there are at most `⌊(3X + 4)/8⌋` odd `s ≥ 1` with `4s ≤ 3X`. -/
theorem minCount_ymPerm_ge (X : ℕ) :
    ((X : ℤ) + 1) / 2 - (3 * (X : ℤ) + 4) / 8 ≤ minCount ymPerm X := by
  sorry

/-- **(drafted, 96%; Theorem Y′ (2)).**  Infinitely many infinite orbits.  Paper proof:
`minCount_ymPerm_ge` is unbounded; `infinitelyManyInfiniteOrbits_of_minima`. -/
theorem ymPerm_infinitelyManyInfiniteOrbits : InfinitelyManyInfiniteOrbits ymPerm := by
  sorry

/-- **(drafted, 88%; Theorem Y′ (4), density, conditional).**  Assuming multidimensional Weyl
equidistribution, the orbit minima have Theorem Y's density
`d = 3/10 + x/8 + x²/10 ≈ 0.39340781`.  Paper proof: by `minCount_ymPerm_add`,
`d = 1/2 − (1/2) Σ_{j ≤ 3} P′_j / c_j`, with `P′_j` the density among the odds of the return
word `O Eʲ` and `R′(s) = c_j (s + 1) + O(1)` (the mirror sandwich).  For `s = 2k − 1`,
`m = 2k` and the run phases are `({k c_0}, {k c_1})`, `c_0 = α/2`, `c_1 = xα/2`, Theorem Y's
torus coordinates (`yc0`, `yc1`); by Theorem M the cylinders `O Eʲ` are Theorem Y's cylinders
`E Oʲ` under the phase map `(a, b) ↦ (f₁, f₂)` (same box, same polygons `R_a`, `R_b`), so
`P′ = P = (1/2, 1/4, 1/(4(1 + x)), x/(4(1 + x)))`, the slopes agree, and the sum is
`densityY_sum_eq`.  (Census: 786 810 minima `≤ 2·10⁶`, `dX = 786 815.6`.) -/
theorem tendsto_minCount_ymPerm (hW : WeylEquidistributionMulti) :
    Tendsto (fun X : ℕ => (minCount ymPerm X : ℝ) / X) atTop (𝓝 densityY) := by
  sorry

end CollatzMoonshot.WythoffMirrorY
