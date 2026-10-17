/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.AmusicalTrap
import CollatzMoonshot.MonotonePotential
import CollatzMoonshot.WythoffGeneral

/-!
# Theorem Y: a sporadic cubic Wythoff member solved by a recurrence

Research note `wythoff-solvable`, §4 (b3).  Let `x ≈ 0.5259574806` be the real root of
`x³ + x² + 3x − 2` (`yRoot`; the polynomial is strictly increasing, so the root is unique,
`yRoot_unique`).  Put `β = 2x ≈ 1.0519` and `α = 2x/(2x − 1) ≈ 20.26227`, so `β = α/(α − 1)` and
`α³ − 22α² + 36α − 16 = 0`.  Let `W = W_α` (`WythoffGeneral.wy`).  No composite slope
`c_j = A xʲ` (`A = α/2`; `c_0, …, c_4 ≈ 10.13, 5.33, 2.80, 1.474, 0.775`) is an integer, so Theorem
G does not apply; instead:

1. **Recurrence** (`wy_iterate_four_eq`).  If `n` is even and `W(n), W²(n), W³(n)` are odd, then
   `W⁴(n) = 4n + W³(n) − W²(n)`, for every `n ∈ ℤ`.  The right side is even, so after an even
   point at most three odd points follow (`exists_even_iterate_Y`).
2. **Classification** (Lemma P, `MonotonePotential`, with `S` = evens, `Φ = {1}`, `T = 4`).  `{1}`
   is the only finite orbit in `ℕ⁺`; every other orbit tends to `∞` both ways; its minimum is the
   unique even `y` with `W⁻¹(y), …, W⁻⁴(y)` all odd.
3. **Count.**  `#{minima ≤ X} + #{even s ≤ X : R(s) ≤ X} = 1 + ⌊X/2⌋` exactly, and
   `R(s) ≥ 4s/3` (the smallest return slope is `c_3 ≈ 1.474`), so
   `#{minima ≤ X} ≥ 1 + ⌊X/2⌋ − ⌊3X/8⌋`: infinitely many infinite orbits.
4. **Density** (conditional on two-dimensional Weyl equidistribution, a literature hypothesis):
   `d = 3/10 + x/8 + x²/10 ≈ 0.3934078`, with minimal polynomial `1280t³ − 352t² − 52t − 3`.

**Proof of the recurrence: phases and a polygon computation.**  Write `n = 2k`, `g = 1 − x − x²`
(`≈ 0.1974`), and define the phases of the run (`yF1`, `yFodd`):
`f₁ = kα − W(n) ∈ [0, 1)` (floor step) and, for odd `v`, the odd-step defect
`f(v) = x(v + 1) − W(v) ∈ (0, 1]` (`W(v) = ⌈x(v + 1)⌉ − 1`, since `((v + 1)/2)·β = x(v + 1)`).
Put `f₂ = f(W n)`, `f₃ = f(W² n)`, `f₄ = f(W³ n)`.

* *Algebra (no floors, any parities; `wy_iterate_three_phase`, `wy_iterate_four_phase`).*  Using
  `kα = n·x/(2x − 1)` and the cubic (`gx/(2x − 1) = 2`, `x³ = 2 − 3x − x²`):
  `W³ = −2n + W − W² + Δ′ − f₃` with `Δ′ = g f₁ + 2x + x² − (1 + x) f₂` (`yPhase3`), and
  `W⁴ = 2n + W − 2W² + 2 − g f₁ − (2 + x²) f₂ − x f₃ − f₄`.  (Expand
  `f₂ = x(W + 1) − W²`, `f₃ = x(W² + 1) − W³`, `f₄ = x(W³ + 1) − W⁴`; everything cancels except a
  multiple of `n·(x³ + x² + 3x − 2)`.)
* *Integers.*  `t := W³ − (−2n + W − W²) = Δ′ − f₃` is an integer; on the box `Δ′ ∈ (−1, 2)`
  (`yPhase3_mem`) and `f₃ ∈ (0, 1]`, so `t ∈ {−1, 0, 1}` (`wy_iterate_three_sub_mem`).  With `W`,
  `W²` odd, `t ≡ W³ (mod 2)`, so `W³` odd forces `t = ±1`.
  `u := W⁴ − (2n + W − 2W²) = Δ_t − f₄` where, substituting `f₃ = Δ′ − t` (`yPhase4_sub`),
  `Δ_t = 3x − x² + x t − g(1 + x) f₁ − (2 − x) f₂` (`yPhase4`), affine in `(f₁, f₂)`.
* *Polygon.*  `t = 1` means `Δ′ = 1 + f₃ ≥ 1`: on the polygon `R_a = {Δ′ ≥ 1}` of the box,
  with vertices `(0, 0), (1, 0), (1, x/(1 + x)), (0, (2x + x² − 1)/(1 + x))`, `Δ_1` takes the
  values `1.8272, 1.5260, 1.0179, 1.5098`, so `1 < Δ_1 < 2` (`yPhase4_of_one`) and `u = 1`.
  `t = −1` means `Δ′ = f₃ − 1 ≤ 0`: on `R_b = {Δ′ ≤ 0}`, with vertices
  `(0, (2x + x²)/(1 + x)), (0, 1), (1, 1)`, `Δ_{−1}` takes the values `−0.5081, −0.6988, −1`; the
  value `−1` is attained only at the corner `f₁ = 1`, excluded since `f₁ < 1`, so
  `−1 < Δ_{−1} < 0` (`yPhase4_of_neg_one`) and `u = −1`.  In both cases `u = t`, and eliminating
  `t` gives `W⁴ = 4n + W³ − W²`.  No irrationality or equidistribution is used.

Each polygon bound is a Farkas certificate: an affine function of `(f₁, f₂)` minus its bound is a
nonnegative combination of the constraints `f₁ ≥ 0`, `1 − f₁ ≥ 0` (or `> 0`), `f₂ ≥ 0`,
`1 − f₂ ≥ 0`, `Δ′ − 1 ≥ 0` (resp. `−Δ′ ≥ 0`) plus a constant that is positive by
`yRoot_bounds` (e.g. `Δ_1 − 1 = λ(Δ′ − 1) + μ(1 − f₁) + κ` with `λ = (2 − x)/(1 + x)`,
`μ = g(λ + 1 + x)`, `κ = Δ_1(1, x/(1 + x)) − 1 ≈ 0.0179`).  The multipliers are polynomials in
`x`, so after clearing the denominator `1 + x` this is `nlinarith` with the products of the
box constraints and the bounds on `x`.

Truth checks: `tmp/drafter-Y/check.py` (certified 384-bit interval arithmetic; the recurrence on
all 17 242 `E O³` points of `[−2·10⁵, 2·10⁵]`; Lemma P test = brute-force minima for
`1 < y ≤ 2·10⁴` (7 867); census 786 811 minima `≤ 2·10⁶` besides `1`, as in the research note).
-/

namespace CollatzMoonshot.WythoffSporadic

open CollatzMoonshot.WythoffGeneral CollatzMoonshot.MonotonePotential
open CollatzMoonshot.AmusicalTrap (permOrbit InfinitelyManyInfiniteOrbits)
open Filter Topology Polynomial

/-! ## The root `x` and the parameters `α`, `β` -/

open Classical in
/-- The real root `x ∈ (1/2, 3/5)` of `x³ + x² + 3x − 2` (`yRoot_spec`). -/
noncomputable def yRoot : ℝ :=
  if h : ∃ x : ℝ, 1 / 2 < x ∧ x < 3 / 5 ∧ x ^ 3 + x ^ 2 + 3 * x - 2 = 0 then h.choose else 0

/-- `α = 2x/(2x − 1) ≈ 20.26227`. -/
noncomputable def alphaY : ℝ :=
  2 * yRoot / (2 * yRoot - 1)

/-- `β = 2x = α/(α − 1) ≈ 1.05192`. -/
noncomputable def betaY : ℝ :=
  2 * yRoot

/-- The cubic changes sign on `[1/2, 3/5]` (IVT). -/
theorem exists_yRoot : ∃ x : ℝ, 1 / 2 < x ∧ x < 3 / 5 ∧ x ^ 3 + x ^ 2 + 3 * x - 2 = 0 := by
  have hc : ContinuousOn (fun x : ℝ => x ^ 3 + x ^ 2 + 3 * x - 2) (Set.Icc (1 / 2) (3 / 5)) := by
    fun_prop
  obtain ⟨x, ⟨h1, h2⟩, hx⟩ := intermediate_value_Icc (by norm_num) hc
    (show (0 : ℝ) ∈ Set.Icc _ _ by constructor <;> norm_num)
  simp only at hx
  refine ⟨x, lt_of_le_of_ne h1 ?_, lt_of_le_of_ne h2 ?_, hx⟩ <;> rintro rfl <;> norm_num at hx

/-- `F(x) = x³ + x² + 3x − 2` is strictly increasing. -/
theorem yCubic_lt {a b : ℝ} (h : a < b) :
    a ^ 3 + a ^ 2 + 3 * a - 2 < b ^ 3 + b ^ 2 + 3 * b - 2 := by
  have : 0 < b ^ 2 + a * b + a ^ 2 + b + a + 3 := by
    nlinarith [sq_nonneg (a + b + 1), sq_nonneg (a - b)]
  nlinarith [mul_pos (sub_pos.2 h) this]

/-- **(drafted, 99%).**  The root exists.  Paper proof: IVT for `F(x) = x³ + x² + 3x − 2` on
`[1/2, 3/5]`: `F(1/2) = −1/8 < 0`, `F(3/5) = 0.176 > 0`; then `dif_pos`,
`Classical.choose_spec`. -/
theorem yRoot_spec :
    1 / 2 < yRoot ∧ yRoot < 3 / 5 ∧ yRoot ^ 3 + yRoot ^ 2 + 3 * yRoot - 2 = 0 := by
  unfold yRoot
  rw [dif_pos exists_yRoot]
  exact exists_yRoot.choose_spec

/-- **(drafted, 99%).**  `x³ + x² + 3x − 2` has exactly one real root.  Paper proof: it is
strictly increasing (`F′ = 3x² + 2x + 3 > 0`; or directly, `F(y) − F(x) =
(y − x)(y² + xy + x² + y + x + 3)` and the second factor is `> 0`). -/
theorem yRoot_unique {y : ℝ} (hy : y ^ 3 + y ^ 2 + 3 * y - 2 = 0) : y = yRoot := by
  have h := yRoot_spec.2.2
  rcases lt_trichotomy y yRoot with hl | he | hl
  · linarith [yCubic_lt hl]
  · exact he
  · linarith [yCubic_lt hl]

/-- **(drafted, 99%).**  Interval bounds used by the polygon lemmas.  Paper proof: `F` is
increasing and `F(0.52595748) < 0 < F(0.52595749)` (`norm_num`). -/
theorem yRoot_bounds : (52595748 : ℝ) / 10 ^ 8 < yRoot ∧ yRoot < 52595749 / 10 ^ 8 := by
  have h := yRoot_spec.2.2
  constructor
  · by_contra hc
    rcases (not_lt.1 hc).lt_or_eq with hl | he
    · have := yCubic_lt hl; norm_num at this; linarith
    · rw [he] at h; norm_num at h
  · by_contra hc
    rcases (not_lt.1 hc).lt_or_eq with hl | he
    · have := yCubic_lt hl; norm_num at this; linarith
    · rw [← he] at h; norm_num at h

/-- The cubic has no rational root (a rational root of the monic integer cubic is an integer,
and `F(z) ≤ −2` for `z ≤ 0`, `F(z) ≥ 3` for `z ≥ 1`). -/
theorem yCubic_ne_zero_rat (q : ℚ) : q ^ 3 + q ^ 2 + 3 * q - 2 ≠ 0 := by
  intro h
  have hmon : (X ^ 3 + X ^ 2 + C 3 * X - C 2 : ℤ[X]).Monic := by monicity!
  have hr : aeval q (X ^ 3 + X ^ 2 + C 3 * X - C 2 : ℤ[X]) = 0 := by
    simp only [map_sub, map_add, map_pow, map_mul, aeval_X, aeval_C]
    simpa using h
  obtain ⟨z, hz⟩ := isInteger_of_is_root_of_monic hmon hr
  have hz' : (z : ℚ) = q := hz
  subst hz'
  have hz3 : z ^ 3 + z ^ 2 + 3 * z - 2 = 0 := by exact_mod_cast h
  rcases le_or_gt z 0 with h0 | h0
  · nlinarith [sq_nonneg z, sq_nonneg (z + 1)]
  · nlinarith [sq_nonneg z, sq_nonneg (z - 1)]

theorem natDegree_yCubic : (X ^ 3 + X ^ 2 + C 3 * X - C 2 : ℚ[X]).natDegree = 3 := by
  compute_degree!

theorem irreducible_yCubic : Irreducible (X ^ 3 + X ^ 2 + C 3 * X - C 2 : ℚ[X]) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [natDegree_yCubic]; decide
  · intro q hq
    apply yCubic_ne_zero_rat q
    simpa using hq

/-- **(drafted, 99%).**  `x` is irrational: a rational root of the monic integer cubic would be
an integer dividing `2`, and `F(±1), F(±2) = 3, −5, 16, −12 ≠ 0`. -/
theorem irrational_yRoot : Irrational yRoot := by
  rintro ⟨q, hq⟩
  apply yCubic_ne_zero_rat q
  have h := yRoot_spec.2.2
  rw [← hq] at h
  exact_mod_cast h

/-- **(drafted, 97%).**  `deg x = 3`: `1, x, x²` are `ℚ`-independent.  Paper proof: the monic cubic
has no rational root (`irrational_yRoot`'s argument), hence is irreducible over `ℚ` and is the
minimal polynomial of `x`; a `ℚ`-relation `a + bx + cx² = 0` would give a polynomial of degree
`≤ 2` vanishing at `x` (`minpoly.degree_le_of_ne_zero`). -/
theorem linearIndependent_yRoot : LinearIndependent ℚ fun i : Fin 3 => yRoot ^ (i : ℕ) := by
  have hmin : (X ^ 3 + X ^ 2 + C 3 * X - C 2 : ℚ[X]) = minpoly ℚ yRoot := by
    apply minpoly.eq_of_irreducible_of_monic irreducible_yCubic
    · simp only [map_sub, map_add, map_pow, map_mul, aeval_X, aeval_C]
      simpa using yRoot_spec.2.2
    · monicity!
  have h := linearIndependent_pow (K := ℚ) yRoot
  rw [← hmin, natDegree_yCubic] at h
  exact h

/-- **(proved from `yRoot_spec`).**  `β = α/(α − 1)` (`field_simp`; `2x − 1 > 0`). -/
theorem alphaY_div_sub_one : alphaY / (alphaY - 1) = betaY := by
  have h := yRoot_spec
  have hp : 0 < 2 * yRoot - 1 := by linarith
  unfold alphaY betaY
  field_simp
  ring

/-- **(proved from `yRoot_spec`).**  `α³ − 22α² + 36α − 16 = 0`: after clearing `(2x − 1)³`
(`field_simp`) the identity is `−8` times the cubic. -/
theorem alphaY_cubic : alphaY ^ 3 - 22 * alphaY ^ 2 + 36 * alphaY - 16 = 0 := by
  have h := yRoot_spec
  have hp : 2 * yRoot - 1 ≠ 0 := by linarith
  unfold alphaY
  field_simp
  linear_combination (-8 : ℝ) * h.2.2

/-- **(proved from `yRoot_bounds`).**  `20 < α < 21` (`α = 1 + 1/(2x − 1)`, `yRoot_bounds`). -/
theorem alphaY_mem : 20 < alphaY ∧ alphaY < 21 := by
  have h := yRoot_bounds
  have hp : 0 < 2 * yRoot - 1 := by linarith
  unfold alphaY
  constructor
  · rw [lt_div_iff₀ hp]; linarith
  · rw [div_lt_iff₀ hp]; linarith

theorem one_lt_alphaY : 1 < alphaY := by
  linarith [alphaY_mem.1]

/-- **(drafted, 99%).**  `α` is irrational (`α = 1 + 1/(2x − 1)`, `irrational_yRoot`). -/
theorem irrational_alphaY : Irrational alphaY := by
  have hp : 2 * yRoot - 1 ≠ 0 := by linarith [yRoot_spec.1]
  have h : alphaY = 1 + (2 * yRoot - 1)⁻¹ := by
    unfold alphaY; field_simp; ring
  rw [h]
  have h2 : Irrational (2 * yRoot - 1) := by
    have := irrational_yRoot.ratCast_mul (q := 2) (by norm_num)
    simpa using this.sub_ratCast (q := 1)
  simpa using (h2.inv).ratCast_add (q := 1)

/-! ## The polygon computation on the phase square -/

/-- `Δ′(f₁, f₂) = g f₁ + 2x + x² − (1 + x) f₂` with `g = 1 − x − x²`: the third step is
`W³ = −2n + W − W² + Δ′ − f₃`. -/
noncomputable def yPhase3 (f₁ f₂ : ℝ) : ℝ :=
  (1 - yRoot - yRoot ^ 2) * f₁ + 2 * yRoot + yRoot ^ 2 - (1 + yRoot) * f₂

/-- `Δ_t(f₁, f₂) = 3x − x² + x t − g(1 + x) f₁ − (2 − x) f₂`: when `t = Δ′ − f₃`, the fourth step
is `W⁴ = 2n + W − 2W² + Δ_t − f₄`. -/
noncomputable def yPhase4 (t : ℤ) (f₁ f₂ : ℝ) : ℝ :=
  3 * yRoot - yRoot ^ 2 + yRoot * t - (1 - yRoot - yRoot ^ 2) * (1 + yRoot) * f₁ -
    (2 - yRoot) * f₂

theorem yG_pos : 0 < 1 - yRoot - yRoot ^ 2 := by
  have h := yRoot_bounds
  nlinarith

/-- **(drafted, 99%).**  On the closed box, `−1 < Δ′ < 2`.  Paper proof: `Δ′` is affine, its
extremes over `[0, 1]²` are at the corners: `Δ′(0, 1) = −g ≈ −0.197` and
`Δ′(1, 0) = 1 + x ≈ 1.526`; `nlinarith` with `yRoot_bounds`. -/
theorem yPhase3_mem {f₁ f₂ : ℝ} (h₁ : 0 ≤ f₁) (h₁' : f₁ ≤ 1) (h₂ : 0 ≤ f₂) (h₂' : f₂ ≤ 1) :
    -1 < yPhase3 f₁ f₂ ∧ yPhase3 f₁ f₂ < 2 := by
  have hg := yG_pos
  have hx := yRoot_bounds
  unfold yPhase3
  constructor
  · nlinarith [mul_nonneg hg.le h₁,
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + yRoot) (sub_nonneg.2 h₂')]
  · nlinarith [mul_nonneg hg.le (sub_nonneg.2 h₁'),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + yRoot) h₂]

/-- **(drafted, 98%; polygon `R_a`).**  If `Δ′ ≥ 1` on the closed box then `1 < Δ_1 < 2`.
Paper proof: the polygon `{Δ′ ≥ 1} ∩ [0, 1]²` has vertices `(0, 0), (1, 0), (1, x/(1 + x)),
(0, (2x + x² − 1)/(1 + x))` where `Δ_1 = 1.8272, 1.5260, 1.0179, 1.5098`.  Certificates: lower,
`Δ_1 − 1 = λ(Δ′ − 1) + μ(1 − f₁) + κ`, `λ = (2 − x)/(1 + x)`, `μ = g(λ + 1 + x)`,
`κ ≈ 0.0179 > 0`; upper, `2 − Δ_1 ≥ 2 − Δ_1(0, 0) = 2 − 4x + x² ≈ 0.173 > 0` since `Δ_1` is
decreasing in both phases. -/
theorem yPhase4_of_one {f₁ f₂ : ℝ} (h₁ : 0 ≤ f₁) (h₁' : f₁ ≤ 1) (h₂ : 0 ≤ f₂) (h₂' : f₂ ≤ 1)
    (h : 1 ≤ yPhase3 f₁ f₂) : 1 < yPhase4 1 f₁ f₂ ∧ yPhase4 1 f₁ f₂ < 2 := by
  have hg := yG_pos
  have hx := yRoot_bounds
  have key : (1 + yRoot) * (yPhase4 1 f₁ f₂ - 1) = (2 - yRoot) * (yPhase3 f₁ f₂ - 1) +
      (1 - yRoot - yRoot ^ 2) * (yRoot ^ 2 + yRoot + 3) * (1 - f₁) +
        yRoot * (2 * yRoot - 1) := by
    unfold yPhase3 yPhase4; push_cast; linear_combination (yRoot + 1) * yRoot_spec.2.2
  constructor
  · have hA : 0 ≤ (2 - yRoot) * (yPhase3 f₁ f₂ - 1) := mul_nonneg (by linarith) (by linarith)
    have hB : 0 ≤ (1 - yRoot - yRoot ^ 2) * (yRoot ^ 2 + yRoot + 3) * (1 - f₁) :=
      mul_nonneg (mul_nonneg hg.le (by nlinarith [sq_nonneg yRoot])) (by linarith)
    have hC : 0 < yRoot * (2 * yRoot - 1) := mul_pos (by linarith) (by linarith)
    by_contra hn
    nlinarith
  · unfold yPhase4; push_cast
    nlinarith [mul_nonneg (mul_nonneg hg.le (by linarith : (0 : ℝ) ≤ 1 + yRoot)) h₁,
      mul_nonneg (by linarith : (0 : ℝ) ≤ 2 - yRoot) h₂]

/-- **(drafted, 98%; polygon `R_b`).**  If `Δ′ ≤ 0`, `0 ≤ f₁ < 1` and `0 ≤ f₂ ≤ 1` then
`−1 < Δ_{−1} < 0`.  Paper proof: the polygon `{Δ′ ≤ 0} ∩ [0, 1]²` has vertices
`(0, (2x + x²)/(1 + x)), (0, 1), (1, 1)` where `Δ_{−1} = −0.5081, −0.6988, −1`.  Upper:
`Δ_{−1} − Δ_{−1}(0, (2x + x²)/(1 + x)) = −λ′(−Δ′) − μ′f₁` (nonpositive) with `λ′ = (2 − x)/(1 + x)`.
Lower: `Δ_{−1}` is strictly decreasing in `f₁` and `f₂`, `Δ_{−1}(1, 1) = −1` exactly (by the
cubic), and `f₁ < 1`, `f₂ ≤ 1` give `Δ_{−1}(f₁, f₂) ≥ Δ_{−1}(f₁, 1) > Δ_{−1}(1, 1) = −1`.
The bound is tight: with `f₁ = 1` allowed the lemma is false (`f = (1, 1, 1, 1)` gives
`t = −1`, `u = −2`, the tooth in `check.py`). -/
theorem yPhase4_of_neg_one {f₁ f₂ : ℝ} (h₁ : 0 ≤ f₁) (h₁' : f₁ < 1) (h₂ : 0 ≤ f₂)
    (h₂' : f₂ ≤ 1) (h : yPhase3 f₁ f₂ ≤ 0) : -1 < yPhase4 (-1) f₁ f₂ ∧ yPhase4 (-1) f₁ f₂ < 0 := by
  have hg := yG_pos
  have hx := yRoot_bounds
  constructor
  · have key : yPhase4 (-1) f₁ f₂ + 1 =
        (1 - yRoot - yRoot ^ 2) * (1 + yRoot) * (1 - f₁) + (2 - yRoot) * (1 - f₂) := by
      unfold yPhase4; push_cast; linear_combination yRoot_spec.2.2
    have hA : 0 < (1 - yRoot - yRoot ^ 2) * (1 + yRoot) * (1 - f₁) :=
      mul_pos (mul_pos hg (by linarith)) (by linarith)
    have hB : 0 ≤ (2 - yRoot) * (1 - f₂) := mul_nonneg (by linarith) (by linarith)
    linarith
  · have key : (1 + yRoot) * yPhase4 (-1) f₁ f₂ = (2 - yRoot) * yPhase3 f₁ f₂ -
        (1 - yRoot - yRoot ^ 2) * (yRoot ^ 2 + yRoot + 3) * f₁ + (yRoot ^ 2 - 2 * yRoot) := by
      unfold yPhase3 yPhase4; push_cast; ring
    have hA : (2 - yRoot) * yPhase3 f₁ f₂ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) h
    have hB : 0 ≤ (1 - yRoot - yRoot ^ 2) * (yRoot ^ 2 + yRoot + 3) * f₁ :=
      mul_nonneg (mul_nonneg hg.le (by nlinarith [sq_nonneg yRoot])) h₁
    by_contra hn
    nlinarith

/-- **(proved from `yRoot_spec`).**  Substituting `f₃ = Δ′ − t`:
`2 − g f₁ − (2 + x²) f₂ − x(Δ′ − t) = Δ_t`.  Paper proof: `ring_nf` and `x³ = 2 − 3x − x²`
(`2 − 2x² − x³ = 3x − x²`); `linear_combination (-1) * yRoot_spec.2.2`. -/
theorem yPhase4_sub (t : ℤ) (f₁ f₂ : ℝ) :
    2 - (1 - yRoot - yRoot ^ 2) * f₁ - (2 + yRoot ^ 2) * f₂ - yRoot * (yPhase3 f₁ f₂ - t) =
      yPhase4 t f₁ f₂ := by
  unfold yPhase3 yPhase4
  linear_combination (-1 : ℝ) * yRoot_spec.2.2

/-! ## The phases of a run -/

/-- The floor-step phase `f₁ = (n/2)·α − W(n)` (`= {kα}` for `n = 2k`). -/
noncomputable def yF1 (n : ℤ) : ℝ :=
  ((n / 2 : ℤ) : ℝ) * alphaY - wy alphaY n

/-- The odd-step defect `f(v) = x(v + 1) − W(v)` (in `(0, 1]` for odd `v`). -/
noncomputable def yFodd (v : ℤ) : ℝ :=
  yRoot * ((v : ℝ) + 1) - wy alphaY v

/-- **(drafted, 99%).**  For even `n`, `0 ≤ f₁ < 1` (`wy_two_mul`, `Int.fract_nonneg`,
`Int.fract_lt_one`). -/
theorem yF1_mem {n : ℤ} (hn : n % 2 = 0) : 0 ≤ yF1 n ∧ yF1 n < 1 := by
  have h : n = 2 * (n / 2) := by omega
  have hw : wy alphaY n = ⌊((n / 2 : ℤ) : ℝ) * alphaY⌋ := by
    conv_lhs => rw [h]
    exact wy_two_mul _ _
  unfold yF1
  rw [hw]
  constructor
  · linarith [Int.floor_le (((n / 2 : ℤ) : ℝ) * alphaY)]
  · linarith [Int.lt_floor_add_one (((n / 2 : ℤ) : ℝ) * alphaY)]

/-- **(drafted, 99%).**  For odd `v`, `0 < f(v) ≤ 1`.  Paper proof: `v = 2j − 1`,
`W(v) = ⌈jβ⌉ − 1` (`wy_two_mul_sub_one`, `alphaY_div_sub_one`) and `jβ = 2jx = x(v + 1)`;
`⌈y⌉ − 1 ∈ [y − 1, y)` (`Int.ceil_lt_add_one`, `Int.le_ceil`). -/
theorem yFodd_mem {v : ℤ} (hv : v % 2 = 1) : 0 < yFodd v ∧ yFodd v ≤ 1 := by
  have h : v = 2 * ((v + 1) / 2) - 1 := by omega
  have hw : wy alphaY v = ⌈(((v + 1) / 2 : ℤ) : ℝ) * (alphaY / (alphaY - 1))⌉ - 1 := by
    conv_lhs => rw [h]
    exact wy_two_mul_sub_one _ _
  have hy : (((v + 1) / 2 : ℤ) : ℝ) * (alphaY / (alphaY - 1)) = yRoot * ((v : ℝ) + 1) := by
    rw [alphaY_div_sub_one, betaY]
    have : ((v + 1 : ℤ) : ℝ) = 2 * (((v + 1) / 2 : ℤ) : ℝ) := by
      exact_mod_cast (by omega : v + 1 = 2 * ((v + 1) / 2))
    push_cast at this
    rw [this]; ring
  unfold yFodd
  rw [hw, hy]
  push_cast
  constructor
  · linarith [Int.ceil_lt_add_one (yRoot * ((v : ℝ) + 1))]
  · linarith [Int.le_ceil (yRoot * ((v : ℝ) + 1))]

/-- `g α = 4` (the cubic, after clearing `2x − 1`). -/
theorem g_mul_alphaY : (1 - yRoot - yRoot ^ 2) * alphaY = 4 := by
  have h := yRoot_spec
  have hp : 2 * yRoot - 1 ≠ 0 := by linarith
  unfold alphaY
  rw [← mul_div_assoc, div_eq_iff hp]
  linear_combination (-2 : ℝ) * h.2.2

theorem wy_iterate_two (n : ℤ) : (wy alphaY)^[2] n = wy alphaY (wy alphaY n) := by
  rw [Function.iterate_succ_apply', Function.iterate_one]

theorem wy_iterate_succ (i : ℕ) (n : ℤ) :
    (wy alphaY)^[i + 1] n = wy alphaY ((wy alphaY)^[i] n) :=
  Function.iterate_succ_apply' _ _ _

/-- **(drafted, 99%; algebra, any parities).**  For even `n`:
`W³ = −2n + W − W² + Δ′(f₁, f(W n)) − f(W² n)`.  Paper proof: unfold `yF1`, `yFodd`,
`yPhase3`; with `kα = n·x/(2x − 1)` everything cancels to `n·(g x/(2x − 1) − 2) = 0`, which is
the cubic (`field_simp`, `linear_combination`). -/
theorem wy_iterate_three_phase {n : ℤ} (hn : n % 2 = 0) :
    (((wy alphaY)^[3] n : ℤ) : ℝ) =
      -2 * n + wy alphaY n - (wy alphaY)^[2] n +
        yPhase3 (yF1 n) (yFodd (wy alphaY n)) - yFodd ((wy alphaY)^[2] n) := by
  have hn' : (n : ℝ) = 2 * ((n / 2 : ℤ) : ℝ) := by exact_mod_cast (by omega : n = 2 * (n / 2))
  unfold yF1 yFodd yPhase3
  rw [hn', wy_iterate_succ 2, wy_iterate_two]
  linear_combination (-((n / 2 : ℤ) : ℝ)) * g_mul_alphaY

/-- **(drafted, 99%; algebra, any parities).**  For even `n`:
`W⁴ = 2n + W − 2W² + 2 − g f₁ − (2 + x²) f₂ − x f₃ − f₄` with `f₂, f₃, f₄` the defects at
`W n, W² n, W³ n`.  Paper proof: as `wy_iterate_three_phase`, using `c_3 = 2 + c_0 − 2c_1`
(i.e. `A x³ = 2 + A − 2Ax`, the cubic) and `x³ + x² + 3x = 2`. -/
theorem wy_iterate_four_phase {n : ℤ} (hn : n % 2 = 0) :
    (((wy alphaY)^[4] n : ℤ) : ℝ) =
      2 * n + wy alphaY n - 2 * (wy alphaY)^[2] n + 2 -
        (1 - yRoot - yRoot ^ 2) * yF1 n - (2 + yRoot ^ 2) * yFodd (wy alphaY n) -
        yRoot * yFodd ((wy alphaY)^[2] n) - yFodd ((wy alphaY)^[3] n) := by
  have hn' : (n : ℝ) = 2 * ((n / 2 : ℤ) : ℝ) := by exact_mod_cast (by omega : n = 2 * (n / 2))
  unfold yF1 yFodd
  rw [hn', wy_iterate_succ 3, wy_iterate_succ 2, wy_iterate_two]
  linear_combination (((n / 2 : ℤ) : ℝ)) * g_mul_alphaY +
    (1 + (wy alphaY n : ℝ)) * yRoot_spec.2.2

/-! ## Theorem Y (1): the recurrence on `E O³` -/

/-- **(drafted, 98%).**  On `E O O`, `W³(n) − (−2n + W(n) − W²(n)) ∈ {−1, 0, 1}`, for every
`n ∈ ℤ`.  Paper proof: it is the integer `Δ′ − f₃` (`wy_iterate_three_phase`), and
`Δ′ ∈ (−1, 2)` (`yPhase3_mem`, `yF1_mem`, `yFodd_mem`), `f₃ ∈ (0, 1]`. -/
theorem wy_iterate_three_sub_mem {n : ℤ} (hn : n % 2 = 0) (h₁ : wy alphaY n % 2 = 1)
    (h₂ : (wy alphaY)^[2] n % 2 = 1) :
    (wy alphaY)^[3] n - (-2 * n + wy alphaY n - (wy alphaY)^[2] n) ∈ ({-1, 0, 1} : Set ℤ) := by
  have hph := wy_iterate_three_phase hn
  obtain ⟨a1, a2⟩ := yF1_mem hn
  obtain ⟨b1, b2⟩ := yFodd_mem h₁
  obtain ⟨c1, c2⟩ := yFodd_mem h₂
  obtain ⟨d1, d2⟩ := yPhase3_mem a1 a2.le b1.le b2
  have hlo : ((-2 : ℤ) : ℝ) <
      (((wy alphaY)^[3] n - (-2 * n + wy alphaY n - (wy alphaY)^[2] n) : ℤ) : ℝ) := by
    push_cast; linarith
  have hhi : (((wy alphaY)^[3] n - (-2 * n + wy alphaY n - (wy alphaY)^[2] n) : ℤ) : ℝ) <
      ((2 : ℤ) : ℝ) := by
    push_cast; linarith
  have hlo' := Int.cast_lt.1 hlo
  have hhi' := Int.cast_lt.1 hhi
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-- **(drafted, 95%; Theorem Y (1)).**  If `n` is even and `W(n), W²(n), W³(n)` are odd, then
`W⁴(n) = 4n + W³(n) − W²(n)`; for every `n ∈ ℤ`.  Paper proof: module docstring (`t = ±1` by
parity and `wy_iterate_three_sub_mem`; `u = Δ_t − f₄` by `wy_iterate_four_phase` and
`yPhase4_sub`; `u = t` by `yPhase4_of_one` / `yPhase4_of_neg_one` and `f₄ ∈ (0, 1]`). -/
theorem wy_iterate_four_eq {n : ℤ} (hn : n % 2 = 0)
    (hodd : ∀ i : ℕ, 1 ≤ i → i ≤ 3 → (wy alphaY)^[i] n % 2 = 1) :
    (wy alphaY)^[4] n = 4 * n + (wy alphaY)^[3] n - (wy alphaY)^[2] n := by
  have o1 := hodd 1 le_rfl (by norm_num)
  have o2 := hodd 2 (by norm_num) (by norm_num)
  have o3 := hodd 3 (by norm_num) le_rfl
  rw [Function.iterate_one] at o1
  have ht := wy_iterate_three_sub_mem hn o1 o2
  have hph3 := wy_iterate_three_phase hn
  have hph4 := wy_iterate_four_phase hn
  obtain ⟨a1, a2⟩ := yF1_mem hn
  obtain ⟨b1, b2⟩ := yFodd_mem o1
  obtain ⟨c1, c2⟩ := yFodd_mem o2
  obtain ⟨e1, e2⟩ := yFodd_mem o3
  set t : ℤ := (wy alphaY)^[3] n - (-2 * n + wy alphaY n - (wy alphaY)^[2] n) with ht_def
  have hf3 : yFodd ((wy alphaY)^[2] n) = yPhase3 (yF1 n) (yFodd (wy alphaY n)) - t := by
    rw [ht_def]; push_cast; linarith
  have hu : ((((wy alphaY)^[4] n - (2 * n + wy alphaY n - 2 * (wy alphaY)^[2] n)) : ℤ) : ℝ) =
      yPhase4 t (yF1 n) (yFodd (wy alphaY n)) - yFodd ((wy alphaY)^[3] n) := by
    rw [← yPhase4_sub, ← hf3]; push_cast; linarith
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
  rcases ht with h | h | h
  · -- `t = −1`
    rw [h] at hf3 hu
    obtain ⟨p1, p2⟩ := yPhase4_of_neg_one a1 a2 b1.le b2 (by push_cast at hf3; linarith)
    have hlo : ((-2 : ℤ) : ℝ) <
        ((((wy alphaY)^[4] n - (2 * n + wy alphaY n - 2 * (wy alphaY)^[2] n)) : ℤ) : ℝ) := by
      rw [hu]; push_cast; linarith
    have hhi : ((((wy alphaY)^[4] n - (2 * n + wy alphaY n - 2 * (wy alphaY)^[2] n)) : ℤ) : ℝ) <
        ((0 : ℤ) : ℝ) := by
      rw [hu]; push_cast; linarith
    have := Int.cast_lt.1 hlo
    have := Int.cast_lt.1 hhi
    omega
  · omega
  · -- `t = 1`
    rw [h] at hf3 hu
    obtain ⟨p1, p2⟩ := yPhase4_of_one a1 a2.le b1.le b2 (by push_cast at hf3; linarith)
    have hlo : ((0 : ℤ) : ℝ) <
        ((((wy alphaY)^[4] n - (2 * n + wy alphaY n - 2 * (wy alphaY)^[2] n)) : ℤ) : ℝ) := by
      rw [hu]; push_cast; linarith
    have hhi : ((((wy alphaY)^[4] n - (2 * n + wy alphaY n - 2 * (wy alphaY)^[2] n)) : ℤ) : ℝ) <
        ((2 : ℤ) : ℝ) := by
      rw [hu]; push_cast; linarith
    have := Int.cast_lt.1 hlo
    have := Int.cast_lt.1 hhi
    omega

/-- **(drafted, 95%; Theorem Y (1), runs).**  After an even point at most three odd points
follow: some `W^{j+1}(n)`, `j ≤ 3`, is even.  Paper proof: `wy_iterate_four_eq`
(`4n + W³ − W²` is even when `W², W³` are odd). -/
theorem exists_even_iterate_Y {n : ℤ} (hn : n % 2 = 0) :
    ∃ j ≤ 3, (wy alphaY)^[j + 1] n % 2 = 0 := by
  by_contra hne
  push Not at hne
  have hodd : ∀ i : ℕ, 1 ≤ i → i ≤ 3 → (wy alphaY)^[i] n % 2 = 1 := by
    intro i hi1 hi3
    have := hne (i - 1) (by omega)
    rw [show i - 1 + 1 = i by omega] at this
    omega
  have h4 := wy_iterate_four_eq hn hodd
  have h2 := hodd 2 (by norm_num) (by norm_num)
  have h3 := hodd 3 (by norm_num) le_rfl
  have h5 : (wy alphaY)^[4] n % 2 ≠ 0 := hne 3 le_rfl
  omega

theorem alphaY_bounds : 2026 / 100 < alphaY ∧ alphaY < 203 / 10 := by
  have h := yRoot_bounds
  have hp : 0 < 2 * yRoot - 1 := by linarith
  unfold alphaY
  constructor
  · rw [lt_div_iff₀ hp]; linarith
  · rw [div_lt_iff₀ hp]; linarith

/-- Floor step of the sandwich: `(n/2)·α < W(n) + 1` for even `n`. -/
theorem wy_even_add_one_gt {n : ℤ} (hn : n % 2 = 0) :
    ((n / 2 : ℤ) : ℝ) * alphaY < wy alphaY n + 1 := by
  have := (yF1_mem hn).2; unfold yF1 at this; linarith

/-- Odd step of the sandwich: `x(v + 1) ≤ W(v) + 1` for odd `v`. -/
theorem wy_odd_add_one_ge {v : ℤ} (hv : v % 2 = 1) :
    yRoot * ((v : ℝ) + 1) ≤ wy alphaY v + 1 := by
  have := (yFodd_mem hv).2; unfold yFodd at this; linarith

/-- **(drafted, 97%; the (H2) input).**  For `n > 0` even, `j ≤ 3`, and `W(n), …, Wʲ(n)` odd:
`4n ≤ 3·W^{j+1}(n)`.  Paper proof: the sandwich of `WythoffLine` (`y₁ = An`,
`y_{i+1} = x(Wⁱ n + 1)`, `x yᵢ ≤ y_{i+1}`, strict at `i = 1`) gives `W^{j+1}(n) > c_j n − 1` with
`c_j = A xʲ ≥ c_3 = A x³ > 1.47` (`yRoot_bounds`), and `1.47n − 1 ≥ 4n/3` for `n ≥ 8`; for
`n ∈ {2, 4, 6}`, `W(n) = 20, 40, 60` (`alphaY_mem`, `α < 20.3`) is even, so only `j = 0` occurs
and `W(n) = ⌊nα/2⌋ ≥ 10n`.  (Measured: `min R(s)/s = 1.4722` at `s = 72`; slope `3/2` fails.) -/
theorem le_wy_iterate_of_odd_run_Y {n : ℤ} (hn0 : 0 < n) (hn : n % 2 = 0) {j : ℕ} (hj : j ≤ 3)
    (hodd : ∀ i : ℕ, 1 ≤ i → i ≤ j → (wy alphaY)^[i] n % 2 = 1) :
    4 * n ≤ 3 * (wy alphaY)^[j + 1] n := by
  have hx := yRoot_bounds
  have hα := alphaY_bounds
  have hnk : n = 2 * (n / 2) := by omega
  have hk1 : (1 : ℝ) ≤ ((n / 2 : ℤ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n / 2)
  have hn' : (n : ℝ) = 2 * ((n / 2 : ℤ) : ℝ) := by exact_mod_cast hnk
  have hchain : ∀ i : ℕ, i ≤ j → yRoot ^ i * (((n / 2 : ℤ) : ℝ) * alphaY) <
      ((wy alphaY)^[i + 1] n : ℝ) + 1 := by
    intro i
    induction i with
    | zero => intro _; simpa using wy_even_add_one_gt hn
    | succ i ih =>
      intro hi
      have h1 := ih (by omega)
      have h2 := wy_odd_add_one_ge (hodd (i + 1) (by omega) hi)
      rw [wy_iterate_succ (i + 1)]
      calc yRoot ^ (i + 1) * (((n / 2 : ℤ) : ℝ) * alphaY)
          = yRoot * (yRoot ^ i * (((n / 2 : ℤ) : ℝ) * alphaY)) := by ring
        _ < yRoot * (((wy alphaY)^[i + 1] n : ℝ) + 1) :=
          mul_lt_mul_of_pos_left h1 (by linarith)
        _ ≤ _ := h2
  have hfin := hchain j le_rfl
  suffices key : ((4 * n : ℤ) : ℝ) < ((3 * (wy alphaY)^[j + 1] n : ℤ) : ℝ) from
    (Int.cast_lt.1 key).le
  push_cast
  rcases Nat.eq_zero_or_pos j with hj0 | hj0
  · subst hj0
    simp only [pow_zero, one_mul] at hfin
    nlinarith
  · rcases le_or_gt (n / 2) 3 with hk3 | hk4
    · -- `n ∈ {2, 4, 6}`: `W(n) = 20·(n/2)` is even, so no odd run follows
      exfalso
      have h1 := hodd 1 le_rfl hj0
      rw [Function.iterate_one, hnk, wy_two_mul] at h1
      have hk3' : ((n / 2 : ℤ) : ℝ) ≤ 3 := by exact_mod_cast hk3
      have hfl : ⌊((n / 2 : ℤ) : ℝ) * alphaY⌋ = 20 * (n / 2) := by
        rw [Int.floor_eq_iff]; push_cast; constructor <;> nlinarith
      rw [hfl] at h1
      omega
    · have hk4' : (4 : ℝ) ≤ ((n / 2 : ℤ) : ℝ) := by exact_mod_cast hk4
      have hx3 : (1454 : ℝ) / 10000 < yRoot ^ 3 := by
        have : ((52595748 : ℝ) / 10 ^ 8) ^ 3 < yRoot ^ 3 :=
          pow_lt_pow_left₀ hx.1 (by norm_num) (by norm_num)
        norm_num at this ⊢; linarith
      have hxj : yRoot ^ 3 ≤ yRoot ^ j :=
        pow_le_pow_of_le_one (by linarith) (by linarith) (by omega)
      have hprod : (1454 : ℝ) / 10000 * 2026 / 100 * ((n / 2 : ℤ) : ℝ) ≤
          yRoot ^ j * (((n / 2 : ℤ) : ℝ) * alphaY) := by
        have := mul_le_mul (hx3.le.trans hxj) (mul_le_mul_of_nonneg_left hα.1.le
          (by linarith : (0 : ℝ) ≤ ((n / 2 : ℤ) : ℝ))) (by nlinarith)
          (pow_nonneg (by linarith) _)
        linarith
      nlinarith

/-! ## Theorem Y (2)-(4): classification, count, density -/

/-- `W_α` for Theorem Y, as a permutation of `ℤ`. -/
noncomputable def yPerm : Equiv.Perm ℤ :=
  wyPerm alphaY one_lt_alphaY

theorem yPerm_apply (n : ℤ) : yPerm n = wy alphaY n := rfl

/-- **(drafted, 96%; Theorem Y (2)).**  Lemma P applies with `S` = evens, `Φ = {1}`, `T = 4`.
Paper proof: `pos_iff` is `wy_pos_iff`; `W(1) = 1` (`wy_one`, `α ≥ 2`) and injectivity give
`mem_fix_iff`; (H1) is `wy_lt_of_odd` (`α ≥ 3`); (H2): by `exists_even_iterate_Y` the first
return word is `E Oʲ`, `j ≤ 3` (take the least such `j`, `Nat.find`), and
`R(s) ≥ 4s/3 > s` by `le_wy_iterate_of_odd_run_Y`. -/
theorem hyp_yPerm : Hyp yPerm {n | n % 2 = 0} {1} 4 := by
  sorry

/-- **(drafted, 96%).**  The first return to the evens at least multiplies by `4/3`. -/
theorem returnMap_yPerm_ge {s : ℤ} (hs0 : 0 < s) (hs : s % 2 = 0) :
    4 * s ≤ 3 * returnMap yPerm {n | n % 2 = 0} s := by
  sorry

/-- **(drafted, 96%; Theorem Y (2)).**  `{1}` is the only finite orbit in `ℕ⁺`
(`permOrbit_finite_iff` with `hyp_yPerm`). -/
theorem permOrbit_yPerm_finite_iff {x : ℤ} (hx : 0 < x) :
    (permOrbit yPerm x).Finite ↔ x = 1 := by
  sorry

/-- **(drafted, 96%; Theorem Y (2), forward escape).** -/
theorem tendsto_yPerm_pow {x : ℤ} (hx : 1 < x) :
    Tendsto (fun n : ℕ => (yPerm ^ n) x) atTop atTop := by
  sorry

/-- **(drafted, 96%; Theorem Y (2), backward escape).** -/
theorem tendsto_yPerm_pow_neg {x : ℤ} (hx : 1 < x) :
    Tendsto (fun n : ℕ => (yPerm ^ (-(n : ℤ))) x) atTop atTop := by
  sorry

/-- **(drafted, 96%; Theorem Y (2), minima).**  For `x > 1`: `x` is the minimum of its orbit iff
`x` is even and its four predecessors are odd (`isOrbitMin_iff`, `T = 4`).  (Three predecessors
do not suffice: 582 mismatches with brute force for `y ≤ 2·10⁴`.) -/
theorem isOrbitMin_yPerm_iff {x : ℤ} (hx : 1 < x) :
    IsOrbitMin yPerm x ↔
      x % 2 = 0 ∧ ∀ i : ℕ, 1 ≤ i → i ≤ 4 → (yPerm ^ (-(i : ℤ))) x % 2 = 1 := by
  sorry

/-- **(drafted, 96%; Theorem Y (3), exact count).**
`#{minima ≤ X} + #{even s ∈ [1, X] : R(s) ≤ X} = 1 + ⌊X/2⌋`.  Paper proof:
`minCount_add_returnCount` with `Φ = {1}` and `#(evens ∩ [1, X]) = ⌊X/2⌋`, as
`WythoffLine.minCount_gPerm_add`. -/
theorem minCount_yPerm_add {X : ℕ} (hX : 1 ≤ X) :
    minCount yPerm X + returnCount yPerm {n | n % 2 = 0} {1} X = 1 + X / 2 := by
  sorry

/-- **(drafted, 96%; Theorem Y (3), unconditional lower bound).**
`#{minima ≤ X} ≥ 1 + ⌊X/2⌋ − ⌊3X/8⌋`.  Paper proof: `R(s) ≤ X` forces `4s ≤ 3X`
(`returnMap_yPerm_ge`), and there are `⌊3X/8⌋` even `s ≥ 1` with `4s ≤ 3X`. -/
theorem minCount_yPerm_ge {X : ℕ} (hX : 1 ≤ X) :
    1 + (X : ℤ) / 2 - 3 * (X : ℤ) / 8 ≤ minCount yPerm X := by
  sorry

/-- **(drafted, 96%; Theorem Y (2)).**  Infinitely many infinite orbits.  Paper proof:
`minCount_yPerm_ge` is unbounded, so the minima `> 1` are infinite;
`infinitelyManyInfiniteOrbits_of_minima`. -/
theorem yPerm_infinitelyManyInfiniteOrbits : InfinitelyManyInfiniteOrbits yPerm := by
  sorry

/-- The minima density `d = 3/10 + x/8 + x²/10 ≈ 0.3934078`. -/
noncomputable def densityY : ℝ :=
  3 / 10 + yRoot / 8 + yRoot ^ 2 / 10

/-- **(proved from `yRoot_spec`).**  `d` is a root of `1280t³ − 352t² − 52t − 3` (reduce `x³, …, x⁶`
with the cubic). -/
theorem densityY_minpoly : 1280 * densityY ^ 3 - 352 * densityY ^ 2 - 52 * densityY - 3 = 0 := by
  unfold densityY
  have h3 : yRoot ^ 3 = 2 - 3 * yRoot - yRoot ^ 2 := by linarith [yRoot_spec.2.2]
  have h4 : yRoot ^ 4 = yRoot * (2 - 3 * yRoot - yRoot ^ 2) := by rw [← h3]; ring
  have h5 : yRoot ^ 5 = yRoot ^ 2 * (2 - 3 * yRoot - yRoot ^ 2) := by rw [← h3]; ring
  have h6 : yRoot ^ 6 = (2 - 3 * yRoot - yRoot ^ 2) ^ 2 := by rw [← h3]; ring
  nlinarith [h3, h4, h5, h6]

/-- **(drafted, 90%; Theorem Y (4), density, conditional).**  Assuming multidimensional Weyl
equidistribution (a literature hypothesis), the orbit minima have density
`d = 3/10 + x/8 + x²/10 ≈ 0.3934078`.  Paper proof (research note §4 (b3), proof of 2-4): by
`minCount_yPerm_add`, `d = 1/2 − (1/2) Σ_{j ≤ 3} P_j / c_j`, where `P_j` is the density among the
evens of the return word `E Oʲ` and `R(s) = c_j s + O(1)` on word `j` (the sandwich).  With
`n = 2k`, the parities along the run are functions of the two phases `({k c_0}, {k c_1})`
(`c_2 = −2 + c_0 − c_1` is an integer combination, so the third phase is determined, and the
fourth step is forced by the recurrence); in the coordinates `(f₁, f₂)` of the module docstring
the `E O O` cylinder carries uniform `(f₁, f₂) ∈ [0, 1)²`, and its `E O³` part is
`R_a ∪ R_b`, of area `(1 − x³)/(2(1 + x)) + g/(2(1 + x)) = x/(1 + x)`.  `WeylEquidistributionMulti`
with `θ = (c_0, c_1)`, independent by `linearIndependent_yRoot` (times `2x − 1`:
`2x − 1, x, x²`), applied to these polygons (Lebesgue-null frontier), gives
`P = (1/2, 1/4, 1/(4(1 + x)), x/(4(1 + x)))`, and the sum reduces in `ℚ(x)` to `d`.  (Census:
786 812 minima `≤ 2·10⁶` including `1`, against `dX = 786 815.6`.) -/
theorem tendsto_minCount_yPerm (hW : WeylEquidistributionMulti) :
    Tendsto (fun X : ℕ => (minCount yPerm X : ℝ) / X) atTop
      (𝓝 densityY) := by
  sorry

end CollatzMoonshot.WythoffSporadic
