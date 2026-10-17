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

theorem yPerm_pow_apply (i : ℕ) (s : ℤ) : (yPerm ^ i) s = (wy alphaY)^[i] s := by
  rw [Equiv.Perm.coe_pow]; rfl

theorem yPerm_one : yPerm 1 = 1 := wy_one (by linarith [alphaY_mem.1])

theorem yPerm_fix : ∀ z ∈ ({1} : Set ℤ), yPerm z = z := by
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst hz
  exact yPerm_one

/-- `#(evens ∩ [1, M]) = ⌊M/2⌋`. -/
theorem card_filter_even_Icc (M : ℕ) :
    ((Finset.Icc (1 : ℤ) M).filter fun x => x % 2 = 0).card = M / 2 := by
  have : ((Finset.Icc (1 : ℤ) M).filter fun x => x % 2 = 0) =
      (Finset.Icc (1 : ℤ) ((M : ℤ) / 2)).image fun k => 2 * k := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨x / 2, ⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨k, ⟨h1, h2⟩, rfl⟩; omega
  rw [this, Finset.card_image_of_injective _ (fun a b h => by
    have : 2 * a = 2 * b := h; omega),
    Int.card_Icc]
  omega

/-- **(drafted, 96%; Theorem Y (2)).**  Lemma P applies with `S` = evens, `Φ = {1}`, `T = 4`.
Paper proof: `pos_iff` is `wy_pos_iff`; `W(1) = 1` (`wy_one`, `α ≥ 2`) and injectivity give
`mem_fix_iff`; (H1) is `wy_lt_of_odd` (`α ≥ 3`); (H2): by `exists_even_iterate_Y` the first
return word is `E Oʲ`, `j ≤ 3` (take the least such `j`, `Nat.find`), and
`R(s) ≥ 4s/3 > s` by `le_wy_iterate_of_odd_run_Y`. -/
theorem hyp_yPerm : Hyp yPerm {n | n % 2 = 0} {1} 4 := by
  have hα := alphaY_mem
  refine ⟨fun n => wy_pos_iff one_lt_alphaY n, ?_, ?_, ?_⟩
  · intro z
    simp only [Set.mem_singleton_iff]
    constructor
    · intro h; rw [← yPerm_one] at h; exact yPerm.injective h
    · rintro rfl; exact yPerm_one
  · intro z hz hS hΦ
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff] at hS hΦ
    rw [yPerm_apply]
    exact wy_lt_of_odd (by linarith) (by omega) (by omega)
  · intro s hs hs0 hsΦ
    simp only [Set.mem_ofPred_eq] at hs
    have hex := exists_even_iterate_Y hs
    classical
    have hj : Nat.find hex ≤ 3 ∧ (wy alphaY)^[Nat.find hex + 1] s % 2 = 0 := Nat.find_spec hex
    have hodd : ∀ i : ℕ, 1 ≤ i → i ≤ Nat.find hex → (wy alphaY)^[i] s % 2 = 1 := by
      intro i hi1 hij
      have := Nat.find_min hex (show i - 1 < Nat.find hex by omega)
      rw [show i - 1 + 1 = i by omega] at this
      omega
    have hrun := le_wy_iterate_of_odd_run_Y hs0 hs hj.1 hodd
    refine ⟨Nat.find hex + 1, by omega, by omega, ?_, ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq, yPerm_pow_apply]; exact hj.2
    · rw [yPerm_pow_apply]; omega
    · intro i hi1 hi2
      simp only [Set.mem_ofPred_eq, yPerm_pow_apply]
      have := hodd i hi1 (by omega); omega

/-- **(drafted, 96%).**  The first return to the evens at least multiplies by `4/3`. -/
theorem returnMap_yPerm_ge {s : ℤ} (hs0 : 0 < s) (hs : s % 2 = 0) :
    4 * s ≤ 3 * returnMap yPerm {n | n % 2 = 0} s := by
  have hΦ : s ∉ ({1} : Set ℤ) := by simp only [Set.mem_singleton_iff]; omega
  obtain ⟨h1, h2, -, -, h5⟩ :=
    returnTime_spec hyp_yPerm (show s ∈ {n : ℤ | n % 2 = 0} from hs) hs0 hΦ
  unfold returnMap
  rw [yPerm_pow_apply]
  obtain ⟨j, hj⟩ : ∃ j, returnTime yPerm {n | n % 2 = 0} s = j + 1 := 
    ⟨returnTime yPerm {n | n % 2 = 0} s - 1, by omega⟩
  rw [hj] at h2 h5 ⊢
  apply le_wy_iterate_of_odd_run_Y hs0 hs (by omega)
  intro i hi1 hij
  have := h5 i hi1 (by omega)
  simp only [Set.mem_ofPred_eq, yPerm_pow_apply] at this
  omega

/-- **(drafted, 96%; Theorem Y (2)).**  `{1}` is the only finite orbit in `ℕ⁺`
(`permOrbit_finite_iff` with `hyp_yPerm`). -/
theorem permOrbit_yPerm_finite_iff {x : ℤ} (hx : 0 < x) :
    (permOrbit yPerm x).Finite ↔ x = 1 := by
  rw [permOrbit_finite_iff hyp_yPerm yPerm_fix hx, Set.mem_singleton_iff]

/-- **(drafted, 96%; Theorem Y (2), forward escape).** -/
theorem tendsto_yPerm_pow {x : ℤ} (hx : 1 < x) :
    Tendsto (fun n : ℕ => (yPerm ^ n) x) atTop atTop :=
  tendsto_pow hyp_yPerm (by omega) (by simp only [Set.mem_singleton_iff]; omega)

/-- **(drafted, 96%; Theorem Y (2), backward escape).** -/
theorem tendsto_yPerm_pow_neg {x : ℤ} (hx : 1 < x) :
    Tendsto (fun n : ℕ => (yPerm ^ (-(n : ℤ))) x) atTop atTop :=
  tendsto_pow_neg hyp_yPerm (by omega) (by simp only [Set.mem_singleton_iff]; omega)

/-- **(drafted, 96%; Theorem Y (2), minima).**  For `x > 1`: `x` is the minimum of its orbit iff
`x` is even and its four predecessors are odd (`isOrbitMin_iff`, `T = 4`).  (Three predecessors
do not suffice: 582 mismatches with brute force for `y ≤ 2·10⁴`.) -/
theorem isOrbitMin_yPerm_iff {x : ℤ} (hx : 1 < x) :
    IsOrbitMin yPerm x ↔
      x % 2 = 0 ∧ ∀ i : ℕ, 1 ≤ i → i ≤ 4 → (yPerm ^ (-(i : ℤ))) x % 2 = 1 := by
  rw [isOrbitMin_iff hyp_yPerm (by omega) (by simp only [Set.mem_singleton_iff]; omega)]
  simp only [Set.mem_ofPred_eq]
  refine and_congr Iff.rfl (forall_congr' fun i => imp_congr_right fun _ =>
    imp_congr_right fun _ => ?_)
  constructor <;> intro h <;> omega

/-- **(drafted, 96%; Theorem Y (3), exact count).**
`#{minima ≤ X} + #{even s ∈ [1, X] : R(s) ≤ X} = 1 + ⌊X/2⌋`.  Paper proof:
`minCount_add_returnCount` with `Φ = {1}` and `#(evens ∩ [1, X]) = ⌊X/2⌋`, as
`WythoffLine.minCount_gPerm_add`. -/
theorem minCount_yPerm_add {X : ℕ} (hX : 1 ≤ X) :
    minCount yPerm X + returnCount yPerm {n | n % 2 = 0} {1} X = 1 + X / 2 := by
  rw [minCount_add_returnCount hyp_yPerm yPerm_fix X]
  congr 1
  · unfold setCount
    rw [Finset.card_eq_one]
    refine ⟨1, ?_⟩
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, Set.mem_singleton_iff, Finset.mem_singleton]
    omega
  · unfold setCount
    rw [← card_filter_even_Icc X]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, Set.mem_sdiff, Set.mem_ofPred_eq,
      Set.mem_singleton_iff]
    omega

/-- **(drafted, 96%; Theorem Y (3), unconditional lower bound).**
`#{minima ≤ X} ≥ 1 + ⌊X/2⌋ − ⌊3X/8⌋`.  Paper proof: `R(s) ≤ X` forces `4s ≤ 3X`
(`returnMap_yPerm_ge`), and there are `⌊3X/8⌋` even `s ≥ 1` with `4s ≤ 3X`. -/
theorem minCount_yPerm_ge {X : ℕ} (hX : 1 ≤ X) :
    1 + (X : ℤ) / 2 - 3 * (X : ℤ) / 8 ≤ minCount yPerm X := by
  have hadd := minCount_yPerm_add hX
  have hle : returnCount yPerm {n | n % 2 = 0} {1} X ≤ 3 * X / 8 := by
    unfold returnCount
    calc _ ≤ ((Finset.Icc (1 : ℤ) ((3 * X / 8 : ℕ) : ℤ)).image fun k => 2 * k).card := by
          apply Finset.card_le_card
          intro s hs
          simp only [Finset.mem_filter, Finset.mem_Icc, Set.mem_ofPred_eq,
            Set.mem_singleton_iff] at hs
          obtain ⟨⟨h1, h2⟩, h3, h4, h5⟩ := hs
          have := returnMap_yPerm_ge (by omega) h3
          simp only [Finset.mem_image, Finset.mem_Icc]
          exact ⟨s / 2, ⟨by omega, by omega⟩, by omega⟩
      _ ≤ _ := Finset.card_image_le.trans (by rw [Int.card_Icc]; omega)
  omega

/-- **(drafted, 96%; Theorem Y (2)).**  Infinitely many infinite orbits.  Paper proof:
`minCount_yPerm_ge` is unbounded, so the minima `> 1` are infinite;
`infinitelyManyInfiniteOrbits_of_minima`. -/
theorem yPerm_infinitelyManyInfiniteOrbits : InfinitelyManyInfiniteOrbits yPerm := by
  apply infinitelyManyInfiniteOrbits_of_minima hyp_yPerm
  intro hfin
  classical
  have hX : 1 ≤ 8 * (hfin.toFinset.card + 2) := by omega
  have hge := minCount_yPerm_ge hX
  have hle : minCount yPerm (8 * (hfin.toFinset.card + 2)) ≤ hfin.toFinset.card + 1 := by
    unfold minCount
    calc _ ≤ (insert 1 hfin.toFinset).card := by
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_filter, Finset.mem_Icc] at hx
          rw [Finset.mem_insert, Set.Finite.mem_toFinset]
          by_cases h1 : x = 1
          · exact Or.inl h1
          · exact Or.inr ⟨by omega, by simpa using h1, hx.2⟩
      _ ≤ _ := Finset.card_insert_le _ _
  push_cast at hge
  omega

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

/-! ## Theorem Y (4): the density

The return word of `2k` is read off the phase `(u, w) = ({k c₀}, {k c₁})`, `c₀ = α/2`,
`c₁ = xα/2` (`yPh_mem_yWord`): `E` iff `u < 1/2`; `E O` iff `u ≥ 1/2` and the second phase
`w − xu + x ∉ (1/2, 1]`; on `E O O`, `E O O E` iff `w` lies in the strip
`[μ(u), μ(u) + δ)`, `δ = 1/(2(1 + x))` (via `Δ′ ∈ (0, 1]`).  The cylinders are a box, two
convex polygons and their differences (null frontier, `Convex.addHaar_frontier`); their areas
are computed by Fubini on sheared strips (`volume_shear`). -/

section Density

open MeasureTheory Set

/-- The phase frequencies `c₀ = α/2`, `c₁ = αx/2`. -/
noncomputable def yc0 : ℝ := alphaY / 2
noncomputable def yc1 : ℝ := yRoot * alphaY / 2

theorem floor_two_mul_of_lt' {y : ℝ} (h : Int.fract y < 1 / 2) : ⌊2 * y⌋ = 2 * ⌊y⌋ := by
  rw [Int.floor_eq_iff]
  have := Int.fract_nonneg y
  unfold Int.fract at *
  push_cast
  constructor <;> linarith

theorem floor_two_mul_of_ge' {y : ℝ} (h : 1 / 2 ≤ Int.fract y) : ⌊2 * y⌋ = 2 * ⌊y⌋ + 1 := by
  rw [Int.floor_eq_iff]
  have := Int.fract_lt_one y
  unfold Int.fract at *
  push_cast
  constructor <;> linarith

/-- First step: `W(2k) = 2⌊kc₀⌋ + [u ≥ 1/2]`. -/
theorem wy_two_mul_phase (k : ℤ) :
    wy alphaY (2 * k) =
      2 * ⌊(k : ℝ) * yc0⌋ + if 1 / 2 ≤ Int.fract ((k : ℝ) * yc0) then 1 else 0 := by
  rw [wy_two_mul, show (k : ℝ) * alphaY = 2 * ((k : ℝ) * yc0) by unfold yc0; ring]
  split_ifs with h
  · exact floor_two_mul_of_ge' h
  · rw [floor_two_mul_of_lt' (not_le.1 h)]; ring

theorem wy_two_mul_odd_iff (k : ℤ) :
    wy alphaY (2 * k) % 2 = 1 ↔ 1 / 2 ≤ Int.fract ((k : ℝ) * yc0) := by
  rw [wy_two_mul_phase]
  split_ifs with h
  · simp only [h, iff_true]; omega
  · simp only [h, iff_false]; omega

theorem yF1_phase {k : ℤ} (h : 1 / 2 ≤ Int.fract ((k : ℝ) * yc0)) :
    yF1 (2 * k) = 2 * Int.fract ((k : ℝ) * yc0) - 1 := by
  unfold yF1
  rw [wy_two_mul_phase, if_pos h, show 2 * k / 2 = k by omega]
  have := Int.floor_add_fract ((k : ℝ) * yc0)
  unfold yc0 at *
  push_cast
  linarith

/-- The second phase `w' = w − xu + x` and the second step:
`W²(2k) = 2⌊kc₁⌋ + ⌈2w'⌉ − 1` when `u ≥ 1/2`. -/
theorem wy_wy_two_mul_phase {k : ℤ} (h : 1 / 2 ≤ Int.fract ((k : ℝ) * yc0)) :
    wy alphaY (wy alphaY (2 * k)) = 2 * ⌊(k : ℝ) * yc1⌋ +
      ⌈2 * (Int.fract ((k : ℝ) * yc1) - yRoot * Int.fract ((k : ℝ) * yc0) + yRoot)⌉ - 1 := by
  rw [wy_two_mul_phase, if_pos h,
    show 2 * ⌊(k : ℝ) * yc0⌋ + 1 = 2 * (⌊(k : ℝ) * yc0⌋ + 1) - 1 by ring,
    wy_two_mul_sub_one, alphaY_div_sub_one, betaY]
  have h0 := Int.floor_add_fract ((k : ℝ) * yc0)
  have h1 := Int.floor_add_fract ((k : ℝ) * yc1)
  have hc : yc1 = yRoot * yc0 := by unfold yc0 yc1; ring
  rw [show (((⌊(k : ℝ) * yc0⌋ + 1 : ℤ) : ℝ) * (2 * yRoot)) =
      ((2 * ⌊(k : ℝ) * yc1⌋ : ℤ) : ℝ) +
        2 * (Int.fract ((k : ℝ) * yc1) - yRoot * Int.fract ((k : ℝ) * yc0) + yRoot) by
    push_cast; linear_combination (2 * yRoot) * h0 - 2 * h1 - 2 * (k : ℝ) * hc]
  rw [Int.ceil_intCast_add]
  try ring

theorem ceil_two_mul_even_iff {y : ℝ} (h0 : 0 < y) (h1 : y < 3 / 2) :
    ⌈2 * y⌉ % 2 = 0 ↔ 1 / 2 < y ∧ y ≤ 1 := by
  rcases le_or_gt y (1 / 2) with ha | ha
  · have : ⌈2 * y⌉ = 1 := by rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith
    rw [this]; constructor
    · intro h; omega
    · rintro ⟨h, -⟩; linarith
  rcases le_or_gt y 1 with hb | hb
  · have : ⌈2 * y⌉ = 2 := by rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith
    rw [this]; exact ⟨fun _ => ⟨ha, hb⟩, fun _ => rfl⟩
  · have : ⌈2 * y⌉ = 3 := by rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith
    rw [this]; constructor
    · intro h; omega
    · rintro ⟨-, h⟩; linarith

/-- The second phase `w' = w − xu + x`. -/
noncomputable def yW2 (u w : ℝ) : ℝ := w - yRoot * u + yRoot

theorem yW2_mem {u w : ℝ} (hu : 1 / 2 ≤ u) (hu1 : u < 1) (hw : 0 ≤ w) (hw1 : w < 1) :
    0 < yW2 u w ∧ yW2 u w < 3 / 2 := by
  have hx := yRoot_bounds
  unfold yW2
  constructor <;> nlinarith

theorem wy_wy_two_mul_odd_iff {k : ℤ} (h : 1 / 2 ≤ Int.fract ((k : ℝ) * yc0)) :
    wy alphaY (wy alphaY (2 * k)) % 2 = 1 ↔
      1 / 2 < yW2 (Int.fract ((k : ℝ) * yc0)) (Int.fract ((k : ℝ) * yc1)) ∧
        yW2 (Int.fract ((k : ℝ) * yc0)) (Int.fract ((k : ℝ) * yc1)) ≤ 1 := by
  obtain ⟨h0, h1⟩ := yW2_mem h (Int.fract_lt_one _) (Int.fract_nonneg _) (Int.fract_lt_one _)
  rw [wy_wy_two_mul_phase h, ← ceil_two_mul_even_iff h0 h1]
  unfold yW2
  omega

theorem yFodd_phase {k : ℤ} (h : 1 / 2 ≤ Int.fract ((k : ℝ) * yc0))
    (h2 : wy alphaY (wy alphaY (2 * k)) % 2 = 1) :
    yFodd (wy alphaY (2 * k)) =
      2 * yW2 (Int.fract ((k : ℝ) * yc0)) (Int.fract ((k : ℝ) * yc1)) - 1 := by
  obtain ⟨h0, h1⟩ := yW2_mem h (Int.fract_lt_one _) (Int.fract_nonneg _) (Int.fract_lt_one _)
  have hw := (wy_wy_two_mul_odd_iff h).1 h2
  have hc : ⌈2 * yW2 (Int.fract ((k : ℝ) * yc0)) (Int.fract ((k : ℝ) * yc1))⌉ = 2 := by
    rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith [hw.1, hw.2]
  unfold yFodd
  rw [wy_wy_two_mul_phase h]
  unfold yW2 at hc ⊢
  rw [hc, wy_two_mul_phase, if_pos h]
  have h0' := Int.floor_add_fract ((k : ℝ) * yc0)
  have h1' := Int.floor_add_fract ((k : ℝ) * yc1)
  have hcc : yc1 = yRoot * yc0 := by unfold yc0 yc1; ring
  push_cast
  linear_combination (2 * yRoot) * h0' - 2 * h1' - 2 * (k : ℝ) * hcc

/-- On `E O O`, `W³` is odd iff `Δ′ ∉ (0, 1]`. -/
theorem wy_iterate_three_odd_iff {n : ℤ} (hn : n % 2 = 0) (h₁ : wy alphaY n % 2 = 1)
    (h₂ : (wy alphaY)^[2] n % 2 = 1) :
    (wy alphaY)^[3] n % 2 = 1 ↔
      ¬ (0 < yPhase3 (yF1 n) (yFodd (wy alphaY n)) ∧
        yPhase3 (yF1 n) (yFodd (wy alphaY n)) ≤ 1) := by
  have ht := wy_iterate_three_sub_mem hn h₁ h₂
  have hph := wy_iterate_three_phase hn
  obtain ⟨c1, c2⟩ := yFodd_mem h₂
  set t := (wy alphaY)^[3] n - (-2 * n + wy alphaY n - (wy alphaY)^[2] n) with ht_def
  have htr : (t : ℝ) = yPhase3 (yF1 n) (yFodd (wy alphaY n)) - yFodd ((wy alphaY)^[2] n) := by
    rw [ht_def]; push_cast; linarith
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
  constructor
  · rintro hodd ⟨hp0, hp1⟩
    have : t = 0 := by
      have a : (-1 : ℝ) < t := by rw [htr]; linarith
      have b : (t : ℝ) < 1 := by rw [htr]; linarith
      have := Int.cast_lt.1 (show ((-1 : ℤ) : ℝ) < t by push_cast; exact a)
      have := Int.cast_lt.1 (show (t : ℝ) < ((1 : ℤ) : ℝ) by push_cast; exact b)
      omega
    omega
  · intro hn'
    rcases ht with h | h | h
    · omega
    · exfalso; apply hn'
      have : (t : ℝ) = 0 := by rw [h]; simp
      constructor <;> linarith
    · omega

/-- The second-phase threshold `m(u)` and width `δ` of the `E O O E` cylinder. -/
noncomputable def yMu (u : ℝ) : ℝ :=
  (yRoot + (1 - yRoot - yRoot ^ 2) / (1 + yRoot)) * u +
    (1 / 2 - yRoot + (2 * yRoot ^ 2 + 3 * yRoot - 2) / (2 * (1 + yRoot)))

noncomputable def yDelta : ℝ := 1 / (2 * (1 + yRoot))

theorem yPhase3_eq_mu (u w : ℝ) :
    yPhase3 (2 * u - 1) (2 * yW2 u w - 1) = 2 * (1 + yRoot) * (yMu u + yDelta - w) := by
  have hx := yRoot_bounds
  have hp : (1 + yRoot) ≠ 0 := by linarith
  unfold yPhase3 yW2 yMu yDelta
  field_simp
  ring

theorem yPhase3_mem_Ioc_iff (u w : ℝ) :
    (0 < yPhase3 (2 * u - 1) (2 * yW2 u w - 1) ∧ yPhase3 (2 * u - 1) (2 * yW2 u w - 1) ≤ 1) ↔
      yMu u ≤ w ∧ w < yMu u + yDelta := by
  have hx := yRoot_bounds
  have hp : 0 < 1 + yRoot := by linarith
  rw [yPhase3_eq_mu]
  have hd : 2 * (1 + yRoot) * yDelta = 1 := by unfold yDelta; field_simp
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · nlinarith
    · nlinarith
  · rintro ⟨h1, h2⟩
    constructor
    · nlinarith
    · nlinarith

/-! ### Word cylinders in the phase square -/

/-- The Weyl frequencies `(c₀, c₁)`. -/
noncomputable def yTheta : Fin 2 → ℝ := ![yc0, yc1]

/-- The phase `({k c₀}, {k c₁})`. -/
noncomputable def yPh (k : ℕ) : Fin 2 → ℝ := fun i => Int.fract ((k : ℝ) * yTheta i)

def yCube : Set (Fin 2 → ℝ) := Set.univ.pi fun _ => Set.Ico (0 : ℝ) 1

def yB0 : Set (Fin 2 → ℝ) := {ψ | ψ ∈ yCube ∧ ψ 0 < 1 / 2}

noncomputable def yS23 : Set (Fin 2 → ℝ) :=
  {ψ | ψ ∈ yCube ∧ 1 / 2 ≤ ψ 0 ∧ 1 / 2 < yW2 (ψ 0) (ψ 1) ∧ yW2 (ψ 0) (ψ 1) ≤ 1}

noncomputable def yB2 : Set (Fin 2 → ℝ) :=
  {ψ | ψ ∈ yCube ∧ 1 / 2 ≤ ψ 0 ∧ yMu (ψ 0) ≤ ψ 1 ∧ ψ 1 < yMu (ψ 0) + yDelta}

noncomputable def yB1 : Set (Fin 2 → ℝ) := yCube \ (yB0 ∪ yS23)

noncomputable def yB3 : Set (Fin 2 → ℝ) := yS23 \ yB2

/-- The cylinder of return word `E Oʲ`. -/
noncomputable def yWord : ℕ → Set (Fin 2 → ℝ)
  | 0 => yB0
  | 1 => yB1
  | 2 => yB2
  | _ => yB3

lemma mem_yCube {ψ : Fin 2 → ℝ} : ψ ∈ yCube ↔ (0 ≤ ψ 0 ∧ ψ 0 < 1) ∧ (0 ≤ ψ 1 ∧ ψ 1 < 1) := by
  simp [yCube, Set.mem_pi, Fin.forall_fin_two]

lemma yPh_mem (k : ℕ) : yPh k ∈ yCube :=
  mem_yCube.2 ⟨⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩⟩

lemma yPh_zero (k : ℕ) : yPh k 0 = Int.fract (((k : ℤ) : ℝ) * yc0) := by
  simp [yPh, yTheta]

lemma yPh_one (k : ℕ) : yPh k 1 = Int.fract (((k : ℤ) : ℝ) * yc1) := by
  simp [yPh, yTheta]

lemma yMu_add_yDelta (u : ℝ) :
    yMu u + yDelta = yRoot * u - yRoot + 1 + (1 - yRoot - yRoot ^ 2) / (1 + yRoot) * (u - 1) := by
  have hx := yRoot_bounds
  have hp : (1 + yRoot) ≠ 0 := by linarith
  have h3 := yRoot_spec.2.2
  unfold yMu yDelta
  field_simp
  ring

lemma yB2_subset : yB2 ⊆ yS23 := by
  rintro ψ ⟨hc, h0, h1, h2⟩
  have hx := yRoot_bounds
  have hc' := mem_yCube.1 hc
  have hp : 0 < 1 + yRoot := by linarith
  have hg := yG_pos
  have hq : 0 < (1 - yRoot - yRoot ^ 2) / (1 + yRoot) := div_pos hg hp
  refine ⟨hc, h0, ?_, ?_⟩
  · unfold yW2
    unfold yMu at h1
    have : (1 - yRoot - yRoot ^ 2) / (1 + yRoot) * ψ 0 ≥ 0 := by positivity
    have e : (2 * yRoot ^ 2 + 3 * yRoot - 2) / (2 * (1 + yRoot)) =
        (yRoot ^ 2 + 2 * yRoot - 1) / (2 * (1 + yRoot)) -
          (1 - yRoot - yRoot ^ 2) / (1 + yRoot) / 2 := by
      field_simp; ring
    rw [e] at h1
    have : (yRoot ^ 2 + 2 * yRoot - 1) / (2 * (1 + yRoot)) > 0 :=
      div_pos (by nlinarith) (by linarith)
    nlinarith
  · unfold yW2
    rw [yMu_add_yDelta] at h2
    have : (1 - yRoot - yRoot ^ 2) / (1 + yRoot) * (ψ 0 - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hq.le (by linarith)
    linarith

/-- On `E O O`, `W³` is even iff the phase lies in the `E O O E` strip. -/
lemma wy_three_even_iff_strip {k : ℤ} (h : 1 / 2 ≤ Int.fract ((k : ℝ) * yc0))
    (h2 : wy alphaY (wy alphaY (2 * k)) % 2 = 1) :
    (wy alphaY)^[3] (2 * k) % 2 = 0 ↔
      yMu (Int.fract ((k : ℝ) * yc0)) ≤ Int.fract ((k : ℝ) * yc1) ∧
        Int.fract ((k : ℝ) * yc1) < yMu (Int.fract ((k : ℝ) * yc0)) + yDelta := by
  have h1 : wy alphaY (2 * k) % 2 = 1 := (wy_two_mul_odd_iff k).2 h
  have := wy_iterate_three_odd_iff (show (2 * k) % 2 = 0 by omega) h1 h2
  rw [yF1_phase h, yFodd_phase h h2, yPhase3_mem_Ioc_iff] at this
  constructor
  · intro he; by_contra hn; have := this.2 hn; omega
  · intro hs; by_contra hn; exact this.1 (by omega) hs

lemma yWord_disjoint {j j' : ℕ} (hj : j < j') (hj' : j' ≤ 3) :
    Disjoint (yWord j) (yWord j') := by
  rw [Set.disjoint_left]
  intro ψ h1 h2
  interval_cases j' <;> interval_cases j <;>
    simp only [yWord, yB0, yB1, yB3, Set.mem_sdiff, Set.mem_union, Set.mem_ofPred_eq] at h1 h2
  · exact h2.2 (Or.inl h1)
  · linarith [h1.2, h2.2.1]
  · exact h1.2 (Or.inr (yB2_subset h2))
  · linarith [h1.2, h2.1.2.1]
  · exact h1.2 (Or.inr h2.1)
  · exact h2.2 h1

/-- The return word of `2k` is read off the phase of `k`. -/
lemma yPh_mem_yWord (k : ℕ) (hk : 1 ≤ k) :
    yPh k ∈ yWord (returnTime yPerm {n | n % 2 = 0} (2 * (k : ℤ)) - 1) := by
  have hS0 : 2 * (k : ℤ) ∈ {n : ℤ | n % 2 = 0} := by simp only [Set.mem_ofPred_eq]; omega
  have hΦ0 : 2 * (k : ℤ) ∉ ({1} : Set ℤ) := by simp only [Set.mem_singleton_iff]; omega
  obtain ⟨h1, hT, hRS, -, hint⟩ := returnTime_spec hyp_yPerm hS0 (by omega) hΦ0
  set τ := returnTime yPerm {n | n % 2 = 0} (2 * (k : ℤ))
  have hodd : ∀ i, 1 ≤ i → i < τ → (wy alphaY)^[i] (2 * (k : ℤ)) % 2 = 1 := by
    intro i hi1 hi2
    have := hint i hi1 hi2
    simp only [Set.mem_ofPred_eq, yPerm_pow_apply] at this
    omega
  have hev : (wy alphaY)^[τ] (2 * (k : ℤ)) % 2 = 0 := by
    have := hRS
    simp only [returnMap, Set.mem_ofPred_eq, yPerm_pow_apply] at this
    exact this
  have hc := yPh_mem k
  have hu := yPh_zero k
  have hw := yPh_one k
  have hτ : τ = 1 ∨ τ = 2 ∨ τ = 3 ∨ τ = 4 := by omega
  rcases hτ with h | h | h | h
  · rw [h] at hev
    rw [h]
    refine ⟨hc, ?_⟩
    rw [hu]
    by_contra hne
    have := (wy_two_mul_odd_iff (k : ℤ)).2 (not_lt.1 hne)
    simp only [Function.iterate_one] at hev
    omega
  · rw [h] at hev hodd
    rw [h]
    have hW := hodd 1 le_rfl (by norm_num)
    simp only [Function.iterate_one] at hW
    have hu' := (wy_two_mul_odd_iff (k : ℤ)).1 hW
    refine ⟨hc, ?_⟩
    rintro (h0 | ⟨-, -, hs⟩)
    · exact absurd h0.2 (by rw [hu]; linarith)
    · have := (wy_wy_two_mul_odd_iff hu').2 (by rw [← hu, ← hw]; exact hs)
      rw [wy_iterate_two] at hev
      omega
  · rw [h] at hev hodd
    rw [h]
    have hW := hodd 1 le_rfl (by norm_num)
    have hW2 := hodd 2 (by norm_num) (by norm_num)
    simp only [Function.iterate_one] at hW
    rw [wy_iterate_two] at hW2
    have hu' := (wy_two_mul_odd_iff (k : ℤ)).1 hW
    have hs := (wy_three_even_iff_strip hu' hW2).1 hev
    refine ⟨hc, by rw [hu]; exact hu', ?_⟩
    rw [hu, hw]
    exact hs
  · rw [h] at hodd
    rw [h]
    have hW := hodd 1 le_rfl (by norm_num)
    have hW2 := hodd 2 (by norm_num) (by norm_num)
    have hW3 := hodd 3 (by norm_num) (by norm_num)
    simp only [Function.iterate_one] at hW
    rw [wy_iterate_two] at hW2
    have hu' := (wy_two_mul_odd_iff (k : ℤ)).1 hW
    have hs := (wy_wy_two_mul_odd_iff hu').1 hW2
    refine ⟨⟨hc, by rw [hu]; exact hu', by rw [hu, hw]; exact hs.1,
      by rw [hu, hw]; exact hs.2⟩, ?_⟩
    rintro ⟨-, -, hs2⟩
    have := (wy_three_even_iff_strip hu' hW2).2 (by rw [← hu, ← hw]; exact hs2)
    omega

/-- `returnTime = j + 1` iff the phase lies in the `j`-th word cylinder. -/
lemma returnTime_yPerm_eq_iff (k : ℕ) (hk : 1 ≤ k) {j : ℕ} (hj : j ≤ 3) :
    returnTime yPerm {n | n % 2 = 0} (2 * (k : ℤ)) = j + 1 ↔ yPh k ∈ yWord j := by
  have hmem := yPh_mem_yWord k hk
  have hS0 : 2 * (k : ℤ) ∈ {n : ℤ | n % 2 = 0} := by simp only [Set.mem_ofPred_eq]; omega
  have hΦ0 : 2 * (k : ℤ) ∉ ({1} : Set ℤ) := by simp only [Set.mem_singleton_iff]; omega
  obtain ⟨h1, hT, -⟩ := returnTime_spec hyp_yPerm hS0 (by omega) hΦ0
  constructor
  · intro he; rw [he] at hmem; simpa using hmem
  · intro hw
    by_contra hne
    rcases lt_or_gt_of_ne (show returnTime yPerm {n | n % 2 = 0} (2 * (k : ℤ)) - 1 ≠ j by
      omega) with hlt | hgt
    · exact Set.disjoint_left.1 (yWord_disjoint hlt hj) hmem hw
    · exact Set.disjoint_left.1 (yWord_disjoint hgt (by omega)) hw hmem

/-! ### Volumes and frontiers of the word cylinders -/

lemma volume_shear (A T : Set ℝ) (hA : MeasurableSet A) (hT : MeasurableSet T) (f : ℝ → ℝ)
    (hf : Measurable f) :
    volume {ψ : Fin 2 → ℝ | ψ 0 ∈ A ∧ ψ 1 - f (ψ 0) ∈ T} = volume A * volume T := by
  set s : Set (ℝ × ℝ) := {p | p.1 ∈ A ∧ p.2 - f p.1 ∈ T}
  have hs : MeasurableSet s :=
    (measurable_fst hA).inter ((measurable_snd.sub (hf.comp measurable_fst)) hT)
  have hpre : {ψ : Fin 2 → ℝ | ψ 0 ∈ A ∧ ψ 1 - f (ψ 0) ∈ T} =
      MeasurableEquiv.finTwoArrow ⁻¹' s := by
    ext ψ; simp [s, MeasurableEquiv.finTwoArrow, MeasurableEquiv.piFinTwo]
  rw [hpre, (volume_preserving_finTwoArrow ℝ).measure_preimage hs.nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_apply hs]
  have hsec : ∀ x : ℝ, volume (Prod.mk x ⁻¹' s) = A.indicator (fun _ => volume T) x := by
    intro x
    by_cases hx : x ∈ A
    · rw [indicator_of_mem hx]
      have : Prod.mk x ⁻¹' s = (fun y => y + -f x) ⁻¹' T := by
        ext y; simp [s, hx, sub_eq_add_neg]
      rw [this, measure_preimage_add_right]
    · rw [indicator_of_notMem hx]
      have : Prod.mk x ⁻¹' s = ∅ := by ext y; simp [s, hx]
      rw [this, measure_empty]
  simp_rw [hsec]
  rw [lintegral_indicator_const hA, mul_comm]

lemma measurableSet_shear (A T : Set ℝ) (hA : MeasurableSet A) (hT : MeasurableSet T)
    (f : ℝ → ℝ) (hf : Measurable f) :
    MeasurableSet {ψ : Fin 2 → ℝ | ψ 0 ∈ A ∧ ψ 1 - f (ψ 0) ∈ T} :=
  ((measurable_pi_apply 0) hA).inter
    (((measurable_pi_apply 1).sub (hf.comp (measurable_pi_apply 0))) hT)

lemma yW2_lower {u : ℝ} (hu : 1 / 2 ≤ u) : 0 < yRoot * u - yRoot + 1 / 2 := by
  have hx := yRoot_bounds; nlinarith

lemma yMu_lower {u : ℝ} (hu : 1 / 2 ≤ u) : 1 / 2 < yW2 u (yMu u) := by
  have hx := yRoot_bounds
  have hp : 0 < 1 + yRoot := by linarith
  have hq : 0 < (1 - yRoot - yRoot ^ 2) / (1 + yRoot) := div_pos yG_pos hp
  unfold yW2 yMu
  have e : (2 * yRoot ^ 2 + 3 * yRoot - 2) / (2 * (1 + yRoot)) =
      (yRoot ^ 2 + 2 * yRoot - 1) / (2 * (1 + yRoot)) -
        (1 - yRoot - yRoot ^ 2) / (1 + yRoot) / 2 := by
    field_simp; ring
  rw [e]
  have : (yRoot ^ 2 + 2 * yRoot - 1) / (2 * (1 + yRoot)) > 0 :=
    div_pos (by nlinarith) (by linarith)
  nlinarith

lemma yMu_upper {u : ℝ} (hu : u ≤ 1) : yMu u + yDelta ≤ yRoot * u - yRoot + 1 := by
  have hx := yRoot_bounds
  have hp : 0 < 1 + yRoot := by linarith
  have hq : 0 < (1 - yRoot - yRoot ^ 2) / (1 + yRoot) := div_pos yG_pos hp
  rw [yMu_add_yDelta]
  have : (1 - yRoot - yRoot ^ 2) / (1 + yRoot) * (u - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hq.le (by linarith)
  linarith

lemma yDelta_pos : 0 < yDelta := by
  have hx := yRoot_bounds; unfold yDelta; apply div_pos one_pos; linarith

lemma yB0_eq :
    yB0 = {ψ : Fin 2 → ℝ | ψ 0 ∈ Ico 0 (1 / 2) ∧ ψ 1 - (fun _ => 0) (ψ 0) ∈ Ico 0 1} := by
  ext ψ
  simp only [yB0, mem_yCube, Set.mem_ofPred_eq, Set.mem_Ico, sub_zero]
  constructor
  · rintro ⟨⟨⟨a, -⟩, c⟩, d⟩; exact ⟨⟨a, d⟩, c⟩
  · rintro ⟨⟨a, d⟩, c⟩; exact ⟨⟨⟨a, by linarith⟩, c⟩, d⟩

lemma yS23_eq : yS23 = {ψ : Fin 2 → ℝ | ψ 0 ∈ Ico (1 / 2) 1 ∧
    ψ 1 - (fun u => yRoot * u - yRoot) (ψ 0) ∈ Ioc (1 / 2) 1} := by
  ext ψ
  simp only [yS23, mem_yCube, Set.mem_ofPred_eq, Set.mem_Ico, Set.mem_Ioc, yW2]
  have hx := yRoot_bounds
  constructor
  · rintro ⟨⟨⟨a, b⟩, c⟩, d, e, f⟩
    exact ⟨⟨d, b⟩, by linarith, by linarith⟩
  · rintro ⟨⟨d, b⟩, e, f⟩
    have := yW2_lower d
    refine ⟨⟨⟨by linarith, b⟩, by linarith, by nlinarith⟩, d, by linarith, by linarith⟩

lemma yB2_eq : yB2 = {ψ : Fin 2 → ℝ | ψ 0 ∈ Ico (1 / 2) 1 ∧ ψ 1 - yMu (ψ 0) ∈ Ico 0 yDelta} := by
  ext ψ
  simp only [yB2, mem_yCube, Set.mem_ofPred_eq, Set.mem_Ico]
  have hx := yRoot_bounds
  constructor
  · rintro ⟨⟨⟨a, b⟩, c⟩, d, e, f⟩
    exact ⟨⟨d, b⟩, by linarith, by linarith⟩
  · rintro ⟨⟨d, b⟩, e, f⟩
    have h1 := yMu_lower d
    have h2 := yMu_upper b.le
    have h3 := yW2_lower d
    unfold yW2 at h1
    refine ⟨⟨⟨by linarith, b⟩, by linarith, by nlinarith⟩, d, by linarith, by linarith⟩

lemma measurable_yMu : Measurable yMu := by
  unfold yMu; fun_prop

lemma measurableSet_yCube : MeasurableSet yCube :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico

lemma measurableSet_yB0 : MeasurableSet yB0 := by
  rw [yB0_eq]; exact measurableSet_shear _ _ measurableSet_Ico measurableSet_Ico _ measurable_const

lemma measurableSet_yS23 : MeasurableSet yS23 := by
  rw [yS23_eq]
  exact measurableSet_shear _ _ measurableSet_Ico measurableSet_Ioc (fun u => yRoot * u - yRoot)
    ((measurable_id.const_mul _).sub_const _)

lemma measurableSet_yB2 : MeasurableSet yB2 := by
  rw [yB2_eq]; exact measurableSet_shear _ _ measurableSet_Ico measurableSet_Ico _ measurable_yMu

lemma volume_yCube : volume yCube = 1 := by
  rw [yCube, Real.volume_pi_Ico]; simp

lemma volume_yB0 : volume.real yB0 = 1 / 2 := by
  rw [measureReal_def, yB0_eq, volume_shear _ _ measurableSet_Ico measurableSet_Ico _
    measurable_const, Real.volume_Ico, Real.volume_Ico, ← ENNReal.ofReal_mul (by norm_num),
    ENNReal.toReal_ofReal (by norm_num)]
  norm_num

lemma volume_yS23 : volume.real yS23 = 1 / 4 := by
  rw [measureReal_def, yS23_eq, volume_shear _ _ measurableSet_Ico measurableSet_Ioc
    (fun u => yRoot * u - yRoot) ((measurable_id.const_mul _).sub_const _), Real.volume_Ico,
    Real.volume_Ioc, ← ENNReal.ofReal_mul (by norm_num),
    ENNReal.toReal_ofReal (by norm_num)]
  norm_num

lemma volume_yB2 : volume.real yB2 = 1 / (4 * (1 + yRoot)) := by
  have hx := yRoot_bounds
  rw [measureReal_def, yB2_eq, volume_shear _ _ measurableSet_Ico measurableSet_Ico _
    measurable_yMu, Real.volume_Ico, Real.volume_Ico, ← ENNReal.ofReal_mul (by norm_num),
    ENNReal.toReal_ofReal (by have := yDelta_pos; positivity)]
  unfold yDelta
  field_simp
  ring

lemma yB0_subset : yB0 ⊆ yCube := fun _ h => h.1
lemma yS23_subset : yS23 ⊆ yCube := fun _ h => h.1

lemma volume_yB1 : volume.real yB1 = 1 / 4 := by
  have hd : Disjoint yB0 yS23 := by
    rw [Set.disjoint_left]; rintro ψ ⟨-, h⟩ ⟨-, h', -⟩; linarith
  rw [yB1, measureReal_sdiff (Set.union_subset yB0_subset yS23_subset)
    (measurableSet_yB0.union measurableSet_yS23) (by rw [volume_yCube]; simp),
    measureReal_union hd measurableSet_yS23
      (measure_ne_top_of_subset yB0_subset (by rw [volume_yCube]; simp))
      (measure_ne_top_of_subset yS23_subset (by rw [volume_yCube]; simp)),
    volume_yB0, volume_yS23, measureReal_def, volume_yCube]
  norm_num

lemma volume_yB3 : volume.real yB3 = yRoot / (4 * (1 + yRoot)) := by
  have hx := yRoot_bounds
  rw [yB3, measureReal_sdiff yB2_subset measurableSet_yB2
    (measure_ne_top_of_subset yS23_subset (by rw [volume_yCube]; simp)),
    volume_yS23, volume_yB2]
  have hp : 1 + yRoot ≠ 0 := by linarith
  field_simp
  ring

lemma comb_lt {a b p q p' q' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (hp : p < p')
    (hq : q < q') : a * p + b * q < a * p' + b * q' := by
  rcases ha.eq_or_lt with rfl | ha'
  · rw [zero_add] at hab; subst hab; linarith
  · nlinarith [mul_lt_mul_of_pos_left hp ha', mul_le_mul_of_nonneg_left hq.le hb]

lemma comb_le {a b p q p' q' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : p ≤ p') (hq : q ≤ q') :
    a * p + b * q ≤ a * p' + b * q' := by
  nlinarith [mul_le_mul_of_nonneg_left hp ha, mul_le_mul_of_nonneg_left hq hb]

lemma yMu_comb {a b : ℝ} (hab : a + b = 1) (u u' : ℝ) :
    yMu (a * u + b * u') = a * yMu u + b * yMu u' := by
  have : yMu (a * u + b * u') - (a * yMu u + b * yMu u') = (1 - (a + b)) * yMu 0 := by
    unfold yMu; ring
  rw [hab] at this; linarith

lemma yW2_comb {a b : ℝ} (hab : a + b = 1) (u u' w w' : ℝ) :
    yW2 (a * u + b * u') (a * w + b * w') = a * yW2 u w + b * yW2 u' w' := by
  have : yW2 (a * u + b * u') (a * w + b * w') - (a * yW2 u w + b * yW2 u' w') =
      (1 - (a + b)) * yW2 0 0 := by
    unfold yW2; ring
  rw [hab] at this; linarith

lemma convex_yCube : Convex ℝ yCube := convex_pi fun _ _ => convex_Ico 0 1

lemma comb_apply (ψ φ : Fin 2 → ℝ) (a b : ℝ) (i : Fin 2) :
    (a • ψ + b • φ) i = a * ψ i + b * φ i := by simp

lemma convex_yB0 : Convex ℝ yB0 := by
  intro ψ ⟨hψ, h⟩ φ ⟨hφ, h'⟩ a b ha hb hab
  refine ⟨convex_yCube hψ hφ ha hb hab, ?_⟩
  rw [comb_apply]
  have := comb_lt ha hb hab h h'
  rw [← add_mul, hab, one_mul] at this
  exact this

lemma convex_yS23 : Convex ℝ yS23 := by
  intro ψ ⟨hψ, h0, h1, h2⟩ φ ⟨hφ, h0', h1', h2'⟩ a b ha hb hab
  refine ⟨convex_yCube hψ hφ ha hb hab, ?_, ?_, ?_⟩ <;> simp only [comb_apply]
  · have := comb_le ha hb h0 h0'
    rw [← add_mul, hab, one_mul] at this
    exact this
  · rw [yW2_comb hab]
    have := comb_lt ha hb hab h1 h1'
    rw [← add_mul, hab, one_mul] at this
    exact this
  · rw [yW2_comb hab]
    have := comb_le ha hb h2 h2'
    rw [← add_mul, hab, one_mul] at this
    exact this

lemma convex_yB2 : Convex ℝ yB2 := by
  intro ψ ⟨hψ, h0, h1, h2⟩ φ ⟨hφ, h0', h1', h2'⟩ a b ha hb hab
  refine ⟨convex_yCube hψ hφ ha hb hab, ?_, ?_, ?_⟩ <;> simp only [comb_apply]
  · have := comb_le ha hb h0 h0'
    rw [← add_mul, hab, one_mul] at this
    exact this
  · rw [yMu_comb hab]
    exact comb_le ha hb h1 h1'
  · rw [yMu_comb hab]
    have := comb_lt ha hb hab h2 h2'
    have e : a * (yMu (ψ 0) + yDelta) + b * (yMu (φ 0) + yDelta) =
        a * yMu (ψ 0) + b * yMu (φ 0) + yDelta := by
      linear_combination yDelta * hab
    linarith

lemma frontier_sdiff_subset' {X : Type*} [TopologicalSpace X] (s t : Set X) :
    frontier (s \ t) ⊆ frontier s ∪ frontier t := by
  rw [Set.sdiff_eq]
  refine (frontier_inter_subset s tᶜ).trans ?_
  rw [frontier_compl]
  exact Set.union_subset_union Set.inter_subset_left Set.inter_subset_right

lemma volume_frontier_yWord (j : ℕ) : volume (frontier (yWord j)) = 0 := by
  have c0 := convex_yB0.addHaar_frontier volume
  have c1 := convex_yS23.addHaar_frontier volume
  have c2 := convex_yB2.addHaar_frontier volume
  have c3 := convex_yCube.addHaar_frontier volume
  match j with
  | 0 => exact c0
  | 1 =>
    refine measure_mono_null ((frontier_sdiff_subset' _ _).trans
      (Set.union_subset_union_right _ ((frontier_union_subset _ _).trans
        (Set.union_subset_union Set.inter_subset_left Set.inter_subset_right)))) ?_
    exact measure_union_null c3 (measure_union_null c0 c1)
  | 2 => exact c2
  | _ + 3 =>
    exact measure_mono_null (frontier_sdiff_subset' _ _) (measure_union_null c1 c2)

lemma measurableSet_yWord (j : ℕ) : MeasurableSet (yWord j) := by
  match j with
  | 0 => exact measurableSet_yB0
  | 1 => exact measurableSet_yCube.diff (measurableSet_yB0.union measurableSet_yS23)
  | 2 => exact measurableSet_yB2
  | _ + 3 => exact measurableSet_yS23.diff measurableSet_yB2

/-- The word frequencies `(1/2, 1/4, 1/(4(1 + x)), x/(4(1 + x)))`. -/
noncomputable def yVol : ℕ → ℝ
  | 0 => 1 / 2
  | 1 => 1 / 4
  | 2 => 1 / (4 * (1 + yRoot))
  | _ => yRoot / (4 * (1 + yRoot))

lemma yWord_subset (j : ℕ) : yWord j ⊆ yCube := by
  match j with
  | 0 => exact yB0_subset
  | 1 => exact Set.sdiff_subset
  | 2 => exact yB2_subset.trans yS23_subset
  | _ + 3 => exact Set.sdiff_subset.trans yS23_subset

lemma volume_yWord (j : ℕ) :
    (volume (yWord j ∩ Set.univ.pi fun _ => Set.Ico (0 : ℝ) 1)).toReal = yVol j := by
  change (volume (yWord j ∩ yCube)).toReal = yVol j
  rw [Set.inter_eq_left.2 (yWord_subset j), ← measureReal_def]
  match j with
  | 0 => exact volume_yB0
  | 1 => exact volume_yB1
  | 2 => exact volume_yB2
  | _ + 3 => exact volume_yB3

/-! ### Weyl input, the sandwich, and the count -/

/-- `1, c₀, c₁` are `ℚ`-independent (times `2x − 1`: `2x − 1, x, x²`). -/
lemma linearIndependent_yTheta :
    LinearIndependent ℚ (Fin.cons (1 : ℝ) yTheta : Fin 3 → ℝ) := by
  have hind := linearIndependent_yRoot
  have hx := yRoot_bounds
  have hp : (2 * yRoot - 1) ≠ 0 := by linarith
  rw [Fintype.linearIndependent_iff] at hind ⊢
  intro g hg
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.cons_zero, Fin.cons_succ, Rat.smul_def,
    mul_one, yTheta, yc0, yc1, alphaY] at hg
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Matrix.cons_val_zero,
    Matrix.cons_val_one] at hg
  set g' : Fin 3 → ℚ := ![-g 0, 2 * g 0 + g 1, g 2]
  have h' : ∑ i, g' i • yRoot ^ (i : ℕ) = 0 := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Rat.smul_def, g']
    simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Fin.val_zero,
      Fin.val_one, Fin.val_two, pow_zero, pow_one, add_zero]
    push_cast
    have : (g 0 : ℝ) + (g 1 : ℝ) * (2 * yRoot / (2 * yRoot - 1) / 2) +
        (g 2 : ℝ) * (yRoot * (2 * yRoot / (2 * yRoot - 1)) / 2) = 0 := by
      linear_combination hg
    field_simp at this
    linear_combination this
  have hz := hind g' h'
  have a := hz 0
  have b := hz 1
  have c := hz 2
  simp only [g', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons, neg_eq_zero] at a b c
  intro i
  fin_cases i
  · exact a
  · simp only [Fin.mk_one]; rw [a] at b; simpa using b
  · exact c

open Classical in
/-- Weyl for the word cylinders. -/
lemma tendsto_yWordCount (hW : WeylEquidistributionMulti) (j : ℕ) :
    Tendsto (fun N : ℕ =>
      (((Finset.Icc 1 N).filter fun k : ℕ => yPh k ∈ yWord j).card : ℝ) / N)
        atTop (𝓝 (yVol j)) := by
  have := hW 2 yTheta linearIndependent_yTheta (yWord j) (measurableSet_yWord j)
    (volume_frontier_yWord j)
  rw [volume_yWord] at this
  exact this

/-- **Sandwich.**  Along an odd run, `|W^{j+1}(n) − xʲ(n/2)α| < 2`. -/
lemma yRun_sandwich {n : ℤ} (hn : n % 2 = 0) (j : ℕ)
    (hodd : ∀ i : ℕ, 1 ≤ i → i ≤ j → (wy alphaY)^[i] n % 2 = 1) :
    |((wy alphaY)^[j + 1] n : ℝ) - yRoot ^ j * (((n / 2 : ℤ) : ℝ) * alphaY)| < 2 := by
  have hx := yRoot_bounds
  induction j with
  | zero =>
    have := yF1_mem hn
    unfold yF1 at this
    rw [abs_lt]; simp only [zero_add, Function.iterate_one, pow_zero, one_mul]
    constructor <;> linarith
  | succ j ih =>
    have h1 := ih fun i h1 h2 => hodd i h1 (by omega)
    have h2 := yFodd_mem (hodd (j + 1) (by omega) le_rfl)
    unfold yFodd at h2
    rw [wy_iterate_succ (j + 1)]
    set v := (wy alphaY)^[j + 1] n
    set E := ((n / 2 : ℤ) : ℝ) * alphaY
    rw [abs_lt] at h1 ⊢
    have e : (wy alphaY v : ℝ) - yRoot ^ (j + 1) * E =
        yRoot * ((v : ℝ) - yRoot ^ j * E) + yRoot - (yRoot * ((v : ℝ) + 1) - wy alphaY v) := by
      ring
    rw [e]
    obtain ⟨a, b⟩ := h1
    constructor <;> nlinarith

/-- `⌊cX + d⌋₊ / X → c`. -/
lemma yTendsto_floor_linear_div {c : ℝ} (hc : 0 < c) (d : ℝ) :
    Tendsto (fun X : ℕ => (⌊c * X + d⌋₊ : ℝ) / X) atTop (𝓝 c) := by
  have hlo : Tendsto (fun X : ℕ => c + (d - 1) / X) atTop (𝓝 c) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (d - 1))
  have hhi : Tendsto (fun X : ℕ => c + d / X) atTop (𝓝 c) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat d)
  have hev : ∀ᶠ X : ℕ in atTop, 0 ≤ c * X + d ∧ (0 : ℝ) < X := by
    obtain ⟨N, hN⟩ := exists_nat_gt (|d| / c)
    refine eventually_atTop.2 ⟨N + 1, fun X hX => ⟨?_, Nat.cast_pos.2 (by omega)⟩⟩
    have hX' : (N : ℝ) + 1 ≤ X := by exact_mod_cast hX
    have : |d| < c * X := by rw [div_lt_iff₀ hc] at hN; nlinarith
    linarith [neg_abs_le d]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [hev] with X ⟨h0, hX⟩
    have := Nat.lt_floor_add_one (c * X + d)
    rw [le_div_iff₀ hX]
    have e : (c + (d - 1) / X) * X = c * X + d - 1 := by field_simp; ring
    linarith
  · filter_upwards [hev] with X ⟨h0, hX⟩
    have := Nat.floor_le h0
    rw [div_le_iff₀ hX]
    have e : (c + d / X) * X = c * X + d := by field_simp
    linarith

/-- Rescaling a counting limit: if `C(N)/N → L`, `f → ∞` and `f(X)/X → c`, then
`C(f(X))/X → L c`. -/
lemma yTendsto_comp_div {C f : ℕ → ℕ} {L c : ℝ}
    (hC : Tendsto (fun N : ℕ => (C N : ℝ) / N) atTop (𝓝 L)) (hf : Tendsto f atTop atTop)
    (hfr : Tendsto (fun X : ℕ => (f X : ℝ) / X) atTop (𝓝 c)) :
    Tendsto (fun X : ℕ => (C (f X) : ℝ) / X) atTop (𝓝 (L * c)) := by
  refine ((hC.comp hf).mul hfr).congr' ?_
  filter_upwards [hf.eventually_ge_atTop 1] with X hX
  have : (f X : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  show (C (f X) : ℝ) / f X * (f X / X) = _
  rw [div_mul_div_cancel₀ this]

/-- `⌊c·X + d⌋₊ → ∞`. -/
lemma yTendsto_floor_linear {c : ℝ} (hc : 0 < c) (d : ℝ) :
    Tendsto (fun X : ℕ => ⌊c * X + d⌋₊) atTop atTop :=
  tendsto_nat_floor_atTop.comp
    ((tendsto_natCast_atTop_atTop.const_mul_atTop hc).atTop_add tendsto_const_nhds)

lemma yPerm_returnCount_eq (X : ℕ) :
    returnCount yPerm {n | n % 2 = 0} {1} X =
      ((Finset.Icc 1 (X / 2)).filter fun k : ℕ =>
        returnMap yPerm {n | n % 2 = 0} (2 * (k : ℤ)) ≤ X).card := by
  classical
  unfold returnCount
  symm
  apply Finset.card_nbij (fun k : ℕ => 2 * (k : ℤ))
  · intro k hk
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq,
      Set.mem_singleton_iff] at hk ⊢
    obtain ⟨⟨h1, h2⟩, hR⟩ := hk
    exact ⟨⟨by omega, by omega⟩, by omega, by omega, hR⟩
  · intro a _ b _ h
    have : (a : ℤ) = b := by simp only at h; omega
    exact_mod_cast this
  · intro s hs
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq,
      Set.mem_singleton_iff] at hs
    obtain ⟨⟨h1, h2⟩, he, -, hR⟩ := hs
    refine ⟨(s / 2).toNat, ?_, by simp only; omega⟩
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [show 2 * (((s / 2).toNat : ℕ) : ℤ) = s by omega]
    exact hR

/-- On word `j`, `|R(2k) − αxʲk| < 2`. -/
lemma yReturn_bound (k : ℕ) (hk : 1 ≤ k) :
    |(returnMap yPerm {n | n % 2 = 0} (2 * (k : ℤ)) : ℝ) -
      alphaY * yRoot ^ (returnTime yPerm {n | n % 2 = 0} (2 * (k : ℤ)) - 1) * k| < 2 := by
  have hS0 : 2 * (k : ℤ) ∈ {n : ℤ | n % 2 = 0} := by simp only [Set.mem_ofPred_eq]; omega
  have hΦ0 : 2 * (k : ℤ) ∉ ({1} : Set ℤ) := by simp only [Set.mem_singleton_iff]; omega
  obtain ⟨h1, hT, -, -, hint⟩ := returnTime_spec hyp_yPerm hS0 (by omega) hΦ0
  set τ := returnTime yPerm {n | n % 2 = 0} (2 * (k : ℤ))
  have hodd : ∀ i : ℕ, 1 ≤ i → i ≤ τ - 1 → (wy alphaY)^[i] (2 * (k : ℤ)) % 2 = 1 := by
    intro i hi1 hi2
    have := hint i hi1 (by omega)
    rw [yPerm_pow_apply, Set.mem_ofPred_eq] at this
    omega
  have hs := yRun_sandwich (show (2 * (k : ℤ)) % 2 = 0 by omega) (τ - 1) hodd
  have hRm : returnMap yPerm {n | n % 2 = 0} (2 * (k : ℤ)) =
      (wy alphaY)^[τ - 1 + 1] (2 * (k : ℤ)) := by
    rw [returnMap, yPerm_pow_apply]; congr 1; omega
  rw [hRm]
  rw [show 2 * (k : ℤ) / 2 = k by omega] at hs
  convert hs using 3
  push_cast
  ring

lemma two_le_alphaY_mul_pow {j : ℕ} (hj : j ≤ 3) : 2 ≤ alphaY * yRoot ^ j := by
  have hx := yRoot_bounds
  have hα := alphaY_bounds
  have hx3 : (1454 : ℝ) / 10000 < yRoot ^ 3 := by
    have : ((52595748 : ℝ) / 10 ^ 8) ^ 3 < yRoot ^ 3 :=
      pow_lt_pow_left₀ hx.1 (by norm_num) (by norm_num)
    norm_num at this ⊢; linarith
  have hxj : yRoot ^ 3 ≤ yRoot ^ j := pow_le_pow_of_le_one (by linarith) (by linarith) hj
  nlinarith

open Classical in
/-- **Return-count density.**  `#{s ≤ X : R(s) ≤ X}/X → Σ_{j ≤ 3} P_j/(αxʲ)`. -/
theorem tendsto_returnCount_yPerm (hW : WeylEquidistributionMulti) :
    Tendsto (fun X : ℕ => (returnCount yPerm {n | n % 2 = 0} {1} X : ℝ) / X) atTop
      (𝓝 (∑ j ∈ Finset.range 4, yVol j * (alphaY * yRoot ^ j)⁻¹)) := by
  set c : ℕ → ℝ := fun j => alphaY * yRoot ^ j
  set Cnt : ℕ → ℕ → ℕ := fun j N =>
    ((Finset.Icc 1 N).filter fun k : ℕ => yPh k ∈ yWord j).card
  set T : ℕ → ℕ → ℕ := fun j X => ((Finset.Icc 1 (X / 2)).filter fun k : ℕ =>
    returnTime yPerm {n | n % 2 = 0} (2 * (k : ℤ)) = j + 1 ∧
      returnMap yPerm {n | n % 2 = 0} (2 * (k : ℤ)) ≤ X).card
  have hspec : ∀ k : ℕ, 1 ≤ k → 1 ≤ returnTime yPerm {n | n % 2 = 0} (2 * (k : ℤ)) ∧
      returnTime yPerm {n | n % 2 = 0} (2 * (k : ℤ)) ≤ 4 := by
    intro k hk
    have hS0 : 2 * (k : ℤ) ∈ {n : ℤ | n % 2 = 0} := by simp only [Set.mem_ofPred_eq]; omega
    have hΦ0 : 2 * (k : ℤ) ∉ ({1} : Set ℤ) := by simp only [Set.mem_singleton_iff]; omega
    obtain ⟨h1, hT, -⟩ := returnTime_spec hyp_yPerm hS0 (by omega) hΦ0
    exact ⟨h1, hT⟩
  have hsum : ∀ X, returnCount yPerm {n | n % 2 = 0} {1} X = ∑ j ∈ Finset.range 4, T j X := by
    intro X
    rw [yPerm_returnCount_eq, Finset.card_eq_sum_card_fiberwise
      (f := fun k : ℕ => returnTime yPerm {n | n % 2 = 0} (2 * (k : ℤ)) - 1) (t := Finset.range 4)]
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp only [T, Finset.filter_filter]
      congr 1
      refine Finset.filter_congr fun k hk => ?_
      have := (hspec k (Finset.mem_Icc.1 hk).1).1
      omega
    · intro k hk
      simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hk
      have := (hspec k hk.1.1).2
      simp only [Finset.coe_range, Set.mem_Iio]
      omega
  have hlo : ∀ j, j ≤ 3 → ∀ X : ℕ, Cnt j ⌊(c j)⁻¹ * X + -2 / c j⌋₊ ≤ T j X := by
    intro j hj X
    apply Finset.card_le_card
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk ⊢
    obtain ⟨⟨hk1, hk2⟩, hw⟩ := hk
    have hcj : 2 ≤ c j := two_le_alphaY_mul_pow hj
    have hkr := (Nat.le_floor_iff' (by omega)).1 hk2
    have hck : c j * k ≤ X - 2 := by
      have := mul_le_mul_of_nonneg_left hkr (by linarith : (0 : ℝ) ≤ c j)
      rw [mul_add, ← mul_assoc, mul_inv_cancel₀ (by linarith), one_mul,
        mul_div_cancel₀ _ (by linarith)] at this
      linarith
    have hrt := (returnTime_yPerm_eq_iff k hk1 hj).2 hw
    have hb := yReturn_bound k hk1
    rw [hrt, Nat.add_sub_cancel] at hb
    have hRX : (returnMap yPerm {n | n % 2 = 0} (2 * (k : ℤ)) : ℝ) < X := by
      linarith [(abs_lt.1 hb).2]
    refine ⟨⟨hk1, ?_⟩, hrt, by exact_mod_cast hRX.le⟩
    have : (2 : ℝ) * k ≤ X := by
      have : (2 : ℝ) * k ≤ c j * k := by
        have : (0 : ℝ) ≤ k := by positivity
        nlinarith
      linarith
    have : 2 * k ≤ X := by exact_mod_cast this
    omega
  have hhi : ∀ j, j ≤ 3 → ∀ X : ℕ, T j X ≤ Cnt j ⌊(c j)⁻¹ * X + 2 / c j⌋₊ := by
    intro j hj X
    apply Finset.card_le_card
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk ⊢
    obtain ⟨⟨hk1, -⟩, hrt, hRX⟩ := hk
    have hcj : 2 ≤ c j := two_le_alphaY_mul_pow hj
    refine ⟨⟨hk1, Nat.le_floor ?_⟩, (returnTime_yPerm_eq_iff k hk1 hj).1 hrt⟩
    have hb := yReturn_bound k hk1
    rw [hrt, Nat.add_sub_cancel] at hb
    have hRX' : (returnMap yPerm {n | n % 2 = 0} (2 * (k : ℤ)) : ℝ) ≤ X := by exact_mod_cast hRX
    have : c j * k < X + 2 := by linarith [(abs_lt.1 hb).1]
    rw [show (c j)⁻¹ * X + 2 / c j = (X + 2) / c j by field_simp, le_div_iff₀ (by linarith)]
    linarith
  have hlimT : ∀ j ∈ Finset.range 4, Tendsto (fun X : ℕ => (T j X : ℝ) / X) atTop
      (𝓝 (yVol j * (alphaY * yRoot ^ j)⁻¹)) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hcj : 2 ≤ c j := two_le_alphaY_mul_pow (by omega)
    have hcpos : 0 < (c j)⁻¹ := inv_pos.2 (by linarith)
    have L1 := yTendsto_comp_div (tendsto_yWordCount hW j)
      (yTendsto_floor_linear hcpos (-2 / c j)) (yTendsto_floor_linear_div hcpos (-2 / c j))
    have L2 := yTendsto_comp_div (tendsto_yWordCount hW j)
      (yTendsto_floor_linear hcpos (2 / c j)) (yTendsto_floor_linear_div hcpos (2 / c j))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le L1 L2 (fun X => ?_) (fun X => ?_)
    · exact div_le_div_of_nonneg_right (Nat.cast_le.2 (hlo j (by omega) X)) (by positivity)
    · exact div_le_div_of_nonneg_right (Nat.cast_le.2 (hhi j (by omega) X)) (by positivity)
  refine (tendsto_finsetSum (Finset.range 4) hlimT).congr fun X => ?_
  simp only [hsum X, Nat.cast_sum, Finset.sum_div]

/-- The closed form: `1/2 − Σ_{j ≤ 3} P_j/(αxʲ) = 3/10 + x/8 + x²/10`. -/
lemma densityY_sum_eq :
    1 / 2 - ∑ j ∈ Finset.range 4, yVol j * (alphaY * yRoot ^ j)⁻¹ = densityY := by
  have hx := yRoot_bounds
  have h3 := yRoot_spec.2.2
  have hx0 : yRoot ≠ 0 := by linarith
  have hp : 1 + yRoot ≠ 0 := by linarith
  have hq : 2 * yRoot - 1 ≠ 0 := by linarith
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, yVol, densityY, alphaY]
  field_simp
  linear_combination 32 * (-5 - 5 * yRoot ^ 2 - 4 * yRoot ^ 3) * h3

end Density

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
  have hR := tendsto_returnCount_yPerm hW
  have hX : ∀ X : ℕ, 1 ≤ X → (minCount yPerm X : ℝ) / X =
      1 / X + ((X / 2 : ℕ) : ℝ) / X - (returnCount yPerm {n | n % 2 = 0} {1} X : ℝ) / X := by
    intro X hX1
    have := minCount_yPerm_add hX1
    rw [← add_div, div_sub_div_same]
    congr 1
    have : (minCount yPerm X : ℝ) =
        1 + (X / 2 : ℕ) - returnCount yPerm {n | n % 2 = 0} {1} X := by
      rw [eq_sub_iff_add_eq]; exact_mod_cast this
    exact this
  have hhalf : Tendsto (fun X : ℕ => ((X / 2 : ℕ) : ℝ) / X) atTop (𝓝 (1 / 2)) := by
    have := yTendsto_floor_linear_div (c := 1 / 2) (by norm_num) 0
    refine this.congr fun X => ?_
    have h := Nat.floor_div_eq_div (K := ℝ) X 2
    push_cast at h
    rw [add_zero, one_div_mul_eq_div, h]
  have hlim := ((tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).add hhalf).sub hR
  rw [zero_add, densityY_sum_eq] at hlim
  exact hlim.congr' (eventually_atTop.2 ⟨1, fun X hX1 => (hX X hX1).symm⟩)

end CollatzMoonshot.WythoffSporadic
