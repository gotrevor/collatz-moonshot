/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.WythoffGeneral

/-!
# The plastic member: a cylinder of 7-cycles

Research note `wythoff-classify`, §0 by-products and §7 (3).  Let `x ≈ 0.5698402910` be the real
root of `x³ − x² + 2x − 1` (`pRoot`; the cubic is strictly increasing, `pRoot_unique`), so
`1/x = x² − x + 2 = ρ²` with `ρ` the plastic number.  Put `β = 2x ≈ 1.13968` and
`α = 2x/(2x − 1) ≈ 8.15920` (`alphaP`, `α³ − 10α² + 16α − 8 = 0`), and let `W = W_α`
(`WythoffGeneral.wy`).  Write `A = α/2 = 2x² − x + 4` (`2x − 1` is a unit of `ℤ[x]`).

**The slope-1 identity** (`pRoot_pow_seven`).  `x⁷ = (2x − 1)²`, i.e. `A² x⁵ = 1`: the word
`E O E O⁴` (two even steps of slope `A`, five odd steps of slope `x`) has composite slope `1`.

**Theorem (7-cycles)** (`wy_alphaP_iterate_seven_eq`).  If `n` is even and the parities of
`W(n), …, W⁶(n)` are `O, E, O, O, O, O`, then `W⁷(n) = n`, for every `n ∈ ℤ`.  So every such `n`
has minimal period exactly `7` (`minimalPeriod_alphaP_of_cyl`; `W(n) ≠ n` by parity and `7` is
prime).  Example: `20 → 81 → 46 → 187 → 107 → 61 → 35 → 20` (`minimalPeriod_alphaP_twenty`,
unconditional).  Measured: `9 427` of the first `10⁵` even `n` lie on the cylinder, all with
`W⁷(n) = n`.  **Infinitely many 7-cycles, unconditionally** (`infinite_minimalPeriod_seven`):
`20 + 2q` stays on the cylinder whenever `‖qA‖, ‖qAx‖ < 1/200` (`twenty_add_two_mul_mem_sevenCyl`,
a translation lemma: all prefix slopes lie in `ℤ + ℤA + ℤAx`), and simultaneous Dirichlet
approximation supplies infinitely many such `q` (`infinite_simultaneous_approx`).  No
equidistribution hypothesis is used.

**Proof: integer labels.**  Write `u_i = Wⁱ(n)`.  In the `ℤ`-basis `1, A, Ax = x² + 2` of
`ℤ[x]`, the slopes of the prefixes are `A²x = −1 + 2A + Ax`, `A²x² = −1 + A + Ax`,
`A²x³ = −1 + A`, `A²x⁴ = A − Ax`, `A²x⁵ = 1`; so the integer approximations of `u_3, …, u_7`
are `−n + 2u_1 + u_2`, `−n + u_1 + u_2`, `−n + u_1`, `u_1 − u_2`, `n`, and the labels
`K_i = u_i − (approximation)` are small.  With the phases `G_1 = u_1 + 1 − An ∈ (0, 1]`,
`G_2 = u_2 + 1 − x(u_1 + 1) ∈ [0, 1)`, put `a = G_1 − 1 ∈ (−1, 0]`, `b = xG_1 + G_2 − 1 ∈ (−1, x)`
and let `h_i ∈ (0, 1]` be the defect of the odd step into `u_i`
(`u_i = x(u_{i−1} + 1) − 1 + h_i`).  Exact algebra (the cubic) gives
`K_{i+1} = x K_i + (x ε_i − ε_{i+1}) + x − 1 + h_{i+1}`, `ε_i = q_i a + r_i b` with `(q_i, r_i)`
the `A`, `Ax` coordinates above, and the cylinder parities fix `K_i`:
* `K_3 = ⌊(A − 1)(⌈z⌉ − 1 − 2ψ₁) + 2 − 2G_1⌋` in the torus coordinates `ψ₀ = {kA}`,
  `ψ₁ = {kAx}` (`n = 2k`, `u_1` odd iff `ψ₀ ≥ 1/2`, `z = 2ψ₁ + xG_1`, `u_2` even iff `⌈z⌉` is
  odd); on `⌈z⌉ = 1` it lies in `(−1.33, 2)`, on `⌈z⌉ = 3` in `(0, 2)`; `u_3` odd makes `K_3` odd,
  so `K_3 = ±1` (`wy_alphaP_iterate_three_sub_mem`).
* `K_4 = xK_3 + (2x − 1)a + (x − 1)b + x − 1 + h_4 ∈ (−0.25, 1.57)` (`K_3 = 1`) or
  `(−1.39, 0.43)` (`K_3 = −1`); `u_4` odd makes `K_4` even, so `K_4 = 0`
  (`wy_alphaP_iterate_four_eq`).
* `K_5 = 0` without a parity hypothesis: on `E O O` (at `u_2`) Theorem N (2) for
  `P = t³ − t² + 2t − 1` has `Φ₀ = −(1 − x)(x G + G′) ∈ (−1, 0)`, so `u_5 = u_4 − u_2`
  (`wy_alphaP_eoo`); in particular `u_5` is odd.
* `K_6 = (x − 1)a + b + x − 1 + h_6 ∈ (−1.43, 1.57)`; `u_6` odd makes `K_6` even, so `K_6 = 0`.
* `K_7 = x(1 − x)G_1 − xG_2 + x − 1 + h_7 ∈ (−1, 1)` (as `G_1 > 0`, `G_2 < 1`, `h_7 ≤ 1`), so
  `K_7 = 0`: `W⁷(n) = n`.

Truth checks: `tmp/drafter-classify/check.py` (certified 400-bit interval arithmetic; every
label value on `[−2·10⁵, 2·10⁵]`; teeth: the other slope-1 cylinder `E O³ E O²` has
`W⁷(n) = n − 1` throughout, and the perturbed cubic `x³ − x² + 2x − 1.001` breaks the cycle).
-/

namespace CollatzMoonshot.WythoffSeven

open CollatzMoonshot.WythoffGeneral
open Polynomial

/-! ## The root `x` and the parameters -/

open Classical in
/-- The real root `x ∈ (1/2, 3/5)` of `x³ − x² + 2x − 1` (`pRoot_spec`). -/
noncomputable def pRoot : ℝ :=
  if h : ∃ x : ℝ, 1 / 2 < x ∧ x < 3 / 5 ∧ x ^ 3 - x ^ 2 + 2 * x - 1 = 0 then h.choose else 0

/-- `α = 2x/(2x − 1) ≈ 8.15920`. -/
noncomputable def alphaP : ℝ :=
  2 * pRoot / (2 * pRoot - 1)

/-- `β = 2x = α/(α − 1) ≈ 1.13968`. -/
noncomputable def betaP : ℝ :=
  2 * pRoot

/-- The cubic changes sign on `[1/2, 3/5]` (IVT). -/
theorem exists_pRoot : ∃ x : ℝ, 1 / 2 < x ∧ x < 3 / 5 ∧ x ^ 3 - x ^ 2 + 2 * x - 1 = 0 := by
  have hc : ContinuousOn (fun x : ℝ => x ^ 3 - x ^ 2 + 2 * x - 1) (Set.Icc (1 / 2) (3 / 5)) := by
    fun_prop
  obtain ⟨x, ⟨h1, h2⟩, hx⟩ := intermediate_value_Icc (by norm_num) hc
    (show (0 : ℝ) ∈ Set.Icc _ _ by constructor <;> norm_num)
  simp only at hx
  refine ⟨x, lt_of_le_of_ne h1 ?_, lt_of_le_of_ne h2 ?_, hx⟩ <;> rintro rfl <;> norm_num at hx

/-- `F(x) = x³ − x² + 2x − 1` is strictly increasing
(`F(b) − F(a) = (b − a)(a² + ab + b² − a − b + 2)`). -/
theorem pCubic_lt {a b : ℝ} (h : a < b) :
    a ^ 3 - a ^ 2 + 2 * a - 1 < b ^ 3 - b ^ 2 + 2 * b - 1 := by
  have : 0 < b ^ 2 + a * b + a ^ 2 - b - a + 2 := by
    nlinarith [sq_nonneg (a + b - 1), sq_nonneg (a - b)]
  nlinarith [mul_pos (sub_pos.2 h) this]

/-- **(proved).**  The root exists (`exists_pRoot`, `dif_pos`, `Classical.choose_spec`). -/
theorem pRoot_spec :
    1 / 2 < pRoot ∧ pRoot < 3 / 5 ∧ pRoot ^ 3 - pRoot ^ 2 + 2 * pRoot - 1 = 0 := by
  unfold pRoot
  rw [dif_pos exists_pRoot]
  exact exists_pRoot.choose_spec

/-- **(proved).**  `x³ − x² + 2x − 1` has exactly one real root (`pCubic_lt`). -/
theorem pRoot_unique {y : ℝ} (hy : y ^ 3 - y ^ 2 + 2 * y - 1 = 0) : y = pRoot := by
  have h := pRoot_spec.2.2
  rcases lt_trichotomy y pRoot with hl | he | hl
  · linarith [pCubic_lt hl]
  · exact he
  · linarith [pCubic_lt hl]

/-- **(proved).**  `0.56984029 < x < 0.56984030` (`F` increasing, `norm_num` at the
endpoints). -/
theorem pRoot_bounds : (56984029 : ℝ) / 10 ^ 8 < pRoot ∧ pRoot < 56984030 / 10 ^ 8 := by
  have h := pRoot_spec.2.2
  constructor
  · by_contra hc
    rcases (not_lt.1 hc).lt_or_eq with hl | he
    · have := pCubic_lt hl; norm_num at this; linarith
    · rw [he] at h; norm_num at h
  · by_contra hc
    rcases (not_lt.1 hc).lt_or_eq with hl | he
    · have := pCubic_lt hl; norm_num at this; linarith
    · rw [← he] at h; norm_num at h

/-- **(proved).**  `x` is irrational: a rational root of the monic integer cubic is an
integer, and `F(z) ≤ −1` for `z ≤ 0`, `F(z) ≥ 1` for `z ≥ 1` (`isInteger_of_is_root_of_monic`,
as `WythoffSporadic.irrational_yRoot`). -/
theorem pCubic_ne_zero_rat (q : ℚ) : q ^ 3 - q ^ 2 + 2 * q - 1 ≠ 0 := by
  intro h
  have hmon : (X ^ 3 - X ^ 2 + C 2 * X - C 1 : ℤ[X]).Monic := by monicity!
  have hr : aeval q (X ^ 3 - X ^ 2 + C 2 * X - C 1 : ℤ[X]) = 0 := by
    simp only [map_sub, map_add, map_pow, map_mul, aeval_X, aeval_C]
    simpa using h
  obtain ⟨z, hz⟩ := isInteger_of_is_root_of_monic hmon hr
  have hz' : (z : ℚ) = q := hz
  subst hz'
  have hz3 : z ^ 3 - z ^ 2 + 2 * z - 1 = 0 := by exact_mod_cast h
  rcases le_or_gt z 0 with h0 | h0
  · nlinarith [sq_nonneg z, sq_nonneg (z - 1)]
  · nlinarith [sq_nonneg z, sq_nonneg (z - 1)]

theorem natDegree_pCubic : (X ^ 3 - X ^ 2 + C 2 * X - C 1 : ℚ[X]).natDegree = 3 := by
  compute_degree!

theorem irreducible_pCubic : Irreducible (X ^ 3 - X ^ 2 + C 2 * X - C 1 : ℚ[X]) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [natDegree_pCubic]; decide
  · intro q hq
    apply pCubic_ne_zero_rat q
    simpa using hq

theorem irrational_pRoot : Irrational pRoot := by
  rintro ⟨q, hq⟩
  apply pCubic_ne_zero_rat q
  have h := pRoot_spec.2.2
  rw [← hq] at h
  exact_mod_cast h

/-- **(proved).**  `deg x = 3`: `1, x, x²` are `ℚ`-independent (irreducible cubic, no
rational root; `minpoly.eq_of_irreducible_of_monic`, `linearIndependent_pow`, as
`WythoffSporadic.linearIndependent_yRoot`). -/
theorem linearIndependent_pRoot : LinearIndependent ℚ fun i : Fin 3 => pRoot ^ (i : ℕ) := by
  have hmin : (X ^ 3 - X ^ 2 + C 2 * X - C 1 : ℚ[X]) = minpoly ℚ pRoot := by
    apply minpoly.eq_of_irreducible_of_monic irreducible_pCubic
    · simp only [map_sub, map_add, map_pow, map_mul, aeval_X, aeval_C]
      simpa using pRoot_spec.2.2
    · monicity!
  have h := linearIndependent_pow (K := ℚ) pRoot
  rw [← hmin, natDegree_pCubic] at h
  exact h

/-- **(proved from `pRoot_spec`).**  The slope-1 identity `x⁷ = (2x − 1)²`:
`x⁷ − (2x − 1)² = (x⁴ + x³ − x² − 2x + 1)(x³ − x² + 2x − 1)`. -/
theorem pRoot_pow_seven : pRoot ^ 7 = (2 * pRoot - 1) ^ 2 := by
  linear_combination (pRoot ^ 4 + pRoot ^ 3 - pRoot ^ 2 - 2 * pRoot + 1) * pRoot_spec.2.2

/-- **(proved from `pRoot_spec`).**  `1/x = x² − x + 2` (`= ρ²`; `x` is a unit). -/
theorem pRoot_mul_eq_one : pRoot * (pRoot ^ 2 - pRoot + 2) = 1 := by
  linear_combination pRoot_spec.2.2

/-- **(proved).**  `β = α/(α − 1)` (`field_simp`; `2x − 1 > 0`). -/
theorem alphaP_div_sub_one : alphaP / (alphaP - 1) = betaP := by
  have h := pRoot_spec
  have hp : 0 < 2 * pRoot - 1 := by linarith
  unfold alphaP betaP
  field_simp
  ring

/-- **(proved).**  `A = α/2 = 2x² − x + 4` (`(2x² − x + 4)(2x − 1) − x = 4F(x)`). -/
theorem half_alphaP_eq : alphaP / 2 = 2 * pRoot ^ 2 - pRoot + 4 := by
  have h := pRoot_spec
  have hp : 2 * pRoot - 1 ≠ 0 := by linarith
  unfold alphaP
  field_simp
  linear_combination (-4 : ℝ) * h.2.2

/-- **(proved).**  `α³ − 10α² + 16α − 8 = 0` (after clearing `(2x − 1)³` the identity is
`−8` times the cubic). -/
theorem alphaP_cubic : alphaP ^ 3 - 10 * alphaP ^ 2 + 16 * alphaP - 8 = 0 := by
  have h := pRoot_spec
  have hp : 2 * pRoot - 1 ≠ 0 := by linarith
  unfold alphaP
  field_simp
  linear_combination (-8 : ℝ) * h.2.2

/-- **(proved).**  `8.159 < α < 8.1593` (`α = 1 + 1/(2x − 1)`, `pRoot_bounds`). -/
theorem alphaP_mem : 8159 / 1000 < alphaP ∧ alphaP < 81593 / 10000 := by
  have h := pRoot_bounds
  have hp : 0 < 2 * pRoot - 1 := by linarith
  unfold alphaP
  constructor
  · rw [lt_div_iff₀ hp]; linarith
  · rw [div_lt_iff₀ hp]; linarith

/-- **(proved).**  `α` is irrational (`α = 1 + 1/(2x − 1)`, `irrational_pRoot`). -/
theorem irrational_alphaP : Irrational alphaP := by
  have hp : 2 * pRoot - 1 ≠ 0 := by linarith [pRoot_spec.1]
  have h : alphaP = 1 + (2 * pRoot - 1)⁻¹ := by
    unfold alphaP; field_simp; ring
  rw [h]
  have h2 : Irrational (2 * pRoot - 1) := by
    have := irrational_pRoot.ratCast_mul (q := 2) (by norm_num)
    simpa using this.sub_ratCast (q := 1)
  simpa using (h2.inv).ratCast_add (q := 1)

/-! ## The labels along `E O E O⁴` -/

section Labels

local notation "W" => wy alphaP

/-- **(proved).**  The even step: `W(m) + 1 = Am + g` with `g ∈ (0, 1]` (`A = α/2`). -/
theorem evenStep {m : ℤ} (hm : m % 2 = 0) : ∃ g : ℝ, 0 < g ∧ g ≤ 1 ∧
    ((W m : ℤ) : ℝ) = (2 * pRoot ^ 2 - pRoot + 4) * m + g - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k := ⟨m / 2, by omega⟩
  rw [wy_two_mul, ← half_alphaP_eq]
  refine ⟨(⌊(k : ℝ) * alphaP⌋ : ℝ) + 1 - k * alphaP, ?_, ?_, ?_⟩
  · linarith [Int.lt_floor_add_one ((k : ℝ) * alphaP)]
  · linarith [Int.floor_le ((k : ℝ) * alphaP)]
  · push_cast; ring

/-- **(proved).**  The odd step: `W(m) + 1 = x(m + 1) + g` with `g ∈ [0, 1)` (`β = 2x`). -/
theorem oddStep {m : ℤ} (hm : m % 2 = 1) : ∃ g : ℝ, 0 ≤ g ∧ g < 1 ∧
    ((W m : ℤ) : ℝ) = pRoot * (m + 1) + g - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k - 1 := ⟨(m + 1) / 2, by omega⟩
  rw [wy_two_mul_sub_one, alphaP_div_sub_one, betaP]
  refine ⟨(⌈(k : ℝ) * (2 * pRoot)⌉ : ℝ) - k * (2 * pRoot), ?_, ?_, ?_⟩
  · linarith [Int.le_ceil ((k : ℝ) * (2 * pRoot))]
  · linarith [Int.ceil_lt_add_one ((k : ℝ) * (2 * pRoot))]
  · push_cast; ring

/-- **(proved; Theorem N (2) instance).**  On `E O O`: if `v` is even and `W(v), W²(v)`
are odd, then `W³(v) = W²(v) − v` (so `W³(v)` is odd).  Paper proof:
`WythoffAutomaton.first_step_eq_ceil` with `P = t³ − t² + 2t − 1`: `q = (2 − x + x², x − 1, 1)`,
`q_0 + 2a_0 = x² − x`, `Φ₀ = −(1 − x)(x G_E + G) ∈ (−(1 − x²), 0)` since `G_E ∈ (0, 1]`,
`G ∈ [0, 1)`; so the integer `w_3 − w_2 + v = W³ v − W² v + v` is `⌈Φ₀⌉ = 0`.  Directly: with
`W v + 1 = Av + G_E`, `W² v + 1 = x(W v + 1) + G′`, `W³ v + 1 = x(W² v + 1) + G″` and the cubic,
`W³ v − W² v + v = Φ₀ + G″ ∈ (−1, 1)`. -/
theorem wy_alphaP_eoo {v : ℤ} (hv : v % 2 = 0) (h₁ : W v % 2 = 1) (h₂ : W^[2] v % 2 = 1) :
    W^[3] v = W^[2] v - v := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply] at h₂ ⊢
  obtain ⟨g1, a1, b1, e1⟩ := evenStep hv
  obtain ⟨g2, a2, b2, e2⟩ := oddStep h₁
  obtain ⟨g3, a3, b3, e3⟩ := oddStep h₂
  obtain ⟨hx1, hx2⟩ := pRoot_bounds
  have hc := pRoot_spec.2.2
  set x := pRoot
  have hK : ((W (W (W v)) - W (W v) + v : ℤ) : ℝ) = (x ^ 2 - x) * g1 + (x - 1) * g2 + g3 := by
    push_cast
    rw [e3, e2, e1]
    linear_combination (2 * x - 1) * (v : ℝ) * hc
  have q1 : x ^ 2 - x < 0 := by nlinarith
  have p1 : x ^ 2 - x ≤ (x ^ 2 - x) * g1 := by nlinarith
  have p2 : (x ^ 2 - x) * g1 < 0 := mul_neg_of_neg_of_pos q1 a1
  have p3 : x - 1 < (x - 1) * g2 := by nlinarith
  have p4 : (x - 1) * g2 ≤ 0 := by nlinarith
  have l1 : -1 < W (W (W v)) - W (W v) + v := by
    have : ((-1 : ℤ) : ℝ) < ((W (W (W v)) - W (W v) + v : ℤ) : ℝ) := by
      rw [hK]; push_cast; nlinarith
    exact_mod_cast this
  have l2 : W (W (W v)) - W (W v) + v < 1 := by
    have : ((W (W (W v)) - W (W v) + v : ℤ) : ℝ) < ((1 : ℤ) : ℝ) := by
      rw [hK]; push_cast; nlinarith
    exact_mod_cast this
  omega

/-- **(proved).**  On `E O E O`: `W³(n) − (−n + 2W(n) + W²(n)) ∈ {−1, 1}`.  Lean proof (no torus
coordinates needed): with the phases `g_1 ∈ (0, 1]`, `g_2 ∈ [0, 1)`, `g_3 ∈ (0, 1]` of the steps
into `u_1, u_2, u_3`, the cubic gives exactly
`K_3 = (x² − x)g_1 + (A − 1)(g_2 − 1) + g_3 + 1 ∈ (−x² − 2, 2) ⊂ (−3, 2)`, and `K_3` is odd. -/
theorem wy_alphaP_iterate_three_sub_mem {n : ℤ} (hn : n % 2 = 0) (h₁ : W n % 2 = 1)
    (h₂ : W^[2] n % 2 = 0) (h₃ : W^[3] n % 2 = 1) :
    W^[3] n - (-n + 2 * W n + W^[2] n) ∈ ({-1, 1} : Set ℤ) := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply] at h₂ h₃ ⊢
  obtain ⟨g1, a1, b1, e1⟩ := evenStep hn
  obtain ⟨g2, a2, b2, e2⟩ := oddStep h₁
  obtain ⟨g3, a3, b3, e3⟩ := evenStep h₂
  obtain ⟨hx1, hx2⟩ := pRoot_bounds
  have hc := pRoot_spec.2.2
  set x := pRoot
  have hK : ((W (W (W n)) - (-n + 2 * W n + W (W n)) : ℤ) : ℝ) =
      (x ^ 2 - x) * g1 + (2 * x ^ 2 - x + 3) * (g2 - 1) + g3 + 1 := by
    push_cast
    rw [e3, e2, e1]
    linear_combination (2 * g1 + 7 * n + 4 * n * x ^ 2) * hc
  have q1 : x ^ 2 - x < 0 := by nlinarith
  have p1 : x ^ 2 - x ≤ (x ^ 2 - x) * g1 := by nlinarith
  have p2 : (x ^ 2 - x) * g1 < 0 := mul_neg_of_neg_of_pos q1 a1
  have p3 : -(2 * x ^ 2 - x + 3) ≤ (2 * x ^ 2 - x + 3) * (g2 - 1) := by nlinarith
  have p4 : (2 * x ^ 2 - x + 3) * (g2 - 1) < 0 := by nlinarith
  have l1 : -3 < W (W (W n)) - (-n + 2 * W n + W (W n)) := by
    have : ((-3 : ℤ) : ℝ) < ((W (W (W n)) - (-n + 2 * W n + W (W n)) : ℤ) : ℝ) := by
      rw [hK]; push_cast; nlinarith
    exact_mod_cast this
  have l2 : W (W (W n)) - (-n + 2 * W n + W (W n)) < 2 := by
    have : ((W (W (W n)) - (-n + 2 * W n + W (W n)) : ℤ) : ℝ) < ((2 : ℤ) : ℝ) := by
      rw [hK]; push_cast; nlinarith
    exact_mod_cast this
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-- **(proved).**  On `E O E O O`: `W⁴(n) = −n + W(n) + W²(n)`.  Lean proof: exactly
`K_4 = (x² − x)g_1 + (x² + 1)g_2 + xg_3 + g_4 − x² − 1 ∈ (−1 − x, 1 + x)`, and `K_4` is even
(the value of `K_3` is not needed). -/
theorem wy_alphaP_iterate_four_eq {n : ℤ} (hn : n % 2 = 0) (h₁ : W n % 2 = 1)
    (h₂ : W^[2] n % 2 = 0) (h₃ : W^[3] n % 2 = 1) (h₄ : W^[4] n % 2 = 1) :
    W^[4] n = -n + W n + W^[2] n := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply] at h₂ h₃ h₄ ⊢
  obtain ⟨g1, a1, b1, e1⟩ := evenStep hn
  obtain ⟨g2, a2, b2, e2⟩ := oddStep h₁
  obtain ⟨g3, a3, b3, e3⟩ := evenStep h₂
  obtain ⟨g4, a4, b4, e4⟩ := oddStep h₃
  obtain ⟨hx1, hx2⟩ := pRoot_bounds
  have hc := pRoot_spec.2.2
  set x := pRoot
  have hK : ((W (W (W (W n))) + n - W n - W (W n) : ℤ) : ℝ) =
      (x ^ 2 - x) * g1 + (x ^ 2 + 1) * g2 + x * g3 + g4 - x ^ 2 - 1 := by
    push_cast
    rw [e4, e3, e2, e1]
    linear_combination (-2 + g1 + 2 * g1 * x + 2 * g2 + 3 * n + 9 * n * x + 4 * n * x ^ 3) * hc
  have q1 : x ^ 2 - x < 0 := by nlinarith
  have p1 : x ^ 2 - x ≤ (x ^ 2 - x) * g1 := by nlinarith
  have p2 : (x ^ 2 - x) * g1 < 0 := mul_neg_of_neg_of_pos q1 a1
  have p3 : 0 ≤ (x ^ 2 + 1) * g2 := by positivity
  have p4 : (x ^ 2 + 1) * g2 < x ^ 2 + 1 := by nlinarith
  have p5 : 0 < x * g3 := by nlinarith
  have p6 : x * g3 ≤ x := by nlinarith
  have l1 : -2 < W (W (W (W n))) + n - W n - W (W n) := by
    have : ((-2 : ℤ) : ℝ) < ((W (W (W (W n))) + n - W n - W (W n) : ℤ) : ℝ) := by
      rw [hK]; push_cast; linarith
    exact_mod_cast this
  have l2 : W (W (W (W n))) + n - W n - W (W n) < 2 := by
    have : ((W (W (W (W n))) + n - W n - W (W n) : ℤ) : ℝ) < ((2 : ℤ) : ℝ) := by
      rw [hK]; push_cast; linarith
    exact_mod_cast this
  omega

/-- **(proved).**  On `E O E O O`: `W⁵(n) = −n + W(n)`, odd.  Paper proof:
`wy_alphaP_eoo` at `v = W²(n)` and `wy_alphaP_iterate_four_eq`. -/
theorem wy_alphaP_iterate_five_eq {n : ℤ} (hn : n % 2 = 0) (h₁ : W n % 2 = 1)
    (h₂ : W^[2] n % 2 = 0) (h₃ : W^[3] n % 2 = 1) (h₄ : W^[4] n % 2 = 1) :
    W^[5] n = -n + W n := by
  have h4 := wy_alphaP_iterate_four_eq hn h₁ h₂ h₃ h₄
  have h3' : W (W^[2] n) % 2 = 1 := by
    rw [← Function.iterate_succ_apply' (f := W)]; exact h₃
  have h4' : W^[2] (W^[2] n) % 2 = 1 := by
    rw [← Function.iterate_add_apply]; exact h₄
  have e := wy_alphaP_eoo h₂ h3' h4'
  rw [← Function.iterate_add_apply, ← Function.iterate_add_apply] at e
  rw [e, h4]; ring

/-- **(proved).**  On `E O E O O O O`: `W⁶(n) = W(n) − W²(n)`.  Lean proof: exactly
`K_6 = (2x − 1)g_1 + g_2 + g_6 − 1 ∈ (−1, 2x)`, and `K_6` is even. -/
theorem wy_alphaP_iterate_six_eq {n : ℤ} (hn : n % 2 = 0) (h₁ : W n % 2 = 1)
    (h₂ : W^[2] n % 2 = 0) (h₃ : W^[3] n % 2 = 1) (h₄ : W^[4] n % 2 = 1)
    (h₆ : W^[6] n % 2 = 1) :
    W^[6] n = W n - W^[2] n := by
  have h5 := wy_alphaP_iterate_five_eq hn h₁ h₂ h₃ h₄
  rw [Function.iterate_succ_apply', h5] at h₆ ⊢
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply] at h₂ ⊢
  have h5o : (-n + W n) % 2 = 1 := by omega
  obtain ⟨g1, a1, b1, e1⟩ := evenStep hn
  obtain ⟨g2, a2, b2, e2⟩ := oddStep h₁
  obtain ⟨g6, a6, b6, e6⟩ := oddStep h5o
  obtain ⟨hx1, hx2⟩ := pRoot_bounds
  have hc := pRoot_spec.2.2
  set x := pRoot
  have hK : ((W (-n + W n) - W n + W (W n) : ℤ) : ℝ) = (2 * x - 1) * g1 + g2 + g6 - 1 := by
    push_cast
    rw [e6, e2]; push_cast; rw [e1]
    linear_combination (4 * n) * hc
  have p1 : 0 < (2 * x - 1) * g1 := by nlinarith
  have p2 : (2 * x - 1) * g1 ≤ 2 * x - 1 := by nlinarith
  have l1 : -1 < W (-n + W n) - W n + W (W n) := by
    have : ((-1 : ℤ) : ℝ) < ((W (-n + W n) - W n + W (W n) : ℤ) : ℝ) := by
      rw [hK]; push_cast; linarith
    exact_mod_cast this
  have l2 : W (-n + W n) - W n + W (W n) < 2 := by
    have : ((W (-n + W n) - W n + W (W n) : ℤ) : ℝ) < ((2 : ℤ) : ℝ) := by
      rw [hK]; push_cast; linarith
    exact_mod_cast this
  omega

/-- **(proved; the 7-cycle identity).**  If `n` is even and `W(n), …, W⁶(n)` have parities
`O, E, O, O, O, O`, then `W⁷(n) = n`; for every `n ∈ ℤ`.  Paper proof: module docstring
(`K_7 = x(1 − x)G_1 − xG_2 + x − 1 + h_7 ∈ (−1, 2x − x²)` given `K_6 = 0`).  The hypothesis on
`W⁵(n)` is automatic (`wy_alphaP_iterate_five_eq`); it is kept to state the cylinder. -/
theorem wy_alphaP_iterate_seven_eq {n : ℤ} (hn : n % 2 = 0) (h₁ : W n % 2 = 1)
    (h₂ : W^[2] n % 2 = 0) (h₃ : W^[3] n % 2 = 1) (h₄ : W^[4] n % 2 = 1)
    (h₅ : W^[5] n % 2 = 1) (h₆ : W^[6] n % 2 = 1) :
    W^[7] n = n := by
  have _ := h₅  -- automatic (`wy_alphaP_iterate_five_eq`); kept to state the cylinder
  have h6 := wy_alphaP_iterate_six_eq hn h₁ h₂ h₃ h₄ h₆
  rw [h6] at h₆
  rw [Function.iterate_succ_apply', h6]
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply] at h₆ ⊢
  obtain ⟨g1, a1, b1, e1⟩ := evenStep hn
  obtain ⟨g2, a2, b2, e2⟩ := oddStep h₁
  obtain ⟨g7, a7, b7, e7⟩ := oddStep h₆
  obtain ⟨hx1, hx2⟩ := pRoot_bounds
  have hc := pRoot_spec.2.2
  set x := pRoot
  have hK : ((W (W n - W (W n)) - n : ℤ) : ℝ) = x * (1 - x) * g1 - x * g2 + g7 + x - 1 := by
    push_cast
    rw [e7]; push_cast; rw [e2, e1]
    linear_combination (n - 2 * n * x) * hc
  have p1 : 0 < x * (1 - x) * g1 := by
    have : 0 < x * (1 - x) := by nlinarith
    positivity
  have p2 : x * (1 - x) * g1 ≤ x * (1 - x) := by nlinarith
  have p3 : x * g2 < x := by nlinarith
  have p4 : 0 ≤ x * g2 := by nlinarith
  have l1 : -1 < W (W n - W (W n)) - n := by
    have : ((-1 : ℤ) : ℝ) < ((W (W n - W (W n)) - n : ℤ) : ℝ) := by
      rw [hK]; push_cast; nlinarith
    exact_mod_cast this
  have l2 : W (W n - W (W n)) - n < 1 := by
    have : ((W (W n - W (W n)) - n : ℤ) : ℝ) < ((1 : ℤ) : ℝ) := by
      rw [hK]; push_cast; nlinarith
    exact_mod_cast this
  omega

end Labels

/-! ## 7-cycles -/

/-- The cylinder `E O E O O O O` of `W_α`. -/
def sevenCyl : Set ℤ :=
  {n | n % 2 = 0 ∧ wy alphaP n % 2 = 1 ∧ (wy alphaP)^[2] n % 2 = 0 ∧
    ∀ i : ℕ, 3 ≤ i → i ≤ 6 → (wy alphaP)^[i] n % 2 = 1}

/-- **(proved).**  Every point of the cylinder has minimal period exactly `7`.  Paper
proof: `wy_alphaP_iterate_seven_eq` gives `IsPeriodicPt W 7 n`, so the minimal period divides
`7` (`Function.IsPeriodicPt.minimalPeriod_dvd`); it is not `1` since `W(n)` is odd and `n` even;
`Nat.Prime 7`. -/
theorem minimalPeriod_alphaP_of_cyl {n : ℤ} (hn : n ∈ sevenCyl) :
    Function.minimalPeriod (wy alphaP) n = 7 := by
  obtain ⟨h0, h1, h2, h⟩ := hn
  have hp : Function.IsPeriodicPt (wy alphaP) 7 n :=
    wy_alphaP_iterate_seven_eq h0 h1 h2 (h 3 le_rfl (by norm_num)) (h 4 (by norm_num) (by norm_num))
      (h 5 (by norm_num) (by norm_num)) (h 6 (by norm_num) le_rfl)
  rcases (Nat.prime_seven.eq_one_or_self_of_dvd _ hp.minimalPeriod_dvd) with h7 | h7
  · rw [Function.minimalPeriod_eq_one_iff_isFixedPt] at h7
    have : wy alphaP n = n := h7
    omega
  · exact h7

/-- **(proved).**  Evaluating `W` on an even point from a floor bracket. -/
theorem evenEval {u w : ℤ} (hu : u % 2 = 0) (h1 : (w : ℝ) ≤ alphaP / 2 * u)
    (h2 : alphaP / 2 * u < w + 1) : wy alphaP u = w := by
  obtain ⟨k, rfl⟩ : ∃ k, u = 2 * k := ⟨u / 2, by omega⟩
  rw [wy_two_mul, Int.floor_eq_iff]
  push_cast at h1 h2
  constructor <;> linarith

/-- **(proved).**  Evaluating `W` on an odd point from a ceiling bracket
(`W(u) + 1 = ⌈x(u + 1)⌉`). -/
theorem oddEval {u w : ℤ} (hu : u % 2 = 1) (h1 : (w : ℝ) < pRoot * (u + 1))
    (h2 : pRoot * (u + 1) ≤ w + 1) : wy alphaP u = w := by
  obtain ⟨k, rfl⟩ : ∃ k, u = 2 * k - 1 := ⟨(u + 1) / 2, by omega⟩
  rw [wy_two_mul_sub_one, alphaP_div_sub_one, betaP]
  have : ⌈(k : ℝ) * (2 * pRoot)⌉ = w + 1 := by
    rw [Int.ceil_eq_iff]; push_cast at h1 h2 ⊢; constructor <;> linarith
  omega

/-- **(proved; unconditional example).**  `20 → 81 → 46 → 187 → 107 → 61 → 35 → 20`.
Paper proof: `20 ∈ sevenCyl` by evaluating the seven floors with `alphaP_mem` (`⌊10α⌋ = 81`,
`⌈41β⌉ − 1 = 46`, `⌊23α⌋ = 187`, `⌈94β⌉ − 1 = 107`, `⌈54β⌉ − 1 = 61`, `⌈31β⌉ − 1 = 35`; `β`
from `alphaP_div_sub_one` and `pRoot_bounds`); `minimalPeriod_alphaP_of_cyl`. -/
theorem minimalPeriod_alphaP_twenty : Function.minimalPeriod (wy alphaP) 20 = 7 := by
  obtain ⟨hx1, hx2⟩ := pRoot_bounds
  obtain ⟨hα1, hα2⟩ := alphaP_mem
  have s1 : wy alphaP 20 = 81 := evenEval (by norm_num) (by push_cast; linarith)
    (by push_cast; linarith)
  have s2 : wy alphaP 81 = 46 := oddEval (by norm_num) (by push_cast; linarith)
    (by push_cast; linarith)
  have s3 : wy alphaP 46 = 187 := evenEval (by norm_num) (by push_cast; linarith)
    (by push_cast; linarith)
  have s4 : wy alphaP 187 = 107 := oddEval (by norm_num) (by push_cast; linarith)
    (by push_cast; linarith)
  have s5 : wy alphaP 107 = 61 := oddEval (by norm_num) (by push_cast; linarith)
    (by push_cast; linarith)
  have s6 : wy alphaP 61 = 35 := oddEval (by norm_num) (by push_cast; linarith)
    (by push_cast; linarith)
  refine minimalPeriod_alphaP_of_cyl ⟨by norm_num, by rw [s1]; norm_num, ?_, ?_⟩
  · simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, s1, s2]; norm_num
  · intro i hi3 hi6
    interval_cases i <;>
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, s1, s2, s3, s4, s5,
        s6] <;> norm_num

/-- **(proved).**  Two points of `[0, ∞)` in the same cell of side `1/Q` are `1/Q`-close. -/
theorem abs_sub_le_of_floor_eq {Q : ℕ} (hQ : 0 < Q) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ⌊(Q : ℝ) * a⌋₊ = ⌊(Q : ℝ) * b⌋₊) : |a - b| ≤ 1 / Q := by
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have h1 := Nat.floor_le (mul_nonneg hQ'.le ha)
  have h2 := Nat.lt_floor_add_one ((Q : ℝ) * a)
  have h3 := Nat.floor_le (mul_nonneg hQ'.le hb)
  have h4 := Nat.lt_floor_add_one ((Q : ℝ) * b)
  rw [h] at h1 h2
  have : |(Q : ℝ) * a - Q * b| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  rw [← mul_sub, abs_mul, abs_of_pos hQ'] at this
  rw [le_div_iff₀ hQ', mul_comm]; exact this

/-- **(proved; simultaneous Dirichlet approximation).**  For reals `θ₁, θ₂` and `Q ≥ 1`
there is `1 ≤ q ≤ Q²` with `‖qθ₁‖, ‖qθ₂‖ ≤ 1/Q`.  Paper proof: pigeonhole on the `Q² + 1`
points `({qθ₁}, {qθ₂})`, `0 ≤ q ≤ Q²`, in the `Q²` boxes of side `1/Q`
(`Finset.exists_ne_map_eq_of_card_lt_of_maps_to`); subtract the two indices. -/
theorem exists_simultaneous_approx (θ₁ θ₂ : ℝ) {Q : ℕ} (hQ : 1 ≤ Q) :
    ∃ q : ℤ, 1 ≤ q ∧ q ≤ (Q : ℤ) ^ 2 ∧ ∃ m₁ m₂ : ℤ,
      |q * θ₁ - m₁| ≤ 1 / Q ∧ |q * θ₂ - m₂| ≤ 1 / Q := by
  let f : ℕ → ℕ × ℕ := fun k =>
    (⌊(Q : ℝ) * Int.fract ((k : ℝ) * θ₁)⌋₊, ⌊(Q : ℝ) * Int.fract ((k : ℝ) * θ₂)⌋₊)
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hmaps : Set.MapsTo f (Finset.range (Q ^ 2 + 1) : Set ℕ)
      ((Finset.range Q ×ˢ Finset.range Q : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
    intro k _
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    constructor <;> rw [Nat.floor_lt (mul_nonneg hQ'.le (Int.fract_nonneg _))] <;>
      nlinarith [Int.fract_lt_one ((k : ℝ) * θ₁), Int.fract_lt_one ((k : ℝ) * θ₂)]
  have hcard : (Finset.range Q ×ˢ Finset.range Q).card < (Finset.range (Q ^ 2 + 1)).card := by
    simp [Finset.card_product]; nlinarith
  -- the core: from `a < b` with `f a = f b`
  have key : ∀ a b : ℕ, a < b → b ≤ Q ^ 2 → f a = f b → ∃ q : ℤ, 1 ≤ q ∧ q ≤ (Q : ℤ) ^ 2 ∧
      ∃ m₁ m₂ : ℤ, |q * θ₁ - m₁| ≤ 1 / Q ∧ |q * θ₂ - m₂| ≤ 1 / Q := by
    intro a b hab hb hf
    simp only [f, Prod.mk.injEq] at hf
    have hb' : (b : ℤ) ≤ (Q : ℤ) ^ 2 := by exact_mod_cast hb
    refine ⟨(b : ℤ) - a, by omega, by omega,
      ⌊(b : ℝ) * θ₁⌋ - ⌊(a : ℝ) * θ₁⌋, ⌊(b : ℝ) * θ₂⌋ - ⌊(a : ℝ) * θ₂⌋, ?_, ?_⟩
    · have := abs_sub_le_of_floor_eq (by omega) (Int.fract_nonneg _) (Int.fract_nonneg _) hf.1
      rw [abs_sub_comm] at this
      convert this using 2
      simp only [Int.fract]; push_cast; ring
    · have := abs_sub_le_of_floor_eq (by omega) (Int.fract_nonneg _) (Int.fract_nonneg _) hf.2
      rw [abs_sub_comm] at this
      convert this using 2
      simp only [Int.fract]; push_cast; ring
  obtain ⟨a, ha, b, hb, hne, hab⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  rw [Finset.mem_range] at ha hb
  rcases lt_or_gt_of_ne hne with h | h
  · exact key a b h (by omega) hab
  · exact key b a h (by omega) hab.symm

/-- **(proved).**  If `θ₁` is irrational, then for every `ε > 0` infinitely many `q ≥ 1`
have `‖qθ₁‖ < ε` and `‖qθ₂‖ < ε`.  Paper proof: if the set were finite, `μ = min ‖qθ₁‖ > 0` over
it (`θ₁` irrational, `q ≠ 0`); `exists_simultaneous_approx` with `Q > max(1/μ, 1/ε)` produces a
member with `‖qθ₁‖ < μ`. -/
theorem infinite_simultaneous_approx {θ₁ : ℝ} (θ₂ : ℝ) (h : Irrational θ₁) {ε : ℝ} (hε : 0 < ε) :
    {q : ℤ | 1 ≤ q ∧ ∃ m₁ m₂ : ℤ, |q * θ₁ - m₁| < ε ∧ |q * θ₂ - m₂| < ε}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨N, hN⟩
  let g : ℤ → ℝ := fun q => |q * θ₁ - round ((q : ℝ) * θ₁)|
  have gpos : ∀ q : ℤ, q ≠ 0 → 0 < g q := fun q hq => by
    refine abs_pos.2 (sub_ne_zero.2 fun he => ?_)
    exact (h.intCast_mul hq).ne_int _ he
  obtain ⟨δ, hδ, hδle⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ Finset.Icc (1 : ℤ) N, δ ≤ g q := by
    by_cases hne : (Finset.Icc (1 : ℤ) N).Nonempty
    · obtain ⟨q₀, hq₀, hmin⟩ := Finset.exists_min_image _ g hne
      exact ⟨g q₀, gpos q₀ (by rw [Finset.mem_Icc] at hq₀; omega), hmin⟩
    · exact ⟨1, one_pos, fun q hq => absurd ⟨q, hq⟩ hne⟩
  obtain ⟨Q, hQ⟩ := exists_nat_gt (max (1 / δ) (1 / ε))
  have hQ0 : (0 : ℝ) < Q := lt_of_le_of_lt (by positivity) (lt_of_le_of_lt (le_max_left _ _) hQ)
  have hQ1 : 1 ≤ Q := by exact_mod_cast hQ0
  have h1Q : 1 / (Q : ℝ) < δ := by
    rw [div_lt_iff₀ hQ0]; have := lt_of_le_of_lt (le_max_left _ _) hQ
    rw [div_lt_iff₀ hδ] at this; linarith
  have h1Q' : 1 / (Q : ℝ) < ε := by
    rw [div_lt_iff₀ hQ0]; have := lt_of_le_of_lt (le_max_right _ _) hQ
    rw [div_lt_iff₀ hε] at this; linarith
  obtain ⟨q, hq1, -, m₁, m₂, hm₁, hm₂⟩ := exists_simultaneous_approx θ₁ θ₂ hQ1
  have hmem : q ∈ {q : ℤ | 1 ≤ q ∧ ∃ m₁ m₂ : ℤ, |q * θ₁ - m₁| < ε ∧ |q * θ₂ - m₂| < ε} :=
    ⟨hq1, m₁, m₂, by linarith, by linarith⟩
  have hqN := hN hmem
  have := hδle q (Finset.mem_Icc.2 ⟨hq1, hqN⟩)
  have := round_le ((q : ℝ) * θ₁) m₁
  simp only [g] at *
  linarith

/-- The hypotheses of the translation lemma, in pure real arithmetic. -/
structure TCtx (x A d₁ d₂ : ℝ) : Prop where
  hx1 : 56984029 / 10 ^ 8 < x
  hx2 : x < 56984030 / 10 ^ 8
  hA1 : 40795 / 10000 < A
  hA2 : A < 40797 / 10000
  d1l : -(1 / 200) < d₁
  d1u : d₁ < 1 / 200
  d2l : -(1 / 200) < d₂
  d2u : d₂ < 1 / 200

/-- The error products of the translation lemma. -/
theorem TCtx.xd1 {x A d₁ d₂ : ℝ} (c : TCtx x A d₁ d₂) :
    -(1 / 200) < x * d₁ ∧ x * d₁ < 1 / 200 := by
  have := c.hx1; have := c.hx2; have := c.d1l; have := c.d1u
  constructor <;> nlinarith

theorem TCtx.xd2 {x A d₁ d₂ : ℝ} (c : TCtx x A d₁ d₂) :
    -(1 / 200) < x * d₂ ∧ x * d₂ < 1 / 200 := by
  have := c.hx1; have := c.hx2; have := c.d2l; have := c.d2u
  constructor <;> nlinarith

theorem TCtx.Ad2 {x A d₁ d₂ : ℝ} (c : TCtx x A d₁ d₂) :
    -(40797 / 10000 / 200) < A * d₂ ∧ A * d₂ < 40797 / 10000 / 200 := by
  have := c.hA1; have := c.hA2; have := c.d2l; have := c.d2u
  constructor <;> nlinarith

/-- The seven-step translation, step by step (`TCtx`; the slope relations `r1`-`r4`). -/
theorem tstep1 {x A d₁ d₂ q m₁ : ℝ} (c : TCtx x A d₁ d₂) (hm₁ : m₁ = q * A - d₁) :
    81 + 2 * m₁ ≤ A * (20 + 2 * q) ∧ A * (20 + 2 * q) < 81 + 2 * m₁ + 1 := by
  have e : A * (20 + 2 * q) = 81 + 2 * m₁ + (20 * A - 81 + 2 * d₁) := by rw [hm₁]; ring
  have := c.hA1; have := c.hA2; have := c.d1l; have := c.d1u
  rw [e]; constructor <;> linarith

theorem tstep2 {x A d₁ d₂ q m₁ m₂ : ℝ} (c : TCtx x A d₁ d₂) (hm₁ : m₁ = q * A - d₁)
    (hm₂ : m₂ = q * (A * x) - d₂) :
    46 + 2 * m₂ < x * (81 + 2 * m₁ + 1) ∧ x * (81 + 2 * m₁ + 1) ≤ 46 + 2 * m₂ + 1 := by
  have e : x * (81 + 2 * m₁ + 1) = 46 + 2 * m₂ + (82 * x - 46 + 2 * d₂ - 2 * (x * d₁)) := by
    rw [hm₁, hm₂]; ring
  have := c.hx1; have := c.hx2; have := c.d2l; have := c.d2u; have := c.xd1
  rw [e]; constructor <;> linarith

theorem tstep3 {x A d₁ d₂ q m₁ m₂ : ℝ} (c : TCtx x A d₁ d₂) (hm₁ : m₁ = q * A - d₁)
    (hm₂ : m₂ = q * (A * x) - d₂) (r1 : A * A * x = -1 + 2 * A + A * x) :
    187 + 2 * (-q + 2 * m₁ + m₂) ≤ A * (46 + 2 * m₂) ∧
      A * (46 + 2 * m₂) < 187 + 2 * (-q + 2 * m₁ + m₂) + 1 := by
  have e : A * (46 + 2 * m₂) = 187 + 2 * (-q + 2 * m₁ + m₂) +
      (46 * A - 187 + 2 * (2 * d₁ + d₂) - 2 * (A * d₂)) := by
    rw [hm₁, hm₂]; linear_combination (2 * q) * r1
  have := c.hA1; have := c.hA2; have := c.d1l; have := c.d1u; have := c.d2l; have := c.d2u
  have := c.Ad2
  rw [e]; constructor <;> linarith

theorem tstep4 {x A d₁ d₂ q m₁ m₂ : ℝ} (c : TCtx x A d₁ d₂) (hm₁ : m₁ = q * A - d₁)
    (hm₂ : m₂ = q * (A * x) - d₂) (r2 : x * (-1 + 2 * A + A * x) = -1 + A + A * x) :
    107 + 2 * (-q + m₁ + m₂) < x * (187 + 2 * (-q + 2 * m₁ + m₂) + 1) ∧
      x * (187 + 2 * (-q + 2 * m₁ + m₂) + 1) ≤ 107 + 2 * (-q + m₁ + m₂) + 1 := by
  have e : x * (187 + 2 * (-q + 2 * m₁ + m₂) + 1) = 107 + 2 * (-q + m₁ + m₂) +
      (188 * x - 107 + 2 * (d₁ + d₂) - 4 * (x * d₁) - 2 * (x * d₂)) := by
    rw [hm₁, hm₂]; linear_combination (2 * q) * r2
  have := c.hx1; have := c.hx2; have := c.d1l; have := c.d1u; have := c.d2l; have := c.d2u
  have := c.xd1; have := c.xd2
  rw [e]; constructor <;> linarith

theorem tstep5 {x A d₁ d₂ q m₁ m₂ : ℝ} (c : TCtx x A d₁ d₂) (hm₁ : m₁ = q * A - d₁)
    (hm₂ : m₂ = q * (A * x) - d₂) (r3 : x * (-1 + A + A * x) = -1 + A) :
    61 + 2 * (-q + m₁) < x * (107 + 2 * (-q + m₁ + m₂) + 1) ∧
      x * (107 + 2 * (-q + m₁ + m₂) + 1) ≤ 61 + 2 * (-q + m₁) + 1 := by
  have e : x * (107 + 2 * (-q + m₁ + m₂) + 1) = 61 + 2 * (-q + m₁) +
      (108 * x - 61 + 2 * d₁ - 2 * (x * d₁) - 2 * (x * d₂)) := by
    rw [hm₁, hm₂]; linear_combination (2 * q) * r3
  have := c.hx1; have := c.hx2; have := c.d1l; have := c.d1u
  have := c.xd1; have := c.xd2
  rw [e]; constructor <;> linarith

theorem tstep6 {x A d₁ d₂ q m₁ m₂ : ℝ} (c : TCtx x A d₁ d₂) (hm₁ : m₁ = q * A - d₁)
    (hm₂ : m₂ = q * (A * x) - d₂) (r4 : x * (-1 + A) = A - A * x) :
    35 + 2 * (m₁ - m₂) < x * (61 + 2 * (-q + m₁) + 1) ∧
      x * (61 + 2 * (-q + m₁) + 1) ≤ 35 + 2 * (m₁ - m₂) + 1 := by
  have e : x * (61 + 2 * (-q + m₁) + 1) = 35 + 2 * (m₁ - m₂) +
      (62 * x - 35 + 2 * d₁ - 2 * d₂ - 2 * (x * d₁)) := by
    rw [hm₁, hm₂]; linear_combination (2 * q) * r4
  have := c.hx1; have := c.hx2; have := c.d1l; have := c.d1u; have := c.d2l; have := c.d2u
  have := c.xd1
  rw [e]; constructor <;> linarith

/-- **(proved; the translation lemma).**  If `‖qA‖ < 1/200` and `‖qAx‖ < 1/200`
(`A = α/2`), then `20 + 2q` lies on the cylinder.  Paper proof: write `qA = m₁ + δ₁`,
`qAx = m₂ + δ₂`.  The prefix slopes `s_i` of `E O E O⁴` have coordinates `(c₀, c₁, c₂)` on the
`ℤ`-basis `1, A, Ax`: `s_0 = 1`, `s_1 = A`, `s_2 = Ax`, `s_3 = −1 + 2A + Ax`, `s_4 = −1 + A + Ax`,
`s_5 = −1 + A`, `s_6 = A − Ax` (module docstring).  Claim `Wⁱ(20 + 2q) = Wⁱ(20) + D_i` with the
even integers `D_i = 2(c₀ q + c₁ m₁ + c₂ m₂)` (`D_0 = 2q`), by induction: the `i`-th step's
argument (`A·u` on evens, `x(u + 1)` on odds; the branch is unchanged as `D_{i−1}` is even)
moves by `λ_i D_{i−1} = D_i + e_i` with `e_i = 2(c_i·δ) − 2λ_i (c_{i−1}·δ)`, `|e_i| ≤ 10.2·max|δ|
< 0.052`; the arguments at `n = 20` (`81.592, 46.727, 187.661, 107.130, 61.543, 35.330`) are at
distance `≥ 0.1299` from `ℤ`, so each floor/ceiling moves by exactly `D_i`
(`pRoot_bounds`, `alphaP_mem`).  Parities are preserved. -/
theorem twenty_add_two_mul_mem_sevenCyl {q m₁ m₂ : ℤ} (h₁ : |q * (alphaP / 2) - m₁| < 1 / 200)
    (h₂ : |q * (alphaP / 2 * pRoot) - m₂| < 1 / 200) : 20 + 2 * q ∈ sevenCyl := by
  obtain ⟨hx1, hx2⟩ := pRoot_bounds
  obtain ⟨hα1, hα2⟩ := alphaP_mem
  have hc := pRoot_spec.2.2
  have hA := half_alphaP_eq
  have r1 : alphaP / 2 * (alphaP / 2) * pRoot = -1 + 2 * (alphaP / 2) + alphaP / 2 * pRoot := by
    rw [hA]; linear_combination (7 + 4 * pRoot ^ 2) * hc
  have r2 : pRoot * (-1 + 2 * (alphaP / 2) + alphaP / 2 * pRoot) =
      -1 + alphaP / 2 + alphaP / 2 * pRoot := by
    rw [hA]; linear_combination (3 + 2 * pRoot) * hc
  have r3 : pRoot * (-1 + alphaP / 2 + alphaP / 2 * pRoot) = -1 + alphaP / 2 := by
    rw [hA]; linear_combination (3 + 2 * pRoot) * hc
  have r4 : pRoot * (-1 + alphaP / 2) = alphaP / 2 - alphaP / 2 * pRoot := by
    rw [hA]; linear_combination 4 * hc
  obtain ⟨d₁, hm₁⟩ : ∃ d : ℝ, (m₁ : ℝ) = q * (alphaP / 2) - d := ⟨q * (alphaP / 2) - m₁, by ring⟩
  obtain ⟨d₂, hm₂⟩ : ∃ d : ℝ, (m₂ : ℝ) = q * (alphaP / 2 * pRoot) - d :=
    ⟨q * (alphaP / 2 * pRoot) - m₂, by ring⟩
  rw [hm₁, sub_sub_cancel] at h₁
  rw [hm₂, sub_sub_cancel] at h₂
  have c : TCtx pRoot (alphaP / 2) d₁ d₂ :=
    ⟨hx1, hx2, by linarith, by linarith, (abs_lt.1 h₁).1, (abs_lt.1 h₁).2, (abs_lt.1 h₂).1,
      (abs_lt.1 h₂).2⟩
  have s1 : wy alphaP (20 + 2 * q) = 81 + 2 * m₁ := by
    obtain ⟨a, b⟩ := tstep1 (q := q) c hm₁
    exact evenEval (by omega) (by push_cast; exact a) (by push_cast; exact b)
  have s2 : wy alphaP (81 + 2 * m₁) = 46 + 2 * m₂ := by
    obtain ⟨a, b⟩ := tstep2 c hm₁ hm₂
    exact oddEval (by omega) (by push_cast; exact a) (by push_cast; exact b)
  have s3 : wy alphaP (46 + 2 * m₂) = 187 + 2 * (-q + 2 * m₁ + m₂) := by
    obtain ⟨a, b⟩ := tstep3 c hm₁ hm₂ r1
    exact evenEval (by omega) (by push_cast; exact a) (by push_cast; exact b)
  have s4 : wy alphaP (187 + 2 * (-q + 2 * m₁ + m₂)) = 107 + 2 * (-q + m₁ + m₂) := by
    obtain ⟨a, b⟩ := tstep4 c hm₁ hm₂ r2
    exact oddEval (by omega) (by push_cast; exact a) (by push_cast; exact b)
  have s5 : wy alphaP (107 + 2 * (-q + m₁ + m₂)) = 61 + 2 * (-q + m₁) := by
    obtain ⟨a, b⟩ := tstep5 c hm₁ hm₂ r3
    exact oddEval (by omega) (by push_cast; exact a) (by push_cast; exact b)
  have s6 : wy alphaP (61 + 2 * (-q + m₁)) = 35 + 2 * (m₁ - m₂) := by
    obtain ⟨a, b⟩ := tstep6 c hm₁ hm₂ r4
    exact oddEval (by omega) (by push_cast; exact a) (by push_cast; exact b)
  refine ⟨by omega, ?_, ?_, ?_⟩
  · rw [s1]; omega
  · simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, s1, s2]; omega
  · intro i hi3 hi6
    interval_cases i <;>
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, s1, s2, s3, s4, s5,
        s6] <;> omega

/-- **(proved; infinitely many 7-cycles, unconditional).**  Infinitely many positive integers
have minimal period `7`.  Paper proof: `infinite_simultaneous_approx` with `θ₁ = A`
(irrational, `irrational_alphaP`), `θ₂ = Ax`, `ε = 1/200`; the injective map `q ↦ 20 + 2q` sends
that infinite set into `{n > 0 : n ∈ sevenCyl}` (`twenty_add_two_mul_mem_sevenCyl`), and every
cylinder point has minimal period `7` (`minimalPeriod_alphaP_of_cyl`). -/
theorem infinite_minimalPeriod_seven :
    {n : ℤ | 0 < n ∧ Function.minimalPeriod (wy alphaP) n = 7}.Infinite := by
  have hirr : Irrational (alphaP / 2) := by
    simpa using irrational_alphaP.div_natCast (m := 2) (by norm_num)
  have hS := infinite_simultaneous_approx (alphaP / 2 * pRoot) hirr
    (show (0 : ℝ) < 1 / 200 by norm_num)
  refine Set.infinite_of_injOn_mapsTo (f := fun q : ℤ => 20 + 2 * q)
    (fun a _ b _ hab => by simp only at hab; omega) ?_ hS
  rintro q ⟨hq, m₁, m₂, h₁, h₂⟩
  exact ⟨by show 0 < 20 + 2 * q; omega,
    minimalPeriod_alphaP_of_cyl (twenty_add_two_mul_mem_sevenCyl h₁ h₂)⟩

end CollatzMoonshot.WythoffSeven
