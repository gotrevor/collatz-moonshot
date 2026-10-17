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

/-- **(drafted, 96%; Theorem N (2) instance).**  On `E O O`: if `v` is even and `W(v), W²(v)`
are odd, then `W³(v) = W²(v) − v` (so `W³(v)` is odd).  Paper proof:
`WythoffAutomaton.first_step_eq_ceil` with `P = t³ − t² + 2t − 1`: `q = (2 − x + x², x − 1, 1)`,
`q_0 + 2a_0 = x² − x`, `Φ₀ = −(1 − x)(x G_E + G) ∈ (−(1 − x²), 0)` since `G_E ∈ (0, 1]`,
`G ∈ [0, 1)`; so the integer `w_3 − w_2 + v = W³ v − W² v + v` is `⌈Φ₀⌉ = 0`.  Directly: with
`W v + 1 = Av + G_E`, `W² v + 1 = x(W v + 1) + G′`, `W³ v + 1 = x(W² v + 1) + G″` and the cubic,
`W³ v − W² v + v = Φ₀ + G″ ∈ (−1, 1)`. -/
theorem wy_alphaP_eoo {v : ℤ} (hv : v % 2 = 0) (h₁ : W v % 2 = 1) (h₂ : W^[2] v % 2 = 1) :
    W^[3] v = W^[2] v - v := by
  sorry

/-- **(drafted, 95%).**  On `E O E O`: `W³(n) − (−n + 2W(n) + W²(n)) ∈ {−1, 1}`.  Paper proof:
module docstring (`K_3`; torus coordinates, two cases `⌈z⌉ ∈ {1, 3}`, parity). -/
theorem wy_alphaP_iterate_three_sub_mem {n : ℤ} (hn : n % 2 = 0) (h₁ : W n % 2 = 1)
    (h₂ : W^[2] n % 2 = 0) (h₃ : W^[3] n % 2 = 1) :
    W^[3] n - (-n + 2 * W n + W^[2] n) ∈ ({-1, 1} : Set ℤ) := by
  sorry

/-- **(drafted, 95%).**  On `E O E O O`: `W⁴(n) = −n + W(n) + W²(n)`.  Paper proof: module
docstring (`K_4 ∈ (−1.39, 1.57)`, even). -/
theorem wy_alphaP_iterate_four_eq {n : ℤ} (hn : n % 2 = 0) (h₁ : W n % 2 = 1)
    (h₂ : W^[2] n % 2 = 0) (h₃ : W^[3] n % 2 = 1) (h₄ : W^[4] n % 2 = 1) :
    W^[4] n = -n + W n + W^[2] n := by
  sorry

/-- **(drafted, 95%).**  On `E O E O O`: `W⁵(n) = −n + W(n)`, odd.  Paper proof:
`wy_alphaP_eoo` at `v = W²(n)` and `wy_alphaP_iterate_four_eq`. -/
theorem wy_alphaP_iterate_five_eq {n : ℤ} (hn : n % 2 = 0) (h₁ : W n % 2 = 1)
    (h₂ : W^[2] n % 2 = 0) (h₃ : W^[3] n % 2 = 1) (h₄ : W^[4] n % 2 = 1) :
    W^[5] n = -n + W n := by
  sorry

/-- **(drafted, 95%).**  On `E O E O O O O`: `W⁶(n) = W(n) − W²(n)`.  Paper proof: module
docstring (`K_6 ∈ (−1.43, 1.57)`, even). -/
theorem wy_alphaP_iterate_six_eq {n : ℤ} (hn : n % 2 = 0) (h₁ : W n % 2 = 1)
    (h₂ : W^[2] n % 2 = 0) (h₃ : W^[3] n % 2 = 1) (h₄ : W^[4] n % 2 = 1)
    (h₆ : W^[6] n % 2 = 1) :
    W^[6] n = W n - W^[2] n := by
  sorry

/-- **(drafted, 95%; the 7-cycle identity).**  If `n` is even and `W(n), …, W⁶(n)` have parities
`O, E, O, O, O, O`, then `W⁷(n) = n`; for every `n ∈ ℤ`.  Paper proof: module docstring
(`K_7 = x(1 − x)G_1 − xG_2 + x − 1 + h_7 ∈ (−1, 1)` given `K_6 = 0`).  The hypothesis on
`W⁵(n)` is automatic (`wy_alphaP_iterate_five_eq`); it is kept to state the cylinder. -/
theorem wy_alphaP_iterate_seven_eq {n : ℤ} (hn : n % 2 = 0) (h₁ : W n % 2 = 1)
    (h₂ : W^[2] n % 2 = 0) (h₃ : W^[3] n % 2 = 1) (h₄ : W^[4] n % 2 = 1)
    (h₅ : W^[5] n % 2 = 1) (h₆ : W^[6] n % 2 = 1) :
    W^[7] n = n := by
  sorry

end Labels

/-! ## 7-cycles -/

/-- The cylinder `E O E O O O O` of `W_α`. -/
def sevenCyl : Set ℤ :=
  {n | n % 2 = 0 ∧ wy alphaP n % 2 = 1 ∧ (wy alphaP)^[2] n % 2 = 0 ∧
    ∀ i : ℕ, 3 ≤ i → i ≤ 6 → (wy alphaP)^[i] n % 2 = 1}

/-- **(drafted, 95%).**  Every point of the cylinder has minimal period exactly `7`.  Paper
proof: `wy_alphaP_iterate_seven_eq` gives `IsPeriodicPt W 7 n`, so the minimal period divides
`7` (`Function.IsPeriodicPt.minimalPeriod_dvd`); it is not `1` since `W(n)` is odd and `n` even;
`Nat.Prime 7`. -/
theorem minimalPeriod_alphaP_of_cyl {n : ℤ} (hn : n ∈ sevenCyl) :
    Function.minimalPeriod (wy alphaP) n = 7 := by
  sorry

/-- **(drafted, 97%; unconditional example).**  `20 → 81 → 46 → 187 → 107 → 61 → 35 → 20`.
Paper proof: `20 ∈ sevenCyl` by evaluating the seven floors with `alphaP_mem` (`⌊10α⌋ = 81`,
`⌈41β⌉ − 1 = 46`, `⌊23α⌋ = 187`, `⌈94β⌉ − 1 = 107`, `⌈54β⌉ − 1 = 61`, `⌈31β⌉ − 1 = 35`; `β`
from `alphaP_div_sub_one` and `pRoot_bounds`); `minimalPeriod_alphaP_of_cyl`. -/
theorem minimalPeriod_alphaP_twenty : Function.minimalPeriod (wy alphaP) 20 = 7 := by
  sorry

/-- **(drafted, 97%; simultaneous Dirichlet approximation).**  For reals `θ₁, θ₂` and `Q ≥ 1`
there is `1 ≤ q ≤ Q²` with `‖qθ₁‖, ‖qθ₂‖ ≤ 1/Q`.  Paper proof: pigeonhole on the `Q² + 1`
points `({qθ₁}, {qθ₂})`, `0 ≤ q ≤ Q²`, in the `Q²` boxes of side `1/Q`
(`Finset.exists_ne_map_eq_of_card_lt_of_maps_to`); subtract the two indices. -/
theorem exists_simultaneous_approx (θ₁ θ₂ : ℝ) {Q : ℕ} (hQ : 1 ≤ Q) :
    ∃ q : ℤ, 1 ≤ q ∧ q ≤ (Q : ℤ) ^ 2 ∧ ∃ m₁ m₂ : ℤ,
      |q * θ₁ - m₁| ≤ 1 / Q ∧ |q * θ₂ - m₂| ≤ 1 / Q := by
  sorry

/-- **(drafted, 96%).**  If `θ₁` is irrational, then for every `ε > 0` infinitely many `q ≥ 1`
have `‖qθ₁‖ < ε` and `‖qθ₂‖ < ε`.  Paper proof: if the set were finite, `μ = min ‖qθ₁‖ > 0` over
it (`θ₁` irrational, `q ≠ 0`); `exists_simultaneous_approx` with `Q > max(1/μ, 1/ε)` produces a
member with `‖qθ₁‖ < μ`. -/
theorem infinite_simultaneous_approx {θ₁ : ℝ} (θ₂ : ℝ) (h : Irrational θ₁) {ε : ℝ} (hε : 0 < ε) :
    {q : ℤ | 1 ≤ q ∧ ∃ m₁ m₂ : ℤ, |q * θ₁ - m₁| < ε ∧ |q * θ₂ - m₂| < ε}.Infinite := by
  sorry

/-- **(drafted, 95%; the translation lemma).**  If `‖qA‖ < 1/200` and `‖qAx‖ < 1/200`
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
  sorry

/-- **(drafted, 95%; infinitely many 7-cycles, unconditional).**  Infinitely many positive integers
have minimal period `7`.  Paper proof: `infinite_simultaneous_approx` with `θ₁ = A`
(irrational, `irrational_alphaP`), `θ₂ = Ax`, `ε = 1/200`; the injective map `q ↦ 20 + 2q` sends
that infinite set into `{n > 0 : n ∈ sevenCyl}` (`twenty_add_two_mul_mem_sevenCyl`), and every
cylinder point has minimal period `7` (`minimalPeriod_alphaP_of_cyl`). -/
theorem infinite_minimalPeriod_seven :
    {n : ℤ | 0 < n ∧ Function.minimalPeriod (wy alphaP) n = 7}.Infinite := by
  sorry

end CollatzMoonshot.WythoffSeven
