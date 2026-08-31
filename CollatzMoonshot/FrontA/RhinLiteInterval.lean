/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.FrontA.RhinLiteCritical

/-!
# Exact local interval bounds for the Rhin-lite kernel

`RhinLiteCritical.lean` proves that every critical point on `[2,4]` lies in one of seven
millionth-wide rational brackets.  Here we attach deliberately rounded-up rational bounds to the
six Rhin factors on each bracket.  Their weighted product still has ample slack below
`(9/40)^1000`.

All large arithmetic is one finite `native_decide` certificate.  The remaining proofs only show
that a linear or quadratic function stays between its endpoint values on the indicated tiny
interval.
-/

namespace CollatzMoonshot.FrontA

open Set

/-- Rounded-up factor bounds, in millionths.  Row `i` corresponds to critical bracket `i.succ`;
columns are `Q₁,…,Q₆`. -/
def rhinLiteFactorBound : Fin 7 → Fin 6 → ℚ :=
  ![![884897 / 1000000, 115104 / 1000000, 1884897 / 1000000, 1424485 / 1000000,
      4311726 / 1000000, 568430 / 1000000],
    ![776757 / 1000000, 223244 / 1000000, 1776757 / 1000000, 883785 / 1000000,
      1256975 / 1000000, 2196889 / 1000000],
    ![687488 / 1000000, 312513 / 1000000, 1687488 / 1000000, 437440 / 1000000,
      965148 / 1000000, 4144793 / 1000000],
    ![479105 / 1000000, 520896 / 1000000, 1479105 / 1000000, 604480 / 1000000,
      5097810 / 1000000, 7513352 / 1000000],
    ![474819 / 1000000, 1474819 / 1000000, 525182 / 1000000, 5374095 / 1000000,
      5167314 / 1000000, 1867502 / 1000000],
    ![652360 / 1000000, 1652360 / 1000000, 347641 / 1000000, 6261800 / 1000000,
      1765272 / 1000000, 3000058 / 1000000],
    ![780898 / 1000000, 1780898 / 1000000, 219103 / 1000000, 6904490 / 1000000,
      1366629 / 1000000, 7271621 / 1000000]]

def rhinLiteBoundProduct (i : Fin 7) : ℚ :=
  rhinLiteFactorBound i 0 ^ rhinLiteW1 *
    rhinLiteFactorBound i 1 ^ rhinLiteW2 *
    rhinLiteFactorBound i 2 ^ rhinLiteW3 *
    rhinLiteFactorBound i 3 ^ rhinLiteW4 *
    rhinLiteFactorBound i 4 ^ rhinLiteW5 *
    rhinLiteFactorBound i 5 ^ rhinLiteW6

theorem rhinLite_factorBound_nonneg (i : Fin 7) (j : Fin 6) :
    0 ≤ rhinLiteFactorBound i j := by
  native_decide +revert

/-- The rounded factor bounds retain at least the target geometric decay. -/
theorem rhinLite_boundProduct_certificate (i : Fin 7) :
    rhinLiteBoundProduct i ≤
      rhinLiteRootLeft i.succ ^ rhinLiteScale * (9 / 40 : ℚ) ^ rhinLiteScale := by
  native_decide +revert

def rhinLiteFactor1 (x : ℝ) : ℝ := x - 3
def rhinLiteFactor2 (x : ℝ) : ℝ := x - 2
def rhinLiteFactor3 (x : ℝ) : ℝ := x - 4
def rhinLiteFactor4 (x : ℝ) : ℝ := 5 * x - 12
def rhinLiteFactor5 (x : ℝ) : ℝ := 17 * x ^ 2 - 102 * x + 144
def rhinLiteFactor6 (x : ℝ) : ℝ := 19 * x ^ 2 - 108 * x + 144

theorem abs_rhinLiteFactor1_le (i : Fin 7) {x : ℝ}
    (hx : x ∈ Icc (rhinLiteRootLeft i.succ : ℝ) (rhinLiteRootRight i.succ : ℝ)) :
    |rhinLiteFactor1 x| ≤ (rhinLiteFactorBound i 0 : ℝ) := by
  fin_cases i <;>
    simp [rhinLiteRootLeft, rhinLiteRootRight, rhinLiteFactorBound,
      rhinLiteFactor1] at hx ⊢ <;> norm_num at hx ⊢ <;>
    rw [abs_le] <;> constructor <;> linarith

theorem abs_rhinLiteFactor2_le (i : Fin 7) {x : ℝ}
    (hx : x ∈ Icc (rhinLiteRootLeft i.succ : ℝ) (rhinLiteRootRight i.succ : ℝ)) :
    |rhinLiteFactor2 x| ≤ (rhinLiteFactorBound i 1 : ℝ) := by
  fin_cases i <;>
    simp [rhinLiteRootLeft, rhinLiteRootRight, rhinLiteFactorBound,
      rhinLiteFactor2] at hx ⊢ <;> norm_num at hx ⊢ <;>
    rw [abs_le] <;> constructor <;> linarith

theorem abs_rhinLiteFactor3_le (i : Fin 7) {x : ℝ}
    (hx : x ∈ Icc (rhinLiteRootLeft i.succ : ℝ) (rhinLiteRootRight i.succ : ℝ)) :
    |rhinLiteFactor3 x| ≤ (rhinLiteFactorBound i 2 : ℝ) := by
  fin_cases i <;>
    simp [rhinLiteRootLeft, rhinLiteRootRight, rhinLiteFactorBound,
      rhinLiteFactor3] at hx ⊢ <;> norm_num at hx ⊢ <;>
    rw [abs_le] <;> constructor <;> linarith

theorem abs_rhinLiteFactor4_le (i : Fin 7) {x : ℝ}
    (hx : x ∈ Icc (rhinLiteRootLeft i.succ : ℝ) (rhinLiteRootRight i.succ : ℝ)) :
    |rhinLiteFactor4 x| ≤ (rhinLiteFactorBound i 3 : ℝ) := by
  fin_cases i <;>
    simp [rhinLiteRootLeft, rhinLiteRootRight, rhinLiteFactorBound,
      rhinLiteFactor4] at hx ⊢ <;> norm_num at hx ⊢ <;>
    rw [abs_le] <;> constructor <;> linarith

/-- Difference factorization used to order either quadratic on a short interval. -/
theorem rhinLiteQuadratic_sub (a b c x y : ℝ) :
    (a * y ^ 2 + b * y + c) - (a * x ^ 2 + b * x + c) =
      (y - x) * (a * (y + x) + b) := by
  ring

theorem abs_rhinLiteFactor5_le (i : Fin 7) {x : ℝ}
    (hx : x ∈ Icc (rhinLiteRootLeft i.succ : ℝ) (rhinLiteRootRight i.succ : ℝ)) :
    |rhinLiteFactor5 x| ≤ (rhinLiteFactorBound i 4 : ℝ) := by
  fin_cases i <;>
    simp [rhinLiteRootLeft, rhinLiteRootRight, rhinLiteFactorBound,
      rhinLiteFactor5] at hx ⊢ <;> norm_num at hx ⊢ <;>
    rw [abs_le] <;>
    constructor <;>
    nlinarith [sq_nonneg (x - 3), mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hx.2)]

theorem abs_rhinLiteFactor6_le (i : Fin 7) {x : ℝ}
    (hx : x ∈ Icc (rhinLiteRootLeft i.succ : ℝ) (rhinLiteRootRight i.succ : ℝ)) :
    |rhinLiteFactor6 x| ≤ (rhinLiteFactorBound i 5 : ℝ) := by
  fin_cases i <;>
    simp [rhinLiteRootLeft, rhinLiteRootRight, rhinLiteFactorBound,
      rhinLiteFactor6] at hx ⊢ <;> norm_num at hx ⊢ <;>
    rw [abs_le] <;>
    constructor <;>
    nlinarith [sq_nonneg (19 * x - 54),
      mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hx.2)]

/-! ## Weighted product certificate -/

def rhinLiteKernelAbs (x : ℝ) : ℝ :=
  |rhinLiteFactor1 x| ^ rhinLiteW1 *
    |rhinLiteFactor2 x| ^ rhinLiteW2 *
    |rhinLiteFactor3 x| ^ rhinLiteW3 *
    |rhinLiteFactor4 x| ^ rhinLiteW4 *
    |rhinLiteFactor5 x| ^ rhinLiteW5 *
    |rhinLiteFactor6 x| ^ rhinLiteW6

theorem rhinLiteKernelAbs_le_boundProduct (i : Fin 7) {x : ℝ}
    (hx : x ∈ Icc (rhinLiteRootLeft i.succ : ℝ) (rhinLiteRootRight i.succ : ℝ)) :
    rhinLiteKernelAbs x ≤ (rhinLiteBoundProduct i : ℝ) := by
  have hb0 : (0 : ℝ) ≤ (rhinLiteFactorBound i 0 : ℝ) := by
    exact_mod_cast rhinLite_factorBound_nonneg i 0
  have hb1 : (0 : ℝ) ≤ (rhinLiteFactorBound i 1 : ℝ) := by
    exact_mod_cast rhinLite_factorBound_nonneg i 1
  have hb2 : (0 : ℝ) ≤ (rhinLiteFactorBound i 2 : ℝ) := by
    exact_mod_cast rhinLite_factorBound_nonneg i 2
  have hb3 : (0 : ℝ) ≤ (rhinLiteFactorBound i 3 : ℝ) := by
    exact_mod_cast rhinLite_factorBound_nonneg i 3
  have hb4 : (0 : ℝ) ≤ (rhinLiteFactorBound i 4 : ℝ) := by
    exact_mod_cast rhinLite_factorBound_nonneg i 4
  have hb5 : (0 : ℝ) ≤ (rhinLiteFactorBound i 5 : ℝ) := by
    exact_mod_cast rhinLite_factorBound_nonneg i 5
  simp only [rhinLiteKernelAbs, rhinLiteBoundProduct, Rat.cast_mul, Rat.cast_pow]
  gcongr <;>
    first
    | exact abs_rhinLiteFactor1_le i hx
    | exact abs_rhinLiteFactor2_le i hx
    | exact abs_rhinLiteFactor3_le i hx
    | exact abs_rhinLiteFactor4_le i hx
    | exact abs_rhinLiteFactor5_le i hx
    | exact abs_rhinLiteFactor6_le i hx

theorem rhinLite_positiveRootLeft (i : Fin 7) :
    (0 : ℚ) < rhinLiteRootLeft i.succ := by
  native_decide +revert

set_option maxRecDepth 100000 in
/-- On every certified critical bracket, the weighted absolute kernel has the required geometric
decay.  This is the finite interval-arithmetic endpoint promised by the exploratory script. -/
theorem rhinLiteKernelAbs_div_pow_le (i : Fin 7) {x : ℝ}
    (hx : x ∈ Icc (rhinLiteRootLeft i.succ : ℝ) (rhinLiteRootRight i.succ : ℝ)) :
    rhinLiteKernelAbs x / x ^ rhinLiteScale ≤ (9 / 40 : ℝ) ^ rhinLiteScale := by
  have hcert' : (rhinLiteBoundProduct i : ℝ) ≤
      ((rhinLiteRootLeft i.succ ^ rhinLiteScale *
        (9 / 40 : ℚ) ^ rhinLiteScale : ℚ) : ℝ) := by
    exact_mod_cast rhinLite_boundProduct_certificate i
  have hcert : (rhinLiteBoundProduct i : ℝ) ≤
      (rhinLiteRootLeft i.succ : ℝ) ^ rhinLiteScale *
        (9 / 40 : ℝ) ^ rhinLiteScale := by
    push_cast at hcert'
    exact hcert'
  have hleft : (0 : ℝ) ≤ (rhinLiteRootLeft i.succ : ℝ) := by
    exact_mod_cast (rhinLite_positiveRootLeft i).le
  have hxpos : (0 : ℝ) < x :=
    lt_of_lt_of_le (by exact_mod_cast rhinLite_positiveRootLeft i) hx.1
  apply (div_le_iff₀ (pow_pos hxpos rhinLiteScale)).2
  calc
    rhinLiteKernelAbs x ≤ (rhinLiteBoundProduct i : ℝ) :=
      rhinLiteKernelAbs_le_boundProduct i hx
    _ ≤ (rhinLiteRootLeft i.succ : ℝ) ^ rhinLiteScale *
        (9 / 40 : ℝ) ^ rhinLiteScale := hcert
    _ ≤ x ^ rhinLiteScale * (9 / 40 : ℝ) ^ rhinLiteScale := by
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hleft hx.1 rhinLiteScale) (pow_nonneg (by norm_num) _)
    _ = (9 / 40 : ℝ) ^ rhinLiteScale * x ^ rhinLiteScale := mul_comm _ _

/-- **Tight per-bracket certificate on the `[3,4]` brackets.**  On the brackets with
`rootLeft ≥ 3` (namely the three critical brackets of `[3,4]`, `rootLeft ∈ {3.4748, 3.6524,
3.7809}`), the SAME rounded factor products already clear the strictly smaller target
`(2209/10000)^{scale}` — the `[3,4]` peak sits `exp(2.7)` below it, and the millionth-rounded factor
table has ample residual slack (verified `≥1.18` digits on the tightest bracket).  Finite
`native_decide` certificate.  (The `[2,3]` brackets do NOT satisfy this — the higher peak there
exceeds the target — so the `rootLeft ≥ 3` guard is essential.) -/
theorem rhinLite_boundProduct_certificate_tight (i : Fin 7)
    (hi : (3 : ℚ) ≤ rhinLiteRootLeft i.succ) :
    rhinLiteBoundProduct i ≤
      rhinLiteRootLeft i.succ ^ rhinLiteScale * (2209 / 10000 : ℚ) ^ rhinLiteScale := by
  native_decide +revert

set_option maxRecDepth 100000 in
/-- Tight decay on every certified `[3,4]` critical bracket (`rootLeft ≥ 3`): the weighted absolute
kernel is bounded by `(2209/10000)^{scale}`, strictly below the global `(9/40)^{scale}`. -/
theorem rhinLiteKernelAbs_div_pow_le_tight (i : Fin 7)
    (hi : (3 : ℚ) ≤ rhinLiteRootLeft i.succ) {x : ℝ}
    (hx : x ∈ Icc (rhinLiteRootLeft i.succ : ℝ) (rhinLiteRootRight i.succ : ℝ)) :
    rhinLiteKernelAbs x / x ^ rhinLiteScale ≤ (2209 / 10000 : ℝ) ^ rhinLiteScale := by
  have hcert' : (rhinLiteBoundProduct i : ℝ) ≤
      ((rhinLiteRootLeft i.succ ^ rhinLiteScale *
        (2209 / 10000 : ℚ) ^ rhinLiteScale : ℚ) : ℝ) := by
    exact_mod_cast rhinLite_boundProduct_certificate_tight i hi
  have hcert : (rhinLiteBoundProduct i : ℝ) ≤
      (rhinLiteRootLeft i.succ : ℝ) ^ rhinLiteScale *
        (2209 / 10000 : ℝ) ^ rhinLiteScale := by
    push_cast at hcert'
    exact hcert'
  have hleft : (0 : ℝ) ≤ (rhinLiteRootLeft i.succ : ℝ) := by
    exact_mod_cast (rhinLite_positiveRootLeft i).le
  have hxpos : (0 : ℝ) < x :=
    lt_of_lt_of_le (by exact_mod_cast rhinLite_positiveRootLeft i) hx.1
  apply (div_le_iff₀ (pow_pos hxpos rhinLiteScale)).2
  calc
    rhinLiteKernelAbs x ≤ (rhinLiteBoundProduct i : ℝ) :=
      rhinLiteKernelAbs_le_boundProduct i hx
    _ ≤ (rhinLiteRootLeft i.succ : ℝ) ^ rhinLiteScale *
        (2209 / 10000 : ℝ) ^ rhinLiteScale := hcert
    _ ≤ x ^ rhinLiteScale * (2209 / 10000 : ℝ) ^ rhinLiteScale := by
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hleft hx.1 rhinLiteScale) (pow_nonneg (by norm_num) _)
    _ = (2209 / 10000 : ℝ) ^ rhinLiteScale * x ^ rhinLiteScale := mul_comm _ _

end CollatzMoonshot.FrontA
