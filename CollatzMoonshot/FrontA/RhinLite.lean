/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.FrontA.RhinKernel
import Mathlib.Data.Nat.Choose.Vandermonde

/-!
# A certificate-friendly rationalization of Rhin's two-log kernel

Rhin's published six weights have denominator `10^6`.  For the weaker independent
re-derivation needed by Front A, the nearby weights

```text
  (705, 551, 449, 109, 39, 54) / 1000
```

are substantially easier to certify.  They retain all three exact load-bearing balances:
degree `2`, 2-adic content `2`, and 3-adic content `1`.  Passing to the subsequence whose
original index is `2000t` makes every factor exponent even, so both real integrands are
nonnegative and cancellation cannot hide their asymptotic size.

The central coefficient also admits deliberately coarse *integer* certificates.  At each
1000-index block, selecting respectively

```text
  (352, 330, 192, 61, 27, 38)
```

linear terms from the six factor groups gives more than `17^1000`.  Evaluation at the rational
Cauchy radius `ρ = 14/5` gives an upper bound below `18^1000`.  Thus the hard-looking contour
saddle in the published argument can be replaced by finite arithmetic plus positivity.

This file proves the exact balances and the two finite integer certificates.  It does not yet
assert the analytic interval bound; the next target is the rational certificate
`|H(x)| / x^1000 ≤ (9/40)^1000` on `[2,3]` and `[3,4]`.
-/

namespace CollatzMoonshot.FrontA

open Polynomial

def rhinLiteScale : ℕ := 1000

def rhinLiteW1 : ℕ := 705
def rhinLiteW2 : ℕ := 551
def rhinLiteW3 : ℕ := 449
def rhinLiteW4 : ℕ := 109
def rhinLiteW5 : ℕ := 39
def rhinLiteW6 : ℕ := 54

/-- The rationalized weights still give degree exactly `2`. -/
theorem rhinLite_degree_balance :
    rhinLiteW1 + rhinLiteW2 + rhinLiteW3 + rhinLiteW4 +
        2 * rhinLiteW5 + 2 * rhinLiteW6 = 2 * rhinLiteScale := by
  norm_num [rhinLiteW1, rhinLiteW2, rhinLiteW3, rhinLiteW4, rhinLiteW5, rhinLiteW6,
    rhinLiteScale]

/-- The rationalized weights still supply exactly two 2-adic units per index. -/
theorem rhinLite_v2_balance :
    rhinLiteW2 + 2 * rhinLiteW3 + 2 * rhinLiteW4 +
        3 * rhinLiteW5 + 4 * rhinLiteW6 = 2 * rhinLiteScale := by
  norm_num [rhinLiteW2, rhinLiteW3, rhinLiteW4, rhinLiteW5, rhinLiteW6, rhinLiteScale]

/-- The rationalized weights still supply exactly one 3-adic unit per index. -/
theorem rhinLite_v3_balance :
    rhinLiteW1 + rhinLiteW4 + 2 * rhinLiteW5 + 2 * rhinLiteW6 = rhinLiteScale := by
  norm_num [rhinLiteW1, rhinLiteW4, rhinLiteW5, rhinLiteW6, rhinLiteScale]

def rhinLiteS1 : ℕ := 352
def rhinLiteS2 : ℕ := 330
def rhinLiteS3 : ℕ := 192
def rhinLiteS4 : ℕ := 61
def rhinLiteS5 : ℕ := 27
def rhinLiteS6 : ℕ := 38

/-- The selected linear degrees add to the central index. -/
theorem rhinLite_selection_balance :
    rhinLiteS1 + rhinLiteS2 + rhinLiteS3 + rhinLiteS4 + rhinLiteS5 + rhinLiteS6 =
      rhinLiteScale := by
  norm_num [rhinLiteS1, rhinLiteS2, rhinLiteS3, rhinLiteS4, rhinLiteS5, rhinLiteS6,
    rhinLiteScale]

/-- Each selected degree fits in its factor group. -/
theorem rhinLite_selection_fits :
    rhinLiteS1 ≤ rhinLiteW1 ∧ rhinLiteS2 ≤ rhinLiteW2 ∧ rhinLiteS3 ≤ rhinLiteW3 ∧
      rhinLiteS4 ≤ rhinLiteW4 ∧ rhinLiteS5 ≤ rhinLiteW5 ∧ rhinLiteS6 ≤ rhinLiteW6 := by
  norm_num [rhinLiteS1, rhinLiteS2, rhinLiteS3, rhinLiteS4, rhinLiteS5, rhinLiteS6,
    rhinLiteW1, rhinLiteW2, rhinLiteW3, rhinLiteW4, rhinLiteW5, rhinLiteW6]

/-- One explicit positive contribution to the central coefficient in a 1000-index block.

For the two quadratic factors only their constant and linear terms are selected; their positive
quadratic terms can only increase the coefficient. -/
def rhinLiteBlockTerm : ℕ :=
  (rhinLiteW1.choose rhinLiteS1 * 3 ^ (rhinLiteW1 - rhinLiteS1)) *
  (rhinLiteW2.choose rhinLiteS2 * 2 ^ (rhinLiteW2 - rhinLiteS2)) *
  (rhinLiteW3.choose rhinLiteS3 * 4 ^ (rhinLiteW3 - rhinLiteS3)) *
  (rhinLiteW4.choose rhinLiteS4 * 5 ^ rhinLiteS4 * 12 ^ (rhinLiteW4 - rhinLiteS4)) *
  (rhinLiteW5.choose rhinLiteS5 * 102 ^ rhinLiteS5 * 144 ^ (rhinLiteW5 - rhinLiteS5)) *
  (rhinLiteW6.choose rhinLiteS6 * 108 ^ rhinLiteS6 * 144 ^ (rhinLiteW6 - rhinLiteS6))

/-- **Finite lower certificate:** the chosen contribution already exceeds `17^1000`. -/
theorem seventeen_pow_scale_le_rhinLiteBlockTerm :
    17 ^ rhinLiteScale ≤ rhinLiteBlockTerm := by
  native_decide

/-- **Finite upper certificate at `ρ = 14/5`.**

After clearing powers of `5`, this says that evaluation of the positive transform of the full
six-factor polynomial at `14/5`, divided by `(14/5)^1000`, is at most `18^1000`.
The factors evaluate to `29/5`, `24/5`, `34/5`, `26`, `14072/25`, and `14884/25`.
-/
theorem rhinLite_cauchy_radius_certificate :
    29 ^ rhinLiteW1 * 24 ^ rhinLiteW2 * 34 ^ rhinLiteW3 * 26 ^ rhinLiteW4 *
        14072 ^ rhinLiteW5 * 14884 ^ rhinLiteW6 ≤
      252 ^ rhinLiteScale * 5 ^ 891 := by
  native_decide

/-- A single term in Vandermonde's sum gives this useful supermultiplicativity inequality. -/
theorem choose_mul_choose_le_choose_add (m n i j : ℕ) :
    m.choose i * n.choose j ≤ (m + n).choose (i + j) := by
  rw [Nat.add_choose_eq]
  let f : ℕ × ℕ → ℕ := fun ij => m.choose ij.1 * n.choose ij.2
  have hm : (i, j) ∈ Finset.HasAntidiagonal.antidiagonal (i + j) := by
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
  change f (i, j) ≤ ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal (i + j), f ij
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hm

/-- Repeating a fixed block gives at least the corresponding power of its binomial coefficient. -/
theorem choose_pow_le_choose_mul (w s t : ℕ) :
    (w.choose s) ^ t ≤ (w * t).choose (s * t) := by
  induction t with
  | zero => simp
  | succ t ih =>
      calc
        (w.choose s) ^ (t + 1) = (w.choose s) ^ t * w.choose s := by rw [pow_succ]
        _ ≤ (w * t).choose (s * t) * w.choose s := Nat.mul_le_mul_right _ ih
        _ ≤ (w * t + w).choose (s * t + s) :=
          choose_mul_choose_le_choose_add (w * t) w (s * t) s
        _ = (w * (t + 1)).choose (s * (t + 1)) := by simp [Nat.mul_succ]

/-- A fixed constant/linear selection in one factor group is supermultiplicative over blocks. -/
theorem binomialBlock_pow_le (w s c l t : ℕ) :
    (w.choose s * l ^ s * c ^ (w - s)) ^ t ≤
      (w * t).choose (s * t) * l ^ (s * t) * c ^ (w * t - s * t) := by
  simp only [mul_pow, ← pow_mul, Nat.sub_mul]
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (choose_pow_le_choose_mul w s t))

/-- The same selected contribution in `t` repeated 1000-index blocks. -/
def rhinLiteSelectedTerm (t : ℕ) : ℕ :=
  ((rhinLiteW1 * t).choose (rhinLiteS1 * t) * 3 ^ (rhinLiteW1 * t - rhinLiteS1 * t)) *
  ((rhinLiteW2 * t).choose (rhinLiteS2 * t) * 2 ^ (rhinLiteW2 * t - rhinLiteS2 * t)) *
  ((rhinLiteW3 * t).choose (rhinLiteS3 * t) * 4 ^ (rhinLiteW3 * t - rhinLiteS3 * t)) *
  ((rhinLiteW4 * t).choose (rhinLiteS4 * t) * 5 ^ (rhinLiteS4 * t) *
    12 ^ (rhinLiteW4 * t - rhinLiteS4 * t)) *
  ((rhinLiteW5 * t).choose (rhinLiteS5 * t) * 102 ^ (rhinLiteS5 * t) *
    144 ^ (rhinLiteW5 * t - rhinLiteS5 * t)) *
  ((rhinLiteW6 * t).choose (rhinLiteS6 * t) * 108 ^ (rhinLiteS6 * t) *
    144 ^ (rhinLiteW6 * t - rhinLiteS6 * t))

/-- The one-block contribution injects into every repeated-block contribution. -/
theorem rhinLiteBlockTerm_pow_le_selectedTerm (t : ℕ) :
    rhinLiteBlockTerm ^ t ≤ rhinLiteSelectedTerm t := by
  simp only [rhinLiteBlockTerm, rhinLiteSelectedTerm, mul_pow]
  apply Nat.mul_le_mul
  · apply Nat.mul_le_mul
    · apply Nat.mul_le_mul
      · apply Nat.mul_le_mul
        · apply Nat.mul_le_mul
          · simpa [mul_pow] using binomialBlock_pow_le rhinLiteW1 rhinLiteS1 3 1 t
          · simpa [mul_pow] using binomialBlock_pow_le rhinLiteW2 rhinLiteS2 2 1 t
        · simpa [mul_pow] using binomialBlock_pow_le rhinLiteW3 rhinLiteS3 4 1 t
      · simpa [mul_pow] using binomialBlock_pow_le rhinLiteW4 rhinLiteS4 12 5 t
    · simpa [mul_pow] using binomialBlock_pow_le rhinLiteW5 rhinLiteS5 144 102 t
  · simpa [mul_pow] using binomialBlock_pow_le rhinLiteW6 rhinLiteS6 144 108 t

/-- **Uniform coefficient-term lower certificate:** the selected term grows at least as `17^n`
along the 1000-index subsequence. -/
theorem seventeen_pow_le_rhinLiteSelectedTerm (t : ℕ) :
    17 ^ (rhinLiteScale * t) ≤ rhinLiteSelectedTerm t := by
  rw [pow_mul]
  exact (Nat.pow_le_pow_left seventeen_pow_scale_le_rhinLiteBlockTerm t).trans
    (rhinLiteBlockTerm_pow_le_selectedTerm t)

/-! ## From the selected term to the actual positive polynomial coefficient -/

/-- Coefficientwise nonnegativity for rational polynomials. -/
def CoeffNonneg (p : ℚ[X]) := ∀ k, 0 ≤ p.coeff k

theorem CoeffNonneg.one : CoeffNonneg (1 : ℚ[X]) := by
  intro k
  cases k <;> simp [coeff_one]

theorem CoeffNonneg.mul {p q : ℚ[X]} (hp : CoeffNonneg p) (hq : CoeffNonneg q) :
    CoeffNonneg (p * q) := by
  intro k
  rw [coeff_mul]
  exact Finset.sum_nonneg fun ij _ => mul_nonneg (hp _) (hq _)

theorem CoeffNonneg.pow {p : ℚ[X]} (hp : CoeffNonneg p) (n : ℕ) : CoeffNonneg (p ^ n) := by
  induction n with
  | zero => exact CoeffNonneg.one
  | succ n ih => rw [pow_succ]; exact ih.mul hp

/-- A chosen convolution term is bounded by the corresponding product coefficient. -/
theorem coeff_mul_term_le {p q : ℚ[X]} (hp : CoeffNonneg p) (hq : CoeffNonneg q)
    (i j : ℕ) : p.coeff i * q.coeff j ≤ (p * q).coeff (i + j) := by
  rw [coeff_mul]
  let f : ℕ × ℕ → ℚ := fun ij => p.coeff ij.1 * q.coeff ij.2
  have hm : (i, j) ∈ Finset.HasAntidiagonal.antidiagonal (i + j) := by
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
  change f (i, j) ≤ ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal (i + j), f ij
  exact Finset.single_le_sum (fun _ _ => mul_nonneg (hp _) (hq _)) hm

/-- Six-fold version of `coeff_mul_term_le`, matching Rhin's six factor groups. -/
theorem six_coeff_product_le
    (p1 p2 p3 p4 p5 p6 : ℚ[X]) (k1 k2 k3 k4 k5 k6 : ℕ)
    (h1 : CoeffNonneg p1) (h2 : CoeffNonneg p2) (h3 : CoeffNonneg p3)
    (h4 : CoeffNonneg p4) (h5 : CoeffNonneg p5) (h6 : CoeffNonneg p6) :
    p1.coeff k1 * p2.coeff k2 * p3.coeff k3 * p4.coeff k4 *
        p5.coeff k5 * p6.coeff k6 ≤
      (p1 * p2 * p3 * p4 * p5 * p6).coeff (k1 + k2 + k3 + k4 + k5 + k6) := by
  have h12 : p1.coeff k1 * p2.coeff k2 ≤ (p1 * p2).coeff (k1 + k2) :=
    coeff_mul_term_le h1 h2 k1 k2
  have h123 : p1.coeff k1 * p2.coeff k2 * p3.coeff k3 ≤
      (p1 * p2 * p3).coeff (k1 + k2 + k3) := by
    calc
      _ ≤ (p1 * p2).coeff (k1 + k2) * p3.coeff k3 :=
        mul_le_mul_of_nonneg_right h12 (h3 _)
      _ ≤ _ := coeff_mul_term_le (h1.mul h2) h3 (k1 + k2) k3
  have h1234 : p1.coeff k1 * p2.coeff k2 * p3.coeff k3 * p4.coeff k4 ≤
      (p1 * p2 * p3 * p4).coeff (k1 + k2 + k3 + k4) := by
    calc
      _ ≤ (p1 * p2 * p3).coeff (k1 + k2 + k3) * p4.coeff k4 :=
        mul_le_mul_of_nonneg_right h123 (h4 _)
      _ ≤ _ := coeff_mul_term_le ((h1.mul h2).mul h3) h4 (k1 + k2 + k3) k4
  have h12345 : p1.coeff k1 * p2.coeff k2 * p3.coeff k3 * p4.coeff k4 *
      p5.coeff k5 ≤ (p1 * p2 * p3 * p4 * p5).coeff (k1 + k2 + k3 + k4 + k5) := by
    calc
      _ ≤ (p1 * p2 * p3 * p4).coeff (k1 + k2 + k3 + k4) * p5.coeff k5 :=
        mul_le_mul_of_nonneg_right h1234 (h5 _)
      _ ≤ _ := coeff_mul_term_le (((h1.mul h2).mul h3).mul h4) h5
        (k1 + k2 + k3 + k4) k5
  calc
    _ ≤ (p1 * p2 * p3 * p4 * p5).coeff (k1 + k2 + k3 + k4 + k5) * p6.coeff k6 :=
      mul_le_mul_of_nonneg_right h12345 (h6 _)
    _ ≤ _ := coeff_mul_term_le ((((h1.mul h2).mul h3).mul h4).mul h5) h6
      (k1 + k2 + k3 + k4 + k5) k6

/-- A positive constant/linear factor `c + lX`. -/
noncomputable def rhinLiteLinear (c l : ℕ) : ℚ[X] := C (c : ℚ) + C (l : ℚ) * X

theorem rhinLiteLinear_coeff_nonneg (c l : ℕ) : CoeffNonneg (rhinLiteLinear c l) := by
  intro k
  simp [rhinLiteLinear, coeff_X]
  positivity

/-- Exact binomial coefficient of `(c + lX)^n`. -/
theorem coeff_rhinLiteLinear_pow (c l n k : ℕ) (hl : l ≠ 0) (hk : k ≤ n) :
    ((rhinLiteLinear c l) ^ n).coeff k =
      (n.choose k : ℚ) * l ^ k * c ^ (n - k) := by
  have hln : (l : ℚ) ≠ 0 := by exact_mod_cast hl
  have hfrac : (l : ℚ) * ((c : ℚ) / l) = c := by field_simp
  have hp : rhinLiteLinear c l = C (l : ℚ) * (X + C ((c : ℚ) / l)) := by
    rw [rhinLiteLinear, mul_add, ← C_mul, hfrac]
    ac_rfl
  rw [hp, mul_pow, ← C_pow, coeff_C_mul, coeff_X_add_C_pow]
  rw [show n = k + (n - k) by omega, pow_add]
  simp [div_pow]
  field_simp [hln]

theorem rhinLiteLinear_pow_coeff_nonneg (c l n : ℕ) :
    CoeffNonneg ((rhinLiteLinear c l) ^ n) :=
  (rhinLiteLinear_coeff_nonneg c l).pow n

/-- The product obtained by dropping only the positive quadratic terms from `Q₅(-X), Q₆(-X)`. -/
noncomputable def rhinLiteMinorant (t : ℕ) : ℚ[X] :=
  (rhinLiteLinear 3 1) ^ (rhinLiteW1 * t) *
  (rhinLiteLinear 2 1) ^ (rhinLiteW2 * t) *
  (rhinLiteLinear 4 1) ^ (rhinLiteW3 * t) *
  (rhinLiteLinear 12 5) ^ (rhinLiteW4 * t) *
  (rhinLiteLinear 144 102) ^ (rhinLiteW5 * t) *
  (rhinLiteLinear 144 108) ^ (rhinLiteW6 * t)

/-- The selected integer term is genuinely one positive contribution to the central coefficient. -/
theorem rhinLiteSelectedTerm_le_coeff_minorant (t : ℕ) :
    (rhinLiteSelectedTerm t : ℚ) ≤ (rhinLiteMinorant t).coeff (rhinLiteScale * t) := by
  rcases rhinLite_selection_fits with ⟨h1, h2, h3, h4, h5, h6⟩
  have ht1 := Nat.mul_le_mul_right t h1
  have ht2 := Nat.mul_le_mul_right t h2
  have ht3 := Nat.mul_le_mul_right t h3
  have ht4 := Nat.mul_le_mul_right t h4
  have ht5 := Nat.mul_le_mul_right t h5
  have ht6 := Nat.mul_le_mul_right t h6
  have h := six_coeff_product_le
    ((rhinLiteLinear 3 1) ^ (rhinLiteW1 * t))
    ((rhinLiteLinear 2 1) ^ (rhinLiteW2 * t))
    ((rhinLiteLinear 4 1) ^ (rhinLiteW3 * t))
    ((rhinLiteLinear 12 5) ^ (rhinLiteW4 * t))
    ((rhinLiteLinear 144 102) ^ (rhinLiteW5 * t))
    ((rhinLiteLinear 144 108) ^ (rhinLiteW6 * t))
    (rhinLiteS1 * t) (rhinLiteS2 * t) (rhinLiteS3 * t) (rhinLiteS4 * t)
    (rhinLiteS5 * t) (rhinLiteS6 * t)
    (rhinLiteLinear_pow_coeff_nonneg 3 1 _) (rhinLiteLinear_pow_coeff_nonneg 2 1 _)
    (rhinLiteLinear_pow_coeff_nonneg 4 1 _) (rhinLiteLinear_pow_coeff_nonneg 12 5 _)
    (rhinLiteLinear_pow_coeff_nonneg 144 102 _) (rhinLiteLinear_pow_coeff_nonneg 144 108 _)
  rw [coeff_rhinLiteLinear_pow 3 1 _ _ (by norm_num) ht1,
      coeff_rhinLiteLinear_pow 2 1 _ _ (by norm_num) ht2,
      coeff_rhinLiteLinear_pow 4 1 _ _ (by norm_num) ht3,
      coeff_rhinLiteLinear_pow 12 5 _ _ (by norm_num) ht4,
      coeff_rhinLiteLinear_pow 144 102 _ _ (by norm_num) ht5,
      coeff_rhinLiteLinear_pow 144 108 _ _ (by norm_num) ht6] at h
  have hsum := congrArg (fun n : ℕ => n * t) rhinLite_selection_balance
  simp only [Nat.add_mul] at hsum
  rw [← hsum]
  simpa [rhinLiteSelectedTerm, rhinLiteMinorant] using h

/-- Coefficientwise comparison of rational polynomials. -/
def CoeffLE (p q : ℚ[X]) := ∀ k, p.coeff k ≤ q.coeff k

theorem CoeffLE.refl (p : ℚ[X]) : CoeffLE p p := fun _ => le_rfl

theorem CoeffLE.mul {p q r s : ℚ[X]} (hpq : CoeffLE p q) (hrs : CoeffLE r s)
    (hr : CoeffNonneg r) (hq : CoeffNonneg q) : CoeffLE (p * r) (q * s) := by
  intro k
  rw [coeff_mul, coeff_mul]
  apply Finset.sum_le_sum
  intro ij _
  exact mul_le_mul (hpq _) (hrs _) (hr _) (hq _)

theorem CoeffLE.pow {p q : ℚ[X]} (hpq : CoeffLE p q)
    (hp : CoeffNonneg p) (hq : CoeffNonneg q) (n : ℕ) : CoeffLE (p ^ n) (q ^ n) := by
  induction n with
  | zero => exact CoeffLE.refl 1
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact ih.mul hpq hp (hq.pow n)

theorem CoeffNonneg.add {p q : ℚ[X]} (hp : CoeffNonneg p) (hq : CoeffNonneg q) :
    CoeffNonneg (p + q) := by
  intro k
  rw [coeff_add]
  exact add_nonneg (hp _) (hq _)

/-- A positive quadratic `c + lX + qX²`. -/
noncomputable def rhinLiteQuadratic (c l q : ℕ) : ℚ[X] :=
  rhinLiteLinear c l + C (q : ℚ) * X ^ 2

theorem rhinLiteQuadratic_coeff_nonneg (c l q : ℕ) :
    CoeffNonneg (rhinLiteQuadratic c l q) := by
  apply (rhinLiteLinear_coeff_nonneg c l).add
  intro k
  rw [coeff_C_mul_X_pow]
  split <;> positivity

theorem rhinLiteLinear_coeff_le_quadratic (c l q : ℕ) :
    CoeffLE (rhinLiteLinear c l) (rhinLiteQuadratic c l q) := by
  intro k
  rw [rhinLiteQuadratic, coeff_add]
  exact le_add_of_nonneg_right ((by
    rw [coeff_C_mul_X_pow]
    split <;> positivity) : (0 : ℚ) ≤ (C (q : ℚ) * X ^ 2).coeff k)

/-- The positive transform of the complete rationalized Rhin polynomial. -/
noncomputable def rhinLitePositive (t : ℕ) : ℚ[X] :=
  (rhinLiteLinear 3 1) ^ (rhinLiteW1 * t) *
  (rhinLiteLinear 2 1) ^ (rhinLiteW2 * t) *
  (rhinLiteLinear 4 1) ^ (rhinLiteW3 * t) *
  (rhinLiteLinear 12 5) ^ (rhinLiteW4 * t) *
  (rhinLiteQuadratic 144 102 17) ^ (rhinLiteW5 * t) *
  (rhinLiteQuadratic 144 108 19) ^ (rhinLiteW6 * t)

theorem rhinLiteMinorant_coeff_le_positive (t k : ℕ) :
    (rhinLiteMinorant t).coeff k ≤ (rhinLitePositive t).coeff k := by
  let f1 := (rhinLiteLinear 3 1) ^ (rhinLiteW1 * t)
  let f2 := (rhinLiteLinear 2 1) ^ (rhinLiteW2 * t)
  let f3 := (rhinLiteLinear 4 1) ^ (rhinLiteW3 * t)
  let f4 := (rhinLiteLinear 12 5) ^ (rhinLiteW4 * t)
  let l5 := (rhinLiteLinear 144 102) ^ (rhinLiteW5 * t)
  let l6 := (rhinLiteLinear 144 108) ^ (rhinLiteW6 * t)
  let q5 := (rhinLiteQuadratic 144 102 17) ^ (rhinLiteW5 * t)
  let q6 := (rhinLiteQuadratic 144 108 19) ^ (rhinLiteW6 * t)
  have hf1 : CoeffNonneg f1 := rhinLiteLinear_pow_coeff_nonneg 3 1 _
  have hf2 : CoeffNonneg f2 := rhinLiteLinear_pow_coeff_nonneg 2 1 _
  have hf3 : CoeffNonneg f3 := rhinLiteLinear_pow_coeff_nonneg 4 1 _
  have hf4 : CoeffNonneg f4 := rhinLiteLinear_pow_coeff_nonneg 12 5 _
  have hl5 : CoeffNonneg l5 := rhinLiteLinear_pow_coeff_nonneg 144 102 _
  have hl6 : CoeffNonneg l6 := rhinLiteLinear_pow_coeff_nonneg 144 108 _
  have hq5 : CoeffNonneg q5 := (rhinLiteQuadratic_coeff_nonneg 144 102 17).pow _
  have hq6 : CoeffNonneg q6 := (rhinLiteQuadratic_coeff_nonneg 144 108 19).pow _
  have h5 : CoeffLE l5 q5 := (rhinLiteLinear_coeff_le_quadratic 144 102 17).pow
    (rhinLiteLinear_coeff_nonneg 144 102) (rhinLiteQuadratic_coeff_nonneg 144 102 17) _
  have h6 : CoeffLE l6 q6 := (rhinLiteLinear_coeff_le_quadratic 144 108 19).pow
    (rhinLiteLinear_coeff_nonneg 144 108) (rhinLiteQuadratic_coeff_nonneg 144 108 19) _
  have hpre : CoeffNonneg (f1 * f2 * f3 * f4) := ((hf1.mul hf2).mul hf3).mul hf4
  have hpreq5 : CoeffNonneg (f1 * f2 * f3 * f4 * q5) := hpre.mul hq5
  have hlepre : CoeffLE (f1 * f2 * f3 * f4) (f1 * f2 * f3 * f4) := CoeffLE.refl _
  exact ((hlepre.mul h5 hl5 hpre).mul h6 hl6 hpreq5) k

/-- **Central-coefficient lower bound:** no contour asymptotics or cancellation theorem is needed. -/
theorem seventeen_pow_le_rhinLitePositive_coeff (t : ℕ) :
    (17 ^ (rhinLiteScale * t) : ℚ) ≤
      (rhinLitePositive t).coeff (rhinLiteScale * t) := by
  have hnat := seventeen_pow_le_rhinLiteSelectedTerm t
  have hcast : (17 ^ (rhinLiteScale * t) : ℚ) ≤ (rhinLiteSelectedTerm t : ℚ) := by
    exact_mod_cast hnat
  exact hcast.trans ((rhinLiteSelectedTerm_le_coeff_minorant t).trans
    (rhinLiteMinorant_coeff_le_positive t _))

/-! ## A rational Cauchy certificate for the matching upper bound -/

set_option maxRecDepth 10000 in
/-- Rational form of `rhinLite_cauchy_radius_certificate`, before polynomial evaluation is
introduced. -/
theorem rhinLite_cauchy_rational_certificate :
    ((29 / 5 : ℚ) ^ rhinLiteW1 * (24 / 5 : ℚ) ^ rhinLiteW2 *
        (34 / 5 : ℚ) ^ rhinLiteW3 * 26 ^ rhinLiteW4 *
        (14072 / 25 : ℚ) ^ rhinLiteW5 * (14884 / 25 : ℚ) ^ rhinLiteW6) ≤
      (14 / 5 : ℚ) ^ rhinLiteScale * 18 ^ rhinLiteScale := by
  have h := rhinLite_cauchy_radius_certificate
  dsimp [rhinLiteW1, rhinLiteW2, rhinLiteW3, rhinLiteW4, rhinLiteW5, rhinLiteW6,
    rhinLiteScale] at h ⊢
  field_simp
  exact_mod_cast h

/-- Direct evaluation of the six positive factors at the rational radius `14/5`. -/
theorem rhinLitePositive_eval_one : (rhinLitePositive 1).eval (14 / 5 : ℚ) =
    ((29 / 5 : ℚ) ^ rhinLiteW1 * (24 / 5 : ℚ) ^ rhinLiteW2 *
        (34 / 5 : ℚ) ^ rhinLiteW3 * 26 ^ rhinLiteW4 *
        (14072 / 25 : ℚ) ^ rhinLiteW5 * (14884 / 25 : ℚ) ^ rhinLiteW6) := by
  simp [rhinLitePositive, rhinLiteLinear, rhinLiteQuadratic]
  norm_num

theorem rhinLitePositive_coeff_nonneg (t : ℕ) : CoeffNonneg (rhinLitePositive t) := by
  exact (((((rhinLiteLinear_pow_coeff_nonneg 3 1 _).mul
    (rhinLiteLinear_pow_coeff_nonneg 2 1 _)).mul
    (rhinLiteLinear_pow_coeff_nonneg 4 1 _)).mul
    (rhinLiteLinear_pow_coeff_nonneg 12 5 _)).mul
    ((rhinLiteQuadratic_coeff_nonneg 144 102 17).pow _)).mul
    ((rhinLiteQuadratic_coeff_nonneg 144 108 19).pow _)

/-- Every nonnegative polynomial coefficient, multiplied by its evaluation power, is bounded by
the full evaluation. -/
theorem coeff_mul_pow_le_eval {p : ℚ[X]} (hp : CoeffNonneg p) {x : ℚ} (hx : 0 ≤ x) (k : ℕ) :
    p.coeff k * x ^ k ≤ p.eval x := by
  by_cases hk : k ≤ p.natDegree
  · rw [eval_eq_sum_range]
    exact Finset.single_le_sum
      (fun i _ => mul_nonneg (hp _) (pow_nonneg hx _))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  · have hz : p.coeff k = 0 := coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hk)
    rw [hz, zero_mul, eval_eq_sum_range]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hp _) (pow_nonneg hx _)

/-- Evaluation of every repeated block is at most the corresponding `18`-geometric bound. -/
theorem rhinLitePositive_eval_le (t : ℕ) :
    (rhinLitePositive t).eval (14 / 5 : ℚ) ≤
      (14 / 5 : ℚ) ^ (rhinLiteScale * t) * 18 ^ (rhinLiteScale * t) := by
  rw [show (rhinLitePositive t).eval (14 / 5 : ℚ) =
      ((rhinLitePositive 1).eval (14 / 5 : ℚ)) ^ t by
    simp [rhinLitePositive, pow_mul, mul_pow]]
  calc
    _ ≤ (((14 / 5 : ℚ) ^ rhinLiteScale * 18 ^ rhinLiteScale) ^ t) :=
      pow_le_pow_left₀ (by rw [rhinLitePositive_eval_one]; positivity)
        (rhinLitePositive_eval_one.le.trans rhinLite_cauchy_rational_certificate) t
    _ = _ := by simp [mul_pow, pow_mul]

/-- **Central-coefficient upper bound:** rational Cauchy evaluation gives `Bₙ ≤ 18ⁿ`. -/
theorem rhinLitePositive_coeff_le_eighteen_pow (t : ℕ) :
    (rhinLitePositive t).coeff (rhinLiteScale * t) ≤
      (18 : ℚ) ^ (rhinLiteScale * t) := by
  have hterm := coeff_mul_pow_le_eval (rhinLitePositive_coeff_nonneg t)
    (show (0 : ℚ) ≤ 14 / 5 by norm_num) (rhinLiteScale * t)
  have h := hterm.trans (rhinLitePositive_eval_le t)
  have hpos : 0 < (14 / 5 : ℚ) ^ (rhinLiteScale * t) := pow_pos (by norm_num) _
  exact le_of_mul_le_mul_right (by simpa [mul_comm] using h) hpos

/-! ## The degree-eight critical polynomial for the interval remainder -/

noncomputable def rhinLiteQ1 : ℤ[X] := X - C 3
noncomputable def rhinLiteQ2 : ℤ[X] := X - C 2
noncomputable def rhinLiteQ3 : ℤ[X] := X - C 4
noncomputable def rhinLiteQ4 : ℤ[X] := C 5 * X - C 12
noncomputable def rhinLiteQ5 : ℤ[X] := C 17 * X ^ 2 - C 102 * X + C 144
noncomputable def rhinLiteQ6 : ℤ[X] := C 19 * X ^ 2 - C 108 * X + C 144

noncomputable def rhinLiteBaseProduct : ℤ[X] :=
  rhinLiteQ1 * rhinLiteQ2 * rhinLiteQ3 * rhinLiteQ4 * rhinLiteQ5 * rhinLiteQ6

/-- Numerator of the logarithmic derivative of
`(Q₁^705 Q₂^551 Q₃^449 Q₄^109 Q₅^39 Q₆^54) / x^1000`.

Factoring out the high powers leaves this polynomial of degree only eight. -/
noncomputable def rhinLiteCriticalPolynomial : ℤ[X] :=
  X *
    (C (rhinLiteW1 : ℤ) * rhinLiteQ1.derivative *
        (rhinLiteQ2 * rhinLiteQ3 * rhinLiteQ4 * rhinLiteQ5 * rhinLiteQ6) +
      C (rhinLiteW2 : ℤ) * rhinLiteQ2.derivative *
        (rhinLiteQ1 * rhinLiteQ3 * rhinLiteQ4 * rhinLiteQ5 * rhinLiteQ6) +
      C (rhinLiteW3 : ℤ) * rhinLiteQ3.derivative *
        (rhinLiteQ1 * rhinLiteQ2 * rhinLiteQ4 * rhinLiteQ5 * rhinLiteQ6) +
      C (rhinLiteW4 : ℤ) * rhinLiteQ4.derivative *
        (rhinLiteQ1 * rhinLiteQ2 * rhinLiteQ3 * rhinLiteQ5 * rhinLiteQ6) +
      C (rhinLiteW5 : ℤ) * rhinLiteQ5.derivative *
        (rhinLiteQ1 * rhinLiteQ2 * rhinLiteQ3 * rhinLiteQ4 * rhinLiteQ6) +
      C (rhinLiteW6 : ℤ) * rhinLiteQ6.derivative *
        (rhinLiteQ1 * rhinLiteQ2 * rhinLiteQ3 * rhinLiteQ4 * rhinLiteQ5)) -
    C (rhinLiteScale : ℤ) * rhinLiteBaseProduct

noncomputable def rhinLiteCriticalExplicit : ℤ[X] :=
  C (-5971968000) + C 13269961728 * X - C 11385536256 * X ^ 2 +
    C 4171412736 * X ^ 3 - C 28892592 * X ^ 4 - C 519935532 * X ^ 5 +
    C 185301612 * X ^ 6 - C 27888891 * X ^ 7 + C 1615000 * X ^ 8

/-- **Finite bridge to the Sturm certificate:** the factored logarithmic derivative really is the
explicit degree-eight polynomial used by `experiments/rhin_lite_certificate.py`. -/
theorem rhinLiteCriticalPolynomial_eq_explicit :
    rhinLiteCriticalPolynomial = rhinLiteCriticalExplicit := by
  norm_num [rhinLiteCriticalPolynomial, rhinLiteCriticalExplicit, rhinLiteBaseProduct,
    rhinLiteQ1, rhinLiteQ2, rhinLiteQ3, rhinLiteQ4, rhinLiteQ5, rhinLiteQ6,
    rhinLiteW1, rhinLiteW2, rhinLiteW3, rhinLiteW4, rhinLiteW5, rhinLiteW6, rhinLiteScale]
  ring

end CollatzMoonshot.FrontA
