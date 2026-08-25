/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.FrontA.RhinLite
import Mathlib.Analysis.Polynomial.Order

/-!
# Exhausting the critical points of the Rhin-lite kernel

The logarithmic derivative from `RhinLite.lean` has numerator of degree eight.  A Sturm
calculation initially suggested isolating its seven roots in `(2,4)`.  There is a substantially
smaller certificate: the same polynomial changes sign in seven disjoint millionth-wide intervals
inside `(2,4)`, and once more in `(-3,-2)`.  The intermediate value theorem therefore supplies
eight distinct real roots.  A nonzero degree-eight polynomial has no room for another root.

Thus no formal Sturm theory is needed.  This file reflects the rational sign certificate and
proves that the eight intervals exhaust all real roots.
-/

namespace CollatzMoonshot.FrontA

open Polynomial Set

/-- Left endpoints of the eight sign-changing brackets.  Index zero is the auxiliary negative
root; the remaining seven brackets contain all critical points relevant on `[2,4]`. -/
def rhinLiteRootLeft : Fin 8 → ℚ :=
  ![-3, 2115103 / 1000000, 2223243 / 1000000, 2312512 / 1000000,
    2520895 / 1000000, 3474818 / 1000000, 3652359 / 1000000, 3780897 / 1000000]

/-- Right endpoints of the eight sign-changing brackets. -/
def rhinLiteRootRight : Fin 8 → ℚ :=
  ![-2, 2115104 / 1000000, 2223244 / 1000000, 2312513 / 1000000,
    2520896 / 1000000, 3474819 / 1000000, 3652360 / 1000000, 3780898 / 1000000]

/-- Horner evaluation of the explicit critical polynomial over the rationals.  Keeping this
function computational makes the endpoint sign checks a small `native_decide` certificate. -/
def rhinLiteCriticalValueQ (x : ℚ) : ℚ :=
  ((((((((1615000 * x - 27888891) * x + 185301612) * x - 519935532) * x - 28892592) *
      x + 4171412736) * x - 11385536256) * x + 13269961728) * x - 5971968000)

/-- Every listed bracket is nonempty. -/
theorem rhinLite_rootBracket_lt (i : Fin 8) :
    rhinLiteRootLeft i < rhinLiteRootRight i := by
  native_decide +revert

/-- The brackets are strictly ordered and hence pairwise disjoint. -/
theorem rhinLite_rootBrackets_separated (i j : Fin 8) (hij : i < j) :
    rhinLiteRootRight i < rhinLiteRootLeft j := by
  native_decide +revert

/-- The exact rational endpoint values have opposite signs in all eight brackets. -/
theorem rhinLite_critical_sign_change (i : Fin 8) :
    rhinLiteCriticalValueQ (rhinLiteRootLeft i) *
        rhinLiteCriticalValueQ (rhinLiteRootRight i) < 0 := by
  native_decide +revert

/-- The explicit critical polynomial, now viewed over the reals. -/
noncomputable def rhinLiteCriticalReal : ℝ[X] :=
  rhinLiteCriticalExplicit.map (Int.castRingHom ℝ)

/-- Its real evaluation is the same Horner expression used by the rational certificate. -/
theorem rhinLiteCriticalReal_eval (x : ℝ) :
    rhinLiteCriticalReal.eval x =
      ((((((((1615000 * x - 27888891) * x + 185301612) * x - 519935532) * x - 28892592) *
        x + 4171412736) * x - 11385536256) * x + 13269961728) * x - 5971968000) := by
  simp [rhinLiteCriticalReal, rhinLiteCriticalExplicit]
  ring

/-- Evaluation commutes with casting a rational endpoint to the reals. -/
theorem rhinLiteCriticalReal_eval_rat (x : ℚ) :
    rhinLiteCriticalReal.eval (x : ℝ) = (rhinLiteCriticalValueQ x : ℝ) := by
  rw [rhinLiteCriticalReal_eval]
  norm_num [rhinLiteCriticalValueQ]

theorem rhinLite_critical_real_sign_change (i : Fin 8) :
    rhinLiteCriticalReal.eval (rhinLiteRootLeft i : ℝ) *
        rhinLiteCriticalReal.eval (rhinLiteRootRight i : ℝ) < 0 := by
  rw [rhinLiteCriticalReal_eval_rat, rhinLiteCriticalReal_eval_rat]
  exact_mod_cast rhinLite_critical_sign_change i

/-- A continuous real polynomial whose endpoint values have negative product has a zero between
the endpoints. -/
theorem exists_polynomial_root_of_eval_mul_neg {p : ℝ[X]} {a b : ℝ} (hab : a ≤ b)
    (hneg : p.eval a * p.eval b < 0) :
    ∃ x ∈ Icc a b, p.eval x = 0 := by
  have hz : (0 : ℝ) ∈ uIcc (p.eval a) (p.eval b) := by
    rw [mem_uIcc]
    rcases (mul_neg_iff.mp hneg) with h | h
    · exact Or.inr ⟨h.2.le, h.1.le⟩
    · exact Or.inl ⟨h.1.le, h.2.le⟩
  obtain ⟨x, hx, heval⟩ :=
    (intermediate_value_uIcc p.continuous.continuousOn) hz
  refine ⟨x, ?_, heval⟩
  simpa [uIcc_of_le hab] using hx

/-- Each of the eight rational brackets contains a real root. -/
theorem exists_rhinLiteCriticalRoot (i : Fin 8) :
    ∃ x : ℝ, x ∈ Icc (rhinLiteRootLeft i : ℝ) (rhinLiteRootRight i : ℝ) ∧
      rhinLiteCriticalReal.eval x = 0 := by
  apply exists_polynomial_root_of_eval_mul_neg
  · exact_mod_cast (rhinLite_rootBracket_lt i).le
  · exact rhinLite_critical_real_sign_change i

/-- One chosen root in each bracket. -/
noncomputable def rhinLiteCriticalRoot (i : Fin 8) : ℝ :=
  Classical.choose (exists_rhinLiteCriticalRoot i)

theorem rhinLiteCriticalRoot_mem (i : Fin 8) :
    rhinLiteCriticalRoot i ∈
      Icc (rhinLiteRootLeft i : ℝ) (rhinLiteRootRight i : ℝ) :=
  (Classical.choose_spec (exists_rhinLiteCriticalRoot i)).1

theorem rhinLiteCriticalRoot_eval (i : Fin 8) :
    rhinLiteCriticalReal.eval (rhinLiteCriticalRoot i) = 0 :=
  (Classical.choose_spec (exists_rhinLiteCriticalRoot i)).2

/-- Strictly separated brackets make the chosen roots strictly increasing. -/
theorem rhinLiteCriticalRoot_strictMono : StrictMono rhinLiteCriticalRoot := by
  intro i j hij
  have hsep : (rhinLiteRootRight i : ℝ) < (rhinLiteRootLeft j : ℝ) := by
    exact_mod_cast rhinLite_rootBrackets_separated i j hij
  exact lt_of_le_of_lt (rhinLiteCriticalRoot_mem i).2
    (lt_of_lt_of_le hsep (rhinLiteCriticalRoot_mem j).1)

theorem rhinLiteCriticalRoot_injective : Function.Injective rhinLiteCriticalRoot :=
  rhinLiteCriticalRoot_strictMono.injective

/-- The explicit real critical polynomial really has degree eight. -/
theorem rhinLiteCriticalReal_natDegree : rhinLiteCriticalReal.natDegree = 8 := by
  change (rhinLiteCriticalExplicit.map (Int.castRingHom ℝ)).natDegree = 8
  rw [natDegree_map_eq_of_injective (f := Int.castRingHom ℝ) Int.cast_injective]
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · simp only [rhinLiteCriticalExplicit]
    compute_degree
  · norm_num [rhinLiteCriticalExplicit, coeff_X]

theorem rhinLiteCriticalReal_ne_zero : rhinLiteCriticalReal ≠ 0 := by
  intro h
  have := rhinLiteCriticalReal_natDegree
  simp [h] at this

/-- The eight sign-change roots exhaust the real root finset. -/
theorem rhinLiteCritical_roots_toFinset_eq :
    rhinLiteCriticalReal.roots.toFinset =
      Finset.univ.image rhinLiteCriticalRoot := by
  classical
  apply Finset.Subset.antisymm
  · intro x hx
    by_contra hnot
    have himage : Finset.univ.image rhinLiteCriticalRoot ⊆
        rhinLiteCriticalReal.roots.toFinset := by
      intro y hy
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      rw [Multiset.mem_toFinset, rhinLiteCriticalReal.mem_roots rhinLiteCriticalReal_ne_zero]
      exact rhinLiteCriticalRoot_eval i
    have hcardRoots : rhinLiteCriticalReal.roots.toFinset.card ≤ 8 := by
      calc
        _ ≤ rhinLiteCriticalReal.roots.card := Multiset.toFinset_card_le _
        _ ≤ rhinLiteCriticalReal.natDegree := Polynomial.card_roots' _
        _ = 8 := rhinLiteCriticalReal_natDegree
    have hcardImage : (Finset.univ.image rhinLiteCriticalRoot).card = 8 := by
      rw [Finset.card_image_of_injective _ rhinLiteCriticalRoot_injective]
      simp
    have hproper : Finset.univ.image rhinLiteCriticalRoot ⊂
        rhinLiteCriticalReal.roots.toFinset :=
      ssubset_iff_subset_ne.mpr ⟨himage, fun heq ↦ hnot (heq ▸ hx)⟩
    have := Finset.card_lt_card hproper
    omega
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    rw [Multiset.mem_toFinset, rhinLiteCriticalReal.mem_roots rhinLiteCriticalReal_ne_zero]
    exact rhinLiteCriticalRoot_eval i

/-- **Root exhaustion certificate.** Every real root lies in one of the eight certified rational
brackets. -/
theorem rhinLiteCriticalRoot_exhaustive {x : ℝ} (hx : rhinLiteCriticalReal.eval x = 0) :
    ∃ i : Fin 8,
      x ∈ Icc (rhinLiteRootLeft i : ℝ) (rhinLiteRootRight i : ℝ) := by
  have hxroots : x ∈ rhinLiteCriticalReal.roots.toFinset := by
    rw [Multiset.mem_toFinset, rhinLiteCriticalReal.mem_roots rhinLiteCriticalReal_ne_zero]
    exact hx
  rw [rhinLiteCritical_roots_toFinset_eq] at hxroots
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hxroots
  exact ⟨i, rhinLiteCriticalRoot_mem i⟩

/-- On `[2,4]` the auxiliary negative bracket is impossible, leaving precisely the seven tiny
positive brackets. -/
theorem rhinLiteCriticalRoot_exhaustive_Icc {x : ℝ} (hx24 : x ∈ Icc (2 : ℝ) 4)
    (hx : rhinLiteCriticalReal.eval x = 0) :
    ∃ i : Fin 8, i ≠ 0 ∧
      x ∈ Icc (rhinLiteRootLeft i : ℝ) (rhinLiteRootRight i : ℝ) := by
  obtain ⟨i, hi⟩ := rhinLiteCriticalRoot_exhaustive hx
  refine ⟨i, ?_, hi⟩
  intro hzero
  subst i
  norm_num [rhinLiteRootRight] at hi
  linarith [hx24.1]

/-- Convenient reindexing of the seven positive brackets. -/
theorem rhinLiteCriticalRoot_exhaustive_positive {x : ℝ} (hx24 : x ∈ Icc (2 : ℝ) 4)
    (hx : rhinLiteCriticalReal.eval x = 0) :
    ∃ i : Fin 7,
      x ∈ Icc (rhinLiteRootLeft i.succ : ℝ) (rhinLiteRootRight i.succ : ℝ) := by
  obtain ⟨i, hi0, hi⟩ := rhinLiteCriticalRoot_exhaustive_Icc hx24 hx
  refine ⟨i.pred hi0, ?_⟩
  simpa using hi

end CollatzMoonshot.FrontA
