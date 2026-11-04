/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.OrbitWordLawProb

/-!
# The orbit word law: logarithmic density

Open nodes are `Prop`s here, with their `sorry`s in `OrbitWordLaw.lean`.

* `LogDens0 P`: the starts satisfying `P` have logarithmic density `0`, in the form that
  `OrbitWordLaw` uses (`orbitWordLaw_iff`).
* Windows give density (`LogDens0OfWindow`): `[1, X]` is covered by windows `[y, y^α]`, each
  of log-weight `≍ log y`, and the exceptional probability tends to `0`, so the exceptional
  log-weight is `o(log X)`.
* Odd parts (`LogDens0OddPart`): the starts `2^a m` with `m` exceptional carry at most twice the
  log-weight of the exceptional `m`.
* Large 2-adic valuation (`SummableLargeTwoAdic`): the starts `2^a m` with
  `a > ε size m` have finite log-weight.
* The even reduction (`NotBadStartOfGoodOdd`): `2^a m` reads `a` zeros and then the letters of
  `m`, so it is good once `m` is good over `4.2 size m` letters and `a` is small.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord
open TaoCollatz

open Classical in
/-- The starts satisfying `P` have logarithmic density `0`. -/
def LogDens0 (P : ℕ → Prop) : Prop :=
  Tendsto (fun X : ℕ => (∑ n ∈ (Finset.Ico 1 X).filter P, (1 : ℝ) / n) / Real.log X)
    atTop (𝓝 0)

/-- `OrbitWordLaw` is `LogDens0` of the bad starts. -/
theorem orbitWordLaw_iff (C : ℕ) :
    OrbitWordLaw C ↔ ∀ (u : List Bool) (δ : ℝ), 0 < δ → LogDens0 (BadStart C u δ) := by
  rfl

open Classical in
/-- The log-weight below `X`, over `log X`. -/
theorem logDens0_def (P : ℕ → Prop) : LogDens0 P ↔ Tendsto
    (fun X : ℕ => (∑ n ∈ (Finset.Ico 1 X).filter P, (1 : ℝ) / n) / Real.log X) atTop (𝓝 0) :=
  Iff.rfl

open Classical in
theorem logWeight_nonneg (P : ℕ → Prop) (X : ℕ) :
    0 ≤ (∑ n ∈ (Finset.Ico 1 X).filter P, (1 : ℝ) / n) / Real.log X :=
  div_nonneg (Finset.sum_nonneg fun n _ => by positivity) (Real.log_natCast_nonneg X)

/-- Fewer starts, smaller density. -/
theorem LogDens0.mono {P Q : ℕ → Prop} (hQ : LogDens0 Q) (h : ∀ n, P n → Q n) : LogDens0 P := by
  classical
  refine squeeze_zero (fun X => logWeight_nonneg P X) (fun X => ?_) hQ
  refine div_le_div_of_nonneg_right ?_ (Real.log_natCast_nonneg X)
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) fun n _ _ => by positivity
  simp only [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, h n hn.2⟩

/-- Density `0` is closed under unions. -/
theorem LogDens0.or {P Q : ℕ → Prop} (hP : LogDens0 P) (hQ : LogDens0 Q) :
    LogDens0 (fun n => P n ∨ Q n) := by
  classical
  have hsum := hP.add hQ
  rw [add_zero] at hsum
  refine squeeze_zero (fun X => logWeight_nonneg _ X) (fun X => ?_) hsum
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ (Real.log_natCast_nonneg X)
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (t := (Finset.Ico 1 X).filter P ∪
    (Finset.Ico 1 X).filter Q) (fun n hn => ?_) fun n _ _ => by positivity) ?_
  · simp only [Finset.mem_filter, Finset.mem_union] at hn ⊢
    rcases hn.2 with h | h
    · exact Or.inl ⟨hn.1, h⟩
    · exact Or.inr ⟨hn.1, h⟩
  · rw [← Finset.sum_union_inter]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun n _ => by positivity)

open Classical in
/-- Finite log-weight has density `0`. -/
theorem logDens0_of_summable {P : ℕ → Prop}
    (h : Summable fun n : ℕ => if P n then (1 : ℝ) / n else 0) : LogDens0 P := by
  have hlim : Tendsto (fun X : ℕ => (∑' n : ℕ, if P n then (1 : ℝ) / n else 0) / Real.log X)
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  refine squeeze_zero (fun X => logWeight_nonneg P X) (fun X => ?_) hlim
  refine div_le_div_of_nonneg_right ?_ (Real.log_natCast_nonneg X)
  rw [Finset.sum_filter]
  exact h.sum_le_tsum _ fun n _ => by split_ifs <;> positivity

/-- A bounded set has density `0`. -/
theorem logDens0_of_bdd {P : ℕ → Prop} {B : ℕ} (h : ∀ n, P n → n ≤ B) : LogDens0 P := by
  classical
  refine logDens0_of_summable (summable_of_ne_finset_zero (s := Finset.range (B + 1))
    fun n hn => ?_)
  rw [if_neg]
  intro hP
  exact hn (Finset.mem_range.mpr (Nat.lt_succ_of_le (h n hP)))

/-- **Node: windows give density.**  If the `winLaw x`-probability of `B` tends to `0`, the odd starts in
`B` have logarithmic density `0`. -/
def LogDens0OfWindow : Prop :=
  ∀ B : ℕ → Prop, Tendsto (fun x => (winLaw x).expect (Set.indicator {n | B n} 1)) atTop (𝓝 0) →
    LogDens0 (fun n => n % 2 = 1 ∧ B n)

/-- **Node: odd parts.**  If the odd starts in `B` have density `0`, so do the starts whose odd part is
in `B`. -/
def LogDens0OddPart : Prop :=
  ∀ B : ℕ → Prop, LogDens0 (fun n => n % 2 = 1 ∧ B n) → LogDens0 (fun n => B (oddPart n))

open Classical in
/-- **Node: large 2-adic valuation has finite log-weight.** -/
def SummableLargeTwoAdic : Prop :=
  ∀ ε : ℝ, 0 < ε → Summable fun n : ℕ =>
      if ε * Nat.size (oddPart n) < padicValNat 2 n then (1 : ℝ) / n else 0

/-- **Node: the even reduction.**  For `C ≤ 4`, a start `2^a m` with `m` odd and large, `m` good over
`4.2 size m` letters within `δ / 2`, and `15 a ≤ size m`, `8 a ≤ δ size m`, is not bad. -/
def NotBadStartOfGoodOdd : Prop :=
  ∀ (C : ℕ), C ≤ 4 → ∀ (u : List Bool) (δ : ℝ), 0 < δ →
    ∃ s₀ : ℕ, ∀ a m : ℕ, m % 2 = 1 → s₀ ≤ Nat.size m → 15 * a ≤ Nat.size m →
      8 * (a : ℝ) ≤ δ * Nat.size m → GoodOdd u (δ / 2) m → ¬ BadStart C u δ (2 ^ a * m)

end CollatzMoonshot.Conjugacy
