/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.OrbitWordLawProb

/-!
# The orbit word law: logarithmic density

* `LogDens0 P`: the starts satisfying `P` have logarithmic density `0`, in the form that
  `OrbitWordLaw` uses (`orbitWordLaw_iff`).
* Windows give density (`logDens0_of_window`): `[1, X]` is covered by windows `[y, y^α]`, each
  of log-weight `≍ log y`, and the exceptional probability tends to `0`, so the exceptional
  log-weight is `o(log X)`.
* Odd parts (`logDens0_oddPart`): the starts `2^a m` with `m` exceptional carry at most twice the
  log-weight of the exceptional `m`.
* Large 2-adic valuation (`summable_large_twoAdic`): the starts `2^a m` with
  `a > ε size m` have finite log-weight.
* The even reduction (`not_badStart_of_goodOdd`): `2^a m` reads `a` zeros and then the letters of
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
  sorry

/-- Fewer starts, smaller density. -/
theorem LogDens0.mono {P Q : ℕ → Prop} (hQ : LogDens0 Q) (h : ∀ n, P n → Q n) : LogDens0 P := by
  sorry

/-- Density `0` is closed under unions. -/
theorem LogDens0.or {P Q : ℕ → Prop} (hP : LogDens0 P) (hQ : LogDens0 Q) :
    LogDens0 (fun n => P n ∨ Q n) := by
  sorry

open Classical in
/-- Finite log-weight has density `0`. -/
theorem logDens0_of_summable {P : ℕ → Prop}
    (h : Summable fun n : ℕ => if P n then (1 : ℝ) / n else 0) : LogDens0 P := by
  sorry

/-- A bounded set has density `0`. -/
theorem logDens0_of_bdd {P : ℕ → Prop} {B : ℕ} (h : ∀ n, P n → n ≤ B) : LogDens0 P := by
  sorry

/-- **Windows give density.**  If the `winLaw x`-probability of `B` tends to `0`, the odd starts in
`B` have logarithmic density `0`. -/
theorem logDens0_of_window (B : ℕ → Prop)
    (h : Tendsto (fun x => (winLaw x).expect (Set.indicator {n | B n} 1)) atTop (𝓝 0)) :
    LogDens0 (fun n => n % 2 = 1 ∧ B n) := by
  sorry

/-- **Odd parts.**  If the odd starts in `B` have density `0`, so do the starts whose odd part is
in `B`. -/
theorem logDens0_oddPart (B : ℕ → Prop) (h : LogDens0 (fun n => n % 2 = 1 ∧ B n)) :
    LogDens0 (fun n => B (oddPart n)) := by
  sorry

open Classical in
/-- **Large 2-adic valuation has finite log-weight.** -/
theorem summable_large_twoAdic {ε : ℝ} (hε : 0 < ε) :
    Summable fun n : ℕ =>
      if ε * Nat.size (oddPart n) < padicValNat 2 n then (1 : ℝ) / n else 0 := by
  sorry

/-- **The even reduction.**  For `C ≤ 4`, a start `2^a m` with `m` odd and large, `m` good over
`4.2 size m` letters within `δ / 2`, and `15 a ≤ size m`, `8 a ≤ δ size m`, is not bad. -/
theorem not_badStart_of_goodOdd {C : ℕ} (hC4 : C ≤ 4) (u : List Bool) {δ : ℝ} (hδ : 0 < δ) :
    ∃ s₀ : ℕ, ∀ a m : ℕ, m % 2 = 1 → s₀ ≤ Nat.size m → 15 * a ≤ Nat.size m →
      8 * (a : ℝ) ≤ δ * Nat.size m → GoodOdd u (δ / 2) m → ¬ BadStart C u δ (2 ^ a * m) := by
  sorry

end CollatzMoonshot.Conjugacy
