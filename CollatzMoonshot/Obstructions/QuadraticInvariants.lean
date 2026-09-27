import CollatzMoonshot.Obstructions.MinimalRepairs

namespace CollatzMoonshot.Obstructions.ArithmeticLifts

/-- A two-odd-factor replacement in an arbitrary finite context. -/
def QuadraticMultiStep (s t : Multiset ℤ) : Prop :=
  ∃ (a b c d : ℤ) (r : Multiset ℤ),
    0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
    a % 2 = 1 ∧ b % 2 = 1 ∧ c % 2 = 1 ∧ d % 2 = 1 ∧
    pairRel a b c d ∧ s = {a,b} + r ∧ t = {c,d} + r

abbrev QuadraticMultiReach := Relation.ReflTransGen QuadraticMultiStep

/-- The small generators are frozen under arbitrary quadratic replacements. -/
theorem small_generator_count_invariant (a : ℤ) (ha : a = 1 ∨ a = 3 ∨ a = 5)
    {s t : Multiset ℤ} (h : QuadraticMultiReach s t) : s.count a = t.count a := by
  sorry

/-- Unlike the earlier cubic example, this identity has no quadratic
implementation even after adjoining any finite multiset of catalysts. -/
theorem no_catalyst_for_five_exchange (catalyst : Multiset ℤ) :
    ¬ QuadraticMultiReach ({5,55,83} + catalyst) ({11,13,17} + catalyst) := by
  sorry

theorem five_exchange_value :
    certificateValue 0 [5,55,83] = certificateValue 0 [11,13,17] ∧
    certificateValue 0 [5,55,83] = (11 : ℚ)/40 := by native_decide

end CollatzMoonshot.Obstructions.ArithmeticLifts
