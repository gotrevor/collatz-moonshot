/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.Obstructions.FiveHead

/-! A smaller-input borrowing exchange on h = 2 + 95t.
This supplies one legal introduction rule, not recursive closure or full repair. -/
namespace CollatzMoonshot.Obstructions.ArithmeticLifts.RestrictedRepair

def recursiveH (t : ℕ) : ℕ := 2 + 95 * t
def recursiveX (t : ℕ) : ℕ := 3349 + 124032 * t
def recursiveZ (t : ℕ) : ℕ := 785 + 29070 * t
def recursiveB (t : ℕ) : ℕ := 661 + 24480 * t

/-- On this subclass the introduced head label is exactly `5 * recursiveX t`. -/
theorem lowerC_recursiveH (t : ℕ) : lowerC (recursiveH t) = 5 * recursiveX t := by
  dsimp [lowerC, recursiveH, recursiveX]; ring

/-- The reverse five-head exchange: the `Q5` relation for `(n, c, d) = (x, b, z)`
lets the pair `[x, z]` be replaced by `[5x, b]`.  Only certificate value and
positive-odd legality are asserted; availability in a larger state is separate. -/
theorem five_head_pair_of_Q5_rev {n c d : ℕ} (hn : 0 < n) (hc : 0 < c) (hd : 0 < d)
    (hno : n % 2 = 1) (hco : c % 2 = 1) (hdo : d % 2 = 1)
    (hQ : 5 * c * (3 * n + 1) * (3 * d + 1) = d * (15 * n + 1) * (3 * c + 1)) :
    legalPairMove [n, d] ([n, d], [5 * n, c]) = true := by
  have hfwd := five_head_pair_of_Q5 hn hc hd hno hco hdo hQ
  simp only [legalPairMove, decide_eq_true_eq] at hfwd ⊢
  obtain ⟨-, -, -, hodd, hval⟩ := hfwd
  refine ⟨le_refl _, rfl, rfl, ?_, hval.symm⟩
  intro u hu
  refine hodd u ?_
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hu ⊢
  rcases hu with rfl | rfl | rfl | rfl <;> tauto

/-- Available smaller inputs introduce the needed lower-family auxiliary. -/
theorem recursive_borrow_pair (t : ℕ) :
    legalPairMove [recursiveX t, recursiveZ t]
      ([recursiveX t, recursiveZ t], [lowerC (recursiveH t), recursiveB t]) = true := by
  rw [lowerC_recursiveH]
  refine five_head_pair_of_Q5_rev ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    dsimp [recursiveX, recursiveZ, recursiveB] <;> try omega
  ring

/-- Every label in the supply rule is positive, odd and 3-free; both
inputs and the companion are strictly below the introduced label. -/
theorem recursive_borrow_height (t : ℕ) :
    recursiveX t < lowerC (recursiveH t) ∧
    recursiveZ t < lowerC (recursiveH t) ∧
    recursiveB t < lowerC (recursiveH t) ∧
    ∀ u ∈ [recursiveX t, recursiveZ t, recursiveB t, lowerC (recursiveH t)],
      0 < u ∧ u % 2 = 1 ∧ u % 3 ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false, lowerC, recursiveH,
      recursiveX, recursiveZ, recursiveB]
  · omega
  · omega
  · omega
  · rintro u (rfl | rfl | rfl | rfl) <;> omega

end CollatzMoonshot.Obstructions.ArithmeticLifts.RestrictedRepair
