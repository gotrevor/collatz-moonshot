/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.Obstructions.Repair71

/-!
# Two families of legal quadratic exchanges at the artificial five-head

These statements assert only the legality of one available pair replacement.
They do not assert uniform borrowability of the second input, nor a complete
repair of the resulting virtual word.
-/

namespace CollatzMoonshot.Obstructions.ArithmeticLifts.RestrictedRepair

/-- The family through the observed `1031` exchange, restricted to positive odd
labels outside `3ℕ` and to `n ≡ 7 mod 64`. -/
def observedN (h : ℕ) : ℕ := 1031 + 8868288 * h
def observedC (h : ℕ) : ℕ := 1045 + 8988672 * h
def observedD (h : ℕ) : ℕ := 5525 + 47523840 * h

open CollatzMoonshot.FrontB in
/-- For an odd `u`, the halving step satisfies `2 * tstep u = 3 * u + 1`. -/
theorem two_tstep_odd {u : ℕ} (hu : u % 2 = 1) : 2 * tstep u = 3 * u + 1 := by
  have h2 : ¬ u % 2 = 0 := by omega
  simp only [tstep, h2, if_false]
  omega

open CollatzMoonshot.FrontB in
/-- The odd-label ratio in closed rational form. -/
theorem odd_ratio {u : ℕ} (hu : u % 2 = 1) :
    (u : ℚ) / (tstep u : ℚ) = 2 * (u : ℚ) / (3 * (u : ℚ) + 1) := by
  have hnat : 2 * tstep u = 3 * u + 1 := two_tstep_odd hu
  have hq : 2 * (tstep u : ℚ) = 3 * (u : ℚ) + 1 := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℚ)) hnat
  have hpos : (0 : ℚ) < 3 * (u : ℚ) + 1 := by positivity
  have ht : (0 : ℚ) < (tstep u : ℚ) := by nlinarith
  field_simp
  nlinarith [hq]

/-- The whole five-head exchange, for any positive odd triple satisfying the
quadratic relation `Q5`. -/
theorem five_head_pair_of_Q5 {n c d : ℕ} (hn : 0 < n) (hc : 0 < c) (hd : 0 < d)
    (hno : n % 2 = 1) (hco : c % 2 = 1) (hdo : d % 2 = 1)
    (hQ : 5 * c * (3 * n + 1) * (3 * d + 1) = d * (15 * n + 1) * (3 * c + 1)) :
    legalPairMove [5 * n, c] ([5 * n, c], [n, d]) = true := by
  have h5o : (5 * n) % 2 = 1 := by omega
  have h5p : 0 < 5 * n := by omega
  have hval : certificateValue 0 [5 * n, c] = certificateValue 0 [n, d] := by
    have hQq : (5 : ℚ) * c * (3 * n + 1) * (3 * d + 1)
        = (d : ℚ) * (15 * n + 1) * (3 * c + 1) := by exact_mod_cast hQ
    have hnq : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
    have hcq : (0 : ℚ) < (c : ℚ) := by exact_mod_cast hc
    have hdq : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
    simp only [certificateValue, pow_zero, one_mul, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one]
    rw [odd_ratio h5o, odd_ratio hco, odd_ratio hno, odd_ratio hdo]
    have h15 : ((5 * n : ℕ) : ℚ) = 5 * (n : ℚ) := by push_cast; ring
    rw [h15]
    have d1 : (0 : ℚ) < 3 * (5 * (n : ℚ)) + 1 := by linarith
    have d2 : (0 : ℚ) < 3 * (c : ℚ) + 1 := by linarith
    have d3 : (0 : ℚ) < 3 * (n : ℚ) + 1 := by linarith
    have d4 : (0 : ℚ) < 3 * (d : ℚ) + 1 := by linarith
    field_simp
    nlinarith [hQq, hnq, hcq, hdq]
  simp only [legalPairMove, decide_eq_true_eq]
  refine ⟨le_refl _, rfl, rfl, ?_, hval⟩
  intro u hu
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl <;> omega

/-- If the factor `observedC h` is available alongside `5 * observedN h`,
this one quadratic move is legal.  Availability in a larger state is separate. -/
theorem observed_five_head_pair (h : ℕ) :
    legalPairMove [5 * observedN h, observedC h]
      ([5 * observedN h, observedC h], [observedN h, observedD h]) = true := by
  refine five_head_pair_of_Q5 ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    dsimp [observedN, observedC, observedD] <;> try omega
  ring

/-- A second family with both output/input auxiliary labels below the head.
Again, this inequality is not a uniform borrowing or repair theorem. -/
def lowerN (h : ℕ) : ℕ := 9223 + 16320 * h
def lowerC (h : ℕ) : ℕ := 3689 + 6528 * h
def lowerD (h : ℕ) : ℕ := 5425 + 9600 * h

theorem lower_five_head_pair (h : ℕ) :
    legalPairMove [5 * lowerN h, lowerC h]
      ([5 * lowerN h, lowerC h], [lowerN h, lowerD h]) = true := by
  refine five_head_pair_of_Q5 ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    dsimp [lowerN, lowerC, lowerD] <;> try omega
  ring

theorem lower_five_head_height (h : ℕ) :
    lowerC h < lowerN h ∧ lowerD h < lowerN h := by
  dsimp [lowerC, lowerN, lowerD]
  omega

end CollatzMoonshot.Obstructions.ArithmeticLifts.RestrictedRepair
