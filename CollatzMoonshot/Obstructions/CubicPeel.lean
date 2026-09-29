import CollatzMoonshot.Obstructions.RecursiveBorrow

/-! A variable cubic peels the second actual odd factor on a CRT subclass.
This is a scalar identity with legal odd labels. It is not a rule of the
old fixed C5 palette and does not assert a balanced certificate or termination.

The frozen progression is `t = 16475 + 25172*s`, `h = recursiveH t`, and
`n = lowerN h`; the exchange coefficients are the `K64` refinement, i.e.
`q1 = (3a-1)/64` and `e1 = (3a+1)/58` for `a = tstep n`.  Nothing below
asserts convergence of any trajectory. -/
namespace CollatzMoonshot.Obstructions.ArithmeticLifts.RestrictedRepair

def cubicN (s : ℕ) : ℕ := 25542881863 + 39026668800*s
def cubicM (s : ℕ) : ℕ := 8979919405 + 13720313250*s
def cubicA (s : ℕ) : ℕ := 38314322795 + 58540003200*s
def cubicV (s : ℕ) : ℕ := 191571613973 + 292700016000*s
def cubicQ1 (s : ℕ) : ℕ := 1795983881 + 2744062650*s
def cubicQ2 (s : ℕ) : ℕ := 4119819655 + 6294624000*s
def cubicE1 (s : ℕ) : ℕ := 1981775317 + 3027931200*s
def cubicE2 (s : ℕ) : ℕ := 3648983123 + 5575238400*s

/-- The companion growth label, normalised so that `cubicP s + 1` is four
times an affine form with odd slope. -/
def cubicP (s : ℕ) : ℕ := 32327709859 + 49393127700*s

private theorem cubicN_odd (s : ℕ) : cubicN s % 2 = 1 := by simp only [cubicN]; omega
private theorem cubicA_odd (s : ℕ) : cubicA s % 2 = 1 := by simp only [cubicA]; omega
private theorem cubicV_odd (s : ℕ) : cubicV s % 2 = 1 := by simp only [cubicV]; omega
private theorem cubicQ1_odd (s : ℕ) : cubicQ1 s % 2 = 1 := by simp only [cubicQ1]; omega
private theorem cubicQ2_odd (s : ℕ) : cubicQ2 s % 2 = 1 := by simp only [cubicQ2]; omega
private theorem cubicE1_odd (s : ℕ) : cubicE1 s % 2 = 1 := by simp only [cubicE1]; omega
private theorem cubicE2_odd (s : ℕ) : cubicE2 s % 2 = 1 := by simp only [cubicE2]; omega

/-- Both odd-label products collapse to `4(2a-7)/(3(9a+61))`, so the variable
cubic is an exact scalar exchange. -/
theorem cubic_peel_value (s : ℕ) :
    certificateValue 0 [cubicV s, cubicQ1 s, cubicQ2 s] =
    certificateValue 0 [cubicA s, cubicE1 s, cubicE2 s] := by
  have hV : (3 * (cubicV s : ℚ) + 1) ≠ 0 := by positivity
  have hQ1 : (3 * (cubicQ1 s : ℚ) + 1) ≠ 0 := by positivity
  have hQ2 : (3 * (cubicQ2 s : ℚ) + 1) ≠ 0 := by positivity
  have hA : (3 * (cubicA s : ℚ) + 1) ≠ 0 := by positivity
  have hE1 : (3 * (cubicE1 s : ℚ) + 1) ≠ 0 := by positivity
  have hE2 : (3 * (cubicE2 s : ℚ) + 1) ≠ 0 := by positivity
  simp only [certificateValue, pow_zero, one_mul, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one]
  rw [odd_ratio (cubicV_odd s), odd_ratio (cubicQ1_odd s), odd_ratio (cubicQ2_odd s),
    odd_ratio (cubicA_odd s), odd_ratio (cubicE1_odd s), odd_ratio (cubicE2_odd s)]
  field_simp
  simp only [cubicV, cubicQ1, cubicQ2, cubicA, cubicE1, cubicE2]
  push_cast
  ring

/-- All seven labels are positive, odd and outside `3ℕ`, the four exchanged
labels stay below the smaller frontier `cubicM`, and `cubicM < cubicN`. -/
theorem cubic_peel_domain (s : ℕ) :
    cubicM s < cubicN s ∧
    (∀ u ∈ [cubicQ1 s,cubicQ2 s,cubicE1 s,cubicE2 s], u<cubicM s) ∧
    (∀ u ∈ [cubicN s,cubicA s,cubicV s,cubicQ1 s,cubicQ2 s,cubicE1 s,cubicE2 s],
      0<u ∧ u%2=1 ∧ u%3≠0) := by
  refine ⟨by simp only [cubicM, cubicN]; omega, ?_, ?_⟩
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with h|h|h|h <;> subst h <;>
      simp only [cubicM, cubicQ1, cubicQ2, cubicE1, cubicE2] <;> omega
  · intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with h|h|h|h|h|h|h <;> subst h <;>
      simp only [cubicN, cubicA, cubicV, cubicQ1, cubicQ2, cubicE1, cubicE2] <;>
      exact ⟨by omega, by omega, by omega⟩

open CollatzMoonshot.FrontB in
/-- The two frontier steps: `cubicN` steps onto the actual head `cubicA`, and
the virtual head `cubicV` steps onto a power-of-two multiple of `cubicM`. -/
theorem cubic_peel_frontiers (s : ℕ) :
    tstep (cubicN s) = cubicA s ∧ tstep (cubicV s) = 32*cubicM s := by
  have hn := two_tstep_odd (cubicN_odd s)
  have hv := two_tstep_odd (cubicV_odd s)
  simp only [cubicN, cubicA, cubicV, cubicM] at hn hv ⊢
  exact ⟨by omega, by omega⟩

/-- The head of the progression is the `t = 16475 + 25172*s` slice of the
existing recursive-borrow family. -/
theorem cubic_peel_link (s : ℕ) :
    cubicN s = lowerN (recursiveH (16475 + 25172*s)) := by
  simp only [cubicN, lowerN, recursiveH]
  ring

private lemma exists_lin (N a : ℕ) [NeZero N] (h : Nat.Coprime a N) (y : ZMod N) :
    ∃ t : ZMod N, (a : ZMod N) * t = y := by
  obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime a N).2 h
  refine ⟨((u⁻¹ : (ZMod N)ˣ) : ZMod N) * y, ?_⟩
  rw [← hu, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

/-- Growth congruence: since `cubicP s + 1 = 4*(8081927465 + 12348281925*s)`
has odd slope, the linear congruence is solvable modulo every `2^j`, and the
fixed factor `4` lifts the solution to divisibility by `2^(j+2)`. -/
theorem cubic_peel_growth_congruence (j : ℕ) :
    ∃ s : ℕ, 2^(j+2) ∣ cubicP s + 1 := by
  have : NeZero (2^j) := ⟨pow_ne_zero j two_ne_zero⟩
  have hcop : Nat.Coprime 12348281925 (2^j) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 ⟨6174140962, by norm_num⟩)
  obtain ⟨t, ht⟩ := exists_lin (2^j) 12348281925 hcop (-(8081927465 : ZMod (2^j)))
  push_cast at ht
  refine ⟨t.val, ?_⟩
  have hdvd : 2^j ∣ 8081927465 + 12348281925 * t.val := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast [ZMod.natCast_val, ZMod.cast_id]
    linear_combination ht
  obtain ⟨c, hc⟩ := hdvd
  refine ⟨c, ?_⟩
  have hP : cubicP t.val + 1 = 4 * (8081927465 + 12348281925 * t.val) := by
    simp only [cubicP]; ring
  rw [hP, hc, pow_add]
  ring

end CollatzMoonshot.Obstructions.ArithmeticLifts.RestrictedRepair
