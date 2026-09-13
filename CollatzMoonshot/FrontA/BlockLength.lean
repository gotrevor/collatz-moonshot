import CollatzMoonshot.FrontA.BlockCycle

/-!
# Explicit length bound from arbitrary-block composition

The numerical feedback uses the already proved polynomial two-log measure.
An elementary binary-length argument gives twice the proposed architecture
bound, avoiding real logarithms and square roots in this final step.
-/

namespace CollatzMoonshot.FrontA

open scoped BigOperators

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

/-- A deliberately loose explicit bound for at most `b` positive odd runs. -/
def fixedBlockLengthBound (b : ℕ) : ℕ :=
  4 * ((2^b-1)*(b+53342))^2+b

private theorem binary_length_square (t : ℕ) (ht : 4 ≤ t) :
    (t+1)^2 ≤ 2 * 2^t := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih =>
    rw [pow_succ 2 t]
    nlinarith

/-- The existing polynomial separation gives a uniform binary deficit scale,
including the easy non-window regime. -/
theorem block_polynomial_deficit_scale (a m : ℕ) (ha : 1 ≤ a)
    (hsub : 3^a < 2^m) :
    2^m ≤ 2^(52906+436*(Nat.log 2 a+1))*(2^m-3^a) := by
  by_cases hwin : 2^m < 2*3^a
  · exact threeBlock_polynomial_window_scale a m ha hsub hwin
  · have hpow : (2 : ℕ) ≤ 2^(52906+436*(Nat.log 2 a+1)) := by
      exact le_trans (by norm_num : 2 ≤ 2^1)
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hd : 2^m ≤ 2*(2^m-3^a) := by omega
    exact hd.trans (Nat.mul_le_mul_right _ hpow)

/-- **Numerical feedback closes uniformly.** The composition inequality and
the existing polynomial measure give an explicit bound depending only on b. -/
theorem blockComposition_length_bound (a m b : ℕ) (ha : 1 ≤ a) (hb : 0 < b)
    (hsub : 3^a < 2^m)
    (hmass : (2 : ℚ)^a < ((b : ℚ)/(1-(3 : ℚ)^a/2^m))^(2^b-1))
    (hlen : (2 : ℚ)^m < 2^b*3^a) :
    m < fixedBlockLengthBound b := by
  let C := 2^b-1
  let t := Nat.log 2 a
  let S := 52906+436*(t+1)
  let H := C*(b+53342)
  have hC : 1 ≤ C := by
    have hp : (2 : ℕ)^1 ≤ 2^b := Nat.pow_le_pow_right (by norm_num) hb
    dsimp [C]
    norm_num at hp
    omega
  have hH : 53343 ≤ H := by
    have hmul := Nat.mul_le_mul_right (b+53342) hC
    dsimp [H]
    nlinarith
  have hD : (0 : ℚ) < 2^m-3^a := by
    have : (3 : ℚ)^a < 2^m := by exact_mod_cast hsub
    linarith
  have hscale : (2 : ℚ)^m ≤ 2^S*(2^m-3^a) := by
    have h := block_polynomial_deficit_scale a m ha hsub
    have hc : ((2^m : ℕ) : ℚ) ≤ ((2^(52906+436*(Nat.log 2 a+1)) : ℕ) : ℚ) *
        ((2^m-3^a : ℕ) : ℚ) := by exact_mod_cast h
    push_cast [Nat.cast_sub hsub.le] at hc
    exact hc
  have hK : (b : ℚ)/(1-(3 : ℚ)^a/2^m) ≤ 2^(b+S) := by
    have he : (b : ℚ)/(1-(3 : ℚ)^a/2^m) = b*(2^m/(2^m-3^a)) := by
      field_simp
    rw [he, pow_add]
    have hquot : (2 : ℚ)^m/(2^m-3^a) ≤ 2^S := (div_le_iff₀ hD).2 hscale
    have hbpow : (b : ℚ) ≤ 2^b := by exact_mod_cast (Nat.lt_two_pow_self (n := b)).le
    exact mul_le_mul hbpow hquot (div_nonneg (by positivity) hD.le) (by positivity)
  have hKpos : (0 : ℚ) < (b : ℚ)/(1-(3 : ℚ)^a/2^m) := by
    apply div_pos (by exact_mod_cast hb)
    have : (3 : ℚ)^a/2^m < 1 := (div_lt_one (by positivity)).2 (by
      exact_mod_cast hsub)
    linarith
  have haexp : a < (b+S)*C := by
    have hp := pow_le_pow_left₀ hKpos.le hK C
    have hlt : (2 : ℚ)^a < 2^((b+S)*C) := by
      rw [pow_mul]
      exact hmass.trans_le hp
    exact (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℚ) < 2)).1 hlt
  have haf : a < H*(t+1) := by
    apply lt_of_lt_of_le haexp
    dsimp [H, S]
    nlinarith [Nat.zero_le (C*(b+52906)*t)]
  have habound : a < 2*H^2 := by
    by_cases ht : 4 ≤ t
    · have hsq := binary_length_square t ht
      have hp : 2^t ≤ a := Nat.pow_log_le_self 2 (by omega)
      have hsquare : a^2 < (H*(t+1))^2 := by nlinarith [haf]
      have hbound : (H*(t+1))^2 ≤ 2*H^2*a := by
        nlinarith [Nat.mul_le_mul_left (H^2) (hsq.trans (Nat.mul_le_mul_left 2 hp))]
      nlinarith
    · have hp : a < 2^(t+1) := Nat.lt_pow_succ_log_self (by norm_num) a
      have hsmall : 2^(t+1) ≤ (2 : ℕ)^4 := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at hsmall
      nlinarith
  have hmlt : m < b+2*a := by
    have h3 : (3 : ℚ)^a ≤ 4^a := pow_le_pow_left₀ (by norm_num) (by norm_num) a
    have he : (4 : ℚ)^a = 2^(2*a) := by rw [pow_mul]; norm_num
    have hp : (2 : ℚ)^m < 2^(b+2*a) := by
      rw [pow_add, ← he]
      exact hlen.trans_le (mul_le_mul_of_nonneg_left h3 (by positivity))
    exact (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℚ) < 2)).1 hp
  change m < 4*H^2+b
  omega

/-- The explicit bound already applies to every positive-odd-run integer
cascade with increasing endpoint. No global Collatz theorem is assumed. -/
theorem headBlock_cascade_length_bound (b : ℕ) (hb : 0 < b)
    (q e x : ℕ → ℕ) (hq : ∀ i < b, 0 < q i)
    (hid : ∀ i < b, 2^(q i+e i)*x (i+1)+2^(q i) = 3^(q i)*(x i+1))
    (hsub : 3^(∑ i ∈ Finset.range b, q i) < 2^(∑ i ∈ Finset.range b, (q i+e i)))
    (hup : x 0 < x b) :
    (∑ i ∈ Finset.range b, (q i+e i)) < fixedBlockLengthBound b := by
  have hsubQ : (3 : ℚ)^(∑ i ∈ Finset.range b, q i) /
      2^(∑ i ∈ Finset.range b, (q i+e i)) < 1 := by
    apply (div_lt_one (by positivity)).2
    exact_mod_cast hsub
  obtain ⟨hmass, hlen⟩ := headBlock_cascade_composition b hb q e x hq hid hsubQ hup
  have ha : 1 ≤ ∑ i ∈ Finset.range b, q i := by
    have hsum := Finset.single_le_sum (f := q) (fun i _ => Nat.zero_le (q i))
      (Finset.mem_range.mpr hb)
    have := hq 0 hb
    omega
  exact blockComposition_length_bound _ _ b ha hb hsub hmass hlen

end CollatzMoonshot.FrontA
