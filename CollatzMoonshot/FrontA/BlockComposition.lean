import CollatzMoonshot.FrontA.ThreeBlock

/-!
# Campaign B: the composition mechanism

This is the kernel-checked algebraic part of the architecture in
`BLOCK-COMPOSITION-2026-09-13.md`. It does not yet claim the uniform segment theorem.
The remaining bridge constructs the cyclic maximum-product potential from a word.
The potential recurrence bounds the total odd mass for arbitrary block count; it
uses neither a uniform Collatz theorem nor a bounded-block induction hypothesis.
-/

namespace CollatzMoonshot.FrontA

open scoped BigOperators

/-- A head block in the `u=x+1` coordinate has a nonnegative additive term
strictly below one. This is the input to the rational affine fixed-point envelope. -/
theorem headBlock_conjugate {n q e y : ℕ}
    (h : 2 ^ (q + e) * y + 2 ^ q = 3 ^ q * (n + 1)) :
    (y : ℚ) + 1 = (3 : ℚ)^q / 2^(q+e) * (n+1) + (1 - 1 / 2^e) := by
  have hz : (2 : ℚ)^(q+e) * y + 2^q = 3^q * ((n : ℚ)+1) := by
    exact_mod_cast h
  have hp : (2 : ℚ)^(q+e) ≠ 0 := by positivity
  have he : (2 : ℚ)^e ≠ 0 := by positivity
  apply (mul_left_cancel₀ hp)
  field_simp
  linear_combination (2 : ℚ)^e * hz

/-- The exact prefix elimination composes without dropping its remainder.
Iterate with `p=3^q`, `h=2^(e+q_next)`, `c=2^e-1`. -/
theorem blockCascade_compose {P H T p h c w₀ w w' : ℤ}
    (hprefix : P*w₀ = H*w-T) (hstep : p*w = h*w'-c) :
    (p*P)*w₀ = (H*h)*w' - (p*T+H*c) := by
  linear_combination p*hprefix + H*hstep

/-- **Arbitrary-block integer cascade from the head-block identities.**
The final component of each scale identity includes the endpoint equation;
the joint equations are asserted exactly where there is a following block. -/
theorem blockCascade_of_identities (b : ℕ) (q e x : ℕ → ℕ)
    (hid : ∀ i < b, 2^(q i+e i)*x (i+1)+2^(q i) = 3^(q i)*(x i+1)) :
    ∃ w : ℕ → ℕ,
      (∀ i < b, x i+1 = 2^(q i)*w i ∧ 3^(q i)*w i = 2^(e i)*x (i+1)+1) ∧
      (∀ i, i+1 < b → 3^(q i)*w i+2^(e i) = 2^(e i+q (i+1))*w (i+1)+1) ∧
      (∀ i < b, 1 ≤ w i) := by
  let w : ℕ → ℕ := fun i => (x i+1)/2^(q i)
  have hw (i : ℕ) (hi : i < b) :
      x i+1 = 2^(q i)*w i ∧ 3^(q i)*w i = 2^(e i)*x (i+1)+1 := by
    obtain ⟨v, hv, he⟩ := headBlock_scale (hid i hi)
    have hval : w i = v := by simp [w, hv]
    simpa only [hval] using And.intro hv he
  refine ⟨w, hw, ?_, ?_⟩
  · intro i hi
    have hfirst := (hw i (by omega)).2
    have hsecond := (hw (i+1) hi).1
    rw [hfirst, pow_add]
    calc 2^(e i)*x (i+1)+1+2^(e i) = 2^(e i)*(x (i+1)+1)+1 := by ring
      _ = _ := by rw [hsecond]; ring
  · intro i hi
    have h := (hw i hi).1
    by_contra hn
    have hz : w i = 0 := by omega
    simp [hz] at h

/-- At a cut, positive suffix slope preserves the prefix remainder's effect.
This is the domination step for the affine fixed point, not an integer-cycle assertion. -/
theorem affineFixedPoint_dominates {R S u v P A : ℚ}
    (hR : R < 1) (hP : 0 < P) (hend : u < R*u+S)
    (hprefix : v = P*u+A) :
    v < P*(S/(1-R))+A := by
  have hd : 0 < 1-R := by linarith
  have hu : u < S/(1-R) := (lt_div_iff₀ hd).2 (by nlinarith)
  rw [hprefix]
  linarith [mul_lt_mul_of_pos_left hu hP]

/-- The block multiplier is at most `2^q`. The useful strictness comes from
the separate positivity envelope `2^q < K*M`. -/
theorem blockMultiplier_le_two_pow (q e : ℕ) :
    (3 : ℚ)^q / 2^(q+e) ≤ 2^q := by
  apply (div_le_iff₀ (by positivity : (0 : ℚ) < 2^(q+e))).2
  calc (3 : ℚ)^q ≤ 4^q := by gcongr <;> norm_num
    _ = 2^q * 2^q := by rw [← mul_pow]; norm_num
    _ ≤ 2^q * 2^(q+e) := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num) (Nat.le_add_right q e)) (by positivity)

/-- One step of the cyclic maximum-product potential. -/
theorem blockPotential_step {K M : ℚ} (q e : ℕ)
    (hK : 1 < K) (hM : 1 ≤ M) (hq : (2 : ℚ)^q < K*M) :
    max 1 ((3 : ℚ)^q / 2^(q+e) * M) ≤ K*M^2 := by
  have hMp : 0 < M := by linarith
  have hm2 : 1 ≤ M^2 := by nlinarith
  apply max_le
  · nlinarith
  · have hs := mul_le_mul_of_nonneg_right (blockMultiplier_le_two_pow q e) hMp.le
    have ht := mul_lt_mul_of_pos_right hq hMp
    nlinarith

/-- A subcritical cyclic multiplier system has a potential vertex of value one.
If every maximum selected the multiplier branch, multiplying around the finite
permutation would force the total multiplier to equal one. -/
theorem blockPotential_has_unit {b : ℕ} (next : Equiv.Perm (Fin b))
    (r M : Fin b → ℚ) (hM : ∀ i, 1 ≤ M i)
    (hnext : ∀ i, M (next i) = max 1 (r i*M i))
    (hsub : (∏ i, r i) < 1) :
    ∃ i, M i = 1 := by
  by_contra h
  push_neg at h
  have heq (i : Fin b) : M (next i) = r i*M i := by
    have hgt : 1 < M (next i) := lt_of_le_of_ne (hM _) (Ne.symm (h _))
    have hr : 1 < r i*M i := by
      rw [hnext] at hgt
      rcases lt_max_iff.mp hgt with hbad | hgood
      · exact False.elim (lt_irrefl _ hbad)
      · exact hgood
    rw [hnext, max_eq_right hr.le]
  have hp : (∏ i, M i) = (∏ i, r i)*(∏ i, M i) := by
    calc (∏ i, M i) = ∏ i, M (next i) := (Equiv.prod_comp next M).symm
      _ = ∏ i, r i*M i := Finset.prod_congr rfl (fun i _ => heq i)
      _ = _ := Finset.prod_mul_distrib
  have hpos : 0 < ∏ i, M i := Finset.prod_pos (fun i _ => by linarith [hM i])
  nlinarith

/-- Positivity at every run start also controls total length. On the rational
fixed orbit each additive term is below one and each value is at least two,
so the total multiplier is strictly greater than `2^(-b)`. -/
theorem affineCycle_multiplier_lower (b : ℕ) (hb : 0 < b)
    (next : Equiv.Perm (Fin b)) (r s z : Fin b → ℚ)
    (hz : ∀ i, 2 ≤ z i) (hs : ∀ i, s i < 1)
    (hstep : ∀ i, z (next i) = r i*z i+s i) :
    1 < 2^b * ∏ i, r i := by
  have hlocal (i : Fin b) : z (next i) < 2*(r i*z i) := by
    linarith [hz (next i), hs i, hstep i]
  have hp := Finset.prod_lt_prod_of_nonempty
    (s := (Finset.univ : Finset (Fin b)))
    (f := fun i => z (next i)) (g := fun i => 2*(r i*z i))
    (fun i _ => by linarith [hz (next i)]) (fun i _ => hlocal i)
    ⟨⟨0, hb⟩, Finset.mem_univ _⟩
  have hleft : (∏ i, z (next i)) = ∏ i, z i := Equiv.prod_comp next z
  have hright : (∏ i, 2*(r i*z i)) = 2^b * (∏ i, r i) * (∏ i, z i) := by
    simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    ring
  rw [hleft, hright] at hp
  have hpos : 0 < ∏ i, z i := Finset.prod_pos (fun i _ => by linarith [hz i])
  nlinarith

private theorem blockPotential_prefix_bounds (b : ℕ) (q : ℕ → ℕ) (M : ℕ → ℚ)
    (K : ℚ) (hK : 1 < K) (hzero : M 0 ≤ 1)
    (hM : ∀ i ≤ b, 0 ≤ M i)
    (hstep : ∀ i < b, M (i+1) ≤ K*(M i)^2)
    (hq : ∀ i < b, (2 : ℚ)^(q i) < K*M i) :
    M b ≤ K^(2^b-1) ∧ (2 : ℚ)^(∑ i ∈ Finset.range b, q i) ≤ K^(2^b-1) := by
  induction b with
  | zero => simpa using hzero
  | succ b ih =>
    obtain ⟨hm, ha⟩ := ih (fun i hi => hM i (by omega))
      (fun i hi => hstep i (by omega)) (fun i hi => hq i (by omega))
    have hk : 0 ≤ K := by linarith
    have hexp : 2^(b+1)-1 = (2^b-1)+(2^b-1)+1 := by
      have := Nat.one_le_two_pow (n := b)
      simp only [pow_succ] at *
      omega
    have he : K^(2^(b+1)-1) = K * (K^(2^b-1))^2 := by
      rw [hexp, pow_add, pow_add, pow_one]
      ring
    have hsq : (M b)^2 ≤ (K^(2^b-1))^2 := by
      exact pow_le_pow_left₀ (hM b (by omega)) hm 2
    constructor
    · rw [he]
      exact le_trans (hstep b (by omega)) (mul_le_mul_of_nonneg_left hsq hk)
    · rw [Finset.sum_range_succ, pow_add, he]
      have hlast : (2 : ℚ)^(q b) ≤ K*K^(2^b-1) :=
        le_trans (hq b (by omega)).le (mul_le_mul_of_nonneg_left hm hk)
      calc (2 : ℚ)^(∑ i ∈ Finset.range b, q i) * 2^(q b)
          ≤ K^(2^b-1) * (K*K^(2^b-1)) :=
            mul_le_mul ha hlast (by positivity) (by positivity)
        _ = K * (K^(2^b-1))^2 := by ring

/-- **Arbitrary-block mass contraction.** Once a cyclic potential has been cut
at a vertex with value one, the sum of all odd run lengths is bounded by a
single power of `K`. In the word construction `K=b/δ`, and the exponent is
`2^b-1`; no individual run length or parity-word residue is assumed bounded. -/
theorem blockPotential_mass_bound (b : ℕ) (hb : 0 < b) (q : ℕ → ℕ) (M : ℕ → ℚ)
    (K : ℚ) (hK : 1 < K) (hzero : M 0 ≤ 1)
    (hM : ∀ i ≤ b, 0 ≤ M i)
    (hstep : ∀ i < b, M (i+1) ≤ K*(M i)^2)
    (hq : ∀ i < b, (2 : ℚ)^(q i) < K*M i) :
    (2 : ℚ)^(∑ i ∈ Finset.range b, q i) < K^(2^b-1) := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
  obtain ⟨hm, ha⟩ := blockPotential_prefix_bounds b q M K hK hzero
    (fun i hi => hM i (by omega)) (fun i hi => hstep i (by omega))
    (fun i hi => hq i (by omega))
  have hk : 0 ≤ K := by linarith
  have hlast : (2 : ℚ)^(q b) < K*K^(2^b-1) :=
    lt_of_lt_of_le (hq b (by omega)) (mul_le_mul_of_nonneg_left hm hk)
  have hexp : 2^(b+1)-1 = (2^b-1)+(2^b-1)+1 := by
    have := Nat.one_le_two_pow (n := b)
    simp only [pow_succ] at *
    omega
  rw [Finset.sum_range_succ, pow_add]
  calc (2 : ℚ)^(∑ i ∈ Finset.range b, q i) * 2^(q b)
      < K^(2^b-1) * (K*K^(2^b-1)) :=
        lt_of_le_of_lt (mul_le_mul_of_nonneg_right ha (by positivity))
          (mul_lt_mul_of_pos_left hlast (by positivity))
    _ = K^(2^(b+1)-1) := by rw [hexp, pow_add, pow_add, pow_one]; ring

end CollatzMoonshot.FrontA
