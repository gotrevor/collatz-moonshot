import CollatzMoonshot.FrontA.BlockComposition
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Uniform composition through the smallest affine-cycle vertex

The auxiliary cycle is rational, not an integer Collatz cycle. Bernoulli's
inequality supplies a vertex below `b / (1 - R)`. At every positive odd run,
the head-block map grows by less than the square of its input. This gives the
composition inequality without constructing maximum partial products.
-/

namespace CollatzMoonshot.FrontA

open scoped BigOperators

/-- A positive affine cycle with additive terms below one has a small vertex.
This holds even for a permutation with several cycles. -/
theorem affineCycle_has_small {b : ℕ} (hb : 0 < b)
    (next : Equiv.Perm (Fin b)) (r s z : Fin b → ℚ)
    (hz : ∀ i, 0 < z i) (hs : ∀ i, s i < 1)
    (hstep : ∀ i, z (next i) = r i * z i + s i)
    (hRpos : 0 < ∏ i, r i) (hR : (∏ i, r i) < 1) :
    ∃ i, z i < (b : ℚ) / (1 - ∏ i, r i) := by
  let R := ∏ i, r i
  let c : ℚ := (1 - R) / b
  have hbq : (0 : ℚ) < b := by exact_mod_cast hb
  have hb1 : (1 : ℚ) ≤ b := by exact_mod_cast hb
  have hc : 0 < c := div_pos (by dsimp [R]; linarith) hbq
  have hc1 : c < 1 := (div_lt_one hbq).2 (by dsimp [R]; linarith)
  have hbc : (b : ℚ) * c = 1 - R := by dsimp [c]; field_simp
  by_contra h
  push_neg at h
  have hlocal (i : Fin b) : (1-c) * z (next i) < r i * z i := by
    have ht : 1 ≤ c * z (next i) := by
      have hi := h (next i)
      have hd : 0 < 1 - R := by dsimp [R]; linarith
      have hi' : (b : ℚ) ≤ z (next i) * (1-R) := (div_le_iff₀ hd).1 hi
      dsimp [c]
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hbq).2
      simpa [mul_comm] using hi'
    linarith [hstep i, hs i]
  have hp := Finset.prod_lt_prod_of_nonempty
    (s := (Finset.univ : Finset (Fin b)))
    (f := fun i => (1-c) * z (next i)) (g := fun i => r i * z i)
    (fun i _ => mul_pos (sub_pos.mpr hc1) (hz _))
    (fun i _ => hlocal i) ⟨⟨0, hb⟩, Finset.mem_univ _⟩
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Equiv.prod_comp] at hp
  have hzp : 0 < ∏ i, z i := Finset.prod_pos (fun i _ => hz i)
  have hpow : (1-c)^b < R := (mul_lt_mul_iff_left₀ hzp).1 hp
  have hbern := one_add_mul_le_pow (a := -c) (by linarith : -2 ≤ -c) b
  simp only [← sub_eq_add_neg] at hbern
  have : R ≤ (1-c)^b := by nlinarith [hbern]
  exact (not_lt_of_ge this) hpow

/-- A nonempty odd run leaves enough slack in `3^q ≤ 4^q` to absorb the
additive term. This is stronger than the coarse multiplier bound. -/
theorem blockMultiplier_gap (q e : ℕ) (hq : 0 < q) :
    (3 : ℚ)^q / 2^(q+e) + 1/2 ≤ 2^q := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  change (3 : ℚ)^(k+1) / 2^(k+1+e) + 1/2 ≤ 2^(k+1)
  have hpow : (3 : ℚ)^(k+1) ≤ 3 * 4^k := by
    rw [pow_succ, mul_comm]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) (by norm_num) k)
      (by norm_num)
  have htwo : (2 : ℚ)^k ≤ 4^k := by gcongr <;> norm_num
  have hp : (3 : ℚ)^(k+1) + 2^k ≤ 2^(k+1) * 2^(k+1) := by
    have he : (4 : ℚ)^k = 2^k * 2^k := by rw [← mul_pow]; norm_num
    simp only [pow_succ] at hpow ⊢
    nlinarith
  have hbase : (3 : ℚ)^(k+1) / 2^(k+1) + 1/2 ≤ 2^(k+1) := by
    apply (le_of_mul_le_mul_right (a := (2 : ℚ)^(k+1)) ?_ (by positivity))
    field_simp
    simp only [pow_succ] at hp ⊢
    nlinarith [hp]
  have hdiv : (3 : ℚ)^(k+1) / 2^(k+1+e) ≤ 3^(k+1) / 2^(k+1) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  linarith

/-- The fixed-point envelope grows at most quadratically across a head block. -/
theorem affineBlock_lt_square (q e : ℕ) (hq : 0 < q) {z s : ℚ}
    (hz : (2 : ℚ)^q ≤ z) (hs : s < 1) :
    (3 : ℚ)^q / 2^(q+e) * z + s < z^2 := by
  have hq2 : (2 : ℚ) ≤ 2^q := by
    simpa using pow_le_pow_right₀ (show (1 : ℚ) ≤ 2 by norm_num)
      (show 1 ≤ q by omega)
  have hz2 : (2 : ℚ) ≤ z := hq2.trans hz
  have hmul := mul_le_mul_of_nonneg_right (blockMultiplier_gap q e hq)
    (by linarith : 0 ≤ z)
  have hsq := mul_le_mul_of_nonneg_right hz (by linarith : 0 ≤ z)
  nlinarith

private theorem squareOrbit_prefix_bound (b : ℕ) (z : ℕ → ℚ) (K : ℚ)
    (hK : 0 < K) (hzero : z 0 < K) (hz : ∀ i ≤ b, 0 ≤ z i)
    (hstep : ∀ i < b, z (i+1) ≤ (z i)^2) :
    z b < K^(2^b) := by
  induction b with
  | zero => simpa using hzero
  | succ b ih =>
    have hprev := ih (fun i hi => hz i (by omega))
      (fun i hi => hstep i (by omega))
    calc z (b+1) ≤ (z b)^2 := hstep b (by omega)
      _ < (K^(2^b))^2 := by nlinarith [hz b (by omega), pow_pos hK (2^b)]
      _ = K^(2^(b+1)) := by rw [← pow_mul, pow_succ]

/-- Repeated squaring bounds the total odd mass after a cut at a small vertex. -/
theorem squareOrbit_mass_bound (b : ℕ) (hb : 0 < b) (q : ℕ → ℕ)
    (z : ℕ → ℚ) (K : ℚ) (hK : 0 < K) (hzero : z 0 < K)
    (hz : ∀ i ≤ b, 0 ≤ z i) (hstep : ∀ i < b, z (i+1) ≤ (z i)^2)
    (hq : ∀ i < b, (2 : ℚ)^(q i) ≤ z i) :
    (2 : ℚ)^(∑ i ∈ Finset.range b, q i) < K^(2^b-1) := by
  have hlocal (i : ℕ) (hi : i ∈ Finset.range b) : (2 : ℚ)^(q i) < K^(2^i) := by
    have hi' := Finset.mem_range.mp hi
    exact lt_of_le_of_lt (hq i hi') (squareOrbit_prefix_bound i z K hK hzero
      (fun j hj => hz j (by omega)) (fun j hj => hstep j (by omega)))
  have hp := Finset.prod_lt_prod_of_nonempty (s := Finset.range b)
    (f := fun i => (2 : ℚ)^(q i)) (g := fun i => K^(2^i))
    (fun i _ => by positivity) hlocal ⟨0, Finset.mem_range.mpr hb⟩
  have hsum (k : ℕ) : ∑ i ∈ Finset.range k, 2^i = 2^k-1 := by
    induction k with
    | zero => simp
    | succ b ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      have := Nat.one_le_two_pow (n := b)
      omega
  simpa only [Finset.prod_pow_eq_pow_sum, hsum] using hp

/-- **Uniform arbitrary-block composition inequality.** Every rational affine
head-block cycle satisfying positivity at every run start obeys the proposed
odd-mass bound. All cyclic bookkeeping is explicit; rotation only reindexes
the auxiliary rational values. -/
theorem affineBlockCycle_mass_bound {b : ℕ} (hb : 0 < b)
    (q e : Fin b → ℕ) (z : Fin b → ℚ)
    (hq : ∀ i, 0 < q i) (hz : ∀ i, (2 : ℚ)^(q i) ≤ z i)
    (hstep : ∀ i, z (finRotate b i) =
      (3 : ℚ)^(q i) / 2^(q i+e i) * z i + (1-1/2^(e i)))
    (hsub : (∏ i, (3 : ℚ)^(q i) / 2^(q i+e i)) < 1) :
    (2 : ℚ)^(∑ i, q i) <
      ((b : ℚ)/(1-∏ i, (3 : ℚ)^(q i) / 2^(q i+e i)))^(2^b-1) := by
  letI : NeZero b := ⟨by omega⟩
  let r : Fin b → ℚ := fun i => 3^(q i) / 2^(q i+e i)
  let K : ℚ := (b : ℚ)/(1-∏ i, r i)
  have hzpos (i : Fin b) : 0 < z i := lt_of_lt_of_le (by positivity) (hz i)
  have hs (i : Fin b) : (1 : ℚ)-1/2^(e i) < 1 := by
    have : (0 : ℚ) < 1/2^(e i) := by positivity
    linarith
  obtain ⟨pivot, hpivot⟩ := affineCycle_has_small hb (finRotate b) r
    (fun i => 1-1/2^(e i)) z hzpos hs hstep
    (Finset.prod_pos (fun i _ => by dsimp [r]; positivity)) hsub
  let v : ℕ → Fin b := fun i => Fin.ofNat b i + pivot
  have hv (i : ℕ) : v (i+1) = finRotate b (v i) := by
    have hcast : Fin.ofNat b (i+1) = Fin.ofNat b i + 1 := by
      apply Fin.ext
      simp [Fin.add_def, Nat.add_mod]
    change Fin.ofNat b (i+1)+pivot = finRotate b (Fin.ofNat b i+pivot)
    rw [hcast, finRotate_apply]
    ac_rfl
  have hK : 0 < K := div_pos (by exact_mod_cast hb) (by dsimp [r]; linarith)
  have hmass := squareOrbit_mass_bound b hb (fun i => q (v i)) (fun i => z (v i)) K hK
    (by simpa [v, K, r] using hpivot)
    (fun i _ => (hzpos _).le)
    (fun i _ => by
      rw [hv i, hstep (v i)]
      exact (affineBlock_lt_square (q (v i)) (e (v i)) (hq _) (hz _) (hs _)).le)
    (fun i _ => hz _)
  have hsum : (∑ i ∈ Finset.range b, q (v i)) = ∑ i, q i := by
    calc (∑ i ∈ Finset.range b, q (v i)) = ∑ i : Fin b, q (i+pivot) := by
          simpa [v] using (Fin.sum_univ_eq_sum_range (fun i => q (v i)) b).symm
      _ = ∑ i, q i := Equiv.sum_comp (finCycle pivot) q
  simpa only [hsum] using hmass

/-- Close an increasing subcritical affine path into a rational cycle above
every path vertex. The correction includes the actual endpoint displacement,
so no prefix remainder or admission datum is discarded. -/
theorem affinePath_cycle_envelope (b : ℕ) (r s u : ℕ → ℚ)
    (hr : ∀ i < b, 0 < r i)
    (hstep : ∀ i < b, u (i+1) = r i*u i+s i)
    (hsub : (∏ i ∈ Finset.range b, r i) < 1) (hup : u 0 < u b) :
    ∃ z : ℕ → ℚ, z b = z 0 ∧ (∀ i ≤ b, u i < z i) ∧
      (∀ i < b, z (i+1) = r i*z i+s i) := by
  let P : ℕ → ℚ := fun i => ∏ j ∈ Finset.range i, r j
  let c : ℚ := (u b-u 0)/(1-P b)
  have hd : 0 < 1-P b := by dsimp [P]; linarith
  have hc : 0 < c := div_pos (by linarith) hd
  have heq : (1-P b)*c = u b-u 0 := by dsimp [c]; field_simp
  refine ⟨fun i => u i+P i*c, ?_, ?_, ?_⟩
  · dsimp only
    have hP0 : P 0 = 1 := by simp [P]
    rw [hP0]
    nlinarith [heq]
  · intro i hi
    have hp : 0 < P i := Finset.prod_pos (fun j hj => hr j (by
      have := Finset.mem_range.mp hj
      omega))
    exact lt_add_of_pos_right _ (mul_pos hp hc)
  · intro i hi
    dsimp only
    have hp : P (i+1) = P i*r i := Finset.prod_range_succ _ _
    rw [hstep i hi, hp]
    ring

private theorem finRotate_value_of_closed_path {b : ℕ} (hb : 0 < b)
    (z : ℕ → ℚ) (hclose : z b = z 0) (i : Fin b) :
    z (finRotate b i).val = z (i.val+1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
  obtain ⟨i, hi⟩ := i
  by_cases hlt : i < k
  · rw [finRotate_of_lt hlt]
  · have he : i = k := by omega
    subst i
    rw [finRotate_last']
    exact hclose.symm

/-- **Composition from the integer head identities.** This is the uniform
inequality about arbitrary genuine integer cascades, not an assumption that
the rational envelope exists. Maximality of the odd runs is unnecessary here;
positive odd lengths and nonnegative even lengths suffice. -/
theorem headBlock_cascade_composition (b : ℕ) (hb : 0 < b)
    (q e x : ℕ → ℕ) (hq : ∀ i < b, 0 < q i)
    (hid : ∀ i < b, 2^(q i+e i)*x (i+1)+2^(q i) = 3^(q i)*(x i+1))
    (hsub : (3 : ℚ)^(∑ i ∈ Finset.range b, q i) /
      2^(∑ i ∈ Finset.range b, (q i+e i)) < 1)
    (hup : x 0 < x b) :
    (2 : ℚ)^(∑ i ∈ Finset.range b, q i) <
      ((b : ℚ)/(1-(3 : ℚ)^(∑ i ∈ Finset.range b, q i) /
        2^(∑ i ∈ Finset.range b, (q i+e i))))^(2^b-1) ∧
    (2 : ℚ)^(∑ i ∈ Finset.range b, (q i+e i)) <
      2^b*3^(∑ i ∈ Finset.range b, q i) := by
  let r : ℕ → ℚ := fun i => 3^(q i)/2^(q i+e i)
  let s : ℕ → ℚ := fun i => 1-1/2^(e i)
  let u : ℕ → ℚ := fun i => (x i : ℚ)+1
  have hprod : (∏ i ∈ Finset.range b, r i) =
      (3 : ℚ)^(∑ i ∈ Finset.range b, q i) /
        2^(∑ i ∈ Finset.range b, (q i+e i)) := by
    simp only [r, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
  obtain ⟨z, hclose, hdom, hzstep⟩ := affinePath_cycle_envelope b r s u
    (fun i _ => by dsimp [r]; positivity)
    (fun i hi => headBlock_conjugate (hid i hi))
    (by rwa [hprod]) (by dsimp [u]; exact_mod_cast Nat.add_lt_add_right hup 1)
  have hz (i : Fin b) : (2 : ℚ)^(q i.val) ≤ z i.val := by
    obtain ⟨w, hw, _⟩ := headBlock_scale (hid i.val i.isLt)
    have hwpos : 1 ≤ w := by
      by_contra hn
      have : w = 0 := by omega
      simp [this] at hw
    have hlow : 2^(q i.val) ≤ x i.val+1 := by
      rw [hw]
      simpa using Nat.mul_le_mul_left (2^(q i.val)) hwpos
    exact le_trans (by dsimp [u]; exact_mod_cast hlow) (hdom i.val i.isLt.le).le
  have hcycle (i : Fin b) : z (finRotate b i).val =
      (3 : ℚ)^(q i.val)/2^(q i.val+e i.val)*z i.val+(1-1/2^(e i.val)) := by
    rw [finRotate_value_of_closed_path hb z hclose i]
    exact hzstep i.val i.isLt
  have hprodFin : (∏ i : Fin b, (3 : ℚ)^(q i.val)/2^(q i.val+e i.val)) =
      (3 : ℚ)^(∑ i ∈ Finset.range b, q i) /
        2^(∑ i ∈ Finset.range b, (q i+e i)) := by
    simpa only [← hprod] using Fin.prod_univ_eq_prod_range r b
  constructor
  · have h := affineBlockCycle_mass_bound hb (fun i => q i.val) (fun i => e i.val)
      (fun i => z i.val) (fun i => hq i.val i.isLt) hz hcycle
      (by rwa [hprodFin])
    simpa only [Fin.sum_univ_eq_sum_range, hprodFin] using h
  · have hz2 (i : Fin b) : (2 : ℚ) ≤ z i.val := by
      apply le_trans ?_ (hz i)
      simpa using pow_le_pow_right₀ (show (1 : ℚ) ≤ 2 by norm_num)
        (show 1 ≤ q i.val by have := hq i.val i.isLt; omega)
    have hs (i : Fin b) : s i.val < 1 := by
      dsimp [s]
      have : (0 : ℚ) < 1/2^(e i.val) := by positivity
      linarith
    have h := affineCycle_multiplier_lower b hb (finRotate b)
      (fun i => r i.val) (fun i => s i.val) (fun i => z i.val) hz2 hs hcycle
    change 1 < 2^b * (∏ i : Fin b, (3 : ℚ)^(q i.val)/2^(q i.val+e i.val)) at h
    rw [hprodFin, ← mul_div_assoc] at h
    simpa only [one_mul] using (lt_div_iff₀ (by positivity)).1 h

end CollatzMoonshot.FrontA
