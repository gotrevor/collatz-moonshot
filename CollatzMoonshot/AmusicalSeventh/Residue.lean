/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalContinuousReversor.Cylinder

namespace CollatzMoonshot.Amusical

/-- Equality of a set with its image under a bijection makes membership invariant. -/
theorem mem_iff_mem_iterate_of_image_eq (f : Equiv.Perm ℤ) (m : ℕ) (S : Set ℤ)
    (h : (f^[m]) '' S = S) (n : ℤ) : n ∈ S ↔ f^[m] n ∈ S := by
  constructor
  · intro hn
    rw [← h]
    exact ⟨n, hn, rfl⟩
  · intro hn
    rw [← h] at hn
    obtain ⟨a, ha, han⟩ := hn
    have : a = n := (f.injective.iterate m) han
    simpa [this] using ha

/-- Membership is consequently invariant under every natural iterate of the bijection. -/
theorem mem_iff_mem_mul_iterate_of_image_eq (f : Equiv.Perm ℤ) (m k : ℕ) (S : Set ℤ)
    (h : (f^[m]) '' S = S) (n : ℤ) : n ∈ S ↔ f^[m * k] n ∈ S := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
      rw [Nat.mul_succ, Function.iterate_add_apply]
      exact (mem_iff_mem_iterate_of_image_eq f m S h n).trans (ih (f^[m] n))

/-- On a sufficiently long forward cylinder, one residue modulo a power of two can be sent to
any other residue.  The time can moreover be required to be a multiple of `m`. -/
theorem exists_amusical_mul_iterate_modEq_pow_two (m b : ℕ) (hm : 0 < m) (x y : ℤ) :
    ∃ k : ℕ, ∃ z : ℤ, x ≡ z [ZMOD (2 : ℤ) ^ b] ∧
      amusical^[m * k] z ≡ y [ZMOD (2 : ℤ) ^ b] := by
  let k := b + 1
  let t := m * k
  have hbt : b ≤ t := by
    dsimp [t, k]
    calc
      b ≤ 1 * (b + 1) := by omega
      _ ≤ m * (b + 1) := Nat.mul_le_mul_right _ hm
  have hcop : IsCoprime ((2 : ℤ) ^ b) ((3 : ℤ) ^ t) := by
    exact (by norm_num : IsCoprime (2 : ℤ) 3).pow
  obtain ⟨q, hq⟩ := exists_mul_modEq_of_isCoprime hcop
      (d := y - amusical^[t] x)
  refine ⟨k, x + amusicalForwardPeriod t x * q, ?_, ?_⟩
  · rw [Int.modEq_iff_dvd]
    simpa only [add_sub_cancel_left] using dvd_mul_of_dvd_left
      ((pow_dvd_pow (2 : ℤ) hbt).trans (pow_two_dvd_amusicalForwardPeriod t x)) q
  · change amusical^[t] (x + amusicalForwardPeriod t x * q) ≡ y
        [ZMOD (2 : ℤ) ^ b]
    rw [amusical_iterate_add_forwardPeriod_mul]
    calc
      amusical^[t] x + 3 ^ t * q ≡
          amusical^[t] x + (y - amusical^[t] x) [ZMOD (2 : ℤ) ^ b] :=
        hq.add_left _
      _ = y := by ring

/-- The residue-transitivity target is complete for every power-of-two modulus. -/
theorem amusical_pow_classUnion_invariant_pow_two (m b : ℕ) (hm : 0 < m)
    (R : Set (ZMod (2 ^ b)))
    (h : (amusical^[m]) '' {n : ℤ | (n : ZMod (2 ^ b)) ∈ R} =
      {n : ℤ | (n : ZMod (2 ^ b)) ∈ R}) :
    R = ∅ ∨ R = Set.univ := by
  classical
  by_cases hR : R = ∅
  · exact Or.inl hR
  · right
    obtain ⟨r, hr⟩ := Set.nonempty_iff_ne_empty.mpr hR
    ext s
    simp only [Set.mem_univ, iff_true]
    let x : ℤ := r.cast
    let y : ℤ := s.cast
    obtain ⟨k, z, hxz, hzy⟩ := exists_amusical_mul_iterate_modEq_pow_two m b hm x y
    have hx : (x : ZMod (2 ^ b)) ∈ R := by
      simpa [x] using hr
    have hz : (z : ZMod (2 ^ b)) ∈ R := by
      have heq : (x : ZMod (2 ^ b)) = (z : ZMod (2 ^ b)) :=
        (ZMod.intCast_eq_intCast_iff x z (2 ^ b)).2 hxz
      exact heq ▸ hx
    have hit : (amusical^[m * k] z : ZMod (2 ^ b)) ∈ R :=
      (mem_iff_mem_mul_iterate_of_image_eq amusicalPerm m k _ h z).mp hz
    have heq : (amusical^[m * k] z : ZMod (2 ^ b)) = (y : ZMod (2 ^ b)) :=
      (ZMod.intCast_eq_intCast_iff _ y (2 ^ b)).2 hzy
    have hy : (y : ZMod (2 ^ b)) ∈ R := heq ▸ hit
    simpa [y] using hy

/-- On a sufficiently long backward cylinder, one residue modulo a power of three can be sent to
any other residue.  Equivalently, the corresponding forward time can be required to be a multiple
of `m`. -/
theorem exists_amusical_mul_iterate_modEq_pow_three (m b : ℕ) (hm : 0 < m) (x y : ℤ) :
    ∃ k : ℕ, ∃ z : ℤ, x ≡ z [ZMOD (3 : ℤ) ^ b] ∧
      amusical^[m * k] z ≡ y [ZMOD (3 : ℤ) ^ b] := by
  let k := b + 1
  let t := m * k
  have hbt : b ≤ t := by
    dsimp [t, k]
    calc
      b ≤ 1 * (b + 1) := by omega
      _ ≤ m * (b + 1) := Nat.mul_le_mul_right _ hm
  have hcop : IsCoprime ((3 : ℤ) ^ b)
      ((2 : ℤ) ^ (t + amusicalBackwardFourCount t y)) := by
    exact (show IsCoprime (3 : ℤ) 2 from ⟨1, -1, by norm_num⟩).pow
  obtain ⟨q, hq⟩ := exists_mul_modEq_of_isCoprime hcop
      (d := x - amusicalInv^[t] y)
  let w := y + (3 : ℤ) ^ t * q
  let z := amusicalInv^[t] w
  refine ⟨k, z, ?_, ?_⟩
  · change x ≡ amusicalInv^[t] w [ZMOD (3 : ℤ) ^ b]
    rw [show w = y + (3 : ℤ) ^ t * q by rfl]
    rw [amusicalInv_iterate_add_pow_three_mul_slope t t le_rfl]
    simp only [Nat.sub_self, pow_zero, one_mul]
    calc
      x ≡ amusicalInv^[t] y + (x - amusicalInv^[t] y) [ZMOD (3 : ℤ) ^ b] := by
        have heq : amusicalInv^[t] y + (x - amusicalInv^[t] y) = x := by ring
        rw [heq]
      _ ≡ amusicalInv^[t] y +
          2 ^ (t + amusicalBackwardFourCount t y) * q [ZMOD (3 : ℤ) ^ b] :=
        hq.symm.add_left _
  · change amusical^[t] z ≡ y [ZMOD (3 : ℤ) ^ b]
    rw [show z = amusicalInv^[t] w by rfl, amusical_iterate_amusicalInv_iterate]
    rw [Int.modEq_iff_dvd]
    rw [show y - w = -(3 ^ t * q) by simp [w]]
    exact dvd_neg.mpr (dvd_mul_of_dvd_left (pow_dvd_pow (3 : ℤ) hbt) q)

/-- The residue-transitivity target is complete for every power-of-three modulus. -/
theorem amusical_pow_classUnion_invariant_pow_three (m b : ℕ) (hm : 0 < m)
    (R : Set (ZMod (3 ^ b)))
    (h : (amusical^[m]) '' {n : ℤ | (n : ZMod (3 ^ b)) ∈ R} =
      {n : ℤ | (n : ZMod (3 ^ b)) ∈ R}) :
    R = ∅ ∨ R = Set.univ := by
  classical
  by_cases hR : R = ∅
  · exact Or.inl hR
  · right
    obtain ⟨r, hr⟩ := Set.nonempty_iff_ne_empty.mpr hR
    ext s
    simp only [Set.mem_univ, iff_true]
    let x : ℤ := r.cast
    let y : ℤ := s.cast
    obtain ⟨k, z, hxz, hzy⟩ := exists_amusical_mul_iterate_modEq_pow_three m b hm x y
    have hx : (x : ZMod (3 ^ b)) ∈ R := by
      simpa [x] using hr
    have hz : (z : ZMod (3 ^ b)) ∈ R := by
      have heq : (x : ZMod (3 ^ b)) = (z : ZMod (3 ^ b)) :=
        (ZMod.intCast_eq_intCast_iff x z (3 ^ b)).2 hxz
      exact heq ▸ hx
    have hit : (amusical^[m * k] z : ZMod (3 ^ b)) ∈ R :=
      (mem_iff_mem_mul_iterate_of_image_eq amusicalPerm m k _ h z).mp hz
    have heq : (amusical^[m * k] z : ZMod (3 ^ b)) = (y : ZMod (3 ^ b)) :=
      (ZMod.intCast_eq_intCast_iff _ y (3 ^ b)).2 hzy
    have hy : (y : ZMod (3 ^ b)) ∈ R := heq ▸ hit
    simpa [y] using hy

private theorem periodic_eq_of_modEq {S : ℤ → Prop} {M a b : ℤ}
    (hper : Function.Periodic S M) (hab : a ≡ b [ZMOD M]) (x : ℤ) :
    S (x + a) = S (x + b) := by
  rw [Int.modEq_iff_dvd] at hab
  obtain ⟨q, hq⟩ := hab
  have hp := hper.int_mul q (x + a)
  calc
    S (x + a) = S ((x + a) + q * M) := by simpa using hp.symm
    _ = S (x + b) := by
      rw [show (x + a) + q * M = x + b by linear_combination -hq]

private theorem isCoprime_right_of_modEq {M a b : ℤ} (ha : IsCoprime M a)
    (hab : a ≡ b [ZMOD M]) : IsCoprime M b := by
  obtain ⟨u, v, huv⟩ := ha
  rw [Int.modEq_iff_dvd] at hab
  obtain ⟨q, hq⟩ := hab
  refine ⟨u - v * q, v, ?_⟩
  linear_combination huv + v * hq

/-- A periodic predicate invariant under a long `amusical` iterate does not see the
two-primary part of its period. -/
private theorem periodic_strip_two (t M : ℕ) (hM : M ≠ 0)
    (ht : M.factorization 2 ≤ t) (S : ℤ → Prop)
    (hper : Function.Periodic S (M : ℤ))
    (hinv : ∀ n, S (amusical^[t] n) = S n) :
    Function.Periodic S (ordCompl[2] M : ℤ) := by
  let a := M.factorization 2
  let D := ordCompl[2] M
  have hdecomp : (M : ℤ) = (2 : ℤ) ^ a * D := by
    exact_mod_cast (Nat.ordProj_mul_ordCompl_eq_self M 2).symm
  have hcop : IsCoprime ((2 : ℤ) ^ a) ((3 : ℤ) ^ t) :=
    (show IsCoprime (2 : ℤ) 3 from ⟨-1, 1, by norm_num⟩).pow
  obtain ⟨k, hk⟩ := exists_mul_modEq_of_isCoprime hcop (d := 1)
  intro y
  let n := amusicalInv^[t] y
  let q : ℤ := D * k
  have hpow : (2 : ℤ) ^ a ∣ amusicalForwardPeriod t n :=
    (pow_dvd_pow (2 : ℤ) ht).trans (pow_two_dvd_amusicalForwardPeriod t n)
  obtain ⟨c, hc⟩ := hpow
  have hinput : S (n + amusicalForwardPeriod t n * q) = S n := by
    have hp := hper.int_mul (c * k) n
    rw [show ((c * k : ℤ) : ℤ) = c * k by rfl] at hp
    convert hp using 1 <;> dsimp [q] <;> rw [hc, hdecomp] <;> ring
  have hout : S (amusical^[t] n + 3 ^ t * q) = S (amusical^[t] n) := by
    calc
      S (amusical^[t] n + 3 ^ t * q) =
          S (amusical^[t] (n + amusicalForwardPeriod t n * q)) := by
            rw [amusical_iterate_add_forwardPeriod_mul]
      _ = S (n + amusicalForwardPeriod t n * q) := hinv _
      _ = S n := hinput
      _ = S (amusical^[t] n) := (hinv n).symm
  have hshift : (3 : ℤ) ^ t * D * k ≡ D [ZMOD M] := by
    rw [Int.modEq_iff_dvd] at hk ⊢
    obtain ⟨c', hc'⟩ := hk
    refine ⟨c', ?_⟩
    rw [hdecomp]
    linear_combination D * hc'
  have hout' : S (y + (3 : ℤ) ^ t * D * k) = S y := by
    dsimp [n, q] at hout ⊢
    rw [amusical_iterate_amusicalInv_iterate] at hout
    simpa [mul_assoc] using hout
  calc
    S (y + D) = S (y + (3 : ℤ) ^ t * D * k) :=
      periodic_eq_of_modEq hper hshift.symm y
    _ = S y := hout'

/-- The backward cylinder gives the analogous removal of the three-primary period. -/
private theorem periodic_strip_three (t M : ℕ) (hM : M ≠ 0)
    (ht : M.factorization 3 ≤ t) (S : ℤ → Prop)
    (hper : Function.Periodic S (M : ℤ))
    (hinv : ∀ n, S (amusical^[t] n) = S n) :
    Function.Periodic S (ordCompl[3] M : ℤ) := by
  let a := M.factorization 3
  let D := ordCompl[3] M
  have hdecomp : (M : ℤ) = (3 : ℤ) ^ a * D := by
    exact_mod_cast (Nat.ordProj_mul_ordCompl_eq_self M 3).symm
  intro y
  let n := amusical^[t] y
  have hcop : IsCoprime ((3 : ℤ) ^ a) (amusicalBackwardMultiplier t n) := by
    rw [amusicalBackwardMultiplier_eq]
    exact (show IsCoprime (3 : ℤ) 2 from ⟨1, -1, by norm_num⟩).pow
  obtain ⟨k, hk⟩ := exists_mul_modEq_of_isCoprime hcop (d := 1)
  let q : ℤ := D * k
  have hpow : (3 : ℤ) ^ a ∣ (3 : ℤ) ^ t := pow_dvd_pow 3 ht
  obtain ⟨c, hc⟩ := hpow
  have hinput : S (n + (3 : ℤ) ^ t * q) = S n := by
    have hp := hper.int_mul (c * k) n
    rw [show ((c * k : ℤ) : ℤ) = c * k by rfl] at hp
    convert hp using 1 <;> dsimp [q] <;> rw [hc, hdecomp] <;> ring
  have hinvBack : ∀ z, S (amusicalInv^[t] z) = S z := by
    intro z
    have hz := hinv (amusicalInv^[t] z)
    rw [amusical_iterate_amusicalInv_iterate] at hz
    exact hz.symm
  have hout : S (amusicalInv^[t] n + amusicalBackwardMultiplier t n * q) =
      S (amusicalInv^[t] n) := by
    calc
      S (amusicalInv^[t] n + amusicalBackwardMultiplier t n * q) =
          S (amusicalInv^[t] (n + (3 : ℤ) ^ t * q)) := by
            rw [amusicalInv_iterate_add_pow_three_mul_exact t t le_rfl]
            simp
      _ = S (n + (3 : ℤ) ^ t * q) := hinvBack _
      _ = S n := hinput
      _ = S (amusicalInv^[t] n) := (hinvBack n).symm
  have hshift : amusicalBackwardMultiplier t n * D * k ≡ D [ZMOD M] := by
    rw [Int.modEq_iff_dvd] at hk ⊢
    obtain ⟨c', hc'⟩ := hk
    refine ⟨c', ?_⟩
    rw [hdecomp]
    linear_combination D * hc'
  have hout' : S (y + amusicalBackwardMultiplier t n * D * k) = S y := by
    dsimp [n, q] at hout ⊢
    rw [amusicalInv_iterate_amusical_iterate] at hout
    simpa [mul_assoc] using hout
  calc
    S (y + D) = S (y + amusicalBackwardMultiplier t n * D * k) :=
      periodic_eq_of_modEq hper hshift.symm y
    _ = S y := hout'

/-- The input at the start of a word consisting of one `B` branch followed by `k` `A`
branches. -/
private def mixedBase (k : ℕ) : ℤ :=
  4 * ∑ i ∈ Finset.range k, (4 : ℤ) ^ i + 3

private theorem three_mul_geom_four_add_one (k : ℕ) :
    3 * (∑ i ∈ Finset.range k, (4 : ℤ) ^ i) + 1 = 4 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, pow_succ]
      linear_combination ih

private theorem mixedBase_relation (k : ℕ) :
    3 * mixedBase k = (4 : ℤ) ^ (k + 1) + 5 := by
  rw [mixedBase, pow_succ]
  linear_combination 4 * three_mul_geom_four_add_one k

private theorem amusical_iterate_allA (t : ℕ) (q : ℤ) :
    amusical^[t] (1 + (4 : ℤ) ^ t * q) = 1 + (3 : ℤ) ^ t * q := by
  induction t generalizing q with
  | zero => simp
  | succ t ih =>
      rw [Function.iterate_succ_apply]
      rw [show 1 + (4 : ℤ) ^ (t + 1) * q = 4 * (4 ^ t * q) + 1 by
        rw [pow_succ]; ring]
      rw [amusical_four_mul_add_one]
      convert ih (3 * q) using 1 <;> ring

private theorem amusical_iterate_mixed (k : ℕ) (q : ℤ) :
    amusical^[k + 1] (mixedBase k + (4 : ℤ) ^ (k + 1) * q) =
      1 + (3 : ℤ) ^ k + (3 : ℤ) ^ (k + 1) * q := by
  rw [Function.iterate_succ_apply]
  rw [show mixedBase k + (4 : ℤ) ^ (k + 1) * q =
      4 * ((∑ i ∈ Finset.range k, (4 : ℤ) ^ i) + 4 ^ k * q) + 3 by
    rw [mixedBase, pow_succ]; ring]
  rw [amusical_four_mul_add_three]
  have hfirst :
      3 * ((∑ i ∈ Finset.range k, (4 : ℤ) ^ i) + 4 ^ k * q) + 2 =
        1 + 4 ^ k * (1 + 3 * q) := by
    linear_combination three_mul_geom_four_add_one k
  rw [hfirst, amusical_iterate_allA]
  ring

/-- Once the period is coprime to `6`, the all-`A` word and the word `B A^k` force a
translation by a unit, hence make the predicate constant. -/
private theorem constant_of_periodic_coprime_two_three (m N : ℕ) (hm : 0 < m)
    (hN : N ≠ 0) (hN2 : Nat.Coprime N 2) (hN3 : Nat.Coprime N 3)
    (S : ℤ → Prop) (hper : Function.Periodic S (N : ℤ))
    (hinv : ∀ n, S (amusical^[m] n) = S n) : ∀ x y, S x = S y := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have hN2z : IsCoprime (N : ℤ) 2 := hN2.isCoprime
  have hN3z : IsCoprime (N : ℤ) 3 := hN3.isCoprime
  have hN4 : IsCoprime (N : ℤ) ((4 : ℤ) ^ (k + 1)) := by
    rw [show (4 : ℤ) ^ (k + 1) = 2 ^ (2 * (k + 1)) by rw [pow_mul]; norm_num]
    exact hN2z.pow_right
  obtain ⟨d, hd⟩ := exists_mul_modEq_of_isCoprime hN4
    (d := 1 - mixedBase k)
  let δ : ℤ := 3 ^ k + 3 ^ (k + 1) * d
  have hrel : (4 : ℤ) ^ (k + 1) * δ ≡ -2 * 3 ^ k [ZMOD N] := by
    calc
      (4 : ℤ) ^ (k + 1) * δ =
          4 ^ (k + 1) * 3 ^ k + 3 ^ (k + 1) * (4 ^ (k + 1) * d) := by
            simp only [δ]; ring
      _ ≡ 4 ^ (k + 1) * 3 ^ k + 3 ^ (k + 1) * (1 - mixedBase k) [ZMOD N] :=
        (hd.mul_left (3 ^ (k + 1))).add_left _
      _ = -2 * 3 ^ k := by
        rw [pow_succ]
        linear_combination -(3 ^ k) * mixedBase_relation k
  have hunit : IsCoprime (N : ℤ) (-2 * 3 ^ k) :=
    (hN2z.mul_right hN3z.pow_right).neg_right
  have hδ : IsCoprime (N : ℤ) δ :=
    (isCoprime_right_of_modEq hunit hrel.symm).of_mul_right_right
  have hperδ : Function.Periodic S δ := by
    intro y
    have hN3pow : IsCoprime (N : ℤ) ((3 : ℤ) ^ (k + 1)) := hN3z.pow_right
    obtain ⟨q, hq⟩ := exists_mul_modEq_of_isCoprime hN3pow (d := y - 1)
    have hstart : mixedBase k + 4 ^ (k + 1) * (q + d) ≡
        1 + 4 ^ (k + 1) * q [ZMOD N] := by
      calc
        mixedBase k + 4 ^ (k + 1) * (q + d) =
            mixedBase k + 4 ^ (k + 1) * q + 4 ^ (k + 1) * d := by ring
        _ ≡ mixedBase k + 4 ^ (k + 1) * q + (1 - mixedBase k) [ZMOD N] :=
          hd.add_left _
        _ = 1 + 4 ^ (k + 1) * q := by ring
    have hout : S (1 + 3 ^ k + 3 ^ (k + 1) * (q + d)) =
        S (1 + 3 ^ (k + 1) * q) := by
      calc
        S (1 + 3 ^ k + 3 ^ (k + 1) * (q + d)) =
            S (amusical^[k + 1] (mixedBase k + 4 ^ (k + 1) * (q + d))) := by
              rw [amusical_iterate_mixed]
        _ = S (mixedBase k + 4 ^ (k + 1) * (q + d)) := hinv _
        _ = S (1 + 4 ^ (k + 1) * q) := by
          simpa using periodic_eq_of_modEq hper hstart 0
        _ = S (amusical^[k + 1] (1 + 4 ^ (k + 1) * q)) := (hinv _).symm
        _ = S (1 + 3 ^ (k + 1) * q) := by rw [amusical_iterate_allA]
    have hout' : S ((1 + 3 ^ (k + 1) * q) + δ) =
        S (1 + 3 ^ (k + 1) * q) := by
      convert hout using 1 <;> dsimp [δ] <;> ring
    have hy : 1 + (3 : ℤ) ^ (k + 1) * q ≡ y [ZMOD N] := by
      convert hq.add_left 1 using 1 <;> ring
    calc
      S (y + δ) = S ((1 + 3 ^ (k + 1) * q) + δ) :=
        by simpa using periodic_eq_of_modEq hper (hy.add_right δ).symm 0
      _ = S (1 + 3 ^ (k + 1) * q) := hout'
      _ = S y := by simpa using periodic_eq_of_modEq hper hy 0
  intro x y
  obtain ⟨j, hj⟩ := exists_mul_modEq_of_isCoprime hδ (d := y - x)
  have hxy : x + j * δ ≡ y [ZMOD N] := by
    convert hj.add_left x using 1 <;> ring
  calc
    S x = S (x + j * δ) := (hperδ.int_mul j x).symm
    _ = S y := by simpa using periodic_eq_of_modEq hper hxy 0

/-- Full residue transitivity, obtained by stripping the primary periods before applying the
coprime affine-word translation. -/
theorem amusical_pow_classUnion_invariant_of_image_eq (m M : ℕ) (hm : 0 < m) (hM : 0 < M)
    (R : Set (ZMod M))
    (h : (amusical^[m]) '' {n : ℤ | (n : ZMod M) ∈ R} =
      {n : ℤ | (n : ZMod M) ∈ R}) :
    R = ∅ ∨ R = Set.univ := by
  classical
  let S : ℤ → Prop := fun n => (n : ZMod M) ∈ R
  let t := m * M
  have hMt : M ≤ t := by
    dsimp [t]
    simpa using Nat.mul_le_mul_right M hm
  have hperM : Function.Periodic S (M : ℤ) := by
    intro n
    apply propext
    change ((n + M : ℤ) : ZMod M) ∈ R ↔ (n : ZMod M) ∈ R
    simp
  have hinvM : ∀ n, S (amusical^[t] n) = S n := by
    intro n
    apply propext
    exact (mem_iff_mem_mul_iterate_of_image_eq amusicalPerm m M _ h n).symm
  let D := ordCompl[2] M
  let N := ordCompl[3] D
  have hD0 : D ≠ 0 := (Nat.ordCompl_pos 2 hM.ne').ne'
  have hN0 : N ≠ 0 := (Nat.ordCompl_pos 3 hD0).ne'
  have hperD : Function.Periodic S (D : ℤ) := by
    apply periodic_strip_two t M hM.ne' _ S hperM hinvM
    exact (Nat.factorization_lt 2 hM.ne').le.trans hMt
  have hperN : Function.Periodic S (N : ℤ) := by
    apply periodic_strip_three t D hD0 _ S hperD hinvM
    exact (Nat.factorization_lt 3 hD0).le.trans
      ((Nat.ordCompl_le M 2).trans hMt)
  have hN2 : Nat.Coprime N 2 := by
    exact (Nat.coprime_ordCompl Nat.prime_two hM.ne').symm.coprime_dvd_left
      (Nat.ordCompl_dvd D 3)
  have hN3 : Nat.Coprime N 3 := (Nat.coprime_ordCompl (by norm_num) hD0).symm
  have hinvm : ∀ n, S (amusical^[m] n) = S n := by
    intro n
    apply propext
    exact (mem_iff_mem_iterate_of_image_eq amusicalPerm m _ h n).symm
  have hconst : ∀ x y, S x = S y :=
    constant_of_periodic_coprime_two_three m N hm hN0 hN2 hN3 S hperN hinvm
  by_cases hR : R = ∅
  · exact Or.inl hR
  · right
    obtain ⟨r, hr⟩ := Set.nonempty_iff_ne_empty.mpr hR
    ext s
    simp only [Set.mem_univ, iff_true]
    let x : ℤ := r.cast
    let y : ℤ := s.cast
    have hx : S x := by simpa [S, x] using hr
    have hy : S y := (hconst x y) ▸ hx
    simpa [S, y] using hy

end CollatzMoonshot.Amusical
