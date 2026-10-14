/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalLogBalance.Transport

/-!
# Finite reciprocal-weight estimates for the amusical permutation

The even branch transports exactly to multiples of three.  The two odd branches differ from
weight factor `4/3` by a telescoping error, while the unmatched cutoff intervals are controlled
by elementary cardinality bounds.  These estimates imply the uniform even and three-divisibility
balances used by `AmusicalLogBalance.lean`.
-/

namespace CollatzMoonshot.Amusical

open Classical in
theorem reciprocal_sum_filter_Icc_le (P : ℤ → Prop) [DecidablePred P] {a b : ℤ}
    (ha : 0 < a) (hab : a ≤ b + 1) :
    ∑ n ∈ (Finset.Icc a b).filter P, (1 : ℝ) / n ≤
      ((b + 1 - a : ℤ) : ℝ) / a := by
  calc
    ∑ n ∈ (Finset.Icc a b).filter P, (1 : ℝ) / n ≤
        ∑ _n ∈ (Finset.Icc a b).filter P, (1 : ℝ) / a := by
      apply Finset.sum_le_sum
      intro n hn
      have han : a ≤ n := (Finset.mem_Icc.1 (Finset.mem_filter.1 hn).1).1
      exact one_div_le_one_div_of_le (by exact_mod_cast ha) (by exact_mod_cast han)
    _ = (((Finset.Icc a b).filter P).card : ℝ) / a := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ ((Finset.Icc a b).card : ℝ) / a := by
      gcongr
      exact Finset.filter_subset P (Finset.Icc a b)
    _ = ((b + 1 - a : ℤ) : ℝ) / a := by
      congr 1
      exact_mod_cast Int.card_Icc_of_le a b hab

theorem half_reciprocal_telescope {x : ℝ} (hx : 1 < x) :
    (1 / 2 : ℝ) * (1 / (x - 1) - 1 / x) = 1 / (2 * x * (x - 1)) := by
  have hx0 : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  have hxm : x - 1 ≠ 0 := ne_of_gt (sub_pos.2 hx)
  field_simp [hx0, hxm]
  ring

theorem amusical_odd_pos {n : ℤ} (hn : 0 < n) (hodd : ¬ 2 ∣ n) :
    0 < amusical n := by
  unfold amusical
  split_ifs <;> omega

theorem amusical_odd_le {n : ℤ} (hn : 0 < n) (hodd : ¬ 2 ∣ n) :
    amusical n ≤ n := by
  unfold amusical
  split_ifs <;> omega

theorem amusical_odd_not_three {n : ℤ} (hodd : ¬ 2 ∣ n) :
    ¬ 3 ∣ amusical n := by
  unfold amusical
  split_ifs <;> omega

theorem amusicalInv_pos_of_pos {m : ℤ} (hm : 0 < m) : 0 < amusicalInv m := by
  unfold amusicalInv
  split_ifs <;> omega

theorem amusicalInv_odd_of_not_three {m : ℤ} (h3 : ¬ 3 ∣ m) : ¬ 2 ∣ amusicalInv m := by
  unfold amusicalInv
  split_ifs <;> omega

theorem two_mul_amusicalInv_le_three_mul {m : ℤ} (hm : 0 < m) (h3 : ¬ 3 ∣ m) :
    2 * amusicalInv m ≤ 3 * m := by
  unfold amusicalInv
  split_ifs <;> omega

theorem amusical_odd_reciprocal_error {n : ℤ} (hn : 0 < n) (hodd : ¬ 2 ∣ n) :
    |(1 : ℝ) / amusical n - 4 / (3 * n)| ≤
      if n = 1 then 1 / 3 else
        (1 / 2 : ℝ) * (1 / (n - 1) - 1 / n) := by
  by_cases hn1 : n = 1
  · subst n
    norm_num [amusical]
  · rw [if_neg hn1]
    have hn3 : 3 ≤ n := by omega
    have hmod : n % 4 = 1 ∨ n % 4 = 3 := by omega
    rcases hmod with hmod | hmod
    · let k := n / 4
      have hk : 1 ≤ k := by dsimp [k]; omega
      have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have hnform : n = 4 * k + 1 := by dsimp [k]; omega
      rw [hnform, amusical_four_mul_add_one]
      have hsign : (1 : ℝ) / (3 * k + 1) - 4 / (3 * (4 * k + 1)) ≤ 0 := by
        field_simp
        nlinarith
      push_cast at hsign ⊢
      rw [abs_of_nonpos hsign]
      have herr :
          -(1 / (3 * (k : ℝ) + 1) - 4 / (3 * (4 * (k : ℝ) + 1))) =
            1 / (3 * (4 * (k : ℝ) + 1) * (3 * (k : ℝ) + 1)) := by
        field_simp
        ring
      have htel := half_reciprocal_telescope (x := 4 * (k : ℝ) + 1) (by nlinarith)
      rw [herr, htel]
      apply one_div_le_one_div_of_le (mul_pos
        (mul_pos (by norm_num) (by nlinarith : 0 < (4 : ℝ) * k + 1))
        (by nlinarith : 0 < (4 : ℝ) * k + 1 - 1))
      have hsmall : 2 * (4 * (k : ℝ) + 1 - 1) ≤ 3 * (3 * (k : ℝ) + 1) := by
        nlinarith
      have hmul := mul_le_mul_of_nonneg_left hsmall
        (show 0 ≤ (4 : ℝ) * k + 1 by positivity)
      ring_nf at hmul ⊢
      exact hmul
    · let k := n / 4
      have hk : 0 ≤ k := by dsimp [k]; omega
      have hkr : (0 : ℝ) ≤ k := by exact_mod_cast hk
      have hnform : n = 4 * k + 3 := by dsimp [k]; omega
      rw [hnform, amusical_four_mul_add_three]
      have hsign : 0 ≤ (1 : ℝ) / (3 * k + 2) - 4 / (3 * (4 * k + 3)) := by
        field_simp
        nlinarith
      push_cast at hsign ⊢
      rw [abs_of_nonneg hsign]
      have herr :
          1 / (3 * (k : ℝ) + 2) - 4 / (3 * (4 * (k : ℝ) + 3)) =
            1 / (3 * (4 * (k : ℝ) + 3) * (3 * (k : ℝ) + 2)) := by
        field_simp
        ring
      have htel := half_reciprocal_telescope (x := 4 * (k : ℝ) + 3) (by nlinarith)
      rw [herr, htel]
      apply one_div_le_one_div_of_le (mul_pos
        (mul_pos (by norm_num) (by nlinarith : 0 < (4 : ℝ) * k + 3))
        (by nlinarith : 0 < (4 : ℝ) * k + 3 - 1))
      have hsmall : 2 * (4 * (k : ℝ) + 3 - 1) ≤ 3 * (3 * (k : ℝ) + 2) := by
        nlinarith
      have hmul := mul_le_mul_of_nonneg_left hsmall
        (show 0 ≤ (4 : ℝ) * k + 3 by positivity)
      ring_nf at hmul ⊢
      exact hmul

theorem sum_half_reciprocal_telescope_range (K : ℕ) :
    ∑ j ∈ Finset.range K, (1 / 2 : ℝ) *
        (1 / (j + 2) - 1 / (j + 3)) =
      (1 / 2 : ℝ) * (1 / 2 - 1 / (K + 2)) := by
  induction K with
  | zero => norm_num
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      field_simp
      ring

theorem sum_half_reciprocal_telescope_Icc (N : ℕ) (hN : 3 ≤ N) :
    ∑ n ∈ Finset.Icc (3 : ℤ) N,
        (1 / 2 : ℝ) * (1 / (n - 1) - 1 / n) ≤ 1 / 4 := by
  have hbij :
      ∑ j ∈ Finset.range (N - 2), (1 / 2 : ℝ) *
          (1 / (j + 2) - 1 / (j + 3)) =
        ∑ n ∈ Finset.Icc (3 : ℤ) N,
          (1 / 2 : ℝ) * (1 / (n - 1) - 1 / n) := by
    apply Finset.sum_bij (fun j _ ↦ ((j + 3 : ℕ) : ℤ))
    · intro j hj
      simp only [Finset.mem_range] at hj
      simp only [Finset.mem_Icc]
      constructor <;> omega
    · intro a ha b hb hab
      have : a + 3 = b + 3 := by exact_mod_cast hab
      omega
    · intro n hn
      simp only [Finset.mem_Icc] at hn
      refine ⟨n.toNat - 3, ?_, ?_⟩
      · simp only [Finset.mem_range]
        omega
      · omega
    · intro j hj
      push_cast
      ring
  rw [← hbij, sum_half_reciprocal_telescope_range]
  have : (0 : ℝ) ≤ 1 / (((N - 2 : ℕ) : ℝ) + 2) :=
    one_div_nonneg.mpr (by positivity)
  linarith

open Classical in
theorem sum_amusical_odd_reciprocal_error (S : Set ℤ) (N : ℕ) (hN : 3 ≤ N) :
    ∑ n ∈ (Finset.Icc (1 : ℤ) N).filter (fun n ↦ n ∈ S ∧ ¬ 2 ∣ n),
        |(1 : ℝ) / amusical n - 4 / (3 * n)| ≤ 2 / 3 := by
  let R := (Finset.Icc (1 : ℤ) N).filter (fun n ↦ n ∈ S ∧ ¬ 2 ∣ n)
  let T := insert (1 : ℤ) (Finset.Icc (3 : ℤ) N)
  let g : ℤ → ℝ := fun n ↦
    if n = 1 then 1 / 3 else (1 / 2) * (1 / (n - 1) - 1 / n)
  have hRT : R ⊆ T := by
    intro n hn
    simp only [R, Finset.mem_filter, Finset.mem_Icc] at hn
    simp only [T, Finset.mem_insert, Finset.mem_Icc]
    rcases hn with ⟨⟨hn1, hnN⟩, _hnS, hnodd⟩
    by_cases hn_eq : n = 1
    · exact Or.inl hn_eq
    · exact Or.inr ⟨by omega, hnN⟩
  calc
    ∑ n ∈ (Finset.Icc (1 : ℤ) N).filter (fun n ↦ n ∈ S ∧ ¬ 2 ∣ n),
        |(1 : ℝ) / amusical n - 4 / (3 * n)| =
        ∑ n ∈ R, |(1 : ℝ) / amusical n - 4 / (3 * n)| := by rfl
    _ ≤ ∑ n ∈ R, g n := by
      apply Finset.sum_le_sum
      intro n hn
      have hn' := Finset.mem_filter.1 hn
      exact amusical_odd_reciprocal_error
        (lt_of_lt_of_le (by norm_num) (Finset.mem_Icc.1 hn'.1).1) hn'.2.2
    _ ≤ ∑ n ∈ T, g n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hRT
      intro n hnT hnR
      simp only [T, Finset.mem_insert, Finset.mem_Icc] at hnT
      rcases hnT with rfl | hnT
      · simp [g]
      · simp only [g, if_neg (by omega : n ≠ 1)]
        have hle : (1 : ℝ) / n ≤ 1 / (n - 1) :=
          one_div_le_one_div_of_le (by exact_mod_cast (show 0 < n - 1 by omega))
            (by norm_num)
        positivity
    _ = 1 / 3 + ∑ n ∈ Finset.Icc (3 : ℤ) N,
        (1 / 2 : ℝ) * (1 / (n - 1) - 1 / n) := by
      rw [show T = insert (1 : ℤ) (Finset.Icc (3 : ℤ) N) by rfl,
        Finset.sum_insert (by simp)]
      simp only [g, if_pos]
      congr 1
      apply Finset.sum_congr rfl
      intro n hn
      simp only [Finset.mem_Icc] at hn
      rw [if_neg (by omega)]
    _ ≤ 1 / 3 + 1 / 4 := by linarith [sum_half_reciprocal_telescope_Icc N hN]
    _ ≤ 2 / 3 := by norm_num

open Classical in
theorem sum_nonmultiples_three_transport {S : Set ℤ}
    (hS : ∀ x, amusical x ∈ S ↔ x ∈ S) (N : ℕ) :
    ∑ m ∈ (Finset.Icc (1 : ℤ) N).filter
        (fun m ↦ m ∈ S ∧ ¬ 3 ∣ m ∧ amusicalInv m ≤ N), (1 : ℝ) / m =
      ∑ n ∈ (Finset.Icc (1 : ℤ) N).filter
        (fun n ↦ n ∈ S ∧ ¬ 2 ∣ n), (1 : ℝ) / amusical n := by
  apply Finset.sum_bij (fun m _ ↦ amusicalInv m)
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
    rcases hm with ⟨⟨hm1, hmN⟩, hmS, hm3, hminv⟩
    have hmpos : 0 < m := lt_of_lt_of_le (by norm_num) hm1
    refine ⟨⟨by exact_mod_cast (amusicalInv_pos_of_pos hmpos), hminv⟩, ?_,
      amusicalInv_odd_of_not_three hm3⟩
    exact (hS _).1 (by simpa [amusical_amusicalInv] using hmS)
  · intro a ha b hb hab
    simpa [amusical_amusicalInv] using congrArg amusical hab
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    rcases hn with ⟨⟨hn1, hnN⟩, hnS, hn2⟩
    have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn1
    refine ⟨amusical n, ?_, amusicalInv_amusical n⟩
    simp only [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨amusical_odd_pos hnpos hn2, (amusical_odd_le hnpos hn2).trans hnN⟩,
      (hS _).2 hnS, amusical_odd_not_three hn2, ?_⟩
    simpa [amusicalInv_amusical] using hnN
  · intro m hm
    rw [amusical_amusicalInv]

end CollatzMoonshot.Amusical

namespace CollatzMoonshot.Amusical

open Classical in
theorem sum_multiples_three_transport_cutoff {S : Set ℤ}
    (hS : ∀ x, amusical x ∈ S ↔ x ∈ S) (N : ℕ) :
    ∑ m ∈ (Finset.Icc (1 : ℤ) N).filter
        (fun m ↦ m ∈ S ∧ 3 ∣ m), (1 : ℝ) / m =
      (2 / 3 : ℝ) * ∑ n ∈ (Finset.Icc (1 : ℤ)
        ((2 * (N / 3) : ℕ) : ℤ)).filter
        (fun n ↦ n ∈ S ∧ 2 ∣ n), (1 : ℝ) / n := by
  classical
  symm
  rw [Finset.mul_sum]
  apply Finset.sum_bij (fun n _ ↦ amusical n)
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    rcases hn with ⟨⟨hn1, hnN⟩, hnS, hn2⟩
    obtain ⟨k, rfl⟩ := hn2
    rw [amusical_two_mul]
    constructor
    · constructor <;> omega
    · exact ⟨by simpa [amusical_two_mul] using (hS _).2 hnS, dvd_mul_right 3 k⟩
  · intro a ha b hb hab
    exact amusical_injective hab
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
    rcases hm with ⟨⟨hm1, hmN⟩, hmS, hm3⟩
    obtain ⟨k, rfl⟩ := hm3
    refine ⟨2 * k, ?_, amusical_two_mul k⟩
    · constructor
      · constructor <;> omega
      · exact ⟨(hS _).1 (by simpa [amusical_two_mul] using hmS), dvd_mul_right 2 k⟩
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    rcases hn with ⟨⟨hn1, hnN⟩, hnS, hn2⟩
    obtain ⟨k, rfl⟩ := hn2
    rw [amusical_two_mul]
    norm_num
    field_simp

open Classical in
theorem even_cutoff_tail_le (P : ℤ → Prop) [DecidablePred P] (N : ℕ) (hN : 9 ≤ N) :
    ∑ n ∈ (Finset.Icc ((2 * (N / 3) + 1 : ℕ) : ℤ) N).filter P,
        (1 : ℝ) / n ≤
      3 / 4 := by
  have hbase := reciprocal_sum_filter_Icc_le P
    (a := (2 * (N / 3) + 1 : ℕ)) (b := (N : ℤ)) (by positivity) (by omega)
  calc
    ∑ n ∈ (Finset.Icc ((2 * (N / 3) + 1 : ℕ) : ℤ) N).filter P,
        (1 : ℝ) / n ≤
        (((N : ℤ) + 1 - (2 * (N / 3) + 1 : ℕ) : ℤ) : ℝ) /
          ((2 * (N / 3) + 1 : ℕ) : ℤ) := hbase
    _ ≤ 3 / 4 := by
      norm_num only [Int.cast_sub, Int.cast_add, Int.cast_ofNat, Nat.cast_ofNat,
        Int.cast_natCast, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
      apply (div_le_iff₀ (by positivity)).2
      have hnat : 4 * (N - 2 * (N / 3)) ≤ 3 * (2 * (N / 3) + 1) := by omega
      have hsub : 2 * (N / 3) ≤ N := by omega
      have hreal : (4 : ℝ) * ((N - 2 * (N / 3) : ℕ) : ℝ) ≤
          3 * ((2 * (N / 3) + 1 : ℕ) : ℝ) := by exact_mod_cast hnat
      rw [Nat.cast_sub hsub] at hreal
      push_cast at hreal
      simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] at ⊢
      change (N : ℝ) + 1 - (2 * ((N / 3 : ℕ) : ℝ) + 1) ≤
        (3 / 4) * (2 * ((N / 3 : ℕ) : ℝ) + 1)
      nlinarith

open Classical in
theorem odd_cutoff_tail_le (P : ℤ → Prop) [DecidablePred P] (N : ℕ) (hN : 9 ≤ N) :
    ∑ n ∈ (Finset.Icc ((2 * N / 3 + 1 : ℕ) : ℤ) N).filter P,
        (1 : ℝ) / n ≤
      2 / 3 := by
  have hbase := reciprocal_sum_filter_Icc_le P
    (a := (2 * N / 3 + 1 : ℕ)) (b := (N : ℤ)) (by positivity) (by omega)
  calc
    ∑ n ∈ (Finset.Icc ((2 * N / 3 + 1 : ℕ) : ℤ) N).filter P,
        (1 : ℝ) / n ≤
        (((N : ℤ) + 1 - (2 * N / 3 + 1 : ℕ) : ℤ) : ℝ) /
          ((2 * N / 3 + 1 : ℕ) : ℤ) := hbase
    _ ≤ 2 / 3 := by
      norm_num only [Int.cast_sub, Int.cast_add, Int.cast_ofNat, Nat.cast_ofNat,
        Int.cast_natCast, Nat.cast_add, Nat.cast_mul, Nat.cast_div, Nat.cast_one]
      apply (div_le_iff₀ (by positivity)).2
      have hnat : 3 * (N - 2 * N / 3) ≤ 2 * (2 * N / 3 + 1) := by omega
      have hsub : 2 * N / 3 ≤ N := by omega
      have hreal : (3 : ℝ) * ((N - 2 * N / 3 : ℕ) : ℝ) ≤
          2 * ((2 * N / 3 + 1 : ℕ) : ℝ) := by exact_mod_cast hnat
      rw [Nat.cast_sub hsub] at hreal
      push_cast at hreal ⊢
      nlinarith

open Classical in
theorem reciprocal_sum_partition (S : Set ℤ) (d : ℤ) (N : ℕ) :
    ∑ n ∈ (Finset.Icc (1 : ℤ) N).filter (fun n ↦ n ∈ S), (1 : ℝ) / n =
      ∑ n ∈ (Finset.Icc (1 : ℤ) N).filter (fun n ↦ n ∈ S ∧ d ∣ n),
          (1 : ℝ) / n +
        ∑ n ∈ (Finset.Icc (1 : ℤ) N).filter (fun n ↦ n ∈ S ∧ ¬ d ∣ n),
          (1 : ℝ) / n := by
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hnS : n ∈ S <;> by_cases hnd : d ∣ n <;> simp [hnS, hnd]

open Classical in
theorem positive_reciprocal_sum_nonneg (P : ℤ → Prop) [DecidablePred P] (N : ℕ) :
    0 ≤ ∑ n ∈ (Finset.Icc (1 : ℤ) N).filter P, (1 : ℝ) / n := by
  apply Finset.sum_nonneg
  intro n hn
  have hn1 := (Finset.mem_Icc.1 (Finset.mem_filter.1 hn).1).1
  exact one_div_nonneg.mpr (by exact_mod_cast (show 0 ≤ n by omega))

open Classical in
theorem small_reciprocal_sum_le_three (S : Set ℤ) (N : ℕ) (hN : N < 9) :
    ∑ n ∈ (Finset.Icc (1 : ℤ) N).filter (fun n ↦ n ∈ S), (1 : ℝ) / n ≤ 3 := by
  calc
    ∑ n ∈ (Finset.Icc (1 : ℤ) N).filter (fun n ↦ n ∈ S), (1 : ℝ) / n ≤
        ∑ n ∈ Finset.Icc (1 : ℤ) 8, (1 : ℝ) / n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
        omega
      · intro n hn hnS
        have hn1 := (Finset.mem_Icc.1 hn).1
        exact one_div_nonneg.mpr (by exact_mod_cast (show 0 ≤ n by omega))
    _ = ∑ i ∈ Finset.range 8, (1 : ℝ) / (i + 1) := by
      symm
      apply Finset.sum_bij (fun i _ ↦ ((i + 1 : ℕ) : ℤ))
      · intro i hi
        simp only [Finset.mem_range] at hi
        simp only [Finset.mem_Icc]
        constructor <;> omega
      · intro i hi j hj hij
        have : i + 1 = j + 1 := by exact_mod_cast hij
        omega
      · intro n hn
        simp only [Finset.mem_Icc] at hn
        refine ⟨n.toNat - 1, by simp only [Finset.mem_range]; omega, ?_⟩
        omega
      · intro i hi
        norm_num
    _ ≤ 3 := by norm_num [Finset.sum_range_succ]

open Classical in
theorem multiples_three_even_approx {S : Set ℤ}
    (hS : ∀ x, amusical x ∈ S ↔ x ∈ S) (N : ℕ) (hN : 9 ≤ N) :
    |∑ m ∈ (Finset.Icc (1 : ℤ) N).filter (fun m ↦ m ∈ S ∧ 3 ∣ m),
          (1 : ℝ) / m -
        (2 / 3 : ℝ) * ∑ n ∈ (Finset.Icc (1 : ℤ) N).filter
          (fun n ↦ n ∈ S ∧ 2 ∣ n), (1 : ℝ) / n| ≤ 1 / 2 := by
  let E₀ := (Finset.Icc (1 : ℤ) ((2 * (N / 3) : ℕ) : ℤ)).filter
    (fun n ↦ n ∈ S ∧ 2 ∣ n)
  let E := (Finset.Icc (1 : ℤ) N).filter (fun n ↦ n ∈ S ∧ 2 ∣ n)
  let A := (Finset.Icc (1 : ℤ) N).filter (fun n ↦ n ∈ S ∧ 3 ∣ n)
  have hE₀E : E₀ ⊆ E := by
    intro n hn
    simp only [E₀, E, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    rcases hn with ⟨⟨hn1, hncut⟩, hnS, hn2⟩
    refine ⟨⟨hn1, hncut.trans ?_⟩, hnS, hn2⟩
    exact_mod_cast (show 2 * (N / 3) ≤ N by omega)
  have hsplit :
      ∑ n ∈ E \ E₀, (1 : ℝ) / n + ∑ n ∈ E₀, (1 : ℝ) / n =
        ∑ n ∈ E, (1 : ℝ) / n := Finset.sum_sdiff hE₀E
  have htail_subset :
      E \ E₀ ⊆ (Finset.Icc ((2 * (N / 3) + 1 : ℕ) : ℤ) N).filter
        (fun n ↦ n ∈ S ∧ 2 ∣ n) := by
    intro n hn
    simp only [Finset.mem_sdiff, E, E₀, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    rcases hn with ⟨⟨⟨hn1, hnN⟩, hnS, hn2⟩, hnE₀⟩
    refine ⟨⟨?_, hnN⟩, hnS, hn2⟩
    by_contra hnlow
    apply hnE₀
    constructor
    · exact ⟨hn1, by omega⟩
    · exact ⟨hnS, hn2⟩
  have htail_nonneg : 0 ≤ ∑ n ∈ E \ E₀, (1 : ℝ) / n := by
    apply Finset.sum_nonneg
    intro n hn
    have hn1 := (Finset.mem_Icc.1 (Finset.mem_filter.1
      (Finset.mem_sdiff.1 hn).1).1).1
    exact one_div_nonneg.mpr (by exact_mod_cast (show 0 ≤ n by omega))
  have htail : ∑ n ∈ E \ E₀, (1 : ℝ) / n ≤ 3 / 4 := by
    calc
      ∑ n ∈ E \ E₀, (1 : ℝ) / n ≤
          ∑ n ∈ (Finset.Icc ((2 * (N / 3) + 1 : ℕ) : ℤ) N).filter
            (fun n ↦ n ∈ S ∧ 2 ∣ n), (1 : ℝ) / n := by
        apply Finset.sum_le_sum_of_subset_of_nonneg htail_subset
        intro n hn hnE
        have hn1 := (Finset.mem_Icc.1 (Finset.mem_filter.1 hn).1).1
        exact one_div_nonneg.mpr (by exact_mod_cast (show 0 ≤ n by omega))
      _ ≤ 3 / 4 := even_cutoff_tail_le _ N hN
  have htrans : ∑ n ∈ A, (1 : ℝ) / n =
      (2 / 3 : ℝ) * ∑ n ∈ E₀, (1 : ℝ) / n := by
    simpa only [A, E₀] using sum_multiples_three_transport_cutoff hS N
  change |∑ n ∈ A, (1 : ℝ) / n -
    (2 / 3 : ℝ) * ∑ n ∈ E, (1 : ℝ) / n| ≤ 1 / 2
  rw [abs_le]
  constructor <;> nlinarith

open Classical in
theorem nonmultiples_three_odd_approx {S : Set ℤ}
    (hS : ∀ x, amusical x ∈ S ↔ x ∈ S) (N : ℕ) (hN : 9 ≤ N) :
    |∑ m ∈ (Finset.Icc (1 : ℤ) N).filter (fun m ↦ m ∈ S ∧ ¬ 3 ∣ m),
          (1 : ℝ) / m -
        (4 / 3 : ℝ) * ∑ n ∈ (Finset.Icc (1 : ℤ) N).filter
          (fun n ↦ n ∈ S ∧ ¬ 2 ∣ n), (1 : ℝ) / n| ≤ 4 / 3 := by
  let B₀ := (Finset.Icc (1 : ℤ) N).filter
    (fun m ↦ m ∈ S ∧ ¬ 3 ∣ m ∧ amusicalInv m ≤ N)
  let B := (Finset.Icc (1 : ℤ) N).filter (fun m ↦ m ∈ S ∧ ¬ 3 ∣ m)
  let O := (Finset.Icc (1 : ℤ) N).filter (fun n ↦ n ∈ S ∧ ¬ 2 ∣ n)
  have hB₀B : B₀ ⊆ B := by
    intro m hm
    simp only [B₀, B, Finset.mem_filter, Finset.mem_Icc] at hm ⊢
    exact ⟨hm.1, hm.2.1, hm.2.2.1⟩
  have hsplit :
      ∑ m ∈ B \ B₀, (1 : ℝ) / m + ∑ m ∈ B₀, (1 : ℝ) / m =
        ∑ m ∈ B, (1 : ℝ) / m := Finset.sum_sdiff hB₀B
  have hextra_subset :
      B \ B₀ ⊆ (Finset.Icc ((2 * N / 3 + 1 : ℕ) : ℤ) N).filter
        (fun m ↦ m ∈ S ∧ ¬ 3 ∣ m) := by
    intro m hm
    simp only [Finset.mem_sdiff, B, B₀, Finset.mem_filter, Finset.mem_Icc] at hm ⊢
    rcases hm with ⟨⟨⟨hm1, hmN⟩, hmS, hm3⟩, hmB₀⟩
    have hmpos : 0 < m := lt_of_lt_of_le (by norm_num) hm1
    have hminv : ¬ amusicalInv m ≤ (N : ℤ) := by
      intro hle
      exact hmB₀ ⟨⟨hm1, hmN⟩, hmS, hm3, hle⟩
    have hbound := two_mul_amusicalInv_le_three_mul hmpos hm3
    refine ⟨⟨?_, hmN⟩, hmS, hm3⟩
    omega
  have hextra_nonneg : 0 ≤ ∑ m ∈ B \ B₀, (1 : ℝ) / m := by
    apply Finset.sum_nonneg
    intro m hm
    have hm1 := (Finset.mem_Icc.1 (Finset.mem_filter.1
      (Finset.mem_sdiff.1 hm).1).1).1
    exact one_div_nonneg.mpr (by exact_mod_cast (show 0 ≤ m by omega))
  have hextra : ∑ m ∈ B \ B₀, (1 : ℝ) / m ≤ 2 / 3 := by
    calc
      ∑ m ∈ B \ B₀, (1 : ℝ) / m ≤
          ∑ m ∈ (Finset.Icc ((2 * N / 3 + 1 : ℕ) : ℤ) N).filter
            (fun m ↦ m ∈ S ∧ ¬ 3 ∣ m), (1 : ℝ) / m := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hextra_subset
        intro m hm hmB
        have hm1 := (Finset.mem_Icc.1 (Finset.mem_filter.1 hm).1).1
        exact one_div_nonneg.mpr (by exact_mod_cast (show 0 ≤ m by omega))
      _ ≤ 2 / 3 := odd_cutoff_tail_le _ N hN
  have htrans : ∑ m ∈ B₀, (1 : ℝ) / m =
      ∑ n ∈ O, (1 : ℝ) / amusical n := by
    simpa only [B₀, O] using sum_nonmultiples_three_transport hS N
  have hscaled : (4 / 3 : ℝ) * ∑ n ∈ O, (1 : ℝ) / n =
      ∑ n ∈ O, (4 : ℝ) / (3 * n) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hn1 := (Finset.mem_Icc.1 (Finset.mem_filter.1 hn).1).1
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp [hn0]
  have herr : |∑ m ∈ B₀, (1 : ℝ) / m -
      (4 / 3 : ℝ) * ∑ n ∈ O, (1 : ℝ) / n| ≤ 2 / 3 := by
    rw [htrans, hscaled, ← Finset.sum_sub_distrib]
    calc
      |∑ n ∈ O, ((1 : ℝ) / amusical n - 4 / (3 * n))| ≤
          ∑ n ∈ O, |(1 : ℝ) / amusical n - 4 / (3 * n)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ 2 / 3 := by simpa only [O] using sum_amusical_odd_reciprocal_error S N (by omega)
  change |∑ m ∈ B, (1 : ℝ) / m -
    (4 / 3 : ℝ) * ∑ n ∈ O, (1 : ℝ) / n| ≤ 4 / 3
  rw [abs_le] at herr ⊢
  constructor <;> nlinarith

open Classical in
theorem reciprocal_sum_even_balance {S : Set ℤ}
    (hS : ∀ x, amusical x ∈ S ↔ x ∈ S) (N : ℕ) :
    |∑ n ∈ (Finset.Icc (1 : ℤ) N).filter (fun n ↦ n ∈ S ∧ 2 ∣ n),
          (1 : ℝ) / n -
        (∑ n ∈ (Finset.Icc (1 : ℤ) N).filter (fun n ↦ n ∈ S),
          (1 : ℝ) / n) / 2| ≤ 3 := by
  let W := (Finset.Icc (1 : ℤ) N).filter (fun n ↦ n ∈ S)
  let E := (Finset.Icc (1 : ℤ) N).filter (fun n ↦ n ∈ S ∧ 2 ∣ n)
  let O := (Finset.Icc (1 : ℤ) N).filter (fun n ↦ n ∈ S ∧ ¬ 2 ∣ n)
  let A := (Finset.Icc (1 : ℤ) N).filter (fun n ↦ n ∈ S ∧ 3 ∣ n)
  let B := (Finset.Icc (1 : ℤ) N).filter (fun n ↦ n ∈ S ∧ ¬ 3 ∣ n)
  have hpart₂ : ∑ n ∈ W, (1 : ℝ) / n =
      ∑ n ∈ E, (1 : ℝ) / n + ∑ n ∈ O, (1 : ℝ) / n := by
    simpa only [W, E, O] using reciprocal_sum_partition S 2 N
  change |∑ n ∈ E, (1 : ℝ) / n -
    (∑ n ∈ W, (1 : ℝ) / n) / 2| ≤ 3
  by_cases hsmall : N < 9
  · have hE₀ : 0 ≤ ∑ n ∈ E, (1 : ℝ) / n := by
      simpa only [E] using positive_reciprocal_sum_nonneg (fun n ↦ n ∈ S ∧ 2 ∣ n) N
    have hO₀ : 0 ≤ ∑ n ∈ O, (1 : ℝ) / n := by
      simpa only [O] using positive_reciprocal_sum_nonneg (fun n ↦ n ∈ S ∧ ¬ 2 ∣ n) N
    have hW : ∑ n ∈ W, (1 : ℝ) / n ≤ 3 := by
      simpa only [W] using small_reciprocal_sum_le_three S N hsmall
    rw [abs_le]
    constructor <;> nlinarith
  · have hN : 9 ≤ N := by omega
    have hpart₃ : ∑ n ∈ W, (1 : ℝ) / n =
        ∑ n ∈ A, (1 : ℝ) / n + ∑ n ∈ B, (1 : ℝ) / n := by
      simpa only [W, A, B] using reciprocal_sum_partition S 3 N
    have hA : |∑ n ∈ A, (1 : ℝ) / n -
        (2 / 3 : ℝ) * ∑ n ∈ E, (1 : ℝ) / n| ≤ 1 / 2 := by
      simpa only [A, E] using multiples_three_even_approx hS N hN
    have hB : |∑ n ∈ B, (1 : ℝ) / n -
        (4 / 3 : ℝ) * ∑ n ∈ O, (1 : ℝ) / n| ≤ 4 / 3 := by
      simpa only [B, O] using nonmultiples_three_odd_approx hS N hN
    rw [abs_le] at hA hB ⊢
    constructor <;> nlinarith

open Classical in
theorem reciprocal_sum_three_balance {S : Set ℤ}
    (hS : ∀ x, amusical x ∈ S ↔ x ∈ S) (N : ℕ) :
    |∑ n ∈ (Finset.Icc (1 : ℤ) N).filter (fun n ↦ n ∈ S ∧ 3 ∣ n),
          (1 : ℝ) / n -
        (∑ n ∈ (Finset.Icc (1 : ℤ) N).filter (fun n ↦ n ∈ S),
          (1 : ℝ) / n) / 3| ≤ 3 := by
  let W := (Finset.Icc (1 : ℤ) N).filter (fun n ↦ n ∈ S)
  let E := (Finset.Icc (1 : ℤ) N).filter (fun n ↦ n ∈ S ∧ 2 ∣ n)
  let A := (Finset.Icc (1 : ℤ) N).filter (fun n ↦ n ∈ S ∧ 3 ∣ n)
  let B := (Finset.Icc (1 : ℤ) N).filter (fun n ↦ n ∈ S ∧ ¬ 3 ∣ n)
  change |∑ n ∈ A, (1 : ℝ) / n -
    (∑ n ∈ W, (1 : ℝ) / n) / 3| ≤ 3
  by_cases hsmall : N < 9
  · have hpart₃ : ∑ n ∈ W, (1 : ℝ) / n =
        ∑ n ∈ A, (1 : ℝ) / n + ∑ n ∈ B, (1 : ℝ) / n := by
      simpa only [W, A, B] using reciprocal_sum_partition S 3 N
    have hA₀ : 0 ≤ ∑ n ∈ A, (1 : ℝ) / n := by
      simpa only [A] using positive_reciprocal_sum_nonneg (fun n ↦ n ∈ S ∧ 3 ∣ n) N
    have hB₀ : 0 ≤ ∑ n ∈ B, (1 : ℝ) / n := by
      simpa only [B] using positive_reciprocal_sum_nonneg (fun n ↦ n ∈ S ∧ ¬ 3 ∣ n) N
    have hW : ∑ n ∈ W, (1 : ℝ) / n ≤ 3 := by
      simpa only [W] using small_reciprocal_sum_le_three S N hsmall
    rw [abs_le]
    constructor <;> nlinarith
  · have hN : 9 ≤ N := by omega
    have hE : |∑ n ∈ E, (1 : ℝ) / n -
        (∑ n ∈ W, (1 : ℝ) / n) / 2| ≤ 3 := by
      simpa only [E, W] using reciprocal_sum_even_balance hS N
    have hA : |∑ n ∈ A, (1 : ℝ) / n -
        (2 / 3 : ℝ) * ∑ n ∈ E, (1 : ℝ) / n| ≤ 1 / 2 := by
      simpa only [A, E] using multiples_three_even_approx hS N hN
    rw [abs_le] at hE hA ⊢
    constructor <;> nlinarith

end CollatzMoonshot.Amusical
