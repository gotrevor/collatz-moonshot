/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalSeventh.Sparse

/-!
# Assembling the sparse sweep

The deterministic half of `sparse_sweep`: every visit of an infinite orbit below `X` within
time `T` is either an exceptional center (a strict descent at some time `K < i ≤ L`) or lies
within `K` steps of an `(L-K)`-window minimum, and those minima are packed apart along the
orbit.
-/

namespace CollatzMoonshot.Amusical

open CollatzMoonshot.Obstructions.Amusical

/-- Every power of `U` preserves the nonnegative integers. -/
theorem amusicalPerm_zpow_nonneg {z : ℤ} (hz : 0 ≤ z) (t : ℤ) :
    0 ≤ (amusicalPerm ^ t) z := by
  have hf : ∀ k : ℕ, 0 ≤ amusical^[k] z := by
    intro k
    induction k with
    | zero => simpa using hz
    | succ k ih => rw [Function.iterate_succ_apply']; exact amusical_nonneg ih
  have hb : ∀ k : ℕ, 0 ≤ amusicalInv^[k] z := by
    intro k
    induction k with
    | zero => simpa using hz
    | succ k ih => rw [Function.iterate_succ_apply']; exact amusicalInv_nonneg ih
  rcases Int.eq_nat_or_neg t with ⟨k, rfl | rfl⟩
  · rw [← amusical_iterate_eq_perm_pow]; exact hf k
  · rw [← amusicalInv_iterate_eq_perm_pow]; exact hb k

/-- **Deterministic sweep count.**  The visits of an infinite orbit below `X` at times
`|j| ≤ T`, weighted by the packing length `L-K+1`, are bounded by the exceptional descent
centers plus `(2K+1)` copies of the packing bound for `(L-K)`-window minima. -/
theorem sweep_card_mul_le (K L T X : ℕ) (hKL : K ≤ L) (x : ℤ)
    (hinf : (amusicalOrbit x).Infinite) :
    (L - K + 1) * ((Finset.Icc (-(T : ℤ)) T).filter
        fun j => 0 ≤ (amusicalPerm ^ j) x ∧ (amusicalPerm ^ j) x < X).card ≤
      (L - K + 1) * Nat.count (fun n : ℕ => ∃ i : ↥(Finset.Icc (K + 1) L),
        (amusical^[i] (n : ℤ) < n ∨ amusicalInv^[i] (n : ℤ) < n)) X +
      (2 * K + 1) * (2 * (T + L) + 1) := by
  classical
  set F := (Finset.Icc (-(T : ℤ)) T).filter
    fun j => 0 ≤ (amusicalPerm ^ j) x ∧ (amusicalPerm ^ j) x < X with hF
  set E : ℕ → Prop := fun n : ℕ => ∃ i : ↥(Finset.Icc (K + 1) L),
    (amusical^[i] (n : ℤ) < n ∨ amusicalInv^[i] (n : ℤ) < n) with hE
  have hinj := perm_zpow_apply_injective_of_infinite amusicalPerm hinf
  have hmemF : ∀ j ∈ F, |j| ≤ (T : ℤ) ∧ 0 ≤ (amusicalPerm ^ j) x ∧
      (amusicalPerm ^ j) x < X := by
    intro j hj
    rw [hF, Finset.mem_filter, Finset.mem_Icc] at hj
    exact ⟨abs_le.mpr hj.1, hj.2⟩
  -- exceptional visits
  set H := F.filter fun j => E ((amusicalPerm ^ j) x).toNat with hH
  set G := F.filter fun j => ¬ E ((amusicalPerm ^ j) x).toNat with hG
  have hsplit : H.card + G.card = F.card := by
    rw [hH, hG]; exact Finset.card_filter_add_card_filter_not _
  have hHcard : H.card ≤ Nat.count E X := by
    rw [Nat.count_eq_card_filter_range]
    apply Finset.card_le_card_of_injOn (fun j => ((amusicalPerm ^ j) x).toNat)
    · intro j hj
      have hj' := Finset.mem_filter.mp hj
      obtain ⟨-, h0, hX⟩ := hmemF j hj'.1
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hj'.2⟩
      show ((amusicalPerm ^ j) x).toNat < X
      omega
    · intro a ha b hb hab
      have ha' := hmemF a (Finset.mem_filter.mp ha).1
      have hb' := hmemF b (Finset.mem_filter.mp hb).1
      apply hinj
      dsimp only at hab ⊢
      omega
  -- nonexceptional visits sit near packed window minima
  choose tm htm hmin using fun n : ℤ => exists_centered_window_minimizer L n
  set M := (Finset.range X).filter fun m : ℕ => IsWindowMin (L - K) (m : ℤ) ∧
    ∃ j : ℤ, (amusicalPerm ^ j) x = m ∧ |j| ≤ ((T + K : ℕ) : ℤ) with hM
  have hnear : ∀ j ∈ G, |tm ((amusicalPerm ^ j) x)| ≤ K := by
    intro j hj
    have hj' := Finset.mem_filter.mp hj
    obtain ⟨-, h0, -⟩ := hmemF j hj'.1
    set n := (amusicalPerm ^ j) x with hn
    by_contra hout
    push Not at hout
    have hinfn : (amusicalOrbit n).Infinite := by
      rwa [amusicalOrbit_eq_of_mem ⟨j, rfl⟩]
    apply hj'.2
    have hcast : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg h0
    rcases centered_minimizer_outside_implies_descent hinfn (htm n) hout (hmin n) with
      ⟨i, hKi, hiL, hi⟩ | ⟨i, hKi, hiL, hi⟩
    · exact ⟨⟨i, Finset.mem_Icc.mpr ⟨hKi, hiL⟩⟩, Or.inl (by rw [hcast]; exact hi)⟩
    · exact ⟨⟨i, Finset.mem_Icc.mpr ⟨hKi, hiL⟩⟩, Or.inr (by rw [hcast]; exact hi)⟩
  have hGcard : G.card ≤ M.card * (2 * K + 1) := by
    have hprod : (M ×ˢ Finset.Icc (-(K : ℤ)) K).card = M.card * (2 * K + 1) := by
      rw [Finset.card_product, Int.card_Icc]
      congr 1
      omega
    rw [← hprod]
    apply Finset.card_le_card_of_injOn (fun j =>
      (((amusicalPerm ^ (tm ((amusicalPerm ^ j) x) + j)) x).toNat, tm ((amusicalPerm ^ j) x)))
    · intro j hj
      have hj' := Finset.mem_filter.mp hj
      obtain ⟨hjT, h0, hX⟩ := hmemF j hj'.1
      have ht := hnear j hj
      set n := (amusicalPerm ^ j) x with hn
      set t := tm n with ht_def
      have hval : (amusicalPerm ^ (t + j)) x = (amusicalPerm ^ t) n := by
        rw [zpow_add, Equiv.Perm.mul_apply]
      have hle : (amusicalPerm ^ t) n ≤ n := by simpa using hmin n 0 (by simp)
      have hnn : 0 ≤ (amusicalPerm ^ t) n := amusicalPerm_zpow_nonneg h0 t
      have hwin : IsWindowMin (L - K) ((amusicalPerm ^ t) n) :=
        isWindowMin_sub_of_centered_minimizer hKL ht (hmin n)
      have hcast : ((((amusicalPerm ^ t) n).toNat : ℕ) : ℤ) = (amusicalPerm ^ t) n :=
        Int.toNat_of_nonneg hnn
      refine Finset.mem_product.mpr ⟨?_, ?_⟩
      · dsimp only
        rw [hval]
        refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_, t + j, ?_, ?_⟩
        · rw [hcast]; exact hwin
        · rw [hcast, hval]
        · have h1 := abs_add_le t j
          push_cast
          omega
      · dsimp only
        exact Finset.mem_Icc.mpr (abs_le.mp ht)
    · intro a ha b hb hab
      have ha' := hmemF a (Finset.mem_filter.mp ha).1
      have hb' := hmemF b (Finset.mem_filter.mp hb).1
      simp only [Prod.mk.injEq] at hab
      obtain ⟨hv, htt⟩ := hab
      have hna := amusicalPerm_zpow_nonneg ha'.2.1 (tm ((amusicalPerm ^ a) x))
      have hnb := amusicalPerm_zpow_nonneg hb'.2.1 (tm ((amusicalPerm ^ b) x))
      rw [← Equiv.Perm.mul_apply, ← zpow_add] at hna hnb
      have hv' : (amusicalPerm ^ (tm ((amusicalPerm ^ a) x) + a)) x =
          (amusicalPerm ^ (tm ((amusicalPerm ^ b) x) + b)) x := by omega
      have := hinj hv'
      omega
  have hMcard : M.card * (L - K + 1) ≤ 2 * (T + K + (L - K)) + 1 := by
    apply windowMin_card_mul_le M
    · intro n hn
      exact (Finset.mem_filter.mp hn).2.1
    · intro n hn
      exact (Finset.mem_filter.mp hn).2.2
  have hTL : T + K + (L - K) = T + L := by omega
  rw [hTL] at hMcard
  calc
    (L - K + 1) * F.card = (L - K + 1) * H.card + (L - K + 1) * G.card := by
      rw [← hsplit, Nat.mul_add]
    _ ≤ (L - K + 1) * Nat.count E X + (L - K + 1) * (M.card * (2 * K + 1)) := by
      gcongr
    _ = (L - K + 1) * Nat.count E X + (2 * K + 1) * (M.card * (L - K + 1)) := by ring
    _ ≤ (L - K + 1) * Nat.count E X + (2 * K + 1) * (2 * (T + L) + 1) := by gcongr

/-- The exceptional-center bound of `count_descent_between_geometric_le` is at most `ηX/2`
once `K` is fixed by `η` and `324^(3L) ≤ X` with `L ≥ 24/η`. -/
theorem sweep_exceptional_le_half {η : ℝ} (hη : 0 < η) {K L X : ℕ}
    (hK : ((99 : ℝ) / 100) ^ K < η / 800) (hcubeN : (324 ^ L) ^ 3 ≤ X)
    (hceil : 24 / η ≤ (L : ℝ)) :
    200 * ((99 : ℝ) / 100) ^ (K + 1) * X + 6 * (L + 1) * 324 ^ L ≤ η * X / 2 := by
  have hX0 : (0 : ℝ) ≤ X := by positivity
  have ha : 200 * ((99 : ℝ) / 100) ^ (K + 1) * X ≤ η * X / 4 := by
    have h1 : ((99 : ℝ) / 100) ^ (K + 1) ≤ ((99 : ℝ) / 100) ^ K :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ K)
    have h2 : 200 * ((99 : ℝ) / 100) ^ (K + 1) ≤ η / 4 := by linarith
    have h3 := mul_le_mul_of_nonneg_right h2 hX0
    linarith
  set a : ℝ := (324 : ℝ) ^ L with ha_def
  have hcube : a ^ 3 ≤ X := by
    rw [ha_def]
    exact_mod_cast hcubeN
  have hLaN : L + 1 ≤ 324 ^ L := Nat.lt_pow_self (by norm_num)
  have hLa : (L : ℝ) + 1 ≤ a := by
    rw [ha_def]
    exact_mod_cast hLaN
  have h24' : 24 ≤ η * a := by
    rw [div_le_iff₀ hη] at hceil
    nlinarith
  have ha0 : 0 ≤ a := by positivity
  have hb1 := mul_le_mul_of_nonneg_left hLa (show (0 : ℝ) ≤ 6 * a by positivity)
  have hb2 := mul_le_mul_of_nonneg_left hcube hη.le
  have hb3 := mul_le_mul_of_nonneg_right h24' (sq_nonneg a)
  have hb : 6 * ((L : ℝ) + 1) * a ≤ η * X / 4 := by nlinarith
  linarith

/-- The packing term is at most `(L-K+1) ηX/2` once `c = η / (48 (2K+1) log 324)`, the time
horizon is `T ≤ cX log X`, `log X ≤ (3L+3) log 324`, `L ≥ 2K`, and `X ≥ 16(2K+1)/η`. -/
theorem sweep_packing_le_half {η c : ℝ} (hη : 0 < η) {K L T X : ℕ}
    (hc : c * Real.log 324 * (48 * (2 * K + 1)) = η) (hc0 : 0 ≤ c)
    (hTle : (T : ℝ) ≤ c * X * Real.log X)
    (hlog : Real.log X ≤ (3 * L + 3) * Real.log 324)
    (h2K : 2 * K ≤ L) (hXbig : 16 * (2 * K + 1) / η ≤ (X : ℝ)) :
    (2 * K + 1) * (2 * ((T : ℝ) + L) + 1) ≤ ((L : ℝ) - K + 1) * (η * X / 2) := by
  have hX0 : (0 : ℝ) ≤ X := by positivity
  have hTbound : (2 * K + 1) * (2 * (T : ℝ)) ≤ ((L : ℝ) + 1) * (η * X / 8) := by
    have h1 : (T : ℝ) ≤ c * X * ((3 * L + 3) * Real.log 324) :=
      le_trans hTle (mul_le_mul_of_nonneg_left hlog (by positivity))
    have h2 := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 2 * (2 * K + 1) by positivity)
    have h3 : 2 * (2 * K + 1) * (c * X * ((3 * L + 3) * Real.log 324)) =
        ((L : ℝ) + 1) * X * (c * Real.log 324 * (48 * (2 * K + 1))) / 8 := by ring
    rw [hc] at h3
    have h4 : (2 * K + 1) * (2 * (T : ℝ)) = 2 * (2 * K + 1) * T := by ring
    have h5 : ((L : ℝ) + 1) * X * η / 8 = ((L : ℝ) + 1) * (η * X / 8) := by ring
    linarith
  have hLbound : (2 * K + 1) * (2 * (L : ℝ) + 1) ≤ ((L : ℝ) + 1) * (η * X / 8) := by
    have h1 : 2 * (2 * K + 1) ≤ η * X / 8 := by
      rw [div_le_iff₀ hη] at hXbig
      linarith
    have hK0 : (0 : ℝ) ≤ 2 * K + 1 := by positivity
    have h2 := mul_le_mul_of_nonneg_left (show 2 * (L : ℝ) + 1 ≤ 2 * (L + 1) by linarith) hK0
    have h3 := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ L + 1 by positivity)
    linarith
  have hLK : (L : ℝ) + 1 ≤ 2 * ((L : ℝ) - K + 1) := by
    have : (2 * K : ℝ) ≤ L := by exact_mod_cast h2K
    linarith
  have hηX : 0 ≤ η * X / 4 := by positivity
  have h1 := mul_le_mul_of_nonneg_right hLK hηX
  have h2 : (2 * K + 1) * (2 * ((T : ℝ) + L) + 1) =
      (2 * K + 1) * (2 * (T : ℝ)) + (2 * K + 1) * (2 * (L : ℝ) + 1) := by ring
  linarith

/-- **Sparse sweep, assembled.**  Fix `K` with `200·(99/100)^(K+1) ≤ η/4`, take
`L = ⌊log₃₂₄ X⌋ / 3` and `c = η / (48 (2K+1) log 324)`.  The exceptional centers cost at most
`ηX/4 + 6(L+1)·324^L ≤ ηX/2`, and the packed window minima cost at most `ηX/2`. -/
theorem sparse_sweep_assembled : ∀ η : ℝ, 0 < η → ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀,
    ∀ x : ℤ, (amusicalOrbit x).Infinite →
    (((Finset.Icc (-⌊c * X * Real.log X⌋) ⌊c * X * Real.log X⌋).filter
        fun j => 0 ≤ (amusicalPerm ^ j) x ∧ (amusicalPerm ^ j) x < X).card : ℝ) ≤ η * X := by
  intro η hη
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (show 0 < η / 800 by positivity)
    (show (99 : ℝ) / 100 < 1 by norm_num)
  have hℓpos : 0 < Real.log 324 := Real.log_pos (by norm_num)
  refine ⟨η / (48 * (2 * K + 1) * Real.log 324), by positivity,
    max (324 ^ (3 * max (2 * K) ⌈24 / η⌉₊)) ⌈16 * (2 * K + 1) / η⌉₊, ?_⟩
  intro X hX x hinf
  set c := η / (48 * (2 * K + 1) * Real.log 324) with hc
  have hcℓ : c * Real.log 324 * (48 * (2 * K + 1)) = η := by
    rw [hc]
    field_simp
  have hXpow : 324 ^ (3 * max (2 * K) ⌈24 / η⌉₊) ≤ X := le_trans (le_max_left _ _) hX
  have hX1 : 1 ≤ X := le_trans (Nat.one_le_pow _ _ (by norm_num)) hXpow
  have hlogge : 3 * max (2 * K) ⌈24 / η⌉₊ ≤ Nat.log 324 X :=
    Nat.le_log_of_pow_le (by norm_num) hXpow
  have h2K : 2 * K ≤ Nat.log 324 X / 3 := by
    have := le_max_left (2 * K) ⌈24 / η⌉₊
    omega
  have hceilL : ⌈24 / η⌉₊ ≤ Nat.log 324 X / 3 := by
    have := le_max_right (2 * K) ⌈24 / η⌉₊
    omega
  have hKL : K ≤ Nat.log 324 X / 3 := by omega
  have hXR : (⌈16 * (2 * K + 1) / η⌉₊ : ℝ) ≤ X := by
    exact_mod_cast le_trans (le_max_right _ _) hX
  have hXbig : 16 * (2 * K + 1) / η ≤ (X : ℝ) := le_trans (Nat.le_ceil _) hXR
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX1
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg (by exact_mod_cast hX1)
  have hTz0 : 0 ≤ ⌊c * X * Real.log X⌋ := Int.floor_nonneg.mpr (by positivity)
  have hTcast : ((⌊c * X * Real.log X⌋.toNat : ℕ) : ℤ) = ⌊c * X * Real.log X⌋ :=
    Int.toNat_of_nonneg hTz0
  have hTle : ((⌊c * X * Real.log X⌋.toNat : ℕ) : ℝ) ≤ c * X * Real.log X := by
    have h := Int.floor_le (c * X * Real.log X)
    rw [← hTcast] at h
    exact_mod_cast h
  rw [← hTcast]
  generalize ⌊c * X * Real.log X⌋.toNat = T at hTle ⊢
  generalize hL : Nat.log 324 X / 3 = L at h2K hceilL hKL
  have hlog3 : 3 * L ≤ Nat.log 324 X := by omega
  have hlog3' : Nat.log 324 X + 1 ≤ 3 * L + 3 := by omega
  have hmain := sweep_card_mul_le K L T X hKL x hinf
  generalize ((Finset.Icc (-(T : ℤ)) T).filter
    fun j => 0 ≤ (amusicalPerm ^ j) x ∧ (amusicalPerm ^ j) x < X).card = N at hmain ⊢
  have hCle := count_descent_between_geometric_le K L X
  generalize Nat.count (fun n : ℕ => ∃ i : ↥(Finset.Icc (K + 1) L),
    (amusical^[i] (n : ℤ) < n ∨ amusicalInv^[i] (n : ℤ) < n)) X = C at hmain hCle
  have hP : ((L - K + 1 : ℕ) : ℝ) = (L : ℝ) - K + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hKL, Nat.cast_one]
  have hmainR : ((L : ℝ) - K + 1) * N ≤
      ((L : ℝ) - K + 1) * C + (2 * K + 1) * (2 * (T + L) + 1) := by
    rw [← hP]
    exact_mod_cast hmain
  have hcubeN : (324 ^ L) ^ 3 ≤ X := by
    rw [← pow_mul]
    calc 324 ^ (L * 3) ≤ 324 ^ Nat.log 324 X :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ X := Nat.pow_log_le_self 324 (by omega)
  have hceil : 24 / η ≤ (L : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hceilL)
  have hexc := sweep_exceptional_le_half hη hK hcubeN hceil
  have hlog : Real.log X ≤ (3 * L + 3) * Real.log 324 := by
    have hlt : X < 324 ^ (3 * L + 3) :=
      lt_of_lt_of_le (Nat.lt_pow_succ_log_self (by norm_num) X)
        (Nat.pow_le_pow_right (by norm_num) hlog3')
    have hltR : (X : ℝ) < (324 : ℝ) ^ (3 * L + 3) := by exact_mod_cast hlt
    have := Real.log_lt_log hXpos hltR
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hpack := sweep_packing_le_half hη hcℓ (by positivity) hTle hlog h2K hXbig
  have hPpos : 0 < (L : ℝ) - K + 1 := by
    have : (K : ℝ) ≤ L := by exact_mod_cast hKL
    linarith
  have hNC : (N : ℝ) ≤ C + η * X / 2 := by
    have h : ((L : ℝ) - K + 1) * N ≤ ((L : ℝ) - K + 1) * (C + η * X / 2) := by
      rw [mul_add]
      linarith
    exact le_of_mul_le_mul_left h hPpos
  linarith

end CollatzMoonshot.Amusical
