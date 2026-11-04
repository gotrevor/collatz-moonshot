/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.OrbitWordLawStage

/-!
# The orbit word law: reading off the orbit

`goodOddOfStages_holds` proves `GoodOddOfStages`.  The passages below the scales
`x_0 = x > x_1 > ⋯ > x_3999` cut the letters of `n` into stretches, each a prefix of a passage
location of length at most `lam x_j` (`next_passes`).  A good prefix has deviation at most
`δ ℓ + H` at every length `ℓ ≤ Λ`, so over the first `L_j` letters the deviation is at most
`δ T + ∑ H` (`wdev_chain`).  Applied to the letter `1` this bounds the descent rate, so the passage
below `x_3999 ≤ n^(1/50)` comes after more than `4.2 size n` letters.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord
open TaoCollatz

/-! ## Numerics -/

set_option exponentiation.threshold 5000 in
/-- `1.001^3999 ≥ 50`, in `ℕ`. -/
theorem pow_1001_ge : (50 : ℕ) * 1000 ^ 3999 ≤ 1001 ^ 3999 := by decide +kernel

set_option exponentiation.threshold 5000 in
/-- `1.001^4000 ≤ 60`, in `ℕ`. -/
theorem pow_1001_le : (1001 : ℕ) ^ 4000 ≤ 60 * 1000 ^ 4000 := by decide +kernel

/-- `α = 1001 / 1000`. -/
theorem alpha_eq : alpha = 1001 / 1000 := by norm_num [alpha]

/-- The last scale is below `x^(1/50)`. -/
theorem alpha_inv_pow_last : alpha⁻¹ ^ 3999 ≤ 1 / 50 := by
  have h : ((50 * 1000 ^ 3999 : ℕ) : ℝ) ≤ ((1001 ^ 3999 : ℕ) : ℝ) := Nat.cast_le.mpr pow_1001_ge
  push_cast at h
  rw [alpha_eq, inv_pow, div_pow, inv_div, div_le_div_iff₀ (by positivity) (by norm_num),
    one_mul, mul_comm]
  exact h

/-- Every scale up to `4000` is above `x^(1/60)`. -/
theorem alpha_inv_pow_ge {j : ℕ} (hj : j ≤ 4000) : 1 / 60 ≤ alpha⁻¹ ^ j := by
  have h : ((1001 ^ 4000 : ℕ) : ℝ) ≤ ((60 * 1000 ^ 4000 : ℕ) : ℝ) := Nat.cast_le.mpr pow_1001_le
  push_cast at h
  have h4 : 1 / 60 ≤ alpha⁻¹ ^ 4000 := by
    rw [alpha_eq, inv_pow, div_pow, inv_div, div_le_div_iff₀ (by norm_num) (by positivity),
      one_mul, mul_comm]
    exact h
  refine le_trans h4 (pow_le_pow_of_le_one (by rw [alpha_eq]; norm_num)
    (by rw [alpha_eq]; norm_num) hj)

/-- `α^(−j) ≤ 1`. -/
theorem alpha_inv_pow_le_one (j : ℕ) : alpha⁻¹ ^ j ≤ 1 :=
  pow_le_one₀ (by rw [alpha_eq]; norm_num) (by rw [alpha_eq]; norm_num)

/-- `log₂ 3 ≥ 1.58`. -/
theorem logb_three_ge : 158 / 100 ≤ Real.logb 2 3 := by
  have h : Real.log ((2 : ℝ) ^ 79) ≤ Real.log ((3 : ℝ) ^ 50) :=
    Real.log_le_log (by positivity) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  rw [Real.logb, le_div_iff₀ (Real.log_pos (by norm_num))]
  push_cast at h
  linarith

/-! ## Sizes -/

/-- `log₂ 2^s = s`. -/
theorem logb_two_pow (s : ℕ) : Real.logb 2 ((2 : ℝ) ^ s) = s := by
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]

/-- `log₂ n < size n`. -/
theorem logb_lt_size {n : ℕ} (hn : 1 ≤ n) : Real.logb 2 n < Nat.size n := by
  have h : (n : ℝ) < ((2 ^ Nat.size n : ℕ) : ℝ) := by exact_mod_cast Nat.lt_size_self n
  push_cast at h
  have := Real.logb_lt_logb one_lt_two (by exact_mod_cast hn) h
  rwa [logb_two_pow] at this

/-- `size n ≤ log₂ n + 1`. -/
theorem size_le_logb_add_one {n : ℕ} (hn : 1 ≤ n) : (Nat.size n : ℝ) ≤ Real.logb 2 n + 1 := by
  have hs : 0 < Nat.size n := Nat.size_pos.mpr hn
  have h2 : 2 ^ (Nat.size n - 1) ≤ n := Nat.lt_size.mp (by omega)
  have h2R : (2 : ℝ) ^ (Nat.size n - 1) ≤ n := by exact_mod_cast h2
  have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h2R
  rw [logb_two_pow] at this
  have hc : ((Nat.size n - 1 : ℕ) : ℝ) = Nat.size n - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  linarith

/-! ## Scales -/

/-- `log₂ x_j = α^(−j) log₂ x`. -/
theorem logb_scale {x : ℝ} (hx : 0 < x) (j : ℕ) :
    Real.logb 2 (scale x j) = alpha⁻¹ ^ j * Real.logb 2 x :=
  logb_rpow_eq hx _

/-- `x_(j+1) = x_j^(1/α)`. -/
theorem scale_succ' {x : ℝ} (hx : 0 ≤ x) (j : ℕ) : scale x (j + 1) = scale x j ^ alpha⁻¹ := by
  rw [scale, scale, ← Real.rpow_mul hx, pow_succ]

/-- `y ≥ 2` from `log₂ y ≥ 1`. -/
theorem two_le_of_logb {y : ℝ} (hy : 0 < y) (h : 1 ≤ Real.logb 2 y) : 2 ≤ y := by
  by_contra hlt
  push Not at hlt
  have := Real.logb_lt_logb one_lt_two hy hlt
  rw [Real.logb_self_eq_one (by norm_num)] at this
  linarith

/-! ## Stages -/

/-- **The first stage.**  For `log₂ x ≥ 10⁴`, an odd `N ≤ x^(α²)` whose prefixes are good for the
letter `1` passes below `x` within `lam x` letters. -/
theorem start_passes {η x : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 1000) (hx0 : 0 < x)
    (hL : 10000 ≤ Real.logb 2 x) {N : ℕ} (hN : N % 2 = 1) (hNx : (N : ℝ) ≤ x ^ alpha ^ 2)
    (hpref : PrefGood [true] (1 / 100) (hgt η x) (lam x) N) :
    passes ⌊x⌋₊ N ∧ ltime ⌊x⌋₊ N ≤ lam x := by
  have hx2 : 2 ≤ x := two_le_of_logb hx0 (by linarith)
  have hy := logb_rpow_eq hx0 (alpha ^ 2)
  have hxy : x ≤ x ^ alpha ^ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le (x := x) (by linarith)
      (show (1 : ℝ) ≤ alpha ^ 2 by norm_num [alpha])
    simpa using this
  have hlam := lam_ge x
  have hhgt := hgt_le (η := η) (x := x) (mul_nonneg hη.le (by linarith))
  have hcov : 20 * (Real.logb 2 (x ^ alpha ^ 2) - Real.logb 2 x + 2) + 4 * (hgt η x : ℝ) ≤
      lam x := by
    rw [hy]
    have ha : alpha ^ 2 = 1.002001 := by norm_num [alpha]
    rw [ha]
    have hηL : η * Real.logb 2 x ≤ Real.logb 2 x / 1000 := by nlinarith
    linarith
  exact stagePasses_holds N _ _ (x ^ alpha ^ 2) x hN hNx hx2 hxy hcov
    (lam_le_self (by linarith)) hpref

/-- **The next stage.**  For `log₂ y ≥ 10⁴`, an odd `M ≤ y` whose prefixes are good for the letter
`1` passes below `y^(1/α)` within `lam y` letters. -/
theorem next_passes {η y : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 1000) (hy : 0 < y)
    (hL : 10000 ≤ Real.logb 2 y) {M : ℕ} (hM : M % 2 = 1) (hMy : (M : ℝ) ≤ y)
    (hpref : PrefGood [true] (1 / 100) (hgt η y) (lam y) M) :
    passes ⌊y ^ alpha⁻¹⌋₊ M ∧ ltime ⌊y ^ alpha⁻¹⌋₊ M ≤ lam y := by
  set z := y ^ alpha⁻¹ with hzdef
  have hz0 : 0 < z := Real.rpow_pos_of_pos hy _
  have hai : alpha⁻¹ = 1000 / 1001 := by rw [alpha_eq]; norm_num
  have hlz : Real.logb 2 z = 1000 / 1001 * Real.logb 2 y := by
    rw [hzdef, logb_rpow_eq hy, hai]
  have hy2 : 2 ≤ y := two_le_of_logb hy (by linarith)
  have hz2 : 2 ≤ z := two_le_of_logb hz0 (by rw [hlz]; linarith)
  have hzy : z ≤ y := by
    have := Real.rpow_le_rpow_of_exponent_le (x := y) (by linarith)
      (show alpha⁻¹ ≤ 1 by rw [hai]; norm_num)
    simpa using this
  have hlam := lam_ge y
  have hhgt := hgt_le (η := η) (x := y) (mul_nonneg hη.le (by linarith))
  have hηL : η * Real.logb 2 y ≤ Real.logb 2 y / 1000 := by nlinarith
  have hcov : 20 * (Real.logb 2 y - Real.logb 2 z + 2) + 4 * (hgt η y : ℝ) ≤ lam y := by
    rw [hlz]
    linarith
  have hΛz : (lam y : ℝ) ≤ z := by
    have h1 := lam_le (show (1 : ℝ) ≤ y by linarith)
    have h2 := logb_le_two_mul hz0
    rw [hlz] at h2
    linarith
  exact stagePasses_holds M _ _ y z hM hMy hz2 hzy hcov hΛz hpref

/-! ## The chain of stretches -/

/-- A good prefix has deviation at most `δ ℓ + H` at every length `ℓ ≤ Λ`. -/
theorem abs_wdev_le_add {v : List Bool} {δ : ℝ} {H Λ M ℓ : ℕ} (hδ : 0 ≤ δ)
    (h : PrefGood v δ H Λ M) (hℓ : ℓ ≤ Λ) : |wdev v M 0 ℓ| ≤ δ * ℓ + H := by
  rcases le_or_gt H ℓ with hH | hH
  · have := h ℓ hH hℓ
    have : (0 : ℝ) ≤ H := Nat.cast_nonneg _
    linarith
  · have := abs_wdev_le v M 0 ℓ
    have : (ℓ : ℝ) ≤ H := by exact_mod_cast hH.le
    have : 0 ≤ δ * ℓ := by positivity
    linarith

/-- **The chain of stretches.**  If the first `L 0 ≤ Λ₀` letters are a good prefix of `n`, and each
stretch `[L j, L (j + 1))` is a good prefix of `tstep^[L j] n` of length `≤ Λ j`, then every prefix
of length `T ≤ L j` has deviation at most `δ T + H₀ + ∑_{i < j} H i`. -/
theorem wdev_chain (v : List Bool) {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) (L H Λ : ℕ → ℕ) (H₀ Λ₀ J : ℕ)
    (h0 : PrefGood v δ H₀ Λ₀ n) (hL0 : L 0 ≤ Λ₀)
    (hstep : ∀ j < J, L j ≤ L (j + 1) ∧ L (j + 1) ≤ L j + Λ j ∧
      PrefGood v δ (H j) (Λ j) (tstep^[L j] n)) :
    ∀ j ≤ J, ∀ T ≤ L j,
      |wdev v n 0 T| ≤ δ * T + ((H₀ : ℝ) + ∑ i ∈ Finset.range j, (H i : ℝ)) := by
  intro j
  induction j with
  | zero =>
    intro _ T hT
    simpa using abs_wdev_le_add hδ h0 (le_trans hT hL0)
  | succ j ih =>
    intro hj T hT
    obtain ⟨h1, h2, h3⟩ := hstep j (by omega)
    have hsum : ∑ i ∈ Finset.range (j + 1), (H i : ℝ) = ∑ i ∈ Finset.range j, (H i : ℝ) + H j :=
      Finset.sum_range_succ _ _
    have hH : (0 : ℝ) ≤ H j := Nat.cast_nonneg _
    rcases le_or_gt T (L j) with hTj | hTj
    · have := ih (by omega) T hTj
      rw [hsum]
      linarith
    · obtain ⟨s, rfl⟩ : ∃ s, T = L j + s := ⟨T - L j, by omega⟩
      have hs : s ≤ Λ j := by omega
      have e : wdev v n (0 + L j) s = wdev v (tstep^[L j] n) 0 s := by
        rw [zero_add, ← wdev_shift, add_zero]
      have hA := ih (by omega) (L j) le_rfl
      have hB := abs_wdev_le_add hδ h3 hs
      rw [wdev_add, e, hsum]
      push_cast
      have := abs_add_le (wdev v n 0 (L j)) (wdev v (tstep^[L j] n) 0 s)
      linarith

/-- The deviation of the letter `1` is the odd count minus half the length. -/
theorem wdev_true_eq (n ℓ : ℕ) : wdev [true] n 0 ℓ = (oddCount n ℓ : ℝ) - ℓ / 2 := by
  rw [wdev, wcnt_true_eq_oddCount]
  simp
  ring

/-! ## Reading off -/

/-- **Reading off the orbit** (`GoodOddOfStages`). -/
theorem goodOddOfStages_holds : GoodOddOfStages := by
  intro u δ' hδ'
  obtain ⟨η, hη0, hηa, hηb⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ δ' / 10 ^ 4 ∧ η ≤ 1 / 10 ^ 6 :=
    ⟨min (δ' / 10 ^ 4) (1 / 10 ^ 6), lt_min (by positivity) (by norm_num), min_le_left _ _,
      min_le_right _ _⟩
  obtain ⟨K, hK1, hK2⟩ : ∃ K : ℕ, (10 : ℝ) ^ 5 / δ' ≤ K ∧ (10 : ℝ) ^ 6 ≤ K := by
    refine ⟨⌈(10 : ℝ) ^ 5 / δ'⌉₊ + 10 ^ 6, ?_, ?_⟩
    · have := Nat.le_ceil ((10 : ℝ) ^ 5 / δ')
      push_cast
      linarith
    · have := Nat.cast_nonneg (α := ℝ) ⌈(10 : ℝ) ^ 5 / δ'⌉₊
      push_cast
      linarith
  refine ⟨δ' / 10, η, 2 ^ K, by positivity, hη0, by linarith,
    fun x hx n hn hnlo hnhi hsg hloc => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have hKl : (K : ℝ) ≤ Real.logb 2 x := le_logb_of_two_pow_le hx
  clear hx
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ, ℓ = Real.logb 2 x := ⟨_, rfl⟩
  rw [← hℓdef] at hKl
  replace hK1 : (10 : ℝ) ^ 5 / δ' ≤ ℓ := le_trans hK1 hKl
  replace hK2 : (10 : ℝ) ^ 6 ≤ ℓ := le_trans hK2 hKl
  clear hKl
  have hδℓ : (10 : ℝ) ^ 5 ≤ δ' * ℓ := by
    rw [div_le_iff₀ hδ'] at hK1
    linarith
  have hns : (numScales : ℕ) = 4000 := rfl
  -- the scales
  have hxj : ∀ j ≤ 4000, 0 < scale x j ∧ ℓ / 60 ≤ Real.logb 2 (scale x j) ∧
      Real.logb 2 (scale x j) ≤ ℓ := by
    intro j hj
    refine ⟨Real.rpow_pos_of_pos hx0 _, ?_, ?_⟩
    · rw [logb_scale hx0, ← hℓdef]
      have := alpha_inv_pow_ge hj
      nlinarith
    · rw [logb_scale hx0, ← hℓdef]
      have := alpha_inv_pow_le_one j
      have : 0 ≤ alpha⁻¹ ^ j := by rw [alpha_eq]; positivity
      nlinarith
  have hbig : ∀ j ≤ 4000, 10000 ≤ Real.logb 2 (scale x j) := by
    intro j hj
    have := (hxj j hj).2.1
    linarith
  have hscale0 : scale x 0 = x := by simp [scale]
  have hn1 : 1 ≤ n := by omega
  -- the first stage
  have hpref0 : ∀ (v : List Bool) (d : ℝ), WinGood v d (hgt η x) (lam x) n →
      PrefGood v d (hgt η x) (lam x) n := by
    intro v d h
    have := prefGood_of_winGood (b := 0) h (Nat.zero_le _)
    rwa [Function.iterate_zero_apply] at this
  obtain ⟨hpass0, hL0⟩ := start_passes hη0 (by linarith) hx0 (by linarith) hn hnhi
    (hpref0 _ _ hsg.2)
  set L : ℕ → ℕ := fun j => ltime ⌊scale x j⌋₊ n with hLdef
  -- the next stages
  have hstage : ∀ j, j + 1 < 4000 → passes ⌊scale x j⌋₊ n →
      passes ⌊scale x (j + 1)⌋₊ n ∧
        L (j + 1) = L j + ltime ⌊scale x (j + 1)⌋₊ (passLoc ⌊scale x j⌋₊ n) ∧
        ltime ⌊scale x (j + 1)⌋₊ (passLoc ⌊scale x j⌋₊ n) ≤ lam (scale x j) := by
    intro j hj hp
    obtain ⟨hy0, -, -⟩ := hxj j (by omega)
    have hy1 : 1 ≤ scale x j := le_trans (by norm_num)
      (two_le_of_logb hy0 (by linarith [hbig j (by omega)]))
    have hMo := passLoc_odd ⌊scale x j⌋₊ n hn
    have hMy := passLoc_le_cast n (scale x j) hy1
    have hlocj := hloc j (by rw [hns]; omega)
    obtain ⟨hp', hlt⟩ := next_passes hη0 (by linarith) hy0 (hbig j (by omega)) hMo hMy hlocj.2
    rw [← scale_succ' hx0.le] at hp' hlt
    have hzz : ⌊scale x (j + 1)⌋₊ ≤ ⌊scale x j⌋₊ := by
      refine Nat.floor_le_floor ?_
      rw [scale_succ' hx0.le]
      have := Real.rpow_le_rpow_of_exponent_le (x := scale x j) hy1
        (show alpha⁻¹ ≤ 1 by rw [alpha_eq]; norm_num)
      simpa using this
    obtain ⟨hpn, hlt'⟩ := passes_passLoc hzz hn hp hp'
    exact ⟨hpn, hlt', hlt⟩
  have hpassAll : ∀ j < 4000, passes ⌊scale x j⌋₊ n := by
    intro j
    induction j with
    | zero => intro _; rw [hscale0]; exact hpass0
    | succ j ih => intro hj; exact (hstage j hj (ih (by omega))).1
  have hL0' : L 0 ≤ lam x := by
    show ltime ⌊scale x 0⌋₊ n ≤ lam x
    rw [hscale0]
    exact hL0
  -- the chain, for any word whose windows and locations are good
  have hchain : ∀ (v : List Bool) (d : ℝ), 0 ≤ d → WinGood v d (hgt η x) (lam x) n →
      (∀ j < 4000, PrefGood v d (hgt η (scale x j)) (lam (scale x j))
        (passLoc ⌊scale x j⌋₊ n)) →
      ∀ T ≤ L 3999, |wdev v n 0 T| ≤ d * T + ((hgt η x : ℝ) +
        ∑ i ∈ Finset.range 3999, (hgt η (scale x i) : ℝ)) := by
    intro v d hd hw hl
    refine wdev_chain v hd n L (fun j => hgt η (scale x j)) (fun j => lam (scale x j))
      (hgt η x) (lam x) 3999 (hpref0 v d hw) hL0' (fun j hj => ?_) 3999 le_rfl
    obtain ⟨-, he, hle⟩ := hstage j (by omega) (hpassAll j (by omega))
    refine ⟨by omega, by omega, ?_⟩
    have := hl j (by omega)
    rwa [passLoc_eq_tstep hn (hpassAll j (by omega))] at this
  -- the error budget
  set E : ℝ := (hgt η x : ℝ) + ∑ i ∈ Finset.range 3999, (hgt η (scale x i) : ℝ) with hEdef
  have hE0 : 0 ≤ E :=
    add_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun i _ => Nat.cast_nonneg _)
  have hE : E ≤ 4000 * (η * ℓ + 1) := by
    have h1 : (hgt η x : ℝ) ≤ η * ℓ + 1 := by
      rw [hℓdef]
      exact hgt_le (mul_nonneg hη0.le (by linarith))
    have h2 : ∑ i ∈ Finset.range 3999, (hgt η (scale x i) : ℝ) ≤
        ∑ i ∈ Finset.range 3999, (η * ℓ + 1) := by
      refine Finset.sum_le_sum fun i hi => ?_
      have hi' : i ≤ 4000 := by simp at hi; omega
      obtain ⟨-, hlo, hhi⟩ := hxj i hi'
      refine le_trans (hgt_le (mul_nonneg hη0.le (by linarith))) ?_
      nlinarith
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
    push_cast at h2
    rw [hEdef]
    linarith
  -- the letter `1` over the first `L 3999` letters
  have hones := hchain [true] (1 / 100) (by norm_num) hsg.2
    (fun j hj => (hloc j (by rw [hns]; exact hj)).2) (L 3999) le_rfl
  rw [wdev_true_eq] at hones
  -- the height at the last passage
  have hpJ := hpassAll 3999 (by omega)
  have hMJ : passLoc ⌊scale x 3999⌋₊ n = tstep^[L 3999] n := passLoc_eq_tstep hn hpJ
  obtain ⟨hyJ, -, -⟩ := hxj 3999 (by omega)
  have hMJy : (tstep^[L 3999] n : ℝ) ≤ scale x 3999 := by
    rw [← hMJ]
    exact passLoc_le_cast n _ (le_trans (by norm_num)
      (two_le_of_logb hyJ (by linarith [hbig 3999 (by omega)])))
  have hT1 : (1 : ℝ) ≤ tstep^[L 3999] n := by exact_mod_cast one_le_tstep_iterate hn1 _
  have hlogMJ : Real.logb 2 (tstep^[L 3999] n) ≤ ℓ / 50 := by
    refine le_trans (Real.logb_le_logb_of_le (by norm_num) (by linarith) hMJy) ?_
    rw [logb_scale hx0, ← hℓdef]
    have := alpha_inv_pow_last
    nlinarith
  have hid := height_identity hn1 (L 3999)
  have hcorr := heightCorr_nonneg hn1 (L 3999)
  -- `log₂ n ≥ ℓ`
  have hnl : ℓ ≤ Real.logb 2 n := by
    have h1 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (Real.rpow_pos_of_pos hx0 _) hnlo
    rw [logb_rpow_eq hx0, ← hℓdef] at h1
    have : alpha = 1.001 := rfl
    nlinarith
  have hsz := size_le_logb_add_one hn1
  have hsz' := logb_lt_size hn1
  have hl3 := logb_three_ge
  have hl3' := logb_three_lt
  intro T hT
  have hTR : 5 * (T : ℝ) ≤ 21 * Nat.size n := by exact_mod_cast hT
  -- the passage below the last scale comes late
  have hTL : T ≤ L 3999 := by
    by_contra hlt
    push Not at hlt
    have hltR : (L 3999 : ℝ) < T := by exact_mod_cast hlt
    set o : ℝ := (oddCount n (L 3999) : ℝ) with hodef
    set Lr : ℝ := (L 3999 : ℝ) with hLrdef
    have hLr0 : 0 ≤ Lr := Nat.cast_nonneg _
    have ho : 49 / 100 * Lr - E ≤ o := by
      have := (abs_le.mp hones).1
      linarith
    have ho3 : (49 / 100 * Lr - E) * Real.logb 2 3 ≤ o * Real.logb 2 3 :=
      mul_le_mul_of_nonneg_right ho (by linarith)
    have hrate : Lr * (1 - 49 / 100 * Real.logb 2 3) ≤ Lr * (2258 / 10000) :=
      mul_le_mul_of_nonneg_left (by linarith) hLr0
    have hE3 : E * Real.logb 2 3 ≤ E * (8 / 5) := mul_le_mul_of_nonneg_left hl3'.le hE0
    have hηℓ : η * ℓ ≤ 1 / 10 ^ 6 * ℓ := mul_le_mul_of_nonneg_right hηb (by linarith)
    linarith
  -- the deviation of `u`
  have hu := hchain u (δ' / 10) (by positivity) hsg.1
    (fun j hj => (hloc j (by rw [hns]; exact hj)).1) T hTL
  have hηℓ : η * ℓ ≤ δ' / 10 ^ 4 * ℓ := mul_le_mul_of_nonneg_right hηa (by linarith)
  have hTs : δ' / 10 * T ≤ δ' / 10 * (21 / 5 * Nat.size n) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hℓs : δ' * ℓ ≤ δ' * Nat.size n := mul_le_mul_of_nonneg_left (by linarith) hδ'.le
  linarith

end CollatzMoonshot.Conjugacy
