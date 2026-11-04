/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.OrbitStageLawPull
import CollatzMoonshot.Conjugacy.OrbitStageLawTerras

/-!
# The stage word law: P3/P4, the window chain

Deterministic.  `ClassGood u η s r` bounds the deviation of every prefix of `≤ s` letters by
`|u| η s + 2|u|` (`abs_wdev_le_of_classGood`).  `OddLow (1/200)` gives
`size (stageMap M) ≥ (39/50) size M − 1` (`size_stageMap_ge`) and `SufGood (s/10)` with `s ≥ 70` gives
`size (stageMap M) ≤ size M` (`size_stageMap_le`).  Twelve good windows then cover
`(∑_(j<12) (39/50)^j) k − 60 ≥ 4.3 k − 60` letters, each with deviation `≤ |u| η k + 2|u|`.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord

/-! ## Prefix counts from class counts -/

/-- The window at `i` of `r` is the window at `0` of `T^i r`. -/
theorem windowMatch_iff_iterate (g : ℕ → Bool) (L i r : ℕ) :
    WindowMatch g L i r ↔ WindowMatch g L 0 (tstep^[i] r) := by
  unfold WindowMatch
  refine forall_congr' fun s => imp_congr_right fun _ => ?_
  simp only [accWord]
  rw [zero_add, add_comm i s, Function.iterate_add_apply]

/-- A window count, letter by letter. -/
theorem wcnt_eq_sum (u : List Bool) (r a ℓ : ℕ) :
    wcnt u r a ℓ = ∑ c ∈ Finset.range ℓ,
      if WindowMatch (uLet u) u.length 0 (tstep^[a + c] r) then 1 else 0 := by
  unfold wcnt
  rw [Finset.card_filter, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [if_congr (windowMatch_iff_iterate _ _ _ _) rfl rfl]
  rfl

/-- A prefix of `q |u|` letters splits into the `|u|` classes. -/
theorem wcnt_mul_eq_sum_blkCnt (u : List Bool) (r : ℕ) : ∀ q : ℕ,
    wcnt u r 0 (q * u.length) =
      ∑ c ∈ Finset.range u.length, blkCnt (WindowMatch (uLet u) u.length 0) u.length c q r
  | 0 => by simp [wcnt, blkCnt_zero]
  | q + 1 => by
    rw [add_mul, one_mul, wcnt_add, wcnt_mul_eq_sum_blkCnt u r q, zero_add, wcnt_eq_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [blkCnt_succ, add_comm (q * u.length) c]

/-- **A prefix of `q |u|` letters.**  Under `ClassGood`, its deviation is at most `|u| η s`. -/
theorem abs_wdev_mul_le {u : List Bool} {η : ℝ} {s r : ℕ} (hL : 1 ≤ u.length) (hη : 0 ≤ η)
    (h : ClassGood u η s r) (q : ℕ) (hq : q * u.length + u.length ≤ s + 1) :
    |wdev u r 0 (q * u.length)| ≤ u.length * η * s := by
  set L := u.length with hLdef
  set p : ℝ := (1 / 2 : ℝ) ^ L with hp
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hdev : wdev u r 0 (q * L) = ∑ c ∈ Finset.range L,
      ((blkCnt (WindowMatch (uLet u) L 0) L c q r : ℝ) - q * p) := by
    unfold wdev
    rw [wcnt_mul_eq_sum_blkCnt, Finset.sum_sub_distrib]
    push_cast
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [hdev]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  by_cases hbig : η * s ≤ q
  · have hqs : (q : ℝ) * L ≤ s := by exact_mod_cast (by omega : q * L ≤ s)
    calc ∑ c ∈ Finset.range L, |(blkCnt (WindowMatch (uLet u) L 0) L c q r : ℝ) - q * p|
        ≤ ∑ _c ∈ Finset.range L, η * q := by
          refine Finset.sum_le_sum fun c hc => ?_
          have hc' := Finset.mem_range.mp hc
          exact h c hc' q (by rw [← hLdef]; omega) hbig
      _ = η * (q * L) := by simp; ring
      _ ≤ η * s := mul_le_mul_of_nonneg_left hqs hη
      _ ≤ L * η * s := by nlinarith [mul_nonneg hη hs0]
  · push Not at hbig
    calc ∑ c ∈ Finset.range L, |(blkCnt (WindowMatch (uLet u) L 0) L c q r : ℝ) - q * p|
        ≤ ∑ _c ∈ Finset.range L, (q : ℝ) := by
          refine Finset.sum_le_sum fun c _ => ?_
          have hb : (blkCnt (WindowMatch (uLet u) L 0) L c q r : ℝ) ≤ q := by
            have : blkCnt (WindowMatch (uLet u) L 0) L c q r ≤ q := by
              unfold blkCnt
              exact le_trans (Finset.card_filter_le _ _) (by simp)
            exact_mod_cast this
          have hb0 : (0 : ℝ) ≤ blkCnt (WindowMatch (uLet u) L 0) L c q r := Nat.cast_nonneg _
          rw [abs_le]
          constructor <;> nlinarith
      _ = L * q := by simp
      _ ≤ L * (η * s) := mul_le_mul_of_nonneg_left hbig.le (by linarith)
      _ = L * η * s := by ring

/-- **Every prefix of at most `s` letters.**  Under `ClassGood`, its deviation is at most
`|u| η s + 2|u|`. -/
theorem abs_wdev_le_of_classGood {u : List Bool} {η : ℝ} {s r : ℕ} (hL : 1 ≤ u.length)
    (hη : 0 ≤ η) (h : ClassGood u η s r) {ℓ : ℕ} (hℓ : ℓ ≤ s) :
    |wdev u r 0 ℓ| ≤ u.length * η * s + 2 * u.length := by
  have hL' := hL
  obtain ⟨L, hLdef⟩ : ∃ L, u.length = L := ⟨_, rfl⟩
  rw [hLdef] at hL ⊢
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hmain : 0 ≤ (L : ℝ) * η * s := by positivity
  by_cases hsL : s + 1 < L
  · refine le_trans (abs_wdev_le _ _ _ _) ?_
    have : (ℓ : ℝ) ≤ L := by exact_mod_cast (by omega : ℓ ≤ L)
    linarith
  · push Not at hsL
    obtain ⟨ℓ₁, h₁l, h₁s, h₁⟩ : ∃ ℓ₁, ℓ₁ ≤ ℓ ∧ ℓ₁ ≤ s + 1 - L ∧ ℓ - ℓ₁ ≤ L := by
      refine ⟨min ℓ (s + 1 - L), min_le_left _ _, min_le_right _ _, ?_⟩
      omega
    have hdm := Nat.div_add_mod' ℓ₁ L
    have hdl : ℓ₁ / L * L ≤ ℓ₁ := Nat.div_mul_le_self _ _
    have hml : ℓ₁ % L < L := Nat.mod_lt _ (by omega)
    generalize ℓ₁ / L = q at hdm hdl
    generalize ℓ₁ % L = ρ at hdm hml
    have hsplit : ℓ = (q * L + ρ) + (ℓ - ℓ₁) := by omega
    have hq : q * L + L ≤ s + 1 := by omega
    have hρ : ρ ≤ L := hml.le
    have hd : ℓ - ℓ₁ ≤ L := h₁
    rw [hsplit, wdev_add, wdev_add]
    have e1 := abs_wdev_mul_le hL' hη h q (by rw [hLdef]; exact hq)
    rw [hLdef] at e1
    have e2 := abs_wdev_le u r (0 + q * L) ρ
    have e3 := abs_wdev_le u r (0 + (q * L + ρ)) (ℓ - ℓ₁)
    have hρr : (ρ : ℝ) ≤ L := by exact_mod_cast hρ
    have hdr : ((ℓ - ℓ₁ : ℕ) : ℝ) ≤ L := by exact_mod_cast hd
    calc |wdev u r 0 (q * L) + wdev u r (0 + q * L) ρ + wdev u r (0 + (q * L + ρ)) (ℓ - ℓ₁)|
        ≤ |wdev u r 0 (q * L)| + |wdev u r (0 + q * L) ρ| +
            |wdev u r (0 + (q * L + ρ)) (ℓ - ℓ₁)| := abs_add_three _ _ _
      _ ≤ L * η * s + 2 * L := by linarith

/-! ## The size of the next window -/

/-- A positive start has a positive window image. -/
theorem one_le_stageMap {M : ℕ} (hM : 1 ≤ M) : 1 ≤ stageMap M := by
  have h := three_pow_mul_le M (Nat.size M)
  unfold stageMap
  by_contra h0
  push Not at h0
  have : tstep^[Nat.size M] M = 0 := by omega
  rw [this, mul_zero] at h
  have : 0 < 3 ^ oddCount M (Nat.size M) * M := Nat.mul_pos (by positivity) hM
  omega

/-- **The next window is not much shorter.**  With at least `(1/2 − 1/200) s` odd letters,
`size (stageMap M) ≥ (39/50) size M − 1`. -/
theorem size_stageMap_ge {M : ℕ} (hM : 1 ≤ M) (h : OddLow (1 / 200) (Nat.size M) M) :
    (39 / 50 : ℝ) * Nat.size M - 1 ≤ Nat.size (stageMap M) := by
  set s := Nat.size M
  set a := oddCount M s
  set X := stageMap M
  have h3 : 3 ^ a * M ≤ 2 ^ s * X := three_pow_mul_le M s
  have h2 : 2 ^ s ≤ 2 * M := two_pow_size_le hM
  have hX : X < 2 ^ Nat.size X := Nat.lt_size_self X
  have hlt : 3 ^ a < 2 ^ (Nat.size X + 1) := by
    have h4 : 3 ^ a * 2 ^ s ≤ 2 ^ s * (2 * X) := by
      calc 3 ^ a * 2 ^ s ≤ 3 ^ a * (2 * M) := Nat.mul_le_mul_left _ h2
        _ = 2 * (3 ^ a * M) := by ring
        _ ≤ 2 * (2 ^ s * X) := Nat.mul_le_mul_left _ h3
        _ = 2 ^ s * (2 * X) := by ring
    have h5 : 3 ^ a ≤ 2 * X := by
      rw [mul_comm] at h4
      exact Nat.le_of_mul_le_mul_left h4 (by positivity)
    rw [pow_succ]
    omega
  have hltr : ((3 : ℝ) ^ a) < (2 : ℝ) ^ (Nat.size X + 1) := by exact_mod_cast hlt
  have hlog := Real.logb_lt_logb (b := 2) (by norm_num) (by positivity) hltr
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at hlog
  have hl3 := logb_three_ge
  have ha : (1 / 2 - 1 / 200 : ℝ) * s ≤ a := h
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  push_cast at hlog
  nlinarith

/-- `10 (q + 1) ≤ 2^q` for `q ≥ 7`. -/
theorem ten_mul_succ_le_two_pow : ∀ q, 7 ≤ q → 10 * (q + 1) ≤ 2 ^ q := by
  intro q hq
  induction q, hq using Nat.le_induction with
  | base => norm_num
  | succ q hq ih =>
    rw [pow_succ]
    have : 10 ≤ 2 ^ q := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hq)
    omega

/-- `27^s · 32 ≤ 32^s` for `s ≥ 21`. -/
theorem twentyseven_pow_le : ∀ s, 21 ≤ s → 27 ^ s * 32 ≤ 32 ^ s := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s _ ih =>
    rw [pow_succ, pow_succ]
    have := Nat.mul_le_mul_right 27 ih
    have h0 : 0 ≤ 32 ^ s := Nat.zero_le _
    linarith

/-- **The next window is not longer.**  With no long suffix above `3/5` odd letters, and
`size M ≥ 70`, `size (stageMap M) ≤ size M`. -/
theorem size_stageMap_le {M : ℕ} (hs : 70 ≤ Nat.size M)
    (h : SufGood (Nat.size M / 10) (Nat.size M) M) : Nat.size (stageMap M) ≤ Nat.size M := by
  set s := Nat.size M
  set a := oddCount M s
  set X := stageMap M
  have hup : 2 ^ s * X ≤ 3 ^ a * M + s * 2 ^ (s + s / 10) :=
    le_trans (two_pow_mul_le M s) (Nat.add_le_add_left (sum_offset_le h) _)
  have hMs : M < 2 ^ s := Nat.lt_size_self M
  have ha : 5 * a ≤ 3 * s := by
    have := h 0 (by omega)
    simpa [oddCount_zero] using this
  -- `3^a ≤ 2^(s−1)`
  have h3a : 3 ^ a ≤ 2 ^ (s - 1) := by
    have h5 : (3 ^ a) ^ 5 ≤ (2 ^ (s - 1)) ^ 5 := by
      rw [← pow_mul, ← pow_mul]
      calc 3 ^ (a * 5) ≤ 3 ^ (3 * s) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 27 ^ s := by rw [pow_mul]; norm_num
        _ ≤ 27 ^ s * 32 / 32 := by simp
        _ ≤ 32 ^ s / 32 := Nat.div_le_div_right (twentyseven_pow_le s (by omega))
        _ = 2 ^ ((s - 1) * 5) := by
          rw [show (32 : ℕ) = 2 ^ 5 by norm_num, ← pow_mul, show (s - 1) * 5 = 5 * s - 5 by omega,
            Nat.pow_div (by omega) (by norm_num)]
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h5
  -- `s 2^(s/10) ≤ 2^(s−1)`
  have hoff : s * 2 ^ (s / 10) ≤ 2 ^ (s - 1) := by
    have h1 := ten_mul_succ_le_two_pow (s / 10) (by omega)
    have h2 : s ≤ 2 ^ (s / 10) := by omega
    calc s * 2 ^ (s / 10) ≤ 2 ^ (s / 10) * 2 ^ (s / 10) := Nat.mul_le_mul_right _ h2
      _ = 2 ^ (s / 10 + s / 10) := by rw [pow_add]
      _ ≤ 2 ^ (s - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hX : X < 2 ^ s := by
    have hss : 2 ^ s = 2 ^ (s - 1) * 2 := by rw [← pow_succ]; congr 1; omega
    have hsplit : s * 2 ^ (s + s / 10) = 2 ^ s * (s * 2 ^ (s / 10)) := by rw [pow_add]; ring
    have hlt : 2 ^ s * X < 2 ^ s * 2 ^ s := by
      calc 2 ^ s * X ≤ 3 ^ a * M + s * 2 ^ (s + s / 10) := hup
        _ < 3 ^ a * 2 ^ s + 2 ^ s * (s * 2 ^ (s / 10)) := by
            rw [hsplit]
            exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left hMs (by positivity)) _
        _ ≤ 2 ^ (s - 1) * 2 ^ s + 2 ^ s * 2 ^ (s - 1) := by
            refine Nat.add_le_add (Nat.mul_le_mul_right _ h3a) (Nat.mul_le_mul_left _ hoff)
        _ = 2 ^ s * 2 ^ s := by rw [hss]; ring
    exact Nat.lt_of_mul_lt_mul_left hlt
  exact Nat.size_le.mpr hX

end CollatzMoonshot.Conjugacy
