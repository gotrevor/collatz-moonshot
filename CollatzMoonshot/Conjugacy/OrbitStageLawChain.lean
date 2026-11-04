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

/-! ## The chain of windows -/

/-- The letters read by the first `j` windows: `∑_(i<j) size (stageMap^[i] m)`. -/
def chainLen (m j : ℕ) : ℕ := ∑ i ∈ Finset.range j, Nat.size (stageMap^[i] m)

/-- After the first `j` windows the orbit is at `stageMap^[j] m`. -/
theorem iterate_chainLen (m : ℕ) : ∀ j, tstep^[chainLen m j] m = stageMap^[j] m
  | 0 => rfl
  | j + 1 => by
    rw [chainLen, Finset.sum_range_succ, ← chainLen, add_comm, Function.iterate_add_apply,
      iterate_chainLen m j, Function.iterate_succ_apply']
    rfl

/-- **The deviation along the chain.**  If the first `J` windows are class-good and at most `k`
letters long, every prefix inside the first `j ≤ J` windows deviates by at most
`j (|u| η k + 2|u|)`. -/
theorem abs_wdev_chain {u : List Bool} {η : ℝ} (hL : 1 ≤ u.length) (hη : 0 ≤ η) (m k J : ℕ)
    (hgood : ∀ j < J, ClassGood u η (Nat.size (stageMap^[j] m)) (stageMap^[j] m))
    (hsz : ∀ j < J, Nat.size (stageMap^[j] m) ≤ k) :
    ∀ j ≤ J, ∀ ℓ ≤ chainLen m j, |wdev u m 0 ℓ| ≤ j * (u.length * η * k + 2 * u.length) := by
  have hB : 0 ≤ (u.length : ℝ) * η * k + 2 * u.length := by positivity
  intro j
  induction j with
  | zero =>
    intro _ ℓ hℓ
    have : ℓ = 0 := by simpa [chainLen] using hℓ
    subst this
    simp [wdev, wcnt]
  | succ j ih =>
    intro hj ℓ hℓ
    by_cases hle : ℓ ≤ chainLen m j
    · refine le_trans (ih (by omega) ℓ hle) ?_
      push_cast
      nlinarith
    · push Not at hle
      have hℓ' : ℓ - chainLen m j ≤ Nat.size (stageMap^[j] m) := by
        rw [chainLen, Finset.sum_range_succ, ← chainLen] at hℓ
        omega
      rw [show ℓ = chainLen m j + (ℓ - chainLen m j) by omega, wdev_add, zero_add,
        ← add_zero (chainLen m j), wdev_shift, iterate_chainLen, add_zero]
      have e1 := ih (by omega) (chainLen m j) le_rfl
      have e2 := abs_wdev_le_of_classGood hL hη (hgood j (by omega)) hℓ'
      have hs : (Nat.size (stageMap^[j] m) : ℝ) ≤ k := by exact_mod_cast hsz j (by omega)
      have hLη : 0 ≤ (u.length : ℝ) * η := by positivity
      have e3 : (u.length : ℝ) * η * Nat.size (stageMap^[j] m) ≤ u.length * η * k :=
        mul_le_mul_of_nonneg_left hs hLη
      calc |wdev u m 0 (chainLen m j) + wdev u (stageMap^[j] m) 0 (ℓ - chainLen m j)|
          ≤ |wdev u m 0 (chainLen m j)| + |wdev u (stageMap^[j] m) 0 (ℓ - chainLen m j)| :=
            abs_add_le _ _
        _ ≤ j * (u.length * η * k + 2 * u.length) + (u.length * η * k + 2 * u.length) := by
            linarith
        _ = ((j + 1 : ℕ) : ℝ) * (u.length * η * k + 2 * u.length) := by push_cast; ring

/-- `(39/50)^j ≥ 1/16` for `j ≤ 11`. -/
theorem theta_pow_ge {j : ℕ} (hj : j ≤ 11) : (1 / 16 : ℝ) ≤ (39 / 50 : ℝ) ^ j :=
  le_trans (by norm_num) (pow_le_pow_of_le_one (by norm_num) (by norm_num) hj)

/-- **The sizes along the chain.**  If the first `J ≤ 12` windows are good and `size m ≥ 1200`, then
for `j ≤ J` the `j`-th window is at most `size m` letters and at least `(39/50)^j size m − 5`. -/
theorem chain_sizes {u : List Bool} {η : ℝ} {m : ℕ} (hm : 1 ≤ m) (hk : 1200 ≤ Nat.size m)
    {J : ℕ} (hJ : J ≤ 12) (hgood : ∀ j < J, GoodZero u η (1 / 200) (stageMap^[j] m)) :
    ∀ j ≤ J, 1 ≤ stageMap^[j] m ∧ Nat.size (stageMap^[j] m) ≤ Nat.size m ∧
      (39 / 50 : ℝ) ^ j * Nat.size m - 5 ≤ Nat.size (stageMap^[j] m) := by
  intro j
  induction j with
  | zero => intro _; simp [hm]
  | succ j ih =>
    intro hj
    obtain ⟨h1, hle, hge⟩ := ih (by omega)
    obtain ⟨_, hodd, hsuf⟩ := hgood j (by omega)
    have hkr : (1200 : ℝ) ≤ Nat.size m := by exact_mod_cast hk
    have hθ := theta_pow_ge (j := j) (by omega)
    have h70 : 70 ≤ Nat.size (stageMap^[j] m) := by
      have : (70 : ℝ) ≤ Nat.size (stageMap^[j] m) := by nlinarith
      exact_mod_cast this
    have hnext := size_stageMap_ge h1 hodd
    have hup := size_stageMap_le h70 hsuf
    rw [Function.iterate_succ_apply']
    refine ⟨one_le_stageMap h1, le_trans hup hle, ?_⟩
    rw [pow_succ]
    nlinarith

/-- **Twelve windows cover `4.3 k − 60` letters.** -/
theorem chainLen_ge {u : List Bool} {η : ℝ} {m : ℕ} (hm : 1 ≤ m) (hk : 1200 ≤ Nat.size m)
    (hgood : ∀ j < 12, GoodZero u η (1 / 200) (stageMap^[j] m)) :
    (43 / 10 : ℝ) * Nat.size m - 60 ≤ chainLen m 12 := by
  have hs := chain_sizes hm hk le_rfl hgood
  have hsum : ∑ j ∈ Finset.range 12, ((39 / 50 : ℝ) ^ j * Nat.size m - 5) ≤
      ∑ j ∈ Finset.range 12, (Nat.size (stageMap^[j] m) : ℝ) :=
    Finset.sum_le_sum fun j hj => (hs j (by have := Finset.mem_range.mp hj; omega)).2.2
  have hgeo : (43 / 10 : ℝ) ≤ ∑ j ∈ Finset.range 12, (39 / 50 : ℝ) ^ j := by
    norm_num [Finset.sum_range_succ]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul] at hsum
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hk0 : (0 : ℝ) ≤ Nat.size m := Nat.cast_nonneg _
  rw [chainLen]
  push_cast
  nlinarith

/-! ## Assembly -/

/-- The interior occurrences in the first `N` letters are a window count. -/
theorem card_interior_eq_wcnt (u : List Bool) (n N : ℕ) (hL : 1 ≤ u.length) :
    ((Finset.range N).filter fun i =>
      i + u.length ≤ N ∧ WindowMatch (fun s => u.getD s false) u.length i n).card =
      wcnt u n 0 (N + 1 - u.length) := by
  unfold wcnt
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, zero_add]
  constructor
  · rintro ⟨_, h2, h3⟩
    exact ⟨⟨Nat.zero_le _, by omega⟩, h3⟩
  · rintro ⟨⟨_, h2⟩, h3⟩
    exact ⟨by omega, by omega, h3⟩

theorem abs_one_sub_mul_le {x p : ℝ} (hx : 1 ≤ x) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    |(1 - x) * p| ≤ x := by
  rw [abs_le]
  constructor <;> nlinarith

/-- The empty word is never bad. -/
theorem not_badStart_of_length_zero (C : ℕ) {u : List Bool} (hu : u.length = 0) {δ : ℝ}
    (hδ : 0 ≤ δ) (n : ℕ) : ¬ BadStart C u δ n := by
  unfold BadStart
  push Not
  have hW : ∀ i, WindowMatch (fun s => u.getD s false) u.length i n := fun i s hs => by omega
  have hcard : ((Finset.range (C * Nat.size n)).filter fun i =>
      i + u.length ≤ C * Nat.size n ∧ WindowMatch (fun s => u.getD s false) u.length i n).card =
      C * Nat.size n := by
    rw [Finset.filter_true_of_mem fun i hi => ⟨by rw [hu]; simpa using (Finset.mem_range.mp hi).le,
      hW i⟩, Finset.card_range]
  rw [hcard, hu]
  simp only [pow_zero, mul_one, sub_self, abs_zero]
  positivity

/-- **P3/P4, the windows.**  For `C ≤ 4`, a start whose first twelve windows are good is not bad. -/
theorem not_badStart_of_chain' (C : ℕ) (hC4 : C ≤ 4) (u : List Bool) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (η γ : ℝ) (J k₀ : ℕ), 0 < η ∧ 0 < γ ∧ ∀ m : ℕ, 1 ≤ m → k₀ ≤ Nat.size m →
      (∀ j < J, GoodZero u η γ (stageMap^[j] m)) → ¬ BadStart C u δ m := by
  rcases Nat.eq_zero_or_pos u.length with hL0 | hL
  · exact ⟨1, 1, 0, 0, one_pos, one_pos, fun m _ _ _ =>
      not_badStart_of_length_zero C hL0 hδ.le m⟩
  refine ⟨δ / (48 * u.length), 1 / 200, 12, max 1200 (⌈50 * u.length / δ⌉₊ + u.length),
    by positivity, by norm_num, ?_⟩
  intro m hm hk hgood
  have hk1 : 1200 ≤ Nat.size m := le_trans (le_max_left _ _) hk
  have hk2 : ⌈50 * u.length / δ⌉₊ + u.length ≤ Nat.size m := le_trans (le_max_right _ _) hk
  have hLr : (1 : ℝ) ≤ u.length := by exact_mod_cast hL
  have hkr : (1200 : ℝ) ≤ Nat.size m := by exact_mod_cast hk1
  have hkδ : 50 * (u.length : ℝ) / δ ≤ Nat.size m := by
    have h1 := Nat.le_ceil (50 * (u.length : ℝ) / δ)
    have h2 : ((⌈50 * u.length / δ⌉₊ : ℕ) : ℝ) ≤ Nat.size m := by
      exact_mod_cast (by omega : ⌈50 * u.length / δ⌉₊ ≤ Nat.size m)
    linarith
  have hkδ' : 50 * (u.length : ℝ) ≤ δ * Nat.size m := by
    rw [div_le_iff₀ hδ] at hkδ
    linarith
  set k := Nat.size m with hkdef
  set η := δ / (48 * u.length) with hηdef
  have hη : 0 ≤ η := by positivity
  have hLη : (u.length : ℝ) * η = δ / 48 := by
    rw [hηdef]
    field_simp
  -- the deviation over any prefix inside the twelve windows
  have hs := chain_sizes hm hk1 le_rfl hgood
  have hdev := abs_wdev_chain hL hη m k 12 (fun j hj => (hgood j hj).1)
    (fun j hj => (hs j hj.le).2.1) 12 le_rfl
  have hcov := chainLen_ge hm hk1 hgood
  unfold BadStart
  push Not
  rcases Nat.eq_zero_or_pos C with hC0 | hC
  · subst hC0
    simp only [zero_mul, Finset.range_zero, Finset.filter_empty, Finset.card_empty, Nat.cast_zero,
      zero_mul, sub_zero, abs_zero]
    positivity
  have hLN : u.length ≤ C * k := le_trans (by omega) (Nat.le_mul_of_pos_left k hC)
  rw [card_interior_eq_wcnt u m (C * k) hL]
  set ℓ := C * k + 1 - u.length with hℓdef
  have hℓ : ℓ ≤ chainLen m 12 := by
    have h1 : ((C * k : ℕ) : ℝ) ≤ 4 * k := by
      push_cast
      have : (C : ℝ) ≤ 4 := by exact_mod_cast hC4
      nlinarith
    have h2 : ((C * k : ℕ) : ℝ) ≤ chainLen m 12 := by linarith
    have h3 : C * k ≤ chainLen m 12 := by exact_mod_cast h2
    omega
  have hw := hdev ℓ hℓ
  have hcast : (ℓ : ℝ) = ((C * k : ℕ) : ℝ) + 1 - u.length := by
    rw [hℓdef, Nat.cast_sub (by omega)]
    push_cast
    ring
  set p : ℝ := (1 / 2 : ℝ) ^ u.length with hp
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have heq : (wcnt u m 0 ℓ : ℝ) - ((C * k : ℕ) : ℝ) * p = wdev u m 0 ℓ + (1 - u.length) * p := by
    unfold wdev
    rw [hcast]
    ring
  rw [heq]
  have hb : |(1 - (u.length : ℝ)) * p| ≤ u.length := abs_one_sub_mul_le hLr hp0 hp1
  calc |wdev u m 0 ℓ + (1 - u.length) * p| ≤ |wdev u m 0 ℓ| + |(1 - (u.length : ℝ)) * p| :=
        abs_add_le _ _
    _ ≤ (12 : ℕ) * (u.length * η * k + 2 * u.length) + u.length := by linarith
    _ = δ / 4 * k + 25 * u.length := by rw [hLη]; push_cast; ring
    _ ≤ δ * k := by
        have : 0 ≤ δ * k := by positivity
        linarith

end CollatzMoonshot.Conjugacy
