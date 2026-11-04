/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.OrbitHeightSharp

/-!
# The time law: the time along the chain

The deterministic half of `timeLaw_upper`.  A start on the height line gets below `m^θ` in about
`(1 − θ / 2) size m / β` steps; a run of halvings of length at most `θ size m` then reaches the
passage below the first scale under it (`ltime_le_add_run`); and the remaining stages take at most
`lam x_j` letters each (`passChain`), a geometric sum `≤ 51 θ size m` (`sum_lam_Ico_le`).
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord
open TaoCollatz

/-! ## Runs of halvings -/

/-- Over a run of `0` letters the orbit halves: `2^d · T^(t+d) N = T^t N`. -/
theorem two_pow_mul_tstep_run {N : ℕ} (hN : N % 2 = 1) {k t : ℕ} (h1 : valSum N k < t)
    (h2 : t ≤ valSum N (k + 1)) :
    ∀ d, t + d ≤ valSum N (k + 1) → 2 ^ d * tstep^[t + d] N = tstep^[t] N
  | 0, _ => by simp
  | d + 1, h => by
    have ih := two_pow_mul_tstep_run hN h1 h2 d (by omega)
    have hz := (tstep_between hN h1 h2).2 (t + d) (by omega) (by omega)
    simp only [accWord, decide_eq_false_iff_not] at hz
    have hev : tstep^[t + d] N % 2 = 0 := by omega
    rw [← add_assoc, Function.iterate_succ_apply',
      show tstep (tstep^[t + d] N) = tstep^[t + d] N / 2 by simp [tstep, hev], pow_succ,
      mul_assoc, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hev), ih]

/-- **The passage after a low point.**  If `T^t N ≤ w` for odd `N`, the passage below `w` comes
within `d` more letters, where `2^d ≤ T^t N`: the run of `0`s after `t` halves the orbit. -/
theorem ltime_le_add_run {N w t : ℕ} (hN : N % 2 = 1) (hw : tstep^[t] N ≤ w) :
    ∃ d : ℕ, 2 ^ d ≤ tstep^[t] N ∧ ltime w N ≤ t + d := by
  have hN1 : 1 ≤ N := by omega
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · refine ⟨0, by simpa using hN1, ?_⟩
    have h0 : syr^[0] N ≤ w := by simpa using hw
    have := ltime_le_of_le h0
    simpa [valSum] using this
  · obtain ⟨k, hk1, hk2⟩ := exists_valSum_bracket hN ht
    obtain ⟨hsyr, -⟩ := tstep_between hN hk1 hk2
    refine ⟨valSum N (k + 1) - t, ?_, ?_⟩
    · have he := two_pow_mul_tstep_run hN hk1 hk2 (valSum N (k + 1) - t) (by omega)
      have h1 := one_le_tstep_iterate hN1 (t + (valSum N (k + 1) - t))
      calc 2 ^ (valSum N (k + 1) - t)
          ≤ 2 ^ (valSum N (k + 1) - t) * tstep^[t + (valSum N (k + 1) - t)] N :=
            Nat.le_mul_of_pos_right _ h1
        _ = tstep^[t] N := he
    · have := ltime_le_of_le (le_trans hsyr hw)
      omega

/-! ## The chain of passages -/

/-- **The chain of passages.**  Along `J` large scales, an odd start `n ≤ x^(α²)` good at scale `x`,
whose passage locations below `x_j` are good at `x_j` for `j < J`, passes below every `x_j`, and the
stage from `x_j` to `x_(j+1)` takes at most `lam x_j` letters. -/
theorem passChain (u : List Bool) {δ η x : ℝ} {J n : ℕ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 1000)
    (hx0 : 0 < x) (hbig : ∀ j ≤ J, 10000 ≤ Real.logb 2 (scale x j))
    (hn : n % 2 = 1) (hnhi : (n : ℝ) ≤ x ^ alpha ^ 2) (hsg : ScaleGood u δ η x n)
    (hloc : ∀ j < J, LocGood u δ η (scale x j) (passLoc ⌊scale x j⌋₊ n)) :
    (∀ j ≤ J, passes ⌊scale x j⌋₊ n) ∧
      ∀ j < J, ltime ⌊scale x (j + 1)⌋₊ n ≤ ltime ⌊scale x j⌋₊ n + lam (scale x j) := by
  have hscale0 : scale x 0 = x := by simp [scale]
  have hL10 : 10000 ≤ Real.logb 2 x := by
    have := hbig 0 (Nat.zero_le _)
    rwa [hscale0] at this
  have hsc1 : ∀ j ≤ J, 1 ≤ scale x j := fun j hj => le_trans (by norm_num)
    (two_le_of_logb (Real.rpow_pos_of_pos hx0 _) (by linarith [hbig j hj]))
  have hpref0 : PrefGood [true] (1 / 100) (hgt η x) (lam x) n := by
    have := prefGood_of_winGood (b := 0) hsg.2 (Nat.zero_le _)
    rwa [Function.iterate_zero_apply] at this
  obtain ⟨hpass0, -⟩ := start_passes hη0 hη1 hx0 hL10 hn hnhi hpref0
  have hstage : ∀ j, j < J → passes ⌊scale x j⌋₊ n →
      passes ⌊scale x (j + 1)⌋₊ n ∧
        ltime ⌊scale x (j + 1)⌋₊ n ≤ ltime ⌊scale x j⌋₊ n + lam (scale x j) := by
    intro j hj hp
    have hy0 : 0 < scale x j := Real.rpow_pos_of_pos hx0 _
    have hy1 := hsc1 j hj.le
    have hMo := passLoc_odd ⌊scale x j⌋₊ n hn
    have hMy := passLoc_le_cast n (scale x j) hy1
    obtain ⟨hp', hlt⟩ := next_passes hη0 hη1 hy0 (hbig j hj.le) hMo hMy (hloc j hj).2
    rw [← scale_succ' hx0.le] at hp' hlt
    have hzz : ⌊scale x (j + 1)⌋₊ ≤ ⌊scale x j⌋₊ := by
      refine Nat.floor_le_floor ?_
      rw [scale_succ' hx0.le]
      have := Real.rpow_le_rpow_of_exponent_le (x := scale x j) hy1
        (show alpha⁻¹ ≤ 1 by rw [alpha_eq]; norm_num)
      simpa using this
    obtain ⟨hpn, hlt'⟩ := passes_passLoc hzz hn hp hp'
    exact ⟨hpn, by omega⟩
  have hpassAll : ∀ j ≤ J, passes ⌊scale x j⌋₊ n := by
    intro j
    induction j with
    | zero => intro _; rw [hscale0]; exact hpass0
    | succ j ih => intro hj; exact (hstage j (by omega) (ih (by omega))).1
  exact ⟨hpassAll, fun j hj => (hstage j hj (hpassAll j hj.le)).2⟩

/-- The stages from `x_(j₀)` to `x_J` add up. -/
theorem ltime_le_add_sum {x : ℝ} {J j₀ n : ℕ} (hj₀ : j₀ ≤ J)
    (h : ∀ j < J, ltime ⌊scale x (j + 1)⌋₊ n ≤ ltime ⌊scale x j⌋₊ n + lam (scale x j)) :
    ltime ⌊scale x J⌋₊ n ≤ ltime ⌊scale x j₀⌋₊ n + ∑ j ∈ Finset.Ico j₀ J, lam (scale x j) := by
  induction J, hj₀ using Nat.le_induction with
  | base => simp
  | succ J hJ ih =>
    rw [Finset.sum_Ico_succ_top hJ]
    have := h J (by omega)
    have := ih fun j hj => h j (by omega)
    omega

/-- **The tail is geometric.**  `∑_(j₀ ≤ j < J) lam x_j ≤ (1001 / 20) log₂ x_(j₀)`. -/
theorem sum_lam_Ico_le {x : ℝ} (hx : 1 ≤ x) (j₀ J : ℕ) :
    (∑ j ∈ Finset.Ico j₀ J, (lam (scale x j) : ℝ)) ≤ 1001 / 20 * Real.logb 2 (scale x j₀) := by
  have hx0 : 0 < x := by linarith
  have hL0 : 0 ≤ Real.logb 2 x := Real.logb_nonneg (by norm_num) hx
  have hterm : ∀ j ∈ Finset.Ico j₀ J, (lam (scale x j) : ℝ) ≤ Real.logb 2 x / 20 * alpha⁻¹ ^ j := by
    intro j _
    have h1 : 1 ≤ scale x j := Real.one_le_rpow hx (pow_nonneg (by rw [alpha_eq]; norm_num) _)
    have := lam_le h1
    rw [logb_scale hx0] at this
    linarith
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hg := geom_sum_Ico_le_of_lt_one (m := j₀) (n := J) (x := alpha⁻¹)
    (by rw [alpha_eq]; norm_num) (by rw [alpha_eq]; norm_num)
  have he : alpha⁻¹ ^ j₀ / (1 - alpha⁻¹) = 1001 * alpha⁻¹ ^ j₀ := by
    rw [alpha_eq]; field_simp; norm_num
  rw [he] at hg
  rw [logb_scale hx0]
  have := mul_le_mul_of_nonneg_left hg (show 0 ≤ Real.logb 2 x / 20 by positivity)
  linarith

end CollatzMoonshot.Conjugacy
