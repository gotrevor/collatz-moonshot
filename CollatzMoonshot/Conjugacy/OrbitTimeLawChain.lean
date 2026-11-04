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

/-! ## The height line, then the chain -/

/-- **Below `2^(θ s)` on the height line.**  With `τ β = 1 − θ / 2`, `δ = θ / 16` and
`8 τ ≤ θ 2^K`, a start good through `τ size m` is below `2^(θ size m)` at `t₁ = ⌊τ size m⌋`. -/
theorem tstep_floor_le_of_goodOddUpTo {θ τ : ℝ} {m K : ℕ} (hθ : 0 < θ)
    (hτβ : τ * heightSlope = 1 - θ / 2) (hτ0 : 0 < τ) (hK : 8 * τ ≤ θ * 2 ^ K) (hm : 1 ≤ m)
    (hs : 4 * ((K : ℝ) + 1) ≤ θ * Nat.size m) (hs2 : 4 ≤ θ * Nat.size m)
    (hg : GoodOddUpTo (θ / 16) τ m) :
    (tstep^[⌊τ * Nat.size m⌋₊] m : ℝ) ≤ 2 ^ (θ * Nat.size m) := by
  have hβ := heightSlope_pos
  have hβ5 := heightSlope_le
  have hsn : (0 : ℝ) ≤ Nat.size m := Nat.cast_nonneg _
  have hτs : 0 ≤ τ * Nat.size m := by positivity
  have ht₁ := Nat.floor_le hτs
  have ht₁' := Nat.lt_floor_add_one (τ * Nat.size m)
  have hδγ : 4 * (θ / 16) ≤ 1 - τ * heightSlope := by rw [hτβ]; linarith
  have hsγ : 2 * ((K : ℝ) + 1) ≤ (1 - τ * heightSlope) * Nat.size m := by rw [hτβ]; linarith
  have hcore := abs_height_sub_line_le_of_goodOddUpTo hτ0.le (by positivity) hδγ hm hsγ hg ht₁
  have hdev := (abs_le.mp hcore).2
  have h2K : (0 : ℝ) < 2 ^ K := by positivity
  have hdiv : (⌊τ * Nat.size m⌋₊ : ℝ) / 2 ^ K ≤ θ * Nat.size m / 8 := by
    rw [div_le_iff₀ h2K]
    have h1 := mul_le_mul_of_nonneg_right hK hsn
    linarith
  have hlog := logb_lt_size hm
  have hβt : heightSlope * (τ * Nat.size m) ≤ heightSlope * ((⌊τ * Nat.size m⌋₊ : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left ht₁'.le hβ.le
  have hτs' : heightSlope * (τ * Nat.size m) = (1 - θ / 2) * Nat.size m := by
    rw [← hτβ]; ring
  have hpos : (0 : ℝ) < tstep^[⌊τ * Nat.size m⌋₊] m := by
    exact_mod_cast one_le_tstep_iterate hm _
  rw [← Real.logb_le_iff_le_rpow one_lt_two hpos]
  linarith

/-- **The time along the chain** (`reach_of_chain`). -/
theorem reach_of_chain_holds {ε : ℝ} (hε : 0 < ε) :
    ∃ δ τ X₀ : ℝ, 0 < δ ∧ 0 < τ ∧ τ * heightSlope < 1 ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 1000 →
      ∀ (x : ℝ) (J : ℕ), (∀ j ≤ J, X₀ ≤ scale x j) → ∀ m : ℕ, m % 2 = 1 → x ^ alpha ≤ m →
        (m : ℝ) ≤ x ^ alpha ^ 2 → GoodOddUpTo δ τ m → ScaleGood [true] (1 / 100) η x m →
        (∀ j < J, LocGood [true] (1 / 100) η (scale x j) (passLoc ⌊scale x j⌋₊ m)) →
        ∃ t : ℕ, (t : ℝ) ≤ (1 / heightSlope + ε) * Nat.size m ∧
          (tstep^[t] m : ℝ) ≤ scale x J := by
  classical
  have hβ := heightSlope_pos
  have hβ5 := heightSlope_le
  set θ : ℝ := min (1 / 4) (ε / 60) with hθdef
  have hθ : 0 < θ := lt_min (by norm_num) (by positivity)
  have hθ4 : θ ≤ 1 / 4 := min_le_left _ _
  have hθε : θ ≤ ε / 60 := min_le_right _ _
  set τ : ℝ := (1 - θ / 2) / heightSlope with hτdef
  have hτβ : τ * heightSlope = 1 - θ / 2 := by rw [hτdef]; field_simp
  have hτ0 : 0 < τ := div_pos (by linarith) hβ
  have hτ1 : τ ≤ 1 / heightSlope := by
    rw [hτdef]; exact div_le_div_of_nonneg_right (by linarith) hβ.le
  set K : ℕ := ⌈8 * τ / θ⌉₊ with hKdef
  have hK : 8 * τ ≤ θ * 2 ^ K := by
    have h2 : (K : ℝ) ≤ 2 ^ K := by exact_mod_cast Nat.lt_two_pow_self.le
    have h3 := le_trans (Nat.le_ceil (8 * τ / θ)) h2
    rw [div_le_iff₀ hθ] at h3
    linarith
  obtain ⟨S, hS1, hS2, hS3⟩ := exists_nat_ge_three 10000 (4 * ((K : ℝ) + 1) / θ) (4 / θ)
  refine ⟨θ / 16, τ, 2 ^ S, by positivity, hτ0, by linarith,
    fun η hη hη1 x J hJ m hm hlo hhi hg hsg hloc => ?_⟩
  have hx : (2 : ℝ) ^ S ≤ x := by simpa [scale] using hJ 0 (Nat.zero_le _)
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have hlx : (S : ℝ) ≤ Real.logb 2 x := le_logb_of_two_pow_le hx
  have hbig : ∀ j ≤ J, 10000 ≤ Real.logb 2 (scale x j) := fun j hj =>
    le_trans hS1 (le_logb_of_two_pow_le (hJ j hj))
  have hm1 : 1 ≤ m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm1
  -- the size of `m`
  have hlxm : Real.logb 2 x ≤ Real.logb 2 m := by
    have h1 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (Real.rpow_pos_of_pos hx0 _) hlo
    rw [logb_rpow_eq hx0] at h1
    have : alpha = 1.001 := rfl
    rw [this] at h1
    linarith
  have hlmx : Real.logb 2 m ≤ 1.002001 * Real.logb 2 x := by
    have h1 := Real.logb_le_logb_of_le (b := 2) (by norm_num) hmR hhi
    rw [logb_rpow_eq hx0, show alpha ^ 2 = 1.002001 by norm_num [alpha]] at h1
    exact h1
  have hsl := logb_lt_size hm1
  have hsu := size_le_logb_add_one hm1
  have hsn : (0 : ℝ) ≤ Nat.size m := Nat.cast_nonneg _
  have hSs : (S : ℝ) ≤ Nat.size m := by linarith
  have hθs1 : 4 * ((K : ℝ) + 1) ≤ θ * Nat.size m := by
    rw [div_le_iff₀ hθ] at hS2
    have := mul_le_mul_of_nonneg_left hSs hθ.le
    linarith
  have hθs2 : 4 ≤ θ * Nat.size m := by
    rw [div_le_iff₀ hθ] at hS3
    have := mul_le_mul_of_nonneg_left hSs hθ.le
    linarith
  -- the height line
  have hT := tstep_floor_le_of_goodOddUpTo hθ hτβ hτ0 hK hm1 hθs1 hθs2 hg
  set t₁ := ⌊τ * Nat.size m⌋₊ with ht₁def
  set y : ℝ := 2 ^ (θ * Nat.size m) with hydef
  have hy0 : 0 < y := by positivity
  have hxy : y ≤ x := by
    have h1 : θ * Nat.size m ≤ Real.logb 2 x := by
      have := mul_le_mul_of_nonneg_right hθ4 hsn
      linarith
    calc y ≤ (2 : ℝ) ^ Real.logb 2 x := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
      _ = x := Real.rpow_logb (by norm_num) (by norm_num) hx0
  -- the first scale below `y`
  have hex : ∃ j, J ≤ j ∨ scale x (j + 1) < y := ⟨J, Or.inl le_rfl⟩
  set j₀ := Nat.find hex with hj₀def
  have hj₀J : j₀ ≤ J := Nat.find_min' hex (Or.inl le_rfl)
  have hyj₀ : y ≤ scale x j₀ := by
    rcases Nat.eq_zero_or_pos j₀ with h0 | hpos
    · rw [h0]; simpa [scale] using hxy
    · obtain ⟨i, hi⟩ : ∃ i, j₀ = i + 1 := ⟨j₀ - 1, by omega⟩
      have hmin := Nat.find_min hex (show i < j₀ by omega)
      push Not at hmin
      rw [hi]
      exact hmin.2
  have htail : (∑ j ∈ Finset.Ico j₀ J, (lam (scale x j) : ℝ)) ≤ 51 * θ * Nat.size m := by
    rcases eq_or_lt_of_le hj₀J with h | h
    · rw [h, Finset.Ico_self, Finset.sum_empty]
      positivity
    · have hspec := Nat.find_spec hex
      have hlt : scale x (j₀ + 1) < y := hspec.resolve_left (by omega)
      have hl1 : Real.logb 2 (scale x (j₀ + 1)) < θ * Nat.size m :=
        (Real.logb_lt_iff_lt_rpow one_lt_two (Real.rpow_pos_of_pos hx0 _)).mpr hlt
      have hl2 : Real.logb 2 (scale x j₀) = alpha * Real.logb 2 (scale x (j₀ + 1)) := by
        rw [logb_scale hx0, logb_scale hx0, pow_succ]
        have : alpha * alpha⁻¹ = 1 := by rw [alpha_eq]; norm_num
        calc alpha⁻¹ ^ j₀ * Real.logb 2 x = (alpha * alpha⁻¹) * (alpha⁻¹ ^ j₀ * Real.logb 2 x) := by
              rw [this, one_mul]
          _ = _ := by ring
      have hsum := sum_lam_Ico_le (le_trans (one_le_pow₀ (by norm_num)) hx)
        j₀ J
      rw [hl2] at hsum
      have : alpha = 1.001 := rfl
      rw [this] at hsum
      linarith
  -- the run of halvings
  have hTw : tstep^[t₁] m ≤ ⌊scale x j₀⌋₊ := Nat.le_floor (le_trans hT hyj₀)
  obtain ⟨d, hd, hlt⟩ := ltime_le_add_run hm hTw
  have hdR : (d : ℝ) ≤ θ * Nat.size m := by
    have h1 : ((2 ^ d : ℕ) : ℝ) ≤ y := le_trans (by exact_mod_cast hd) hT
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast] at h1
    exact (Real.rpow_le_rpow_left_iff one_lt_two).mp h1
  -- the chain
  obtain ⟨hpass, hstep⟩ := passChain [true] hη hη1 hx0 hbig hm hhi hsg hloc
  have hsum := ltime_le_add_sum hj₀J hstep
  refine ⟨ltime ⌊scale x J⌋₊ m, ?_, ?_⟩
  · have hsumR : (ltime ⌊scale x J⌋₊ m : ℝ) ≤
        ltime ⌊scale x j₀⌋₊ m + ∑ j ∈ Finset.Ico j₀ J, (lam (scale x j) : ℝ) := by
      exact_mod_cast hsum
    have hltR : (ltime ⌊scale x j₀⌋₊ m : ℝ) ≤ t₁ + d := by exact_mod_cast hlt
    have ht₁ : (t₁ : ℝ) ≤ τ * Nat.size m := Nat.floor_le (by positivity)
    have h1 : τ * Nat.size m ≤ 1 / heightSlope * Nat.size m := mul_le_mul_of_nonneg_right hτ1 hsn
    have h2 : 52 * θ * Nat.size m ≤ ε * Nat.size m :=
      mul_le_mul_of_nonneg_right (by linarith) hsn
    have he : (1 / heightSlope + ε) * Nat.size m = 1 / heightSlope * Nat.size m + ε * Nat.size m := by
      ring
    linarith
  · rw [← passLoc_eq_tstep hm (hpass J le_rfl)]
    exact passLoc_le_cast m _ (le_trans (by norm_num) (two_le_of_logb (Real.rpow_pos_of_pos hx0 _)
      (by linarith [hbig J le_rfl])))

end CollatzMoonshot.Conjugacy
