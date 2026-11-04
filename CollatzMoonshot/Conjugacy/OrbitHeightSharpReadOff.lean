/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.OrbitHeightLaw

/-!
# The height line to `C*`: reading off along `J` scales

`goodOddOfStages_holds` reads the orbit off along `4000` scales, with the letter-`1` tolerance
`1 / 100`, out to `4.2 size n` letters.  For the word `[true]` the tolerance of the read-off is the
word's own `δ`, so only the number of scales `J` has to depend on the horizon: the passage below
`x_J ≤ n^(α^(−J))` takes at least `(1 − α^(−J)) log₂ n / (β + 2 δ)` letters, which beats `τ size n`
once `τ β < 1`, `α^(−J) ≤ (1 − τβ) / 4` and `δ` is small (`goodOddUpTo_of_stages`).  The chain of
`dTV_chain` over `J` scales then gives the event with probability tending to `1`
(`goodOddUpTo_whp`).
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord
open TaoCollatz

/-- Good for the letter `1` through `τ size n`: every prefix of length `T ≤ τ size n` has its odd
count within `δ size n` of `T / 2`. -/
def GoodOddUpTo (δ τ : ℝ) (n : ℕ) : Prop :=
  ∀ T : ℕ, (T : ℝ) ≤ τ * Nat.size n → |wdev [true] n 0 T| ≤ δ * Nat.size n

/-- Some power of `α⁻¹` is below any positive bound. -/
theorem exists_alpha_inv_pow_le {c : ℝ} (hc : 0 < c) : ∃ J : ℕ, alpha⁻¹ ^ J ≤ c := by
  obtain ⟨J, hJ⟩ := exists_pow_lt_of_lt_one hc (show alpha⁻¹ < 1 by rw [alpha_eq]; norm_num)
  exact ⟨J, hJ.le⟩

/-- A natural number above three reals. -/
theorem exists_nat_ge_three (a b c : ℝ) : ∃ K : ℕ, a ≤ K ∧ b ≤ K ∧ c ≤ K := by
  refine ⟨⌈a⌉₊ + ⌈b⌉₊ + ⌈c⌉₊, ?_, ?_, ?_⟩ <;> push_cast
  · linarith [Nat.le_ceil a, (Nat.cast_nonneg _ : (0 : ℝ) ≤ ⌈b⌉₊),
      (Nat.cast_nonneg _ : (0 : ℝ) ≤ ⌈c⌉₊)]
  · linarith [Nat.le_ceil b, (Nat.cast_nonneg _ : (0 : ℝ) ≤ ⌈a⌉₊),
      (Nat.cast_nonneg _ : (0 : ℝ) ≤ ⌈c⌉₊)]
  · linarith [Nat.le_ceil c, (Nat.cast_nonneg _ : (0 : ℝ) ≤ ⌈b⌉₊),
      (Nat.cast_nonneg _ : (0 : ℝ) ≤ ⌈a⌉₊)]

/-- **The chain along `J` scales.**  If every scale `x_j`, `j ≤ J`, has `log₂ x_j ≥ 10⁴`, an odd
start `n ≤ x^(α²)` good for the letter `1` at scale `x`, whose passage locations below `x_j` are good
at scale `x_j` for `j < J`, passes below `x_J`, and before that passage every prefix of length `T`
has its odd count within `δ T + (J + 1)(η log₂ x + 1)` of `T / 2`. -/
theorem readOff_chain {δ η x : ℝ} {J n : ℕ} (hδ0 : 0 < δ) (hη0 : 0 < η) (hη1 : η ≤ 1 / 1000)
    (hx0 : 0 < x) (hbig : ∀ j ≤ J, 10000 ≤ Real.logb 2 (scale x j))
    (hle : ∀ j ≤ J, Real.logb 2 (scale x j) ≤ Real.logb 2 x)
    (hn : n % 2 = 1) (hnhi : (n : ℝ) ≤ x ^ alpha ^ 2) (hsg : ScaleGood [true] δ η x n)
    (hloc : ∀ j < J, LocGood [true] δ η (scale x j) (passLoc ⌊scale x j⌋₊ n)) :
    (tstep^[ltime ⌊scale x J⌋₊ n] n : ℝ) ≤ scale x J ∧
      ∀ T ≤ ltime ⌊scale x J⌋₊ n,
        |wdev [true] n 0 T| ≤ δ * T + ((J : ℝ) + 1) * (η * Real.logb 2 x + 1) := by
  have hscale0 : scale x 0 = x := by simp [scale]
  have hL10 : 10000 ≤ Real.logb 2 x := by
    have := hbig 0 (Nat.zero_le _)
    rwa [hscale0] at this
  have hsc1 : ∀ j ≤ J, 1 ≤ scale x j := fun j hj => le_trans (by norm_num)
    (two_le_of_logb (Real.rpow_pos_of_pos hx0 _) (by linarith [hbig j hj]))
  -- the first stage
  have hpref0 : ∀ (v : List Bool) (d : ℝ), WinGood v d (hgt η x) (lam x) n →
      PrefGood v d (hgt η x) (lam x) n := by
    intro v d h
    have := prefGood_of_winGood (b := 0) h (Nat.zero_le _)
    rwa [Function.iterate_zero_apply] at this
  obtain ⟨hpass0, hL0⟩ := start_passes hη0 hη1 hx0 hL10 hn hnhi (hpref0 _ _ hsg.2)
  set L : ℕ → ℕ := fun j => ltime ⌊scale x j⌋₊ n with hLdef
  -- the next stages
  have hstage : ∀ j, j < J → passes ⌊scale x j⌋₊ n →
      passes ⌊scale x (j + 1)⌋₊ n ∧
        L (j + 1) = L j + ltime ⌊scale x (j + 1)⌋₊ (passLoc ⌊scale x j⌋₊ n) ∧
        ltime ⌊scale x (j + 1)⌋₊ (passLoc ⌊scale x j⌋₊ n) ≤ lam (scale x j) := by
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
    exact ⟨hpn, hlt', hlt⟩
  have hpassAll : ∀ j ≤ J, passes ⌊scale x j⌋₊ n := by
    intro j
    induction j with
    | zero => intro _; rw [hscale0]; exact hpass0
    | succ j ih => intro hj; exact (hstage j (by omega) (ih (by omega))).1
  have hL0' : L 0 ≤ lam x := by
    show ltime ⌊scale x 0⌋₊ n ≤ lam x
    rw [hscale0]
    exact hL0
  -- the error budget
  have hE : (hgt η x : ℝ) + ∑ i ∈ Finset.range J, (hgt η (scale x i) : ℝ) ≤
      ((J : ℝ) + 1) * (η * Real.logb 2 x + 1) := by
    have h1 : (hgt η x : ℝ) ≤ η * Real.logb 2 x + 1 :=
      hgt_le (mul_nonneg hη0.le (by linarith))
    have h2 : ∑ i ∈ Finset.range J, (hgt η (scale x i) : ℝ) ≤
        ∑ i ∈ Finset.range J, (η * Real.logb 2 x + 1) := by
      refine Finset.sum_le_sum fun i hi => ?_
      have hi' : i ≤ J := by simp at hi; omega
      have hlo := hbig i hi'
      have hhi := mul_le_mul_of_nonneg_left (hle i hi') hη0.le
      refine le_trans (hgt_le (mul_nonneg hη0.le (by linarith))) ?_
      linarith
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
    linarith
  -- the height at the last passage
  have hMJ : passLoc ⌊scale x J⌋₊ n = tstep^[L J] n := passLoc_eq_tstep hn (hpassAll J le_rfl)
  refine ⟨?_, fun T hT => ?_⟩
  · rw [← hMJ]
    exact passLoc_le_cast n _ (hsc1 J le_rfl)
  · -- the chain for the letter `1`, within `δ`
    have hchain := wdev_chain [true] hδ0.le n L (fun j => hgt η (scale x j))
      (fun j => lam (scale x j)) (hgt η x) (lam x) J (hpref0 [true] δ hsg.1) hL0'
      (fun j hj => by
        obtain ⟨-, he, hle⟩ := hstage j hj (hpassAll j hj.le)
        refine ⟨by omega, by omega, ?_⟩
        have := (hloc j hj).1
        rwa [passLoc_eq_tstep hn (hpassAll j hj.le)] at this) J le_rfl T hT
    linarith

/-- The read-off arithmetic.  Over the first `L` letters the height falls from `log₂ n` to at most
`(γ / 4) ℓ`, at the rate `β` plus `2 δ` plus the budget `E`; this cannot happen before `τ s` letters
when `τ β = 1 − γ` and the constants are small. -/
theorem readOff_arith {β l3 γ τ δ η ℓ Ln s Lr o E c hL J : ℝ} (hβdef : β = 1 - l3 / 2)
    (hl3 : 1 ≤ l3) (hl3' : l3 ≤ 2) (hβ : 0 < β) (hγdef : γ = 1 - τ * β) (hγ : 0 < γ)
    (hτ0 : 0 ≤ τ) (hδ0 : 0 ≤ δ) (hδb : δ * τ ≤ γ / 8) (hηb : η * (J + 1) ≤ γ / 8) (hℓ0 : 0 ≤ ℓ)
    (hs0 : 0 ≤ s) (hsz : s ≤ Ln + 1) (hsl : Ln < s) (hnl : ℓ ≤ Ln) (hK3 : 4 * (2 * J + 3) ≤ γ * ℓ)
    (hLr0 : 0 ≤ Lr) (hLrτ : Lr ≤ τ * s) (hE0 : 0 ≤ E) (hE : E ≤ (J + 1) * (η * ℓ + 1))
    (ho : Lr / 2 - (δ * Lr + E) ≤ o) (hc : 0 ≤ c) (hid : hL = Ln - Lr + o * l3 + c)
    (hlog : hL ≤ γ / 4 * ℓ) : False := by
  have ho3 : (Lr / 2 - (δ * Lr + E)) * l3 ≤ o * l3 := mul_le_mul_of_nonneg_right ho (by linarith)
  have h1 : β * Lr ≤ β * (τ * s) := mul_le_mul_of_nonneg_left hLrτ hβ.le
  have h2 : δ * Lr * l3 ≤ δ * (τ * s) * 2 :=
    mul_le_mul (mul_le_mul_of_nonneg_left hLrτ hδ0) hl3' (by linarith) (by positivity)
  have h3 : E * l3 ≤ E * 2 := mul_le_mul_of_nonneg_left hl3' hE0
  have h5 : η * (J + 1) * ℓ ≤ γ / 8 * ℓ := mul_le_mul_of_nonneg_right hηb hℓ0
  have h6 : δ * τ * s ≤ γ / 8 * s := mul_le_mul_of_nonneg_right hδb hs0
  have h8 : γ * s ≤ γ * (Ln + 1) := mul_le_mul_of_nonneg_left hsz hγ.le
  have h9 : γ * ℓ ≤ γ * Ln := mul_le_mul_of_nonneg_left hnl hγ.le
  have h10 : γ * Ln < γ * s := mul_lt_mul_of_pos_left hsl hγ
  subst hβdef hγdef
  linarith

/-- **Reading off along `J` scales.**  For `0 < τ` with `τ β < 1` and `δ' > 0` there are `δ, η > 0`
and a number of scales `J` such that, for large `x`, an odd start `n ∈ [x^α, x^(α²)]` good for the
letter `1` at scale `x`, whose passage locations below `x_j` are good at scale `x_j` for `j < J`,
is good for the letter `1` through `τ size n`. -/
theorem goodOddUpTo_of_stages {τ : ℝ} (hτ0 : 0 < τ) (hτ : τ * heightSlope < 1) {δ' : ℝ}
    (hδ' : 0 < δ') :
    ∃ (δ η X₀ : ℝ) (J : ℕ), 0 < δ ∧ 0 < η ∧ η ≤ 1 / 1000 ∧ ∀ x : ℝ, X₀ ≤ x → ∀ n : ℕ,
      n % 2 = 1 → x ^ alpha ≤ n → (n : ℝ) ≤ x ^ alpha ^ 2 → ScaleGood [true] δ η x n →
      (∀ j < J, LocGood [true] δ η (scale x j) (passLoc ⌊scale x j⌋₊ n)) →
      GoodOddUpTo δ' τ n := by
  have hβ := heightSlope_pos
  set γ : ℝ := 1 - τ * heightSlope with hγdef
  have hγ : 0 < γ := by rw [hγdef]; linarith
  obtain ⟨J, hJ⟩ := exists_alpha_inv_pow_le (show 0 < γ / 4 by positivity)
  set aJ : ℝ := alpha⁻¹ ^ J with haJ
  have haJ0 : 0 < aJ := by rw [haJ, alpha_eq]; positivity
  have hJ1 : (0 : ℝ) < (J : ℝ) + 1 := by positivity
  -- the tolerance of the letter `1`
  set δ : ℝ := min (1 / 100) (min (δ' / (2 * τ)) (γ / (8 * τ))) with hδdef
  have hδ0 : 0 < δ := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hδa : δ * τ ≤ δ' / 2 := by
    have h : δ ≤ δ' / (2 * τ) := le_trans (min_le_right _ _) (min_le_left _ _)
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have hδb : δ * τ ≤ γ / 8 := by
    have h : δ ≤ γ / (8 * τ) := le_trans (min_le_right _ _) (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  -- the shortest window
  set η : ℝ := min (1 / 1000) (min (δ' / (4 * ((J : ℝ) + 1))) (γ / (8 * ((J : ℝ) + 1))))
    with hηdef
  have hη0 : 0 < η := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hη1 : η ≤ 1 / 1000 := min_le_left _ _
  have hηa : η * ((J : ℝ) + 1) ≤ δ' / 4 := by
    have h : η ≤ δ' / (4 * ((J : ℝ) + 1)) := le_trans (min_le_right _ _) (min_le_left _ _)
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have hηb : η * ((J : ℝ) + 1) ≤ γ / 8 := by
    have h : η ≤ γ / (8 * ((J : ℝ) + 1)) := le_trans (min_le_right _ _) (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  obtain ⟨K, hK1, hK2, hK3⟩ := exists_nat_ge_three (10000 / aJ) (4 * ((J : ℝ) + 1) / δ')
    (4 * (2 * (J : ℝ) + 3) / γ)
  refine ⟨δ, η, 2 ^ K, J, hδ0, hη0, hη1, fun x hx n hn hnlo hnhi hsg hloc => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have hKl : (K : ℝ) ≤ Real.logb 2 x := le_logb_of_two_pow_le hx
  clear hx
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ, ℓ = Real.logb 2 x := ⟨_, rfl⟩
  rw [← hℓdef] at hKl
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hK1' : 10000 ≤ aJ * ℓ := by
    rw [div_le_iff₀ haJ0] at hK1
    have := mul_le_mul_of_nonneg_right hKl haJ0.le
    linarith
  have hK2' : 4 * ((J : ℝ) + 1) ≤ δ' * ℓ := by
    rw [div_le_iff₀ hδ'] at hK2
    have := mul_le_mul_of_nonneg_right hKl hδ'.le
    linarith
  have hK3' : 4 * (2 * (J : ℝ) + 3) ≤ γ * ℓ := by
    rw [div_le_iff₀ hγ] at hK3
    have := mul_le_mul_of_nonneg_right hKl hγ.le
    linarith
  clear hKl hK1 hK2 hK3
  -- the scales
  have hxj : ∀ j ≤ J, aJ * ℓ ≤ Real.logb 2 (scale x j) ∧ Real.logb 2 (scale x j) ≤ ℓ := by
    intro j hj
    rw [logb_scale hx0, ← hℓdef]
    refine ⟨mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (by rw [alpha_eq]; norm_num)
      (by rw [alpha_eq]; norm_num) hj) hℓ0, mul_le_of_le_one_left hℓ0 (alpha_inv_pow_le_one j)⟩
  obtain ⟨hMJ, hchain⟩ := readOff_chain hδ0 hη0 hη1 hx0
    (fun j hj => le_trans hK1' (hxj j hj).1) (fun j hj => hℓdef ▸ (hxj j hj).2) hn hnhi hsg hloc
  rw [← hℓdef] at hchain
  set L := ltime ⌊scale x J⌋₊ n with hLdef
  have hn1 : 1 ≤ n := by omega
  have hT1 : (1 : ℝ) ≤ tstep^[L] n := by exact_mod_cast one_le_tstep_iterate hn1 _
  have hlogMJ : Real.logb 2 (tstep^[L] n) ≤ γ / 4 * ℓ := by
    refine le_trans (Real.logb_le_logb_of_le (by norm_num) (by linarith) hMJ) ?_
    rw [logb_scale hx0, ← hℓdef]
    exact mul_le_mul_of_nonneg_right hJ hℓ0
  -- `log₂ n ≥ ℓ`
  have hnl : ℓ ≤ Real.logb 2 n := by
    have h1 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (Real.rpow_pos_of_pos hx0 _) hnlo
    rw [logb_rpow_eq hx0, ← hℓdef] at h1
    have : alpha = 1.001 := rfl
    rw [this] at h1
    linarith
  have hsz := size_le_logb_add_one hn1
  have hs0 : (0 : ℝ) ≤ Nat.size n := Nat.cast_nonneg _
  intro T hT
  -- the passage below the last scale comes late
  have hTL : T ≤ L := by
    by_contra hlt
    push Not at hlt
    have hltR : (L : ℝ) < T := by exact_mod_cast hlt
    have hones := hchain L le_rfl
    rw [wdev_true_eq] at hones
    exact readOff_arith (β := heightSlope) rfl one_le_logb_three
      (by linarith [logb_three_lt]) hβ hγdef hγ hτ0.le hδ0.le hδb hηb hℓ0 hs0 hsz (logb_lt_size hn1) hnl hK3'
      (Nat.cast_nonneg _) (by linarith) (by positivity) le_rfl
      (by linarith [(abs_le.mp hones).1]) (heightCorr_nonneg hn1 L) (height_identity hn1 L)
      hlogMJ
  -- the deviation of the letter `1`
  have hu := hchain T hTL
  have hTs : δ * T ≤ δ * (τ * Nat.size n) := mul_le_mul_of_nonneg_left hT hδ0.le
  have hδs : δ * τ * Nat.size n ≤ δ' / 2 * Nat.size n := mul_le_mul_of_nonneg_right hδa hs0
  have hηℓ : η * ((J : ℝ) + 1) * ℓ ≤ δ' / 4 * ℓ := mul_le_mul_of_nonneg_right hηa hℓ0
  have hℓs : δ' * ℓ ≤ δ' * Nat.size n :=
    mul_le_mul_of_nonneg_left (by linarith [logb_lt_size hn1]) hδ'.le
  have hEJ : ((J : ℝ) + 1) * (η * ℓ + 1) = η * ((J : ℝ) + 1) * ℓ + ((J : ℝ) + 1) := by ring
  have hτs : δ * (τ * Nat.size n) = δ * τ * Nat.size n := by ring
  linarith

/-- **All `J` scales at once.**  Under `winLaw x`, the start is good for the letter `1` through
`τ size n` with probability tending to `1`. -/
theorem goodOddUpTo_whp {τ : ℝ} (hτ0 : 0 < τ) (hτ : τ * heightSlope < 1) {δ' : ℝ}
    (hδ' : 0 < δ') :
    Tendsto (fun x => (winLaw x).expect (Set.indicator {n | ¬ GoodOddUpTo δ' τ n} 1))
      atTop (𝓝 0) := by
  obtain ⟨δ₀, η, X₀, J, hδ₀, hη, hη1, hread⟩ := goodOddUpTo_of_stages hτ0 hτ hδ'
  have hsum := (scaleGood_whp winGoodWhp_holds [true] hδ₀ hη).add
    (tendsto_finsetSum (Finset.range J) fun j _ =>
      stage_whp winGoodWhp_holds locGoodPassLoc_holds [true] hδ₀ hη hη1 j)
  rw [Finset.sum_const_zero, add_zero] at hsum
  refine squeeze_zero' (Eventually.of_forall fun x => prob_nonneg _ _) ?_ hsum
  filter_upwards [eventually_ge_atTop (max X₀ X_windowBase)] with x hx
  refine le_trans (prob_mono_support _ (B := {N | ¬ ScaleGood [true] δ₀ η x N} ∪
    ⋃ j ∈ Finset.range J,
      {n | ¬ LocGood [true] δ₀ η (scale x j) (passLoc ⌊scale x j⌋₊ n)}) fun n hn hbad => ?_)
    (le_trans (expect_indicator_union_le _ _ _) (add_le_add le_rfl (prob_biUnion_le _ _ _)))
  obtain ⟨hodd, hlo, hhi⟩ := winLaw_support (le_trans (le_max_right _ _) hx) hn
  by_contra hcon
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, not_or,
    not_exists, not_not] at hcon
  exact hbad (hread x (le_trans (le_max_left _ _) hx) n hodd hlo hhi hcon.1
    fun j hj => hcon.2 j hj)

end CollatzMoonshot.Conjugacy
