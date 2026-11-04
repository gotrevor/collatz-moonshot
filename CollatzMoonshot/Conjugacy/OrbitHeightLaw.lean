/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.OrbitWordLaw

/-!
# The height line and the first passage

`orbitWordLaw_of_le_four` counts letters.  Its proof gives more, since `GoodOdd` controls every prefix
of the first `4.2 size n` letters and `height_identity` reads the height off the odd letters: almost
every start in logarithmic density follows the line `log₂ n − β t`, `β = 1 − log₂ 3 / 2`, through
`t = 4 size n` (`heightLawUpTo_four`).  First passage below `n^θ` follows (`firstPassage_law`), at
`t ≈ (1 − θ) size n / β`.

The line must end at `1 / β = C*`, where it would go negative (`not_heightLawUpTo_of_gt`).  Reaching
`C*` from below is the node `HeightLawBelowThreshold`, proved in `OrbitHeightSharp.lean`.

`StageWordLaw` is the same orbit statement over one stage in place of logarithmic density.  It givesnormality (`normal_of_stageWordLaw`), and it is what logarithmic density does not reach (research note
§16).

`experiments/conjugacy/height_line.py` compares the line and the passage times with data out to
`k = 20000`.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord

/-- The slope of the height line, per step: `β = 1 − log₂ 3 / 2`. -/
noncomputable def heightSlope : ℝ := 1 - Real.logb 2 3 / 2

/-- The orbit of `n` leaves the height line by more than `ε size n`, at some `t ≤ τ size n`. -/
def BadHeight (τ ε : ℝ) (n : ℕ) : Prop :=
  ∃ t : ℕ, (t : ℝ) ≤ τ * Nat.size n ∧
    ε * Nat.size n < |Real.logb 2 (tstep^[t] n) - (Real.logb 2 n - heightSlope * t)|

/-- **The height law through `τ size n`.**  Almost every start in logarithmic density stays within
`ε size n` of the height line, for every `ε > 0`. -/
def HeightLawUpTo (τ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → LogDens0 (BadHeight τ ε)

/-! ## The slope -/

/-- The slope is positive. -/
theorem heightSlope_pos : 0 < heightSlope := by
  have := logb_three_lt
  unfold heightSlope
  linarith

/-- `β ≤ 21 / 100`. -/
theorem heightSlope_le : heightSlope ≤ 21 / 100 := by
  have := logb_three_ge
  unfold heightSlope
  linarith

/-! ## The odd core -/

/-- The deviation from the line is the odd-letter error times `log₂ 3`, plus `heightCorr`. -/
theorem height_sub_line_eq {m : ℕ} (hm : 1 ≤ m) (T : ℕ) :
    Real.logb 2 (tstep^[T] m) - (Real.logb 2 m - heightSlope * T) =
      ((oddCount m T : ℝ) - T / 2) * Real.logb 2 3 + heightCorr m T := by
  rw [height_identity hm T]
  unfold heightSlope
  ring

/-- On the prefixes `GoodOdd` controls, the height is at least `log₂ m − βT − (8/5) δ size m`. -/
theorem height_lower_of_goodOdd {δ : ℝ} {m T : ℕ} (hδ : 0 ≤ δ) (hm : 1 ≤ m)
    (hg : GoodOdd [true] δ m) (hT : 5 * T ≤ 21 * Nat.size m) :
    Real.logb 2 m - heightSlope * T - 8 / 5 * δ * Nat.size m ≤ Real.logb 2 (tstep^[T] m) := by
  have hdev := hg T hT
  rw [wdev_true_eq, abs_le] at hdev
  have hL := logb_three_lt
  have hL1 := one_le_logb_three
  have hs : (0 : ℝ) ≤ Nat.size m := Nat.cast_nonneg _
  have hc := heightCorr_nonneg hm T
  have heq := height_sub_line_eq hm T
  have hmul : -(δ * Nat.size m) * Real.logb 2 3 ≤ ((oddCount m T : ℝ) - T / 2) * Real.logb 2 3 :=
    mul_le_mul_of_nonneg_right hdev.1 (by linarith)
  have hδs : 0 ≤ δ * Nat.size m := mul_nonneg hδ hs
  have hmul2 : (δ * Nat.size m) * Real.logb 2 3 ≤ (δ * Nat.size m) * (8 / 5) :=
    mul_le_mul_of_nonneg_left hL.le hδs
  nlinarith

/-- `42 (k + 1) ≤ 2^k` from `k = 9`. -/
theorem forty_two_succ_le_two_pow {k : ℕ} (hk : 9 ≤ k) : 42 * (k + 1) ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k _ ih =>
    rw [pow_succ]
    omega

/-- Under `GoodOdd` with small `δ` and large `size m`, every odd height stays above
`2^(size m / 10)`, which makes `heightCorr` at most `1`. -/
theorem heightCorr_le_one_of_goodOdd {δ : ℝ} {m T : ℕ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1 / 100) (hm : 1 ≤ m)
    (hs : 500 ≤ Nat.size m) (hg : GoodOdd [true] δ m) (hT : 5 * T ≤ 21 * Nat.size m) :
    heightCorr m T ≤ 1 := by
  set s := Nat.size m with hsdef
  set k := s / 10 with hk
  have hk50 : 50 ≤ k := by omega
  have hsk : s < 10 * (k + 1) := by omega
  have hks : 10 * k ≤ s := by omega
  have hsR : (500 : ℝ) ≤ s := by exact_mod_cast hs
  have hksR : (10 : ℝ) * k ≤ s := by exact_mod_cast hks
  have hw : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hle : ∀ i < T, tstep^[i] m % 2 = 1 → 2 ^ k ≤ tstep^[i] m := by
    intro i hi _
    have hi5 : 5 * i ≤ 21 * s := by omega
    have hlow := height_lower_of_goodOdd hδ hm hg hi5
    have hlog := size_le_logb_add_one hm
    have hβ := heightSlope_le
    have hβ0 := heightSlope_pos
    have hiR : (5 : ℝ) * i ≤ 21 * s := by exact_mod_cast hi5
    have hy1 : 1 ≤ tstep^[i] m := one_le_tstep_iterate hm i
    have hkey : (k : ℝ) ≤ Real.logb 2 (tstep^[i] m) := by
      have h1 : heightSlope * i ≤ 21 / 100 * (21 / 5 * s) := by
        have hi' : (i : ℝ) ≤ 21 / 5 * s := by linarith
        have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
        have hs0 : (0 : ℝ) ≤ 21 / 5 * s := by positivity
        exact mul_le_mul hβ hi' hi0 (by norm_num)
      have h2 : 8 / 5 * δ * s ≤ 8 / 5 * (1 / 100) * s := by
        have : (0 : ℝ) ≤ s := by linarith
        gcongr
      linarith
    have hpos : (0 : ℝ) < tstep^[i] m := by exact_mod_cast hy1
    have hp2 : ((2 : ℝ) ^ k) ≤ tstep^[i] m := by
      rw [← Real.logb_le_logb (b := 2) (by norm_num) (by positivity) hpos, Real.logb_pow,
        Real.logb_self_eq_one (by norm_num), mul_one]
      exact hkey
    exact_mod_cast hp2
  have hc := heightCorr_le_of_ge hw hle
  have hTk : T ≤ 2 ^ k := by
    have := forty_two_succ_le_two_pow (k := k) (by omega)
    omega
  refine le_trans hc ?_
  have h2k : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
  rw [div_le_one h2k]
  exact_mod_cast hTk

/-- **The odd core.**  A good odd `m` stays within `(8/5) δ size m + 1` of the line. -/
theorem abs_height_sub_line_le_of_goodOdd {δ : ℝ} {m T : ℕ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1 / 100)
    (hm : 1 ≤ m) (hs : 500 ≤ Nat.size m) (hg : GoodOdd [true] δ m)
    (hT : 5 * T ≤ 21 * Nat.size m) :
    |Real.logb 2 (tstep^[T] m) - (Real.logb 2 m - heightSlope * T)| ≤
      8 / 5 * δ * Nat.size m + 1 := by
  rw [height_sub_line_eq hm T]
  have hc := heightCorr_le_one_of_goodOdd hδ hδ1 hm hs hg hT
  have hc0 := heightCorr_nonneg hm T
  have hdev := hg T hT
  rw [wdev_true_eq] at hdev
  have hL := logb_three_lt
  have hL1 := one_le_logb_three
  have hL0 : 0 ≤ Real.logb 2 3 := by linarith
  have hsn : (0 : ℝ) ≤ Nat.size m := Nat.cast_nonneg _
  have hmul : |((oddCount m T : ℝ) - T / 2) * Real.logb 2 3| ≤ 8 / 5 * δ * Nat.size m := by
    rw [abs_mul, abs_of_nonneg hL0]
    calc |(oddCount m T : ℝ) - T / 2| * Real.logb 2 3
        ≤ (δ * Nat.size m) * (8 / 5) :=
          mul_le_mul hdev hL.le hL0 (mul_nonneg hδ hsn)
      _ = 8 / 5 * δ * Nat.size m := by ring
  refine le_trans (abs_add_le _ _) ?_
  rw [abs_of_nonneg hc0]
  linarith

/-! ## The even reduction -/

/-- `log₂ (2^a m) = a + log₂ m`. -/
theorem logb_two_pow_mul (a : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    Real.logb 2 ((2 ^ a * m : ℕ) : ℝ) = a + Real.logb 2 m := by
  have hm0 : (m : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  push_cast
  rw [Real.logb_mul (by positivity) hm0, Real.logb_pow, Real.logb_self_eq_one (by norm_num),
    mul_one]

/-- A start `2^a m` with `m` good and `15 a ≤ size m` stays within `a` more of the line. -/
theorem abs_height_sub_line_le_two_pow_mul {δ : ℝ} {a m t : ℕ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1 / 100)
    (hm : 1 ≤ m) (hs : 500 ≤ Nat.size m) (hg : GoodOdd [true] δ m)
    (h15 : 15 * a ≤ Nat.size m) (ht : t ≤ 4 * (Nat.size m + a)) :
    |Real.logb 2 (tstep^[t] (2 ^ a * m)) - (Real.logb 2 ((2 ^ a * m : ℕ) : ℝ) - heightSlope * t)| ≤
      8 / 5 * δ * Nat.size m + 1 + a := by
  have hβ0 := heightSlope_pos
  have hβ1 : heightSlope ≤ 1 := by linarith [heightSlope_le]
  have hsn : (0 : ℝ) ≤ Nat.size m := Nat.cast_nonneg _
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hδs : 0 ≤ 8 / 5 * δ * Nat.size m := by positivity
  rcases le_or_gt t a with hta | hta
  · -- only halvings so far
    obtain ⟨b, rfl⟩ : ∃ b, a = t + b := ⟨a - t, by omega⟩
    have hM : 1 ≤ 2 ^ b * m := Nat.mul_pos (by positivity) hm
    have hnm : 2 ^ (t + b) * m = 2 ^ t * (2 ^ b * m) := by rw [pow_add, mul_assoc]
    rw [hnm, tstep_iterate_two_pow_mul, logb_two_pow_mul t hM]
    have hexp : Real.logb 2 ((2 ^ b * m : ℕ) : ℝ) -
        (t + Real.logb 2 ((2 ^ b * m : ℕ) : ℝ) - heightSlope * t) = -((1 - heightSlope) * t) := by
      ring
    rw [hexp, abs_neg, abs_of_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg _))]
    have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
    push_cast
    have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
    nlinarith
  · -- past the halvings, the orbit of `m`
    obtain ⟨T, rfl⟩ : ∃ T, t = T + a := ⟨t - a, by omega⟩
    rw [Function.iterate_add_apply, tstep_iterate_two_pow_mul, logb_two_pow_mul a hm]
    have hT : 5 * T ≤ 21 * Nat.size m := by omega
    have hcore := abs_height_sub_line_le_of_goodOdd hδ hδ1 hm hs hg hT
    have hexp : Real.logb 2 (tstep^[T] m) - (a + Real.logb 2 m - heightSlope * ((T + a : ℕ) : ℝ)) =
        (Real.logb 2 (tstep^[T] m) - (Real.logb 2 m - heightSlope * T)) -
          ((1 - heightSlope) * a) := by
      push_cast
      ring
    rw [hexp]
    refine le_trans (abs_sub _ _) ?_
    rw [abs_of_nonneg (mul_nonneg (by linarith) ha0)]
    nlinarith

/-- **The height line through `t = 4 size n`.**  From `goodOdd_whp` at `u = [true]`, `height_identity`
and the even reduction.  `heightCorr` is small since the line keeps the orbit above `n^(1/10)`. -/
theorem heightLawUpTo_four : HeightLawUpTo 4 := by
  intro ε hε
  set δ : ℝ := min (1 / 100) (ε / 8) with hδdef
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  set ε' : ℝ := min (1 / 15) (ε / 4) with hε'def
  have hε' : 0 < ε' := lt_min (by norm_num) (by positivity)
  set s₀ : ℕ := max 500 ⌈4 / ε⌉₊ with hs₀
  have h1 : LogDens0 (fun n => ε' * Nat.size (TaoCollatz.oddPart n) < padicValNat 2 n) :=
    logDens0_of_summable (summableLargeTwoAdic ε' hε')
  have h2 : LogDens0 (fun n => n ≤ 2 ^ (2 * s₀)) := logDens0_of_bdd (fun n h => h)
  have h3 : LogDens0 (fun n => ¬ GoodOdd [true] δ (TaoCollatz.oddPart n)) :=
    logDens0OddPart (fun m => ¬ GoodOdd [true] δ m)
      (logDens0OfWindow (fun m => ¬ GoodOdd [true] δ m)
        (goodOdd_whp goodOddOfStages winGoodWhp locGoodPassLoc [true] hδ))
  refine ((h1.or h2).or h3).mono fun n hn => ?_
  by_contra hcon
  simp only [not_or, not_lt, not_le, not_not] at hcon
  obtain ⟨⟨ha, hn2⟩, hgood⟩ := hcon
  have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hn2
  obtain ⟨a, ha_def⟩ : ∃ a, a = padicValNat 2 n := ⟨_, rfl⟩
  obtain ⟨m, hm_def⟩ : ∃ m, m = TaoCollatz.oddPart n := ⟨_, rfl⟩
  rw [← ha_def, ← hm_def] at ha
  rw [← hm_def] at hgood
  have hm : m % 2 = 1 := hm_def ▸ TaoCollatz.oddPart_odd hn0
  have hm1 : 1 ≤ m := by omega
  have hm0 : m ≠ 0 := by omega
  have hnm : 2 ^ a * m = n := by rw [ha_def, hm_def]; exact TaoCollatz.two_pow_mul_oddPart n
  have hsnn : (0 : ℝ) ≤ Nat.size m := Nat.cast_nonneg _
  have ha15 : 15 * (a : ℝ) ≤ Nat.size m := by
    have : ε' ≤ 1 / 15 := min_le_left _ _
    nlinarith
  have ha4 : 4 * (a : ℝ) ≤ ε * Nat.size m := by
    have : ε' ≤ ε / 4 := min_le_right _ _
    nlinarith
  have ha15' : 15 * a ≤ Nat.size m := by exact_mod_cast ha15
  have hsize : s₀ ≤ Nat.size m := by
    by_contra hlt
    push Not at hlt
    have hm2 : m < 2 ^ s₀ := lt_of_lt_of_le (Nat.lt_size_self m) (Nat.pow_le_pow_right (by norm_num)
      hlt.le)
    have ha2 : 2 ^ a ≤ 2 ^ s₀ := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : n < 2 ^ (2 * s₀) := by
      rw [← hnm, two_mul, pow_add]
      exact Nat.mul_lt_mul_of_le_of_lt ha2 hm2 (by positivity)
    omega
  have hs500 : 500 ≤ Nat.size m := le_trans (le_max_left _ _) hsize
  have hs1 : 4 ≤ ε * Nat.size m := by
    have h4 : 4 / ε ≤ Nat.size m :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hsize)
    rwa [div_le_iff₀ hε, mul_comm] at h4
  rw [← hnm] at hn
  obtain ⟨t, ht, hdev⟩ := hn
  rw [size_two_pow_mul hm0] at ht hdev
  have ht' : t ≤ 4 * (Nat.size m + a) := by
    have : (t : ℝ) ≤ ((4 * (Nat.size m + a) : ℕ) : ℝ) := by
      push_cast at ht ⊢
      exact ht
    exact_mod_cast this
  have hδ1 : δ ≤ 1 / 100 := min_le_left _ _
  have hδε : δ ≤ ε / 8 := min_le_right _ _
  have hle := abs_height_sub_line_le_two_pow_mul hδ.le hδ1 hm1 hs500 hgood ha15' ht'
  push_cast at hdev hle
  have hδs : 8 / 5 * δ * (Nat.size m : ℝ) ≤ ε / 5 * Nat.size m := by
    have : 8 / 5 * δ ≤ ε / 5 := by linarith
    exact mul_le_mul_of_nonneg_right this hsnn
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hεa : 0 ≤ ε * (a : ℝ) := by positivity
  nlinarith

/-! ## The end of the line -/

/-- All starts together do not have density `0`: the harmonic sum is at least `log X`. -/
theorem not_logDens0_true : ¬ LogDens0 fun _ => True := by
  intro h
  have h1 : ∀ᶠ X : ℕ in atTop,
      (1 : ℝ) ≤ (∑ n ∈ (Finset.Ico 1 X).filter (fun _ => True), (1 : ℝ) / n) / Real.log X := by
    filter_upwards [eventually_ge_atTop 2] with X hX
    have hlog : 0 < Real.log X := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
    rw [le_div_iff₀ hlog, one_mul, Finset.filter_true_of_mem fun _ _ => trivial]
    obtain ⟨Y, rfl⟩ : ∃ Y, X = Y + 1 := ⟨X - 1, by omega⟩
    have hh := log_add_one_le_harmonic Y
    rw [harmonic_eq_sum_Icc] at hh
    have hIco : Finset.Ico 1 (Y + 1) = Finset.Icc 1 Y := by
      ext i
      simp only [Finset.mem_Ico, Finset.mem_Icc]
      omega
    rw [hIco]
    simpa [one_div] using hh
  have h' : Tendsto (fun X : ℕ =>
      (∑ n ∈ (Finset.Ico 1 X).filter (fun _ => True), (1 : ℝ) / n) / Real.log X) atTop (𝓝 0) :=
    h.congr fun X => by congr!
  have := ge_of_tendsto h' h1
  norm_num at this

/-- Past the end of the line, a start with `β < ε size n` is bad at time `⌊τ size n⌋`. -/
theorem badHeight_of_gt {τ : ℝ} (hτ : 1 < τ * heightSlope) {n : ℕ} (hn : 1 ≤ n)
    (hs : heightSlope < (τ * heightSlope - 1) / 2 * Nat.size n) :
    BadHeight τ ((τ * heightSlope - 1) / 2) n := by
  have hβ := heightSlope_pos
  have hτ0 : 0 < τ := by
    by_contra hneg
    have : τ * heightSlope ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hneg) hβ.le
    linarith
  have hsn : (0 : ℝ) ≤ Nat.size n := Nat.cast_nonneg _
  have hτs : 0 ≤ τ * Nat.size n := by positivity
  refine ⟨⌊τ * Nat.size n⌋₊, Nat.floor_le hτs, lt_of_lt_of_le ?_ (le_abs_self _)⟩
  have hy : 0 ≤ Real.logb 2 (tstep^[⌊τ * Nat.size n⌋₊] n) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast one_le_tstep_iterate hn _)
  have hfl := Nat.lt_floor_add_one (τ * Nat.size n)
  have hlog := logb_lt_size hn
  have hmul := mul_lt_mul_of_pos_left hfl hβ
  nlinarith

/-- **The line ends at `C* = 1 / β`.**  Past it the line goes negative while heights stay `≥ 0`, so every
large start is bad. -/
theorem not_heightLawUpTo_of_gt {τ : ℝ} (hτ : 1 < τ * heightSlope) : ¬ HeightLawUpTo τ := by
  intro h
  have hβ := heightSlope_pos
  set ε : ℝ := (τ * heightSlope - 1) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  set K : ℕ := ⌈heightSlope / ε⌉₊ with hK
  refine not_logDens0_true (((h ε hε).or (logDens0_of_bdd (B := 2 ^ (K + 1)) fun n h => h)).mono
    fun n _ => ?_)
  rcases le_or_gt n (2 ^ (K + 1)) with hn | hn
  · exact Or.inr hn
  refine Or.inl (badHeight_of_gt hτ (lt_of_le_of_lt (Nat.zero_le _) hn) ?_)
  have hsize : K + 1 < Nat.size n := Nat.lt_size.mpr hn.le
  have hsR : ((K : ℕ) : ℝ) ≤ Nat.size n := by exact_mod_cast (by omega : K ≤ Nat.size n)
  have hs' : ((K : ℕ) : ℝ) + 1 ≤ Nat.size n := by exact_mod_cast (by omega : K + 1 ≤ Nat.size n)
  have hc : heightSlope / ε ≤ K := Nat.le_ceil _
  rw [div_le_iff₀ hε] at hc
  have : heightSlope < (K + 1) * ε := by nlinarith
  calc heightSlope < (K + 1) * ε := this
    _ ≤ Nat.size n * ε := by gcongr
    _ = ε * Nat.size n := mul_comm _ _

/-- **Node: the height line all the way to `C*`.**  The chain of `dTV_chain` with a number of scales
depending on `τ`, in place of the fixed `numScales`.  Proved in `OrbitHeightSharp.lean`
(`heightLawBelowThreshold`). -/
def HeightLawBelowThreshold : Prop :=
  ∀ τ : ℝ, τ * heightSlope < 1 → HeightLawUpTo τ

/-- **First passage below `n^θ`.**  For `θ` above `1 − 4β ≈ 0.17`, almost every start in logarithmic
density stays above `n^θ` until `((1 − θ) / β − ε) size n` steps, and has been at or below it by
`((1 − θ) / β + ε) size n`.  From `heightLawUpTo_four`. -/
theorem firstPassage_law {θ ε : ℝ} (hθ : 1 - 4 * heightSlope < θ) (hθ1 : θ < 1) (hε : 0 < ε) :
    LogDens0 fun n : ℕ => ¬ (
      (∀ t : ℕ, (t : ℝ) ≤ ((1 - θ) / heightSlope - ε) * Nat.size n →
        (n : ℝ) ^ θ < (tstep^[t] n : ℝ)) ∧
      ∃ t : ℕ, (t : ℝ) ≤ ((1 - θ) / heightSlope + ε) * Nat.size n ∧
        (tstep^[t] n : ℝ) ≤ (n : ℝ) ^ θ) := by
  have hβ := heightSlope_pos
  have hβ5 := heightSlope_le
  set c : ℝ := (1 - θ) / heightSlope with hc
  have hcβ : heightSlope * c = 1 - θ := by rw [hc]; field_simp
  have hc4 : c < 4 := by
    rw [hc, div_lt_iff₀ hβ]
    linarith
  have hc0 : 0 < c := div_pos (by linarith) hβ
  set η : ℝ := min ε (4 - c) with hηdef
  have hη : 0 < η := lt_min hε (by linarith)
  have hηε : η ≤ ε := min_le_left _ _
  have hη4 : η ≤ 4 - c := min_le_right _ _
  set ε₀ : ℝ := heightSlope * η / 2 with hε₀def
  have hε₀ : 0 < ε₀ := by positivity
  have hθ0 : 0 < θ := by linarith
  set K : ℕ := ⌈1 / ε₀⌉₊ with hK
  refine ((heightLawUpTo_four ε₀ hε₀).or
    (logDens0_of_bdd (B := 2 ^ (K + 1)) fun n h => h)).mono fun n hbad => ?_
  by_contra hcon
  simp only [not_or, not_le] at hcon
  obtain ⟨hgood, hn⟩ := hcon
  have hn1 : 1 ≤ n := by
    have : 0 < 2 ^ (K + 1) := by positivity
    omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hsize : K + 1 < Nat.size n := Nat.lt_size.mpr hn.le
  have hsn : (0 : ℝ) ≤ Nat.size n := Nat.cast_nonneg _
  have hlarge : 1 < ε₀ * Nat.size n := by
    have h1 : 1 / ε₀ ≤ K := Nat.le_ceil _
    rw [div_le_iff₀ hε₀] at h1
    have h2 : ((K : ℕ) : ℝ) + 1 ≤ Nat.size n := by exact_mod_cast (by omega : K + 1 ≤ Nat.size n)
    nlinarith
  have hline : ∀ t : ℕ, (t : ℝ) ≤ 4 * Nat.size n →
      |Real.logb 2 (tstep^[t] n) - (Real.logb 2 n - heightSlope * t)| ≤ ε₀ * Nat.size n := by
    intro t ht
    by_contra hlt
    exact hgood ⟨t, ht, not_le.mp hlt⟩
  have hlog := logb_lt_size hn1
  have hlog2 := size_le_logb_add_one hn1
  have h1θ : 0 < 1 - θ := by linarith
  apply hbad
  constructor
  · intro t ht
    have ht4 : (t : ℝ) ≤ 4 * Nat.size n := by
      refine le_trans ht (mul_le_mul_of_nonneg_right ?_ hsn)
      linarith
    have hdev := abs_le.mp (hline t ht4)
    have hy1 : (0 : ℝ) < tstep^[t] n := by exact_mod_cast one_le_tstep_iterate hn1 t
    rw [← Real.logb_lt_logb_iff (b := 2) (by norm_num) (Real.rpow_pos_of_pos hnR θ) hy1,
      Real.logb_rpow_eq_mul_logb_of_pos hnR]
    have h1 : heightSlope * t ≤ heightSlope * ((c - ε) * Nat.size n) :=
      mul_le_mul_of_nonneg_left ht hβ.le
    have h2 : (1 - θ) * ((Nat.size n : ℝ) - 1) ≤ (1 - θ) * Real.logb 2 n :=
      mul_le_mul_of_nonneg_left (by linarith) h1θ.le
    have h3 : heightSlope * ((c - ε) * Nat.size n) =
        (1 - θ) * Nat.size n - heightSlope * ε * Nat.size n := by
      rw [← hcβ]
      ring
    have h4 : 2 * ε₀ * Nat.size n ≤ heightSlope * ε * Nat.size n := by
      refine mul_le_mul_of_nonneg_right ?_ hsn
      rw [hε₀def]
      nlinarith
    nlinarith
  · have hτ : 0 ≤ (c + η) * Nat.size n := by positivity
    refine ⟨⌊(c + η) * Nat.size n⌋₊, ?_, ?_⟩
    · refine le_trans (Nat.floor_le hτ) (mul_le_mul_of_nonneg_right ?_ hsn)
      linarith
    · have ht4 : (⌊(c + η) * Nat.size n⌋₊ : ℝ) ≤ 4 * Nat.size n := by
        refine le_trans (Nat.floor_le hτ) (mul_le_mul_of_nonneg_right ?_ hsn)
        linarith
      have hdev := abs_le.mp (hline _ ht4)
      have hy1 : (0 : ℝ) < tstep^[⌊(c + η) * Nat.size n⌋₊] n := by
        exact_mod_cast one_le_tstep_iterate hn1 _
      rw [← Real.logb_le_logb (b := 2) (by norm_num) hy1 (Real.rpow_pos_of_pos hnR θ),
        Real.logb_rpow_eq_mul_logb_of_pos hnR]
      have hfl := Nat.lt_floor_add_one ((c + η) * Nat.size n)
      have h1 := mul_lt_mul_of_pos_left hfl hβ
      have h2 : (1 - θ) * Real.logb 2 n ≤ (1 - θ) * Nat.size n :=
        mul_le_mul_of_nonneg_left hlog.le h1θ.le
      have h3 : heightSlope * ((c + η) * Nat.size n) =
          (1 - θ) * Nat.size n + 2 * (ε₀ * Nat.size n) := by
        rw [hε₀def, ← hcβ]
        ring
      nlinarith

open Classical in
/-- **Node: the orbit word law over one stage.**  For every word `u` and `δ > 0`, the bad starts are a
vanishing fraction of the `k`-bit integers.  Stronger than `OrbitWordLaw`, which averages stages.
Proved for `C ≤ 4` (`stageWordLaw_of_le_four`, `OrbitStageLaw.lean`).  False for `C ≥ 5`
(`not_stageWordLaw_of_five_le`). -/
def StageWordLaw (C : ℕ) : Prop :=
  ∀ (u : List Bool) (δ : ℝ), 0 < δ → Tendsto
    (fun k : ℕ => (((Finset.Ico (2 ^ (k - 1)) (2 ^ k)).filter (BadStart C u δ)).card : ℝ) / 2 ^ (k - 1))
    atTop (𝓝 0)

/-- The integers of stage `k` have `k` bits. -/
theorem size_of_mem_stage {k n : ℕ} (hk : 1 ≤ k) (h1 : 2 ^ (k - 1) ≤ n) (h2 : n < 2 ^ k) :
    Nat.size n = k := by
  apply le_antisymm
  · exact Nat.size_le.mpr h2
  · have : k - 1 < Nat.size n := Nat.lt_size.mpr h1
    omega

/-- The errors over the fitting offsets of a stage segment are the counts per start, less the
expected total. -/
theorem sum_stageError_eq (g : ℕ → Bool) (L k N m : ℕ) :
    ∑ t ∈ (Finset.range N).filter (fun t => t + L ≤ N), stageError g L k t m =
      ∑ n ∈ Finset.Ico (2 ^ (k - 1)) (2 ^ (k - 1) + m),
        (((Finset.range N).filter fun i => i + L ≤ N ∧ WindowMatch g L i n).card : ℝ) -
      (((Finset.range N).filter (fun t => t + L ≤ N)).card : ℝ) * ((m : ℝ) / 2 ^ L) := by
  unfold stageError
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  congr 1
  have hf : ∀ n, ((Finset.range N).filter fun i => i + L ≤ N ∧ WindowMatch g L i n) =
      ((Finset.range N).filter (fun t => t + L ≤ N)).filter (fun i => WindowMatch g L i n) :=
    fun n => by rw [Finset.filter_filter]
  simp_rw [hf, Finset.card_filter]
  push_cast
  rw [Finset.sum_comm]

/-- A count over `range N` is within `N` of `N 2^(−L)`. -/
theorem abs_card_filter_sub_le (P : ℕ → Prop) [DecidablePred P] (N L : ℕ) :
    |(((Finset.range N).filter P).card : ℝ) - (N : ℕ) * (1 / 2 : ℝ) ^ L| ≤ N := by
  have h1 : (((Finset.range N).filter P).card : ℝ) ≤ N := by
    have := Finset.card_filter_le (Finset.range N) P
    rw [Finset.card_range] at this
    exact_mod_cast this
  have h0 : (0 : ℝ) ≤ ((Finset.range N).filter P).card := Nat.cast_nonneg _
  have hp0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ L := by positivity
  have hp1 : (1 / 2 : ℝ) ^ L ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  rw [abs_le]
  constructor <;> nlinarith

open Classical in
/-- On a stage segment a good start is off by at most `δ k` and a bad start by at most `C k`. -/
theorem abs_sum_card_sub_le (C : ℕ) (u : List Bool) {δ : ℝ} (hδ : 0 ≤ δ) {k m : ℕ} (hk : 1 ≤ k)
    (hm : m ≤ 2 ^ (k - 1)) :
    |∑ n ∈ Finset.Ico (2 ^ (k - 1)) (2 ^ (k - 1) + m),
        (((((Finset.range (C * k)).filter fun i => i + u.length ≤ C * k ∧
          WindowMatch (fun s => u.getD s false) u.length i n).card : ℝ)) -
        (C * k : ℕ) * (1 / 2 : ℝ) ^ u.length)| ≤
      m * (δ * k) +
        ((Finset.Ico (2 ^ (k - 1)) (2 ^ k)).filter (BadStart C u δ)).card * (C * k : ℕ) := by
  have h2k : 2 ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hN0 : (0 : ℝ) ≤ ((C * k : ℕ) : ℝ) := Nat.cast_nonneg _
  have hδk : 0 ≤ δ * k := mul_nonneg hδ (Nat.cast_nonneg _)
  have hbound : ∀ n ∈ Finset.Ico (2 ^ (k - 1)) (2 ^ (k - 1) + m),
      |(((((Finset.range (C * k)).filter fun i => i + u.length ≤ C * k ∧
          WindowMatch (fun s => u.getD s false) u.length i n).card : ℝ)) -
        (C * k : ℕ) * (1 / 2 : ℝ) ^ u.length)| ≤
      δ * k + if BadStart C u δ n then ((C * k : ℕ) : ℝ) else 0 := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hs : Nat.size n = k := size_of_mem_stage hk hn.1 (by omega)
    split_ifs with hbad
    · have := abs_card_filter_sub_le
        (fun i => i + u.length ≤ C * k ∧ WindowMatch (fun s => u.getD s false) u.length i n)
        (C * k) u.length
      linarith
    · rw [add_zero]
      unfold BadStart at hbad
      rw [hs, not_lt] at hbad
      exact hbad
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans (Finset.sum_le_sum hbound) ?_)
  rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, Nat.add_sub_cancel_left, nsmul_eq_mul,
    Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul]
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_right ?_ hN0)
  have hsub : (Finset.Ico (2 ^ (k - 1)) (2 ^ (k - 1) + m)).filter (BadStart C u δ) ⊆
      (Finset.Ico (2 ^ (k - 1)) (2 ^ k)).filter (BadStart C u δ) :=
    Finset.filter_subset_filter _ (Finset.Ico_subset_Ico_right (by omega))
  exact_mod_cast Finset.card_le_card hsub

/-- Dropping the offsets where `u` does not fit moves the expected total by at most `m`. -/
theorem abs_expected_sub_le (L N m : ℕ) :
    |((N : ℕ) - (((Finset.range N).filter (fun t => t + L ≤ N)).card : ℝ)) *
      ((m : ℝ) * (1 / 2 : ℝ) ^ L)| ≤ m := by
  have hle : ((Finset.range N).filter (fun t => t + L ≤ N)).card ≤ N := by
    have := Finset.card_filter_le (Finset.range N) (fun t => t + L ≤ N)
    rwa [Finset.card_range] at this
  have hge : N ≤ ((Finset.range N).filter (fun t => t + L ≤ N)).card + L := by
    have hsub : Finset.range (N - L) ⊆ (Finset.range N).filter (fun t => t + L ≤ N) := by
      intro t ht
      simp only [Finset.mem_range, Finset.mem_filter] at ht ⊢
      omega
    have := Finset.card_le_card hsub
    rw [Finset.card_range] at this
    omega
  have hleR : (((Finset.range N).filter (fun t => t + L ≤ N)).card : ℝ) ≤ N := by exact_mod_cast hle
  have hgeR : (N : ℝ) ≤ ((Finset.range N).filter (fun t => t + L ≤ N)).card + L := by
    exact_mod_cast hge
  have hLp : (L : ℝ) * (1 / 2 : ℝ) ^ L ≤ 1 := by
    have h2 : (L : ℝ) ≤ 2 ^ L := by exact_mod_cast Nat.lt_two_pow_self.le
    have h3 : (2 : ℝ) ^ L * (1 / 2 : ℝ) ^ L = 1 := by
      rw [← mul_pow]
      norm_num
    calc (L : ℝ) * (1 / 2 : ℝ) ^ L ≤ 2 ^ L * (1 / 2 : ℝ) ^ L :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = 1 := h3
  have hp0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ L := by positivity
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  rw [abs_of_nonneg (mul_nonneg (by linarith) (by positivity))]
  have hd : ((N : ℕ) - (((Finset.range N).filter (fun t => t + L ≤ N)).card : ℝ)) *
      (1 / 2 : ℝ) ^ L ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_right (by linarith) hp0) hLp
  calc ((N : ℕ) - (((Finset.range N).filter (fun t => t + L ≤ N)).card : ℝ)) *
        ((m : ℝ) * (1 / 2 : ℝ) ^ L)
      = m * (((N : ℕ) - (((Finset.range N).filter (fun t => t + L ≤ N)).card : ℝ)) *
          (1 / 2 : ℝ) ^ L) := by ring
    _ ≤ m * 1 := mul_le_mul_of_nonneg_left hd hm0
    _ = m := mul_one _

/-- **The stage law gives normality.**  Through `normal_of_stage_bound`: a good start contributes
`δ C k` to the sum over offsets, and each bad start at most `C k`. -/
theorem normal_of_stageWordLaw (C : ℕ) (hC : 1 ≤ C) (h : StageWordLaw C) :
    Normal (collatzChampernowne C) := by
  classical
  refine normal_of_stage_bound C hC fun u δ hδ => ?_
  have hlim := h u (δ / 2) (by positivity)
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds (half_pos hδ)))
  refine ⟨max 1 K₀, le_max_left _ _, fun k hk m hm => ?_⟩
  have hk1 : 1 ≤ k := le_trans (le_max_left _ _) hk
  have hb := hK₀ k (le_trans (le_max_right _ _) hk)
  have hpow : (0 : ℝ) < 2 ^ (k - 1) := by positivity
  rw [div_lt_iff₀ hpow] at hb
  have hsum := abs_sum_card_sub_le C u (δ := δ / 2) (by positivity) hk1 hm
  have hexp := abs_expected_sub_le u.length (C * k) m
  rw [sum_stageError_eq]
  have hmR : (m : ℝ) ≤ 2 ^ (k - 1) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have heq : ∑ n ∈ Finset.Ico (2 ^ (k - 1)) (2 ^ (k - 1) + m),
        (((Finset.range (C * k)).filter fun i => i + u.length ≤ C * k ∧
          WindowMatch (fun s => u.getD s false) u.length i n).card : ℝ) -
      (((Finset.range (C * k)).filter (fun t => t + u.length ≤ C * k)).card : ℝ) *
        ((m : ℝ) / 2 ^ u.length) =
      ∑ n ∈ Finset.Ico (2 ^ (k - 1)) (2 ^ (k - 1) + m),
        (((((Finset.range (C * k)).filter fun i => i + u.length ≤ C * k ∧
          WindowMatch (fun s => u.getD s false) u.length i n).card : ℝ)) -
        (C * k : ℕ) * (1 / 2 : ℝ) ^ u.length) +
      (((C * k : ℕ) : ℝ) -
          (((Finset.range (C * k)).filter (fun t => t + u.length ≤ C * k)).card : ℝ)) *
        ((m : ℝ) * (1 / 2 : ℝ) ^ u.length) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Ico, Nat.add_sub_cancel_left,
      nsmul_eq_mul, one_div, inv_pow, div_eq_mul_inv]
    ring
  rw [heq]
  refine le_trans (abs_add_le _ _) ?_
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hCk : ((C * k : ℕ) : ℝ) = C * k := by push_cast; ring
  rw [hCk] at hsum hexp ⊢
  have hC1 : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have hCk0 : (0 : ℝ) ≤ (C : ℝ) * k := by positivity
  have h1 : (m : ℝ) * (δ / 2 * k) ≤ δ / 2 * (C * k) * 2 ^ (k - 1) := by
    have hk' : (k : ℝ) ≤ C * k := by nlinarith
    calc (m : ℝ) * (δ / 2 * k) = δ / 2 * (k * m) := by ring
      _ ≤ δ / 2 * ((C * k) * 2 ^ (k - 1)) := by gcongr
      _ = δ / 2 * (C * k) * 2 ^ (k - 1) := by ring
  have h2 := mul_le_mul_of_nonneg_right hb.le hCk0
  have h2k : (2 : ℝ) ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [h2k]
  nlinarith

/-- Above the threshold the stage law fails, since `𝒞_C` is not normal. -/
theorem not_stageWordLaw_of_five_le (C : ℕ) (hC : 5 ≤ C) : ¬ StageWordLaw C := fun h =>
  not_normal_of_five_le C hC (normal_of_stageWordLaw C (by omega) h)

end CollatzMoonshot.Conjugacy
