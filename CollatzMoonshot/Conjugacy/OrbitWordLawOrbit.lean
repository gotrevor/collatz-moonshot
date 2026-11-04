/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import TaoCollatz.Sec5.Stabilization
import TaoCollatz.Sec3.Reduction
import CollatzMoonshot.Conjugacy.ChampernowneLog
import CollatzMoonshot.Conjugacy.ChampernowneHeight

/-!
# The orbit word law: the deterministic side

Window counts of a word in the parity letters of an orbit, and how they read off along Tao's
first passages.

* `wcnt u n a ℓ` counts the occurrences of `u` at the start positions `a, …, a + ℓ − 1` of the
  letters of `n`, and `wdev` is its deviation from `ℓ 2^(−|u|)`.  Both are additive in the window
  (`wdev_add`) and shift along the orbit (`wdev_shift`).
* The bridge: for odd `N`, `syr^[k] N = tstep^[valSum N k] N` (`syr_iterate_eq_tstep`).
* Passages compose (`passLoc_passLoc`).
* One stage (`stage_passes`): if the letter `1` has frequency within `1/100` on every prefix of
  length in `[H, Λ]`, the orbit of `M ≤ y` passes below `z` within `Λ` letters, once `Λ` covers
  about `12 log₂ (y / z)`.
* Reading off (`goodOdd_of_stages`): if the start is good at scale `x` and each passage location is
  good at its own scale, the frequency of `u` is right over the first `4.2 size n` letters.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord
open TaoCollatz

/-! ## Window counts -/

/-- Occurrences of `u` at the start positions `a, …, a + ℓ − 1` of the parity letters of `n`. -/
def wcnt (u : List Bool) (n a ℓ : ℕ) : ℕ :=
  ((Finset.Ico a (a + ℓ)).filter fun i => WindowMatch (fun s => u.getD s false) u.length i n).card

/-- The deviation of `wcnt` from its mean `ℓ 2^(−|u|)`. -/
noncomputable def wdev (u : List Bool) (n a ℓ : ℕ) : ℝ :=
  (wcnt u n a ℓ : ℝ) - ℓ * (1 / 2 : ℝ) ^ u.length

/-- Window counts add. -/
theorem wcnt_add (u : List Bool) (n a ℓ₁ ℓ₂ : ℕ) :
    wcnt u n a (ℓ₁ + ℓ₂) = wcnt u n a ℓ₁ + wcnt u n (a + ℓ₁) ℓ₂ := by
  unfold wcnt
  rw [← add_assoc, ← Finset.Ico_union_Ico_eq_Ico (Nat.le_add_right a ℓ₁)
    (Nat.le_add_right (a + ℓ₁) ℓ₂), Finset.filter_union, Finset.card_union_of_disjoint]
  exact Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive _ _ _)

/-- Window deviations add. -/
theorem wdev_add (u : List Bool) (n a ℓ₁ ℓ₂ : ℕ) :
    wdev u n a (ℓ₁ + ℓ₂) = wdev u n a ℓ₁ + wdev u n (a + ℓ₁) ℓ₂ := by
  unfold wdev
  rw [wcnt_add]
  push_cast
  ring

/-- A window of `n` at `b + a` is a window of `tstep^[b] n` at `a`. -/
theorem wcnt_shift (u : List Bool) (n b a ℓ : ℕ) :
    wcnt u n (b + a) ℓ = wcnt u (tstep^[b] n) a ℓ := by
  unfold wcnt
  rw [show b + a + ℓ = b + (a + ℓ) by ring, ← Finset.map_add_left_Ico, Finset.filter_map,
    Finset.card_map]
  congr 1
  refine Finset.filter_congr fun i _ => ?_
  simp only [Function.comp_apply, addLeftEmbedding_apply, WindowMatch]
  refine forall₂_congr fun s _ => ?_
  rw [add_assoc]
  simp only [accWord]
  rw [add_comm b, Function.iterate_add_apply]

/-- Deviations shift along the orbit. -/
theorem wdev_shift (u : List Bool) (n b a ℓ : ℕ) :
    wdev u n (b + a) ℓ = wdev u (tstep^[b] n) a ℓ := by
  unfold wdev
  rw [wcnt_shift]

/-- A deviation is at most the window length. -/
theorem abs_wdev_le (u : List Bool) (n a ℓ : ℕ) : |wdev u n a ℓ| ≤ ℓ := by
  unfold wdev
  have hc : (wcnt u n a ℓ : ℝ) ≤ ℓ := by
    have : wcnt u n a ℓ ≤ ℓ := by
      unfold wcnt
      refine le_trans (Finset.card_filter_le _ _) ?_
      simp
    exact_mod_cast this
  have hp0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ u.length := by positivity
  have hp1 : (1 / 2 : ℝ) ^ u.length ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hl : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _
  have hc0 : (0 : ℝ) ≤ wcnt u n a ℓ := Nat.cast_nonneg _
  rw [abs_le]
  constructor <;> nlinarith

/-- The prefix of the letter `1` counts odd steps. -/
theorem wcnt_true_eq_oddCount (n ℓ : ℕ) : wcnt [true] n 0 ℓ = oddCount n ℓ := by
  rw [oddCount_eq_sum, wcnt, Finset.card_filter, zero_add, ← Finset.range_eq_Ico]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [if_congr (windowMatch_true_iff i n) rfl rfl]

/-! ## Good windows and good prefixes -/

/-- Every window at offset `≤ Λ` with length in `[H, Λ]` has the frequency of `u` within `δ`. -/
def WinGood (u : List Bool) (δ : ℝ) (H Λ n : ℕ) : Prop :=
  ∀ a ℓ, a ≤ Λ → H ≤ ℓ → ℓ ≤ Λ → |wdev u n a ℓ| ≤ δ * ℓ

/-- Every prefix with length in `[H, Λ]` has the frequency of `u` within `δ`. -/
def PrefGood (u : List Bool) (δ : ℝ) (H Λ n : ℕ) : Prop :=
  ∀ ℓ, H ≤ ℓ → ℓ ≤ Λ → |wdev u n 0 ℓ| ≤ δ * ℓ

/-- The window cap at scale `x`: `⌊log₂ x / 20⌋`. -/
noncomputable def lam (x : ℝ) : ℕ := ⌊Real.logb 2 x / 20⌋₊

/-- The shortest controlled window at scale `x`: `⌈η log₂ x⌉`. -/
noncomputable def hgt (η x : ℝ) : ℕ := ⌈η * Real.logb 2 x⌉₊

/-- Good at scale `x`: windows good for `u` (within `δ`) and for the letter `1` (within `1/100`). -/
def ScaleGood (u : List Bool) (δ η x : ℝ) (n : ℕ) : Prop :=
  WinGood u δ (hgt η x) (lam x) n ∧ WinGood [true] (1 / 100) (hgt η x) (lam x) n

/-- A good location at scale `x`: the same, on prefixes only. -/
def LocGood (u : List Bool) (δ η x : ℝ) (M : ℕ) : Prop :=
  PrefGood u δ (hgt η x) (lam x) M ∧ PrefGood [true] (1 / 100) (hgt η x) (lam x) M

/-- Windows give prefixes at every offset `b ≤ Λ`. -/
theorem prefGood_of_winGood {u : List Bool} {δ : ℝ} {H Λ n b : ℕ} (h : WinGood u δ H Λ n)
    (hb : b ≤ Λ) : PrefGood u δ H Λ (tstep^[b] n) := by
  intro ℓ hH hΛ
  rw [← wdev_shift, add_zero]
  exact h b ℓ hb hH hΛ

/-! ## The Syracuse bridge -/

/-- Halving `k` times divides by `2^k`, when `2^k ∣ m`. -/
theorem tstep_iterate_of_dvd : ∀ (k m : ℕ), 2 ^ k ∣ m → tstep^[k] m = m / 2 ^ k
  | 0, m, _ => by simp
  | k + 1, m, h => by
    have h2 : m % 2 = 0 := Nat.mod_eq_zero_of_dvd (dvd_trans (dvd_pow_self 2 (by omega)) h)
    have hk : 2 ^ k ∣ m / 2 := Nat.dvd_div_of_mul_dvd (by rwa [← pow_succ'])
    rw [Function.iterate_succ_apply, show tstep m = m / 2 by simp [tstep, h2],
      tstep_iterate_of_dvd k (m / 2) hk, Nat.div_div_eq_div_mul, pow_succ, mul_comm]

/-- One Syracuse step is `ν₂(3N+1)` steps of `tstep`, for odd `N`. -/
theorem syr_eq_tstep_iterate {N : ℕ} (hN : N % 2 = 1) :
    syr N = tstep^[padicValNat 2 (3 * N + 1)] N := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv : 1 ≤ padicValNat 2 (3 * N + 1) :=
    one_le_padicValNat_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero (by omega))
  · obtain ⟨v, hv'⟩ : ∃ v, padicValNat 2 (3 * N + 1) = v + 1 := ⟨_, (Nat.sub_add_cancel hv).symm⟩
    have hdvd : 2 ^ (v + 1) ∣ 3 * N + 1 := hv' ▸ pow_padicValNat_dvd
    have hdvd' : 2 ^ v ∣ (3 * N + 1) / 2 := Nat.dvd_div_of_mul_dvd (by rwa [← pow_succ'])
    rw [hv', Function.iterate_succ_apply, show tstep N = (3 * N + 1) / 2 by
      simp [tstep, show N % 2 ≠ 0 by omega], tstep_iterate_of_dvd v _ hdvd',
      Nat.div_div_eq_div_mul, ← pow_succ', ← hv']
    rfl

/-- **The bridge.**  The `k`-th Syracuse iterate of an odd `N` is its `tstep` iterate at the letter
time `valSum N k`. -/
theorem syr_iterate_eq_tstep {N : ℕ} (hN : N % 2 = 1) (k : ℕ) :
    syr^[k] N = tstep^[valSum N k] N := by
  induction k with
  | zero => simp [valSum]
  | succ k ih =>
    rw [Function.iterate_succ_apply', syr_eq_tstep_iterate (syr_iterate_odd N k hN), ih,
      valSum_succ, ← Function.iterate_add_apply, ih, add_comm]

/-- Letter times add along the orbit. -/
theorem valSum_add (N a b : ℕ) : valSum N (a + b) = valSum N a + valSum (syr^[a] N) b := by
  unfold valSum
  rw [Finset.sum_range_add]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_comm a i, Function.iterate_add_apply]

/-- After an odd `M`, the orbit halves `3M + 1` until the Syracuse step. -/
theorem tstep_iterate_odd_eq {M : ℕ} (hM : M % 2 = 1) {e : ℕ} (he : 1 ≤ e)
    (hev : e ≤ padicValNat 2 (3 * M + 1)) : tstep^[e] M = (3 * M + 1) / 2 ^ e := by
  obtain ⟨d, rfl⟩ : ∃ d, e = d + 1 := ⟨e - 1, by omega⟩
  have hdvd : 2 ^ (d + 1) ∣ 3 * M + 1 :=
    dvd_trans (pow_dvd_pow 2 hev) pow_padicValNat_dvd
  have hdvd' : 2 ^ d ∣ (3 * M + 1) / 2 := Nat.dvd_div_of_mul_dvd (by rwa [← pow_succ'])
  rw [Function.iterate_succ_apply, show tstep M = (3 * M + 1) / 2 by
    simp [tstep, show M % 2 ≠ 0 by omega], tstep_iterate_of_dvd d _ hdvd',
    Nat.div_div_eq_div_mul, ← pow_succ']

/-- Between consecutive letter times the `tstep` orbit falls: for odd `N` and
`valSum N k < t ≤ valSum N (k + 1)`, the next Syracuse iterate is at most `tstep^[t] N`, and the
letters at `t, …, valSum N (k + 1) − 1` are `0`. -/
theorem tstep_between {N : ℕ} (hN : N % 2 = 1) {k t : ℕ} (h1 : valSum N k < t)
    (h2 : t ≤ valSum N (k + 1)) :
    syr^[k + 1] N ≤ tstep^[t] N ∧ ∀ i, t ≤ i → i < valSum N (k + 1) → accWord N i = false := by
  set M := syr^[k] N with hMdef
  have hM : M % 2 = 1 := syr_iterate_odd N k hN
  have hsM : tstep^[valSum N k] N = M := (syr_iterate_eq_tstep hN k).symm
  have hv := valSum_succ N k
  rw [← hMdef] at hv
  set v := padicValNat 2 (3 * M + 1) with hvdef
  have hat : ∀ e, 1 ≤ e → e ≤ v → tstep^[valSum N k + e] N = (3 * M + 1) / 2 ^ e := by
    intro e he hev
    rw [add_comm, Function.iterate_add_apply, hsM, tstep_iterate_odd_eq hM he hev]
  have hsyr : syr^[k + 1] N = (3 * M + 1) / 2 ^ v := by
    rw [Function.iterate_succ_apply', ← hMdef, syr, oddPart]
  obtain ⟨d, rfl⟩ : ∃ d, t = valSum N k + d := ⟨t - valSum N k, by omega⟩
  refine ⟨?_, fun i hi1 hi2 => ?_⟩
  · rw [hsyr, hat d (by omega) (by omega)]
    exact Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) (by omega)) (by positivity)
  · obtain ⟨e, rfl⟩ : ∃ e, i = valSum N k + e := ⟨i - valSum N k, by omega⟩
    have hdvd : 2 ^ (e + 1) ∣ 3 * M + 1 :=
      dvd_trans (pow_dvd_pow 2 (by omega)) pow_padicValNat_dvd
    obtain ⟨c, hc⟩ := hdvd
    simp only [accWord, hat e (by omega) (by omega), decide_eq_false_iff_not]
    rw [hc, pow_succ, mul_assoc, Nat.mul_div_cancel_left _ (by positivity)]
    omega

/-- The letter time of the first passage below `z`. -/
noncomputable def ltime (z N : ℕ) : ℕ := valSum N (passTime z N)

/-- On passage, the passage location is the `tstep` iterate at the letter time. -/
theorem passLoc_eq_tstep {z N : ℕ} (hN : N % 2 = 1) (h : passes z N) :
    passLoc z N = tstep^[ltime z N] N := by
  rw [passLoc, if_pos h, ltime, syr_iterate_eq_tstep hN]

/-! ## Passages compose -/

/-- **Passages compose.**  For `1 ≤ z' ≤ z`, passing below `z` and then below `z'` is passing below
`z'`, including off passage, where `passLoc = 1`. -/
theorem passLoc_passLoc {z z' : ℕ} (hz' : 1 ≤ z') (hzz : z' ≤ z) (N : ℕ) :
    passLoc z' (passLoc z N) = passLoc z' N := by
  have hone : passLoc z' 1 = 1 := by
    have hp : passes z' 1 := ⟨0, by simpa using hz'⟩
    have ht : passTime z' 1 = 0 := Nat.eq_zero_of_le_zero (Nat.sInf_le (by simpa using hz'))
    rw [passLoc, if_pos hp, ht]
    rfl
  by_cases h : passes z N
  · by_cases h' : passes z' N
    · have hT : passTime z N ≤ passTime z' N := passTime_anti hzz h'
      have := (passTime_stepback z' N (passTime z N) h' hT).2.2
      rw [show passLoc z N = syr^[passTime z N] N by rw [passLoc, if_pos h]]
      exact this
    · have hM : ¬ passes z' (passLoc z N) := by
        rintro ⟨i, hi⟩
        apply h'
        refine ⟨i + passTime z N, ?_⟩
        rw [show passLoc z N = syr^[passTime z N] N by rw [passLoc, if_pos h]] at hi
        rwa [Function.iterate_add_apply]
      rw [show passLoc z' (passLoc z N) = 1 by rw [passLoc, if_neg hM],
        show passLoc z' N = 1 by rw [passLoc, if_neg h']]
  · have h' : ¬ passes z' N := fun hp => h (passes_mono hzz hp)
    rw [show passLoc z N = 1 by rw [passLoc, if_neg h], hone,
      show passLoc z' N = 1 by rw [passLoc, if_neg h']]

/-- Passage times add: from `N` below `z`, then from the location below `z' ≤ z`. -/
theorem passes_passLoc {z z' N : ℕ} (hzz : z' ≤ z) (hN : N % 2 = 1) (h : passes z N)
    (h' : passes z' (passLoc z N)) :
    passes z' N ∧ ltime z' N = ltime z N + ltime z' (passLoc z N) := by
  have hloc : passLoc z N = syr^[passTime z N] N := by rw [passLoc, if_pos h]
  have hp : passes z' N := by
    obtain ⟨i, hi⟩ := h'
    refine ⟨i + passTime z N, ?_⟩
    rw [hloc] at hi
    rwa [Function.iterate_add_apply]
  refine ⟨hp, ?_⟩
  have hT : passTime z N ≤ passTime z' N := passTime_anti hzz hp
  have hsb := (passTime_stepback z' N (passTime z N) hp hT).2.1
  rw [ltime, ltime, ltime, hloc, hsb, ← valSum_add]
  congr 1
  omega

/-! ## One stage of descent -/

/-- **One stage.**  Let `M ≤ y` be odd and let the letter `1` have frequency within `1/100` on
every prefix of `M` with length in `[H, Λ]`.  If `Λ` covers `2 ⌈6 (log₂ y − log₂ z + 1)⌉ + 4 H`
and `Λ ≤ z`, then the orbit passes below `z` within `Λ` letters.

The descent: at most `0.51` of the letters are odd, so the height falls by `0.19` per letter while
it stays above `z` (the correction of the height identity is at most `Λ / (3 z ln 2) ≤ 1`).  The
passage location is the next odd height, which comes after a run of `0`s, and the prefix bounds
cap that run. -/
theorem stage_passes {M H Λ : ℕ} {y z : ℝ} (hM : M % 2 = 1) (hMy : (M : ℝ) ≤ y)
    (hz : 2 ≤ z) (hzy : z ≤ y)
    (hΛ : 2 * ⌈6 * (Real.logb 2 y - Real.logb 2 z + 1)⌉₊ + 4 * H ≤ Λ) (hΛz : (Λ : ℝ) ≤ z)
    (hgood : PrefGood [true] (1 / 100) H Λ M) :
    passes ⌊z⌋₊ M ∧ ltime ⌊z⌋₊ M ≤ Λ := by
  sorry

/-! ## Scales -/

/-- The scales `x_j = x^(α^(−j))`. -/
noncomputable def scale (x : ℝ) (j : ℕ) : ℝ := x ^ (alpha⁻¹ ^ j)

/-- The number of scales: `α^(−3000) < 1/20`. -/
def numScales : ℕ := 3000

/-- Consecutive scales: `x_(j+1)^α = x_j`. -/
theorem scale_succ_rpow {x : ℝ} (hx : 0 ≤ x) (j : ℕ) : scale x (j + 1) ^ alpha = scale x j := by
  have ha : alpha ≠ 0 := by norm_num [alpha]
  rw [scale, scale, ← Real.rpow_mul hx, pow_succ, mul_assoc, inv_mul_cancel₀ ha, mul_one]

/-! ## Reading off the orbit -/

/-- Good over the first `4.2 size n` letters: every prefix of length `T` with `5 T ≤ 21 size n`
has its count of `u` within `δ size n` of `T 2^(−|u|)`. -/
def GoodOdd (u : List Bool) (δ : ℝ) (n : ℕ) : Prop :=
  ∀ T : ℕ, 5 * T ≤ 21 * Nat.size n → |wdev u n 0 T| ≤ δ * Nat.size n

/-- **Reading off the orbit.**  For every `u` and `δ' > 0` there are `δ, η > 0` such that, for large
`x`, an odd start `n ∈ [x^α, x^(α²)]` that is good at scale `x`, and whose passage locations below
`x_j` are good at scale `x_j` for every `j < numScales`, is good over its first `4.2 size n`
letters.

The stretches between passages tile the letters, each a prefix of a passage location of length at
most `Λ`; short stretches cost at most `H` each.  The letter-`1` frequency keeps the height at time
`t` above `n 2^(−0.224 t)`, so the passage below `x_J ≤ n^(1/20)` comes after `4.25 log₂ n`
letters. -/
theorem goodOdd_of_stages (u : List Bool) {δ' : ℝ} (hδ' : 0 < δ') :
    ∃ δ η X₀ : ℝ, 0 < δ ∧ 0 < η ∧ η ≤ 1 / 1000 ∧ ∀ x : ℝ, X₀ ≤ x → ∀ n : ℕ, n % 2 = 1 →
      x ^ alpha ≤ n → (n : ℝ) ≤ x ^ alpha ^ 2 → ScaleGood u δ η x n →
      (∀ j < numScales, LocGood u δ η (scale x j) (passLoc ⌊scale x j⌋₊ n)) →
      GoodOdd u δ' n := by
  sorry

/-- **The location event from the start event.**  For large `x`, if an odd `N ≤ x^(α²)` is good
at scale `x`, its passage location below `x` is a good location at scale `x`. -/
theorem locGood_passLoc (u : List Bool) {δ η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 1000) :
    ∃ X₀ : ℝ, ∀ x : ℝ, X₀ ≤ x → ∀ N : ℕ, N % 2 = 1 → (N : ℝ) ≤ x ^ alpha ^ 2 →
      ScaleGood u δ η x N → LocGood u δ η x (passLoc ⌊x⌋₊ N) := by
  sorry

end CollatzMoonshot.Conjugacy
