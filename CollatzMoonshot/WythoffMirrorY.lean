/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.AmusicalTrap
import CollatzMoonshot.MonotonePotential
import CollatzMoonshot.WythoffGeneral
import CollatzMoonshot.WythoffSporadic

/-!
# Theorem Y′: the mirror of the sporadic cubic member

Research note `wythoff-classify`, §4.  Let `x ≈ 0.5259574806` be the real root of
`x³ + x² + 3x − 2` (`WythoffSporadic.yRoot`) and let `W′ = W_{β}` with `β = 2x ≈ 1.0519150`
(`betaY`), the mirror of Theorem Y's `W_α`, `α = 2x/(2x − 1) ≈ 20.26227` (`alphaY`).  Since
`β/(β − 1) = α`, `W′(2k) = ⌊2kx⌋` (`v ↦ ⌊xv⌋` on evens, a descent) and
`W′(2k − 1) = ⌈kα⌉ − 1` (`s ↦ ⌈A(s + 1)⌉ − 1`, `A = α/2`, an ascent).

1. **Recurrence** (`wy_betaY_iterate_four_eq`).  If `s` is odd and `W′(s), W′²(s), W′³(s)` are
   even, then `W′⁴(s) = 4(s + 1) + W′³(s) − W′²(s) − 1`, for every `s ∈ ℤ`.  The right side is
   odd, so after an odd point at most three even points follow (`exists_odd_iterate_Ym`).
2. **Classification** (Lemma P, `MonotonePotential`, with `S` = odds, `Φ = ∅`, `T = 4`).
   `W′` has **no finite orbit in `ℕ⁺`**; every orbit tends to `∞` both ways; its minimum is the
   unique odd `y` with `W′⁻¹(y), …, W′⁻⁴(y)` all even.
3. **Count.**  `#{minima ≤ X} + #{odd s ≤ X : R′(s) ≤ X} = ⌈X/2⌉` exactly, and
   `R′(s) ≥ 4s/3`, so `#{minima ≤ X} ≥ ⌈X/2⌉ − ⌊(3X + 4)/8⌋`: infinitely many infinite
   orbits.
4. **Density** (conditional on two-dimensional Weyl equidistribution): the same
   `d = 3/10 + x/8 + x²/10 ≈ 0.39340781` as Theorem Y (`WythoffSporadic.densityY`).

**Proof of the recurrence: Theorem M (main/mirror identity).**  For odd `s` put `m = s + 1`
(even), `v_i = W′^i(s)`, and the mirror phases (`ymF1`, `ymFeven`)
`a = (v_1 + 1) − Am ∈ [0, 1)` (`v_1 = ⌈Am⌉ − 1`) and, for even `v`,
`b(v) = (W′(v) + 1) − xv ∈ (0, 1]` (`W′(v) = ⌊xv⌋`).  Then `(−m; −v_1, −v_2, …)` obeys the
recurrences of Theorem Y's main run `(n; W(n) + 1, W²(n) + 1, …)` with the **same** phase
symbols: main `w_1 = An + 1 − f₁`, `w′ = xw + 1 − f(·)`; mirror `−v_1 = A(−m) + 1 − a`,
`−v′ = x(−v) + 1 − b(v)`.  Hence every phase identity of `WythoffSporadic` transfers verbatim
(`wy_betaY_iterate_three_phase`, `wy_betaY_iterate_four_phase`), with `(f₁, f₂, f₃, f₄)`
replaced by `(a, b(v_1), b(v_2), b(v_3))`, which lie in the same box `[0, 1) × (0, 1]³`.  So the
polygon lemmas `yPhase3_mem`, `yPhase4_of_one`, `yPhase4_of_neg_one`, `yPhase4_sub` apply
unchanged, and Theorem Y's recurrence `w_4 = 4n + w_3 − w_2 + 1` becomes
`−v_4 = −4m − v_3 + v_2 + 1`.  The run laws, `J = 3` and the return slopes `c_j = A xʲ` agree
with Theorem Y's.

**(H2).**  The mirror sandwich: `v_1 ≥ A(s + 1) − 1`, `v_{i+1} > x v_i − 1`, so
`W′^{j+1}(s) > c_j(s + 1) − (1 + x + ⋯ + xʲ) ≥ 1.474(s + 1) − 1.95 ≥ 4s/3` for `s ≥ 5`; `s = 1, 3`
directly (`W′(1) = 20, W′(20) = 10, W′(10) = 5`; `W′(3) = 40, W′(40) = 21`).  Measured:
`min R′(s)/s = 1.4731` at `s = 93`.

Truth checks: `tmp/drafter-classify/check.py` (certified 400-bit interval arithmetic; census
786 810 minima `≤ 2·10⁶`, the research note's number; 4-level test = brute force on
`y ≤ 2·10⁴`, the 3-level test fails).
-/

namespace CollatzMoonshot.WythoffMirrorY

open CollatzMoonshot.WythoffGeneral CollatzMoonshot.MonotonePotential
open CollatzMoonshot.WythoffSporadic
open CollatzMoonshot.AmusicalTrap (permOrbit InfinitelyManyInfiniteOrbits)
open Filter Topology

/-! ## The mirror parameter -/

/-- **(proved).**  `β = 2x > 1` (`yRoot_spec`). -/
theorem one_lt_betaY : 1 < betaY := by
  unfold betaY; linarith [yRoot_spec.1]

/-- **(proved).**  `β < 2`. -/
theorem betaY_lt_two : betaY < 2 := by
  unfold betaY; linarith [yRoot_spec.2.1]

/-- **(proved).**  `β/(β − 1) = α` (definitional). -/
theorem betaY_div_sub_one : betaY / (betaY - 1) = alphaY := by
  unfold betaY alphaY; rfl

/-- `W_β` for Theorem Y′, as a permutation of `ℤ`. -/
noncomputable def ymPerm : Equiv.Perm ℤ :=
  wyPerm betaY one_lt_betaY

theorem ymPerm_apply (n : ℤ) : ymPerm n = wy betaY n := rfl

/-! ## The mirror phases -/

/-- The first (ascending) mirror phase `a = (W′(s) + 1) − (α/2)(s + 1)` (in `[0, 1)` for odd
`s`); it plays the role of `yF1`. -/
noncomputable def ymF1 (s : ℤ) : ℝ :=
  (wy betaY s : ℝ) + 1 - alphaY / 2 * ((s : ℝ) + 1)

/-- The descending mirror phase `b(v) = (W′(v) + 1) − xv` (in `(0, 1]` for even `v`); it plays
the role of `yFodd`. -/
noncomputable def ymFeven (v : ℤ) : ℝ :=
  (wy betaY v : ℝ) + 1 - yRoot * v

/-- **(proved).**  For odd `s`, `0 ≤ a < 1`.  Paper proof: `s = 2k − 1`,
`W′(s) = ⌈kα⌉ − 1` (`wy_two_mul_sub_one`, `betaY_div_sub_one`) and `(α/2)(s + 1) = kα`;
`Int.le_ceil`, `Int.ceil_lt_add_one`. -/
theorem ymF1_mem {s : ℤ} (hs : s % 2 = 1) : 0 ≤ ymF1 s ∧ ymF1 s < 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, s = 2 * k - 1 := ⟨(s + 1) / 2, by omega⟩
  unfold ymF1
  rw [wy_two_mul_sub_one, betaY_div_sub_one]
  have e : alphaY / 2 * (((2 * k - 1 : ℤ) : ℝ) + 1) = k * alphaY := by push_cast; ring
  rw [e]; push_cast
  constructor
  · linarith [Int.le_ceil ((k : ℝ) * alphaY)]
  · linarith [Int.ceil_lt_add_one ((k : ℝ) * alphaY)]

/-- **(proved).**  For even `v`, `0 < b(v) ≤ 1` (`W′(2k) = ⌊2kx⌋`, `Int.floor_le`,
`Int.lt_floor_add_one`). -/
theorem ymFeven_mem {v : ℤ} (hv : v % 2 = 0) : 0 < ymFeven v ∧ ymFeven v ≤ 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, v = 2 * k := ⟨v / 2, by omega⟩
  unfold ymFeven
  rw [wy_two_mul]
  have e : yRoot * ((2 * k : ℤ) : ℝ) = k * betaY := by unfold betaY; push_cast; ring
  rw [e]
  constructor
  · linarith [Int.lt_floor_add_one ((k : ℝ) * betaY)]
  · linarith [Int.floor_le ((k : ℝ) * betaY)]

/-! ## Theorem Y′ (1): the recurrence on `O E³` -/

/-- **(proved; algebra, any parities).**  For odd `s`:
`W′³ = −2(s + 1) + W′ − W′² − 1 − Δ′(a, b(W′ s)) + b(W′² s)`.  Paper proof: Theorem M (module
docstring) applied to `wy_iterate_three_phase`; directly, unfold and `linear_combination` with
`g_mul_alphaY` (`(1 − x − x²) α = 4`), exactly as there. -/
theorem wy_betaY_iterate_three_phase {s : ℤ} (hs : s % 2 = 1) :
    (((wy betaY)^[3] s : ℤ) : ℝ) =
      -2 * ((s : ℝ) + 1) + wy betaY s - (wy betaY)^[2] s - 1 -
        yPhase3 (ymF1 s) (ymFeven (wy betaY s)) + ymFeven ((wy betaY)^[2] s) := by
  have _ := hs  -- the identity holds for every `s`
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  unfold ymF1 ymFeven yPhase3
  linear_combination (-(((s : ℝ) + 1) / 2)) * g_mul_alphaY

/-- **(proved; algebra, any parities).**  For odd `s`:
`W′⁴ = 2(s + 1) + W′ − 2W′² − 4 + g a + (2 + x²) b₂ + x b₃ + b₄` with `b_i` the descending phases
at `W′ s, W′² s, W′³ s` and `g = 1 − x − x²`.  Paper proof: Theorem M applied to
`wy_iterate_four_phase` (`linear_combination` with `g_mul_alphaY` and the cubic). -/
theorem wy_betaY_iterate_four_phase {s : ℤ} (hs : s % 2 = 1) :
    (((wy betaY)^[4] s : ℤ) : ℝ) =
      2 * ((s : ℝ) + 1) + wy betaY s - 2 * (wy betaY)^[2] s - 4 +
        (1 - yRoot - yRoot ^ 2) * ymF1 s + (2 + yRoot ^ 2) * ymFeven (wy betaY s) +
        yRoot * ymFeven ((wy betaY)^[2] s) + ymFeven ((wy betaY)^[3] s) := by
  have _ := hs  -- the identity holds for every `s`
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  unfold ymF1 ymFeven
  linear_combination (((s : ℝ) + 1) / 2) * g_mul_alphaY + (wy betaY s : ℝ) * yRoot_spec.2.2

/-- **(proved).**  On `O E E`, `W′³(s) − (−2(s + 1) + W′(s) − W′²(s) − 1) ∈ {−1, 0, 1}`,
for every `s ∈ ℤ`.  Paper proof: it is the integer `b(W′² s) − Δ′`, with `Δ′ ∈ (−1, 2)`
(`yPhase3_mem`, `ymF1_mem`, `ymFeven_mem`) and `b ∈ (0, 1]`. -/
theorem wy_betaY_iterate_three_sub_mem {s : ℤ} (hs : s % 2 = 1) (h₁ : wy betaY s % 2 = 0)
    (h₂ : (wy betaY)^[2] s % 2 = 0) :
    (wy betaY)^[3] s - (-2 * (s + 1) + wy betaY s - (wy betaY)^[2] s - 1) ∈
      ({-1, 0, 1} : Set ℤ) := by
  have hph := wy_betaY_iterate_three_phase hs
  obtain ⟨a1, a2⟩ := ymF1_mem hs
  obtain ⟨b1, b2⟩ := ymFeven_mem h₁
  obtain ⟨c1, c2⟩ := ymFeven_mem h₂
  obtain ⟨d1, d2⟩ := yPhase3_mem a1 a2.le b1.le b2
  have hlo : ((-2 : ℤ) : ℝ) <
      (((wy betaY)^[3] s - (-2 * (s + 1) + wy betaY s - (wy betaY)^[2] s - 1) : ℤ) : ℝ) := by
    push_cast; linarith
  have hhi : (((wy betaY)^[3] s - (-2 * (s + 1) + wy betaY s - (wy betaY)^[2] s - 1) : ℤ) : ℝ) <
      ((2 : ℤ) : ℝ) := by
    push_cast; linarith
  have hlo' := Int.cast_lt.1 hlo
  have hhi' := Int.cast_lt.1 hhi
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-- **(proved; Theorem Y′ (1)).**  If `s` is odd and `W′(s), W′²(s), W′³(s)` are even,
then `W′⁴(s) = 4(s + 1) + W′³(s) − W′²(s) − 1`; for every `s ∈ ℤ`.  Paper proof: as
`wy_iterate_four_eq`.  `t := Δ′(a, b₂) − b₃ = −(W′³ − (−2(s + 1) + W′ − W′² − 1))`
(`wy_betaY_iterate_three_phase`) is odd (`W′, W′², s + 1` even, `W′³` even), so `t = ±1`
(`wy_betaY_iterate_three_sub_mem`).  `u := W′⁴ − (2(s + 1) + W′ − 2W′² − 4) = 2 − Δ_t + b₄`
(`wy_betaY_iterate_four_phase`, `yPhase4_sub` with `b₃ = Δ′ − t`).  `t = 1`: `Δ′ ≥ 1`,
`Δ_1 ∈ (1, 2)` (`yPhase4_of_one`), `u = 1`; `t = −1`: `Δ′ ≤ 0`, `a < 1`, `Δ_{−1} ∈ (−1, 0)`
(`yPhase4_of_neg_one`), `u = 3`.  So `u = 2 − t`; eliminate `t`.  (Main/mirror dictionary:
`n ↦ −(s + 1)`, `W^i n + 1 ↦ −W′^i s`, `(f₁, f(·)) ↦ (a, b(·))`.) -/
theorem wy_betaY_iterate_four_eq {s : ℤ} (hs : s % 2 = 1)
    (heven : ∀ i : ℕ, 1 ≤ i → i ≤ 3 → (wy betaY)^[i] s % 2 = 0) :
    (wy betaY)^[4] s = 4 * (s + 1) + (wy betaY)^[3] s - (wy betaY)^[2] s - 1 := by
  have o1 := heven 1 le_rfl (by norm_num)
  have o2 := heven 2 (by norm_num) (by norm_num)
  have o3 := heven 3 (by norm_num) le_rfl
  rw [Function.iterate_one] at o1
  have ht := wy_betaY_iterate_three_sub_mem hs o1 o2
  have hph3 := wy_betaY_iterate_three_phase hs
  have hph4 := wy_betaY_iterate_four_phase hs
  obtain ⟨a1, a2⟩ := ymF1_mem hs
  obtain ⟨b1, b2⟩ := ymFeven_mem o1
  obtain ⟨c1, c2⟩ := ymFeven_mem o2
  obtain ⟨e1, e2⟩ := ymFeven_mem o3
  set t : ℤ := (wy betaY)^[3] s - (-2 * (s + 1) + wy betaY s - (wy betaY)^[2] s - 1) with ht_def
  have hf3 : ymFeven ((wy betaY)^[2] s) =
      yPhase3 (ymF1 s) (ymFeven (wy betaY s)) - ((-t : ℤ) : ℝ) := by
    rw [ht_def]; push_cast; linarith
  have hu : ((((wy betaY)^[4] s - (2 * (s + 1) + wy betaY s - 2 * (wy betaY)^[2] s - 4)) : ℤ) :
      ℝ) = 2 - yPhase4 (-t) (ymF1 s) (ymFeven (wy betaY s)) + ymFeven ((wy betaY)^[3] s) := by
    rw [← yPhase4_sub, ← hf3]; push_cast; linarith
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
  rcases ht with h | h | h
  · -- `t = −1`, `τ = 1`
    rw [h] at hf3 hu
    obtain ⟨p1, p2⟩ := yPhase4_of_one a1 a2.le b1.le b2 (by push_cast at hf3; linarith)
    have hlo : ((0 : ℤ) : ℝ) <
        ((((wy betaY)^[4] s - (2 * (s + 1) + wy betaY s - 2 * (wy betaY)^[2] s - 4)) : ℤ) :
          ℝ) := by
      rw [hu]; push_cast; linarith
    have hhi : ((((wy betaY)^[4] s - (2 * (s + 1) + wy betaY s - 2 * (wy betaY)^[2] s - 4)) :
        ℤ) : ℝ) < ((2 : ℤ) : ℝ) := by
      rw [hu]; push_cast; linarith
    have := Int.cast_lt.1 hlo
    have := Int.cast_lt.1 hhi
    omega
  · omega
  · -- `t = 1`, `τ = −1`
    rw [h] at hf3 hu
    obtain ⟨p1, p2⟩ := yPhase4_of_neg_one a1 a2 b1.le b2 (by push_cast at hf3; linarith)
    have hlo : ((2 : ℤ) : ℝ) <
        ((((wy betaY)^[4] s - (2 * (s + 1) + wy betaY s - 2 * (wy betaY)^[2] s - 4)) : ℤ) :
          ℝ) := by
      rw [hu]; push_cast; linarith
    have hhi : ((((wy betaY)^[4] s - (2 * (s + 1) + wy betaY s - 2 * (wy betaY)^[2] s - 4)) :
        ℤ) : ℝ) < ((4 : ℤ) : ℝ) := by
      rw [hu]; push_cast; linarith
    have := Int.cast_lt.1 hlo
    have := Int.cast_lt.1 hhi
    omega

/-- **(proved; Theorem Y′ (1), runs).**  After an odd point at most three even points
follow: some `W′^{j+1}(s)`, `j ≤ 3`, is odd.  Paper proof: `wy_betaY_iterate_four_eq`. -/
theorem exists_odd_iterate_Ym {s : ℤ} (hs : s % 2 = 1) :
    ∃ j ≤ 3, (wy betaY)^[j + 1] s % 2 = 1 := by
  by_contra hne
  push Not at hne
  have heven : ∀ i : ℕ, 1 ≤ i → i ≤ 3 → (wy betaY)^[i] s % 2 = 0 := by
    intro i hi1 hi3
    have := hne (i - 1) (by omega)
    rw [show i - 1 + 1 = i by omega] at this
    omega
  have h4 := wy_betaY_iterate_four_eq hs heven
  have h5 : (wy betaY)^[4] s % 2 ≠ 1 := hne 3 le_rfl
  have e2 := heven 2 (by norm_num) (by norm_num)
  have e3 := heven 3 (by norm_num) le_rfl
  omega

/-- **(proved).**  Evaluating `W′` on an even point from a floor bracket (`W′(u) = ⌊xu⌋`). -/
theorem ymEvenEval {u w : ℤ} (hu : u % 2 = 0) (h1 : (w : ℝ) ≤ yRoot * u)
    (h2 : yRoot * u < w + 1) : wy betaY u = w := by
  obtain ⟨k, rfl⟩ : ∃ k, u = 2 * k := ⟨u / 2, by omega⟩
  rw [wy_two_mul, Int.floor_eq_iff]
  unfold betaY
  push_cast at h1 h2
  constructor <;> linarith

/-- **(proved).**  Evaluating `W′` on an odd point (`W′(u) + 1 = ⌈A(u + 1)⌉`). -/
theorem ymOddEval {u w : ℤ} (hu : u % 2 = 1) (h1 : (w : ℝ) < alphaY / 2 * (u + 1))
    (h2 : alphaY / 2 * (u + 1) ≤ w + 1) : wy betaY u = w := by
  obtain ⟨k, rfl⟩ : ∃ k, u = 2 * k - 1 := ⟨(u + 1) / 2, by omega⟩
  rw [wy_two_mul_sub_one, betaY_div_sub_one]
  have : ⌈(k : ℝ) * alphaY⌉ = w + 1 := by
    rw [Int.ceil_eq_iff]; push_cast at h1 h2 ⊢; constructor <;> linarith
  omega

/-- **(proved; the (H2) input).**  For `s > 0` odd, `j ≤ 3`, and `W′(s), …, W′ʲ(s)` even:
`4s ≤ 3·W′^{j+1}(s)`.  Paper proof: module docstring (mirror sandwich; `s ∈ {1, 3}` by direct
evaluation with `yRoot_bounds`, `alphaY_bounds`). -/
theorem le_wy_betaY_iterate_of_even_run {s : ℤ} (hs0 : 0 < s) (hs : s % 2 = 1) {j : ℕ}
    (hj : j ≤ 3) (heven : ∀ i : ℕ, 1 ≤ i → i ≤ j → (wy betaY)^[i] s % 2 = 0) :
    4 * s ≤ 3 * (wy betaY)^[j + 1] s := by
  have hx := yRoot_bounds
  have hα := alphaY_bounds
  rcases (show s = 1 ∨ s = 3 ∨ 5 ≤ s by omega) with rfl | rfl | hs5
  · have e1 : wy betaY 1 = 20 := ymOddEval (by norm_num) (by push_cast; linarith)
      (by push_cast; linarith)
    have e2 : wy betaY 20 = 10 := ymEvenEval (by norm_num) (by push_cast; linarith)
      (by push_cast; linarith)
    have e3 : wy betaY 10 = 5 := ymEvenEval (by norm_num) (by push_cast; linarith)
      (by push_cast; linarith)
    interval_cases j
    · simp [e1]
    · simp [Function.iterate_succ_apply', e1, e2]
    · simp [Function.iterate_succ_apply', e1, e2, e3]
    · have := heven 3 (by norm_num) le_rfl
      simp [Function.iterate_succ_apply', e1, e2, e3] at this
  · have e1 : wy betaY 3 = 40 := ymOddEval (by norm_num) (by push_cast; linarith)
      (by push_cast; linarith)
    have e2 : wy betaY 40 = 21 := ymEvenEval (by norm_num) (by push_cast; linarith)
      (by push_cast; linarith)
    interval_cases j
    · simp [e1]
    · simp [Function.iterate_succ_apply', e1, e2]
    · have := heven 2 (by norm_num) le_rfl
      simp [Function.iterate_succ_apply', e1, e2] at this
    · have := heven 2 (by norm_num) (by norm_num)
      simp [Function.iterate_succ_apply', e1, e2] at this
  · have hK : ∀ i : ℕ, i ≤ j → yRoot ^ i * (alphaY / 2 * ((s : ℝ) + 1) + 6 / 5) ≤
        ((wy betaY)^[i + 1] s : ℝ) + 11 / 5 := by
      intro i
      induction i with
      | zero =>
        intro _
        have := (ymF1_mem hs).1; unfold ymF1 at this
        simp only [pow_zero, one_mul, zero_add, Function.iterate_one]; linarith
      | succ i ih =>
        intro hi
        have h1 := ih (by omega)
        have h2 := (ymFeven_mem (heven (i + 1) (by omega) hi)).1
        unfold ymFeven at h2
        rw [Function.iterate_succ_apply' _ (i + 1)]
        calc yRoot ^ (i + 1) * (alphaY / 2 * ((s : ℝ) + 1) + 6 / 5)
            = yRoot * (yRoot ^ i * (alphaY / 2 * ((s : ℝ) + 1) + 6 / 5)) := by ring
          _ ≤ yRoot * (((wy betaY)^[i + 1] s : ℝ) + 11 / 5) :=
            mul_le_mul_of_nonneg_left h1 (by linarith)
          _ ≤ _ := by nlinarith
    have hfin := hK j le_rfl
    have hs5' : (5 : ℝ) ≤ s := by exact_mod_cast hs5
    have hx3 : (1454 : ℝ) / 10000 < yRoot ^ 3 := by
      have : ((52595748 : ℝ) / 10 ^ 8) ^ 3 < yRoot ^ 3 :=
        pow_lt_pow_left₀ hx.1 (by norm_num) (by norm_num)
      norm_num at this ⊢; linarith
    have hxj : yRoot ^ 3 ≤ yRoot ^ j :=
      pow_le_pow_of_le_one (by linarith) (by linarith) (by omega)
    have hprod : (1454 : ℝ) / 10000 * (2026 / 200 * ((s : ℝ) + 1) + 6 / 5) ≤
        yRoot ^ j * (alphaY / 2 * ((s : ℝ) + 1) + 6 / 5) := by
      apply mul_le_mul (hx3.le.trans hxj) _ (by positivity) (pow_nonneg (by linarith) _)
      nlinarith
    suffices key : ((4 * s : ℤ) : ℝ) ≤ ((3 * (wy betaY)^[j + 1] s : ℤ) : ℝ) from
      Int.cast_le.1 key
    push_cast
    nlinarith

/-! ## Theorem Y′ (2)-(4): classification, count, density -/

theorem ymPerm_pow_apply (i : ℕ) (s : ℤ) : (ymPerm ^ i) s = (wy betaY)^[i] s := by
  rw [Equiv.Perm.coe_pow]; rfl

/-- **(proved; Theorem Y′ (2)).**  Lemma P applies with `S` = odds, `Φ = ∅`, `T = 4`.
Paper proof: `pos_iff` is `wy_pos_iff`; `mem_fix_iff` is trivial; (H1) is `wy_lt_of_even`
(`β < 2`); (H2): by `exists_odd_iterate_Ym` the first return word is `O Eʲ`, `j ≤ 3`
(`Nat.find`), and `R′(s) ≥ 4s/3 > s` by `le_wy_betaY_iterate_of_even_run`. -/
theorem hyp_ymPerm : Hyp ymPerm {n | n % 2 = 1} ∅ 4 := by
  refine ⟨fun n => wy_pos_iff one_lt_betaY n, fun z => by simp only [Set.mem_empty_iff_false],
    fun z hz hzS _ => ?_, fun s hs hs0 _ => ?_⟩
  · simp only [Set.mem_ofPred_eq] at hzS
    rw [ymPerm_apply]
    exact wy_lt_of_even betaY_lt_two hz (by omega)
  · simp only [Set.mem_ofPred_eq] at hs
    have hex := exists_odd_iterate_Ym hs
    classical
    have hj : Nat.find hex ≤ 3 ∧ (wy betaY)^[Nat.find hex + 1] s % 2 = 1 := Nat.find_spec hex
    have heven : ∀ i : ℕ, 1 ≤ i → i ≤ Nat.find hex → (wy betaY)^[i] s % 2 = 0 := by
      intro i hi1 hij
      have := Nat.find_min hex (show i - 1 < Nat.find hex by omega)
      rw [show i - 1 + 1 = i by omega] at this
      omega
    have hrun := le_wy_betaY_iterate_of_even_run hs0 hs hj.1 heven
    refine ⟨Nat.find hex + 1, by omega, by omega, ?_, ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq, ymPerm_pow_apply]; exact hj.2
    · rw [ymPerm_pow_apply]; omega
    · intro i hi1 hi2
      simp only [Set.mem_ofPred_eq, ymPerm_pow_apply]
      have := heven i hi1 (by omega); omega

/-- **(proved).**  The first return to the odds at least multiplies by `4/3`. -/
theorem returnMap_ymPerm_ge {s : ℤ} (hs0 : 0 < s) (hs : s % 2 = 1) :
    4 * s ≤ 3 * returnMap ymPerm {n | n % 2 = 1} s := by
  obtain ⟨h1, h2, -, -, h5⟩ :=
    returnTime_spec hyp_ymPerm (show s ∈ {n : ℤ | n % 2 = 1} from hs) hs0 (Set.notMem_empty s)
  unfold returnMap
  rw [ymPerm_pow_apply]
  obtain ⟨j, hj⟩ : ∃ j, returnTime ymPerm {n | n % 2 = 1} s = j + 1 :=
    ⟨returnTime ymPerm {n | n % 2 = 1} s - 1, by omega⟩
  rw [hj] at h2 h5 ⊢
  apply le_wy_betaY_iterate_of_even_run hs0 hs (by omega)
  intro i hi1 hij
  have := h5 i hi1 (by omega)
  simp only [Set.mem_ofPred_eq, ymPerm_pow_apply] at this
  omega

/-- **(proved from `hyp_ymPerm`; Theorem Y′ (2)).**  No finite orbit in `ℕ⁺`
(`permOrbit_infinite`). -/
theorem permOrbit_ymPerm_infinite {x : ℤ} (hx : 0 < x) : (permOrbit ymPerm x).Infinite := by
  exact permOrbit_infinite hyp_ymPerm hx (Set.notMem_empty x)

/-- **(proved from `hyp_ymPerm`; Theorem Y′ (2), forward escape).** -/
theorem tendsto_ymPerm_pow {x : ℤ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => (ymPerm ^ n) x) atTop atTop :=
  tendsto_pow hyp_ymPerm hx (Set.notMem_empty x)

/-- **(proved from `hyp_ymPerm`; Theorem Y′ (2), backward escape).** -/
theorem tendsto_ymPerm_pow_neg {x : ℤ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => (ymPerm ^ (-(n : ℤ))) x) atTop atTop :=
  tendsto_pow_neg hyp_ymPerm hx (Set.notMem_empty x)

/-- **(proved; Theorem Y′ (2), minima).**  For `x > 0`: `x` is the minimum of its orbit
iff `x` is odd and its four predecessors are even (`isOrbitMin_iff`, `T = 4`).  (Three
predecessors do not suffice: 592 mismatches with brute force for `y ≤ 2·10⁴`.) -/
theorem isOrbitMin_ymPerm_iff {x : ℤ} (hx : 0 < x) :
    IsOrbitMin ymPerm x ↔
      x % 2 = 1 ∧ ∀ i : ℕ, 1 ≤ i → i ≤ 4 → (ymPerm ^ (-(i : ℤ))) x % 2 = 0 := by
  rw [isOrbitMin_iff hyp_ymPerm hx (Set.notMem_empty x)]
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun i a b => by have := h2 i a b; omega⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun i a b => by have := h2 i a b; omega⟩

/-- There are `⌈X/2⌉` odd integers in `[1, X]`. -/
lemma ym_card_filter_odd (X : ℕ) :
    ((Finset.Icc (1 : ℤ) X).filter fun y => y % 2 = 1).card = (X + 1) / 2 := by
  rw [show (X + 1) / 2 = (Finset.Icc 1 ((X + 1) / 2)).card by simp]
  symm
  apply Finset.card_nbij (fun j : ℕ => 2 * (j : ℤ) - 1)
  · intro j hj
    simp only [Finset.coe_Icc, Set.mem_Icc, Finset.coe_filter, Finset.mem_Icc,
      Set.mem_ofPred_eq] at hj ⊢
    omega
  · intro a _ b _ h
    have : (a : ℤ) = b := by simp only at h; omega
    exact_mod_cast this
  · intro y hy
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hy
    refine ⟨((y + 1) / 2).toNat, ?_, ?_⟩
    · simp only [Finset.coe_Icc, Set.mem_Icc]; omega
    · simp only; omega

/-- **(proved; Theorem Y′ (3), exact count).**
`#{minima ≤ X} + #{odd s ∈ [1, X] : R′(s) ≤ X} = ⌈X/2⌉` (no `Φ` term).  Paper proof:
`minCount_add_returnCount` with `Φ = ∅`, as `WythoffLine.minCount_gmPerm_add`. -/
theorem minCount_ymPerm_add (X : ℕ) :
    minCount ymPerm X + returnCount ymPerm {n | n % 2 = 1} ∅ X = (X + 1) / 2 := by
  classical
  rw [minCount_add_returnCount hyp_ymPerm (fun z hz => absurd hz (Set.notMem_empty z)) X]
  have h0 : setCount (∅ : Set ℤ) X = 0 := by unfold setCount; simp
  have h1 : setCount ({n : ℤ | n % 2 = 1} \ ∅) X = (X + 1) / 2 := by
    unfold setCount
    rw [← ym_card_filter_odd X]
    congr 1
    ext y
    simp only [Finset.mem_filter, Set.mem_sdiff, Set.mem_ofPred_eq, Set.notMem_empty,
      not_false_eq_true, and_true]
  rw [h0, h1, zero_add]

/-- **(proved; Theorem Y′ (3), unconditional lower bound).**
`#{minima ≤ X} ≥ ⌈X/2⌉ − ⌊(3X + 4)/8⌋`.  Paper proof: `R′(s) ≤ X` forces `4s ≤ 3X`
(`returnMap_ymPerm_ge`), and there are at most `⌊(3X + 4)/8⌋` odd `s ≥ 1` with `4s ≤ 3X`. -/
theorem minCount_ymPerm_ge (X : ℕ) :
    ((X : ℤ) + 1) / 2 - (3 * (X : ℤ) + 4) / 8 ≤ minCount ymPerm X := by
  classical
  have hadd := minCount_ymPerm_add X
  have hle : returnCount ymPerm {n | n % 2 = 1} ∅ X ≤ (3 * X + 4) / 8 := by
    unfold returnCount
    calc _ ≤ ((Finset.Icc 1 ((3 * X + 4) / 8)).image fun k : ℕ => 2 * (k : ℤ) - 1).card := by
          apply Finset.card_le_card
          intro s hs
          simp only [Finset.mem_filter, Finset.mem_Icc, Set.mem_ofPred_eq, Set.notMem_empty,
            not_false_eq_true, true_and, Finset.mem_image] at hs ⊢
          obtain ⟨⟨h1, h2⟩, hso, hR⟩ := hs
          have hge := returnMap_ymPerm_ge (by omega) hso
          refine ⟨((s + 1) / 2).toNat, ⟨by omega, ?_⟩, by omega⟩
          have : ((((s + 1) / 2).toNat : ℕ) : ℤ) ≤ ((3 * X + 4) / 8 : ℕ) := by
            push_cast; omega
          exact_mod_cast this
      _ ≤ _ := Finset.card_image_le.trans (by simp)
  have c3 : (((X + 1) / 2 : ℕ) : ℤ) = ((X : ℤ) + 1) / 2 := by
    rw [Int.natCast_div]; push_cast; ring
  have c2 : (((3 * X + 4) / 8 : ℕ) : ℤ) = (3 * (X : ℤ) + 4) / 8 := by
    rw [Int.natCast_div]; push_cast; ring
  rw [← c2, ← c3]
  omega

/-- **(proved; Theorem Y′ (2)).**  Infinitely many infinite orbits.  Paper proof:
`minCount_ymPerm_ge` is unbounded; `infinitelyManyInfiniteOrbits_of_minima`. -/
theorem ymPerm_infinitelyManyInfiniteOrbits : InfinitelyManyInfiniteOrbits ymPerm := by
  apply infinitelyManyInfiniteOrbits_of_minima hyp_ymPerm
  by_contra hfin
  rw [Set.not_infinite] at hfin
  classical
  obtain ⟨c, hc⟩ : ∃ c, hfin.toFinset.card = c := ⟨_, rfl⟩
  have hge := minCount_ymPerm_ge (8 * (c + 2))
  have hle : minCount ymPerm (8 * (c + 2)) ≤ c := by
    unfold minCount
    calc _ ≤ hfin.toFinset.card := by
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_filter, Finset.mem_Icc, Set.Finite.mem_toFinset,
            Set.mem_ofPred_eq] at hx ⊢
          exact ⟨by omega, Set.notMem_empty x, hx.2⟩
      _ = c := hc
  push_cast at hge
  omega

/-- **(drafted, 88%; Theorem Y′ (4), density, conditional).**  Assuming multidimensional Weyl
equidistribution, the orbit minima have Theorem Y's density
`d = 3/10 + x/8 + x²/10 ≈ 0.39340781`.  Paper proof: by `minCount_ymPerm_add`,
`d = 1/2 − (1/2) Σ_{j ≤ 3} P′_j / c_j`, with `P′_j` the density among the odds of the return
word `O Eʲ` and `R′(s) = c_j (s + 1) + O(1)` (the mirror sandwich).  For `s = 2k − 1`,
`m = 2k` and the run phases are `({k c_0}, {k c_1})`, `c_0 = α/2`, `c_1 = xα/2`, Theorem Y's
torus coordinates (`yc0`, `yc1`); by Theorem M the cylinders `O Eʲ` are Theorem Y's cylinders
`E Oʲ` under the phase map `(a, b) ↦ (f₁, f₂)` (same box, same polygons `R_a`, `R_b`), so
`P′ = P = (1/2, 1/4, 1/(4(1 + x)), x/(4(1 + x)))`, the slopes agree, and the sum is
`densityY_sum_eq`.  (Census: 786 810 minima `≤ 2·10⁶`, `dX = 786 815.6`.) -/
theorem tendsto_minCount_ymPerm (hW : WeylEquidistributionMulti) :
    Tendsto (fun X : ℕ => (minCount ymPerm X : ℝ) / X) atTop (𝓝 densityY) := by
  sorry

end CollatzMoonshot.WythoffMirrorY
