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

/-! ### Theorem Y′ (4): the density

The involution `σ(m) = −m − 1` conjugates `W′ = σ ∘ W ∘ σ` exactly (`wy_betaY_eq_neg`; Theorem M
as an identity of maps).  So the return word `O Eʲ` of `s = 2k − 1` under `W′` is the return word
`E Oʲ` of `−2k` under Theorem Y's `W`, which Theorem Y reads off the phase of `−k`
(`yPhZ_mem_yWord`, valid for every integer).  The phase of `−k` is the Weyl sequence of the
frequencies `−(c₀, c₁)` (`ymPh`), still `ℚ`-independent of `1`, with Theorem Y's cylinders
`yWord j` and areas `yVol j`; Theorem Y's sandwich at `−2k` gives `|R′(s) − αxʲk| < 3`. -/

/-- **(proved; Theorem M as an identity of maps, every member).**  For `α > 1`, the mirror
`W_β`, `β = α/(α − 1)`, is conjugate to `W_α` by the involution `σ(m) = −m − 1`:
`W_β(n) = −W_α(−n − 1) − 1` for every `n ∈ ℤ` (`⌈−y⌉ = −⌊y⌋`). -/
theorem wy_mirror_eq_neg {α : ℝ} (hα : 1 < α) (n : ℤ) :
    wy (α / (α - 1)) n = -wy α (-n - 1) - 1 := by
  have hβ : α / (α - 1) / (α / (α - 1) - 1) = α := by
    have : α - 1 ≠ 0 := by linarith
    field_simp
    ring
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
    rw [wy_two_mul, show -(2 * k) - 1 = 2 * (-k) - 1 by ring, wy_two_mul_sub_one]
    push_cast
    rw [neg_mul, Int.ceil_neg]
    omega
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k - 1 := ⟨(n + 1) / 2, by omega⟩
    rw [wy_two_mul_sub_one, hβ, show -(2 * k - 1) - 1 = 2 * (-k) by ring, wy_two_mul]
    push_cast
    rw [neg_mul, Int.floor_neg]
    omega
/-- The involution `σ(m) = −m − 1` conjugates: `W′(n) = −W(−n − 1) − 1`. -/
theorem wy_betaY_eq_neg (n : ℤ) : wy betaY n = -wy alphaY (-n - 1) - 1 := by
  rw [← alphaY_div_sub_one]; exact wy_mirror_eq_neg one_lt_alphaY n

theorem wy_betaY_iterate_eq_neg (i : ℕ) (n : ℤ) :
    (wy betaY)^[i] n = -(wy alphaY)^[i] (-n - 1) - 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, wy_betaY_eq_neg]
    rw [show -(-(wy alphaY)^[i] (-n - 1) - 1) - 1 = (wy alphaY)^[i] (-n - 1) by ring]

/-- The phase of an integer `K`: `({K c₀}, {K c₁})`. -/
noncomputable def yPhZ (K : ℤ) : Fin 2 → ℝ := fun i => Int.fract ((K : ℝ) * yTheta i)

lemma yPhZ_zero (K : ℤ) : yPhZ K 0 = Int.fract ((K : ℝ) * yc0) := by
  simp [yPhZ, yTheta]

lemma yPhZ_one (K : ℤ) : yPhZ K 1 = Int.fract ((K : ℝ) * yc1) := by
  simp [yPhZ, yTheta]

lemma yPhZ_mem (K : ℤ) : yPhZ K ∈ yCube :=
  mem_yCube.2 ⟨⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩⟩

/-- Theorem Y's word reading, for every integer `K`: if `W^i(2K)` is odd for `1 ≤ i < τ` and
`W^τ(2K)` is even (`1 ≤ τ ≤ 4`), the phase of `K` lies in `yWord (τ − 1)`. -/
lemma yPhZ_mem_yWord (K : ℤ) {τ : ℕ} (hτ1 : 1 ≤ τ) (hτ4 : τ ≤ 4)
    (hodd : ∀ i, 1 ≤ i → i < τ → (wy alphaY)^[i] (2 * K) % 2 = 1)
    (hev : (wy alphaY)^[τ] (2 * K) % 2 = 0) : yPhZ K ∈ yWord (τ - 1) := by
  have hc := yPhZ_mem K
  have hu := yPhZ_zero K
  have hw := yPhZ_one K
  have hτ : τ = 1 ∨ τ = 2 ∨ τ = 3 ∨ τ = 4 := by omega
  rcases hτ with h | h | h | h
  · subst h
    refine ⟨hc, ?_⟩
    rw [hu]
    by_contra hne
    have := (wy_two_mul_odd_iff K).2 (not_lt.1 hne)
    simp only [Function.iterate_one] at hev
    omega
  · subst h
    have hW := hodd 1 le_rfl (by norm_num)
    simp only [Function.iterate_one] at hW
    have hu' := (wy_two_mul_odd_iff K).1 hW
    refine ⟨hc, ?_⟩
    rintro (h0 | ⟨-, -, hs⟩)
    · exact absurd h0.2 (by rw [hu]; linarith)
    · have := (wy_wy_two_mul_odd_iff hu').2 (by rw [← hu, ← hw]; exact hs)
      rw [wy_iterate_two] at hev
      omega
  · subst h
    have hW := hodd 1 le_rfl (by norm_num)
    have hW2 := hodd 2 (by norm_num) (by norm_num)
    simp only [Function.iterate_one] at hW
    rw [wy_iterate_two] at hW2
    have hu' := (wy_two_mul_odd_iff K).1 hW
    have hs := (wy_three_even_iff_strip hu' hW2).1 hev
    refine ⟨hc, by rw [hu]; exact hu', ?_⟩
    rw [hu, hw]
    exact hs
  · subst h
    have hW := hodd 1 le_rfl (by norm_num)
    have hW2 := hodd 2 (by norm_num) (by norm_num)
    have hW3 := hodd 3 (by norm_num) (by norm_num)
    simp only [Function.iterate_one] at hW
    rw [wy_iterate_two] at hW2
    have hu' := (wy_two_mul_odd_iff K).1 hW
    have hs := (wy_wy_two_mul_odd_iff hu').1 hW2
    refine ⟨⟨hc, by rw [hu]; exact hu', by rw [hu, hw]; exact hs.1,
      by rw [hu, hw]; exact hs.2⟩, ?_⟩
    rintro ⟨-, -, hs2⟩
    have := (wy_three_even_iff_strip hu' hW2).2 (by rw [← hu, ← hw]; exact hs2)
    omega

/-- The mirror Weyl frequencies `−(c₀, c₁)`. -/
noncomputable def ymTheta : Fin 2 → ℝ := -yTheta

/-- The mirror phase `({−k c₀}, {−k c₁})`. -/
noncomputable def ymPh (k : ℕ) : Fin 2 → ℝ := fun i => Int.fract ((k : ℝ) * ymTheta i)

lemma ymPh_eq (k : ℕ) : ymPh k = yPhZ (-(k : ℤ)) := by
  funext i
  simp [ymPh, yPhZ, ymTheta]

lemma odds_mem (k : ℕ) (_hk : 1 ≤ k) : 2 * (k : ℤ) - 1 ∈ {n : ℤ | n % 2 = 1} := by
  simp only [Set.mem_ofPred_eq]; omega

/-- The return word of `2k − 1` under `W′` is read off the mirror phase of `k`. -/
lemma ymPh_mem_yWord (k : ℕ) (hk : 1 ≤ k) :
    ymPh k ∈ yWord (returnTime ymPerm {n | n % 2 = 1} (2 * (k : ℤ) - 1) - 1) := by
  obtain ⟨h1, hT, hRS, -, hint⟩ :=
    returnTime_spec hyp_ymPerm (odds_mem k hk) (by omega) (Set.notMem_empty _)
  set τ := returnTime ymPerm {n | n % 2 = 1} (2 * (k : ℤ) - 1)
  have hσ : ∀ i, (wy betaY)^[i] (2 * (k : ℤ) - 1) =
      -(wy alphaY)^[i] (2 * (-(k : ℤ))) - 1 := by
    intro i; rw [wy_betaY_iterate_eq_neg]; congr 3; ring
  rw [ymPh_eq]
  apply yPhZ_mem_yWord _ h1 hT
  · intro i hi1 hi2
    have := hint i hi1 hi2
    simp only [Set.mem_ofPred_eq, ymPerm_pow_apply, hσ] at this
    omega
  · have := hRS
    simp only [returnMap, Set.mem_ofPred_eq, ymPerm_pow_apply, hσ] at this
    change (-(wy alphaY)^[τ] _ - 1) % 2 = 1 at this
    omega

/-- `returnTime = j + 1` iff the mirror phase lies in the `j`-th word cylinder. -/
lemma returnTime_ymPerm_eq_iff (k : ℕ) (hk : 1 ≤ k) {j : ℕ} (hj : j ≤ 3) :
    returnTime ymPerm {n | n % 2 = 1} (2 * (k : ℤ) - 1) = j + 1 ↔ ymPh k ∈ yWord j := by
  have hmem := ymPh_mem_yWord k hk
  obtain ⟨h1, hT, -⟩ :=
    returnTime_spec hyp_ymPerm (odds_mem k hk) (by omega) (Set.notMem_empty _)
  constructor
  · intro he; rw [he] at hmem; simpa using hmem
  · intro hw
    by_contra hne
    rcases lt_or_gt_of_ne (show returnTime ymPerm {n | n % 2 = 1} (2 * (k : ℤ) - 1) - 1 ≠ j by
      omega) with hlt | hgt
    · exact Set.disjoint_left.1 (yWord_disjoint hlt hj) hmem hw
    · exact Set.disjoint_left.1 (yWord_disjoint hgt (by omega)) hw hmem

lemma linearIndependent_ymTheta :
    LinearIndependent ℚ (Fin.cons (1 : ℝ) ymTheta : Fin 3 → ℝ) := by
  have h := linearIndependent_yTheta.units_smul (fun i : Fin 3 =>
    if i = 0 then (1 : ℚˣ) else -1)
  convert h using 1
  funext i
  fin_cases i <;> (simp [ymTheta, Units.smul_def]; try rfl)

open Classical in
/-- Weyl for the mirror word cylinders. -/
lemma tendsto_ymWordCount (hW : WeylEquidistributionMulti) (j : ℕ) :
    Tendsto (fun N : ℕ =>
      (((Finset.Icc 1 N).filter fun k : ℕ => ymPh k ∈ yWord j).card : ℝ) / N)
        atTop (𝓝 (yVol j)) := by
  have := hW 2 ymTheta linearIndependent_ymTheta (yWord j) (measurableSet_yWord j)
    (volume_frontier_yWord j)
  rw [volume_yWord] at this
  exact this


/-- On word `j`, `|R′(2k − 1) − αxʲk| < 3` (Theorem Y's sandwich at `−2k`, through `σ`). -/
lemma ymReturn_bound (k : ℕ) (hk : 1 ≤ k) :
    |(returnMap ymPerm {n | n % 2 = 1} (2 * (k : ℤ) - 1) : ℝ) -
      alphaY * yRoot ^ (returnTime ymPerm {n | n % 2 = 1} (2 * (k : ℤ) - 1) - 1) * k| < 3 := by
  obtain ⟨h1, hT, -, -, hint⟩ :=
    returnTime_spec hyp_ymPerm (odds_mem k hk) (by omega) (Set.notMem_empty _)
  set τ := returnTime ymPerm {n | n % 2 = 1} (2 * (k : ℤ) - 1)
  have hσ : ∀ i, (wy betaY)^[i] (2 * (k : ℤ) - 1) =
      -(wy alphaY)^[i] (2 * (-(k : ℤ))) - 1 := by
    intro i; rw [wy_betaY_iterate_eq_neg]; congr 3; ring
  have hodd : ∀ i : ℕ, 1 ≤ i → i ≤ τ - 1 → (wy alphaY)^[i] (2 * (-(k : ℤ))) % 2 = 1 := by
    intro i hi1 hi2
    have := hint i hi1 (by omega)
    rw [ymPerm_pow_apply, Set.mem_ofPred_eq, hσ] at this
    omega
  have hs := yRun_sandwich (show (2 * (-(k : ℤ))) % 2 = 0 by omega) (τ - 1) hodd
  have hRm : returnMap ymPerm {n | n % 2 = 1} (2 * (k : ℤ) - 1) =
      -(wy alphaY)^[τ - 1 + 1] (2 * (-(k : ℤ))) - 1 := by
    rw [returnMap, ymPerm_pow_apply, ← hσ]; congr 1; omega
  rw [hRm]
  rw [show 2 * (-(k : ℤ)) / 2 = -k by omega] at hs
  rw [abs_lt] at hs ⊢
  push_cast at hs ⊢
  constructor <;> nlinarith [hs.1, hs.2]

lemma ymPerm_returnCount_eq (X : ℕ) :
    returnCount ymPerm {n | n % 2 = 1} ∅ X =
      ((Finset.Icc 1 ((X + 1) / 2)).filter fun k : ℕ =>
        returnMap ymPerm {n | n % 2 = 1} (2 * (k : ℤ) - 1) ≤ X).card := by
  classical
  unfold returnCount
  symm
  apply Finset.card_nbij (fun k : ℕ => 2 * (k : ℤ) - 1)
  · intro k hk
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq, Set.notMem_empty,
      not_false_eq_true, true_and] at hk ⊢
    obtain ⟨⟨h1, h2⟩, hR⟩ := hk
    exact ⟨⟨by omega, by omega⟩, by omega, hR⟩
  · intro a _ b _ h
    have : (a : ℤ) = b := by simp only at h; omega
    exact_mod_cast this
  · intro s hs
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq, Set.notMem_empty,
      not_false_eq_true, true_and] at hs
    obtain ⟨⟨h1, h2⟩, ho, hR⟩ := hs
    refine ⟨((s + 1) / 2).toNat, ?_, by simp only; omega⟩
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [show 2 * ((((s + 1) / 2).toNat : ℕ) : ℤ) - 1 = s by omega]
    exact hR

open Classical in
/-- **Return-count density.**  `#{odd s ≤ X : R′(s) ≤ X}/X → Σ_{j ≤ 3} P_j/(αxʲ)`. -/
theorem tendsto_returnCount_ymPerm (hW : WeylEquidistributionMulti) :
    Tendsto (fun X : ℕ => (returnCount ymPerm {n | n % 2 = 1} ∅ X : ℝ) / X) atTop
      (𝓝 (∑ j ∈ Finset.range 4, yVol j * (alphaY * yRoot ^ j)⁻¹)) := by
  set c : ℕ → ℝ := fun j => alphaY * yRoot ^ j
  set Cnt : ℕ → ℕ → ℕ := fun j N =>
    ((Finset.Icc 1 N).filter fun k : ℕ => ymPh k ∈ yWord j).card
  set T : ℕ → ℕ → ℕ := fun j X => ((Finset.Icc 1 ((X + 1) / 2)).filter fun k : ℕ =>
    returnTime ymPerm {n | n % 2 = 1} (2 * (k : ℤ) - 1) = j + 1 ∧
      returnMap ymPerm {n | n % 2 = 1} (2 * (k : ℤ) - 1) ≤ X).card
  have hspec : ∀ k : ℕ, 1 ≤ k → 1 ≤ returnTime ymPerm {n | n % 2 = 1} (2 * (k : ℤ) - 1) ∧
      returnTime ymPerm {n | n % 2 = 1} (2 * (k : ℤ) - 1) ≤ 4 := by
    intro k hk
    obtain ⟨h1, hT, -⟩ :=
      returnTime_spec hyp_ymPerm (odds_mem k hk) (by omega) (Set.notMem_empty _)
    exact ⟨h1, hT⟩
  have hsum : ∀ X, returnCount ymPerm {n | n % 2 = 1} ∅ X =
      ∑ j ∈ Finset.range 4, T j X := by
    intro X
    rw [ymPerm_returnCount_eq, Finset.card_eq_sum_card_fiberwise
      (f := fun k : ℕ => returnTime ymPerm {n | n % 2 = 1} (2 * (k : ℤ) - 1) - 1)
      (t := Finset.range 4)]
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp only [T, Finset.filter_filter]
      congr 1
      refine Finset.filter_congr fun k hk => ?_
      have := (hspec k (Finset.mem_Icc.1 hk).1).1
      omega
    · intro k hk
      simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hk
      have := (hspec k hk.1.1).2
      simp only [Finset.coe_range, Set.mem_Iio]
      omega
  have hlo : ∀ j, j ≤ 3 → ∀ X : ℕ, Cnt j ⌊(c j)⁻¹ * X + -3 / c j⌋₊ ≤ T j X := by
    intro j hj X
    apply Finset.card_le_card
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk ⊢
    obtain ⟨⟨hk1, hk2⟩, hw⟩ := hk
    have hcj : 2 ≤ c j := two_le_alphaY_mul_pow hj
    have hkr := (Nat.le_floor_iff' (by omega)).1 hk2
    have hck : c j * k ≤ X - 3 := by
      have := mul_le_mul_of_nonneg_left hkr (by linarith : (0 : ℝ) ≤ c j)
      rw [mul_add, ← mul_assoc, mul_inv_cancel₀ (by linarith), one_mul,
        mul_div_cancel₀ _ (by linarith)] at this
      linarith
    have hrt := (returnTime_ymPerm_eq_iff k hk1 hj).2 hw
    have hb := ymReturn_bound k hk1
    rw [hrt, Nat.add_sub_cancel] at hb
    have hRX : (returnMap ymPerm {n | n % 2 = 1} (2 * (k : ℤ) - 1) : ℝ) < X := by
      linarith [(abs_lt.1 hb).2]
    refine ⟨⟨hk1, ?_⟩, hrt, by exact_mod_cast hRX.le⟩
    have : (2 : ℝ) * k ≤ X := by
      have : (2 : ℝ) * k ≤ c j * k := by
        have : (0 : ℝ) ≤ k := by positivity
        nlinarith
      linarith
    have : 2 * k ≤ X := by exact_mod_cast this
    omega
  have hhi : ∀ j, j ≤ 3 → ∀ X : ℕ, T j X ≤ Cnt j ⌊(c j)⁻¹ * X + 3 / c j⌋₊ := by
    intro j hj X
    apply Finset.card_le_card
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk ⊢
    obtain ⟨⟨hk1, -⟩, hrt, hRX⟩ := hk
    have hcj : 2 ≤ c j := two_le_alphaY_mul_pow hj
    refine ⟨⟨hk1, Nat.le_floor ?_⟩, (returnTime_ymPerm_eq_iff k hk1 hj).1 hrt⟩
    have hb := ymReturn_bound k hk1
    rw [hrt, Nat.add_sub_cancel] at hb
    have hRX' : (returnMap ymPerm {n | n % 2 = 1} (2 * (k : ℤ) - 1) : ℝ) ≤ X := by
      exact_mod_cast hRX
    have : c j * k < X + 3 := by linarith [(abs_lt.1 hb).1]
    rw [show (c j)⁻¹ * X + 3 / c j = (X + 3) / c j by field_simp, le_div_iff₀ (by linarith)]
    linarith
  have hlimT : ∀ j ∈ Finset.range 4, Tendsto (fun X : ℕ => (T j X : ℝ) / X) atTop
      (𝓝 (yVol j * (alphaY * yRoot ^ j)⁻¹)) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hcj : 2 ≤ c j := two_le_alphaY_mul_pow (by omega)
    have hcpos : 0 < (c j)⁻¹ := inv_pos.2 (by linarith)
    have L1 := yTendsto_comp_div (tendsto_ymWordCount hW j)
      (yTendsto_floor_linear hcpos (-3 / c j)) (yTendsto_floor_linear_div hcpos (-3 / c j))
    have L2 := yTendsto_comp_div (tendsto_ymWordCount hW j)
      (yTendsto_floor_linear hcpos (3 / c j)) (yTendsto_floor_linear_div hcpos (3 / c j))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le L1 L2 (fun X => ?_) (fun X => ?_)
    · exact div_le_div_of_nonneg_right (Nat.cast_le.2 (hlo j (by omega) X)) (by positivity)
    · exact div_le_div_of_nonneg_right (Nat.cast_le.2 (hhi j (by omega) X)) (by positivity)
  refine (tendsto_finsetSum (Finset.range 4) hlimT).congr fun X => ?_
  simp only [hsum X, Nat.cast_sum, Finset.sum_div]

/-- **(proved, conditional on Weyl; Theorem Y′ (4), density).**  Assuming multidimensional Weyl
equidistribution, the orbit minima have Theorem Y's density
`d = 3/10 + x/8 + x²/10 ≈ 0.39340781`.  Paper proof: by `minCount_ymPerm_add`,
`d = 1/2 − (1/2) Σ_{j ≤ 3} P′_j / c_j`, with `P′_j` the density among the odds of the return
word `O Eʲ` and `|R′(2k − 1) − c_j k| < 3`, `c_j = αxʲ` (`ymReturn_bound`).  By the conjugacy
`W′ = σ W σ` (`wy_betaY_eq_neg`) the word of `2k − 1` is Theorem Y's word of `−2k`, read off the
phase of `−k` in Theorem Y's cylinders (`returnTime_ymPerm_eq_iff`); Weyl at the frequencies
`−(c₀, c₁)` gives `P′ = (1/2, 1/4, 1/(4(1 + x)), x/(4(1 + x)))` (`tendsto_ymWordCount`), and
the sum is `densityY_sum_eq`.  (Census: 786 810 minima `≤ 2·10⁶`, `dX = 786 815.6`.) -/
theorem tendsto_minCount_ymPerm (hW : WeylEquidistributionMulti) :
    Tendsto (fun X : ℕ => (minCount ymPerm X : ℝ) / X) atTop (𝓝 densityY) := by
  have hR := tendsto_returnCount_ymPerm hW
  have hX : ∀ X : ℕ, (minCount ymPerm X : ℝ) / X =
      (((X + 1) / 2 : ℕ) : ℝ) / X - (returnCount ymPerm {n | n % 2 = 1} ∅ X : ℝ) / X := by
    intro X
    have := minCount_ymPerm_add X
    rw [div_sub_div_same]
    congr 1
    rw [eq_sub_iff_add_eq]; exact_mod_cast this
  have hhalf : Tendsto (fun X : ℕ => (((X + 1) / 2 : ℕ) : ℝ) / X) atTop (𝓝 (1 / 2)) := by
    have := yTendsto_floor_linear_div (c := 1 / 2) (by norm_num) (1 / 2)
    refine this.congr fun X => ?_
    have h := Nat.floor_div_eq_div (K := ℝ) (X + 1) 2
    push_cast at h
    rw [show (1 / 2 : ℝ) * X + 1 / 2 = (X + 1) / 2 by ring, h]
  have hlim := hhalf.sub hR
  rw [densityY_sum_eq] at hlim
  exact hlim.congr fun X => (hX X).symm

end CollatzMoonshot.WythoffMirrorY
