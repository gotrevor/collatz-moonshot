/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.AmusicalTrap
import CollatzMoonshot.MonotonePotential
import CollatzMoonshot.WythoffGeneral

/-!
# Theorem G: the `E Oᵐ`-exact line of solved Wythoff members

Research note `wythoff-solvable`, §2.  Fix integers `m ≥ 0`, `r ≥ 2`.  The polynomial
`x^{m+1} − 2rx + r` has exactly one root `x` in `(1/2, 1)`, and it lies in `(1/2, 3/4)`
(`gRoot`, `gRoot_spec`, `gRoot_unique`).  Put `β = 2x` and `α = 2x/(2x − 1) = 2r/xᵐ`, so
`β = α/(α − 1)`, `(α/2)(β/2)ᵐ = r` and `α^{m+1} = 2^{m+1} r (α − 1)ᵐ`.  Let `W = W_α`
(`WythoffGeneral.wy`: `2k ↦ ⌊kα⌋`, `2k − 1 ↦ ⌈kβ⌉ − 1`) and let `W′ = W_β` be the mirror.

1. **Exact composite.**  If `n` is even and `W(n), …, Wᵐ(n)` are odd then `W^{m+1}(n) = r·n`
   (`wy_iterate_eq_of_odd_run`).  So after an even point at most `m` odd points follow.
2. **Classification** (via Lemma P, `MonotonePotential`, with `S` = evens, `Φ = {1}`,
   `T = m + 1`).  `{1}` is the only finite orbit in `ℕ⁺`; every other orbit tends to `∞` both
   ways; its minimum is the unique even `y` with `W⁻¹(y), …, W^{−(m+1)}(y)` all odd.
3. **Count.**  `#{minima ≤ X} + #{even s ≤ X : R(s) ≤ X} = 1 + ⌊X/2⌋` exactly, and
   `R(s) ≥ r·s`, so `#{minima ≤ X} ≥ 1 + ⌊X/2⌋ − ⌊X/2r⌋`: infinitely many infinite orbits.
4. **Density** (conditional on multidimensional Weyl equidistribution, a literature hypothesis,
   and `deg x = m + 1`): `d = (α − 2)/(2αβᵐ) = (r − xᵐ)/(2^{m+1} r xᵐ)`.
5. **Mirror.**  On `O Eᵐ`, `W′^{m+1}(n) = r(n + 1) − 1`; Lemma P with `S` = odds, `Φ = ∅`:
   no finite orbit in `ℕ⁺`, minima are the odd `y` with `m + 1` even predecessors, same `d`.

Special rows: `m = 0` is Theorem E (`α = 2r`, `gRoot_zero`), `m = 1` is Theorem F
(`α = 2r + 2√(r² − r)`, `alphaG_one`), `m = 2, r = 2` is the cubic
`α³ − 16α² + 32α − 16 = 0`, `α ≈ 13.7587`, `d ≈ 0.36746`.

**Identity, paper proof (a sandwich; no irrationality needed).**  Write `A = α/2`, so the
even step is `v ↦ ⌊Av⌋` and the odd step is `v ↦ ⌈x(v + 1)⌉ − 1`.  For `n` even with
`W(n), …, Wʲ(n)` odd put `y_1 = An` and `y_{i+1} = x(Wⁱ(n) + 1)`, so `W(n) = ⌊y_1⌋` and
`W^{i+1}(n) = ⌈y_{i+1}⌉ − 1` for `1 ≤ i ≤ j`.  From `y − 1 < ⌊y⌋ ≤ y` and
`y − 1 ≤ ⌈y⌉ − 1 < y`: `x·y_1 < y_2 ≤ x·y_1 + x` (floor step, strict on the left) and
`x·y_i ≤ y_{i+1} < x·y_i + x` for `i ≥ 2`, so `c_j n < y_{j+1} ≤ c_j n + Σ_{l=1}^{j} xˡ` with
`c_j = A xʲ` (signs of `n` irrelevant, `x > 0`).  At `j = m`, `c_m = x^{m+1}/(2x − 1) = r` and
`Σ_{l=1}^{m} xˡ < 1` (`⟺ 2x − 1 < x^{m+1} = r(2x − 1)`), so `rn < y_{m+1} < rn + 1` and
`W^{m+1}(n) = ⌈y_{m+1}⌉ − 1 = rn`.  For `j ≤ m` and `n > 0`, `c_j = r x^{j−m} ≥ r`, so
`y_{j+1} > rn` and `W^{j+1}(n) ≥ rn` (`le_wy_iterate_of_odd_run`, the (H2) input).  (`m = 0`:
`c_0 = A = r` and `W(n) = ⌊rn⌋ = rn`.)
-/

namespace CollatzMoonshot.WythoffLine

open CollatzMoonshot.WythoffGeneral CollatzMoonshot.MonotonePotential
open CollatzMoonshot.AmusicalTrap (permOrbit InfinitelyManyInfiniteOrbits)
open Filter Topology

/-! ## The root `x` and the parameters `α`, `β` -/

open Classical in
/-- The root `x ∈ (1/2, 3/4)` of `x^{m+1} − 2rx + r` (`gRoot_spec`, for `r ≥ 2`). -/
noncomputable def gRoot (m r : ℕ) : ℝ :=
  if h : ∃ x : ℝ, 1 / 2 < x ∧ x < 3 / 4 ∧ x ^ (m + 1) = r * (2 * x - 1) then h.choose else 0

/-- `α = 2x/(2x − 1)`. -/
noncomputable def alphaG (m r : ℕ) : ℝ :=
  2 * gRoot m r / (2 * gRoot m r - 1)

/-- `β = 2x = α/(α − 1)`. -/
noncomputable def betaG (m r : ℕ) : ℝ :=
  2 * gRoot m r

section Root

variable {m r : ℕ}

/-- **(ratified).**  The root exists.  Paper proof: IVT for `F(x) = x^{m+1} − 2rx + r` on
`[1/2, 3/4]`: `F(1/2) = 2^{−m−1} > 0`, `F(3/4) ≤ 3/4 − r/2 < 0`. -/
theorem gRoot_spec (hr : 2 ≤ r) :
    1 / 2 < gRoot m r ∧ gRoot m r < 3 / 4 ∧ gRoot m r ^ (m + 1) = r * (2 * gRoot m r - 1) := by
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hex : ∃ x : ℝ, 1 / 2 < x ∧ x < 3 / 4 ∧ x ^ (m + 1) = r * (2 * x - 1) := by
    let F : ℝ → ℝ := fun t => t ^ (m + 1) - r * (2 * t - 1)
    have hF : ContinuousOn F (Set.Icc (1 / 2) (3 / 4)) := by fun_prop
    have h0 : (0 : ℝ) ∈ Set.Ioo (F (3 / 4)) (F (1 / 2)) := by
      have h34 : ((3 : ℝ) / 4) ^ (m + 1) ≤ 3 / 4 :=
        pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
      have h12 : (0 : ℝ) < (1 / 2) ^ (m + 1) := by positivity
      constructor
      · show (3 / 4 : ℝ) ^ (m + 1) - r * (2 * (3 / 4) - 1) < 0; nlinarith
      · show (0 : ℝ) < (1 / 2) ^ (m + 1) - r * (2 * (1 / 2) - 1); nlinarith
    obtain ⟨x, ⟨hx1, hx2⟩, hx⟩ := intermediate_value_Ioo' (by norm_num) hF h0
    exact ⟨x, hx1, hx2, by simp only [F] at hx; linarith⟩
  unfold gRoot
  rw [dif_pos hex]
  exact hex.choose_spec

/-- Two roots of `x^{m+1} − 2rx + r` in `(1/2, 1)` coincide: the slopes of the convex
`t ↦ t^{m+1}` increase, but the chord through two roots has slope `2r` and the chord to `1` has
slope `< 2r`. -/
lemma no_two_roots (hr : 2 ≤ r) {y₁ y₂ : ℝ} (h0 : 0 ≤ y₁) (h12 : y₁ < y₂) (h2 : y₂ < 1)
    (hy₁ : y₁ ^ (m + 1) = r * (2 * y₁ - 1)) (hy₂ : y₂ ^ (m + 1) = r * (2 * y₂ - 1)) : False := by
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hs := (convexOn_pow (𝕜 := ℝ) (m + 1)).slope_mono_adjacent (Set.mem_Ici.2 h0)
    (Set.mem_Ici.2 (zero_le_one' ℝ)) h12 h2
  simp only [one_pow] at hs
  rw [hy₁, hy₂, div_le_div_iff₀ (by linarith) (by linarith)] at hs
  nlinarith

/-- **(ratified).**  Uniqueness in `(1/2, 1)`.  Paper proof: `F` is convex with `F(1/2) > 0` and
`F(1) = 1 − r < 0`, so it has one root in `(1/2, 1)`. -/
theorem gRoot_unique (hr : 2 ≤ r) {y : ℝ} (hy1 : 1 / 2 < y) (hy2 : y < 1)
    (hy : y ^ (m + 1) = r * (2 * y - 1)) : y = gRoot m r := by
  obtain ⟨hx1, hx2, hx⟩ := gRoot_spec (m := m) hr
  rcases lt_trichotomy y (gRoot m r) with h | h | h
  · exact absurd (no_two_roots hr (by linarith) h (by linarith) hy hx) id
  · exact h
  · exact absurd (no_two_roots hr (by linarith) h hy2 hx hy) id

/-- **(ratified).**  For `m ≥ 1`, `x` is irrational: a rational root of the monic integer
polynomial `x^{m+1} − 2rx + r` is an integer, and `x ∈ (1/2, 3/4)`. -/
theorem irrational_gRoot (hm : 1 ≤ m) (hr : 2 ≤ r) : Irrational (gRoot m r) := by
  obtain ⟨hx1, hx2, hx⟩ := gRoot_spec (m := m) hr
  rintro ⟨q, hq⟩
  set x := gRoot m r
  have hd0 : (0 : ℝ) < q.den := by exact_mod_cast q.pos
  have hqx : x = (q.num : ℝ) / q.den := by rw [← hq, Rat.cast_def]
  -- clear denominators: `n^{m+1} = r (2n − d) d^m`
  have hclear : (q.num : ℝ) ^ (m + 1) = r * (2 * q.num - q.den) * (q.den : ℝ) ^ m := by
    rw [hqx, div_pow] at hx
    field_simp at hx
    apply mul_right_cancel₀ hd0.ne'
    linear_combination hx
  have hcl : q.num ^ (m + 1) = r * (2 * q.num - q.den) * (q.den : ℤ) ^ m := by exact_mod_cast hclear
  have hdvd : (q.den : ℤ) ∣ q.num ^ (m + 1) := by
    rw [hcl]
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    exact ⟨r * (2 * q.num - q.den) * (q.den : ℤ) ^ m', by ring⟩
  have hcop : IsCoprime q.num (q.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact q.reduced
  have hunit : IsUnit (q.den : ℤ) :=
    (hcop.pow_left (m := m + 1)).isUnit_of_dvd' hdvd dvd_rfl
  have hd1 : q.den = 1 := by
    rcases Int.isUnit_iff.1 hunit with h | h
    · exact_mod_cast h
    · have := q.pos; omega
  rw [hqx, hd1, Nat.cast_one, div_one] at hx1 hx2
  rcases le_or_gt q.num 0 with h | h
  · have : (q.num : ℝ) ≤ 0 := by exact_mod_cast h
    linarith
  · have : (1 : ℝ) ≤ q.num := by exact_mod_cast h
    linarith

/-- **(ratified, `m = 0`).**  `x = r/(2r − 1)`. -/
theorem gRoot_zero (hr : 2 ≤ r) : gRoot 0 r = r / (2 * r - 1) := by
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hd : (0 : ℝ) < 2 * r - 1 := by linarith
  refine (gRoot_unique hr ?_ ?_ ?_).symm
  · rw [lt_div_iff₀ hd]; linarith
  · rw [div_lt_one hd]; linarith
  · have hd' : (2 * (r : ℝ) - 1) ≠ 0 := hd.ne'
    rw [zero_add, pow_one, mul_div_assoc', eq_comm, div_sub_one hd', mul_div_assoc',
      div_eq_div_iff hd' hd']
    ring

/-- **(ratified).**  `α = 2r/xᵐ`. -/
theorem alphaG_eq (hr : 2 ≤ r) : alphaG m r = 2 * r / gRoot m r ^ m := by
  obtain ⟨hx1, hx2, hx⟩ := gRoot_spec (m := m) hr
  have hxm : 0 < gRoot m r ^ m := pow_pos (by linarith) m
  unfold alphaG
  rw [div_eq_div_iff (by linarith) hxm.ne']
  rw [pow_succ] at hx
  linear_combination 2 * hx

/-- **(ratified).**  `α^{m+1} = 2^{m+1} r (α − 1)ᵐ` (for `m = 2, r = 2`:
`α³ − 16α² + 32α − 16 = 0`). -/
theorem alphaG_pow (hr : 2 ≤ r) :
    alphaG m r ^ (m + 1) = 2 ^ (m + 1) * r * (alphaG m r - 1) ^ m := by
  obtain ⟨hx1, hx2, hx⟩ := gRoot_spec (m := m) hr
  have hu : 0 < 2 * gRoot m r - 1 := by linarith
  have h1 : alphaG m r - 1 = 1 / (2 * gRoot m r - 1) := by
    unfold alphaG; field_simp; ring
  rw [h1]
  unfold alphaG
  rw [div_pow, mul_pow, hx, one_div_pow]
  field_simp
  ring

/-- **(ratified).**  `4 ≤ α` (`α = 2r/xᵐ ≥ 2r`). -/
theorem four_le_alphaG (hr : 2 ≤ r) : 4 ≤ alphaG m r := by
  obtain ⟨hx1, hx2, hx⟩ := gRoot_spec (m := m) hr
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hxm : 0 < gRoot m r ^ m := pow_pos (by linarith) m
  have hxm1 : gRoot m r ^ m ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  rw [alphaG_eq hr, le_div_iff₀ hxm]
  nlinarith

theorem one_lt_alphaG (hr : 2 ≤ r) : 1 < alphaG m r :=
  lt_of_lt_of_le (by norm_num) (four_le_alphaG hr)

/-- **(ratified).**  `1 < β < 3/2`. -/
theorem one_lt_betaG_lt (hr : 2 ≤ r) : 1 < betaG m r ∧ betaG m r < 3 / 2 := by
  obtain ⟨hx1, hx2, -⟩ := gRoot_spec (m := m) hr
  unfold betaG
  constructor <;> linarith

theorem one_lt_betaG (hr : 2 ≤ r) : 1 < betaG m r := (one_lt_betaG_lt hr).1

/-- **(ratified).**  `β = α/(α − 1)`. -/
theorem alphaG_div_sub_one (hr : 2 ≤ r) : alphaG m r / (alphaG m r - 1) = betaG m r := by
  obtain ⟨hx1, -, -⟩ := gRoot_spec (m := m) hr
  have hu : 0 < 2 * gRoot m r - 1 := by linarith
  have h1 : alphaG m r - 1 = 1 / (2 * gRoot m r - 1) := by
    unfold alphaG; field_simp; ring
  rw [h1]
  unfold alphaG betaG
  field_simp

/-- **(ratified).**  `α = β/(β − 1)` (so the mirror `W_β` has partner slope `α`). -/
theorem betaG_div_sub_one (hr : 2 ≤ r) : betaG m r / (betaG m r - 1) = alphaG m r := by
  unfold alphaG betaG
  rfl

/-- **(ratified, `m = 0`: Theorem E).**  `α = 2r`. -/
theorem alphaG_zero (hr : 2 ≤ r) : alphaG 0 r = 2 * r := by
  rw [alphaG_eq hr, pow_zero, div_one]

/-- **(ratified, `m = 1`: Theorem F).**  `α = 2r + 2√(r² − r)`.  Paper proof: `x = r − √(r² − r)`
is the root of `x² − 2rx + r` in `(1/2, 3/4)` (`gRoot_unique`), and `2r/x = 2(r + √(r² − r))`. -/
theorem alphaG_one (hr : 2 ≤ r) : alphaG 1 r = 2 * r + 2 * √((r : ℝ) ^ 2 - r) := by
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hD : (0 : ℝ) ≤ (r : ℝ) ^ 2 - r := by nlinarith
  have hsq := Real.sq_sqrt hD
  have hgt : (r : ℝ) - 3 / 5 < √((r : ℝ) ^ 2 - r) := by
    rw [Real.lt_sqrt (by linarith)]; nlinarith
  have hlt : √((r : ℝ) ^ 2 - r) < r - 1 / 2 := by
    rw [Real.sqrt_lt' (by linarith)]; nlinarith
  have hy : (r : ℝ) - √((r : ℝ) ^ 2 - r) = gRoot 1 r := by
    refine gRoot_unique hr (by linarith) (by linarith) ?_
    linear_combination hsq
  rw [alphaG_eq hr, ← hy, pow_one, div_eq_iff (by linarith)]
  linear_combination 2 * hsq

end Root

/-! ## The maps -/

/-- `W_α` for the `(m, r)` member, as a permutation of `ℤ`. -/
noncomputable def gPerm (m r : ℕ) (hr : 2 ≤ r) : Equiv.Perm ℤ :=
  wyPerm (alphaG m r) (one_lt_alphaG hr)

/-- The mirror `W_β`, `β = 2x`, as a permutation of `ℤ`. -/
noncomputable def gmPerm (m r : ℕ) (hr : 2 ≤ r) : Equiv.Perm ℤ :=
  wyPerm (betaG m r) (one_lt_betaG hr)

theorem gPerm_apply {m r : ℕ} (hr : 2 ≤ r) (n : ℤ) : gPerm m r hr n = wy (alphaG m r) n := rfl

theorem gmPerm_apply {m r : ℕ} (hr : 2 ≤ r) (n : ℤ) : gmPerm m r hr n = wy (betaG m r) n := rfl

/-! ## Theorem G (1): the exact composite on `E Oᵐ` -/

section Identity

variable {m r : ℕ}

/-- `A xᵐ = r` with `A = α/2`. -/
lemma half_alphaG_mul_pow (hr : 2 ≤ r) : alphaG m r / 2 * gRoot m r ^ m = r := by
  obtain ⟨hx1, -, -⟩ := gRoot_spec (m := m) hr
  have hxm : 0 < gRoot m r ^ m := pow_pos (by linarith) m
  rw [alphaG_eq hr]
  field_simp

/-- Even step: `W(v) = ⌊(α/2)v⌋`. -/
lemma wy_even_bounds (α : ℝ) {v : ℤ} (hv : v % 2 = 0) :
    (wy α v : ℝ) ≤ α / 2 * v ∧ α / 2 * v - 1 < wy α v := by
  obtain ⟨k, rfl⟩ : ∃ k, v = 2 * k := ⟨v / 2, by omega⟩
  rw [wy_two_mul]
  have : α / 2 * ((2 * k : ℤ) : ℝ) = (k : ℝ) * α := by push_cast; ring
  rw [this]
  exact ⟨Int.floor_le _, by linarith [Int.lt_floor_add_one ((k : ℝ) * α)]⟩

/-- Odd step: `W(v) = ⌈(γ/2)(v + 1)⌉ − 1` with `γ = α/(α − 1)`. -/
lemma wy_odd_bounds (α : ℝ) {v : ℤ} (hv : v % 2 = 1) :
    α / (α - 1) / 2 * (v + 1) - 1 ≤ wy α v ∧ (wy α v : ℝ) < α / (α - 1) / 2 * (v + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, v = 2 * k - 1 := ⟨(v + 1) / 2, by omega⟩
  rw [wy_two_mul_sub_one]
  have : α / (α - 1) / 2 * (((2 * k - 1 : ℤ) : ℝ) + 1) = (k : ℝ) * (α / (α - 1)) := by
    push_cast; ring
  rw [this]
  push_cast
  exact ⟨by linarith [Int.le_ceil ((k : ℝ) * (α / (α - 1)))],
    by linarith [Int.ceil_lt_add_one ((k : ℝ) * (α / (α - 1)))]⟩

/-- **The sandwich on `E Oʲ`.**  For `n` even with `W(n), …, Wʲ(n)` odd:
`A xʲ n < W^{j+1}(n) + 1` and `(1 − x)(W^{j+1}(n) − A xʲ n) ≤ x − x^{j+1}`. -/
lemma run_sandwich (hr : 2 ≤ r) {n : ℤ} (hn : n % 2 = 0) (j : ℕ)
    (hodd : ∀ i : ℕ, 1 ≤ i → i ≤ j → (wy (alphaG m r))^[i] n % 2 = 1) :
    alphaG m r / 2 * gRoot m r ^ j * n < ((wy (alphaG m r))^[j + 1] n : ℝ) + 1 ∧
      (1 - gRoot m r) * (((wy (alphaG m r))^[j + 1] n : ℝ) - alphaG m r / 2 * gRoot m r ^ j * n)
        ≤ gRoot m r - gRoot m r ^ (j + 1) := by
  obtain ⟨hx1, hx2, -⟩ := gRoot_spec (m := m) hr
  induction j with
  | zero =>
    obtain ⟨h1, h2⟩ := wy_even_bounds (alphaG m r) hn
    simp only [pow_zero, mul_one, zero_add, pow_one, Function.iterate_one, sub_self]
    constructor
    · linarith
    · nlinarith
  | succ j ih =>
    obtain ⟨ih1, ih2⟩ := ih fun i hi1 hi2 => hodd i hi1 (by omega)
    have hv := hodd (j + 1) (by omega) le_rfl
    obtain ⟨h1, h2⟩ := wy_odd_bounds (alphaG m r) hv
    rw [alphaG_div_sub_one hr, betaG, show 2 * gRoot m r / 2 = gRoot m r by ring] at h1 h2
    rw [Function.iterate_succ_apply']
    have hx0 : (0 : ℝ) < gRoot m r := by linarith
    have hx1' : (0 : ℝ) < 1 - gRoot m r := by linarith
    have p1 := mul_lt_mul_of_pos_left ih1 hx0
    have p2 := mul_le_mul_of_nonneg_left h2.le hx1'.le
    have p3 := mul_le_mul_of_nonneg_left ih2 hx0.le
    constructor
    · rw [pow_succ]; nlinarith
    · rw [pow_succ, pow_succ]; nlinarith

/-- **(ratified, Theorem G (1)).**  If `n` is even and `W(n), …, Wᵐ(n)` are odd, then
`W^{m+1}(n) = r·n`; for every `n ∈ ℤ`.  Paper proof: module docstring (for `m = 0`,
`W(2k) = ⌊2rk⌋ = 2rk`). -/
theorem wy_iterate_eq_of_odd_run (hr : 2 ≤ r) {n : ℤ} (hn : n % 2 = 0)
    (hodd : ∀ i : ℕ, 1 ≤ i → i ≤ m → (wy (alphaG m r))^[i] n % 2 = 1) :
    (wy (alphaG m r))^[m + 1] n = r * n := by
  obtain ⟨hx1, hx2, hx⟩ := gRoot_spec (m := m) hr
  obtain ⟨h1, h2⟩ := run_sandwich hr hn m hodd
  rw [half_alphaG_mul_pow hr] at h1 h2
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hlt : gRoot m r - gRoot m r ^ (m + 1) < 1 - gRoot m r := by rw [hx]; nlinarith
  have hup : (((wy (alphaG m r))^[m + 1] n : ℤ) : ℝ) < ((r * n + 1 : ℤ) : ℝ) := by
    push_cast; nlinarith
  have hlo : ((r * n - 1 : ℤ) : ℝ) < (((wy (alphaG m r))^[m + 1] n : ℤ) : ℝ) := by
    push_cast; linarith
  have a := Int.cast_lt.1 hup
  have b := Int.cast_lt.1 hlo
  omega

/-- **(ratified, Theorem G (1), runs).**  After an even point at most `m` odd points follow: some
`W^{j+1}(n)`, `j ≤ m`, is even.  Paper proof: `wy_iterate_eq_of_odd_run` (`r·n` is even). -/
theorem exists_even_iterate (hr : 2 ≤ r) {n : ℤ} (hn : n % 2 = 0) :
    ∃ j ≤ m, (wy (alphaG m r))^[j + 1] n % 2 = 0 := by
  by_contra hne
  push Not at hne
  have hodd : ∀ i : ℕ, 1 ≤ i → i ≤ m → (wy (alphaG m r))^[i] n % 2 = 1 := by
    intro i hi1 hi2
    have := hne (i - 1) (by omega)
    rw [show i - 1 + 1 = i by omega] at this
    omega
  have h2 := hne m le_rfl
  rw [wy_iterate_eq_of_odd_run hr hn hodd] at h2
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
  apply h2
  rw [show (r : ℤ) * (2 * k) = 2 * (r * k) by ring]
  omega

/-- **(ratified, Theorem G, partial runs).**  For `n > 0` even, `j ≤ m`, and `W(n), …, Wʲ(n)`
odd: `r·n ≤ W^{j+1}(n)`.  Paper proof: `W^{j+1}(n) = ⌊c_j n + δ_j⌋ ≥ ⌊c_j n⌋` with
`c_j = r x^{j−m} ≥ r`. -/
theorem le_wy_iterate_of_odd_run (hr : 2 ≤ r) {n : ℤ} (hn0 : 0 < n) (hn : n % 2 = 0) {j : ℕ}
    (hj : j ≤ m) (hodd : ∀ i : ℕ, 1 ≤ i → i ≤ j → (wy (alphaG m r))^[i] n % 2 = 1) :
    r * n ≤ (wy (alphaG m r))^[j + 1] n := by
  obtain ⟨hx1, hx2, hx⟩ := gRoot_spec (m := m) hr
  obtain ⟨h1, -⟩ := run_sandwich hr hn j hodd
  have hxj : gRoot m r ^ m ≤ gRoot m r ^ j :=
    pow_le_pow_of_le_one (by linarith) (by linarith) hj
  have hA : 0 < alphaG m r / 2 := by have := four_le_alphaG (m := m) hr; linarith
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hreq := half_alphaG_mul_pow (m := m) hr
  have p := mul_le_mul_of_nonneg_left hxj hA.le
  have key : (r : ℝ) * n ≤ alphaG m r / 2 * gRoot m r ^ j * n := by nlinarith
  have hlo : ((r * n - 1 : ℤ) : ℝ) < (((wy (alphaG m r))^[j + 1] n : ℤ) : ℝ) := by
    push_cast; linarith
  have := Int.cast_lt.1 hlo
  omega

/-- **The mirror sandwich on `O Eʲ`.**  For `n` odd with `W′(n), …, W′ʲ(n)` even:
`W′^{j+1}(n) < A xʲ (n + 1)` and `(1 − x)(A xʲ (n + 1) − W′^{j+1}(n)) ≤ 1 − x^{j+1}`. -/
lemma run_sandwich_mirror (hr : 2 ≤ r) {n : ℤ} (hn : n % 2 = 1) (j : ℕ)
    (heven : ∀ i : ℕ, 1 ≤ i → i ≤ j → (wy (betaG m r))^[i] n % 2 = 0) :
    ((wy (betaG m r))^[j + 1] n : ℝ) < alphaG m r / 2 * gRoot m r ^ j * (n + 1) ∧
      (1 - gRoot m r) *
          (alphaG m r / 2 * gRoot m r ^ j * (n + 1) - ((wy (betaG m r))^[j + 1] n : ℝ))
        ≤ 1 - gRoot m r ^ (j + 1) := by
  obtain ⟨hx1, hx2, -⟩ := gRoot_spec (m := m) hr
  have hx0 : (0 : ℝ) < gRoot m r := by linarith
  have hx1' : (0 : ℝ) < 1 - gRoot m r := by linarith
  induction j with
  | zero =>
    obtain ⟨h1, h2⟩ := wy_odd_bounds (betaG m r) hn
    rw [betaG_div_sub_one hr] at h1 h2
    simp only [pow_zero, mul_one, zero_add, pow_one, Function.iterate_one]
    constructor
    · linarith
    · nlinarith
  | succ j ih =>
    obtain ⟨ih1, ih2⟩ := ih fun i hi1 hi2 => heven i hi1 (by omega)
    have hv := heven (j + 1) (by omega) le_rfl
    obtain ⟨h1, h2⟩ := wy_even_bounds (betaG m r) hv
    rw [show betaG m r / 2 = gRoot m r by unfold betaG; ring] at h1 h2
    rw [Function.iterate_succ_apply']
    have p1 := mul_lt_mul_of_pos_left ih1 hx0
    have p2 := mul_le_mul_of_nonneg_left h2.le hx1'.le
    have p3 := mul_le_mul_of_nonneg_left ih2 hx0.le
    constructor
    · rw [pow_succ]; nlinarith
    · rw [pow_succ, pow_succ]; nlinarith

/-- **(ratified, mirror identity).**  If `n` is odd and `W′(n), …, W′ᵐ(n)` are even, then
`W′^{m+1}(n) = r(n + 1) − 1`; for every `n ∈ ℤ`.  Paper proof (sandwich): `n = 2k − 1`,
`v_1 = ⌈kα⌉ − 1 ∈ [y − 1, y)` with `y = A(n + 1)`, and each even step `v ↦ ⌊xv⌋` satisfies
`xv − 1 < ⌊xv⌋ ≤ xv`.  So `v_{m+1} < xᵐ y = r(n + 1)` and
`v_{m+1} > xᵐ(y − 1) − Σ_{i<m} xⁱ = r(n + 1) − Σ_{i=0}^{m} xⁱ > r(n + 1) − 2`. -/
theorem wy_iterate_eq_of_even_run_mirror (hr : 2 ≤ r) {n : ℤ} (hn : n % 2 = 1)
    (heven : ∀ i : ℕ, 1 ≤ i → i ≤ m → (wy (betaG m r))^[i] n % 2 = 0) :
    (wy (betaG m r))^[m + 1] n = r * (n + 1) - 1 := by
  obtain ⟨hx1, hx2, hx⟩ := gRoot_spec (m := m) hr
  obtain ⟨h1, h2⟩ := run_sandwich_mirror hr hn m heven
  rw [half_alphaG_mul_pow hr] at h1 h2
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hlt : 1 - gRoot m r ^ (m + 1) < 2 * (1 - gRoot m r) := by rw [hx]; nlinarith
  have hup : (((wy (betaG m r))^[m + 1] n : ℤ) : ℝ) < ((r * (n + 1) : ℤ) : ℝ) := by
    push_cast; linarith
  have hlo : ((r * (n + 1) - 2 : ℤ) : ℝ) < (((wy (betaG m r))^[m + 1] n : ℤ) : ℝ) := by
    push_cast; nlinarith
  have a := Int.cast_lt.1 hup
  have b := Int.cast_lt.1 hlo
  omega

end Identity

/-! ## The parity engine for the density (§7)

Along a run, the parities of `W(n), W²(n), …` are read off the phases `ψ_l = {k·A·xˡ}`
(`n = 2k`): `N₀ = ⌊2ψ₀⌋`, `N_{l+1} = ⌊2ψ_{l+1} + x(ρ + N_l − 2ψ_l)⌋` (`Nf`), with `ρ` the run
parity.  Translating `ψ_i` by `1/2` flips `N_i` by one and fixes every other `N_l`
(`Nf_update`), so every word cylinder on `|I|` coordinates has volume `2^{−|I|}`
(`volume_cyl`); the engine is bounded, its level sets are convex, so cylinders have null
frontier (`volume_frontier_cyl`). -/

namespace Engine

open MeasureTheory

/-- Parity engine: `N₀ = ⌊2ψ₀⌋`, `N_{l+1} = ⌊2ψ_{l+1} + x(ρ + N_l − 2ψ_l)⌋`. -/
noncomputable def Nf (x : ℝ) (ρ : ℤ) (ψ : ℕ → ℝ) : ℕ → ℤ
  | 0 => ⌊2 * ψ 0⌋
  | l + 1 => ⌊2 * ψ (l + 1) + x * (ρ + Nf x ρ ψ l - 2 * ψ l)⌋

/-- Extend `ψ : Fin m → ℝ` by `0`. -/
noncomputable def ext {m : ℕ} (ψ : Fin m → ℝ) (l : ℕ) : ℝ := if h : l < m then ψ ⟨l, h⟩ else 0

/-- Shifting coordinate `i` by `t/2` shifts `N_i` by `t` and leaves the other `N_l`. -/
lemma Nf_update (x : ℝ) (ρ : ℤ) (ψ : ℕ → ℝ) (i : ℕ) (t : ℤ) (l : ℕ) :
    Nf x ρ (Function.update ψ i (ψ i + t / 2)) l = Nf x ρ ψ l + if l = i then t else 0 := by
  induction l with
  | zero =>
    simp only [Nf]
    by_cases hi : 0 = i
    · subst hi
      rw [Function.update_self, if_pos rfl, show 2 * (ψ 0 + t / 2) = 2 * ψ 0 + t by ring,
        Int.floor_add_intCast]
    · rw [Function.update_of_ne hi, if_neg hi, add_zero]
  | succ l ih =>
    simp only [Nf]
    rw [ih]
    by_cases h1 : l + 1 = i
    · subst h1
      rw [Function.update_self, Function.update_of_ne (by omega), if_neg (by omega), if_pos rfl,
        add_zero, show 2 * (ψ (l + 1) + t / 2) + x * (ρ + Nf x ρ ψ l - 2 * ψ l) =
          2 * ψ (l + 1) + x * (ρ + Nf x ρ ψ l - 2 * ψ l) + t by ring, Int.floor_add_intCast]
    · rw [Function.update_of_ne h1, if_neg h1, add_zero]
      by_cases h2 : l = i
      · subst h2
        rw [Function.update_self, if_pos rfl]
        congr 1
        push_cast
        ring
      · rw [Function.update_of_ne h2, if_neg h2, add_zero]

/-- The unit cube `[0, 1)^m`. -/
def cube (m : ℕ) : Set (Fin m → ℝ) := Set.univ.pi fun _ => Set.Ico (0 : ℝ) 1

lemma ext_add_single {m : ℕ} (ψ : Fin m → ℝ) (i : Fin m) :
    ext (Pi.single i (1 / 2 : ℝ) + ψ) =
      Function.update (ext ψ) i (ext ψ i + ((1 : ℤ) : ℝ) / 2) := by
  funext l
  unfold ext
  by_cases hl : l < m
  · rw [dif_pos hl]
    by_cases hli : l = (i : ℕ)
    · subst hli
      rw [Function.update_self, dif_pos i.2]
      simp
      ring
    · rw [Function.update_of_ne hli, dif_pos hl]
      have : (⟨l, hl⟩ : Fin m) ≠ i := fun h => hli (by rw [← h])
      simp [this]
  · rw [dif_neg hl, Function.update_of_ne (by omega), dif_neg hl]

lemma measurable_Nf (x : ℝ) (ρ : ℤ) (m : ℕ) (l : ℕ) :
    Measurable fun ψ : Fin m → ℝ => Nf x ρ (ext ψ) l := by
  have he : ∀ l, Measurable fun ψ : Fin m → ℝ => ext ψ l := by
    intro l
    unfold ext
    by_cases hl : l < m
    · simp only [dif_pos hl]; exact measurable_pi_apply _
    · simp only [dif_neg hl]; exact measurable_const
  induction l with
  | zero => exact ((he 0).const_mul 2).floor
  | succ l ih =>
    simp only [Nf]
    have hc : Measurable fun ψ : Fin m → ℝ => (Nf x ρ (ext ψ) l : ℝ) :=
      (Measurable.of_discrete (f := fun z : ℤ => (z : ℝ))).comp ih
    exact (((he (l + 1)).const_mul 2).add
      (((measurable_const.add hc).sub ((he l).const_mul 2)).const_mul x)).floor

/-- Word cylinders: `N_l ≡ p_l (mod 2)` for `l ∈ I`. -/
def cyl (x : ℝ) (ρ : ℤ) (m : ℕ) (I : Finset ℕ) (p : ℕ → ℤ) : Set (Fin m → ℝ) :=
  cube m ∩ ⋂ l ∈ I, {ψ | (Nf x ρ (ext ψ) l - p l) % 2 = 0}

lemma mem_cyl {x : ℝ} {ρ : ℤ} {m : ℕ} {I : Finset ℕ} {p : ℕ → ℤ} {ψ : Fin m → ℝ} :
    ψ ∈ cyl x ρ m I p ↔ ψ ∈ cube m ∧ ∀ l ∈ I, (Nf x ρ (ext ψ) l - p l) % 2 = 0 := by
  simp [cyl]

lemma measurableSet_cyl (x : ℝ) (ρ : ℤ) (m : ℕ) (I : Finset ℕ) (p : ℕ → ℤ) :
    MeasurableSet (cyl x ρ m I p) := by
  refine MeasurableSet.inter (MeasurableSet.univ_pi fun _ => measurableSet_Ico) ?_
  refine Finset.measurableSet_biInter I fun l _ => ?_
  exact measurable_Nf x ρ m l (MeasurableSet.of_discrete (s := {z : ℤ | (z - p l) % 2 = 0}))

lemma Nf_ext_add (x : ℝ) (ρ : ℤ) {m : ℕ} (φ : Fin m → ℝ) (i : Fin m) (l : ℕ) :
    Nf x ρ (ext (Pi.single i (1 / 2 : ℝ) + φ)) l = Nf x ρ (ext φ) l + if l = i then 1 else 0 := by
  rw [ext_add_single, Nf_update]

lemma mem_cube {m : ℕ} {ψ : Fin m → ℝ} : ψ ∈ cube m ↔ ∀ j, 0 ≤ ψ j ∧ ψ j < 1 := by
  simp [cube]

/-- `φ ∈ [0,1)^m` with `φ_i < 1/2` iff its half-translate is in the cube with coordinate
`≥ 1/2`. -/
lemma cube_add_single_iff {m : ℕ} (φ : Fin m → ℝ) (ii : Fin m) :
    (Pi.single ii (1 / 2 : ℝ) + φ ∈ cube m ∧
        ¬ (Pi.single ii (1 / 2 : ℝ) + φ : Fin m → ℝ) ii < 1 / 2) ↔
      (φ ∈ cube m ∧ φ ii < 1 / 2) := by
  have h1 : (Pi.single ii (1 / 2 : ℝ) + φ : Fin m → ℝ) ii = φ ii + 1 / 2 := by simp; ring
  have h2 : ∀ j, j ≠ ii → (Pi.single ii (1 / 2 : ℝ) + φ : Fin m → ℝ) j = φ j := by
    intro j hj; simp [hj]
  rw [mem_cube, mem_cube, h1]
  constructor
  · rintro ⟨hc, hn⟩
    refine ⟨fun j => ?_, by have := (hc ii).2; rw [h1] at this; linarith⟩
    by_cases hj : j = ii
    · subst hj; have := hc j; rw [h1] at this; constructor <;> linarith
    · rw [← h2 j hj]; exact hc j
  · rintro ⟨hc, hlt⟩
    refine ⟨fun j => ?_, by linarith [(hc ii).1]⟩
    by_cases hj : j = ii
    · subst hj; rw [h1]; constructor <;> linarith [hc j]
    · rw [h2 j hj]; exact hc j

/-- The half-translation in coordinate `i` swaps the two parities of `N_i`. -/
lemma volume_cyl_flip (x : ℝ) (ρ : ℤ) (m : ℕ) (J : Finset ℕ) (p : ℕ → ℤ) {i : ℕ} (hi : i < m) :
    volume (cyl x ρ m J (Function.update p i (p i + 1))) = volume (cyl x ρ m J p) := by
  set ii : Fin m := ⟨i, hi⟩
  set v : Fin m → ℝ := Pi.single ii (1 / 2 : ℝ)
  set L : Set (Fin m → ℝ) := {ψ | ψ ii < 1 / 2}
  have hL : MeasurableSet L := measurableSet_lt (measurable_pi_apply ii) measurable_const
  have hpl : ∀ l, Function.update p i (p i + 1) l = p l + if l = i then 1 else 0 := by
    intro l
    by_cases h : l = i
    · subst h; simp
    · simp [h]
  have key : ∀ φ : Fin m → ℝ, ∀ l, Nf x ρ (ext (v + φ)) l = Nf x ρ (ext φ) l +
      if l = i then 1 else 0 := fun φ l => Nf_ext_add x ρ φ ii l
  have par1 : ∀ φ : Fin m → ℝ, (∀ l ∈ J, (Nf x ρ (ext (v + φ)) l - p l) % 2 = 0) ↔
      ∀ l ∈ J, (Nf x ρ (ext φ) l - Function.update p i (p i + 1) l) % 2 = 0 := by
    intro φ
    refine forall₂_congr fun l _ => ?_
    rw [key, hpl]
    split_ifs <;> omega
  have par2 : ∀ φ : Fin m → ℝ,
      (∀ l ∈ J, (Nf x ρ (ext (v + φ)) l - Function.update p i (p i + 1) l) % 2 = 0) ↔
      ∀ l ∈ J, (Nf x ρ (ext φ) l - p l) % 2 = 0 := by
    intro φ
    refine forall₂_congr fun l _ => ?_
    rw [key, hpl]
    split_ifs <;> omega
  have ha : cyl x ρ m J (Function.update p i (p i + 1)) ∩ L =
      (fun ψ => v + ψ) ⁻¹' (cyl x ρ m J p \ L) := by
    ext ψ
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_sdiff, mem_cyl, L,
      Set.mem_ofPred_eq, par1]
    have := cube_add_single_iff ψ ii
    tauto
  have hb : cyl x ρ m J (Function.update p i (p i + 1)) \ L =
      (fun ψ => -v + ψ) ⁻¹' (cyl x ρ m J p ∩ L) := by
    ext ψ
    have hψ : ψ = v + (-v + ψ) := by abel
    conv_lhs => rw [hψ]
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_sdiff, mem_cyl, L,
      Set.mem_ofPred_eq, par2]
    have := cube_add_single_iff (-v + ψ) ii
    tauto
  rw [← measure_inter_add_sdiff _ hL, ha, hb, measure_preimage_add, measure_preimage_add,
    add_comm, measure_inter_add_sdiff _ hL]


lemma volume_cube (m : ℕ) : volume (cube m) = 1 := by
  rw [cube, Real.volume_pi_Ico]
  simp

/-- **Fair coins.**  Each word cylinder on `|I|` coordinates has volume `2^{−|I|}`. -/
lemma volume_cyl (x : ℝ) (ρ : ℤ) (m : ℕ) (I : Finset ℕ) (hI : ∀ l ∈ I, l < m) (p : ℕ → ℤ) :
    volume (cyl x ρ m I p) = 2⁻¹ ^ I.card := by
  induction I using Finset.induction_on generalizing p with
  | empty =>
    rw [Finset.card_empty, pow_zero, ← volume_cube m]
    congr 1
    ext ψ
    simp [mem_cyl]
  | insert i I hiI ih =>
    have hi : i < m := hI i (Finset.mem_insert_self i I)
    have hI' : ∀ l ∈ I, l < m := fun l hl => hI l (Finset.mem_insert_of_mem hl)
    set p' := Function.update p i (p i + 1)
    have hsplit : cyl x ρ m I p = cyl x ρ m (insert i I) p ∪ cyl x ρ m (insert i I) p' := by
      ext ψ
      simp only [Set.mem_union, mem_cyl, Finset.mem_insert, forall_eq_or_imp]
      have hp' : ∀ l ∈ I, p' l = p l := fun l hl =>
        Function.update_of_ne (fun h => hiI (by rw [← h]; exact hl)) _ _
      have hpi : p' i = p i + 1 := by simp [p']
      constructor
      · rintro ⟨hc, hJ⟩
        by_cases h : (Nf x ρ (ext ψ) i - p i) % 2 = 0
        · exact Or.inl ⟨hc, h, hJ⟩
        · refine Or.inr ⟨hc, by rw [hpi]; omega, fun l hl => by rw [hp' l hl]; exact hJ l hl⟩
      · rintro (⟨hc, -, hJ⟩ | ⟨hc, -, hJ⟩)
        · exact ⟨hc, hJ⟩
        · exact ⟨hc, fun l hl => by have := hJ l hl; rwa [hp' l hl] at this⟩
    have hdisj : Disjoint (cyl x ρ m (insert i I) p) (cyl x ρ m (insert i I) p') := by
      rw [Set.disjoint_left]
      intro ψ h1 h2
      rw [mem_cyl] at h1 h2
      have a := h1.2 i (Finset.mem_insert_self i I)
      have b := h2.2 i (Finset.mem_insert_self i I)
      simp only [p', Function.update_self] at b
      omega
    have hflip := volume_cyl_flip x ρ m (insert i I) p hi
    have h2 := ih hI' p
    rw [hsplit, measure_union hdisj (measurableSet_cyl _ _ _ _ _), hflip, ← two_mul] at h2
    rw [Finset.card_insert_of_notMem hiI, pow_succ', ← h2, ← mul_assoc,
      ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]

/-- The engine stays bounded on the cube: `−4 < N_l − 2ψ_l < 3`. -/
lemma Nf_sub_bound {x : ℝ} (hx0 : 0 < x) (hx1 : x < 3 / 4) {ρ : ℤ} (hρ : ρ = 0 ∨ ρ = 1)
    (ψ : ℕ → ℝ) (l : ℕ) :
    -4 < (Nf x ρ ψ l : ℝ) - 2 * ψ l ∧ (Nf x ρ ψ l : ℝ) - 2 * ψ l < 3 := by
  induction l with
  | zero =>
    simp only [Nf]
    have := Int.floor_le (2 * ψ 0)
    have := Int.lt_floor_add_one (2 * ψ 0)
    constructor <;> linarith
  | succ l ih =>
    simp only [Nf]
    set h := x * (ρ + Nf x ρ ψ l - 2 * ψ l)
    have hρ' : (0 : ℝ) ≤ ρ ∧ (ρ : ℝ) ≤ 1 := by
      rcases hρ with rfl | rfl <;> norm_num
    have hh : -3 < h ∧ h < 3 := by
      obtain ⟨a, b⟩ := ih
      constructor
      · have : (-4 : ℝ) < ρ + Nf x ρ ψ l - 2 * ψ l := by linarith
        nlinarith
      · have : (ρ : ℝ) + Nf x ρ ψ l - 2 * ψ l < 4 := by linarith
        nlinarith
    have := Int.floor_le (2 * ψ (l + 1) + h)
    have := Int.lt_floor_add_one (2 * ψ (l + 1) + h)
    constructor <;> linarith

lemma ext_mem {m : ℕ} {ψ : Fin m → ℝ} (hψ : ψ ∈ cube m) (l : ℕ) : 0 ≤ ext ψ l ∧ ext ψ l < 1 := by
  unfold ext
  split_ifs with h
  · exact (mem_cube.1 hψ) _
  · norm_num

lemma ext_combo {m : ℕ} (ψ φ : Fin m → ℝ) (a b : ℝ) (l : ℕ) :
    ext (a • ψ + b • φ) l = a * ext ψ l + b * ext φ l := by
  unfold ext
  split_ifs <;> simp

/-- Level sets of the engine are convex. -/
lemma convex_level (x : ℝ) (ρ : ℤ) (m : ℕ) (n : ℕ → ℤ) :
    Convex ℝ {ψ : Fin m → ℝ | ψ ∈ cube m ∧ ∀ l < m, Nf x ρ (ext ψ) l = n l} := by
  intro ψ ⟨hψc, hψ⟩ φ ⟨hφc, hφ⟩ a b ha hb hab
  have hcube : Convex ℝ (cube m) := convex_pi fun _ _ => convex_Ico 0 1
  refine ⟨hcube hψc hφc ha hb hab, ?_⟩
  have comb : ∀ (N : ℤ) (u w : ℝ), ⌊u⌋ = N → ⌊w⌋ = N → ⌊a * u + b * w⌋ = N := by
    intro N u w hu hw
    rw [Int.floor_eq_iff] at hu hw ⊢
    obtain ⟨hu1, hu2⟩ := hu
    obtain ⟨hw1, hw2⟩ := hw
    have e1 := mul_le_mul_of_nonneg_left hu1 ha
    have e2 := mul_le_mul_of_nonneg_left hw1 hb
    have s1 : a * (N : ℝ) + b * N = N := by rw [← add_mul, hab, one_mul]
    have s2 : a * ((N : ℝ) + 1) + b * (N + 1) = N + 1 := by rw [← add_mul, hab, one_mul]
    refine ⟨by linarith, ?_⟩
    rcases ha.eq_or_lt with h0 | h0
    · subst h0
      have : b = 1 := by linarith
      subst this
      linarith
    · have e3 := mul_lt_mul_of_pos_left hu2 h0
      have e4 := mul_le_mul_of_nonneg_left hw2.le hb
      linarith
  intro l hl
  induction l with
  | zero =>
    have h1 := hψ 0 hl
    have h2 := hφ 0 hl
    simp only [Nf] at h1 h2 ⊢
    rw [ext_combo]
    rw [show 2 * (a * ext ψ 0 + b * ext φ 0) = a * (2 * ext ψ 0) + b * (2 * ext φ 0) by ring]
    exact comb _ _ _ h1 h2
  | succ l ih =>
    have h1 := hψ (l + 1) hl
    have h2 := hφ (l + 1) hl
    simp only [Nf] at h1 h2 ⊢
    rw [ih (by omega), ext_combo, ext_combo]
    rw [hψ l (by omega)] at h1
    rw [hφ l (by omega)] at h2
    convert comb _ _ _ h1 h2 using 2
    linear_combination (-(x * ((ρ : ℝ) + n l))) * hab

lemma frontier_iUnion_subset_of_finite {X ι : Type*} [TopologicalSpace X] [Finite ι]
    (s : ι → Set X) : frontier (⋃ i, s i) ⊆ ⋃ i, frontier (s i) := by
  intro y hy
  rw [frontier, closure_iUnion_of_finite, Set.mem_sdiff, Set.mem_iUnion] at hy
  obtain ⟨⟨i, hi⟩, hn⟩ := hy
  exact Set.mem_iUnion.2 ⟨i, hi, fun h => hn (interior_mono (Set.subset_iUnion s i) h)⟩

/-- **Null frontier.**  A word cylinder is a finite union of convex pieces (level sets of the
bounded engine), so its frontier is Lebesgue-null. -/
lemma volume_frontier_cyl {x : ℝ} (hx0 : 0 < x) (hx1 : x < 3 / 4) {ρ : ℤ} (hρ : ρ = 0 ∨ ρ = 1)
    (m : ℕ) (I : Finset ℕ) (hI : ∀ l ∈ I, l < m) (p : ℕ → ℤ) :
    volume (frontier (cyl x ρ m I p)) = 0 := by
  set nf : (Fin m → Fin 8) → ℕ → ℤ := fun g l => if h : l < m then (g ⟨l, h⟩ : ℤ) - 3 else 0
  set P : (Fin m → Fin 8) → Set (Fin m → ℝ) := fun g =>
    cyl x ρ m I p ∩ {ψ | ψ ∈ cube m ∧ ∀ l < m, Nf x ρ (ext ψ) l = nf g l}
  have hcover : cyl x ρ m I p = ⋃ g, P g := by
    ext ψ
    simp only [Set.mem_iUnion, P, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro hψ
      have hc := (mem_cyl.1 hψ).1
      have hb : ∀ l, -3 ≤ Nf x ρ (ext ψ) l ∧ Nf x ρ (ext ψ) l ≤ 4 := by
        intro l
        obtain ⟨a, b⟩ := Nf_sub_bound hx0 hx1 hρ (ext ψ) l
        obtain ⟨c, d⟩ := ext_mem hc l
        have h1 : (-4 : ℝ) < Nf x ρ (ext ψ) l := by linarith
        have h2 : (Nf x ρ (ext ψ) l : ℝ) < 5 := by linarith
        constructor
        · have : (-4 : ℤ) < Nf x ρ (ext ψ) l := by exact_mod_cast h1
          omega
        · have : Nf x ρ (ext ψ) l < (5 : ℤ) := by exact_mod_cast h2
          omega
      refine ⟨fun j => ⟨(Nf x ρ (ext ψ) j + 3).toNat, by have := hb j; omega⟩, hψ, hc,
        fun l hl => ?_⟩
      simp only [nf, dif_pos hl]
      have := hb l
      omega
    · rintro ⟨g, hψ, -⟩
      exact hψ
  have hconv : ∀ g, Convex ℝ (P g) := by
    intro g ψ ⟨hψ, hψl⟩ φ ⟨hφ, hφl⟩ a b ha hb hab
    have hχ := convex_level x ρ m (nf g) hψl hφl ha hb hab
    refine ⟨mem_cyl.2 ⟨hχ.1, fun l hl => ?_⟩, hχ⟩
    rw [hχ.2 l (hI l hl), ← hψl.2 l (hI l hl)]
    exact (mem_cyl.1 hψ).2 l hl
  refine measure_mono_null (hcover ▸ frontier_iUnion_subset_of_finite P) ?_
  exact measure_iUnion_null fun g => (hconv g).addHaar_frontier volume

end Engine

/-! ## The density: phases, word cylinders, and the generic count -/

section Density

open Engine MeasureTheory

variable {m r : ℕ}

/-- The Weyl frequencies `θ_i = A xⁱ`, `i < m`. -/
noncomputable def theta (m r : ℕ) : Fin m → ℝ := fun i => alphaG m r / 2 * gRoot m r ^ (i : ℕ)

/-- The phase vector `Ψ(k) = ({k θ_i})_{i < m}`. -/
noncomputable def phase (m r : ℕ) (k : ℕ) : Fin m → ℝ :=
  fun i => Int.fract ((k : ℝ) * theta m r i)

lemma ext_phase (k : ℕ) {l : ℕ} (hl : l < m) :
    ext (phase m r k) l = Int.fract ((k : ℝ) * (alphaG m r / 2 * gRoot m r ^ l)) := by
  simp [ext, hl, phase, theta]

/-- **Run lemma.**  If `W(n₀) = ⌊2kA⌋` and `W(n₀), …, Wˡ(n₀)` have parity `ρ` (`l < m`), then
`W^{l+1}(n₀) = N_l(Ψ k) + 2⌊k A xˡ⌋`. -/
lemma run_Nf (γ : ℝ) (ρ : ℤ) (hpos : ∀ n, 0 < wy γ n ↔ 0 < n)
    (hstep : 2 ≤ m → ∀ v : ℤ, 0 < v → v % 2 = ρ → wy γ v = ⌊gRoot m r * v + gRoot m r * ρ⌋)
    (k : ℕ) {n₀ : ℤ} (hn₀ : 0 < n₀)
    (hfirst : 1 ≤ m → wy γ n₀ = ⌊2 * (k : ℝ) * (alphaG m r / 2)⌋) :
    ∀ l, l < m → (∀ i : ℕ, 1 ≤ i → i ≤ l → (wy γ)^[i] n₀ % 2 = ρ) →
      (wy γ)^[l + 1] n₀ = Nf (gRoot m r) ρ (ext (phase m r k)) l +
        2 * ⌊(k : ℝ) * (alphaG m r / 2 * gRoot m r ^ l)⌋ := by
  set x := gRoot m r
  set A := alphaG m r / 2
  intro l
  induction l with
  | zero =>
    intro hl _
    rw [Function.iterate_one, hfirst (by omega), Nf, ext_phase k hl]
    set u := (k : ℝ) * (A * x ^ 0)
    have : 2 * (k : ℝ) * A = 2 * Int.fract u + ((2 * ⌊u⌋ : ℤ) : ℝ) := by
      simp only [u, pow_zero, mul_one, Int.fract]; push_cast; ring
    rw [this, Int.floor_add_intCast]
  | succ l ih =>
    intro hl hpar
    have hv := ih (by omega) fun i h1 h2 => hpar i h1 (by omega)
    have hvp : (wy γ)^[l + 1] n₀ % 2 = ρ := hpar (l + 1) (by omega) le_rfl
    have hvpos : 0 < (wy γ)^[l + 1] n₀ := by
      clear hv hvp ih hpar
      induction (l + 1) with
      | zero => exact hn₀
      | succ i ihi => rw [Function.iterate_succ_apply', hpos]; exact ihi
    rw [Function.iterate_succ_apply', hstep (by omega) _ hvpos hvp, hv]
    simp only [Nf]
    rw [ext_phase k hl, ext_phase k (by omega)]
    set u := (k : ℝ) * (A * x ^ l)
    set u' := (k : ℝ) * (A * x ^ (l + 1))
    have hu' : u' = x * u := by simp only [u, u']; ring
    have : x * (((Nf x ρ (ext (phase m r k)) l + 2 * ⌊u⌋ : ℤ)) : ℝ) + x * ρ =
        2 * Int.fract u' + x * (ρ + Nf x ρ (ext (phase m r k)) l - 2 * Int.fract u) +
          ((2 * ⌊u'⌋ : ℤ) : ℝ) := by
      simp only [Int.fract]; push_cast; rw [hu']; ring
    rw [this, Int.floor_add_intCast]

/-- The word cylinder of return word `j`: the first `j` run parities are `ρ` and (if `j < m`)
the next one is not. -/
def wordSet (m r : ℕ) (ρ : ℤ) (j : ℕ) : Set (Fin m → ℝ) :=
  cyl (gRoot m r) ρ m (Finset.range (min (j + 1) m)) (Function.update (fun _ => ρ) j (ρ + 1))

lemma phase_mem_cube (k : ℕ) : phase m r k ∈ cube m :=
  mem_cube.2 fun _ => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

lemma wordSet_disjoint (ρ : ℤ) {j j' : ℕ} (hjj : j < j') (hj' : j' ≤ m) :
    Disjoint (wordSet m r ρ j) (wordSet m r ρ j') := by
  rw [Set.disjoint_left]
  intro ψ h1 h2
  have a := (mem_cyl.1 h1).2 j (Finset.mem_range.2 (by omega))
  have b := (mem_cyl.1 h2).2 j (Finset.mem_range.2 (by omega))
  rw [Function.update_self] at a
  rw [Function.update_of_ne (by omega)] at b
  omega

section Generic

variable {σ : Equiv.Perm ℤ} {γ : ℝ} {S Φ : Set ℤ} {ρ : ℤ}

lemma perm_pow_apply (hσ : ∀ n, σ n = wy γ n) (i : ℕ) (n : ℤ) : (σ ^ i) n = (wy γ)^[i] n := by
  rw [Equiv.Perm.coe_pow]
  congr 1
  funext n
  exact hσ n

/-- The return word of `n₀` is read off the phase of `k`. -/
lemma phase_mem_wordSet (hσ : ∀ n, σ n = wy γ n) (hρ : ρ = 0 ∨ ρ = 1)
    (hS : ∀ n, n ∈ S ↔ n % 2 ≠ ρ) (h : Hyp σ S Φ (m + 1))
    (hstep : 2 ≤ m → ∀ v : ℤ, 0 < v → v % 2 = ρ → wy γ v = ⌊gRoot m r * v + gRoot m r * ρ⌋)
    (k : ℕ) {n₀ : ℤ} (hS₀ : n₀ ∈ S) (hn₀ : 0 < n₀) (hΦ₀ : n₀ ∉ Φ)
    (hfirst : 1 ≤ m → wy γ n₀ = ⌊2 * (k : ℝ) * (alphaG m r / 2)⌋) :
    phase m r k ∈ wordSet m r ρ (returnTime σ S n₀ - 1) := by
  obtain ⟨h1, hT, hRS, -, hint⟩ := returnTime_spec h hS₀ hn₀ hΦ₀
  set τ := returnTime σ S n₀
  have hpos : ∀ n, 0 < wy γ n ↔ 0 < n := fun n => by rw [← hσ]; exact h.pos_iff n
  have hodd : ∀ i : ℕ, 1 ≤ i → i < τ → (wy γ)^[i] n₀ % 2 = ρ := by
    intro i hi1 hi2
    have := hint i hi1 hi2
    rw [hS, perm_pow_apply hσ, not_not] at this
    exact this
  refine mem_cyl.2 ⟨phase_mem_cube k, fun l hl => ?_⟩
  rw [Finset.mem_range] at hl
  have hlm : l < m := by omega
  have hrun := run_Nf γ ρ hpos hstep k hn₀ hfirst l hlm fun i hi1 hi2 => hodd i hi1 (by omega)
  by_cases hlτ : l = τ - 1
  · rw [hlτ, Function.update_self]
    have hR : (wy γ)^[τ] n₀ % 2 ≠ ρ := by
      rw [returnMap, perm_pow_apply hσ, hS] at hRS; exact hRS
    rw [show τ = l + 1 by omega, hrun] at hR
    rw [← hlτ]
    rcases hρ with rfl | rfl <;> omega
  · rw [Function.update_of_ne hlτ]
    have := hodd (l + 1) (by omega) (by omega)
    rw [hrun] at this
    omega

/-- `returnTime = j + 1` iff the phase lies in the `j`-th word cylinder. -/
lemma returnTime_eq_iff (hσ : ∀ n, σ n = wy γ n) (hρ : ρ = 0 ∨ ρ = 1)
    (hS : ∀ n, n ∈ S ↔ n % 2 ≠ ρ) (h : Hyp σ S Φ (m + 1))
    (hstep : 2 ≤ m → ∀ v : ℤ, 0 < v → v % 2 = ρ → wy γ v = ⌊gRoot m r * v + gRoot m r * ρ⌋)
    (k : ℕ) {n₀ : ℤ} (hS₀ : n₀ ∈ S) (hn₀ : 0 < n₀) (hΦ₀ : n₀ ∉ Φ)
    (hfirst : 1 ≤ m → wy γ n₀ = ⌊2 * (k : ℝ) * (alphaG m r / 2)⌋) {j : ℕ} (hj : j ≤ m) :
    returnTime σ S n₀ = j + 1 ↔ phase m r k ∈ wordSet m r ρ j := by
  have hmem := phase_mem_wordSet hσ hρ hS h hstep k hS₀ hn₀ hΦ₀ hfirst
  obtain ⟨h1, hT, -⟩ := returnTime_spec h hS₀ hn₀ hΦ₀
  constructor
  · intro he; rw [he] at hmem; simpa using hmem
  · intro hw
    by_contra hne
    rcases lt_or_gt_of_ne (show returnTime σ S n₀ - 1 ≠ j by omega) with hlt | hgt
    · exact Set.disjoint_left.1 (wordSet_disjoint ρ hlt hj) hmem hw
    · exact Set.disjoint_left.1 (wordSet_disjoint ρ hgt (by omega)) hw hmem

end Generic

lemma volume_wordSet (ρ : ℤ) (j : ℕ) :
    (volume (wordSet m r ρ j ∩ Set.univ.pi fun _ => Set.Ico (0 : ℝ) 1)).toReal =
      (1 / 2 : ℝ) ^ min (j + 1) m := by
  have hsub : wordSet m r ρ j ⊆ Set.univ.pi fun _ => Set.Ico (0 : ℝ) 1 :=
    fun ψ hψ => (mem_cyl.1 hψ).1
  rw [Set.inter_eq_left.2 hsub, wordSet, volume_cyl _ _ _ _ (fun l hl => by
    rw [Finset.mem_range] at hl; omega), Finset.card_range, ENNReal.toReal_pow,
    ENNReal.toReal_inv]
  norm_num

lemma measurableSet_wordSet (ρ : ℤ) (j : ℕ) : MeasurableSet (wordSet m r ρ j) :=
  measurableSet_cyl _ _ _ _ _

lemma volume_frontier_wordSet (hr : 2 ≤ r) {ρ : ℤ} (hρ : ρ = 0 ∨ ρ = 1) (j : ℕ) :
    volume (frontier (wordSet m r ρ j)) = 0 := by
  obtain ⟨hx1, hx2, -⟩ := gRoot_spec (m := m) hr
  exact volume_frontier_cyl (by linarith) hx2 hρ m _ (fun l hl => by
    rw [Finset.mem_range] at hl; omega) _

section Generic2

variable {σ : Equiv.Perm ℤ} {γ : ℝ} {S Φ : Set ℤ} {ρ : ℤ}

open Classical in
/-- **Generic return-count density.**  Under Weyl, if the return word of `n₀(k)` is read off
the phase of `k`, and the first return is within `4` of `2k·A·xʲ` on word `j`, then
`#{s ≤ X : R(s) ≤ X}/X → Σ_j 2^{−min(j+1, m)}/(α xʲ)`. -/
theorem tendsto_returnCount_div (hr : 2 ≤ r)
    (hWd : ∀ j, j ≤ m → Tendsto (fun N : ℕ =>
      (((Finset.Icc 1 N).filter fun k : ℕ => phase m r k ∈ wordSet m r ρ j).card : ℝ) / N)
        atTop (𝓝 ((1 / 2 : ℝ) ^ min (j + 1) m)))
    (hσ : ∀ n, σ n = wy γ n) (hρ : ρ = 0 ∨ ρ = 1)
    (hS : ∀ n, n ∈ S ↔ n % 2 ≠ ρ) (h : Hyp σ S Φ (m + 1))
    (hstep : 2 ≤ m → ∀ v : ℤ, 0 < v → v % 2 = ρ → wy γ v = ⌊gRoot m r * v + gRoot m r * ρ⌋)
    (n₀ : ℕ → ℤ) (hn₀ : ∀ k, 1 ≤ k → n₀ k ∈ S ∧ 0 < n₀ k ∧ n₀ k ∉ Φ)
    (hfirst : 1 ≤ m → ∀ k, 1 ≤ k → wy γ (n₀ k) = ⌊2 * (k : ℝ) * (alphaG m r / 2)⌋)
    (hbound : ∀ k, 1 ≤ k → |(returnMap σ S (n₀ k) : ℝ) -
      2 * k * (alphaG m r / 2 * gRoot m r ^ (returnTime σ S (n₀ k) - 1))| < 4)
    (KX : ℕ → ℕ) (hcount : ∀ X, returnCount σ S Φ X =
      ((Finset.Icc 1 (KX X)).filter fun k => returnMap σ S (n₀ k) ≤ X).card)
    (hK : ∀ X k : ℕ, 4 * k ≤ X → k ≤ KX X) :
    Tendsto (fun X : ℕ => (returnCount σ S Φ X : ℝ) / X) atTop
      (𝓝 (∑ j ∈ Finset.range (m + 1),
        (1 / 2 : ℝ) ^ min (j + 1) m * (alphaG m r * gRoot m r ^ j)⁻¹)) := by
  classical
  obtain ⟨hx1, hx2, -⟩ := gRoot_spec (m := m) hr
  set x := gRoot m r
  set A := alphaG m r / 2
  set c : ℕ → ℝ := fun j => alphaG m r * x ^ j
  have hreq : A * x ^ m = r := half_alphaG_mul_pow (m := m) hr
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hc : ∀ j, j ≤ m → 4 ≤ c j := by
    intro j hj
    have hxj : x ^ m ≤ x ^ j := pow_le_pow_of_le_one (by linarith) (by linarith) hj
    have hA : 0 < A := by have := four_le_alphaG (m := m) hr; simp only [A]; linarith
    have : (2 : ℝ) * r ≤ c j := by
      simp only [c]
      rw [show alphaG m r = 2 * A by simp only [A]; ring, ← hreq]
      nlinarith [mul_le_mul_of_nonneg_left hxj hA.le]
    linarith
  have h2c : ∀ j (k : ℕ), 2 * (k : ℝ) * (A * x ^ j) = c j * k := by
    intro j k; simp only [c, A]; ring
  set Cnt : ℕ → ℕ → ℕ := fun j N =>
    ((Finset.Icc 1 N).filter fun k : ℕ => phase m r k ∈ wordSet m r ρ j).card
  set T : ℕ → ℕ → ℕ := fun j X => ((Finset.Icc 1 (KX X)).filter fun k =>
    returnTime σ S (n₀ k) = j + 1 ∧ returnMap σ S (n₀ k) ≤ X).card
  have hiff : ∀ k, 1 ≤ k → ∀ j, j ≤ m →
      (returnTime σ S (n₀ k) = j + 1 ↔ phase m r k ∈ wordSet m r ρ j) := by
    intro k hk j hj
    obtain ⟨a, b, d⟩ := hn₀ k hk
    exact returnTime_eq_iff hσ hρ hS h hstep k a b d (fun hm => hfirst hm k hk) hj
  have hsum : ∀ X, returnCount σ S Φ X = ∑ j ∈ Finset.range (m + 1), T j X := by
    intro X
    rw [hcount, Finset.card_eq_sum_card_fiberwise
      (f := fun k => returnTime σ S (n₀ k) - 1) (t := Finset.range (m + 1))]
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp only [T, Finset.filter_filter]
      congr 1
      refine Finset.filter_congr fun k hk => ?_
      obtain ⟨a, b, d⟩ := hn₀ k (Finset.mem_Icc.1 hk).1
      have := (returnTime_spec h a b d).1
      omega
    · intro k hk
      simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hk
      obtain ⟨a, b, d⟩ := hn₀ k hk.1.1
      have := (returnTime_spec h a b d).2.1
      simp only [Finset.coe_range, Set.mem_Iio]
      omega
  have hlo : ∀ j, j ≤ m → ∀ X : ℕ, Cnt j ⌊(c j)⁻¹ * X + -4 / c j⌋₊ ≤ T j X := by
    intro j hj X
    apply Finset.card_le_card
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk ⊢
    obtain ⟨⟨hk1, hk2⟩, hw⟩ := hk
    have hcj := hc j hj
    have hkr := (Nat.le_floor_iff' (by omega)).1 hk2
    have hck : c j * k ≤ X - 4 := by
      have := mul_le_mul_of_nonneg_left hkr (by linarith : (0 : ℝ) ≤ c j)
      rw [mul_add, ← mul_assoc, mul_inv_cancel₀ (by linarith), one_mul,
        mul_div_cancel₀ _ (by linarith)] at this
      linarith
    have hrt := (hiff k hk1 j hj).2 hw
    have hb := hbound k hk1
    rw [hrt, Nat.add_sub_cancel, h2c] at hb
    have hRX : (returnMap σ S (n₀ k) : ℝ) < X := by linarith [(abs_lt.1 hb).2]
    refine ⟨⟨hk1, hK X k ?_⟩, hrt, by exact_mod_cast hRX.le⟩
    have : (4 : ℝ) * k ≤ X := by
      have : (4 : ℝ) * k ≤ c j * k := by
        have : (0 : ℝ) ≤ k := by positivity
        nlinarith
      linarith
    exact_mod_cast this
  have hhi : ∀ j, j ≤ m → ∀ X : ℕ, T j X ≤ Cnt j ⌊(c j)⁻¹ * X + 4 / c j⌋₊ := by
    intro j hj X
    apply Finset.card_le_card
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk ⊢
    obtain ⟨⟨hk1, -⟩, hrt, hRX⟩ := hk
    have hcj := hc j hj
    refine ⟨⟨hk1, Nat.le_floor ?_⟩, (hiff k hk1 j hj).1 hrt⟩
    have hb := hbound k hk1
    rw [hrt, Nat.add_sub_cancel, h2c] at hb
    have hRX' : (returnMap σ S (n₀ k) : ℝ) ≤ X := by exact_mod_cast hRX
    have : c j * k < X + 4 := by linarith [(abs_lt.1 hb).1]
    rw [show (c j)⁻¹ * X + 4 / c j = (X + 4) / c j by field_simp, le_div_iff₀ (by linarith)]
    linarith
  have hlimT : ∀ j ∈ Finset.range (m + 1), Tendsto (fun X : ℕ => (T j X : ℝ) / X) atTop
      (𝓝 ((1 / 2 : ℝ) ^ min (j + 1) m * (alphaG m r * x ^ j)⁻¹)) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hcj := hc j (by omega)
    have hcpos : 0 < (c j)⁻¹ := inv_pos.2 (by linarith)
    have L1 := tendsto_comp_div (hWd j (by omega)) (tendsto_floor_linear hcpos (-4 / c j))
      (tendsto_floor_linear_div hcpos (-4 / c j))
    have L2 := tendsto_comp_div (hWd j (by omega)) (tendsto_floor_linear hcpos (4 / c j))
      (tendsto_floor_linear_div hcpos (4 / c j))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le L1 L2 (fun X => ?_) (fun X => ?_)
    · exact div_le_div_of_nonneg_right (Nat.cast_le.2 (hlo j (by omega) X)) (by positivity)
    · exact div_le_div_of_nonneg_right (Nat.cast_le.2 (hhi j (by omega) X)) (by positivity)
  refine (tendsto_finsetSum (Finset.range (m + 1)) hlimT).congr fun X => ?_
  simp only [hsum X, Nat.cast_sum, Finset.sum_div]

end Generic2

/-- `1, A, Ax, …, Ax^{m−1}` are `ℚ`-independent when `1, x, …, xᵐ` are (multiply by `xᵐ`,
`A xᵐ = r`). -/
lemma linearIndependent_theta (hr : 2 ≤ r)
    (hind : LinearIndependent ℚ fun i : Fin (m + 1) => gRoot m r ^ (i : ℕ)) :
    LinearIndependent ℚ (Fin.cons (1 : ℝ) (theta m r) : Fin (m + 1) → ℝ) := by
  have hreq := half_alphaG_mul_pow (m := m) hr
  rw [Fintype.linearIndependent_iff] at hind ⊢
  intro g hg
  rw [Fin.sum_univ_succ] at hg
  simp only [Fin.cons_zero, Fin.cons_succ, Rat.smul_def, mul_one, theta] at hg
  set g' : Fin (m + 1) → ℚ := Fin.snoc (fun i : Fin m => (r : ℚ) * g i.succ) (g 0)
  have h' : ∑ i, g' i • gRoot m r ^ (i : ℕ) = 0 := by
    rw [Fin.sum_univ_castSucc]
    simp only [g', Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last,
      Rat.smul_def]
    have : ∑ i : Fin m, (((r : ℚ) * g i.succ : ℚ) : ℝ) * gRoot m r ^ (i : ℕ) +
        ((g 0 : ℚ) : ℝ) * gRoot m r ^ m =
        gRoot m r ^ m * ((g 0 : ℝ) + ∑ i : Fin m, (g i.succ : ℝ) *
          (alphaG m r / 2 * gRoot m r ^ (i : ℕ))) := by
      rw [mul_add, Finset.mul_sum]
      rw [add_comm]
      congr 1
      · ring
      · refine Finset.sum_congr rfl fun i _ => ?_
        push_cast
        rw [← hreq]
        ring
    rw [this, hg, mul_zero]
  have hz := hind g' h'
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · have := hz (Fin.last m)
    simpa [g'] using this
  · have := hz (Fin.castSucc i)
    simp only [g', Fin.snoc_castSucc, mul_eq_zero, Nat.cast_eq_zero] at this
    rcases this with h0 | h0
    · omega
    · exact h0

open Classical in
/-- Weyl for the word cylinders. -/
lemma tendsto_wordCount (hr : 2 ≤ r) (hW : WeylEquidistributionMulti)
    (hind : LinearIndependent ℚ fun i : Fin (m + 1) => gRoot m r ^ (i : ℕ))
    {ρ : ℤ} (hρ : ρ = 0 ∨ ρ = 1) (j : ℕ) :
    Tendsto (fun N : ℕ =>
      (((Finset.Icc 1 N).filter fun k : ℕ => phase m r k ∈ wordSet m r ρ j).card : ℝ) / N)
        atTop (𝓝 ((1 / 2 : ℝ) ^ min (j + 1) m)) := by
  classical
  have := hW m (theta m r) (linearIndependent_theta hr hind) (wordSet m r ρ j)
    (measurableSet_wordSet ρ j) (volume_frontier_wordSet hr hρ j)
  rw [volume_wordSet] at this
  exact this

/-- The closed form of the density: `1/2 − Σ_j 2^{−min(j+1,m)}/(α xʲ) = (α − 2)/(2αβᵐ)`. -/
lemma density_sum_eq (hr : 2 ≤ r) :
    1 / 2 - ∑ j ∈ Finset.range (m + 1),
        (1 / 2 : ℝ) ^ min (j + 1) m * (alphaG m r * gRoot m r ^ j)⁻¹ =
      (alphaG m r - 2) / (2 * alphaG m r * betaG m r ^ m) := by
  obtain ⟨hx1, hx2, -⟩ := gRoot_spec (m := m) hr
  set x := gRoot m r
  have hα : alphaG m r = 2 * x / (2 * x - 1) := rfl
  have hx0 : 0 < x := by linarith
  have hu : 0 < 2 * x - 1 := by linarith
  have hα4 := four_le_alphaG (m := m) hr
  have hgeo : ∀ n, ∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ (j + 1) * (alphaG m r * x ^ j)⁻¹ =
      (1 - (2 * x)⁻¹ ^ n) / 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have e : (1 / 2 : ℝ) ^ (n + 1) * (alphaG m r * x ^ n)⁻¹ =
          (1 - (2 * x)⁻¹) * (2 * x)⁻¹ ^ n / 2 := by
        rw [hα, inv_pow, mul_pow, one_div, inv_pow]
        have hxn : 0 < x ^ n := pow_pos hx0 n
        field_simp
        ring
      rw [e, pow_succ]
      ring
  have hs : ∑ j ∈ Finset.range m, (1 / 2 : ℝ) ^ min (j + 1) m * (alphaG m r * x ^ j)⁻¹ =
      ∑ j ∈ Finset.range m, (1 / 2 : ℝ) ^ (j + 1) * (alphaG m r * x ^ j)⁻¹ :=
    Finset.sum_congr rfl fun j hj => by
      rw [Finset.mem_range] at hj; rw [min_eq_left (by omega)]
  have hβ : betaG m r = 2 * x := rfl
  rw [Finset.sum_range_succ, hs, hgeo, min_eq_right (by omega), hβ, inv_pow]
  have e2 : (1 / 2 : ℝ) ^ m * (alphaG m r * x ^ m)⁻¹ = (alphaG m r * (2 * x) ^ m)⁻¹ := by
    rw [mul_pow, one_div, inv_pow]
    have hxm : 0 < x ^ m := pow_pos hx0 m
    field_simp
  rw [e2]
  have hy : 0 < (2 * x) ^ m := pow_pos (by linarith) m
  field_simp
  ring

lemma irrational_alphaG (hm : 1 ≤ m) (hr : 2 ≤ r) : Irrational (alphaG m r) := by
  obtain ⟨hx1, -, -⟩ := gRoot_spec (m := m) hr
  have hx := irrational_gRoot hm hr
  have h2 : Irrational (2 * gRoot m r - 1) := by
    have := (hx.intCast_mul (m := 2) (by norm_num)).sub_intCast 1
    push_cast at this
    exact this
  have : alphaG m r = ((1 : ℤ) : ℝ) + (2 * gRoot m r - 1)⁻¹ := by
    unfold alphaG
    have : 2 * gRoot m r - 1 ≠ 0 := by linarith
    field_simp
    push_cast
    ring
  rw [this]
  exact h2.inv.intCast_add 1

lemma irrational_betaG (hm : 1 ≤ m) (hr : 2 ≤ r) : Irrational (betaG m r) := by
  have := (irrational_gRoot hm hr).intCast_mul (m := 2) (by norm_num)
  push_cast at this
  exact this

end Density

/-! ## Theorem G (2)-(4): classification, count, density -/

section Classification

variable {m r : ℕ}

lemma gPerm_pow_apply (hr : 2 ≤ r) (n : ℕ) (x : ℤ) :
    (gPerm m r hr ^ n) x = (wy (alphaG m r))^[n] x := by
  rw [Equiv.Perm.coe_pow]; rfl

lemma gmPerm_pow_apply (hr : 2 ≤ r) (n : ℕ) (x : ℤ) :
    (gmPerm m r hr ^ n) x = (wy (betaG m r))^[n] x := by
  rw [Equiv.Perm.coe_pow]; rfl

/-- The first return of a positive even `s` to the evens: word `E Oʲ`, `j ≤ m`, landing
`≥ r·s`. -/
lemma gPerm_first_even (hr : 2 ≤ r) {s : ℤ} (hs0 : 0 < s) (hs : s % 2 = 0) :
    ∃ j ≤ m, (wy (alphaG m r))^[j + 1] s % 2 = 0 ∧
      (∀ i : ℕ, 1 ≤ i → i ≤ j → (wy (alphaG m r))^[i] s % 2 = 1) ∧
      r * s ≤ (wy (alphaG m r))^[j + 1] s := by
  classical
  have hex := exists_even_iterate (m := m) hr hs
  obtain ⟨hjm, hje⟩ := Nat.find_spec hex
  have hodd : ∀ i : ℕ, 1 ≤ i → i ≤ Nat.find hex → (wy (alphaG m r))^[i] s % 2 = 1 := by
    intro i hi1 hi2
    have h' : ¬ (i - 1 ≤ m ∧ (wy (alphaG m r))^[i - 1 + 1] s % 2 = 0) :=
      Nat.find_min hex (by omega)
    rw [show i - 1 + 1 = i by omega] at h'
    have : ¬ (wy (alphaG m r))^[i] s % 2 = 0 := fun h => h' ⟨by omega, h⟩
    omega
  exact ⟨_, hjm, hje, hodd, le_wy_iterate_of_odd_run hr hs0 hs hjm hodd⟩

lemma gPerm_fix (hr : 2 ≤ r) : ∀ z ∈ ({1} : Set ℤ), gPerm m r hr z = z := by
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst hz
  rw [gPerm_apply]
  exact wy_one (by linarith [four_le_alphaG (m := m) hr])

lemma setCount_one {X : ℕ} (hX : 1 ≤ X) : setCount {1} X = 1 := by
  classical
  unfold setCount
  rw [Finset.card_eq_one]
  refine ⟨1, ?_⟩
  ext y
  simp only [Finset.mem_filter, Finset.mem_Icc, Set.mem_singleton_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨-, h⟩; exact h
  · rintro rfl; exact ⟨⟨le_rfl, by exact_mod_cast hX⟩, rfl⟩

/-- There are `⌊X/2⌋` even integers in `[1, X]`. -/
lemma card_filter_even (X : ℕ) :
    ((Finset.Icc (1 : ℤ) X).filter fun y => y % 2 = 0).card = X / 2 := by
  rw [show X / 2 = (Finset.Icc 1 (X / 2)).card by simp]
  symm
  apply Finset.card_nbij (fun j : ℕ => 2 * (j : ℤ))
  · intro j hj
    simp only [Finset.coe_Icc, Set.mem_Icc, Finset.coe_filter, Finset.mem_Icc,
      Set.mem_ofPred_eq] at hj ⊢
    omega
  · intro a _ b _ h
    have : (a : ℤ) = b := by simp only at h; omega
    exact_mod_cast this
  · intro y hy
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hy
    refine ⟨(y / 2).toNat, ?_, ?_⟩
    · simp only [Finset.coe_Icc, Set.mem_Icc]; omega
    · simp only; omega

/-- There are `⌈X/2⌉` odd integers in `[1, X]`. -/
lemma card_filter_odd (X : ℕ) :
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

lemma setCount_evens (X : ℕ) : setCount ({n : ℤ | n % 2 = 0} \ {1}) X = X / 2 := by
  classical
  unfold setCount
  rw [← card_filter_even X]
  congr 1
  ext y
  simp only [Finset.mem_filter, Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2, by omega⟩

lemma setCount_odds (X : ℕ) : setCount ({n : ℤ | n % 2 = 1} \ ∅) X = (X + 1) / 2 := by
  classical
  unfold setCount
  rw [← card_filter_odd X]
  congr 1
  ext y
  simp only [Finset.mem_filter, Set.mem_sdiff, Set.mem_ofPred_eq, Set.notMem_empty,
    not_false_eq_true, and_true]

lemma setCount_empty (X : ℕ) : setCount (∅ : Set ℤ) X = 0 := by
  classical
  unfold setCount
  simp

/-- **(ratified, Theorem G (2)).**  Lemma P applies with `S` = evens, `Φ = {1}`, `T = m + 1`.
Paper proof: `pos_iff` is `wy_pos_iff`; `W(1) = 1` (`wy_one`); (H1) is `wy_lt_of_odd`
(`α ≥ 4`); (H2): by `exists_even_iterate` the first return word is `E Oʲ` with `j ≤ m`, and
`R(s) ≥ r·s > s` by `le_wy_iterate_of_odd_run`. -/
theorem hyp_gPerm (hr : 2 ≤ r) : Hyp (gPerm m r hr) {n | n % 2 = 0} {1} (m + 1) := by
  have h4 := four_le_alphaG (m := m) hr
  have hr' : (2 : ℤ) ≤ r := by exact_mod_cast hr
  refine ⟨fun n => ?_, fun z => ?_, fun z hz hzS hzF => ?_, fun s hs hs0 hsF => ?_⟩
  · exact wy_pos_iff (one_lt_alphaG hr) n
  · simp only [Set.mem_singleton_iff, gPerm_apply]
    have h1 : wy (alphaG m r) 1 = 1 := wy_one (by linarith)
    constructor
    · intro h; exact (wy_bijective (one_lt_alphaG hr)).1 (h.trans h1.symm)
    · rintro rfl; exact h1
  · simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff] at hzS hzF
    rw [gPerm_apply]
    exact wy_lt_of_odd (by linarith) (by omega) (by omega)
  · have hs' : s % 2 = 0 := hs
    obtain ⟨j, hjm, hje, hodd, hge⟩ := gPerm_first_even (m := m) hr hs0 hs'
    refine ⟨j + 1, by omega, by omega, ?_, ?_, ?_⟩
    · rw [gPerm_pow_apply]; exact hje
    · rw [gPerm_pow_apply]; nlinarith
    · intro i hi1 hi2
      rw [gPerm_pow_apply]
      have := hodd i hi1 (by omega)
      simp only [Set.mem_ofPred_eq]
      omega

/-- **(ratified).**  The first return to the evens at least multiplies by `r`. -/
theorem returnMap_gPerm_ge (hr : 2 ≤ r) {s : ℤ} (hs0 : 0 < s) (hs : s % 2 = 0) :
    r * s ≤ returnMap (gPerm m r hr) {n | n % 2 = 0} s := by
  obtain ⟨j, hjm, hje, hodd, hge⟩ := gPerm_first_even (m := m) hr hs0 hs
  have hrt : returnTime (gPerm m r hr) {n | n % 2 = 0} s = j + 1 := by
    apply returnTime_eq (by omega)
    · rw [gPerm_pow_apply]; exact hje
    · intro i hi0 hi
      rw [gPerm_pow_apply]
      have := hodd i hi0 (by omega)
      simp only [Set.mem_ofPred_eq]
      omega
  rw [returnMap, hrt, gPerm_pow_apply]
  exact hge

/-- **(ratified, Theorem G (2)).**  `{1}` is the only finite orbit in `ℕ⁺`. -/
theorem permOrbit_gPerm_finite_iff (hr : 2 ≤ r) {x : ℤ} (hx : 0 < x) :
    (permOrbit (gPerm m r hr) x).Finite ↔ x = 1 := by
  rw [permOrbit_finite_iff (hyp_gPerm hr) (gPerm_fix hr) hx, Set.mem_singleton_iff]

/-- **(ratified, Theorem G (2), forward escape).** -/
theorem tendsto_gPerm_pow (hr : 2 ≤ r) {x : ℤ} (hx : 1 < x) :
    Tendsto (fun n : ℕ => (gPerm m r hr ^ n) x) atTop atTop := by
  exact tendsto_pow (hyp_gPerm hr) (by omega) fun h => by rw [Set.mem_singleton_iff] at h; omega

/-- **(ratified, Theorem G (2), backward escape).** -/
theorem tendsto_gPerm_pow_neg (hr : 2 ≤ r) {x : ℤ} (hx : 1 < x) :
    Tendsto (fun n : ℕ => (gPerm m r hr ^ (-(n : ℤ))) x) atTop atTop := by
  exact tendsto_pow_neg (hyp_gPerm hr) (by omega) fun h => by
    rw [Set.mem_singleton_iff] at h; omega

/-- **(ratified, Theorem G (2), minima).**  For `x > 1`: `x` is the minimum of its orbit iff `x`
is even and its `m + 1` predecessors are odd. -/
theorem isOrbitMin_gPerm_iff (hr : 2 ≤ r) {x : ℤ} (hx : 1 < x) :
    IsOrbitMin (gPerm m r hr) x ↔
      x % 2 = 0 ∧ ∀ i : ℕ, 1 ≤ i → i ≤ m + 1 → (gPerm m r hr ^ (-(i : ℤ))) x % 2 = 1 := by
  rw [isOrbitMin_iff (hyp_gPerm hr) (by omega) fun h => by rw [Set.mem_singleton_iff] at h; omega]
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun i a b => by have := h2 i a b; omega⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun i a b => by have := h2 i a b; omega⟩

/-- **(ratified, Theorem G (3), exact count).**
`#{minima ≤ X} + #{even s ∈ [1, X] : R(s) ≤ X} = 1 + ⌊X/2⌋`.  Paper proof:
`minCount_add_returnCount` with `Φ = {1}` (`#Φ ∩ [1, X] = 1`) and `#(evens ∩ [1, X]) = ⌊X/2⌋`. -/
theorem minCount_gPerm_add (hr : 2 ≤ r) {X : ℕ} (hX : 1 ≤ X) :
    minCount (gPerm m r hr) X + returnCount (gPerm m r hr) {n | n % 2 = 0} {1} X = 1 + X / 2 := by
  rw [minCount_add_returnCount (hyp_gPerm (m := m) hr) (gPerm_fix hr) X, setCount_one hX,
    setCount_evens X]

/-- `#{even s ∈ [1, X] : R(s) ≤ X} ≤ ⌊X/2r⌋` (`R(s) ≥ r·s`). -/
lemma returnCount_gPerm_le (hr : 2 ≤ r) (X : ℕ) :
    returnCount (gPerm m r hr) {n | n % 2 = 0} {1} X ≤ X / (2 * r) := by
  classical
  unfold returnCount
  calc _ ≤ ((Finset.Icc 1 (X / (2 * r))).image fun k : ℕ => 2 * (k : ℤ)).card := by
        apply Finset.card_le_card
        intro s hs
        simp only [Finset.mem_filter, Finset.mem_Icc, Set.mem_ofPred_eq, Set.mem_singleton_iff,
          Finset.mem_image] at hs ⊢
        obtain ⟨⟨h1, h2⟩, hse, -, hR⟩ := hs
        have hge := returnMap_gPerm_ge (m := m) hr (by omega) hse
        obtain ⟨k, rfl⟩ : ∃ k, s = 2 * k := ⟨s / 2, by omega⟩
        refine ⟨k.toNat, ⟨by omega, (Nat.le_div_iff_mul_le (by omega)).2 ?_⟩, by omega⟩
        have : (((k.toNat * (2 * r)) : ℕ) : ℤ) ≤ X := by
          push_cast
          rw [Int.toNat_of_nonneg (by omega)]
          have : k * (2 * (r : ℤ)) = r * (2 * k) := by ring
          linarith
        exact_mod_cast this
    _ ≤ (Finset.Icc 1 (X / (2 * r))).card := Finset.card_image_le
    _ = X / (2 * r) := by simp

/-- **(ratified, Theorem G (3), unconditional lower bound).**
`#{minima ≤ X} ≥ 1 + ⌊X/2⌋ − ⌊X/2r⌋`.  Paper proof: `R(s) ≥ r·s` (`returnMap_gPerm_ge`), so
`R(s) ≤ X` forces `s ≤ X/r`, and there are `⌊X/2r⌋` even `s ≤ X/r`. -/
theorem minCount_gPerm_ge (hr : 2 ≤ r) {X : ℕ} (hX : 1 ≤ X) :
    1 + (X : ℤ) / 2 - (X : ℤ) / (2 * r) ≤ minCount (gPerm m r hr) X := by
  have h := minCount_gPerm_add (m := m) hr hX
  have hB := returnCount_gPerm_le (m := m) hr X
  have c2 : ((X / (2 * r) : ℕ) : ℤ) = (X : ℤ) / (2 * r) := by
    rw [Int.natCast_div]; push_cast; ring
  have c3 : ((X / 2 : ℕ) : ℤ) = (X : ℤ) / 2 := by
    rw [Int.natCast_div]; push_cast; ring
  rw [← c2, ← c3]
  omega

/-- **(ratified, Theorem G (2)).**  Infinitely many infinite orbits. -/
theorem gPerm_infinitelyManyInfiniteOrbits (hr : 2 ≤ r) :
    InfinitelyManyInfiniteOrbits (gPerm m r hr) := by
  apply infinitelyManyInfiniteOrbits_of_minima (hyp_gPerm (m := m) hr)
  by_contra hfin
  rw [Set.not_infinite] at hfin
  classical
  obtain ⟨c, hc⟩ : ∃ c, hfin.toFinset.card = c := ⟨_, rfl⟩
  have hX : 1 ≤ 4 * (c + 2) := by omega
  have hge := minCount_gPerm_ge (m := m) hr hX
  have hle : minCount (gPerm m r hr) (4 * (c + 2)) ≤ c + 1 := by
    unfold minCount
    calc _ ≤ (insert 1 hfin.toFinset).card := by
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert,
            Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Set.mem_singleton_iff] at hx ⊢
          by_cases h1 : x = 1
          · exact Or.inl h1
          · exact Or.inr ⟨by omega, h1, hx.2⟩
      _ ≤ c + 1 := hc ▸ Finset.card_insert_le _ _
  have hr' : (2 : ℤ) ≤ r := by exact_mod_cast hr
  have hq0 := Int.ediv_mul_le ((4 * (c + 2) : ℕ) : ℤ) (show (2 * (r : ℤ)) ≠ 0 by omega)
  have hq1 := Int.ediv_nonneg (show (0 : ℤ) ≤ ((4 * (c + 2) : ℕ) : ℤ) by positivity)
    (show (0 : ℤ) ≤ 2 * r by omega)
  have hq : ((4 * (c + 2) : ℕ) : ℤ) / (2 * r) ≤ c + 2 := by
    by_contra h
    push Not at h
    push_cast at hq0 h
    nlinarith
  push_cast at hge hq
  omega

/-- **(ratified).**  The two forms of the density: `(α − 2)/(2αβᵐ) = (r − xᵐ)/(2^{m+1} r xᵐ)`. -/
theorem densityG_eq (hr : 2 ≤ r) :
    (alphaG m r - 2) / (2 * alphaG m r * betaG m r ^ m) =
      (r - gRoot m r ^ m) / (2 ^ (m + 1) * r * gRoot m r ^ m) := by
  obtain ⟨hx1, -, -⟩ := gRoot_spec (m := m) hr
  have hxm : 0 < gRoot m r ^ m := pow_pos (by linarith) m
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  rw [alphaG_eq hr, betaG, mul_pow]
  field_simp
  ring

lemma gPerm_returnCount_eq (hr : 2 ≤ r) (X : ℕ) :
    returnCount (gPerm m r hr) {n | n % 2 = 0} {1} X =
      ((Finset.Icc 1 (X / 2)).filter fun k : ℕ =>
        returnMap (gPerm m r hr) {n | n % 2 = 0} (2 * (k : ℤ)) ≤ X).card := by
  classical
  unfold returnCount
  symm
  apply Finset.card_nbij (fun k : ℕ => 2 * (k : ℤ))
  · intro k hk
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq, Set.mem_singleton_iff] at hk ⊢
    obtain ⟨⟨h1, h2⟩, hR⟩ := hk
    exact ⟨⟨by omega, by omega⟩, by omega, by omega, hR⟩
  · intro a _ b _ h
    have : (a : ℤ) = b := by simp only at h; omega
    exact_mod_cast this
  · intro s hs
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq, Set.mem_singleton_iff] at hs
    obtain ⟨⟨h1, h2⟩, he, -, hR⟩ := hs
    refine ⟨(s / 2).toNat, ?_, by simp only; omega⟩
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [show 2 * (((s / 2).toNat : ℕ) : ℤ) = s by omega]
    exact hR

/-- **(ratified, Theorem G (4), density, conditional).**  If `deg x = m + 1` (stated as the
`ℚ`-independence of `1, x, …, xᵐ`; `x^{m+1} − 2rx + r` is Eisenstein at any `p ∥ r`, and
irreducible for all `m ≤ 8, r ≤ 60` by computation), then, assuming multidimensional Weyl
equidistribution (a literature hypothesis), the orbit minima have density
`d = (α − 2)/(2αβᵐ)`.  Paper proof (research note §2, proof of 3): by `minCount_gPerm_add`,
`d = 1/2 − Σ_j D_j/c_j` with `D_j` the density of even `n` with return word `E Oʲ`.  The parities
along the run are read off phases `φ_0 = {k c_0}`, `φ_i = {k c_i + h_i(φ_0, …, φ_{i−1})}`
(`h_i` piecewise affine): a triangular, measure-preserving skew product of
`({k c_0}, …, {k c_{m−1}})`, which is equidistributed in `[0, 1)ᵐ` because `1, c_0, …, c_{m−1}`
(times `2x − 1`: `2x − 1, x, …, xᵐ`) are `ℚ`-independent.  So `D_j = 2^{−j−2}` (`j < m`),
`D_m = 2^{−m−1}`, and `R(s) = c_j s + O(1)` on word `j`; summing,
`d = β^{−m}/2 − 1/(αβᵐ)` (using `1 − 1/β = 1/α`). -/
theorem tendsto_minCount_gPerm (hr : 2 ≤ r) (hW : WeylEquidistributionMulti)
    (hind : LinearIndependent ℚ fun i : Fin (m + 1) => gRoot m r ^ (i : ℕ)) :
    Tendsto (fun X : ℕ => (minCount (gPerm m r hr) X : ℝ) / X) atTop
      (𝓝 ((alphaG m r - 2) / (2 * alphaG m r * betaG m r ^ m))) := by
  obtain ⟨hx1, hx2, -⟩ := gRoot_spec (m := m) hr
  have hα1 := one_lt_alphaG (m := m) hr
  have hS : ∀ n : ℤ, n ∈ {n : ℤ | n % 2 = 0} ↔ n % 2 ≠ 1 := fun n => by
    simp only [Set.mem_ofPred_eq]; omega
  have hR := tendsto_returnCount_div (ρ := 1) (S := {n : ℤ | n % 2 = 0}) (Φ := {1}) hr
    (fun j _ => tendsto_wordCount hr hW hind (Or.inr rfl) j) (fun n => gPerm_apply hr n)
    (Or.inr rfl) hS (hyp_gPerm hr) ?step (fun k => 2 * (k : ℤ)) ?n0 ?first ?bound
    (fun X => X / 2) (gPerm_returnCount_eq hr) (fun X k hk => by omega)
  case step =>
    intro hm v hv hvo
    obtain ⟨k, rfl⟩ : ∃ k, v = 2 * k - 1 := ⟨(v + 1) / 2, by omega⟩
    rw [wy_two_mul_sub_one_eq_floor hα1 (irrational_alphaG (by omega) hr) (by omega),
      alphaG_div_sub_one hr, betaG]
    congr 1
    push_cast
    ring
  case n0 =>
    intro k hk
    refine ⟨?_, by omega, ?_⟩
    · simp only [Set.mem_ofPred_eq]; omega
    · simp only [Set.mem_singleton_iff]; omega
  case first =>
    intro _ k _
    rw [wy_two_mul]
    congr 1
    push_cast
    ring
  case bound =>
    intro k hk
    have hS0 : 2 * (k : ℤ) ∈ {n : ℤ | n % 2 = 0} := by simp only [Set.mem_ofPred_eq]; omega
    have hΦ0 : 2 * (k : ℤ) ∉ ({1} : Set ℤ) := by simp only [Set.mem_singleton_iff]; omega
    obtain ⟨h1, hT, -, -, hint⟩ := returnTime_spec (hyp_gPerm (m := m) hr) hS0 (by omega) hΦ0
    set τ := returnTime (gPerm m r hr) {n | n % 2 = 0} (2 * (k : ℤ))
    have hodd : ∀ i : ℕ, 1 ≤ i → i ≤ τ - 1 →
        (wy (alphaG m r))^[i] (2 * (k : ℤ)) % 2 = 1 := by
      intro i hi1 hi2
      have := hint i hi1 (by omega)
      rw [gPerm_pow_apply, Set.mem_ofPred_eq] at this
      omega
    obtain ⟨s1, s2⟩ := run_sandwich hr (show (2 * (k : ℤ)) % 2 = 0 by omega) (τ - 1) hodd
    have hRm : returnMap (gPerm m r hr) {n | n % 2 = 0} (2 * (k : ℤ)) =
        (wy (alphaG m r))^[τ - 1 + 1] (2 * (k : ℤ)) := by
      rw [returnMap, gPerm_pow_apply]; congr 1; omega
    rw [hRm]
    have hxj : 0 ≤ gRoot m r ^ (τ - 1 + 1) := pow_nonneg (by linarith) _
    push_cast at s1 s2
    set D := (((wy (alphaG m r))^[τ - 1 + 1] (2 * (k : ℤ)) : ℤ) : ℝ) -
      alphaG m r / 2 * gRoot m r ^ (τ - 1) * (2 * (k : ℝ)) with hDdef
    have hD1 : -1 < D := by rw [hDdef]; linarith
    have hD2 : D < 4 := by
      by_contra hc
      push Not at hc
      have := mul_le_mul_of_nonneg_left hc (show (0 : ℝ) ≤ 1 - gRoot m r by linarith)
      linarith
    rw [abs_lt]
    constructor <;> linarith
  have hX : ∀ X : ℕ, 1 ≤ X → (minCount (gPerm m r hr) X : ℝ) / X =
      1 / X + ((X / 2 : ℕ) : ℝ) / X - (returnCount (gPerm m r hr) {n | n % 2 = 0} {1} X : ℝ) / X
      := by
    intro X hX1
    have := minCount_gPerm_add (m := m) hr hX1
    rw [← add_div, div_sub_div_same]
    congr 1
    have : (minCount (gPerm m r hr) X : ℝ) =
        1 + (X / 2 : ℕ) - returnCount (gPerm m r hr) {n | n % 2 = 0} {1} X := by
      rw [eq_sub_iff_add_eq]; exact_mod_cast this
    exact this
  have hhalf : Tendsto (fun X : ℕ => ((X / 2 : ℕ) : ℝ) / X) atTop (𝓝 (1 / 2)) := by
    have := tendsto_floor_linear_div (c := 1 / 2) (by norm_num) 0
    refine this.congr fun X => ?_
    have h := Nat.floor_div_eq_div (K := ℝ) X 2
    push_cast at h
    rw [add_zero, one_div_mul_eq_div, h]
  have hlim := ((tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).add hhalf).sub hR
  rw [zero_add, density_sum_eq hr] at hlim
  refine hlim.congr' (eventually_atTop.2 ⟨1, fun X hX1 => (hX X hX1).symm⟩)

end Classification

/-! ## The mirror `W_β` -/

section Mirror

variable {m r : ℕ}

/-- For `m ≥ 1` the root satisfies `x ≤ 3/5` (`x² ≥ x^{m+1} = r(2x − 1) ≥ 2(2x − 1)`). -/
lemma gRoot_le_of_pos (hr : 2 ≤ r) (hm : 1 ≤ m) : gRoot m r ≤ 3 / 5 := by
  obtain ⟨hx1, hx2, hx⟩ := gRoot_spec (m := m) hr
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hpow : gRoot m r ^ (m + 1) ≤ gRoot m r ^ 2 :=
    pow_le_pow_of_le_one (by linarith) (by linarith) (by omega)
  nlinarith

/-- **Mirror partial runs.**  For `n > 0` odd, `j ≤ m`, and `W′(n), …, W′ʲ(n)` even:
`r(n + 1) − 1 ≤ W′^{j+1}(n)`.  At `j = m` this is the mirror identity; for `j < m` the slope
`c_j = A xʲ ≥ r/x` beats the error `1/(1 − x)` because `x ≤ 3/5`. -/
lemma le_wy_iterate_of_even_run_mirror (hr : 2 ≤ r) {n : ℤ} (hn0 : 0 < n) (hn : n % 2 = 1)
    {j : ℕ} (hj : j ≤ m) (heven : ∀ i : ℕ, 1 ≤ i → i ≤ j → (wy (betaG m r))^[i] n % 2 = 0) :
    r * (n + 1) - 1 ≤ (wy (betaG m r))^[j + 1] n := by
  rcases Nat.eq_or_lt_of_le hj with rfl | hjm
  · rw [wy_iterate_eq_of_even_run_mirror hr hn heven]
  obtain ⟨hx1, hx2, hx⟩ := gRoot_spec (m := m) hr
  have hx35 := gRoot_le_of_pos (m := m) hr (by omega)
  obtain ⟨-, h2⟩ := run_sandwich_mirror hr hn j heven
  set x := gRoot m r
  set y := alphaG m r / 2 * x ^ j
  set v : ℝ := (((wy (betaG m r))^[j + 1] n : ℤ) : ℝ)
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hN : (2 : ℝ) ≤ n + 1 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn0
    linarith
  have hreq := half_alphaG_mul_pow (m := m) hr
  have hyx : (r : ℝ) ≤ y * x := by
    have hxp : x ^ (m - j) ≤ x := pow_le_of_le_one (by linarith) (by linarith) (by omega)
    have hy0 : 0 ≤ y := by
      have := four_le_alphaG (m := m) hr
      positivity
    have : y * x ^ (m - j) = r := by
      rw [← hreq]; simp only [y]; rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hjm.le]
    nlinarith [mul_le_mul_of_nonneg_left hxp hy0]
  have hxj : 0 ≤ x ^ (j + 1) := by positivity
  have key : (r : ℝ) * (n + 1) - 2 < v := by
    have e1 : (1 - x) * (y * (n + 1) - v) ≤ 1 := by linarith
    have e2 : (1 - x) * (1 - x) * (n + 1) * r ≤ (1 - x) * (n + 1) * x * (y - r) := by
      have h1x : 0 ≤ (1 - x) * (n + 1) := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hyx h1x]
    by_contra hcon
    push Not at hcon
    have e3 : (1 - x) * (y * (n + 1) - (r * (n + 1) - 2)) ≤ 1 := by
      nlinarith [mul_le_mul_of_nonneg_left hcon (show (0 : ℝ) ≤ 1 - x by linarith)]
    have e4 : x * ((1 - x) * (n + 1) * (y - r) + 2 * (1 - x)) ≤ x := by
      have := mul_le_mul_of_nonneg_left e3 (show (0 : ℝ) ≤ x by linarith)
      linarith
    have hNr : (4 : ℝ) ≤ (n + 1) * r := by nlinarith
    have e5 : (1 - x) * (1 - x) * 4 ≤ (1 - x) * (1 - x) * ((n + 1) * r) :=
      mul_le_mul_of_nonneg_left hNr (by nlinarith)
    nlinarith
  have hlo : ((r * (n + 1) - 2 : ℤ) : ℝ) < (((wy (betaG m r))^[j + 1] n : ℤ) : ℝ) := by
    push_cast; exact key
  have := Int.cast_lt.1 hlo
  omega

lemma gmPerm_first_odd (hr : 2 ≤ r) {s : ℤ} (hs0 : 0 < s) (hs : s % 2 = 1) :
    ∃ j ≤ m, (wy (betaG m r))^[j + 1] s % 2 = 1 ∧
      (∀ i : ℕ, 1 ≤ i → i ≤ j → (wy (betaG m r))^[i] s % 2 = 0) ∧
      r * (s + 1) - 1 ≤ (wy (betaG m r))^[j + 1] s := by
  classical
  have hex : ∃ j, j ≤ m ∧ (wy (betaG m r))^[j + 1] s % 2 = 1 := by
    by_contra hne
    push Not at hne
    have heven : ∀ i : ℕ, 1 ≤ i → i ≤ m → (wy (betaG m r))^[i] s % 2 = 0 := by
      intro i hi1 hi2
      have := hne (i - 1) (by omega)
      rw [show i - 1 + 1 = i by omega] at this
      omega
    have h2 := hne m le_rfl
    rw [wy_iterate_eq_of_even_run_mirror hr hs heven] at h2
    obtain ⟨k, rfl⟩ : ∃ k, s = 2 * k - 1 := ⟨(s + 1) / 2, by omega⟩
    apply h2
    rw [show (r : ℤ) * (2 * k - 1 + 1) - 1 = 2 * (r * k) - 1 by ring]
    omega
  obtain ⟨hjm, hjo⟩ := Nat.find_spec hex
  have heven : ∀ i : ℕ, 1 ≤ i → i ≤ Nat.find hex → (wy (betaG m r))^[i] s % 2 = 0 := by
    intro i hi1 hi2
    have h' : ¬ (i - 1 ≤ m ∧ (wy (betaG m r))^[i - 1 + 1] s % 2 = 1) :=
      Nat.find_min hex (by omega)
    rw [show i - 1 + 1 = i by omega] at h'
    have : ¬ (wy (betaG m r))^[i] s % 2 = 1 := fun h => h' ⟨by omega, h⟩
    omega
  exact ⟨_, hjm, hjo, heven, le_wy_iterate_of_even_run_mirror hr hs0 hs hjm heven⟩

/-- **(ratified, mirror (2)).**  Lemma P applies to the mirror with `S` = odds, `Φ = ∅`,
`T = m + 1`.  Paper proof: (H1) is `wy_lt_of_even` (`β < 2`); (H2): by the mirror identity the
first return word of an odd `s` is `O Eʲ`, `j ≤ m`, and `R′(s) ≥ r(s + 1) − 1 > s`
(`returnMap_gmPerm_ge`). -/
theorem hyp_gmPerm (hr : 2 ≤ r) : Hyp (gmPerm m r hr) {n | n % 2 = 1} ∅ (m + 1) := by
  have hβ := one_lt_betaG_lt (m := m) hr
  have hr' : (2 : ℤ) ≤ r := by exact_mod_cast hr
  refine ⟨fun n => ?_, fun z => ?_, fun z hz hzS _ => ?_, fun s hs hs0 _ => ?_⟩
  · exact wy_pos_iff hβ.1 n
  · simp only [Set.mem_empty_iff_false]
  · simp only [Set.mem_ofPred_eq] at hzS
    rw [gmPerm_apply]
    exact wy_lt_of_even (by linarith) hz (by omega)
  · have hs' : s % 2 = 1 := hs
    obtain ⟨j, hjm, hjo, heven, hge⟩ := gmPerm_first_odd (m := m) hr hs0 hs'
    refine ⟨j + 1, by omega, by omega, ?_, ?_, ?_⟩
    · rw [gmPerm_pow_apply]; exact hjo
    · rw [gmPerm_pow_apply]; nlinarith
    · intro i hi1 hi2
      rw [gmPerm_pow_apply]
      have := heven i hi1 (by omega)
      simp only [Set.mem_ofPred_eq]
      omega

/-- **(ratified).**  The mirror's first return to the odds: `R′(s) ≥ r(s + 1) − 1`.  Paper proof:
on `O Eʲ` (`j ≤ m`), `W′^{j+1}(s) = ⌊(s + 1) c_j − ε⌋` with slope `c_j = r x^{j−m} ≥ r` and error
`ε = Σ_l f_l x^{j+1−l} ∈ [0, 1)`; at `j = m` this is the mirror identity. -/
theorem returnMap_gmPerm_ge (hr : 2 ≤ r) {s : ℤ} (hs0 : 0 < s) (hs : s % 2 = 1) :
    r * (s + 1) - 1 ≤ returnMap (gmPerm m r hr) {n | n % 2 = 1} s := by
  obtain ⟨j, hjm, hjo, heven, hge⟩ := gmPerm_first_odd (m := m) hr hs0 hs
  have hrt : returnTime (gmPerm m r hr) {n | n % 2 = 1} s = j + 1 := by
    apply returnTime_eq (by omega)
    · rw [gmPerm_pow_apply]; exact hjo
    · intro i hi0 hi
      rw [gmPerm_pow_apply]
      have := heven i hi0 (by omega)
      simp only [Set.mem_ofPred_eq]
      omega
  rw [returnMap, hrt, gmPerm_pow_apply]
  exact hge

/-- **(ratified, mirror (2)).**  No finite orbit in `ℕ⁺`. -/
theorem permOrbit_gmPerm_infinite (hr : 2 ≤ r) {x : ℤ} (hx : 0 < x) :
    (permOrbit (gmPerm m r hr) x).Infinite := by
  exact permOrbit_infinite (hyp_gmPerm hr) hx (Set.notMem_empty x)

/-- **(ratified, mirror forward escape).** -/
theorem tendsto_gmPerm_pow (hr : 2 ≤ r) {x : ℤ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => (gmPerm m r hr ^ n) x) atTop atTop := by
  exact tendsto_pow (hyp_gmPerm hr) hx (Set.notMem_empty x)

/-- **(ratified, mirror backward escape).** -/
theorem tendsto_gmPerm_pow_neg (hr : 2 ≤ r) {x : ℤ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => (gmPerm m r hr ^ (-(n : ℤ))) x) atTop atTop := by
  exact tendsto_pow_neg (hyp_gmPerm hr) hx (Set.notMem_empty x)

/-- **(ratified, mirror minima).**  For `x > 0`: `x` is the minimum of its orbit iff `x` is odd
and its `m + 1` predecessors are even. -/
theorem isOrbitMin_gmPerm_iff (hr : 2 ≤ r) {x : ℤ} (hx : 0 < x) :
    IsOrbitMin (gmPerm m r hr) x ↔
      x % 2 = 1 ∧ ∀ i : ℕ, 1 ≤ i → i ≤ m + 1 → (gmPerm m r hr ^ (-(i : ℤ))) x % 2 = 0 := by
  rw [isOrbitMin_iff (hyp_gmPerm hr) hx (Set.notMem_empty x)]
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun i a b => by have := h2 i a b; omega⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun i a b => by have := h2 i a b; omega⟩

/-- **(ratified, mirror exact count).**
`#{minima ≤ X} + #{odd s ∈ [1, X] : R′(s) ≤ X} = ⌈X/2⌉` (no `Φ` term). -/
theorem minCount_gmPerm_add (hr : 2 ≤ r) (X : ℕ) :
    minCount (gmPerm m r hr) X + returnCount (gmPerm m r hr) {n | n % 2 = 1} ∅ X =
      (X + 1) / 2 := by
  rw [minCount_add_returnCount (hyp_gmPerm (m := m) hr) (fun z hz => absurd hz (Set.notMem_empty z))
    X, setCount_empty, setCount_odds, zero_add]

/-- `#{odd s ∈ [1, X] : R′(s) ≤ X} ≤ ⌊(X + 1)/2r⌋` (`R′(s) ≥ r(s + 1) − 1`). -/
lemma returnCount_gmPerm_le (hr : 2 ≤ r) (X : ℕ) :
    returnCount (gmPerm m r hr) {n | n % 2 = 1} ∅ X ≤ (X + 1) / (2 * r) := by
  classical
  unfold returnCount
  calc _ ≤ ((Finset.Icc 1 ((X + 1) / (2 * r))).image fun k : ℕ => 2 * (k : ℤ) - 1).card := by
        apply Finset.card_le_card
        intro s hs
        simp only [Finset.mem_filter, Finset.mem_Icc, Set.mem_ofPred_eq, Set.notMem_empty,
          not_false_eq_true, Finset.mem_image, true_and] at hs ⊢
        obtain ⟨⟨h1, h2⟩, hso, hR⟩ := hs
        have hge := returnMap_gmPerm_ge (m := m) hr (by omega) hso
        obtain ⟨k, rfl⟩ : ∃ k, s = 2 * k - 1 := ⟨(s + 1) / 2, by omega⟩
        refine ⟨k.toNat, ⟨by omega, (Nat.le_div_iff_mul_le (by omega)).2 ?_⟩, by omega⟩
        have : (((k.toNat * (2 * r)) : ℕ) : ℤ) ≤ X + 1 := by
          push_cast
          rw [Int.toNat_of_nonneg (by omega)]
          have : k * (2 * (r : ℤ)) = r * (2 * k - 1 + 1) := by ring
          linarith
        exact_mod_cast this
    _ ≤ (Finset.Icc 1 ((X + 1) / (2 * r))).card := Finset.card_image_le
    _ = (X + 1) / (2 * r) := by simp

/-- **(ratified, mirror lower bound).**  `#{minima ≤ X} ≥ ⌊(X + 1)/2⌋ − ⌊(X + 1)/2r⌋`.  Paper
proof: `R′(s) ≤ X` forces `s + 1 ≤ (X + 1)/r` (`returnMap_gmPerm_ge`). -/
theorem minCount_gmPerm_ge (hr : 2 ≤ r) (X : ℕ) :
    ((X : ℤ) + 1) / 2 - ((X : ℤ) + 1) / (2 * r) ≤ minCount (gmPerm m r hr) X := by
  have h := minCount_gmPerm_add (m := m) hr X
  have hB := returnCount_gmPerm_le (m := m) hr X
  have c2 : (((X + 1) / (2 * r) : ℕ) : ℤ) = ((X : ℤ) + 1) / (2 * r) := by
    rw [Int.natCast_div]; push_cast; ring
  have c3 : (((X + 1) / 2 : ℕ) : ℤ) = ((X : ℤ) + 1) / 2 := by
    rw [Int.natCast_div]; push_cast; ring
  rw [← c2, ← c3]
  omega

/-- **(ratified, mirror).**  Infinitely many infinite orbits. -/
theorem gmPerm_infinitelyManyInfiniteOrbits (hr : 2 ≤ r) :
    InfinitelyManyInfiniteOrbits (gmPerm m r hr) := by
  apply infinitelyManyInfiniteOrbits_of_minima (hyp_gmPerm (m := m) hr)
  by_contra hfin
  rw [Set.not_infinite] at hfin
  classical
  obtain ⟨c, hc⟩ : ∃ c, hfin.toFinset.card = c := ⟨_, rfl⟩
  have hge := minCount_gmPerm_ge (m := m) hr (4 * (c + 2))
  have hle : minCount (gmPerm m r hr) (4 * (c + 2)) ≤ c := by
    unfold minCount
    calc _ ≤ hfin.toFinset.card := by
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_filter, Finset.mem_Icc, Set.Finite.mem_toFinset,
            Set.mem_ofPred_eq] at hx ⊢
          exact ⟨by omega, Set.notMem_empty x, hx.2⟩
      _ = c := hc
  have hr' : (2 : ℤ) ≤ r := by exact_mod_cast hr
  have hq0 := Int.ediv_mul_le (((4 * (c + 2) : ℕ) : ℤ) + 1) (show (2 * (r : ℤ)) ≠ 0 by omega)
  have hq : (((4 * (c + 2) : ℕ) : ℤ) + 1) / (2 * r) ≤ c + 2 := by
    by_contra h
    push Not at h
    push_cast at hq0 h
    nlinarith
  push_cast at hge hq
  omega

lemma gmPerm_returnCount_eq (hr : 2 ≤ r) (X : ℕ) :
    returnCount (gmPerm m r hr) {n | n % 2 = 1} ∅ X =
      ((Finset.Icc 1 ((X + 1) / 2)).filter fun k : ℕ =>
        returnMap (gmPerm m r hr) {n | n % 2 = 1} (2 * (k : ℤ) - 1) ≤ X).card := by
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

/-- **(ratified, mirror density, conditional).**  Same `d = (α − 2)/(2αβᵐ)`.  Paper proof: as
`tendsto_minCount_gPerm`, with the parity roles swapped; the run phases are the same
`{k c_i}`. -/
theorem tendsto_minCount_gmPerm (hr : 2 ≤ r) (hW : WeylEquidistributionMulti)
    (hind : LinearIndependent ℚ fun i : Fin (m + 1) => gRoot m r ^ (i : ℕ)) :
    Tendsto (fun X : ℕ => (minCount (gmPerm m r hr) X : ℝ) / X) atTop
      (𝓝 ((alphaG m r - 2) / (2 * alphaG m r * betaG m r ^ m))) := by
  obtain ⟨hx1, hx2, -⟩ := gRoot_spec (m := m) hr
  have hβ1 := one_lt_betaG (m := m) hr
  have hS : ∀ n : ℤ, n ∈ {n : ℤ | n % 2 = 1} ↔ n % 2 ≠ 0 := fun n => by
    simp only [Set.mem_ofPred_eq]; omega
  have hR := tendsto_returnCount_div (ρ := 0) (S := {n : ℤ | n % 2 = 1}) (Φ := ∅) hr
    (fun j _ => tendsto_wordCount hr hW hind (Or.inl rfl) j) (fun n => gmPerm_apply hr n)
    (Or.inl rfl) hS (hyp_gmPerm hr) ?step (fun k => 2 * (k : ℤ) - 1) ?n0 ?first ?bound
    (fun X => (X + 1) / 2) (gmPerm_returnCount_eq hr) (fun X k hk => by omega)
  case step =>
    intro _ v hv hve
    obtain ⟨k, rfl⟩ : ∃ k, v = 2 * k := ⟨v / 2, by omega⟩
    rw [wy_two_mul, betaG]
    congr 1
    push_cast
    ring
  case n0 =>
    intro k hk
    refine ⟨?_, by omega, Set.notMem_empty _⟩
    simp only [Set.mem_ofPred_eq]; omega
  case first =>
    intro hm k hk
    rw [wy_two_mul_sub_one_eq_floor hβ1 (irrational_betaG hm hr) (by omega),
      betaG_div_sub_one hr]
    congr 1
    push_cast
    ring
  case bound =>
    intro k hk
    have hS0 : 2 * (k : ℤ) - 1 ∈ {n : ℤ | n % 2 = 1} := by simp only [Set.mem_ofPred_eq]; omega
    obtain ⟨h1, hT, -, -, hint⟩ :=
      returnTime_spec (hyp_gmPerm (m := m) hr) hS0 (by omega) (Set.notMem_empty _)
    set τ := returnTime (gmPerm m r hr) {n | n % 2 = 1} (2 * (k : ℤ) - 1)
    have hev : ∀ i : ℕ, 1 ≤ i → i ≤ τ - 1 →
        (wy (betaG m r))^[i] (2 * (k : ℤ) - 1) % 2 = 0 := by
      intro i hi1 hi2
      have := hint i hi1 (by omega)
      rw [gmPerm_pow_apply, Set.mem_ofPred_eq] at this
      omega
    obtain ⟨s1, s2⟩ :=
      run_sandwich_mirror hr (show (2 * (k : ℤ) - 1) % 2 = 1 by omega) (τ - 1) hev
    have hRm : returnMap (gmPerm m r hr) {n | n % 2 = 1} (2 * (k : ℤ) - 1) =
        (wy (betaG m r))^[τ - 1 + 1] (2 * (k : ℤ) - 1) := by
      rw [returnMap, gmPerm_pow_apply]; congr 1; omega
    rw [hRm]
    have hxj : 0 ≤ gRoot m r ^ (τ - 1 + 1) := pow_nonneg (by linarith) _
    push_cast at s1 s2
    have e : (2 * (k : ℝ) - 1 + 1) = 2 * k := by ring
    rw [e] at s1 s2
    set D := alphaG m r / 2 * gRoot m r ^ (τ - 1) * (2 * (k : ℝ)) -
      (((wy (betaG m r))^[τ - 1 + 1] (2 * (k : ℤ) - 1) : ℤ) : ℝ) with hDdef
    have hD1 : 0 < D := by rw [hDdef]; linarith
    have hD2 : D < 4 := by
      by_contra hc
      push Not at hc
      have := mul_le_mul_of_nonneg_left hc (show (0 : ℝ) ≤ 1 - gRoot m r by linarith)
      linarith
    rw [abs_lt]
    constructor <;> linarith
  have hX : ∀ X : ℕ, (minCount (gmPerm m r hr) X : ℝ) / X =
      (((X + 1) / 2 : ℕ) : ℝ) / X - (returnCount (gmPerm m r hr) {n | n % 2 = 1} ∅ X : ℝ) / X
      := by
    intro X
    have := minCount_gmPerm_add (m := m) hr X
    rw [div_sub_div_same]
    congr 1
    rw [eq_sub_iff_add_eq]; exact_mod_cast this
  have hhalf : Tendsto (fun X : ℕ => (((X + 1) / 2 : ℕ) : ℝ) / X) atTop (𝓝 (1 / 2)) := by
    have := tendsto_floor_linear_div (c := 1 / 2) (by norm_num) (1 / 2)
    refine this.congr fun X => ?_
    have h := Nat.floor_div_eq_div (K := ℝ) (X + 1) 2
    push_cast at h
    rw [show (1 / 2 : ℝ) * X + 1 / 2 = (X + 1) / 2 by ring, h]
  have hlim := hhalf.sub hR
  rw [density_sum_eq hr] at hlim
  exact hlim.congr fun X => (hX X).symm

end Mirror

end CollatzMoonshot.WythoffLine
