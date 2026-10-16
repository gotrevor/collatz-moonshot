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

/-- **(ratified, Theorem G (1)).**  If `n` is even and `W(n), …, Wᵐ(n)` are odd, then
`W^{m+1}(n) = r·n`; for every `n ∈ ℤ`.  Paper proof: module docstring (for `m = 0`,
`W(2k) = ⌊2rk⌋ = 2rk`). -/
theorem wy_iterate_eq_of_odd_run (hr : 2 ≤ r) {n : ℤ} (hn : n % 2 = 0)
    (hodd : ∀ i : ℕ, 1 ≤ i → i ≤ m → (wy (alphaG m r))^[i] n % 2 = 1) :
    (wy (alphaG m r))^[m + 1] n = r * n := by
  sorry

/-- **(ratified, Theorem G (1), runs).**  After an even point at most `m` odd points follow: some
`W^{j+1}(n)`, `j ≤ m`, is even.  Paper proof: `wy_iterate_eq_of_odd_run` (`r·n` is even). -/
theorem exists_even_iterate (hr : 2 ≤ r) {n : ℤ} (hn : n % 2 = 0) :
    ∃ j ≤ m, (wy (alphaG m r))^[j + 1] n % 2 = 0 := by
  sorry

/-- **(ratified, Theorem G, partial runs).**  For `n > 0` even, `j ≤ m`, and `W(n), …, Wʲ(n)`
odd: `r·n ≤ W^{j+1}(n)`.  Paper proof: `W^{j+1}(n) = ⌊c_j n + δ_j⌋ ≥ ⌊c_j n⌋` with
`c_j = r x^{j−m} ≥ r`. -/
theorem le_wy_iterate_of_odd_run (hr : 2 ≤ r) {n : ℤ} (hn0 : 0 < n) (hn : n % 2 = 0) {j : ℕ}
    (hj : j ≤ m) (hodd : ∀ i : ℕ, 1 ≤ i → i ≤ j → (wy (alphaG m r))^[i] n % 2 = 1) :
    r * n ≤ (wy (alphaG m r))^[j + 1] n := by
  sorry

/-- **(ratified, mirror identity).**  If `n` is odd and `W′(n), …, W′ᵐ(n)` are even, then
`W′^{m+1}(n) = r(n + 1) − 1`; for every `n ∈ ℤ`.  Paper proof (sandwich): `n = 2k − 1`,
`v_1 = ⌈kα⌉ − 1 ∈ [y − 1, y)` with `y = A(n + 1)`, and each even step `v ↦ ⌊xv⌋` satisfies
`xv − 1 < ⌊xv⌋ ≤ xv`.  So `v_{m+1} < xᵐ y = r(n + 1)` and
`v_{m+1} > xᵐ(y − 1) − Σ_{i<m} xⁱ = r(n + 1) − Σ_{i=0}^{m} xⁱ > r(n + 1) − 2`. -/
theorem wy_iterate_eq_of_even_run_mirror (hr : 2 ≤ r) {n : ℤ} (hn : n % 2 = 1)
    (heven : ∀ i : ℕ, 1 ≤ i → i ≤ m → (wy (betaG m r))^[i] n % 2 = 0) :
    (wy (betaG m r))^[m + 1] n = r * (n + 1) - 1 := by
  sorry

end Identity

/-! ## Theorem G (2)-(4): classification, count, density -/

section Classification

variable {m r : ℕ}

/-- **(ratified, Theorem G (2)).**  Lemma P applies with `S` = evens, `Φ = {1}`, `T = m + 1`.
Paper proof: `pos_iff` is `wy_pos_iff`; `W(1) = 1` (`wy_one`); (H1) is `wy_lt_of_odd`
(`α ≥ 4`); (H2): by `exists_even_iterate` the first return word is `E Oʲ` with `j ≤ m`, and
`R(s) ≥ r·s > s` by `le_wy_iterate_of_odd_run`. -/
theorem hyp_gPerm (hr : 2 ≤ r) : Hyp (gPerm m r hr) {n | n % 2 = 0} {1} (m + 1) := by
  sorry

/-- **(ratified).**  The first return to the evens at least multiplies by `r`. -/
theorem returnMap_gPerm_ge (hr : 2 ≤ r) {s : ℤ} (hs0 : 0 < s) (hs : s % 2 = 0) :
    r * s ≤ returnMap (gPerm m r hr) {n | n % 2 = 0} s := by
  sorry

/-- **(ratified, Theorem G (2)).**  `{1}` is the only finite orbit in `ℕ⁺`. -/
theorem permOrbit_gPerm_finite_iff (hr : 2 ≤ r) {x : ℤ} (hx : 0 < x) :
    (permOrbit (gPerm m r hr) x).Finite ↔ x = 1 := by
  sorry

/-- **(ratified, Theorem G (2), forward escape).** -/
theorem tendsto_gPerm_pow (hr : 2 ≤ r) {x : ℤ} (hx : 1 < x) :
    Tendsto (fun n : ℕ => (gPerm m r hr ^ n) x) atTop atTop := by
  sorry

/-- **(ratified, Theorem G (2), backward escape).** -/
theorem tendsto_gPerm_pow_neg (hr : 2 ≤ r) {x : ℤ} (hx : 1 < x) :
    Tendsto (fun n : ℕ => (gPerm m r hr ^ (-(n : ℤ))) x) atTop atTop := by
  sorry

/-- **(ratified, Theorem G (2), minima).**  For `x > 1`: `x` is the minimum of its orbit iff `x`
is even and its `m + 1` predecessors are odd. -/
theorem isOrbitMin_gPerm_iff (hr : 2 ≤ r) {x : ℤ} (hx : 1 < x) :
    IsOrbitMin (gPerm m r hr) x ↔
      x % 2 = 0 ∧ ∀ i : ℕ, 1 ≤ i → i ≤ m + 1 → (gPerm m r hr ^ (-(i : ℤ))) x % 2 = 1 := by
  sorry

/-- **(ratified, Theorem G (3), exact count).**
`#{minima ≤ X} + #{even s ∈ [1, X] : R(s) ≤ X} = 1 + ⌊X/2⌋`.  Paper proof:
`minCount_add_returnCount` with `Φ = {1}` (`#Φ ∩ [1, X] = 1`) and `#(evens ∩ [1, X]) = ⌊X/2⌋`. -/
theorem minCount_gPerm_add (hr : 2 ≤ r) {X : ℕ} (hX : 1 ≤ X) :
    minCount (gPerm m r hr) X + returnCount (gPerm m r hr) {n | n % 2 = 0} {1} X = 1 + X / 2 := by
  sorry

/-- **(ratified, Theorem G (3), unconditional lower bound).**
`#{minima ≤ X} ≥ 1 + ⌊X/2⌋ − ⌊X/2r⌋`.  Paper proof: `R(s) ≥ r·s` (`returnMap_gPerm_ge`), so
`R(s) ≤ X` forces `s ≤ X/r`, and there are `⌊X/2r⌋` even `s ≤ X/r`. -/
theorem minCount_gPerm_ge (hr : 2 ≤ r) {X : ℕ} (hX : 1 ≤ X) :
    1 + (X : ℤ) / 2 - (X : ℤ) / (2 * r) ≤ minCount (gPerm m r hr) X := by
  sorry

/-- **(ratified, Theorem G (2)).**  Infinitely many infinite orbits. -/
theorem gPerm_infinitelyManyInfiniteOrbits (hr : 2 ≤ r) :
    InfinitelyManyInfiniteOrbits (gPerm m r hr) := by
  sorry

/-- **(ratified).**  The two forms of the density: `(α − 2)/(2αβᵐ) = (r − xᵐ)/(2^{m+1} r xᵐ)`. -/
theorem densityG_eq (hr : 2 ≤ r) :
    (alphaG m r - 2) / (2 * alphaG m r * betaG m r ^ m) =
      (r - gRoot m r ^ m) / (2 ^ (m + 1) * r * gRoot m r ^ m) := by
  sorry

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
  sorry

end Classification

/-! ## The mirror `W_β` -/

section Mirror

variable {m r : ℕ}

/-- **(ratified, mirror (2)).**  Lemma P applies to the mirror with `S` = odds, `Φ = ∅`,
`T = m + 1`.  Paper proof: (H1) is `wy_lt_of_even` (`β < 2`); (H2): by the mirror identity the
first return word of an odd `s` is `O Eʲ`, `j ≤ m`, and `R′(s) ≥ r(s + 1) − 1 > s`
(`returnMap_gmPerm_ge`). -/
theorem hyp_gmPerm (hr : 2 ≤ r) : Hyp (gmPerm m r hr) {n | n % 2 = 1} ∅ (m + 1) := by
  sorry

/-- **(ratified).**  The mirror's first return to the odds: `R′(s) ≥ r(s + 1) − 1`.  Paper proof:
on `O Eʲ` (`j ≤ m`), `W′^{j+1}(s) = ⌊(s + 1) c_j − ε⌋` with slope `c_j = r x^{j−m} ≥ r` and error
`ε = Σ_l f_l x^{j+1−l} ∈ [0, 1)`; at `j = m` this is the mirror identity. -/
theorem returnMap_gmPerm_ge (hr : 2 ≤ r) {s : ℤ} (hs0 : 0 < s) (hs : s % 2 = 1) :
    r * (s + 1) - 1 ≤ returnMap (gmPerm m r hr) {n | n % 2 = 1} s := by
  sorry

/-- **(ratified, mirror (2)).**  No finite orbit in `ℕ⁺`. -/
theorem permOrbit_gmPerm_infinite (hr : 2 ≤ r) {x : ℤ} (hx : 0 < x) :
    (permOrbit (gmPerm m r hr) x).Infinite := by
  sorry

/-- **(ratified, mirror forward escape).** -/
theorem tendsto_gmPerm_pow (hr : 2 ≤ r) {x : ℤ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => (gmPerm m r hr ^ n) x) atTop atTop := by
  sorry

/-- **(ratified, mirror backward escape).** -/
theorem tendsto_gmPerm_pow_neg (hr : 2 ≤ r) {x : ℤ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => (gmPerm m r hr ^ (-(n : ℤ))) x) atTop atTop := by
  sorry

/-- **(ratified, mirror minima).**  For `x > 0`: `x` is the minimum of its orbit iff `x` is odd
and its `m + 1` predecessors are even. -/
theorem isOrbitMin_gmPerm_iff (hr : 2 ≤ r) {x : ℤ} (hx : 0 < x) :
    IsOrbitMin (gmPerm m r hr) x ↔
      x % 2 = 1 ∧ ∀ i : ℕ, 1 ≤ i → i ≤ m + 1 → (gmPerm m r hr ^ (-(i : ℤ))) x % 2 = 0 := by
  sorry

/-- **(ratified, mirror exact count).**
`#{minima ≤ X} + #{odd s ∈ [1, X] : R′(s) ≤ X} = ⌈X/2⌉` (no `Φ` term). -/
theorem minCount_gmPerm_add (hr : 2 ≤ r) (X : ℕ) :
    minCount (gmPerm m r hr) X + returnCount (gmPerm m r hr) {n | n % 2 = 1} ∅ X =
      (X + 1) / 2 := by
  sorry

/-- **(ratified, mirror lower bound).**  `#{minima ≤ X} ≥ ⌊(X + 1)/2⌋ − ⌊(X + 1)/2r⌋`.  Paper
proof: `R′(s) ≤ X` forces `s + 1 ≤ (X + 1)/r` (`returnMap_gmPerm_ge`). -/
theorem minCount_gmPerm_ge (hr : 2 ≤ r) (X : ℕ) :
    ((X : ℤ) + 1) / 2 - ((X : ℤ) + 1) / (2 * r) ≤ minCount (gmPerm m r hr) X := by
  sorry

/-- **(ratified, mirror).**  Infinitely many infinite orbits. -/
theorem gmPerm_infinitelyManyInfiniteOrbits (hr : 2 ≤ r) :
    InfinitelyManyInfiniteOrbits (gmPerm m r hr) := by
  sorry

/-- **(ratified, mirror density, conditional).**  Same `d = (α − 2)/(2αβᵐ)`.  Paper proof: as
`tendsto_minCount_gPerm`, with the parity roles swapped; the run phases are the same
`{k c_i}`. -/
theorem tendsto_minCount_gmPerm (hr : 2 ≤ r) (hW : WeylEquidistributionMulti)
    (hind : LinearIndependent ℚ fun i : Fin (m + 1) => gRoot m r ^ (i : ℕ)) :
    Tendsto (fun X : ℕ => (minCount (gmPerm m r hr) X : ℝ) / X) atTop
      (𝓝 ((alphaG m r - 2) / (2 * alphaG m r * betaG m r ^ m))) := by
  sorry

end Mirror

end CollatzMoonshot.WythoffLine
