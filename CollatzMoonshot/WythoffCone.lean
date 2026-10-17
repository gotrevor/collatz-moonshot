/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.AmusicalTrap
import CollatzMoonshot.WythoffGeneral

/-!
# Theorems A′ and K: the EE identity and the E-cone trap members `α = b + √(b² + 4c)`

Research note `wythoff-2adic`, §3 (Theorem A′, Theorem K).  Write `x = α/2` and suppose
`x² = bx + c` with `b, c ∈ ℤ`; its Galois conjugate is `x′ = b − x`.  For `W = W_α`
(`WythoffGeneral.wy`):

1. **Theorem A′ (EE identity).**  If `W(2k)` is even then
   `W²(2k) = b·W(2k) + c·2k + ⌊x′·{kα}⌋` (`wy_wy_of_even_even`, any real `α`, any `k ∈ ℤ`).
2. **Cone (`0 < x′ < 1`, i.e. `1 ≤ −c ≤ b − 2`).**  The floor vanishes: `W² = bW + cn` on EE,
   which is even, so `T = {n > 0 even : W(n) even}` is a trap (`coneSet_trap`) along which
   `W^{j+2} = b·W^{j+1} + c·W^j` (`wy_iterate_add_two_of_mem_coneSet`).
3. **Anticone (`−1 < x′ < 0`, i.e. `1 ≤ c ≤ b`; e.g. `1 + √5`, `2 + 2√2`).**  For `k ≠ 0`,
   `W² = bW + cn − 1` on EE, which is odd: EE ⇒ O deterministically.
4. **Theorem K.**  In the cone, the entry points `T ∖ W(T)` (the even `n > 0` with `W(n)` even and
   `W⁻¹(n)` odd) are infinite, so by the trap theorem (`AmusicalTrap`) `W_α` has infinitely many
   infinite orbits (`wkPerm_infinitelyManyInfiniteOrbits`, unconditional).  Conditional on Weyl
   equidistribution (`WeylEquidistribution`, a literature hypothesis), the entry points have
   density `(1/4)(1 − 2/α)` (`tendsto_coneEntryCount`).

In both the cone and the anticone `b² + 4c` is automatically not a square (`(b ∓ 1)²` has the
wrong residue mod 4), so `α` is irrational.  Theorem F's members are the cone points
`(b, c) = (2r, −r)` (`alphaK_two_mul_neg`); `3 + √5 = alphaK 3 (−1)` is the `m = 2` multinacci
member of research note `wythoff-solvable` §4(b4).
-/

namespace CollatzMoonshot.WythoffCone

open CollatzMoonshot.WythoffGeneral
open CollatzMoonshot.AmusicalTrap (permOrbit InfinitelyManyInfiniteOrbits
  infinitelyManyInfiniteOrbits_of_trap)
open Filter Topology

/-! ## Theorem A′ for an arbitrary real `α` -/

/-- **(ratified, Theorem A′).**  If `x = α/2` satisfies `x² = bx + c` with `b, c ∈ ℤ` and `W(2k)`
is even, then `W²(2k) = b·W(2k) + c·2k + ⌊(b − x)·{kα}⌋`.  Paper proof: `W(2k) = kα − f = 2j`
with `f = {kα}`; `W(2j) = ⌊jα⌋ = ⌊(kα − f)x⌋` and `kα·x = 2kx² = b·kα + 2kc`, so
`jα = b(2j + f) + 2kc − fx = 2bj + 2kc + f(b − x)`; `Int.floor_intCast_add`. -/
theorem wy_wy_of_even_even {α : ℝ} {b c : ℤ} (hx : (α / 2) ^ 2 = b * (α / 2) + c) (k : ℤ)
    (h : wy α (2 * k) % 2 = 0) :
    wy α (wy α (2 * k)) =
      b * wy α (2 * k) + c * (2 * k) + ⌊((b : ℝ) - α / 2) * Int.fract ((k : ℝ) * α)⌋ := by
  obtain ⟨j, hj⟩ : ∃ j, wy α (2 * k) = 2 * j := ⟨wy α (2 * k) / 2, by omega⟩
  rw [hj, wy_two_mul]
  have hfl : (⌊(k : ℝ) * α⌋ : ℝ) = 2 * j := by rw [← wy_two_mul, hj]; push_cast; ring
  have key : (j : ℝ) * α = ((b * (2 * j) + c * (2 * k) : ℤ) : ℝ) +
      ((b : ℝ) - α / 2) * Int.fract ((k : ℝ) * α) := by
    rw [Int.fract, hfl]; push_cast; linear_combination (2 * (k : ℝ)) * hx
  rw [key, Int.floor_intCast_add]

/-! ## The members `α = b + √(b² + 4c)` -/

/-- `α = b + √(b² + 4c)`; `x = α/2` is the larger root of `x² = bx + c`. -/
noncomputable def alphaK (b c : ℤ) : ℝ :=
  b + √((b : ℝ) ^ 2 + 4 * c)

/-- **(ratified).**  `x = α/2` satisfies `x² = bx + c` when `b² + 4c ≥ 0`. -/
theorem alphaK_half_sq {b c : ℤ} (hD : 0 ≤ b ^ 2 + 4 * c) :
    (alphaK b c / 2) ^ 2 = b * (alphaK b c / 2) + c := by
  have hD' : (0 : ℝ) ≤ (b : ℝ) ^ 2 + 4 * c := by exact_mod_cast hD
  have := Real.sq_sqrt hD'
  unfold alphaK
  linear_combination this / 4

/-- **(ratified).**  Theorem F's members are `(b, c) = (2r, −r)`:
`2r + √(4r² − 4r) = 2r + 2√(r² − r)`. -/
theorem alphaK_two_mul_neg (r : ℕ) :
    alphaK (2 * r) (-r) = 2 * r + 2 * √((r : ℝ) ^ 2 - r) := by
  unfold alphaK
  have : ((2 * r : ℕ) : ℤ) = 2 * (r : ℤ) := by push_cast; ring
  push_cast
  rw [show (2 * (r : ℝ)) ^ 2 + 4 * -(r : ℝ) = 4 * ((r : ℝ) ^ 2 - r) by ring,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), show (4 : ℝ) = 2 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]

/-- An increasing arithmetic progression with step `d ∈ (0, 1/2)` meets `{fract < 1/2}` within
`⌈1/d⌉` steps. -/
lemma fract_hit_pos (a d : ℝ) (hd0 : 0 < d) (hd : d < 1 / 2) :
    ∃ i : ℕ, i ≤ ⌈1 / d⌉₊ ∧ Int.fract (a + i * d) < 1 / 2 := by
  set n : ℤ := ⌊a⌋ + 1 with hn
  have hna : a < n := by rw [hn]; push_cast; exact Int.lt_floor_add_one a
  have hna' : (n : ℝ) ≤ a + 1 := by rw [hn]; push_cast; linarith [Int.floor_le a]
  have hq0 : 0 ≤ ((n : ℝ) - a) / d := div_nonneg (by linarith) hd0.le
  refine ⟨⌈((n : ℝ) - a) / d⌉₊, Nat.ceil_mono ?_, ?_⟩
  · exact div_le_div_of_nonneg_right (by linarith) hd0.le
  · have h1 := Nat.le_ceil (((n : ℝ) - a) / d)
    have h2 := Nat.ceil_lt_add_one hq0
    rw [div_le_iff₀ hd0] at h1
    have e : ((n : ℝ) - a) / d * d = n - a := div_mul_cancel₀ _ hd0.ne'
    have h2' := mul_lt_mul_of_pos_right h2 hd0
    rw [add_mul, e, one_mul] at h2'
    have hfl : ⌊a + (⌈((n : ℝ) - a) / d⌉₊ : ℝ) * d⌋ = n := by
      rw [Int.floor_eq_iff]; constructor <;> linarith
    rw [Int.fract, hfl]
    linarith

/-- A decreasing arithmetic progression with step `d ∈ (0, 1/2)` meets `{fract < 1/2}` within
`⌈1/d⌉` steps. -/
lemma fract_hit_neg (a d : ℝ) (hd0 : 0 < d) (hd : d < 1 / 2) :
    ∃ i : ℕ, i ≤ ⌈1 / d⌉₊ ∧ Int.fract (a - i * d) < 1 / 2 := by
  by_cases h0 : Int.fract a < 1 / 2
  · exact ⟨0, Nat.zero_le _, by simpa using h0⟩
  push Not at h0
  set n : ℤ := ⌊a⌋
  have hfa : Int.fract a = a - n := rfl
  have hf1 := Int.fract_lt_one a
  have hq0 : 0 ≤ (a - n - 1 / 2) / d := div_nonneg (by linarith) hd0.le
  set i : ℕ := ⌊(a - n - 1 / 2) / d⌋₊ + 1 with hi
  have h1 := Nat.lt_floor_add_one ((a - n - 1 / 2) / d)
  have h2 := Nat.floor_le hq0
  have hic : (i : ℝ) = (⌊(a - n - 1 / 2) / d⌋₊ : ℝ) + 1 := by rw [hi]; push_cast; ring
  rw [← hic, div_lt_iff₀ hd0] at h1
  rw [le_div_iff₀ hd0] at h2
  refine ⟨i, ?_, ?_⟩
  · have hle : (i : ℝ) ≤ 1 / d := by
      have : (a - n - 1 / 2) / d ≤ 1 / (2 * d) := by
        rw [div_le_div_iff₀ hd0 (by linarith)]; nlinarith
      have h3 : 1 / (2 * d) + 1 ≤ 1 / d := by
        rw [div_add_one (by linarith), div_le_div_iff₀ (by linarith) hd0]; nlinarith
      have := Nat.floor_le hq0
      linarith
    exact_mod_cast hle.trans (Nat.le_ceil _)
  · have hfl : ⌊a - (i : ℝ) * d⌋ = n := by
      rw [Int.floor_eq_iff]; constructor <;> nlinarith
    rw [Int.fract, hfl]
    linarith

/-- An arithmetic progression with step `ε`, `0 < |ε| < 1/2`, meets `{fract < 1/2}` within
`⌈1/|ε|⌉` steps. -/
lemma fract_hit (a ε : ℝ) (h0 : ε ≠ 0) (h : |ε| < 1 / 2) :
    ∃ i : ℕ, i ≤ ⌈1 / |ε|⌉₊ ∧ Int.fract (a + i * ε) < 1 / 2 := by
  rcases lt_or_gt_of_ne h0 with hn | hp
  · rw [abs_of_neg hn] at h ⊢
    obtain ⟨i, hi, hf⟩ := fract_hit_neg a (-ε) (by linarith) h
    exact ⟨i, hi, by rw [show a + i * ε = a - i * -ε by ring]; exact hf⟩
  · rw [abs_of_pos hp] at h ⊢
    exact fract_hit_pos a ε hp h

/-- `⌊2v⌋` is even when `{v} < 1/2`. -/
lemma floor_two_mul_even {v : ℝ} (h : Int.fract v < 1 / 2) : ⌊2 * v⌋ % 2 = 0 := by
  have : ⌊2 * v⌋ = 2 * ⌊v⌋ := by
    rw [Int.floor_eq_iff]
    have := Int.fract_nonneg v
    rw [Int.fract] at h this
    push_cast
    constructor <;> linarith
  omega

section Cone

variable {b c : ℤ}

/-- In the cone, `b − 2 < √(b² + 4c) < b`. -/
lemma sqrt_bounds_cone (h1 : 1 ≤ -c) (h2 : -c ≤ b - 2) :
    (b : ℝ) - 2 < √((b : ℝ) ^ 2 + 4 * c) ∧ √((b : ℝ) ^ 2 + 4 * c) < b := by
  have hb : (3 : ℝ) ≤ b := by exact_mod_cast (show (3 : ℤ) ≤ b by omega)
  have hc1 : (1 : ℝ) ≤ -c := by exact_mod_cast h1
  have hc2 : (-c : ℝ) ≤ b - 2 := by exact_mod_cast h2
  constructor
  · rw [Real.lt_sqrt (by linarith)]; nlinarith
  · rw [Real.sqrt_lt' (by linarith)]; nlinarith

/-- An integer square strictly between `L²` and `(L + 2)²` is `(L + 1)²`. -/
lemma sq_eq_of_between {L r : ℤ} (hL : 0 ≤ L) (h1 : L ^ 2 < r * r) (h2 : r * r < (L + 2) ^ 2) :
    r * r = (L + 1) ^ 2 := by
  have hn : r * r = |r| * |r| := (abs_mul_abs_self r).symm
  have ha := abs_nonneg r
  rw [hn] at h1 h2 ⊢
  have h3 : L < |r| := by
    by_contra h
    push Not at h
    nlinarith
  have h4 : |r| < L + 2 := by
    by_contra h
    push Not at h
    nlinarith
  have : |r| = L + 1 := by omega
  rw [this]
  ring

/-- **(ratified).**  In the cone `1 ≤ −c ≤ b − 2`: `b ≥ 3` and `3 < α`. -/
theorem three_lt_alphaK_cone (h1 : 1 ≤ -c) (h2 : -c ≤ b - 2) : 3 < alphaK b c := by
  obtain ⟨hl, -⟩ := sqrt_bounds_cone h1 h2
  unfold alphaK
  have : (3 : ℝ) ≤ b := by exact_mod_cast (show (3 : ℤ) ≤ b by omega)
  linarith

theorem one_lt_alphaK_cone (h1 : 1 ≤ -c) (h2 : -c ≤ b - 2) : 1 < alphaK b c :=
  lt_trans (by norm_num) (three_lt_alphaK_cone h1 h2)

/-- **(ratified).**  In the cone the conjugate `x′ = b − α/2 = (b − √(b² + 4c))/2` lies in
`(0, 1)`: `(b − 2)² < b² + 4c < b²`. -/
theorem conj_mem_Ioo_cone (h1 : 1 ≤ -c) (h2 : -c ≤ b - 2) :
    0 < (b : ℝ) - alphaK b c / 2 ∧ (b : ℝ) - alphaK b c / 2 < 1 := by
  obtain ⟨hl, hu⟩ := sqrt_bounds_cone h1 h2
  unfold alphaK
  constructor <;> linarith

/-- **(ratified).**  In the cone `α` is irrational: `(b − 2)² < b² + 4c < b²`, and the only
square strictly between, `(b − 1)²`, is `≢ b² (mod 4)` while `b² + 4c ≡ b² (mod 4)`. -/
theorem irrational_alphaK_cone (h1 : 1 ≤ -c) (h2 : -c ≤ b - 2) : Irrational (alphaK b c) := by
  have hns : ¬IsSquare (b ^ 2 + 4 * c) := by
    rintro ⟨r, hr⟩
    have hsq := sq_eq_of_between (L := b - 2) (r := r) (by omega) (by nlinarith) (by nlinarith)
    have : 4 * c = 1 - 2 * b := by linear_combination hr.trans hsq
    omega
  have hirr : Irrational √(((b ^ 2 + 4 * c : ℤ)) : ℝ) :=
    irrational_sqrt_intCast_iff.2 ⟨hns, by nlinarith⟩
  push_cast at hirr
  exact hirr.intCast_add b

/-- `W_α` for a cone member, as a permutation of `ℤ`. -/
noncomputable def wkPerm (b c : ℤ) (h1 : 1 ≤ -c) (h2 : -c ≤ b - 2) : Equiv.Perm ℤ :=
  wyPerm (alphaK b c) (one_lt_alphaK_cone h1 h2)

theorem wkPerm_apply (h1 : 1 ≤ -c) (h2 : -c ≤ b - 2) (n : ℤ) :
    wkPerm b c h1 h2 n = wy (alphaK b c) n := rfl

/-- **(ratified, cone identity).**  On EE, `W²(2k) = b·W(2k) + c·2k` (even), for every
`k ∈ ℤ`.  Paper proof: Theorem A′ with `⌊x′f⌋ = 0` (`0 < x′ < 1`, `0 ≤ f < 1`). -/
theorem wy_wy_of_even_even_cone (h1 : 1 ≤ -c) (h2 : -c ≤ b - 2) (k : ℤ)
    (h : wy (alphaK b c) (2 * k) % 2 = 0) :
    wy (alphaK b c) (wy (alphaK b c) (2 * k)) = b * wy (alphaK b c) (2 * k) + c * (2 * k) := by
  rw [wy_wy_of_even_even (alphaK_half_sq (by nlinarith)) k h]
  obtain ⟨hl, hu⟩ := conj_mem_Ioo_cone h1 h2
  have hf0 := Int.fract_nonneg ((k : ℝ) * alphaK b c)
  have hf1 := Int.fract_lt_one ((k : ℝ) * alphaK b c)
  have : ⌊((b : ℝ) - alphaK b c / 2) * Int.fract ((k : ℝ) * alphaK b c)⌋ = 0 := by
    rw [Int.floor_eq_zero_iff]
    constructor
    · positivity
    · nlinarith
  rw [this, add_zero]

/-- The E-cone `T = {n > 0 even : W(n) even}`. -/
def coneSet (b c : ℤ) : Set ℤ :=
  {n | 0 < n ∧ n % 2 = 0 ∧ wy (alphaK b c) n % 2 = 0}

/-- **(ratified, Theorem K, trap).**  `W(T) ⊆ T`.  Paper proof: for `n = 2k ∈ T`, `W(n) > 0` is
even and `W(W(n)) = b·W(n) + c·n` is even (`wy_wy_of_even_even_cone`). -/
theorem coneSet_trap (h1 : 1 ≤ -c) (h2 : -c ≤ b - 2) :
    ∀ n ∈ coneSet b c, wkPerm b c h1 h2 n ∈ coneSet b c := by
  rintro n ⟨hn0, hne, hWe⟩
  rw [wkPerm_apply]
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
  refine ⟨(wy_pos_iff (one_lt_alphaK_cone h1 h2) _).2 hn0, hWe, ?_⟩
  rw [wy_wy_of_even_even_cone h1 h2 k hWe]
  obtain ⟨j, hj⟩ : ∃ j, wy (alphaK b c) (2 * k) = 2 * j := ⟨wy (alphaK b c) (2 * k) / 2, by omega⟩
  rw [hj, show b * (2 * j) + c * (2 * k) = 2 * (b * j + c * k) by ring]
  omega

/-- **(ratified, Theorem K, recurrence).**  Along the trap, `W^{j+2} = b·W^{j+1} + c·W^j`. -/
theorem wy_iterate_add_two_of_mem_coneSet (h1 : 1 ≤ -c) (h2 : -c ≤ b - 2) {n : ℤ}
    (hn : n ∈ coneSet b c) (j : ℕ) :
    (wy (alphaK b c))^[j + 2] n =
      b * (wy (alphaK b c))^[j + 1] n + c * (wy (alphaK b c))^[j] n := by
  have hT : ∀ i : ℕ, (wy (alphaK b c))^[i] n ∈ coneSet b c := by
    intro i
    induction i with
    | zero => exact hn
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact coneSet_trap h1 h2 _ ih
  obtain ⟨hm0, hme, hWe⟩ := hT j
  obtain ⟨k, hk⟩ : ∃ k, (wy (alphaK b c))^[j] n = 2 * k := ⟨(wy (alphaK b c))^[j] n / 2, by omega⟩
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
    hk]
  rw [hk] at hWe
  exact wy_wy_of_even_even_cone h1 h2 k hWe

/-- **(ratified, Theorem K, entry points).**  `n ∈ T ∖ W(T)` iff `n > 0` is even, `W(n)` is even
and `W⁻¹(n)` is odd.  Paper proof: for `n ∈ T`, `W⁻¹(n) > 0` (`wy_pos_iff`) and
`W(W⁻¹ n) = n` is even, so `W⁻¹(n) ∈ T` iff `W⁻¹(n)` is even. -/
theorem mem_coneEntry_iff (h1 : 1 ≤ -c) (h2 : -c ≤ b - 2) (n : ℤ) :
    n ∈ coneSet b c \ wkPerm b c h1 h2 '' coneSet b c ↔
      0 < n ∧ n % 2 = 0 ∧ wy (alphaK b c) n % 2 = 0 ∧ (wkPerm b c h1 h2).symm n % 2 = 1 := by
  have hα := one_lt_alphaK_cone h1 h2
  constructor
  · rintro ⟨⟨hn0, hne, hWe⟩, hnot⟩
    refine ⟨hn0, hne, hWe, ?_⟩
    by_contra hodd
    apply hnot
    refine ⟨(wkPerm b c h1 h2).symm n, ⟨?_, by omega, ?_⟩, by simp⟩
    · rw [← wy_pos_iff hα, ← wkPerm_apply h1 h2, Equiv.apply_symm_apply]; exact hn0
    · rw [← wkPerm_apply h1 h2, Equiv.apply_symm_apply]; exact hne
  · rintro ⟨hn0, hne, hWe, hodd⟩
    refine ⟨⟨hn0, hne, hWe⟩, ?_⟩
    rintro ⟨p, ⟨-, hpe, -⟩, hp⟩
    rw [← hp, Equiv.symm_apply_apply] at hodd
    omega

/-- **Syndeticity of `T`.**  There is `L` with a point of `T` in every window `(Y, Y + L]`,
`Y ≥ 0`.  Dirichlet gives `q ≥ 1` with `0 < |q·α/2 − p| ≤ 1/5`; along `k₀ + iq` the phase
`{k·α/2}` is an arithmetic progression mod 1 (`fract_hit`). -/
lemma coneSet_syndetic (h1 : 1 ≤ -c) (h2 : -c ≤ b - 2) :
    ∃ L : ℤ, 0 ≤ L ∧ ∀ Y : ℤ, 0 ≤ Y → ∃ t ∈ coneSet b c, Y < t ∧ t ≤ Y + L := by
  set α := alphaK b c
  have hθ : Irrational (α / 2) := (irrational_alphaK_cone h1 h2).div_natCast (m := 2) (by norm_num)
  obtain ⟨p, q, hq0, -, hpq⟩ := Real.exists_int_int_abs_mul_sub_le (α / 2) (n := 4) (by norm_num)
  set ε : ℝ := q * (α / 2) - p with hε
  have hε0 : ε ≠ 0 := by
    intro h
    exact (hθ.intCast_mul hq0.ne').ne_int p (by linarith)
  have hεh : |ε| < 1 / 2 := by
    have : |ε| ≤ 1 / 5 := by rw [hε]; convert hpq using 2; norm_num
    linarith
  set M : ℕ := ⌈1 / |ε|⌉₊
  refine ⟨2 + 2 * ((M : ℤ) * q), by positivity, fun Y hY => ?_⟩
  set k0 : ℤ := Y / 2 + 1
  obtain ⟨i, hiM, hfr⟩ := fract_hit ((k0 : ℝ) * (α / 2)) ε hε0 hεh
  set k : ℤ := k0 + i * q
  have hk : (k : ℝ) * (α / 2) = ((k0 : ℝ) * (α / 2) + i * ε) + ((i * p : ℤ) : ℝ) := by
    simp only [k, hε]; push_cast; ring
  have hfk : Int.fract ((k : ℝ) * (α / 2)) < 1 / 2 := by rw [hk, Int.fract_add_intCast]; exact hfr
  have hiq : (i : ℤ) * q ≤ M * q := by
    have : (i : ℤ) ≤ M := by exact_mod_cast hiM
    nlinarith
  have hi0 : (0 : ℤ) ≤ i * q := by positivity
  refine ⟨2 * k, ⟨by omega, by omega, ?_⟩, by omega, by omega⟩
  rw [wy_two_mul, show (k : ℝ) * α = 2 * ((k : ℝ) * (α / 2)) by ring]
  exact floor_two_mul_even hfk

/-- On `T`, `W(t) ≥ (3/2)t`. -/
lemma three_le_two_mul_wy (h1 : 1 ≤ -c) (h2 : -c ≤ b - 2) {t : ℤ} (ht : t ∈ coneSet b c) :
    3 * t ≤ 2 * wy (alphaK b c) t := by
  obtain ⟨ht0, hte, -⟩ := ht
  obtain ⟨k, rfl⟩ : ∃ k, t = 2 * k := ⟨t / 2, by omega⟩
  rw [wy_two_mul]
  have h3 := three_lt_alphaK_cone h1 h2
  have hk : (0 : ℝ) ≤ k := by exact_mod_cast (show (0 : ℤ) ≤ k by omega)
  have : 3 * k ≤ ⌊(k : ℝ) * alphaK b c⌋ := by
    rw [Int.le_floor]; push_cast; nlinarith
  omega

lemma iterate_mem_coneSet (h1 : 1 ≤ -c) (h2 : -c ≤ b - 2) {t : ℤ} (ht : t ∈ coneSet b c)
    (i : ℕ) : (wy (alphaK b c))^[i] t ∈ coneSet b c := by
  induction i with
  | zero => exact ht
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact coneSet_trap h1 h2 _ ih

/-- Along `T`, every later point is `≥ (3/2)` times an earlier one. -/
lemma three_le_two_mul_iterate (h1 : 1 ≤ -c) (h2 : -c ≤ b - 2) {t : ℤ} (ht : t ∈ coneSet b c)
    (i : ℕ) : 3 * t ≤ 2 * (wy (alphaK b c))^[i + 1] t := by
  induction i with
  | zero => simpa using three_le_two_mul_wy h1 h2 ht
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    have hT := iterate_mem_coneSet h1 h2 ht (i + 1)
    have := three_le_two_mul_wy h1 h2 hT
    have := hT.1
    omega

/-- Every point of `T` lies on the forward orbit of an entry point. -/
lemma exists_entry (h1 : 1 ≤ -c) (h2 : -c ≤ b - 2) (t : ℤ) :
    ∃ e : ℤ, ∃ j : ℕ, t ∈ coneSet b c →
      (0 ≤ e ∧ e ∈ coneSet b c \ wkPerm b c h1 h2 '' coneSet b c) ∧
        (wy (alphaK b c))^[j] e = t := by
  induction t using Int.strongRec (m := 0) with
  | lt t ht => exact ⟨0, 0, fun h => absurd h.1 (by omega)⟩
  | ge t ht ih =>
    by_cases hT : t ∈ coneSet b c
    · by_cases hW : t ∈ wkPerm b c h1 h2 '' coneSet b c
      · obtain ⟨s, hs, rfl⟩ := hW
        rw [wkPerm_apply] at ih ⊢
        have h3 := three_le_two_mul_wy h1 h2 hs
        have := hs.1
        obtain ⟨e, j, hej⟩ := ih s (by omega)
        obtain ⟨he, hj⟩ := hej hs
        refine ⟨e, j + 1, fun _ => ⟨he, ?_⟩⟩
        rw [Function.iterate_succ_apply', hj]
      · exact ⟨t, 0, fun _ => ⟨⟨by omega, hT, hW⟩, rfl⟩⟩
    · exact ⟨0, 0, fun h => absurd h hT⟩

/-- **(ratified, Theorem K, infinitely many entry points; unconditional).**  Paper proof: if
`E = T ∖ W(T)` were finite, every `t ∈ T` would lie on the forward orbit of a point of `E`
(read backward inside `T` the values strictly decrease, `W(t) > t` on `T`, so the backward
orbit leaves `T` at an entry point); along `T`, `W(t) ≥ (3/2)t − 1`, so each forward orbit has
`O(log X)` points `≤ X` and `#(T ∩ [1, X]) = O(log X)`.  But `T` is syndetic: pick `q ≥ 1` with
`δ = ‖qα/2‖ ∈ (0, 1/4)` (Dirichlet; `α/2` irrational); along `k, k + q, k + 2q, …` the phase
`{kα/2}` moves by `±δ` per step, so it enters `[0, 1/2)` (i.e. `⌊kα⌋` even) within
`⌈1/δ⌉ + 1` steps, giving `#(T ∩ [1, X]) ≥ X/(2q(⌈1/δ⌉ + 1)) − 1`. -/
theorem coneEntry_infinite (h1 : 1 ≤ -c) (h2 : -c ≤ b - 2) :
    {n : ℤ | 0 ≤ n ∧ n ∈ coneSet b c \ wkPerm b c h1 h2 '' coneSet b c}.Infinite := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  classical
  set E := hfin.toFinset
  set N := E.card
  obtain ⟨L, hL0, hsyn⟩ := coneSet_syndetic h1 h2
  choose tf htf using hsyn
  choose ef jf hef using exists_entry h1 h2
  set Y : ℤ := 2 * (N + 1) * (L + 1) + 1
  have hY0 : 0 ≤ Y := by positivity
  -- the window points `t_i ∈ (Y + iL, Y + (i + 1)L]`, `i ≤ N`
  have hwin : ∀ i : ℕ, i ∈ Finset.range (N + 1) →
      tf (Y + i * L) (by positivity) ∈ coneSet b c ∧ Y + i * L < tf (Y + i * L) (by positivity) ∧
        tf (Y + i * L) (by positivity) ≤ Y + i * L + L := fun i _ => htf _ _
  have hmaps : ∀ i ∈ Finset.range (N + 1),
      ef (tf (Y + i * L) (by positivity)) ∈ E := by
    intro i hi
    obtain ⟨hT, -, -⟩ := hwin i hi
    obtain ⟨he, -⟩ := hef _ hT
    simpa [E] using he
  have hinj : Set.InjOn (fun i : ℕ => ef (tf (Y + i * L) (by positivity)))
      (Finset.range (N + 1) : Set ℕ) := by
    intro i hi i' hi' heq
    obtain ⟨hT, hlo, hhi⟩ := hwin i hi
    obtain ⟨hT', hlo', hhi'⟩ := hwin i' hi'
    simp only [Finset.coe_range, Set.mem_Iio] at hi hi'
    simp only at heq
    obtain ⟨⟨-, heT, -⟩, hj⟩ := hef _ hT
    obtain ⟨-, hj'⟩ := hef _ hT'
    rw [heq] at hj
    set t := tf (Y + i * L) (by positivity)
    set t' := tf (Y + i' * L) (by positivity)
    have hiL : (i : ℤ) * L ≤ N * L := by
      have : (i : ℤ) ≤ N := by omega
      nlinarith
    have hiL' : (i' : ℤ) * L ≤ N * L := by
      have : (i' : ℤ) ≤ N := by omega
      nlinarith
    have hNL : 0 ≤ (N : ℤ) * L := by positivity
    have hil0 : 0 ≤ (i : ℤ) * L := by positivity
    have hil0' : 0 ≤ (i' : ℤ) * L := by positivity
    -- both points lie in `[Y, 3Y/2)`
    have hsmall : 2 * t < 3 * Y := by nlinarith
    have hsmall' : 2 * t' < 3 * Y := by nlinarith
    have htt : t = t' := by
      rcases lt_trichotomy (jf t) (jf t') with hlt | hjj | hgt
      · obtain ⟨d, hd⟩ : ∃ d, jf t' = jf t + (d + 1) := ⟨jf t' - jf t - 1, by omega⟩
        have := three_le_two_mul_iterate h1 h2 (hT) d
        rw [← hj, ← Function.iterate_add_apply, show d + 1 + jf t = jf t' by omega, hj'] at this
        omega
      · rw [hjj] at hj; exact hj.symm.trans hj'
      · obtain ⟨d, hd⟩ : ∃ d, jf t = jf t' + (d + 1) := ⟨jf t - jf t' - 1, by omega⟩
        have := three_le_two_mul_iterate h1 h2 (hT') d
        rw [← hj', ← Function.iterate_add_apply, show d + 1 + jf t' = jf t by omega, hj] at this
        omega
    rw [htt] at hlo hhi
    have hLp : 0 < L ∨ L = 0 := by omega
    rcases hLp with hLp | hL
    · by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have : (i : ℤ) + 1 ≤ i' := by exact_mod_cast h
        nlinarith
      · have : (i' : ℤ) + 1 ≤ i := by exact_mod_cast h
        nlinarith
    · subst hL; omega
  have hcard : (Finset.range (N + 1)).card ≤ E.card := by
    refine Finset.card_le_card_of_injOn
      (fun i : ℕ => ef (tf (Y + i * L) (by positivity))) ?_ ?_
    · exact fun i hi => hmaps i hi
    · exact hinj
  rw [Finset.card_range] at hcard
  omega

/-- **(ratified, Theorem K).**  Every cone member has infinitely many infinite orbits.  Paper
proof: `infinitelyManyInfiniteOrbits_of_trap` with `coneSet_trap` and `coneEntry_infinite`. -/
theorem wkPerm_infinitelyManyInfiniteOrbits (h1 : 1 ≤ -c) (h2 : -c ≤ b - 2) :
    InfinitelyManyInfiniteOrbits (wkPerm b c h1 h2) :=
  infinitelyManyInfiniteOrbits_of_trap _ (coneSet_trap h1 h2) (coneEntry_infinite h1 h2)

/-- `⌊2v⌋` is even iff `{v} < 1/2`. -/
lemma floor_two_mul_even_iff (v : ℝ) : ⌊2 * v⌋ % 2 = 0 ↔ Int.fract v < 1 / 2 := by
  refine ⟨fun h => ?_, floor_two_mul_even⟩
  by_contra hc
  push Not at hc
  have : ⌊2 * v⌋ = 2 * ⌊v⌋ + 1 := by
    rw [Int.floor_eq_iff]
    have := Int.fract_lt_one v
    rw [Int.fract] at hc this
    push_cast
    constructor <;> linarith
  omega

open Classical in
/-- The number of entry points `T ∖ W(T)` in `[1, X]`. -/
noncomputable def coneEntryCount (b c : ℤ) (h1 : 1 ≤ -c) (h2 : -c ≤ b - 2) (X : ℕ) : ℕ :=
  ((Finset.Icc (1 : ℤ) X).filter fun n =>
    n ∈ coneSet b c \ wkPerm b c h1 h2 '' coneSet b c).card

open Classical in
/-- The phase count `#{k ∈ [1, N] : {k·α/2} < 1/2}`. -/
noncomputable def phaseCount (α : ℝ) (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter fun k : ℕ => Int.fract ((k : ℝ) * (α / 2)) ∈ Set.Ico 0 (1 / 2)).card

lemma mem_coneSet_two_mul_iff {k : ℤ} :
    2 * k ∈ coneSet b c ↔ 0 < k ∧ Int.fract ((k : ℝ) * (alphaK b c / 2)) < 1 / 2 := by
  unfold coneSet
  simp only [Set.mem_ofPred_eq]
  rw [wy_two_mul, show (k : ℝ) * alphaK b c = 2 * ((k : ℝ) * (alphaK b c / 2)) by ring,
    floor_two_mul_even_iff]
  constructor
  · rintro ⟨h0, -, h⟩; exact ⟨by omega, h⟩
  · rintro ⟨h0, h⟩; exact ⟨by omega, by omega, h⟩

open Classical in
/-- `#(T ∩ [1, X]) = #{k ≤ X/2 : {kα/2} < 1/2}`. -/
lemma card_coneSet_Icc (X : ℕ) :
    ((Finset.Icc (1 : ℤ) X).filter fun n => n ∈ coneSet b c).card =
      phaseCount (alphaK b c) (X / 2) := by
  unfold phaseCount
  symm
  apply Finset.card_nbij (fun k : ℕ => 2 * (k : ℤ))
  · intro k hk
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_Ico, Set.mem_ofPred_eq] at hk ⊢
    obtain ⟨⟨h1, h2⟩, -, hf⟩ := hk
    refine ⟨⟨by omega, by omega⟩, mem_coneSet_two_mul_iff.2 ⟨by omega, by exact_mod_cast hf⟩⟩
  · intro a _ b _ h
    have : (a : ℤ) = b := by simp only at h; omega
    exact_mod_cast this
  · intro n hn
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hn
    obtain ⟨⟨h1, h2⟩, hT⟩ := hn
    have he := hT.2.1
    obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
    obtain ⟨hk0, hf⟩ := mem_coneSet_two_mul_iff.1 hT
    refine ⟨k.toNat, ?_, by simp only; omega⟩
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_Ico, Set.mem_ofPred_eq]
    refine ⟨⟨by omega, by omega⟩, Int.fract_nonneg _, ?_⟩
    have : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast Int.toNat_of_nonneg (by omega)
    rw [this]; exact hf

open Classical in
/-- `#(W(T) ∩ [1, X]) = #{k ≤ ⌊(X + 1)/α⌋ : {kα/2} < 1/2}`. -/
lemma card_image_coneSet_Icc (h1 : 1 ≤ -c) (h2 : -c ≤ b - 2) (X : ℕ) :
    ((Finset.Icc (1 : ℤ) X).filter fun n => n ∈ wkPerm b c h1 h2 '' coneSet b c).card =
      phaseCount (alphaK b c) ⌊(alphaK b c)⁻¹ * X + (alphaK b c)⁻¹⌋₊ := by
  set α := alphaK b c
  have hα3 := three_lt_alphaK_cone h1 h2
  have hirr := irrational_alphaK_cone h1 h2
  have hα0 : 0 < α := by linarith
  -- `⌊kα⌋ ≤ X ↔ k ≤ ⌊(X + 1)/α⌋₊` for `k ≥ 1`
  have hkey : ∀ k : ℕ, 1 ≤ k → (⌊(k : ℝ) * α⌋ ≤ X ↔ k ≤ ⌊α⁻¹ * X + α⁻¹⌋₊) := by
    intro k hk
    have hne : (k : ℝ) * α ≠ ((X + 1 : ℕ) : ℝ) := by
      have := (hirr.natCast_mul (m := k) (by omega)).ne_nat (X + 1)
      exact this
    rw [Int.floor_le_iff, Nat.le_floor_iff (by positivity)]
    have e : α⁻¹ * X + α⁻¹ = (X + 1) / α := by field_simp
    rw [e, le_div_iff₀ hα0]
    push_cast at hne ⊢
    constructor
    · intro h; linarith
    · intro h; exact lt_of_le_of_ne h hne
  unfold phaseCount
  symm
  apply Finset.card_nbij (fun k : ℕ => wy α (2 * (k : ℤ)))
  · intro k hk
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_Ico, Set.mem_ofPred_eq] at hk ⊢
    obtain ⟨⟨hk1, hk2⟩, -, hf⟩ := hk
    have hT : 2 * (k : ℤ) ∈ coneSet b c :=
      mem_coneSet_two_mul_iff.2 ⟨by omega, by exact_mod_cast hf⟩
    have hWT := coneSet_trap h1 h2 _ hT
    rw [wkPerm_apply] at hWT
    refine ⟨⟨hWT.1, ?_⟩, ⟨_, hT, rfl⟩⟩
    rw [wy_two_mul]; push_cast
    exact (hkey k hk1).2 hk2
  · intro a _ b _ h
    have := (wy_bijective (one_lt_alphaK_cone h1 h2)).1 h
    omega
  · intro n hn
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hn
    obtain ⟨⟨hn1, hn2⟩, s, hs, rfl⟩ := hn
    have he := hs.2.1
    obtain ⟨k, rfl⟩ : ∃ k, s = 2 * k := ⟨s / 2, by omega⟩
    obtain ⟨hk0, hf⟩ := mem_coneSet_two_mul_iff.1 hs
    have hkn : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg (by omega)
    refine ⟨k.toNat, ?_, by simp only [hkn]; rfl⟩
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_Ico, Set.mem_ofPred_eq]
    have hkr : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast hkn
    refine ⟨⟨by omega, (hkey _ (by omega)).1 ?_⟩, Int.fract_nonneg _, by rw [hkr]; exact hf⟩
    rw [hkr, ← wy_two_mul]
    rw [wkPerm_apply] at hn2
    exact hn2

/-- **(ratified, Theorem K, entry density, conditional on equidistribution).**  The entry points
have density `(1/4)(1 − 2/α)`, so at least that many infinite orbits per unit meet `[1, X]`.
Paper proof: `⌊kα⌋` is even iff `{kα/2} < 1/2`; by `WeylEquidistribution` (`α/2` irrational)
`#(T ∩ [1, X]) ∼ X/4`.  `W` is injective on `T` and `W(2k) = ⌊kα⌋`, so
`#(W(T) ∩ [1, X]) = #{k ≥ 1 : ⌊kα⌋ even, ⌊kα⌋ ≤ X} ∼ X/(2α)`, and `W(T) ⊆ T`. -/
theorem tendsto_coneEntryCount (h1 : 1 ≤ -c) (h2 : -c ≤ b - 2) (hW : WeylEquidistribution) :
    Tendsto (fun X : ℕ => (coneEntryCount b c h1 h2 X : ℝ) / X) atTop
      (𝓝 ((1 - 2 / alphaK b c) / 4)) := by
  classical
  set α := alphaK b c
  have hα3 := three_lt_alphaK_cone h1 h2
  have hα0 : 0 < α := by linarith
  have hθ : Irrational (α / 2) := (irrational_alphaK_cone h1 h2).div_natCast (m := 2) (by norm_num)
  have hW' : Tendsto (fun N : ℕ => (phaseCount α N : ℝ) / N) atTop (𝓝 (1 / 2)) := by
    have := hW (α / 2) hθ 0 (1 / 2) le_rfl (by norm_num) (by norm_num)
    simpa [phaseCount] using this
  -- the count splits as `#(T ∩ [1, X]) − #(W(T) ∩ [1, X])`
  have hsplit : ∀ X : ℕ, (coneEntryCount b c h1 h2 X : ℝ) =
      phaseCount α (X / 2) - phaseCount α ⌊α⁻¹ * X + α⁻¹⌋₊ := by
    intro X
    rw [← card_coneSet_Icc, ← card_image_coneSet_Icc h1 h2]
    have hsub : (Finset.Icc (1 : ℤ) X).filter (fun n => n ∈ wkPerm b c h1 h2 '' coneSet b c) ⊆
        (Finset.Icc (1 : ℤ) X).filter (fun n => n ∈ coneSet b c) := by
      intro n hn
      simp only [Finset.mem_filter] at hn ⊢
      obtain ⟨hI, s, hs, rfl⟩ := hn
      exact ⟨hI, coneSet_trap h1 h2 s hs⟩
    rw [← Nat.cast_sub (Finset.card_le_card hsub), ← Finset.card_sdiff_of_subset hsub]
    unfold coneEntryCount
    congr 2
    ext n
    simp only [Finset.mem_filter, Finset.mem_sdiff, Set.mem_sdiff]
    tauto
  have hA : Tendsto (fun X : ℕ => (phaseCount α (X / 2) : ℝ) / X) atTop (𝓝 (1 / 2 * (1 / 2))) := by
    have hfe : ∀ X : ℕ, ⌊(1 / 2 : ℝ) * X + 0⌋₊ = X / 2 := by
      intro X
      have := Nat.floor_div_eq_div (K := ℝ) X 2
      push_cast at this
      rw [add_zero, one_div_mul_eq_div, this]
    refine (tendsto_comp_div hW' (tendsto_floor_linear (by norm_num) 0)
      (tendsto_floor_linear_div (by norm_num) 0)).congr' (Eventually.of_forall fun X => ?_)
    simp only [hfe]
  have hB : Tendsto (fun X : ℕ => (phaseCount α ⌊α⁻¹ * X + α⁻¹⌋₊ : ℝ) / X) atTop
      (𝓝 (1 / 2 * α⁻¹)) :=
    tendsto_comp_div hW' (tendsto_floor_linear (inv_pos.2 hα0) _)
      (tendsto_floor_linear_div (inv_pos.2 hα0) _)
  have hlim : (1 - 2 / α) / 4 = 1 / 2 * (1 / 2) - 1 / 2 * α⁻¹ := by field_simp; ring
  rw [hlim]
  refine (hA.sub hB).congr' (Eventually.of_forall fun X => ?_)
  show _ = (coneEntryCount b c h1 h2 X : ℝ) / X
  rw [hsplit, sub_div]

end Cone

section Anticone

variable {b c : ℤ}

/-- In the anticone, `b < √(b² + 4c) < b + 2`. -/
lemma sqrt_bounds_anticone (h1 : 1 ≤ c) (h2 : c ≤ b) :
    (b : ℝ) < √((b : ℝ) ^ 2 + 4 * c) ∧ √((b : ℝ) ^ 2 + 4 * c) < b + 2 := by
  have hb : (1 : ℝ) ≤ b := by exact_mod_cast (show (1 : ℤ) ≤ b by omega)
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast h1
  have hc2 : (c : ℝ) ≤ b := by exact_mod_cast h2
  constructor
  · rw [Real.lt_sqrt (by linarith)]; nlinarith
  · rw [Real.sqrt_lt' (by linarith)]; nlinarith

/-- **(ratified).**  In the anticone `1 ≤ c ≤ b`: `1 < α`. -/
theorem one_lt_alphaK_anticone (h1 : 1 ≤ c) (h2 : c ≤ b) : 1 < alphaK b c := by
  obtain ⟨hl, -⟩ := sqrt_bounds_anticone h1 h2
  unfold alphaK
  have : (1 : ℝ) ≤ b := by exact_mod_cast (show (1 : ℤ) ≤ b by omega)
  linarith

/-- **(ratified).**  In the anticone the conjugate lies in `(−1, 0)`: `b² < b² + 4c < (b + 2)²`. -/
theorem conj_mem_Ioo_anticone (h1 : 1 ≤ c) (h2 : c ≤ b) :
    -1 < (b : ℝ) - alphaK b c / 2 ∧ (b : ℝ) - alphaK b c / 2 < 0 := by
  obtain ⟨hl, hu⟩ := sqrt_bounds_anticone h1 h2
  unfold alphaK
  constructor <;> linarith

/-- **(ratified).**  In the anticone `α` is irrational (the only square strictly between `b²` and
`(b + 2)²` is `(b + 1)² ≢ b² (mod 4)`). -/
theorem irrational_alphaK_anticone (h1 : 1 ≤ c) (h2 : c ≤ b) : Irrational (alphaK b c) := by
  have hns : ¬IsSquare (b ^ 2 + 4 * c) := by
    rintro ⟨r, hr⟩
    have hsq := sq_eq_of_between (L := b) (r := r) (by omega) (by nlinarith) (by nlinarith)
    have : 4 * c = 2 * b + 1 := by linear_combination hr.trans hsq
    omega
  have hirr : Irrational √(((b ^ 2 + 4 * c : ℤ)) : ℝ) :=
    irrational_sqrt_intCast_iff.2 ⟨hns, by nlinarith⟩
  push_cast at hirr
  exact hirr.intCast_add b

/-- **(ratified, anticone identity).**  For `k ≠ 0` with `W(2k)` even,
`W²(2k) = b·W(2k) + c·2k − 1`, which is odd: EE ⇒ O.  Paper proof: Theorem A′ with
`⌊x′f⌋ = −1` (`−1 < x′ < 0`, and `0 < f = {kα} < 1` since `kα ∉ ℤ`). -/
theorem wy_wy_of_even_even_anticone (h1 : 1 ≤ c) (h2 : c ≤ b) {k : ℤ} (hk : k ≠ 0)
    (h : wy (alphaK b c) (2 * k) % 2 = 0) :
    wy (alphaK b c) (wy (alphaK b c) (2 * k)) =
      b * wy (alphaK b c) (2 * k) + c * (2 * k) - 1 := by
  rw [wy_wy_of_even_even (alphaK_half_sq (by nlinarith)) k h]
  obtain ⟨hl, hu⟩ := conj_mem_Ioo_anticone h1 h2
  have hirr : Irrational ((k : ℝ) * alphaK b c) :=
    (irrational_alphaK_anticone h1 h2).intCast_mul hk
  have hf0 : 0 < Int.fract ((k : ℝ) * alphaK b c) := by
    rcases (Int.fract_nonneg ((k : ℝ) * alphaK b c)).lt_or_eq with h' | h'
    · exact h'
    · exfalso
      rw [eq_comm, Int.fract_eq_zero_iff] at h'
      obtain ⟨z, hz⟩ := h'
      exact hirr.ne_int z hz.symm
  have hf1 := Int.fract_lt_one ((k : ℝ) * alphaK b c)
  have : ⌊((b : ℝ) - alphaK b c / 2) * Int.fract ((k : ℝ) * alphaK b c)⌋ = -1 := by
    rw [Int.floor_eq_iff]
    push_cast
    constructor <;> nlinarith
  rw [this]
  ring

end Anticone

end CollatzMoonshot.WythoffCone
