/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalGlobal

/-!
# Ray joins: the orbit of `3^m` cannot reach a power of 2 early (research §52)

The *ray* `2^m → 3·2^{m−1} → ⋯ → 3^m` is the maximal run of `S`-units (`S = {2, 3}`) on an orbit: an
orbit enters it only at `2^m` and leaves only at `3^m`.  A *join* is `U^k(3^m) = 2^{m′}`; it is the
`S`-unit equation `2^{b_k + m′} − 3^{k+m} = C_k` for the prefix word of length `k`.  Round-5
ideation (2026-10-15, Fable, "Theorem J") combined the exact error bound along the orbit with
Ellison's explicit lower bound for `|2^x − 3^y|` to show a ray cannot join within about
`2.1m` steps, past the residue horizon `≈ 1.06m`.  Ellison's theorem enters as the hypothesis
`EllisonBound`.

* `ray_join_three`, `ray_join_four`: the two known joins, `27 → 32` in 9 steps and `81 → 512` in 37.
* `no_early_ray_join`: given `EllisonBound`, `U^k(3^m)` is not a power of 2 for `1 ≤ k ≤ 2m − 2`.

Conjecture J (research §52, 60%): joins happen only from `3^1, …, 3^4`; it would imply (a).
-/

namespace CollatzMoonshot.Amusical

/-- **Literature (Ellison, Séminaire de Théorie des Nombres de Bordeaux 1970/71, exp. 12, Thm 3).**
`|2^x − 3^y| > 2^x e^{−x/10}` for positive `x, y` with `x` outside an explicit finite set. -/
def EllisonBound : Prop :=
  ∀ x y : ℕ, 0 < x → 0 < y →
    x ∉ ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 16, 19, 27} : Finset ℕ) →
    (2 : ℝ) ^ x * Real.exp (-(x : ℝ) / 10) < |(2 : ℝ) ^ x - 3 ^ y|

/-- **Proved.**  The ray of `27` joins `32` after 9 steps. -/
theorem ray_join_three : amusical^[9] 27 = 32 := by
  decide +kernel

/-- **Proved.**  The ray of `81` joins `512` after 37 steps. -/
theorem ray_join_four : amusical^[37] 81 = 512 := by
  decide +kernel

/-- The finite cases `k + m ≤ 17`: no `U^k(3^m)` there divides `2^40`. -/
private theorem fin_check : ∀ m < 17, ∀ k < 18, 1 ≤ k → k + 2 ≤ 2 * m → k + m ≤ 17 →
    (2 : ℤ) ^ 40 % amusical^[k] ((3 : ℤ) ^ m) ≠ 0 := by
  decide +kernel

/-- From `2^(X+1) > 3^Y` with `2Y ≥ 3k + 2`: `8X ≥ 19k + 4` (via `27^4 ≥ 2^19`). -/
private theorem eight_mul_ge (X Y k : ℕ) (h : 3 ^ Y < 2 ^ (X + 1)) (hY : 3 * k + 2 ≤ 2 * Y) :
    19 * k + 4 ≤ 8 * X := by
  have h1 : 3 ^ (3 * k + 2) < 2 ^ (2 * X + 2) := by
    calc 3 ^ (3 * k + 2) ≤ 3 ^ (2 * Y) := Nat.pow_le_pow_right (by norm_num) hY
      _ = (3 ^ Y) ^ 2 := by rw [← pow_mul, mul_comm]
      _ < (2 ^ (X + 1)) ^ 2 := Nat.pow_lt_pow_left h (by norm_num)
      _ = 2 ^ (2 * X + 2) := by rw [← pow_mul]; ring_nf
  have h2 : 2 ^ (19 * k + 12) < 2 ^ (8 * X + 8) := by
    calc 2 ^ (19 * k + 12) = (2 ^ 19) ^ k * 2 ^ 12 := by rw [pow_add, pow_mul]
      _ ≤ (3 ^ 12) ^ k * 3 ^ 8 :=
          Nat.mul_le_mul (Nat.pow_le_pow_left (by norm_num) k) (by norm_num)
      _ = (3 ^ (3 * k + 2)) ^ 4 := by rw [← pow_mul, ← pow_mul, ← pow_add]; ring_nf
      _ < (2 ^ (2 * X + 2)) ^ 4 := Nat.pow_lt_pow_left h1 (by norm_num)
      _ = 2 ^ (8 * X + 8) := by rw [← pow_mul]; ring_nf
  have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 h2
  omega

/-- **Proved (Theorem J).**  Given Ellison's bound, the orbit of `3^m` meets no power of 2 within
its first `2m − 2` steps.  Proof: a join is `2^X = 3^Y + c` with `Y = k + m`, `|c| < 4^k`
(`amusical_iterate_affine`), so `2^(X+1) > 3^Y` and `8X ≥ 19k + 4` (`27^4 ≥ 2^19`).  If `Y ≤ 17` a
kernel check finishes; otherwise `X ≥ 28` is outside Ellison's set and `2^X e^(−X/10) < 4^k`
contradicts `8X ≥ 19k + 4` because `3 log 2 > 1.9`. -/
theorem no_early_ray_join (hE : EllisonBound) (m k m' : ℕ) (hk : 1 ≤ k) (hkm : k + 2 ≤ 2 * m) :
    amusical^[k] ((3 : ℤ) ^ m) ≠ 2 ^ m' := by
  intro hjoin
  obtain ⟨B, c, hBk, hB2k, hc, heq⟩ := amusical_iterate_affine k ((3 : ℤ) ^ m)
  rw [hjoin, ← pow_add, ← pow_add] at heq
  -- `2^X = 3^Y + c` with `X = B + m'`, `Y = k + m`.
  set X := B + m' with hX
  set Y := k + m with hY
  have h4 : (2 : ℤ) * 4 ^ k ≤ 3 ^ Y := by
    have : ((2 * 4 ^ k : ℕ) : ℤ) ≤ ((3 ^ Y : ℕ) : ℤ) := by
      have hsq : (2 * 4 ^ k) ^ 2 ≤ (3 ^ Y) ^ 2 := by
        calc (2 * 4 ^ k) ^ 2 = 4 * 16 ^ k := by
                rw [mul_pow, show (16 : ℕ) = 4 ^ 2 by norm_num, ← pow_mul, ← pow_mul, mul_comm k 2]
                norm_num
          _ ≤ 9 * 27 ^ k := by gcongr <;> norm_num
          _ = 3 ^ (3 * k + 2) := by rw [pow_add, pow_mul]; ring
          _ ≤ 3 ^ (2 * Y) := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = (3 ^ Y) ^ 2 := by rw [← pow_mul, mul_comm]
      exact_mod_cast (Nat.pow_le_pow_iff_left (by norm_num)).1 hsq
    exact_mod_cast this
  have hc' := abs_lt.1 hc
  have hlow : (3 : ℤ) ^ Y < 2 ^ (X + 1) := by rw [pow_succ]; linarith
  have hlowN : 3 ^ Y < 2 ^ (X + 1) := by exact_mod_cast hlow
  have h8 := eight_mul_ge X Y k hlowN (by omega)
  by_cases hsmall : k + m ≤ 17
  · -- finite check: `2^m' ∣ 2^40`
    have hm' : m' ≤ 40 := by
      have hup : (2 : ℤ) ^ m' < 2 ^ 41 := by
        have h1 : (2 : ℤ) ^ m' ≤ 2 ^ X := by
          rw [hX, pow_add]; exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
        have h3 : (3 : ℤ) ^ Y ≤ 3 ^ 17 := pow_le_pow_right₀ (by norm_num) hsmall
        have h44 : (4 : ℤ) ^ k ≤ 3 ^ Y := by linarith [pow_pos (by norm_num : (0:ℤ) < 4) k]
        norm_num at h3 ⊢
        linarith
      have := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℤ) < 2)).1 hup
      omega
    have hdvd : (2 : ℤ) ^ m' ∣ 2 ^ 40 := pow_dvd_pow 2 hm'
    exact fin_check m (by omega) k (by omega) hk hkm hsmall
      (by rw [hjoin]; exact Int.emod_eq_zero_of_dvd hdvd)
  · -- Ellison
    have hXbig : 28 ≤ X := by
      have h3 : 3 ^ 18 ≤ 3 ^ Y := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : 2 ^ 28 < 2 ^ (X + 1) := by
        calc 2 ^ 28 < 3 ^ 18 := by norm_num
          _ ≤ 3 ^ Y := h3
          _ < 2 ^ (X + 1) := hlowN
      have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 this
      omega
    have hS : X ∉ ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 16, 19, 27} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have hEl := hE X Y (by omega) (by omega) hS
    have hcR : |(2 : ℝ) ^ X - 3 ^ Y| < 4 ^ k := by
      have : (2 : ℤ) ^ X - 3 ^ Y = c := by linarith
      have h' : |((2 : ℤ) ^ X - 3 ^ Y : ℤ)| < 4 ^ k := this ▸ hc
      exact_mod_cast h'
    have hlt := hEl.trans hcR
    have hlog := Real.log_lt_log (by positivity) hlt
    rw [Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_pow,
      Real.log_pow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at hlog
    have hl2 := Real.log_two_gt_d9
    have h8R : (19 * k + 4 : ℝ) ≤ 8 * X := by exact_mod_cast h8
    push_cast at hlog
    nlinarith

end CollatzMoonshot.Amusical
