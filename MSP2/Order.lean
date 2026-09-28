/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MSP2.Defs

/-!
# MSP²: `2` is a primitive root modulo `3ⁿ`

The vertical rule `tA` of the Generator Table (§15.9) is multiplication by `2⁻¹` modulo the
column coefficient `A` (§16.7.1).  Every statement the article makes about *distances* along a
vertical loop — §16.3 (the useful distance `3^(n+1) + 1` from `1` to `Bₙ`), §16.7.2 (the loop
length `2·3^(n−1)`), §16.5 (the distance `2·3^(m+1)` between the two sides) — therefore reduces
to the multiplicative order of `2` modulo `3ⁿ`.

Everything here descends from one lifting-the-exponent induction, `two_pow_three_pow`:

  `2 ^ 3ⁿ = −1 + 3^(n+1) · cₙ` with `cₙ ≡ 1 (mod 3)`.

The `−1` gives `2^(3ⁿ) ≡ −1 (mod 3^(n+1))`, so the order of `2` is `2·3ⁿ` there and not a
proper divisor; the extra information `cₙ ≡ 1 (mod 3)` pins the *cube root of unity*
`2^(2·3ⁿ) ≡ 1 + 3^(n+1) (mod 3^(n+2))`, which is what §16.5 needs.
-/

namespace MSP2

/-! ## The lifting-the-exponent induction -/

/-- **The one computation everything rests on.**  `2 ^ 3ⁿ = −1 + 3^(n+1)·c` with `c ≡ 1 (mod 3)`.
Induction on `n`: cubing `−1 + 3^(n+1)c` gives `−1 + 3^(n+2)(c − 3^(n+1)c² + 3^(2n+1)c³)`, and the
new cofactor is `≡ c (mod 3)`. -/
theorem two_pow_three_pow (n : ℕ) :
    ∃ c : ℤ, (2 : ℤ) ^ (3 ^ n) = -1 + 3 ^ (n + 1) * c ∧ c % 3 = 1 := by
  induction n with
  | zero => exact ⟨1, by norm_num, by norm_num⟩
  | succ n ih =>
    obtain ⟨c, hc, hc3⟩ := ih
    refine ⟨c - 3 ^ (n + 1) * c ^ 2 + 3 ^ (2 * n + 1) * c ^ 3, ?_, ?_⟩
    · have hpow : (3 : ℕ) ^ (n + 1) = 3 ^ n * 3 := by ring
      rw [hpow, pow_mul, hc]
      ring
    · have key : c - 3 ^ (n + 1) * c ^ 2 + 3 ^ (2 * n + 1) * c ^ 3
          = c + 3 * (-(3 ^ n * c ^ 2) + 3 ^ (2 * n) * c ^ 3) := by ring
      rw [key, Int.add_mul_emod_self_left, hc3]

/-- `2 ^ 3ⁿ ≡ −1 (mod 3^(n+1))`. -/
theorem two_pow_three_pow_modEq (n : ℕ) :
    (2 : ℤ) ^ (3 ^ n) ≡ -1 [ZMOD (3 ^ (n + 1) : ℕ)] := by
  obtain ⟨c, hc, -⟩ := two_pow_three_pow n
  refine Int.modEq_iff_dvd.mpr ?_
  push_cast
  exact ⟨-c, by linarith⟩

/-- In `ZMod (3^(n+1))`: `2 ^ 3ⁿ = −1`. -/
theorem two_pow_three_pow_zmod (n : ℕ) : (2 : ZMod (3 ^ (n + 1))) ^ (3 ^ n) = -1 := by
  have h := (ZMod.intCast_eq_intCast_iff _ _ _).mpr (two_pow_three_pow_modEq n)
  push_cast at h
  exact h

/-- The exact power of `3` in `2 ^ (2·3ⁿ) − 1` is `3^(n+1)`: it is *not* divisible by
`3^(n+2)`.  This is what rules out every proper divisor of the order. -/
theorem not_dvd_two_pow_two_mul (n : ℕ) :
    ¬ ((3 : ℤ) ^ (n + 2) ∣ (2 : ℤ) ^ (2 * 3 ^ n) - 1) := by
  obtain ⟨c, hc, hc3⟩ := two_pow_three_pow n
  intro ⟨k, hk⟩
  -- `2 ^ (2·3ⁿ) − 1 = 3^(n+1) · c · (−2 + 3^(n+1)·c)`
  have hfac : (2 : ℤ) ^ (2 * 3 ^ n) - 1 = 3 ^ (n + 1) * (c * (-2 + 3 ^ (n + 1) * c)) := by
    have : (2 : ℤ) ^ (2 * 3 ^ n) = ((2 : ℤ) ^ (3 ^ n)) ^ 2 := by
      rw [← pow_mul]; ring_nf
    rw [this, hc]; ring
  have h32 : (3 : ℤ) ^ (n + 2) = 3 ^ (n + 1) * 3 := by ring
  have hne : (0 : ℤ) < 3 ^ (n + 1) := by positivity
  have hcancel : c * (-2 + 3 ^ (n + 1) * c) = 3 * k := by
    have := hk
    rw [hfac, h32] at this
    have h := mul_left_cancel₀ (ne_of_gt hne) (by linarith : (3:ℤ) ^ (n + 1) * (c * (-2 + 3 ^ (n + 1) * c)) = 3 ^ (n + 1) * (3 * k))
    exact h
  -- but `c ≡ 1` and `−2 + 3^(n+1)c ≡ 1 (mod 3)`
  have h1 : (3 : ℤ) ^ (n + 1) = 3 * 3 ^ n := by ring
  rw [h1] at hcancel
  have hmod : (c * (-2 + 3 * 3 ^ n * c)) % 3 = 1 := by
    obtain ⟨t, ht⟩ : ∃ t, c = 1 + 3 * t := ⟨c / 3, by omega⟩
    subst ht
    have e : (1 + 3 * t) * (-2 + 3 * 3 ^ n * (1 + 3 * t))
        = 1 + 3 * (-1 - 2 * t + 3 ^ n * (1 + 3 * t) * (1 + 3 * t)) := by ring
    rw [e, Int.add_mul_emod_self_left]
    norm_num
  rw [hcancel] at hmod
  omega

/-! ## The order of `2` -/

/-- Bridge: `2^e = 1` in `ZMod N` means `N ∣ 2^e − 1` over `ℤ`. -/
theorem int_dvd_of_zmod_pow_eq_one {N e : ℕ} (h : (2 : ZMod N) ^ e = 1) :
    ((N : ℤ)) ∣ (2 : ℤ) ^ e - 1 := by
  have hc : (((2 : ℤ) ^ e : ℤ) : ZMod N) = ((1 : ℤ) : ZMod N) := by push_cast; exact h
  have h2 := (ZMod.intCast_eq_intCast_iff _ _ _).mp hc
  have h3 : ((N : ℤ)) ∣ 1 - 2 ^ e := Int.modEq_iff_dvd.mp h2
  have he : (2 : ℤ) ^ e - 1 = -(1 - 2 ^ e) := by ring
  rw [he]
  exact dvd_neg.mpr h3

/-- **§16.7.2.**  `2` is a primitive root modulo `3^(m+1)`: its multiplicative order is
`2·3^m = φ(3^(m+1))`.

The order divides `2·3^m` because `2^(3^m) = −1`.  It is not a proper divisor: an odd order
would divide `3^m`, giving `2^(3^m) = 1 ≠ −1`; and an even order `2·3^j` with `j < m` would
divide `2·3^(m−1)`, forcing `3^(m+1) ∣ 2^(2·3^(m−1)) − 1`, which `not_dvd_two_pow_two_mul`
rules out. -/
theorem orderOf_two_zmod (m : ℕ) : orderOf (2 : ZMod (3 ^ (m + 1))) = 2 * 3 ^ m := by
  have hpow : (2 : ZMod (3 ^ (m + 1))) ^ (3 ^ m) = -1 := two_pow_three_pow_zmod m
  have hsq : (2 : ZMod (3 ^ (m + 1))) ^ (2 * 3 ^ m) = 1 := by
    rw [mul_comm, pow_mul, hpow]; norm_num
  have hdvd : orderOf (2 : ZMod (3 ^ (m + 1))) ∣ 2 * 3 ^ m := orderOf_dvd_of_pow_eq_one hsq
  have hne1 : (-1 : ZMod (3 ^ (m + 1))) ≠ 1 := by
    intro h
    have h2 : ((2 : ℕ) : ZMod (3 ^ (m + 1))) = 0 := by
      push_cast
      linear_combination -h
    have h3 := (CharP.cast_eq_zero_iff (ZMod (3 ^ (m + 1))) (3 ^ (m + 1)) 2).mp h2
    have h4 : (3 : ℕ) ^ 1 ≤ 3 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h5 := Nat.le_of_dvd (by norm_num) h3
    simp at h4
    omega
  have hnotdvd : ¬ orderOf (2 : ZMod (3 ^ (m + 1))) ∣ 3 ^ m := by
    intro h
    have h1 := orderOf_dvd_iff_pow_eq_one.mp h
    rw [hpow] at h1
    exact hne1 h1
  rcases Nat.even_or_odd (orderOf (2 : ZMod (3 ^ (m + 1)))) with he | ho
  · obtain ⟨d, hd⟩ := he
    have hd' : orderOf (2 : ZMod (3 ^ (m + 1))) = 2 * d := by omega
    have hd2 : d ∣ 3 ^ m :=
      (Nat.mul_dvd_mul_iff_left (show 0 < 2 by norm_num)).mp (by rw [← hd']; exact hdvd)
    obtain ⟨j, hj, hdj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd2
    rcases eq_or_lt_of_le hj with rfl | hjm
    · rw [hd', hdj]
    · exfalso
      obtain ⟨q, rfl⟩ : ∃ q, m = q + 1 := ⟨m - 1, by omega⟩
      have hord : orderOf (2 : ZMod (3 ^ (q + 1 + 1))) ∣ 2 * 3 ^ q := by
        rw [hd', hdj]
        exact Nat.mul_dvd_mul_left 2 (pow_dvd_pow 3 (by omega))
      have h1 : (2 : ZMod (3 ^ (q + 1 + 1))) ^ (2 * 3 ^ q) = 1 :=
        orderOf_dvd_iff_pow_eq_one.mp hord
      have h2 := int_dvd_of_zmod_pow_eq_one h1
      have e : (((3 : ℕ) ^ (q + 1 + 1) : ℕ) : ℤ) = 3 ^ (q + 2) := by push_cast; ring
      rw [e] at h2
      exact not_dvd_two_pow_two_mul q h2
  · exact absurd (Nat.Coprime.dvd_of_dvd_mul_left
      (Nat.coprime_two_right.mpr ho) hdvd) hnotdvd

end MSP2
