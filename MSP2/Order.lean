/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
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

/-! ## The vertical rule as multiplication by `2⁻¹` -/

/-- **§16.7.1.**  For odd `A`, `2·T_A(b) ≡ b (mod A)`. -/
theorem tA_two_modEq {A : ℕ} (hA : A % 2 = 1) (b : ℕ) : 2 * tA A b ≡ b [MOD A] := by
  unfold tA
  split
  · next h => rw [show 2 * (b / 2) = b by omega]
  · next h =>
    rw [show 2 * ((A + b) / 2) = A + b by omega]
    exact Nat.add_mod_left A b

/-- The vertical rule keeps a column entry inside `[0, A)`. -/
theorem tA_lt {A b : ℕ} (hA : A % 2 = 1) (hb : b < A) : tA A b < A := by
  unfold tA; split <;> omega

theorem tA_iterate_lt {A : ℕ} (hA : A % 2 = 1) {b : ℕ} (hb : b < A) (i : ℕ) :
    (tA A)^[i] b < A := by
  induction i with
  | zero => simpa using hb
  | succ i ih => rw [Function.iterate_succ_apply']; exact tA_lt hA ih

/-- Iterating: `2^i · T_A^i(b) ≡ b (mod A)`, i.e. `T_A^i` is multiplication by `2^(−i)`. -/
theorem two_pow_mul_iterate {A : ℕ} (hA : A % 2 = 1) (b i : ℕ) :
    2 ^ i * (tA A)^[i] b ≡ b [MOD A] := by
  induction i with
  | zero => simpa using Nat.ModEq.refl b
  | succ i ih =>
    calc 2 ^ (i + 1) * (tA A)^[i + 1] b
        = 2 ^ i * (2 * tA A ((tA A)^[i] b)) := by rw [Function.iterate_succ_apply']; ring
      _ ≡ 2 ^ i * (tA A)^[i] b [MOD A] := Nat.ModEq.mul_left _ (tA_two_modEq hA _)
      _ ≡ b [MOD A] := ih

/-- Cancelling the factor `2`, which is invertible modulo an odd `A`. -/
theorem modEq_of_two_mul {A x y : ℕ} (hA : A % 2 = 1) (h : 2 * x ≡ 2 * y [MOD A]) :
    x ≡ y [MOD A] :=
  Nat.ModEq.cancel_left_of_coprime (Nat.coprime_two_right.mpr (Nat.odd_iff.mpr hA)) h

/-- **The characterisation of a vertical distance.**  `T_A^i(b) = x` exactly when `x` is the
representative in `[0, A)` with `2^i·x ≡ b (mod A)`. -/
theorem tA_iterate_eq {A : ℕ} (hA : A % 2 = 1) {b x : ℕ} (hb : b < A) (hx : x < A) (i : ℕ)
    (h : 2 ^ i * x ≡ b [MOD A]) : (tA A)^[i] b = x := by
  have hco : Nat.Coprime A (2 ^ i) :=
    Nat.Coprime.pow_right i (Nat.coprime_two_right.mpr (Nat.odd_iff.mpr hA))
  have h2 : (tA A)^[i] b ≡ x [MOD A] :=
    Nat.ModEq.cancel_left_of_coprime hco ((two_pow_mul_iterate hA b i).trans h.symm)
  unfold Nat.ModEq at h2
  rwa [Nat.mod_eq_of_lt (tA_iterate_lt hA hb i), Nat.mod_eq_of_lt hx] at h2

/-! ## Consequences of primitivity -/

theorem zmod_pow_eq_one_iff {A e : ℕ} : (2 : ZMod A) ^ e = 1 ↔ 2 ^ e ≡ 1 [MOD A] := by
  have h := (ZMod.natCast_eq_natCast_iff (2 ^ e) 1 A)
  push_cast at h
  exact h

/-- If `3^(m+1) ∣ 2^k + 1` then `3^m ∣ k`: a `−1` can only be hit at the half-order. -/
theorem three_pow_dvd_of_dvd_two_pow_add_one {m k : ℕ} (h : (3 : ℕ) ^ (m + 1) ∣ 2 ^ k + 1) :
    (3 : ℕ) ^ m ∣ k := by
  have h0 : ((2 ^ k + 1 : ℕ) : ZMod (3 ^ (m + 1))) = 0 :=
    (CharP.cast_eq_zero_iff (ZMod (3 ^ (m + 1))) (3 ^ (m + 1)) _).mpr h
  push_cast at h0
  have hneg : (2 : ZMod (3 ^ (m + 1))) ^ k = -1 := by linear_combination h0
  have hone : (2 : ZMod (3 ^ (m + 1))) ^ (2 * k) = 1 := by
    rw [mul_comm, pow_mul, hneg]; norm_num
  have hdvd : 2 * 3 ^ m ∣ 2 * k := by
    rw [← orderOf_two_zmod m]
    exact orderOf_dvd_of_pow_eq_one hone
  exact (Nat.mul_dvd_mul_iff_left (show 0 < 2 by norm_num)).mp hdvd

/-- The cube root of unity the second optimisation of §16.5 lands on:
`2^(2·3ⁿ) ≡ 1 + 3^(n+1) (mod 3^(n+2))`.  This is where `cₙ ≡ 1 (mod 3)` is used. -/
theorem two_pow_two_mul_three_pow (n : ℕ) :
    (3 : ℤ) ^ (n + 2) ∣ (2 : ℤ) ^ (2 * 3 ^ n) - (1 + 3 ^ (n + 1)) := by
  obtain ⟨c, hc, hc3⟩ := two_pow_three_pow n
  obtain ⟨t, rfl⟩ : ∃ t, c = 1 + 3 * t := ⟨c / 3, by omega⟩
  refine ⟨-1 - 2 * t + 3 ^ n * (1 + 3 * t) ^ 2, ?_⟩
  have hsq : (2 : ℤ) ^ (2 * 3 ^ n) = ((2 : ℤ) ^ (3 ^ n)) ^ 2 := by rw [mul_comm, pow_mul]
  rw [hsq, hc]
  ring

end MSP2
