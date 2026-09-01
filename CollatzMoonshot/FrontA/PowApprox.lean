/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.Basic

/-!
# Approximating powers of three from above by powers of two

One statement, isolated here because it is the entire non-elementary content of the unbounded
half of Rozier--Terracol 2026, Theorem 3.2 (`Assumed/Paradoxical.lean`):

> for every `M` and `N` there are `A > M` and `s` with `3 ^ A < 2 ^ s` and
> `(2 ^ s - 3 ^ A) * N ≤ 3 ^ A`.

In words: `2 ^ s` approximates `3 ^ A` **from above** to arbitrary *relative* precision `1/N`,
with `A` arbitrarily large.  This is exactly RT's "infinitely many left approximations
`3^a / 2^b < 1` of `1`".  Classically it is the density of `{A · log₂ 3}` mod `1`; here it is
proved **without logarithms or irrationality**, by a multiplicative pigeonhole in `ℝ` and one
parity fact (`3 ^ a ≠ 2 ^ b` for `a ≥ 1`).

## Proof (`two_pow_approx_three_pow_from_above`)

Fix `N ≥ 1` (the case `N = 0` is trivial).

1. **Ratios in `(1, 2]`.**  For each `A` let `s A = ⌊log₂ 3^A⌋ + 1`, so `3^A < 2^(s A) ≤ 2·3^A`
   and `q A := 2^(s A) / 3^A ∈ (1, 2]`.
2. **Boxes** (`exists_mul_box`).  Split `(1, 2]` into the `N` multiplicative boxes
   `((1+1/N)^j, (1+1/N)^(j+1)]`, `j < N`; they cover because `(1+1/N)^N ≥ 2` (Bernoulli).
3. **Pigeonhole** (`exists_two_pow_three_pow_ratio_close`).  The `N + 1` indices
   `A = i·(M+1)`, `i ≤ N`, put two ratios `q A₁, q A₂` (`A₁ < A₂`) in one box, so
   `q A₂ / q A₁ = 2^b / 3^a` with `a = A₂ - A₁ ≥ M + 1` and both `2^b/3^a` and `3^a/2^b`
   below `1 + 1/N`.
4. **The flip** (`approx_from_above_of_ratio_close`).  `2^b ≠ 3^a` by parity.  If `3^a < 2^b`
   we are done with `u = 1`.  Otherwise `ρ = 3^a/2^b ∈ (1, 1 + 1/N)`; let `u ≥ 1` be the least
   exponent with `ρ^(u+1) ≥ 2`, so `ρ^u < 2 ≤ ρ · ρ^u`, and then
   `2^(u b + 1) / 3^(u a) = 2 / ρ^u ∈ (1, ρ] ⊂ (1, 1 + 1/N)`.

`#print axioms two_pow_approx_three_pow_from_above` = `[propext, Classical.choice, Quot.sound]`.
-/

namespace CollatzMoonshot.FrontA

/-- `3^a ≠ 2^b` once `a ≥ 1` (parity: `3^a` is odd and exceeds `1`). -/
theorem three_pow_ne_two_pow_of_pos {a b : ℕ} (ha : 0 < a) : (3:ℕ) ^ a ≠ 2 ^ b := by
  intro h
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb
    simp only [pow_zero, Nat.pow_eq_one] at h
    omega
  · have h2 : (2:ℕ) ∣ 3 ^ a := by rw [h]; exact dvd_pow_self 2 (by omega)
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
    omega

/-- Box selection for the multiplicative pigeonhole: for `1 < q ≤ 2` and `N ≥ 1` there is a
box index `j < N` with `(1 + 1/N)^j < q ≤ (1 + 1/N)^(j+1)`.  Covering is Bernoulli's
`(1 + 1/N)^N ≥ 1 + N·(1/N) = 2`. -/
theorem exists_mul_box {q : ℝ} (hq1 : 1 < q) (hq2 : q ≤ 2) {N : ℕ} (hN : 0 < N) :
    ∃ j, j < N ∧ (1 + 1 / (N:ℝ)) ^ j < q ∧ q ≤ (1 + 1 / (N:ℝ)) ^ (j + 1) := by
  classical
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have htop : q ≤ (1 + 1 / (N:ℝ)) ^ (N - 1 + 1) := by
    rw [Nat.sub_add_cancel hN]
    calc q ≤ 2 := hq2
      _ = 1 + (N:ℝ) * (1 / N) := by field_simp; ring
      _ ≤ (1 + 1 / (N:ℝ)) ^ N := by
          have : (0:ℝ) ≤ 1 / N := by positivity
          exact one_add_mul_le_pow (by linarith) N
  have hex : ∃ j, q ≤ (1 + 1 / (N:ℝ)) ^ (j + 1) := ⟨N - 1, htop⟩
  refine ⟨Nat.find hex, ?_, ?_, Nat.find_spec hex⟩
  · have := Nat.find_min' hex htop
    omega
  · obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j := ⟨_, rfl⟩
    rw [hj]
    cases j with
    | zero => simpa using hq1
    | succ j =>
      exact not_le.1 (Nat.find_min hex (m := j) (by omega))

/-- **Multiplicative pigeonhole**: for every `M` and `N ≥ 1` there are `a > M` and `b` with
`2^b / 3^a` within a factor `1 + 1/N` of `1` on both sides.  The `N + 1` ratios
`2^(s A)/3^A ∈ (1, 2]` at `A = i·(M+1)`, `i ≤ N`, land in `N` boxes; a collision at
`A₁ < A₂` gives `a = A₂ - A₁`, a positive multiple of `M + 1`. -/
theorem exists_two_pow_three_pow_ratio_close (M N : ℕ) (hN : 0 < N) :
    ∃ a b : ℕ, M < a ∧ (2:ℝ) ^ b / 3 ^ a < 1 + 1 / N ∧ (3:ℝ) ^ a / 2 ^ b < 1 + 1 / N := by
  classical
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  -- the least `s` with `3^A < 2^s`
  set s : ℕ → ℕ := fun A => Nat.log 2 (3 ^ A) + 1 with hs
  have h1 : ∀ A, 3 ^ A < 2 ^ s A := fun A => Nat.lt_pow_succ_log_self (by norm_num) _
  have h2 : ∀ A, 2 ^ s A ≤ 2 * 3 ^ A := fun A => by
    have := Nat.pow_log_le_self 2 (x := 3 ^ A) (by positivity)
    simp only [hs, pow_succ]
    omega
  have hq1 : ∀ A, 1 < (2:ℝ) ^ s A / 3 ^ A := fun A => by
    rw [lt_div_iff₀ (by positivity), one_mul]; exact_mod_cast h1 A
  have hq2 : ∀ A, (2:ℝ) ^ s A / 3 ^ A ≤ 2 := fun A => by
    rw [div_le_iff₀ (by positivity)]; exact_mod_cast h2 A
  choose box hbox using fun A => exists_mul_box (hq1 A) (hq2 A) hN
  -- the core: two indices `i < i'` in the same box
  have core : ∀ i i' : ℕ, i < i' → box (i * (M + 1)) = box (i' * (M + 1)) →
      ∃ a b : ℕ, M < a ∧ (2:ℝ) ^ b / 3 ^ a < 1 + 1 / N ∧ (3:ℝ) ^ a / 2 ^ b < 1 + 1 / N := by
    intro i i' hii' heq
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hii'
    set A₁ := i * (M + 1) with hA₁
    set a := (d + 1) * (M + 1) with ha
    have hA₂ : (i + d + 1) * (M + 1) = A₁ + a := by rw [hA₁, ha]; ring
    rw [hA₂] at heq
    -- `s` is monotone: `s A₁ ≤ s (A₁ + a)`
    have hsle : s A₁ ≤ s (A₁ + a) := by
      have : 2 ^ s A₁ < 2 ^ (s (A₁ + a) + 1) := by
        calc 2 ^ s A₁ ≤ 2 * 3 ^ A₁ := h2 A₁
          _ ≤ 2 * 3 ^ (A₁ + a) := by gcongr <;> omega
          _ < 2 * 2 ^ s (A₁ + a) := by have := h1 (A₁ + a); omega
          _ = 2 ^ (s (A₁ + a) + 1) := by ring
      have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 this
      omega
    obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le hsle
    refine ⟨a, b, ?_, ?_, ?_⟩
    · rw [ha]; nlinarith
    · -- q (A₁ + a) < (1 + 1/N) * q A₁
      obtain ⟨-, hlo, hhi⟩ := hbox A₁
      obtain ⟨-, hlo', hhi'⟩ := hbox (A₁ + a)
      rw [← heq] at hlo' hhi'
      have hX : (0:ℝ) < 2 ^ s A₁ / 3 ^ A₁ := by positivity
      have key : (2:ℝ) ^ s (A₁ + a) / 3 ^ (A₁ + a) < (1 + 1 / N) * (2 ^ s A₁ / 3 ^ A₁) := by
        calc (2:ℝ) ^ s (A₁ + a) / 3 ^ (A₁ + a) ≤ (1 + 1 / (N:ℝ)) ^ (box A₁ + 1) := hhi'
          _ = (1 + 1 / N) * (1 + 1 / (N:ℝ)) ^ box A₁ := by ring
          _ < (1 + 1 / N) * (2 ^ s A₁ / 3 ^ A₁) := mul_lt_mul_of_pos_left hlo (by positivity)
      have hsplit : (2:ℝ) ^ s (A₁ + a) / 3 ^ (A₁ + a)
          = (2 ^ s A₁ / 3 ^ A₁) * (2 ^ b / 3 ^ a) := by
        rw [hb, pow_add, pow_add]; ring
      rw [hsplit, mul_comm (1 + 1 / (N:ℝ))] at key
      exact lt_of_mul_lt_mul_left key hX.le
    · -- q A₁ < (1 + 1/N) * q (A₁ + a)
      obtain ⟨-, hlo, hhi⟩ := hbox A₁
      obtain ⟨-, hlo', hhi'⟩ := hbox (A₁ + a)
      rw [← heq] at hlo' hhi'
      have hX : (0:ℝ) < 2 ^ s A₁ / 3 ^ A₁ := by positivity
      have key : (2:ℝ) ^ s A₁ / 3 ^ A₁ < (1 + 1 / N) * (2 ^ s (A₁ + a) / 3 ^ (A₁ + a)) := by
        calc (2:ℝ) ^ s A₁ / 3 ^ A₁ ≤ (1 + 1 / (N:ℝ)) ^ (box A₁ + 1) := hhi
          _ = (1 + 1 / N) * (1 + 1 / (N:ℝ)) ^ box A₁ := by ring
          _ < (1 + 1 / N) * (2 ^ s (A₁ + a) / 3 ^ (A₁ + a)) :=
              mul_lt_mul_of_pos_left hlo' (by positivity)
      have hsplit : (2:ℝ) ^ s (A₁ + a) / 3 ^ (A₁ + a)
          = (2 ^ s A₁ / 3 ^ A₁) * (2 ^ b / 3 ^ a) := by
        rw [hb, pow_add, pow_add]; ring
      rw [hsplit, ← mul_assoc, mul_comm (1 + 1 / (N:ℝ)), mul_assoc] at key
      have h1' : 1 < (1 + 1 / (N:ℝ)) * (2 ^ b / 3 ^ a) := by
        have hk : (2:ℝ) ^ s A₁ / 3 ^ A₁ * 1
            < 2 ^ s A₁ / 3 ^ A₁ * ((1 + 1 / N) * (2 ^ b / 3 ^ a)) := by
          rw [mul_one]; exact key
        exact lt_of_mul_lt_mul_left hk hX.le
      rw [div_lt_iff₀ (by positivity)]
      rw [mul_div_assoc', lt_div_iff₀ (by positivity), one_mul] at h1'
      exact h1'
  -- pigeonhole on `N + 1` indices into `N` boxes
  obtain ⟨i, hi, i', hi', hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (N + 1)) (t := Finset.range N) (f := fun i => box (i * (M + 1)))
    (by simp) (fun i _ => by simpa using (hbox (i * (M + 1))).1)
  rcases lt_or_gt_of_ne hne with h | h
  · exact core i i' h heq
  · exact core i' i h heq.symm

/-- **The flip**: from two-sided closeness `2^b/3^a ≈ 1` (both `2^b/3^a` and `3^a/2^b` below
`1 + 1/N`) with `a ≥ 1`, produce an approximation of `3^(u a)` from **above** by a power of two,
to relative precision `1/N`.  If `3^a < 2^b` take `u = 1`; otherwise `ρ = 3^a/2^b ∈ (1, 1+1/N)`
and the least `u` with `ρ^(u+1) ≥ 2` gives `2^(u b + 1)/3^(u a) = 2/ρ^u ∈ (1, ρ]`. -/
theorem approx_from_above_of_ratio_close {a b N : ℕ} (ha : 0 < a) (hN : 0 < N)
    (h1 : (2:ℝ) ^ b / 3 ^ a < 1 + 1 / N) (h2 : (3:ℝ) ^ a / 2 ^ b < 1 + 1 / N) :
    ∃ u s : ℕ, 0 < u ∧ 3 ^ (u * a) < 2 ^ s ∧ (2 ^ s - 3 ^ (u * a)) * N ≤ 3 ^ (u * a) := by
  classical
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  rcases lt_or_gt_of_ne (three_pow_ne_two_pow_of_pos ha : (3:ℕ) ^ a ≠ 2 ^ b) with hlt | hgt
  · -- `3^a < 2^b`: already from above; `u = 1`
    refine ⟨1, b, one_pos, by simpa using hlt, ?_⟩
    rw [one_mul]
    have hr : (2:ℝ) ^ b * N < 3 ^ a * (N + 1) := by
      rw [div_lt_iff₀ (by positivity)] at h1
      calc (2:ℝ) ^ b * N < (1 + 1 / N) * 3 ^ a * N := by gcongr
        _ = 3 ^ a * (N + 1) := by field_simp
    have hnat : 2 ^ b * N ≤ 3 ^ a * (N + 1) := by exact_mod_cast hr.le
    rw [Nat.sub_mul, tsub_le_iff_right]
    nlinarith
  · -- `2^b < 3^a`: flip.  `ρ = 3^a/2^b ∈ (1, 1 + 1/N)`; take the least `u` with `ρ^(u+1) ≥ 2`.
    set ρ : ℝ := 3 ^ a / 2 ^ b with hρ
    have hρ1 : 1 < ρ := by rw [hρ, lt_div_iff₀ (by positivity), one_mul]; exact_mod_cast hgt
    have hρpos : 0 < ρ := by linarith
    have hex : ∃ u, (2:ℝ) ≤ ρ ^ (u + 1) := by
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2:ℝ) hρ1
      refine ⟨n, ?_⟩
      have : ρ ^ n ≤ ρ ^ (n + 1) := pow_le_pow_right₀ hρ1.le (by omega)
      linarith
    have hu := Nat.find_spec hex
    set u := Nat.find hex with hu_def
    have hu0 : u ≠ 0 := by
      intro h
      rw [h, zero_add, pow_one] at hu
      have : (1:ℝ) / N ≤ 1 := by
        rw [div_le_iff₀ hNr, one_mul]; exact_mod_cast hN
      linarith
    have hlt : ρ ^ u < 2 := by
      obtain ⟨u', hu'⟩ := Nat.exists_eq_succ_of_ne_zero hu0
      have := not_le.1 (Nat.find_min hex (m := u') (by omega))
      rwa [hu']
    have hρpow : ρ ^ u = (3:ℝ) ^ (u * a) / 2 ^ (u * b) := by
      rw [hρ, div_pow, ← pow_mul, ← pow_mul, mul_comm a, mul_comm b]
    refine ⟨u, u * b + 1, Nat.pos_of_ne_zero hu0, ?_, ?_⟩
    · have : (3:ℝ) ^ (u * a) < 2 ^ (u * b + 1) := by
        rw [hρpow, div_lt_iff₀ (by positivity)] at hlt
        rw [pow_succ]; linarith
      exact_mod_cast this
    · have h2u : (2:ℝ) < (1 + 1 / N) * ρ ^ u := by
        calc (2:ℝ) ≤ ρ ^ (u + 1) := hu
          _ = ρ * ρ ^ u := by ring
          _ < (1 + 1 / N) * ρ ^ u := by gcongr
      have hr : (2:ℝ) ^ (u * b + 1) * N < 3 ^ (u * a) * (N + 1) := by
        rw [hρpow, mul_div_assoc', lt_div_iff₀ (by positivity)] at h2u
        have : (2:ℝ) ^ (u * b + 1) * N = 2 * 2 ^ (u * b) * N := by ring
        rw [this]
        calc (2:ℝ) * 2 ^ (u * b) * N < (1 + 1 / N) * 3 ^ (u * a) * N := by gcongr
          _ = 3 ^ (u * a) * (N + 1) := by field_simp
      have hnat : 2 ^ (u * b + 1) * N ≤ 3 ^ (u * a) * (N + 1) := by exact_mod_cast hr.le
      rw [Nat.sub_mul, tsub_le_iff_right]
      nlinarith

/-- **Powers of two approximate powers of three from above, to arbitrary relative precision,
infinitely often.**  For all `M N`, there are `A > M` and `s` with `3 ^ A < 2 ^ s` and
`(2 ^ s - 3 ^ A) * N ≤ 3 ^ A`.

This is the single Diophantine input of the unbounded half of Rozier--Terracol Theorem 3.2
(`Assumed/Paradoxical.lean`).  Proved by the multiplicative pigeonhole
`exists_two_pow_three_pow_ratio_close` and the flip `approx_from_above_of_ratio_close`; no
logarithms, no irrationality of `log₂ 3`, no `native_decide`. -/
theorem two_pow_approx_three_pow_from_above (M N : ℕ) :
    ∃ A s : ℕ, M < A ∧ 3 ^ A < 2 ^ s ∧ (2 ^ s - 3 ^ A) * N ≤ 3 ^ A := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    refine ⟨M + 1, 2 * (M + 1), by omega, ?_, by simp⟩
    rw [pow_mul]
    exact Nat.pow_lt_pow_left (by norm_num) (by omega)
  · obtain ⟨a, b, hMa, h1, h2⟩ := exists_two_pow_three_pow_ratio_close M N hN
    obtain ⟨u, s, hu, hlt, hle⟩ := approx_from_above_of_ratio_close (by omega) hN h1 h2
    refine ⟨u * a, s, ?_, hlt, hle⟩
    nlinarith

end CollatzMoonshot.FrontA
