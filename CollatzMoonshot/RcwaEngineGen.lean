/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# The `{2,3}`-slope counter-machine engine for any number of states (Lemma P, `r = 5^j`)

`RcwaEngine.lean` runs a 2-counter machine with at most 20 states inside `ℤ` (`r = 25`).  This
file does the same for `r = 5^j` and any `j ≥ 1`, so a machine with any number of states fits.

Put `N = 4·5^(j−1)` (Euler's `φ(5^j)`), so `2^N ≡ 3^N ≡ 1 (mod 5^j)`.  The **phase** of `n` is the
least `k < N` with `3^k ≡ n (mod 5^j)`.  On the **engine zone** (`n ≠ 0`, `5 ∤ n`, `n mod 5^j` a
power of `3`, and `v₃(n) ≥ phase`) the counters are `C₁ = ⌊v₂/N⌋`, `C₂ = ⌊(v₃ − phase)/N⌋`, and the
junk is `(v₂ mod N, (v₃ − phase) mod N, the part of n prime to 6)`.  States are the phases
`s < orderOf (3 : ZMod (5^j))`, and that order is at least `j` (`le_orderOf_three`), so it is
unbounded in `j`.  No primitive-root theory is needed.

The statements mirror `RcwaEngine.lean` with `20` replaced by `N j`.
-/

namespace CollatzMoonshot.RcwaEngineGen

/-- `N j = 4·5^(j−1) = φ(5^j)`. -/
def N (j : ℕ) : ℕ :=
  4 * 5 ^ (j - 1)

/-- Discrete log to base `3` in `ZMod (5^j)`: the least `k < N j` with `3^k = x` (`0` if none). -/
def dlog3 (j : ℕ) (x : ZMod (5 ^ j)) : ℕ :=
  ((List.range (N j)).find? fun k => (3 : ZMod (5 ^ j)) ^ k = x).getD 0

/-- The phase (machine state) of `n`. -/
def phase (j : ℕ) (n : ℤ) : ℕ :=
  dlog3 j (n : ZMod (5 ^ j))

/-- `v₂(n)`. -/
def v2 (n : ℤ) : ℕ :=
  padicValInt 2 n

/-- `v₃(n)`. -/
def v3 (n : ℤ) : ℕ :=
  padicValInt 3 n

/-- The engine zone: `n ≠ 0`, `5 ∤ n`, `n ≡ 3^phase (mod 5^j)`, and `v₃(n) ≥ phase`. -/
def InEngine (j : ℕ) (n : ℤ) : Prop :=
  n ≠ 0 ∧ ¬ (5 : ℤ) ∣ n ∧ (3 : ZMod (5 ^ j)) ^ phase j n = (n : ZMod (5 ^ j)) ∧
    phase j n ≤ v3 n

/-- The first counter `⌊v₂(n)/N⌋`. -/
def C1 (j : ℕ) (n : ℤ) : ℕ :=
  v2 n / N j

/-- The second counter `⌊(v₃(n) − phase)/N⌋`. -/
def C2 (j : ℕ) (n : ℤ) : ℕ :=
  (v3 n - phase j n) / N j

/-- The junk `(v₂ mod N, (v₃ − phase) mod N, the part of n prime to 6)`. -/
def junk (j : ℕ) (n : ℤ) : ℕ × ℕ × ℤ :=
  (v2 n % N j, (v3 n - phase j n) % N j, n / (2 ^ v2 n * 3 ^ v3 n))

/-- Multiply by `2^A 3^B` for integer exponents `A, B` (exact when the denominators divide). -/
def scale (n A B : ℤ) : ℤ :=
  n * 2 ^ A.toNat * 3 ^ B.toNat / (2 ^ (-A).toNat * 3 ^ (-B).toNat)

/-! ### Helpers: residues mod `5^j` -/

theorem N_pos (j : ℕ) : 0 < N j := by
  unfold N; positivity

/-- Euler: `a^N = 1` in `ZMod (5^j)` for `a` prime to `5`. -/
theorem pow_N_eq_one {j a : ℕ} (hj : 1 ≤ j) (ha : Nat.Coprime a 5) :
    (a : ZMod (5 ^ j)) ^ N j = 1 := by
  have h := ZMod.pow_totient (ZMod.unitOfCoprime a (Nat.Coprime.pow_right j ha))
  rw [Nat.totient_prime_pow Nat.prime_five hj] at h
  have h' := congrArg (fun u : (ZMod (5 ^ j))ˣ => (u : ZMod (5 ^ j))) h
  simp only [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one] at h'
  rw [N, show 4 * 5 ^ (j - 1) = 5 ^ (j - 1) * (5 - 1) by ring]
  exact h'

theorem two_pow_N {j : ℕ} (hj : 1 ≤ j) : (2 : ZMod (5 ^ j)) ^ N j = 1 := by
  exact_mod_cast pow_N_eq_one hj (a := 2) (by norm_num)

theorem three_pow_N {j : ℕ} (hj : 1 ≤ j) : (3 : ZMod (5 ^ j)) ^ N j = 1 := by
  exact_mod_cast pow_N_eq_one hj (a := 3) (by norm_num)

theorem orderOf_three_le {j : ℕ} (hj : 1 ≤ j) : orderOf (3 : ZMod (5 ^ j)) ≤ N j :=
  orderOf_le_of_pow_eq_one (N_pos j) (three_pow_N hj)

theorem dlog3_lt (j : ℕ) (x : ZMod (5 ^ j)) : dlog3 j x < N j := by
  unfold dlog3
  cases h : (List.range (N j)).find? (fun k => (3 : ZMod (5 ^ j)) ^ k = x) with
  | none => exact N_pos j
  | some i =>
    rw [List.find?_range_eq_some] at h
    exact List.mem_range.1 h.2.1

/-- `dlog3` returns a logarithm, the least one, whenever one below `N j` exists. -/
theorem dlog3_spec {j : ℕ} {x : ZMod (5 ^ j)} {k : ℕ} (hk : k < N j) (hx : 3 ^ k = x) :
    3 ^ dlog3 j x = x ∧ ∀ i < dlog3 j x, (3 : ZMod (5 ^ j)) ^ i ≠ x := by
  unfold dlog3
  cases h : (List.range (N j)).find? (fun k => (3 : ZMod (5 ^ j)) ^ k = x) with
  | none =>
    rw [List.find?_range_eq_none] at h
    exact absurd hx (by simpa using h k hk)
  | some i =>
    rw [List.find?_range_eq_some] at h
    obtain ⟨h1, -, h3⟩ := h
    exact ⟨by simpa using h1, fun l hl => by simpa using h3 l hl⟩

theorem dlog3_three_pow {j : ℕ} (hj : 1 ≤ j) {s : ℕ} (hs : s < orderOf (3 : ZMod (5 ^ j))) :
    dlog3 j ((3 : ZMod (5 ^ j)) ^ s) = s := by
  obtain ⟨h1, h2⟩ := dlog3_spec (lt_of_lt_of_le hs (orderOf_three_le hj)) rfl
  have hle : dlog3 j ((3 : ZMod (5 ^ j)) ^ s) ≤ s := by
    by_contra hlt
    exact h2 s (by omega) rfl
  exact pow_injOn_Iio_orderOf (Set.mem_Iio.2 (lt_of_le_of_lt hle hs)) (Set.mem_Iio.2 hs) h1

theorem three_pow_ne_zero {j : ℕ} (hj : 1 ≤ j) (s : ℕ) : (3 : ZMod (5 ^ j)) ^ s ≠ 0 := by
  have : Fact (1 < 5 ^ j) := ⟨Nat.one_lt_pow (by omega) (by norm_num)⟩
  intro h
  have h1 : ((3 : ZMod (5 ^ j)) ^ N j) ^ s = 1 := by rw [three_pow_N hj, one_pow]
  rw [← pow_mul, mul_comm, pow_mul, h, zero_pow (N_pos j).ne'] at h1
  exact zero_ne_one h1

theorem not_five_dvd_of_cast {j : ℕ} (hj : 1 ≤ j) {n : ℤ} {s : ℕ}
    (h : (n : ZMod (5 ^ j)) = 3 ^ s) : ¬ (5 : ℤ) ∣ n := by
  rintro ⟨t, rfl⟩
  have h5 : (5 : ZMod (5 ^ j)) ^ j = 0 := by
    exact_mod_cast ZMod.natCast_self (5 ^ j)
  apply three_pow_ne_zero hj (s * j)
  rw [pow_mul, ← h]
  push_cast
  rw [mul_pow, h5, zero_mul]

theorem three_pow_cancel {j : ℕ} (hj : 1 ≤ j) {s : ℕ} (hs : s < N j) {u : ZMod (5 ^ j)}
    (h : 3 ^ s * u = 3 ^ s) : u = 1 := by
  have h1 : (3 : ZMod (5 ^ j)) ^ (N j - s) * 3 ^ s = 1 := by
    rw [← pow_add, Nat.sub_add_cancel hs.le, three_pow_N hj]
  calc u = (3 ^ (N j - s) * 3 ^ s) * u := by rw [h1, one_mul]
    _ = 3 ^ (N j - s) * (3 ^ s * u) := by ring
    _ = 1 := by rw [h, h1]

/-! ### Helpers: valuations -/

theorem padicValInt_pow_mul {p : ℕ} [Fact p.Prime] {a : ℕ} {k : ℤ} (hk : ¬ (p : ℤ) ∣ k) :
    padicValInt p ((p : ℤ) ^ a * k) = a := by
  have hk0 : k ≠ 0 := by rintro rfl; exact hk (dvd_zero _)
  have hp0 : ((p : ℤ) ^ a) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  apply le_antisymm
  · by_contra hlt
    push Not at hlt
    have h := (padicValInt_dvd_iff (p := p) (a + 1) ((p : ℤ) ^ a * k)).2 (Or.inr hlt)
    rw [pow_succ] at h
    exact hk ((mul_dvd_mul_iff_left hp0).1 h)
  · exact ((padicValInt_dvd_iff (p := p) a ((p : ℤ) ^ a * k)).1 (dvd_mul_right _ _)).resolve_left
      (mul_ne_zero hp0 hk0)

theorem not_dvd_mul_of_prime {p : ℤ} (hp : Prime p) {x y : ℤ} (hx : ¬ p ∣ x) (hy : ¬ p ∣ y) :
    ¬ p ∣ x * y :=
  fun h => (hp.dvd_or_dvd h).elim hx hy

theorem not_dvd_pow_of_prime {p q : ℤ} (hp : Prime p) (hq : ¬ p ∣ q) (k : ℕ) : ¬ p ∣ q ^ k :=
  fun h => hq (hp.dvd_of_dvd_pow h)

theorem v2_mk {a b : ℕ} {m : ℤ} (h2 : ¬ (2 : ℤ) ∣ m) :
    v2 (2 ^ a * 3 ^ b * m) = a := by
  have h : ¬ (2 : ℤ) ∣ 3 ^ b * m :=
    not_dvd_mul_of_prime Int.prime_two (not_dvd_pow_of_prime Int.prime_two (by decide) b) h2
  have := padicValInt_pow_mul (p := 2) (a := a) (k := 3 ^ b * m) (by exact_mod_cast h)
  rw [v2, mul_assoc]
  exact_mod_cast this

theorem v3_mk {a b : ℕ} {m : ℤ} (h3 : ¬ (3 : ℤ) ∣ m) :
    v3 (2 ^ a * 3 ^ b * m) = b := by
  have h : ¬ (3 : ℤ) ∣ 2 ^ a * m :=
    not_dvd_mul_of_prime Int.prime_three (not_dvd_pow_of_prime Int.prime_three (by decide) a) h3
  have := padicValInt_pow_mul (p := 3) (a := b) (k := 2 ^ a * m) (by exact_mod_cast h)
  rw [v3, show (2 : ℤ) ^ a * 3 ^ b * m = 3 ^ b * (2 ^ a * m) by ring]
  exact_mod_cast this

/-- Every nonzero `n` is `2^{v₂} 3^{v₃} m` with `m` prime to `6`. -/
theorem decomp {n : ℤ} (hn : n ≠ 0) :
    ¬ (2 : ℤ) ∣ n / (2 ^ v2 n * 3 ^ v3 n) ∧ ¬ (3 : ℤ) ∣ n / (2 ^ v2 n * 3 ^ v3 n) ∧
      n = 2 ^ v2 n * 3 ^ v3 n * (n / (2 ^ v2 n * 3 ^ v3 n)) := by
  have h2 : (2 : ℤ) ^ v2 n ∣ n := by exact_mod_cast padicValInt_dvd (p := 2) n
  have h3 : (3 : ℤ) ^ v3 n ∣ n := by exact_mod_cast padicValInt_dvd (p := 3) n
  have hc : IsCoprime ((2 : ℤ) ^ v2 n) (3 ^ v3 n) := by
    apply IsCoprime.pow
    rw [Int.isCoprime_iff_gcd_eq_one]
    rfl
  have he : n = 2 ^ v2 n * 3 ^ v3 n * (n / (2 ^ v2 n * 3 ^ v3 n)) :=
    (Int.mul_ediv_cancel' (hc.mul_dvd h2 h3)).symm
  refine ⟨?_, ?_, he⟩
  · rintro ⟨k, hk⟩
    have h : (2 : ℤ) ^ (v2 n + 1) ∣ n := ⟨3 ^ v3 n * k, by nth_rw 1 [he]; rw [hk]; ring⟩
    have h' : v2 n + 1 ≤ v2 n :=
      ((padicValInt_dvd_iff (p := 2) _ n).1 (by exact_mod_cast h)).resolve_left hn
    omega
  · rintro ⟨k, hk⟩
    have h : (3 : ℤ) ^ (v3 n + 1) ∣ n := ⟨2 ^ v2 n * k, by nth_rw 1 [he]; rw [hk]; ring⟩
    have h' : v3 n + 1 ≤ v3 n :=
      ((padicValInt_dvd_iff (p := 3) _ n).1 (by exact_mod_cast h)).resolve_left hn
    omega

/-! ### Helpers: building engine points from state, counters and junk -/

/-- The engine point with junk `(e, D, m)`, state `s` and counters `(c₁, c₂)`. -/
def build (j e D : ℕ) (m : ℤ) (s c₁ c₂ : ℕ) : ℤ :=
  2 ^ (N j * c₁ + e) * 3 ^ (s + N j * c₂ + D) * m

theorem build_cast {j : ℕ} (hj : 1 ≤ j) (e D : ℕ) (m : ℤ) (s c₁ c₂ : ℕ) :
    ((build j e D m s c₁ c₂ : ℤ) : ZMod (5 ^ j)) = 3 ^ s * (2 ^ e * 3 ^ D * m) := by
  simp only [build]
  push_cast
  rw [pow_add, pow_add, pow_add, pow_mul, pow_mul, two_pow_N hj, three_pow_N hj, one_pow,
    one_pow]
  ring

theorem build_spec {j e D s : ℕ} {m : ℤ} (hj : 1 ≤ j) (he : e < N j) (hD : D < N j)
    (hs : s < orderOf (3 : ZMod (5 ^ j))) (h2 : ¬ (2 : ℤ) ∣ m) (h3 : ¬ (3 : ℤ) ∣ m)
    (hu : (2 : ZMod (5 ^ j)) ^ e * 3 ^ D * m = 1) (c₁ c₂ : ℕ) :
    InEngine j (build j e D m s c₁ c₂) ∧ phase j (build j e D m s c₁ c₂) = s ∧
      C1 j (build j e D m s c₁ c₂) = c₁ ∧ C2 j (build j e D m s c₁ c₂) = c₂ ∧
      junk j (build j e D m s c₁ c₂) = (e, D, m) := by
  have hv2 : v2 (build j e D m s c₁ c₂) = N j * c₁ + e := v2_mk h2
  have hv3 : v3 (build j e D m s c₁ c₂) = s + N j * c₂ + D := v3_mk h3
  have hmod : ((build j e D m s c₁ c₂ : ℤ) : ZMod (5 ^ j)) = 3 ^ s := by
    rw [build_cast hj, hu, mul_one]
  have hph : phase j (build j e D m s c₁ c₂) = s := by
    rw [phase, hmod]
    exact dlog3_three_pow hj hs
  have hm0 : m ≠ 0 := by rintro rfl; exact h2 (dvd_zero _)
  have hN := N_pos j
  refine ⟨⟨?_, not_five_dvd_of_cast hj hmod, by rw [hph, hmod], ?_⟩, hph, ?_, ?_, ?_⟩
  · simp only [build]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num))) hm0
  · rw [hph, hv3]; omega
  · rw [C1, hv2, Nat.mul_add_div hN, Nat.div_eq_of_lt he, add_zero]
  · rw [C2, hv3, hph, show s + N j * c₂ + D - s = N j * c₂ + D by omega, Nat.mul_add_div hN,
      Nat.div_eq_of_lt hD, add_zero]
  · rw [junk, hv2, hv3, hph]
    simp only [Prod.mk.injEq]
    refine ⟨by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt he], ?_, ?_⟩
    · rw [show s + N j * c₂ + D - s = N j * c₂ + D by omega, Nat.mul_add_mod, Nat.mod_eq_of_lt hD]
    show 2 ^ (N j * c₁ + e) * 3 ^ (s + N j * c₂ + D) * m /
      (2 ^ (N j * c₁ + e) * 3 ^ (s + N j * c₂ + D)) = m
    exact Int.mul_ediv_cancel_left _ (mul_ne_zero (pow_ne_zero _ (by norm_num))
      (pow_ne_zero _ (by norm_num)))

/-- Every engine point is built from its own junk, state and counters. -/
theorem decode_spec {j : ℕ} (hj : 1 ≤ j) {n : ℤ} (hn : InEngine j n) :
    (junk j n).1 < N j ∧ (junk j n).2.1 < N j ∧ ¬ (2 : ℤ) ∣ (junk j n).2.2 ∧
      ¬ (3 : ℤ) ∣ (junk j n).2.2 ∧
      (2 : ZMod (5 ^ j)) ^ (junk j n).1 * 3 ^ (junk j n).2.1 * ((junk j n).2.2 : ZMod (5 ^ j)) = 1 ∧
      n = build j (junk j n).1 (junk j n).2.1 (junk j n).2.2 (phase j n) (C1 j n) (C2 j n) := by
  obtain ⟨h2, h3, he⟩ := decomp hn.1
  have hb : phase j n ≤ v3 n := hn.2.2.2
  have hN := N_pos j
  have heq :
      n = build j (junk j n).1 (junk j n).2.1 (junk j n).2.2 (phase j n) (C1 j n) (C2 j n) := by
    have ha : N j * (v2 n / N j) + v2 n % N j = v2 n := Nat.div_add_mod _ _
    have hb' : phase j n + N j * ((v3 n - phase j n) / N j) + (v3 n - phase j n) % N j =
        v3 n := by
      have := Nat.div_add_mod (v3 n - phase j n) (N j)
      omega
    simp only [build, junk, C1, C2]
    rw [ha, hb']
    exact he
  refine ⟨Nat.mod_lt _ hN, Nat.mod_lt _ hN, h2, h3, ?_, heq⟩
  have hs : phase j n < N j := dlog3_lt j _
  apply three_pow_cancel hj hs
  rw [← build_cast hj _ _ _ (phase j n) (C1 j n) (C2 j n), ← heq]
  exact hn.2.2.1.symm

theorem build_mul_eq {j e D s s' c₁ c₂ : ℕ} {m δ₁ δ₂ : ℤ} (h₁ : 0 ≤ (c₁ : ℤ) + δ₁)
    (h₂ : 0 ≤ (c₂ : ℤ) + δ₂) :
    build j e D m s c₁ c₂ * 2 ^ (N j * δ₁ : ℤ).toNat * 3 ^ (N j * δ₂ + s' - s : ℤ).toNat =
      build j e D m s' ((c₁ : ℤ) + δ₁).toNat ((c₂ : ℤ) + δ₂).toNat *
        (2 ^ (-(N j * δ₁ : ℤ)).toNat * 3 ^ (-(N j * δ₂ + s' - s : ℤ)).toNat) := by
  have hd₁ : (N j : ℤ) * δ₁ = (N j : ℤ) * ((c₁ : ℤ) + δ₁).toNat - (N j : ℤ) * c₁ := by
    rw [Int.toNat_of_nonneg h₁]; ring
  have hd₂ : (N j : ℤ) * δ₂ = (N j : ℤ) * ((c₂ : ℤ) + δ₂).toNat - (N j : ℤ) * c₂ := by
    rw [Int.toNat_of_nonneg h₂]; ring
  have ha : N j * c₁ + e + (N j * δ₁ : ℤ).toNat =
      N j * ((c₁ : ℤ) + δ₁).toNat + e + (-(N j * δ₁ : ℤ)).toNat := by
    rw [hd₁]; omega
  have hb : s + N j * c₂ + D + (N j * δ₂ + s' - s : ℤ).toNat =
      s' + N j * ((c₂ : ℤ) + δ₂).toNat + D + (-(N j * δ₂ + s' - s : ℤ)).toNat := by
    rw [hd₂]; omega
  simp only [build]
  calc (2 : ℤ) ^ (N j * c₁ + e) * 3 ^ (s + N j * c₂ + D) * m * 2 ^ (N j * δ₁ : ℤ).toNat *
        3 ^ (N j * δ₂ + s' - s : ℤ).toNat
      = 2 ^ (N j * c₁ + e + (N j * δ₁ : ℤ).toNat) *
          3 ^ (s + N j * c₂ + D + (N j * δ₂ + s' - s : ℤ).toNat) * m := by ring
    _ = 2 ^ (N j * ((c₁ : ℤ) + δ₁).toNat + e + (-(N j * δ₁ : ℤ)).toNat) *
          3 ^ (s' + N j * ((c₂ : ℤ) + δ₂).toNat + D + (-(N j * δ₂ + s' - s : ℤ)).toNat) * m := by
        rw [ha, hb]
    _ = _ := by ring

theorem scale_build {j e D s s' c₁ c₂ : ℕ} {m δ₁ δ₂ : ℤ} (h₁ : 0 ≤ (c₁ : ℤ) + δ₁)
    (h₂ : 0 ≤ (c₂ : ℤ) + δ₂) :
    scale (build j e D m s c₁ c₂) (N j * δ₁) (N j * δ₂ + s' - s) =
      build j e D m s' ((c₁ : ℤ) + δ₁).toNat ((c₂ : ℤ) + δ₂).toNat := by
  rw [scale]
  exact Int.ediv_eq_of_eq_mul_left (mul_ne_zero (pow_ne_zero _ (by norm_num))
    (pow_ne_zero _ (by norm_num))) (build_mul_eq h₁ h₂)

/-! ### Lemma P -/

/-- The order of `3` mod `5^j` is at least `j`, so any number of states fits. -/
theorem le_orderOf_three {j : ℕ} (hj : 1 ≤ j) : j ≤ orderOf (3 : ZMod (5 ^ j)) := by
  have h3 := three_pow_N hj
  have hk : 0 < orderOf (3 : ZMod (5 ^ j)) := orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2
    ⟨N j, N_pos j, h3⟩)
  set k := orderOf (3 : ZMod (5 ^ j))
  have hp : ((3 ^ k : ℕ) : ZMod (5 ^ j)) = ((1 : ℕ) : ZMod (5 ^ j)) := by
    push_cast; exact pow_orderOf_eq_one _
  have hd : 5 ^ j ∣ 3 ^ k - 1 :=
    (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).1
      ((ZMod.natCast_eq_natCast_iff _ _ _).1 hp).symm
  have h1 : 1 < 3 ^ k := Nat.one_lt_pow hk.ne' (by norm_num)
  have hle : 5 ^ j ≤ 3 ^ k - 1 := Nat.le_of_dvd (by omega) hd
  have h35 : 3 ^ k ≤ 5 ^ k := Nat.pow_le_pow_left (by norm_num) k
  have hlt : 5 ^ j < 5 ^ k := by omega
  exact ((Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt).le

/-- The engine phase is below `N j`. -/
theorem phase_lt {j : ℕ} (hj : 1 ≤ j) {n : ℤ} (hn : InEngine j n) : phase j n < N j := by
  exact dlog3_lt j _

/-- The first zero test is `2^N ∣ n`. -/
theorem one_le_C1_iff {j : ℕ} (hj : 1 ≤ j) {n : ℤ} (hn : InEngine j n) :
    1 ≤ C1 j n ↔ (2 : ℤ) ^ N j ∣ n := by
  have h := padicValInt_dvd_iff (p := 2) (N j) n
  simp only [Nat.cast_ofNat] at h
  rw [h, C1, Nat.one_le_div_iff (N_pos j)]
  constructor
  · intro h1; right; exact h1
  · rintro (h1 | h1)
    · exact absurd h1 hn.1
    · exact h1

/-- The second zero test is `3^(N + phase n) ∣ n`. -/
theorem one_le_C2_iff {j : ℕ} (hj : 1 ≤ j) {n : ℤ} (hn : InEngine j n) :
    1 ≤ C2 j n ↔ (3 : ℤ) ^ (N j + phase j n) ∣ n := by
  have hb : phase j n ≤ v3 n := hn.2.2.2
  have h := padicValInt_dvd_iff (p := 3) (N j + phase j n) n
  simp only [Nat.cast_ofNat] at h
  rw [h, C2, Nat.one_le_div_iff (N_pos j)]
  constructor
  · intro h1; right; change N j + phase j n ≤ v3 n; omega
  · rintro (h1 | h1)
    · exact absurd h1 hn.1
    · change N j + phase j n ≤ v3 n at h1; omega

section Step

variable {j : ℕ} (hj : 1 ≤ j) {n : ℤ} (hn : InEngine j n) {s' : ℕ}
  (hs' : s' < orderOf (3 : ZMod (5 ^ j))) {δ₁ δ₂ : ℤ}
  (h₁ : 0 ≤ (C1 j n : ℤ) + δ₁) (h₂ : 0 ≤ (C2 j n : ℤ) + δ₂)
include hj hn hs' h₁ h₂

omit hs' in
theorem scale_eq : scale n (N j * δ₁) (N j * δ₂ + s' - phase j n) =
    build j (junk j n).1 (junk j n).2.1 (junk j n).2.2 s' ((C1 j n : ℤ) + δ₁).toNat
      ((C2 j n : ℤ) + δ₂).toNat := by
  have h := scale_build (j := j) (e := (junk j n).1) (D := (junk j n).2.1)
    (m := (junk j n).2.2) (s := phase j n) (s' := s') h₁ h₂
  rwa [← (decode_spec hj hn).2.2.2.2.2] at h

theorem build_scale_spec :
    InEngine j (scale n (N j * δ₁) (N j * δ₂ + s' - phase j n)) ∧
      phase j (scale n (N j * δ₁) (N j * δ₂ + s' - phase j n)) = s' ∧
      C1 j (scale n (N j * δ₁) (N j * δ₂ + s' - phase j n)) = ((C1 j n : ℤ) + δ₁).toNat ∧
      C2 j (scale n (N j * δ₁) (N j * δ₂ + s' - phase j n)) = ((C2 j n : ℤ) + δ₂).toNat ∧
      junk j (scale n (N j * δ₁) (N j * δ₂ + s' - phase j n)) = junk j n := by
  obtain ⟨he, hD, h2, h3, hu, -⟩ := decode_spec hj hn
  rw [scale_eq hj hn h₁ h₂]
  exact build_spec hj he hD hs' h2 h3 hu _ _

/-- The piece is exact: `scale` really multiplies by `2^{Nδ₁} 3^{Nδ₂ + s' − s}`. -/
theorem scale_spec :
    scale n (N j * δ₁) (N j * δ₂ + s' - phase j n) * 2 ^ (-(N j * δ₁ : ℤ)).toNat *
        3 ^ (-(N j * δ₂ + s' - phase j n : ℤ)).toNat =
      n * 2 ^ (N j * δ₁ : ℤ).toNat * 3 ^ (N j * δ₂ + s' - phase j n : ℤ).toNat := by
  have h := build_mul_eq (j := j) (e := (junk j n).1) (D := (junk j n).2.1)
    (m := (junk j n).2.2) (s := phase j n) (s' := s') h₁ h₂
  rw [← (decode_spec hj hn).2.2.2.2.2] at h
  rw [scale_eq hj hn h₁ h₂, h, mul_assoc]

/-- The piece maps the engine into the engine. -/
theorem inEngine_scale : InEngine j (scale n (N j * δ₁) (N j * δ₂ + s' - phase j n)) := by
  exact (build_scale_spec hj hn hs' h₁ h₂).1

/-- The piece moves the state to `s'`. -/
theorem phase_scale : phase j (scale n (N j * δ₁) (N j * δ₂ + s' - phase j n)) = s' := by
  exact (build_scale_spec hj hn hs' h₁ h₂).2.1

/-- The piece adds `δ₁` to the first counter. -/
theorem C1_scale :
    (C1 j (scale n (N j * δ₁) (N j * δ₂ + s' - phase j n)) : ℤ) = C1 j n + δ₁ := by
  rw [(build_scale_spec hj hn hs' h₁ h₂).2.2.1, Int.toNat_of_nonneg h₁]

/-- The piece adds `δ₂` to the second counter. -/
theorem C2_scale :
    (C2 j (scale n (N j * δ₁) (N j * δ₂ + s' - phase j n)) : ℤ) = C2 j n + δ₂ := by
  rw [(build_scale_spec hj hn hs' h₁ h₂).2.2.2.1, Int.toNat_of_nonneg h₂]

/-- The piece leaves the junk unchanged. -/
theorem junk_scale : junk j (scale n (N j * δ₁) (N j * δ₂ + s' - phase j n)) = junk j n := by
  exact (build_scale_spec hj hn hs' h₁ h₂).2.2.2.2

end Step

/-- An engine point is determined by its state, counters and junk. -/
theorem eq_of_decode_eq {j : ℕ} (hj : 1 ≤ j) {n n' : ℤ} (hn : InEngine j n)
    (hn' : InEngine j n') (hp : phase j n = phase j n') (h1 : C1 j n = C1 j n')
    (h2 : C2 j n = C2 j n') (hjk : junk j n = junk j n') : n = n' := by
  calc n = build j (junk j n).1 (junk j n).2.1 (junk j n).2.2 (phase j n) (C1 j n) (C2 j n) :=
        (decode_spec hj hn).2.2.2.2.2
    _ = build j (junk j n').1 (junk j n').2.1 (junk j n').2.2 (phase j n') (C1 j n')
          (C2 j n') := by
        rw [hp, h1, h2, hjk]
    _ = n' := (decode_spec hj hn').2.2.2.2.2.symm

/-- The junk is independent of the configuration: every state below the order of `3`
and every counter pair occur with the junk of any engine point. -/
theorem exists_decode {j : ℕ} (hj : 1 ≤ j) {n₀ : ℤ} (h₀ : InEngine j n₀) {s : ℕ}
    (hs : s < orderOf (3 : ZMod (5 ^ j))) (c₁ c₂ : ℕ) :
    ∃ n, InEngine j n ∧ phase j n = s ∧ C1 j n = c₁ ∧ C2 j n = c₂ ∧ junk j n = junk j n₀ := by
  obtain ⟨he, hD, h2, h3, hu, -⟩ := decode_spec hj h₀
  obtain ⟨hE, hph, hc1, hc2, hjk⟩ := build_spec hj he hD hs h2 h3 hu c₁ c₂
  exact ⟨_, hE, hph, hc1, hc2, hjk⟩

end CollatzMoonshot.RcwaEngineGen
