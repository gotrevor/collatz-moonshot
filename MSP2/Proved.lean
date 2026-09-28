/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MSP2.Order

/-!
# MSP²: the results the article proves

One declaration per result the article establishes, stated over `ℕ`/`ℤ` as literally as
the text allows.  A `sorry` here means *not yet formalized*, never *doubted*: each of these
is arithmetic the article proves, and the numeric instances are already checked in
`MSP2.Checks`.  Parts of the article that need the inverse trees (§4-§7) or the Generator
Table itself (§11-§15) are not stated yet; `MSP2/README.md` lists them.
-/

namespace MSP2

open CollatzMoonshot

/-! ## §2: the odd run -/

/-- **§2.** If `M + 1 = 2^r·u` with `u` odd and `r ≥ 1`, then `r` MSP² odd steps take `M`
to `3^r·u − 1`, which is even; every intermediate value is odd. -/
theorem msp2_odd_run {M r u : ℕ} (hr : 1 ≤ r) (hu : u % 2 = 1) (hM : M + 1 = 2 ^ r * u) :
    msp2Step^[r] M = 3 ^ r * u - 1 ∧ (3 ^ r * u - 1) % 2 = 0 ∧
      ∀ i < r, msp2Step^[i] M % 2 = 1 := by
  sorry

/-- **§2.5 / §4.4.** The next odd value after a run is not a multiple of `3`, so it has the
form `6q ± 1`. -/
theorem not_three_dvd_after_run {r u s : ℕ} (hr : 1 ≤ r) (hu : 1 ≤ u)
    (hs : 2 ^ s ∣ 3 ^ r * u - 1) : ¬ 3 ∣ (3 ^ r * u - 1) / 2 ^ s := by
  intro hdvd
  obtain ⟨k, hk⟩ := hs
  have hpow : (0 : ℕ) < 2 ^ s := by positivity
  have hk3 : 3 ∣ k := by rwa [hk, Nat.mul_div_cancel_left _ hpow] at hdvd
  have h1 : 3 ∣ 3 ^ r * u - 1 := by rw [hk]; exact Dvd.dvd.mul_left hk3 _
  have h3 : 3 ∣ 3 ^ r * u := Dvd.dvd.mul_right (dvd_pow_self 3 (by omega)) u
  have hpos : 1 ≤ 3 ^ r * u := Nat.one_le_iff_ne_zero.mpr (by positivity)
  omega

/-! ## §3: the run-length families partition the odd numbers -/

/-- **§3.** Every odd `n` lies in exactly one family `2^(r+1)·k + 2^r − 1` with `r ≥ 1`. -/
theorem odd_family_unique {n : ℕ} (hn : n % 2 = 1) :
    ∃! p : ℕ × ℕ, 1 ≤ p.1 ∧ n = 2 ^ (p.1 + 1) * p.2 + 2 ^ p.1 - 1 := by
  sorry

/-! ## §9.8-9.9: uniform reproduction of the families, and the blocking points -/

/-- **§9.8.** Writing `u = 4v + s`, the surviving family `(3/4)·A_j·u + 1` is again of the
rank-`j+1` form with `A_{j+1} = 3·A_j`. -/
theorem fam_reproduce (j s v : ℕ) :
    3 * famA j / 4 * (4 * v + s) + 1 = fam (j + 1) s v := by
  have h1 : 3 * famA j / 4 = 216 * 3 ^ j := by
    simp only [famA]
    rw [show 3 * (288 * 3 ^ j) = 4 * (216 * 3 ^ j) by ring,
      Nat.mul_div_cancel_left _ (by norm_num : 0 < 4)]
  have h2 : famA (j + 1) = 864 * 3 ^ j := by simp only [famA]; ring
  have h3 : famA (j + 1) / 4 = 216 * 3 ^ j := by
    rw [h2, show (864 : ℕ) * 3 ^ j = 4 * (216 * 3 ^ j) by ring,
      Nat.mul_div_cancel_left _ (by norm_num : 0 < 4)]
  simp only [fam]
  rw [h3, h2, h1]
  ring

/-- **§9.8** (the Collatz step behind "surviving family"): three steps take `A_j·u + 1`
to `(3/4)·A_j·u + 1`. -/
theorem step_three_fam_zero (j u : ℕ) : step^[3] (fam j 0 u) = 3 * famA j / 4 * u + 1 := by
  have key : ∀ m : ℕ, step^[3] (288 * m + 1) = 216 * m + 1 := by
    intro m
    have s0 : step (288 * m + 1) = 864 * m + 4 := by
      simp only [step, if_neg (by omega : ¬ (288 * m + 1) % 2 = 0)]; ring
    have s1 : step (864 * m + 4) = 432 * m + 2 := by
      simp only [step, if_pos (by omega : (864 * m + 4) % 2 = 0)]; omega
    have s2 : step (432 * m + 2) = 216 * m + 1 := by
      simp only [step, if_pos (by omega : (432 * m + 2) % 2 = 0)]; omega
    show step (step (step _)) = _
    rw [s0, s1, s2]
  have hdiv : 3 * famA j / 4 = 216 * 3 ^ j := by
    simp only [famA]
    rw [show 3 * (288 * 3 ^ j) = 4 * (216 * 3 ^ j) by ring,
      Nat.mul_div_cancel_left _ (by norm_num : 0 < 4)]
  have h1 : fam j 0 u = 288 * (3 ^ j * u) + 1 := by
    simp only [fam, famA]; ring
  rw [h1, key, hdiv]
  ring

/-- Consequently every member `A_j·u + 1` with `u ≥ 1` is covered. -/
theorem covered_fam_zero (j u : ℕ) (hu : 1 ≤ u) : Covered (fam j 0 u) := by
  refine ⟨3, ?_⟩
  rw [step_three_fam_zero]
  have hdiv : 3 * famA j / 4 = 216 * 3 ^ j := by
    simp only [famA]
    rw [show 3 * (288 * 3 ^ j) = 4 * (216 * 3 ^ j) by ring,
      Nat.mul_div_cancel_left _ (by norm_num : 0 < 4)]
  have h1 : fam j 0 u = 288 * (3 ^ j * u) + 1 := by
    simp only [fam, famA]; ring
  have h2 : 3 * famA j / 4 * u = 216 * (3 ^ j * u) := by rw [hdiv]; ring
  have h3 : 1 ≤ 3 ^ j * u := Nat.one_le_iff_ne_zero.mpr (by positivity)
  rw [h1, h2]
  omega

/-- **§9.9.** Closed form of the blocking points: `B_j = 24·16^j + 1`. -/
theorem blockB_eq (j : ℕ) : blockB j = 24 * 16 ^ j + 1 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have h : (16 : ℕ) ^ (j + 1) = 16 * 16 ^ j := by ring
    simp only [blockB, ih, h]
    omega

/-- **§9.9.** The blocking points grow strictly: `B_{j+1} − B_j = 360·16^j`. -/
theorem blockB_succ_sub (j : ℕ) : blockB (j + 1) - blockB j = 360 * 16 ^ j := by
  rw [blockB_eq, blockB_eq]
  have h : (16 : ℕ) ^ (j + 1) = 16 * 16 ^ j := by ring
  omega

/-! ## §16.2: from coverage to reaching 1 -/

/-- **§16.2** ("De la couverture à l'arrivée à 1"): if every `2 ≤ N ≤ K` is covered, every
`1 ≤ N ≤ K` reaches `1` (strong induction). -/
theorem reachesOne_of_covered_upto {K : ℕ} (h : ∀ N, 2 ≤ N → N ≤ K → Covered N) :
    ∀ N, 1 ≤ N → N ≤ K → ReachesOne N := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hN hK
    rcases eq_or_lt_of_le hN with h1 | h2
    · exact h1 ▸ reachesOne_one
    · obtain ⟨j, hj⟩ := h N h2 hK
      have hm1 : 1 ≤ step^[j] N := iterate_step_pos hN j
      obtain ⟨c, hc⟩ := ih (step^[j] N) hj hm1 (by omega)
      exact ⟨c + j, by rw [Function.iterate_add_apply, hc]⟩

/-- The article's `T` is the grouped step `msp2Step`; covered under it and under the
un-accelerated `step` coincide (the skipped value `3M+1` is never the first dip). -/
theorem covered_iff_msp2 {N : ℕ} (hN : 2 ≤ N) : Covered N ↔ ∃ j, msp2Step^[j] N < N := by
  sorry

/-! ## §16.3-16.5: the B constants and the useful distances -/

/-- **§16.3-16.4.** Closed form `B_n = (A_n − 1)/2` with `A_n = 3^(n+2)`. -/
theorem bConst_closed (n : ℕ) : 2 * bConst n + 1 = 3 ^ (n + 2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : (3 : ℕ) ^ (n + 1 + 2) = 3 * 3 ^ (n + 2) := by ring
    simp only [bConst, h]
    omega

/-- **§16.4.** The parity of `B_n` alternates, starting even. -/
theorem bConst_parity (n : ℕ) : bConst n % 2 = n % 2 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [bConst]; omega

/-- **§16.3.** Under the vertical rule at `A = 3^(n+2)`, the useful distance from `1` to
`B_n` is `3^(n+1) + 1` (4, 10, 28, 82, …): reached at that step and not before. -/
theorem tA_distance (n : ℕ) :
    (tA (3 ^ (n + 2)))^[3 ^ (n + 1) + 1] 1 = bConst n ∧
      ∀ i < 3 ^ (n + 1) + 1, (tA (3 ^ (n + 2)))^[i] 1 ≠ bConst n := by
  have hA : (3 : ℕ) ^ (n + 2) % 2 = 1 := by simp [Nat.pow_mod]
  have hb : 2 * bConst n + 1 = 3 ^ (n + 2) := bConst_closed n
  have hbz : 2 * (bConst n : ℤ) + 1 = 3 ^ (n + 2) := by exact_mod_cast hb
  have hA9 : 9 ≤ (3 : ℕ) ^ (n + 2) := by
    calc (9 : ℕ) = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hBlt : bConst n < 3 ^ (n + 2) := by omega
  have h1lt : 1 < (3 : ℕ) ^ (n + 2) := by omega
  -- `2^(3^(n+1)) ≡ −1`, so `2^(3^(n+1)+1) · Bₙ ≡ (−1)·(−1) = 1`
  have hkey : 2 ^ (3 ^ (n + 1) + 1) * bConst n ≡ 1 [MOD 3 ^ (n + 2)] := by
    refine Nat.modEq_iff_dvd.mpr ?_
    push_cast
    obtain ⟨c, hc, -⟩ := two_pow_three_pow (n + 1)
    exact ⟨1 + c - 3 ^ (n + 2) * c, by
      linear_combination (-2 * (bConst n : ℤ)) * hc + (1 - 3 ^ (n + 2) * c) * hbz⟩
  refine ⟨tA_iterate_eq hA h1lt hBlt _ hkey, ?_⟩
  intro i hi heq
  -- an earlier hit would make `2^(i−1) ≡ −1` strictly inside the half period
  have h2 : 2 ^ i * bConst n ≡ 1 [MOD 3 ^ (n + 2)] := by
    have h := two_pow_mul_iterate hA 1 i
    rwa [heq] at h
  obtain ⟨w, hw⟩ : ((3 : ℕ) ^ (n + 2) : ℤ) ∣ 1 - 2 ^ i * (bConst n : ℤ) := by
    have h := Nat.modEq_iff_dvd.mp h2
    push_cast at h ⊢
    exact h
  have h3 : (3 : ℕ) ^ (n + 2) ∣ 2 ^ i + 2 := by
    have hz : ((3 : ℕ) ^ (n + 2) : ℤ) ∣ ((2 ^ i + 2 : ℕ) : ℤ) :=
      ⟨2 * w + 2 ^ i, by push_cast; linear_combination 2 * hw + (2 : ℤ) ^ i * hbz⟩
    exact_mod_cast hz
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · norm_num at h3
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have hfac : 2 ^ (k + 1) + 2 = 2 * (2 ^ k + 1) := by ring
    rw [hfac] at h3
    have hodd : Nat.Coprime ((3 : ℕ) ^ (n + 2)) 2 :=
      Nat.coprime_two_right.mpr (Nat.odd_iff.mpr hA)
    have h4 : (3 : ℕ) ^ (n + 2) ∣ 2 ^ k + 1 := hodd.dvd_of_dvd_mul_left h3
    have h5 : (3 : ℕ) ^ (n + 1) ∣ k := three_pow_dvd_of_dvd_two_pow_add_one h4
    have hklt : k < 3 ^ (n + 1) := by omega
    have hk0 : k = 0 := Nat.eq_zero_of_dvd_of_lt h5 hklt
    subst hk0
    norm_num at h4
    have := Nat.le_of_dvd (by norm_num) h4
    omega

/-- **§16.5.** The left route revisits the right side on alternate levels:
`C_{2m+2} = B_{2m+1}` (13, 121, 1093, …). -/
theorem cLeft_even_eq_bConst (m : ℕ) : cLeft (2 * m + 2) = bConst (2 * m + 1) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have e1 : 2 * (m + 1) + 2 = 2 * m + 2 + 2 := by ring
    have e2 : 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 := by ring
    have c1 : cLeft (2 * m + 2 + 2) = 9 * cLeft (2 * m + 2) + 4 := rfl
    have b1 : bConst (2 * m + 1 + 1) = 3 * bConst (2 * m + 1) + 1 := rfl
    have b2 : bConst (2 * m + 1 + 1 + 1) = 3 * bConst (2 * m + 1 + 1) + 1 := rfl
    rw [e1, e2, c1, b2, b1, ih]
    ring

/-- Closed form of the left route on even indices: `2·C_{2t} + 1 = 3^(2t+1)`. -/
theorem cLeft_closed_even (t : ℕ) : 2 * cLeft (2 * t) + 1 = 3 ^ (2 * t + 1) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have e1 : 2 * (t + 1) = 2 * t + 2 := by ring
    have c1 : cLeft (2 * t + 2) = 9 * cLeft (2 * t) + 4 := rfl
    have e2 : (3 : ℕ) ^ (2 * t + 2 + 1) = 9 * 3 ^ (2 * t + 1) := by ring
    rw [e1, c1, e2]
    omega

/-- Closed form of the left route on odd indices: `2·C_{2t+1} + 1 = 5·3^(2t+2)`. -/
theorem cLeft_closed_odd (t : ℕ) : 2 * cLeft (2 * t + 1) + 1 = 5 * 3 ^ (2 * t + 2) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have e1 : 2 * (t + 1) + 1 = 2 * t + 1 + 2 := by ring
    have c1 : cLeft (2 * t + 1 + 2) = 9 * cLeft (2 * t + 1) + 4 := rfl
    have e2 : (3 : ℕ) ^ (2 * (t + 1) + 2) = 9 * 3 ^ (2 * t + 2) := by
      rw [show 2 * (t + 1) + 2 = 2 * t + 2 + 2 by ring]; ring
    rw [e1, c1, e2]
    omega

/-- **§16.5.** The useful distance between the two sides at `A = 3^(m+3)` is `2·3^(m+1)`
(6, 18, 54, …), in the direction that alternates with the level. -/
theorem tA_distance_opt2 (m : ℕ) :
    if m % 2 = 0 then (tA (3 ^ (m + 3)))^[2 * 3 ^ (m + 1)] (cLeft (m + 1)) = bConst (m + 1)
    else (tA (3 ^ (m + 3)))^[2 * 3 ^ (m + 1)] (bConst (m + 1)) = cLeft (m + 1) := by
  have hA : (3 : ℕ) ^ (m + 3) % 2 = 1 := by simp [Nat.pow_mod]
  have hbn : 2 * bConst (m + 1) + 1 = 3 ^ (m + 3) := by
    have h := bConst_closed (m + 1)
    rwa [show m + 1 + 2 = m + 3 from by ring] at h
  have hbz : 2 * (bConst (m + 1) : ℤ) + 1 = 3 ^ (m + 3) := by exact_mod_cast hbn
  have h3 : (3 : ℕ) ^ (m + 3) = 3 * 3 ^ (m + 2) := by ring
  have h2 : (3 : ℕ) ^ (m + 2) = 3 * 3 ^ (m + 1) := by ring
  -- the distance `2·3^(m+1)` is a third of the loop: `2^(2·3^(m+1)) ≡ 1 + 3^(m+2)`
  obtain ⟨w, hw0⟩ := two_pow_two_mul_three_pow (m + 1)
  have hw : (2 : ℤ) ^ (2 * 3 ^ (m + 1)) = 1 + 3 ^ (m + 2) + 3 ^ (m + 3) * w := by
    linear_combination hw0
  have hcl_even : m % 2 = 0 → 2 * cLeft (m + 1) + 1 = 5 * 3 ^ (m + 2) := by
    intro hm
    obtain ⟨t, rfl⟩ : ∃ t, m = 2 * t := ⟨m / 2, by omega⟩
    exact cLeft_closed_odd t
  have hcl_odd : m % 2 = 1 → 2 * cLeft (m + 1) + 1 = 3 ^ (m + 2) := by
    intro hm
    obtain ⟨t, rfl⟩ : ∃ t, m = 2 * t + 1 := ⟨m / 2, by omega⟩
    have h := cLeft_closed_even (t + 1)
    rw [show 2 * (t + 1) + 1 = 2 * t + 1 + 2 from by ring,
        show 2 * (t + 1) = 2 * t + 1 + 1 from by ring] at h
    exact h
  by_cases hm : m % 2 = 0
  · rw [if_pos hm]
    have hcn := hcl_even hm
    have hcz : 2 * (cLeft (m + 1) : ℤ) + 1 = 5 * 3 ^ (m + 2) := by exact_mod_cast hcn
    refine tA_iterate_eq hA ?_ ?_ _ ?_
    · omega
    · omega
    refine modEq_of_two_mul hA (Nat.modEq_iff_dvd.mpr ?_)
    push_cast
    exact ⟨2 - 2 ^ (2 * 3 ^ (m + 1)) + w, by
      linear_combination hw - (2 : ℤ) ^ (2 * 3 ^ (m + 1)) * hbz + hcz⟩
  · rw [if_neg hm]
    have hcn := hcl_odd (by omega)
    have hcz : 2 * (cLeft (m + 1) : ℤ) + 1 = 3 ^ (m + 2) := by exact_mod_cast hcn
    refine tA_iterate_eq hA ?_ ?_ _ ?_
    · omega
    · omega
    refine modEq_of_two_mul hA (Nat.modEq_iff_dvd.mpr ?_)
    push_cast
    exact ⟨1 - 3 ^ (m + 1) + w - w * 3 ^ (m + 2), by
      linear_combination hbz - (2 : ℤ) ^ (2 * 3 ^ (m + 1)) * hcz + (1 - 3 ^ (m + 2)) * hw⟩

/-! ## §16.7: the vertical rule is multiplication by `2⁻¹` -/

/-- **§16.7.1.** For odd `A`, `T_A(b) ≡ b·2⁻¹ (mod A)`, i.e. `2·T_A(b) ≡ b`. -/
theorem tA_two_mul {A : ℕ} (hA : A % 2 = 1) (b : ℕ) : 2 * tA A b ≡ b [MOD A] :=
  tA_two_modEq hA b

/-- **§16.7.2.** At `A = 3ⁿ` the vertical loop through any `b` prime to `3` has length
`2·3^(n−1)` (2 is a primitive root mod `3ⁿ`). -/
theorem tA_period {n b : ℕ} (hn : 1 ≤ n) (hb : b < 3 ^ n) (h3 : ¬ 3 ∣ b) :
    Function.minimalPeriod (tA (3 ^ n)) b = 2 * 3 ^ (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hA : (3 : ℕ) ^ (m + 1) % 2 = 1 := by simp [Nat.pow_mod]
  have hcop : Nat.Coprime ((3 : ℕ) ^ (m + 1)) b :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
  have hone : 2 ^ (2 * 3 ^ m) ≡ 1 [MOD 3 ^ (m + 1)] :=
    zmod_pow_eq_one_iff.mp (by rw [← orderOf_two_zmod m]; exact pow_orderOf_eq_one _)
  have hfix : (tA (3 ^ (m + 1)))^[2 * 3 ^ m] b = b := by
    refine tA_iterate_eq hA hb hb _ ?_
    calc 2 ^ (2 * 3 ^ m) * b ≡ 1 * b [MOD 3 ^ (m + 1)] := Nat.ModEq.mul_right b hone
      _ = b := one_mul b
  have hper : Function.IsPeriodicPt (tA (3 ^ (m + 1))) (2 * 3 ^ m) b := hfix
  have hdvd1 : Function.minimalPeriod (tA (3 ^ (m + 1))) b ∣ 2 * 3 ^ m := hper.minimalPeriod_dvd
  have hpfix : (tA (3 ^ (m + 1)))^[Function.minimalPeriod (tA (3 ^ (m + 1))) b] b = b :=
    Function.isPeriodicPt_minimalPeriod _ _
  have hmod : 2 ^ Function.minimalPeriod (tA (3 ^ (m + 1))) b * b ≡ 1 * b [MOD 3 ^ (m + 1)] := by
    rw [one_mul]
    have h := two_pow_mul_iterate hA b (Function.minimalPeriod (tA (3 ^ (m + 1))) b)
    rwa [hpfix] at h
  have hdvd2 : 2 * 3 ^ m ∣ Function.minimalPeriod (tA (3 ^ (m + 1))) b := by
    rw [← orderOf_two_zmod m]
    exact orderOf_dvd_of_pow_eq_one
      (zmod_pow_eq_one_iff.mpr (Nat.ModEq.cancel_right_of_coprime hcop hmod))
  exact Nat.dvd_antisymm hdvd1 hdvd2

/-- **§16.7.4**, the closed form the article gives for its recurrence:
`Δ_n = (9·(−3)ⁿ − 5)/2`.  (This is algebra; the open question is whether the Generator
Table's cousin jumps obey `delta` at every level.) -/
theorem delta_closed (n : ℕ) : 2 * delta n = 9 * (-3) ^ n - 5 := by
  induction n with
  | zero => norm_num [delta]
  | succ n ih =>
    simp only [delta, pow_succ]
    linarith

/-- **§16.7.4**, the conditional algebra: with the §16.4 passage (`k ↦ 2k+1` when `B_n` is
even, `k ↦ 2k` when odd, shift `+1`, cousin jump `+Δ_{n+1}`, halve), the jump `delta`
carries `B_n` to `B_{n+1}`. -/
theorem bConst_succ_via_delta (n : ℕ) :
    2 * (bConst (n + 1) : ℤ) =
      (if n % 2 = 0 then 3 * ((3 : ℤ) ^ (n + 2) + bConst n + 1) else 3 * ((bConst n : ℤ) + 1))
        + delta (n + 1) := by
  have hb : 2 * (bConst n : ℤ) + 1 = 3 ^ (n + 2) := by
    have := bConst_closed n; exact_mod_cast this
  have hb1 : 2 * (bConst (n + 1) : ℤ) + 1 = 3 ^ (n + 1 + 2) := by
    have := bConst_closed (n + 1); exact_mod_cast this
  have hd : 2 * delta (n + 1) = 9 * (-3) ^ (n + 1) - 5 := delta_closed _
  have h32 : (3 : ℤ) ^ (n + 2) = 3 * 3 ^ (n + 1) := by ring
  have h33 : (3 : ℤ) ^ (n + 1 + 2) = 9 * 3 ^ (n + 1) := by ring
  rcases Nat.even_or_odd n with he | ho
  · rw [if_pos (Nat.even_iff.mp he)]
    have hneg : ((-3 : ℤ)) ^ (n + 1) = -(3 : ℤ) ^ (n + 1) :=
      Odd.neg_pow (Even.add_one he) 3
    rw [hneg] at hd
    linarith
  · rw [if_neg (by have := Nat.odd_iff.mp ho; omega)]
    have hneg : ((-3 : ℤ)) ^ (n + 1) = (3 : ℤ) ^ (n + 1) :=
      Even.neg_pow (Odd.add_one ho) 3
    rw [hneg] at hd
    linarith

/-! ## §16.8: the residue bound -/

/-- **§16.8** (Proposition): for `m ≥ 2`, `B_{m−2} = (3^m − 1)/2 > K_m = 2^m − 1`. -/
theorem residue_bound {m : ℕ} (hm : 2 ≤ m) : 2 ^ m - 1 < (3 ^ m - 1) / 2 := by
  have key : ∀ k : ℕ, 2 * 2 ^ (k + 2) + 1 ≤ 3 ^ (k + 2) := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      have h2 : (2 : ℕ) ^ (k + 1 + 2) = 2 * 2 ^ (k + 2) := by ring
      have h3 : (3 : ℕ) ^ (k + 1 + 2) = 3 * 3 ^ (k + 2) := by ring
      omega
  have gen : ∀ A B : ℕ, 1 ≤ B → 2 * B + 1 ≤ A → A % 2 = 1 → B - 1 < (A - 1) / 2 := by
    intro A B h0 h1 h2
    obtain ⟨C, rfl⟩ : ∃ C, A = C + 1 := ⟨A - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    omega
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  exact gen _ _ (Nat.one_le_two_pow) (key k) (by simp [Nat.pow_mod])

end MSP2
