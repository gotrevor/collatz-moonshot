/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.ChampernowneOne

/-!
# Early arrival makes `𝒞_C` non-normal

Once `tstep^[t] n = 1` the letters from `t` on are the alternating tail `1010…` of the cycle
`1 → 2 → 1`, so the block `(10)^m` occurs at every other offset from `t` on
(`windowMatch_altWord`).  For `n` in stage `k` with hitting time `≤ r k`, that is about
`((C − r) k − 2m) / 2` occurrences in its word (`card_mul_le_interior`).  Over stage `k` alone this
is a density at least `ρ (C − r) / (4 C)` in the prefix ending with the stage
(`cum_stage_end_le`), a bound independent of `m`, and normality would force `2^(−2m)`.

Only the prefixes ending with a stage are needed.  No input about the in-flight letters enters.

The block `11` is weaker: its tail frequency is `0`, and an in-flight `11`-density above `1/4` could
compensate, so that route needs in-flight input as well.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord

/-- The alternating word `(10)^m`. -/
def altWord (m : ℕ) : List Bool := (List.range (2 * m)).map fun s => decide (s % 2 = 0)

@[simp] theorem length_altWord (m : ℕ) : (altWord m).length = 2 * m := by
  simp [altWord]

/-- From a hit of `1` on, the orbit alternates `1, 2, 1, 2, …`. -/
private theorem iterate_of_iterate_eq_one {n t : ℕ} (h : tstep^[t] n = 1) (i : ℕ) :
    tstep^[t + i] n = if i % 2 = 0 then 1 else 2 := by
  induction i with
  | zero => simpa using h
  | succ i ih =>
    rw [← add_assoc, Function.iterate_succ_apply', ih]
    by_cases hi : i % 2 = 0
    · have : (i + 1) % 2 ≠ 0 := by omega
      simp [hi, this]
    · have : (i + 1) % 2 = 0 := by omega
      simp [hi, this]

/-- From a hit of `1` on, the letters alternate `1, 0, 1, 0, …`. -/
theorem accWord_of_iterate_eq_one {n t : ℕ} (h : tstep^[t] n = 1) (i : ℕ) :
    accWord n (t + i) = decide (i % 2 = 0) := by
  simp only [accWord, iterate_of_iterate_eq_one h i]
  by_cases hi : i % 2 = 0 <;> simp [hi]

/-- Inside its length, `altWord m` reads `decide (s % 2 = 0)`. -/
private theorem altWord_getD {m s : ℕ} (hs : s < 2 * m) :
    (altWord m).getD s false = decide (s % 2 = 0) := by
  simp [altWord, List.getD_eq_getElem?_getD, hs]

/-- The block `(10)^m` occurs at every other offset from a hit of `1` on. -/
theorem windowMatch_altWord {n t : ℕ} (h : tstep^[t] n = 1) (m i : ℕ) :
    WindowMatch (fun s => (altWord m).getD s false) (altWord m).length (t + 2 * i) n := by
  intro s hs
  rw [length_altWord] at hs
  show accWord n (t + 2 * i + s) = (altWord m).getD s false
  rw [altWord_getD hs, add_assoc, accWord_of_iterate_eq_one h]
  have : (2 * i + s) % 2 = s % 2 := by omega
  rw [this]

/-- A set `A` of stage `k` whose words hold `q` such offsets gives `|A| q` interior occurrences. -/
theorem card_mul_le_interior (C : ℕ) (hC : 1 ≤ C) (m k q : ℕ) (hk : 1 ≤ k) (A : Finset ℕ)
    (hA : ∀ n ∈ A, 2 ^ (k - 1) ≤ n ∧ n < 2 ^ k)
    (hfit : ∀ n ∈ A, ∃ t, t + 2 * q + 2 * m ≤ C * k ∧ tstep^[t] n = 1) :
    A.card * q ≤
      interior C (fun s => (altWord m).getD s false) (altWord m).length (2 ^ k - 1) := by
  have hpos : ∀ n ∈ A, 1 ≤ n := fun n hn => le_trans Nat.one_le_two_pow (hA n hn).1
  set f : ℕ → ℕ := fun n => ((Finset.range (champLen C n)).filter fun i =>
    i + (altWord m).length ≤ champLen C n ∧
      WindowMatch (fun s => (altWord m).getD s false) (altWord m).length i (n + 1)).card with hf
  have hword : ∀ n ∈ A, q ≤ f (n - 1) := by
    intro n hn
    obtain ⟨h1, h2⟩ := hA n hn
    have hn1 := hpos n hn
    have hsize : Nat.size n = k := by
      apply le_antisymm (Nat.size_le.2 h2)
      have : k - 1 < Nat.size n := Nat.lt_size.2 h1
      omega
    have hlen : champLen C (n - 1) = C * k := by
      simp [champLen, Nat.sub_add_cancel hn1, hsize, max_eq_left hC]
    obtain ⟨t, ht, hit⟩ := hfit n hn
    have hcard : (Finset.range q).card ≤ f (n - 1) := by
      apply Finset.card_le_card_of_injOn (fun i => t + 2 * i)
      · intro i hi
        have hi' : i < q := by simpa using hi
        simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq, hlen, length_altWord]
        refine ⟨by omega, by omega, ?_⟩
        rw [Nat.sub_add_cancel hn1]
        have hw := windowMatch_altWord hit m i
        rwa [length_altWord] at hw
      · intro a _ b _ hab
        simp only at hab
        omega
    simpa using hcard
  have hinj : Set.InjOn (fun n => n - 1) (A : Set ℕ) := by
    intro a ha b hb hab
    have := hpos a ha
    have := hpos b hb
    simp only at hab
    omega
  have hsub : A.image (fun n => n - 1) ⊆ Finset.range (2 ^ k - 1) := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hx
    have := hpos n hn
    have := (hA n hn).2
    rw [Finset.mem_range]
    omega
  calc A.card * q = ∑ _n ∈ A, q := by simp
    _ ≤ ∑ n ∈ A, f (n - 1) := Finset.sum_le_sum hword
    _ = ∑ x ∈ A.image (fun n => n - 1), f x := (Finset.sum_image hinj).symm
    _ ≤ ∑ x ∈ Finset.range (2 ^ k - 1), f x := Finset.sum_le_sum_of_subset hsub
    _ = _ := rfl

/-- The prefix ending with stage `k` has at most `C k 2^k` letters. -/
theorem cum_stage_end_le (C : ℕ) (hC : 1 ≤ C) (k : ℕ) :
    cum (champLen C) (2 ^ k - 1) ≤ C * k * 2 ^ k := by
  have key : ∀ N, N ≤ 2 ^ k - 1 → cum (champLen C) N ≤ C * k * N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      intro hN
      have hs : Nat.size (N + 1) ≤ k := Nat.size_le.2 (by omega)
      have hl : champLen C N ≤ C * k := by
        rw [champLen, max_eq_left hC]
        exact Nat.mul_le_mul_left C hs
      rw [cum_succ, Nat.mul_succ]
      exact Nat.add_le_add (ih (by omega)) hl
  exact (key _ le_rfl).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))

/-- The rate `r < C` forces `C ≥ 1`: for `C = 0` no `t` has `t ≤ r k < 0`. -/
theorem one_le_of_earlyArrival {C : ℕ} (h : EarlyArrival C) : 1 ≤ C := by
  by_contra hC
  obtain rfl : C = 0 := by omega
  obtain ⟨r, ρ, hr, hρ, hev⟩ := h
  obtain ⟨k, hk, hk1⟩ := (hev.and (eventually_ge_atTop 1)).exists
  have hr0 : r < 0 := by simpa using hr
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hempty : {n : ℕ | 2 ^ (k - 1) ≤ n ∧ n < 2 ^ k ∧
      ∃ t : ℕ, (t : ℝ) ≤ r * k ∧ tstep^[t] n = 1} = ∅ := by
    ext n
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨_, _, t, ht, _⟩
    have h1 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    have h2 : r * k < 0 := mul_neg_of_neg_of_pos hr0 hk0
    linarith
  rw [hempty, Set.ncard_empty] at hk
  have : (0 : ℝ) < ρ * 2 ^ (k - 1) := by positivity
  simp at hk
  linarith

/-- Stage `k` alone gives the prefix ending with it density `≥ ρ (D k − 2m − 2) / (4 C k)`. -/
private theorem density_lower (C : ℕ) (hC : 1 ≤ C) (r ρ : ℝ) (hρ : 0 < ρ) (m k : ℕ) (hk : 1 ≤ k)
    (hcount : ρ * 2 ^ (k - 1) ≤
      (Set.ncard {n : ℕ | 2 ^ (k - 1) ≤ n ∧ n < 2 ^ k ∧
        ∃ t : ℕ, (t : ℝ) ≤ r * k ∧ tstep^[t] n = 1} : ℝ))
    (hbig : 2 * (m : ℝ) + 2 ≤ ((C : ℝ) - r) * k) :
    ρ * (((C : ℝ) - r) * k - 2 * m - 2) / (4 * C * k) ≤
      (occ (collatzChampernowne C) (altWord m) (cum (champLen C) (2 ^ k - 1)) : ℝ) /
        (cum (champLen C) (2 ^ k - 1) : ℝ) := by
  classical
  set x : ℝ := (((C : ℝ) - r) * k - 2 * m) / 2 with hx
  have hx0 : 0 ≤ x := by rw [hx]; linarith
  set q : ℕ := ⌊x⌋₊ with hq
  have hq1 : (q : ℝ) ≤ x := Nat.floor_le hx0
  have hq2 : x < (q : ℝ) + 1 := Nat.lt_floor_add_one x
  set A : Finset ℕ := (Finset.Ico (2 ^ (k - 1)) (2 ^ k)).filter
    fun n => ∃ t : ℕ, (t : ℝ) ≤ r * k ∧ tstep^[t] n = 1 with hAdef
  have hAset : {n : ℕ | 2 ^ (k - 1) ≤ n ∧ n < 2 ^ k ∧
      ∃ t : ℕ, (t : ℝ) ≤ r * k ∧ tstep^[t] n = 1} = (A : Set ℕ) := by
    ext n
    simp [hAdef, and_assoc]
  rw [hAset, Set.ncard_coe_finset] at hcount
  have hA : ∀ n ∈ A, 2 ^ (k - 1) ≤ n ∧ n < 2 ^ k := by
    intro n hn
    have := (Finset.mem_filter.1 hn).1
    exact Finset.mem_Ico.1 this
  have hfit : ∀ n ∈ A, ∃ t, t + 2 * q + 2 * m ≤ C * k ∧ tstep^[t] n = 1 := by
    intro n hn
    obtain ⟨t, ht, hit⟩ := (Finset.mem_filter.1 hn).2
    refine ⟨t, ?_, hit⟩
    have : ((t + 2 * q + 2 * m : ℕ) : ℝ) ≤ ((C * k : ℕ) : ℝ) := by
      push_cast
      rw [hx] at hq1
      nlinarith
    exact_mod_cast this
  have hocc : A.card * q ≤
      occ (collatzChampernowne C) (altWord m) (cum (champLen C) (2 ^ k - 1)) :=
    (card_mul_le_interior C hC m k q hk A hA hfit).trans (occ_cum_le C (altWord m) _).1
  have hP := cum_stage_end_le C hC k
  have hPpos : 0 < cum (champLen C) (2 ^ k - 1) := by
    have h1 := le_cum (champLen C) (one_le_champLen C) (2 ^ k - 1)
    have h2 : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hCR : (0 : ℝ) < C := by exact_mod_cast hC
  set P : ℝ := (cum (champLen C) (2 ^ k - 1) : ℝ) with hPdef
  set O : ℝ := (occ (collatzChampernowne C) (altWord m) (cum (champLen C) (2 ^ k - 1)) : ℝ) with hO
  have hPR : 0 < P := by rw [hPdef]; exact_mod_cast hPpos
  set a : ℝ := (2 : ℝ) ^ (k - 1) with ha
  have ha0 : 0 < a := by positivity
  have h2k : (2 : ℝ) ^ k = 2 * a := by
    rw [ha, ← pow_succ']
    congr 1
    omega
  have hPle : P ≤ C * k * (2 * a) := by
    rw [← h2k, hPdef]
    exact_mod_cast hP
  have hOge : ρ * a * q ≤ O := by
    have h1 : ((A.card : ℝ)) * q ≤ O := by rw [hO]; exact_mod_cast hocc
    exact (mul_le_mul_of_nonneg_right hcount (Nat.cast_nonneg q)).trans h1
  set y : ℝ := ((C : ℝ) - r) * k - 2 * m - 2 with hy
  have hy0 : 0 ≤ y := by rw [hy]; linarith
  have hqy : y ≤ 2 * q := by
    rw [hx] at hq2
    rw [hy]
    linarith
  rw [div_le_div_iff₀ (by positivity) hPR]
  have s1 : ρ * y * P ≤ ρ * y * (C * k * (2 * a)) :=
    mul_le_mul_of_nonneg_left hPle (by positivity)
  have s2 : ρ * y * (C * k * (2 * a)) ≤ ρ * (2 * q) * (C * k * (2 * a)) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hqy hρ.le
  have s3 : ρ * a * q * (4 * C * k) ≤ O * (4 * C * k) :=
    mul_le_mul_of_nonneg_right hOge (by positivity)
  calc ρ * y * P ≤ ρ * (2 * q) * (C * k * (2 * a)) := s1.trans s2
    _ = ρ * a * q * (4 * C * k) := by ring
    _ ≤ O * (4 * C * k) := s3

/-- **Early arrival at positive density makes `𝒞_C` non-normal.** -/
theorem not_normal_of_earlyArrival (C : ℕ) (h : EarlyArrival C) :
    ¬ Normal (collatzChampernowne C) := by
  intro hN
  have hC := one_le_of_earlyArrival h
  obtain ⟨r, ρ, hr, hρ, hev⟩ := h
  have hCR : (0 : ℝ) < C := by exact_mod_cast hC
  set D : ℝ := (C : ℝ) - r with hD
  have hD0 : 0 < D := by rw [hD]; linarith
  set d : ℝ := ρ * D / (4 * C) with hd
  have hd0 : 0 < d := by positivity
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (half_pos hd0) (by norm_num : (1 / 2 : ℝ) < 1)
  have hm2 : (1 / 2 : ℝ) ^ (altWord m).length < d / 2 := by
    rw [length_altWord]
    refine lt_of_le_of_lt ?_ hm
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hPtop : Tendsto (fun k : ℕ => cum (champLen C) (2 ^ k - 1)) atTop atTop := by
    refine tendsto_atTop_mono (fun k => ?_) tendsto_id
    have h1 := le_cum (champLen C) (one_le_champLen C) (2 ^ k - 1)
    have h2 : k < 2 ^ k := Nat.lt_two_pow_self
    simp only [id]
    omega
  have hup := ((hN (altWord m)).comp hPtop).eventually (Iio_mem_nhds hm2)
  have hkbig : ∀ᶠ k : ℕ in atTop, 2 * (2 * (m : ℝ) + 2) / D ≤ (k : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  obtain ⟨k, ⟨⟨hcount, hupk⟩, hk1⟩, hkb⟩ :=
    (((hev.and hup).and (eventually_ge_atTop 1)).and hkbig).exists
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk1
  have hDk : 2 * (2 * (m : ℝ) + 2) ≤ D * k := by
    rw [div_le_iff₀ hD0] at hkb
    linarith
  have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hlow := density_lower C hC r ρ hρ m k hk1 hcount (by rw [← hD]; linarith)
  rw [← hD] at hlow
  have hhalf : d / 2 ≤ ρ * (D * k - 2 * m - 2) / (4 * C * k) := by
    have : d / 2 = ρ * D / (8 * C) := by rw [hd]; field_simp; ring
    rw [this, div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : (ρ * (4 * C)) * (D * k) ≤ (ρ * (4 * C)) * (2 * (D * k - 2 * m - 2)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  have hupk' : (occ (collatzChampernowne C) (altWord m) (cum (champLen C) (2 ^ k - 1)) : ℝ) /
      (cum (champLen C) (2 ^ k - 1) : ℝ) < d / 2 := hupk
  linarith

theorem champernowneNotNormalAboveThreshold_of_earlyArrival
    (h : ∀ C, 5 ≤ C → EarlyArrival C) : ChampernowneNotNormalAboveThreshold :=
  fun C hC => not_normal_of_earlyArrival C (h C hC)

end CollatzMoonshot.Conjugacy
