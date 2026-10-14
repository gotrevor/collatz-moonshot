/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalNearCycleRuns
import CollatzMoonshot.AmusicalNearCycleEntropy.Prefixes

/-!
# Branch words and residue classes (helpers for RT-low)

`key ℓ x` is the branch word of the first `ℓ` steps of `U` from `x`: `0` for `E`, `1` for
`x ≡ 1`, `3` for `x ≡ 3 (mod 4)`.  Its weight `wt` (`1` per `E`, `2` per odd step) is the number
of bits consumed: two starts with the same branch word agree mod `2^wt` (`key_dvd`), so at most
`N / 2^wt + 1` of them lie in `[0, N]`.  `lifts s` lists the `2^{#O}` branch words over an `E`/`O`
pattern `s`; their masses `2^{−wt}` sum to `2^{−|s|}`.
-/

namespace CollatzMoonshot.Amusical.NearCycleEntropy

open Finset

/-- The branch of `U` at `x`. -/
def bcls (x : ℤ) : ℕ := if Even x then 0 else if x % 4 = 1 then 1 else 3

/-- The branch word of the first `ℓ` steps. -/
def key : ℕ → ℤ → List ℕ
  | 0, _ => []
  | ℓ + 1, x => bcls x :: key ℓ (amusical x)

/-- The bits consumed by a branch word. -/
def wt : List ℕ → ℕ
  | [] => 0
  | c :: k => wt k + if c = 0 then 1 else 2

/-- The `E`/`O` pattern of the first `ℓ` steps (`true` = `E`). -/
def pat (ℓ : ℕ) (x : ℤ) : List Bool := (key ℓ x).map fun c => decide (c = 0)

/-- The branch words over an `E`/`O` pattern. -/
def lifts : List Bool → Finset (List ℕ)
  | [] => {[]}
  | true :: s => (lifts s).image (0 :: ·)
  | false :: s => (lifts s).image (1 :: ·) ∪ (lifts s).image (3 :: ·)

theorem bcls_eq_zero {x : ℤ} : bcls x = 0 ↔ Even x := by
  unfold bcls; split_ifs <;> simp_all

theorem length_key (ℓ : ℕ) (x : ℤ) : (key ℓ x).length = ℓ := by
  induction ℓ generalizing x with
  | zero => rfl
  | succ ℓ ih => simp [key, ih]

theorem key_succ' (ℓ : ℕ) (x : ℤ) :
    key (ℓ + 1) x = key ℓ x ++ [bcls (amusical^[ℓ] x)] := by
  induction ℓ generalizing x with
  | zero => rfl
  | succ ℓ ih =>
    rw [key, ih, key, Function.iterate_succ_apply]; rfl

theorem pat_succ' (ℓ : ℕ) (x : ℤ) :
    pat (ℓ + 1) x = pat ℓ x ++ [decide (Even (amusical^[ℓ] x))] := by
  simp [pat, key_succ', bcls_eq_zero]

theorem pat_succ (ℓ : ℕ) (x : ℤ) :
    pat (ℓ + 1) x = decide (Even x) :: pat ℓ (amusical x) := by
  simp [pat, key, bcls_eq_zero]

theorem length_pat (ℓ : ℕ) (x : ℤ) : (pat ℓ x).length = ℓ := by
  simp [pat, length_key]

theorem key_mem_lifts (ℓ : ℕ) (x : ℤ) : key ℓ x ∈ lifts (pat ℓ x) := by
  induction ℓ generalizing x with
  | zero => simp [key, pat, lifts]
  | succ ℓ ih =>
    rw [pat_succ, key]
    by_cases he : Even x
    · rw [decide_eq_true he, lifts, (bcls_eq_zero.mpr he)]
      exact mem_image_of_mem _ (ih _)
    · rw [decide_eq_false he, lifts, mem_union]
      unfold bcls
      rw [if_neg he]
      split_ifs
      · exact Or.inl (mem_image_of_mem _ (ih _))
      · exact Or.inr (mem_image_of_mem _ (ih _))

theorem wt_of_mem_lifts {s : List Bool} {k : List ℕ} (hk : k ∈ lifts s) :
    wt k = s.count true + 2 * s.count false := by
  induction s generalizing k with
  | nil => simp [lifts] at hk; subst hk; rfl
  | cons b s ih =>
    cases b with
    | true =>
      simp only [lifts, mem_image] at hk
      obtain ⟨k', hk', rfl⟩ := hk
      simp [wt, ih hk']; ring
    | false =>
      simp only [lifts, mem_union, mem_image] at hk
      rcases hk with ⟨k', hk', rfl⟩ | ⟨k', hk', rfl⟩ <;> simp [wt, ih hk'] <;> ring

theorem length_of_mem_lifts {s : List Bool} {k : List ℕ} (hk : k ∈ lifts s) :
    k.length = s.length := by
  induction s generalizing k with
  | nil => simp [lifts] at hk; subst hk; rfl
  | cons b s ih =>
    cases b with
    | true =>
      simp only [lifts, mem_image] at hk
      obtain ⟨k', hk', rfl⟩ := hk
      simp [ih hk']
    | false =>
      simp only [lifts, mem_union, mem_image] at hk
      rcases hk with ⟨k', hk', rfl⟩ | ⟨k', hk', rfl⟩ <;> simp [ih hk']

theorem card_lifts_le (s : List Bool) : (lifts s).card ≤ 2 ^ s.count false := by
  induction s with
  | nil => simp [lifts]
  | cons b s ih =>
    cases b with
    | true => simpa [lifts] using card_image_le.trans ih
    | false =>
      simp only [lifts, List.count_cons_self, pow_succ]
      refine (card_union_le _ _).trans ?_
      have := (card_image_le (s := lifts s) (f := (1 :: ·))).trans ih
      have := (card_image_le (s := lifts s) (f := (3 :: ·))).trans ih
      omega

theorem sum_lifts_le (s : List Bool) :
    ∑ k ∈ lifts s, ((1 : ℝ) / 2) ^ wt k ≤ ((1 : ℝ) / 2) ^ s.length := by
  induction s with
  | nil => simp [lifts, wt]
  | cons b s ih =>
    cases b with
    | true =>
      rw [lifts, sum_image (fun _ _ _ _ h => List.cons_injective h)]
      simp only [wt, if_true, pow_succ, List.length_cons]
      rw [← sum_mul]
      exact mul_le_mul_of_nonneg_right ih (by norm_num)
    | false =>
      rw [lifts]
      have hU := sum_union_inter (f := fun k : List ℕ => ((1 : ℝ) / 2) ^ wt k)
        (s₁ := (lifts s).image (1 :: ·)) (s₂ := (lifts s).image (3 :: ·))
      have h0 : (0 : ℝ) ≤ ∑ k ∈ (lifts s).image (1 :: ·) ∩ (lifts s).image (3 :: ·),
          ((1 : ℝ) / 2) ^ wt k := sum_nonneg fun _ _ => by positivity
      rw [sum_image (fun _ _ _ _ h => List.cons_injective h),
        sum_image (fun _ _ _ _ h => List.cons_injective h)] at hU
      simp only [wt, show (1 : ℕ) ≠ 0 by norm_num, show (3 : ℕ) ≠ 0 by norm_num, if_false,
        pow_add, ← sum_mul] at hU
      simp only [List.length_cons, pow_succ]
      nlinarith

theorem two_pow_dvd_of_three_mul {n : ℕ} {z : ℤ} (h : (2 : ℤ) ^ n ∣ 3 * z) : (2 : ℤ) ^ n ∣ z :=
  (IsCoprime.pow_left (⟨-1, 1, by norm_num⟩ : IsCoprime (2 : ℤ) 3)).dvd_of_dvd_mul_left h

theorem four_mul_amusical_odd {x : ℤ} (hx : ¬ Even x) :
    4 * amusical x = 3 * x + if bcls x = 1 then 1 else -1 := by
  have h2 : x % 2 = 1 := Int.not_even_iff.mp hx
  unfold amusical bcls
  simp only [Int.even_iff]
  split_ifs <;> omega

/-- **Same branch word, same residue class.** -/
theorem key_dvd (ℓ : ℕ) (x y : ℤ) (h : key ℓ x = key ℓ y) :
    (2 : ℤ) ^ wt (key ℓ x) ∣ x - y := by
  induction ℓ generalizing x y with
  | zero => simp [key, wt]
  | succ ℓ ih =>
    simp only [key, List.cons.injEq] at h
    obtain ⟨hb, hk⟩ := h
    obtain ⟨c, hc⟩ := ih _ _ hk
    simp only [key, wt]
    apply two_pow_dvd_of_three_mul
    by_cases hx : Even x
    · have hy : Even y := bcls_eq_zero.mp (hb ▸ bcls_eq_zero.mpr hx)
      rw [if_pos (bcls_eq_zero.mpr hx)]
      have h1 := NearCycleRuns.two_mul_amusical_of_even hx
      have h2 := NearCycleRuns.two_mul_amusical_of_even hy
      exact ⟨c, by rw [pow_succ]; linear_combination 2 * hc - h1 + h2⟩
    · have hy : ¬ Even y := fun hy => hx (bcls_eq_zero.mp (hb ▸ bcls_eq_zero.mpr hy))
      have hx0 : bcls x ≠ 0 := fun h => hx (bcls_eq_zero.mp h)
      rw [if_neg hx0]
      have h1 := four_mul_amusical_odd hx
      have h2 := four_mul_amusical_odd hy
      rw [← hb] at h2
      refine ⟨c, ?_⟩
      rw [pow_add]
      split_ifs at h1 h2 <;> linear_combination 4 * hc - h1 + h2

/-- **The fiber count.**  At most `N / 2^wt + 1` starts in `[0, N]` follow a given branch word. -/
theorem card_fiber_le (N : ℕ) (k : List ℕ) :
    ((range (N + 1)).filter fun p : ℕ => key k.length (p : ℤ) = k).card ≤
      N / 2 ^ wt k + 1 := by
  set q := 2 ^ wt k with hq
  have hq0 : 0 < q := by positivity
  rw [← card_range (N / q + 1)]
  refine card_le_card_of_injOn (fun p => p / q) (fun p hp => ?_) (fun p hp p' hp' h => ?_)
  · simp only [coe_filter, Set.mem_ofPred_eq, mem_range] at hp
    simp only [coe_range, Set.mem_Iio]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))
  · simp only [coe_filter, Set.mem_ofPred_eq] at hp hp'
    have hd := key_dvd _ _ _ (hp.2.trans hp'.2.symm)
    rw [hp.2] at hd
    have hmod : p' ≡ p [MOD q] := by
      rw [Nat.modEq_iff_dvd]; push_cast [hq]; exact hd
    simp only at h
    rw [← Nat.div_add_mod p q, ← Nat.div_add_mod p' q, h, hmod]

theorem runs_append_false (l : List Bool) : runs (l ++ [false]) = runs l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => cases a <;> rfl
    | cons b l => simp only [List.cons_append, runs] at ih ⊢; rw [ih]; simp

theorem runs_append_true (l : List Bool) :
    runs (l ++ [true]) = runs l + if l.getLast? = some true then 0 else 1 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => cases a <;> rfl
    | cons b l =>
      have ih' : runs (b :: (l ++ [true])) = runs (b :: l) +
          if (b :: l).getLast? = some true then 0 else 1 := ih
      change runs (a :: b :: (l ++ [true])) = _
      rw [show runs (a :: b :: (l ++ [true])) = runs (b :: (l ++ [true])) +
          (if a = true ∧ some b ≠ some true then 1 else 0) from rfl, ih',
        show runs (a :: b :: l) = runs (b :: l) +
          (if a = true ∧ some b ≠ some true then 1 else 0) from rfl, List.getLast?_cons_cons]
      omega

theorem count_true_pat (ℓ : ℕ) (x : ℤ) :
    (pat ℓ x).count true = NearCycleRuns.cntE (fun i => amusical^[i] x) ℓ := by
  induction ℓ with
  | zero => simp [pat, key, NearCycleRuns.cntE]
  | succ ℓ ih =>
    rw [pat_succ', List.count_append, ih, NearCycleRuns.cntE_succ]
    by_cases h : Even (amusical^[ℓ] x) <;> simp [h]

theorem count_false_pat (ℓ : ℕ) (x : ℤ) :
    (pat ℓ x).count false = ℓ - NearCycleRuns.cntE (fun i => amusical^[i] x) ℓ := by
  have := List.count_true_add_count_false (pat ℓ x)
  rw [length_pat, count_true_pat] at this
  omega

theorem head?_pat (ℓ : ℕ) (x : ℤ) : (pat (ℓ + 1) x).head? = some (decide (Even x)) := by
  rw [pat_succ]; rfl

theorem getLast?_pat (ℓ : ℕ) (x : ℤ) :
    (pat (ℓ + 1) x).getLast? = some (decide (Even (amusical^[ℓ] x))) := by
  rw [pat_succ']; simp

theorem runs_pat (ℓ : ℕ) (x : ℤ) :
    runs (pat (ℓ + 1) x) = NearCycleRuns.cntR (fun i => amusical^[i] x) (ℓ + 1) := by
  induction ℓ with
  | zero =>
    rw [NearCycleRuns.cntR_one]
    by_cases h : Even x <;> simp [pat, key, bcls_eq_zero, h, runs]
  | succ ℓ ih =>
    rw [NearCycleRuns.cntR_succ, ← ih, pat_succ' (ℓ + 1)]
    by_cases h : Even (amusical^[ℓ + 1] x)
    · rw [decide_eq_true h, runs_append_true, getLast?_pat]
      by_cases h' : Even (amusical^[ℓ] x)
      · rw [if_pos (by simp [h']), if_neg (fun hh => (Int.not_odd_iff_even.mpr h') hh.2)]
      · rw [if_neg (by simp [h']), if_pos ⟨h, Int.not_even_iff_odd.mp h'⟩]
    · rw [decide_eq_false h, runs_append_false, if_neg (fun hh => h hh.1), add_zero]

end CollatzMoonshot.Amusical.NearCycleEntropy
