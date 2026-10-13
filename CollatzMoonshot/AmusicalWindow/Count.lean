/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Elementary density lemmas for periodic predicates

This module packages the counting-and-squeeze argument used by window-minimum densities.  A
predicate with a fixed count on every block of length `M` has density `c / M`; changing finitely
many values does not change that density.
-/

open Filter

namespace CollatzMoonshot.Amusical

/-- Filtering the first `t` members of `Fin L` is the same count as filtering `range t`. -/
theorem card_filter_fin_lt_eq_count (L t : ℕ) (ht : t ≤ L) (P : ℕ → Prop)
    [DecidablePred P] :
    (Finset.univ.filter fun i : Fin L => i.val < t ∧ P i.val).card = Nat.count P t := by
  rw [Nat.count_eq_card_filter_range]
  apply Finset.card_bij (fun i _ => i.val)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp [hi]
  · intro i _ j _ hij
    exact Fin.ext hij
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    let i : Fin L := ⟨n, lt_of_lt_of_le hn.1 ht⟩
    refine ⟨i, ?_, rfl⟩
    simp [i, hn]

/-- A predicate and its complement partition every initial interval. -/
theorem count_not_add_count (P : ℕ → Prop) [DecidablePred P] (t : ℕ) :
    Nat.count (fun n => ¬P n) t + Nat.count P t = t := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Nat.count_succ, Nat.count_succ]
      by_cases h : P t <;> simp [h] <;> omega

/-- Consecutive blocks of a periodic predicate all have the same cardinality. -/
theorem count_block_eq_of_add_periodic (P : ℕ → Prop) [DecidablePred P]
    {M : ℕ} (hper : ∀ n : ℕ, P (n + M) ↔ P n) (a : ℕ) :
    Nat.count (fun k => P (a + k)) M = Nat.count P M := by
  induction a with
  | zero => simp
  | succ a ih =>
      let Q : ℕ → Prop := fun k => P (a + k)
      have hs := Nat.count_succ Q M
      have hs' := Nat.count_succ' Q M
      have hp : Q M ↔ Q 0 := by simpa [Q, Nat.add_assoc] using hper a
      change Nat.count (fun k => P (a + 1 + k)) M = Nat.count P M
      rw [← ih]
      have heq : Nat.count (fun k => Q (k + 1)) M = Nat.count Q M := by
        by_cases h0 : Q 0 <;> by_cases hM : Q M <;>
          simp [h0, hM] at hp hs hs' ⊢ <;> omega
      convert heq using 1
      simp [Q, Nat.add_comm, Nat.add_left_comm]

/-- A fixed block count gives a uniform `O(M²)` discrepancy from its expected linear count. -/
theorem count_periodic_block_bound (P : ℕ → Prop) [DecidablePred P]
    {M c : ℕ} (hM : 0 < M)
    (hblock : ∀ a : ℕ, Nat.count (fun k => P (a + k)) M = c) (X : ℕ) :
    M * Nat.count P X ≤ c * X + M * M ∧
      c * X ≤ M * Nat.count P X + M * M := by
  have hc : c ≤ M := by
    rw [← hblock 0]
    exact Nat.count_le _
  induction X using Nat.strong_induction_on with
  | _ X ih =>
      by_cases hX : X < M
      · have hcount : Nat.count P X ≤ X := Nat.count_le _
        constructor <;> nlinarith
      · have hXM : X - M < X := by omega
        have hadd : Nat.count P X = Nat.count P (X - M) + c := by
          calc
            Nat.count P X = Nat.count P ((X - M) + M) := by
              rw [Nat.sub_add_cancel (by omega)]
            _ = Nat.count P (X - M) + Nat.count (fun k => P (X - M + k)) M :=
              Nat.count_add P (X - M) M
            _ = Nat.count P (X - M) + c := by rw [hblock]
        have hcX : c * X = c * (X - M) + c * M := by
          calc
            c * X = c * ((X - M) + M) := by rw [Nat.sub_add_cancel (by omega)]
            _ = c * (X - M) + c * M := Nat.mul_add _ _ _
        have hprev := ih (X - M) hXM
        rw [hadd, hcX]
        simp only [Nat.mul_add]
        rw [Nat.mul_comm M c]
        constructor <;> omega

/-- A predicate containing exactly `c` points in every block of length `M` has natural density
`c / M`. -/
theorem tendsto_count_div_of_periodic_blocks (P : ℕ → Prop) [DecidablePred P]
    {M c : ℕ} (hM : 0 < M)
    (hblock : ∀ a : ℕ, Nat.count (fun k => P (a + k)) M = c) :
    Tendsto (fun X : ℕ => (Nat.count P X : ℝ) / X) atTop
      (nhds ((c : ℝ) / M)) := by
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hlo : Tendsto (fun X : ℕ => (c : ℝ) / M - M / X) atTop
      (nhds ((c : ℝ) / M)) := by
    simpa using tendsto_const_nhds.sub
      (tendsto_const_div_atTop_nhds_zero_nat (M : ℝ))
  have hhi : Tendsto (fun X : ℕ => (c : ℝ) / M + M / X) atTop
      (nhds ((c : ℝ) / M)) := by
    simpa using tendsto_const_nhds.add
      (tendsto_const_div_atTop_nhds_zero_nat (M : ℝ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with X hX
    have hXreal : (0 : ℝ) < X := by exact_mod_cast hX
    have hb : (c : ℝ) * X ≤ M * Nat.count P X + M * M := by
      exact_mod_cast (count_periodic_block_bound P hM hblock X).2
    field_simp [ne_of_gt hMreal, ne_of_gt hXreal]
    nlinarith
  · filter_upwards [eventually_ge_atTop 1] with X hX
    have hXreal : (0 : ℝ) < X := by exact_mod_cast hX
    have hb : (M : ℝ) * Nat.count P X ≤ c * X + M * M := by
      exact_mod_cast (count_periodic_block_bound P hM hblock X).1
    field_simp [ne_of_gt hMreal, ne_of_gt hXreal]
    nlinarith

/-- Counts of predicates which agree past `A` differ by at most `A`. -/
theorem count_eventually_congr_bound (P Q : ℕ → Prop) [DecidablePred P]
    [DecidablePred Q] {A : ℕ} (hPQ : ∀ n : ℕ, A ≤ n → (P n ↔ Q n)) (X : ℕ) :
    Nat.count P X ≤ Nat.count Q X + A ∧ Nat.count Q X ≤ Nat.count P X + A := by
  induction X with
  | zero => simp
  | succ X ih =>
      by_cases hXA : A ≤ X
      · rw [Nat.count_succ, Nat.count_succ]
        have h := hPQ X hXA
        by_cases hP : P X <;> by_cases hQ : Q X <;> simp [hP, hQ] at h ⊢ <;> omega
      · have hX : X < A := by omega
        have hp : Nat.count P (X + 1) ≤ X + 1 := Nat.count_le _
        have hq : Nat.count Q (X + 1) ≤ X + 1 := Nat.count_le _
        constructor <;> omega

/-- Altering finitely many values of a predicate does not change its natural density. -/
theorem tendsto_count_div_of_eventually_congr (P Q : ℕ → Prop) [DecidablePred P]
    [DecidablePred Q] {A : ℕ} (hPQ : ∀ n : ℕ, A ≤ n → (P n ↔ Q n)) {d : ℝ}
    (hQ : Tendsto (fun X : ℕ => (Nat.count Q X : ℝ) / X) atTop (nhds d)) :
    Tendsto (fun X : ℕ => (Nat.count P X : ℝ) / X) atTop (nhds d) := by
  have hzero : Tendsto (fun X : ℕ => (A : ℝ) / X) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (A : ℝ)
  have hlo : Tendsto (fun X : ℕ => (Nat.count Q X : ℝ) / X - A / X) atTop (nhds d) := by
    simpa using hQ.sub hzero
  have hhi : Tendsto (fun X : ℕ => (Nat.count Q X : ℝ) / X + A / X) atTop (nhds d) := by
    simpa using hQ.add hzero
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with X hX
    have hXreal : (0 : ℝ) < X := by exact_mod_cast hX
    have hb : (Nat.count Q X : ℝ) ≤ Nat.count P X + A := by
      exact_mod_cast (count_eventually_congr_bound P Q hPQ X).2
    rw [div_sub_div_same, div_le_div_iff_of_pos_right hXreal]
    linarith
  · filter_upwards [eventually_ge_atTop 1] with X hX
    have hXreal : (0 : ℝ) < X := by exact_mod_cast hX
    have hb : (Nat.count P X : ℝ) ≤ Nat.count Q X + A := by
      exact_mod_cast (count_eventually_congr_bound P Q hPQ X).1
    rw [← add_div, div_le_div_iff_of_pos_right hXreal]
    linarith

namespace WindowCount

open Finset

/-- Counting a periodic predicate along a map which is injective modulo `N` on `[0, N)` gives
the count over one period. -/
theorem count_comp_of_injMod (N : ℕ) (hN : 0 < N) (g : ℤ → Prop) [DecidablePred g]
    (hg : ∀ x, g x ↔ g (x % N)) (φ : ℕ → ℤ)
    (hφ : ∀ a < N, ∀ b < N, φ a % N = φ b % N → a = b) :
    Nat.count (fun m => g (φ m)) N = Nat.count (fun x : ℕ => g x) N := by
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  have hNz : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  let i : ℕ → ℕ := fun m => (φ m % N).toNat
  have hi_cast : ∀ m, ((i m : ℕ) : ℤ) = φ m % N := fun m =>
    Int.toNat_of_nonneg (Int.emod_nonneg _ hNz)
  have hi_lt : ∀ m, i m < N := fun m => by
    have := Int.emod_lt_of_pos (φ m) (by exact_mod_cast hN : (0 : ℤ) < N)
    have h2 := hi_cast m
    omega
  have hinj : ∀ a ∈ range N, ∀ b ∈ range N, i a = i b → a = b := by
    intro a ha b hb hab
    apply hφ a (mem_range.mp ha) b (mem_range.mp hb)
    rw [← hi_cast, ← hi_cast, hab]
  have hsurj : ∀ y ∈ range N, ∃ a, ∃ _ : a ∈ range N, y = i a :=
    Finset.surj_on_of_inj_on_of_card_le (fun a _ => i a)
      (fun a _ => mem_range.mpr (hi_lt a)) (fun a b ha hb h => hinj a ha b hb h) le_rfl
  apply Finset.card_bij (fun a _ => i a)
  · intro a ha
    rw [mem_filter] at ha ⊢
    refine ⟨mem_range.mpr (hi_lt a), ?_⟩
    rw [hi_cast]
    exact (hg _).mp ha.2
  · intro a ha b hb h
    exact hinj a (mem_filter.mp ha).1 b (mem_filter.mp hb).1 h
  · intro y hy
    rw [mem_filter] at hy
    obtain ⟨a, ha, hay⟩ := hsurj y hy.1
    subst hay
    refine ⟨a, ?_, rfl⟩
    rw [mem_filter]
    refine ⟨ha, ?_⟩
    rw [hg, ← hi_cast]
    exact hy.2

/-- Splitting `[0, 4N)` into evens, `1 mod 4` and `3 mod 4`. -/
theorem count_four_mul_decomp (P : ℕ → Prop) [DecidablePred P] (N : ℕ) :
    Nat.count P (4 * N) = Nat.count (fun m => P (2 * m)) (2 * N) +
      Nat.count (fun m => P (4 * m + 1)) N + Nat.count (fun m => P (4 * m + 3)) N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 4 * (N + 1) = 4 * N + 1 + 1 + 1 + 1 by ring,
      show 2 * (N + 1) = 2 * N + 1 + 1 by ring]
    simp only [Nat.count_succ, ih]
    rw [show 2 * (2 * N) = 4 * N by ring, show 2 * (2 * N + 1) = 4 * N + 1 + 1 by ring]
    ring

/-- Splitting `[0, 3N)` into the three residue classes modulo `3`. -/
theorem count_three_mul_decomp (P : ℕ → Prop) [DecidablePred P] (N : ℕ) :
    Nat.count P (3 * N) = Nat.count (fun m => P (3 * m)) N +
      Nat.count (fun m => P (3 * m + 1)) N + Nat.count (fun m => P (3 * m + 2)) N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 3 * (N + 1) = 3 * N + 1 + 1 + 1 by ring]
    simp only [Nat.count_succ, ih]
    rw [show 3 * N + 1 + 1 = 3 * N + 2 by ring]
    ring

/-- The two-modulus Chinese remainder count. -/
theorem count_crt (A B : ℕ) (hAB : Nat.Coprime A B) (F G : ℕ → Prop) [DecidablePred F]
    [DecidablePred G] :
    Nat.count (fun c => F (c % A) ∧ G (c % B)) (A * B) =
      Nat.count F A * Nat.count G B := by
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range,
    Nat.count_eq_card_filter_range, ← Finset.card_product, ← Finset.filter_product]
  rcases Nat.eq_zero_or_pos A with hA0 | hA0
  · subst hA0
    simp
  rcases Nat.eq_zero_or_pos B with hB0 | hB0
  · subst hB0
    simp
  let i : ℕ → ℕ × ℕ := fun c => (c % A, c % B)
  have hinj : ∀ a ∈ range (A * B), ∀ b ∈ range (A * B), i a = i b → a = b := by
    intro a ha b hb h
    simp only [i, Prod.mk.injEq] at h
    have h1 : a ≡ b [MOD A * B] := (Nat.modEq_and_modEq_iff_modEq_mul hAB).mp ⟨h.1, h.2⟩
    rw [Nat.ModEq, Nat.mod_eq_of_lt (mem_range.mp ha), Nat.mod_eq_of_lt (mem_range.mp hb)] at h1
    exact h1
  have hmaps : ∀ a ∈ range (A * B), i a ∈ range A ×ˢ range B := fun a _ =>
    mem_product.mpr ⟨mem_range.mpr (Nat.mod_lt _ hA0), mem_range.mpr (Nat.mod_lt _ hB0)⟩
  have hsurj : ∀ y ∈ range A ×ˢ range B, ∃ a, ∃ _ : a ∈ range (A * B), y = i a :=
    Finset.surj_on_of_inj_on_of_card_le (fun a _ => i a) hmaps
      (fun a b ha hb h => hinj a ha b hb h) (by simp)
  apply Finset.card_bij (fun a _ => i a)
  · intro a ha
    rw [mem_filter] at ha ⊢
    exact ⟨hmaps a ha.1, ha.2⟩
  · intro a ha b hb h
    exact hinj a (mem_filter.mp ha).1 b (mem_filter.mp hb).1 h
  · intro y hy
    rw [mem_filter] at hy
    obtain ⟨a, ha, hay⟩ := hsurj y hy.1
    subst hay
    refine ⟨a, ?_, rfl⟩
    rw [mem_filter]
    exact ⟨ha, hy.2⟩

/-- A periodic predicate has exactly `k` periods' worth of members in `[0, M k)`. -/
theorem count_periodic_mul (P : ℕ → Prop) [DecidablePred P] (M : ℕ)
    (hP : ∀ n, P n ↔ P (n % M)) (k : ℕ) :
    Nat.count P (M * k) = k * Nat.count P M := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Nat.count_add, ih]
    have hblock : Nat.count (fun j => P (M * k + j)) M = Nat.count P M := by
      rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
      congr 1
      apply Finset.filter_congr
      intro j _
      rw [hP (M * k + j), hP j, Nat.mul_add_mod]
    rw [hblock]
    ring

/-- Bounds on the count of a periodic predicate on `[0, X)`. -/
theorem count_periodic_bounds (P : ℕ → Prop) [DecidablePred P] (M : ℕ) (hM : 0 < M)
    (hP : ∀ n, P n ↔ P (n % M)) (X : ℕ) :
    (X / M) * Nat.count P M ≤ Nat.count P X ∧
      Nat.count P X ≤ (X / M + 1) * Nat.count P M := by
  constructor
  · rw [← count_periodic_mul P M hP]
    exact Nat.count_monotone P (Nat.mul_div_le X M)
  · rw [← count_periodic_mul P M hP]
    apply Nat.count_monotone P
    have := Nat.lt_mul_div_succ X hM
    omega

end WindowCount

end CollatzMoonshot.Amusical
