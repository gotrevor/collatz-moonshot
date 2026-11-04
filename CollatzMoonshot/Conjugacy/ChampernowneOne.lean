/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.Champernowne

/-!
# `𝒞_1` is normal

Fix a word `u` of length `L`.  The proof counts occurrences **by offset**, not by stage.

* **One period** (`card_windowMatch`).  Among `r < 2^(t+L)`, exactly `2^t` have letters
  `t, …, t+L−1` reading `u`: Terras's flip `accWord_add_two_pow`, by induction on `L`.
* **Any interval** (`abs_card_Ico_windowMatch_sub_le`).  The window is periodic in `n` with period
  `2^(t+L)` (`windowMatch_periodic`), so over *any* `m` consecutive integers the count is
  `m / 2^L` up to `2^t`.  No alignment is needed, so no dyadic cut of a partial stage.
* **All offsets** (`abs_interior_sub_main_le`).  For offset `t`, the integers `n ≤ N` whose word
  holds the window are the interval `[2^(t+L−1), N]`.  The errors sum to `∑ 2^t ≤ 2N` over
  `t < size N`.
* **The rest** (`occ_cum_le`, `abs_main_sub_cum_le`).  At most `L` positions per word straddle a
  boundary.

So `|occ (cum N) − cum N / 2^L| ≤ (2L + 2) N` (`abs_occ_cum_sub_le`), while `cum N / N → ∞`.  The
last letter of a word needs no separate treatment: its window is the offset `t = size n − L`.

The two bounds were checked exactly on `n < 2^15` before this file was written
(`|count − m/2^L| / 2^t` reached `0.938`, so that bound has little slack).
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord

/-- Letters `t, …, t + L − 1` of the parity word of `n` read `g 0, …, g (L − 1)`. -/
def WindowMatch (g : ℕ → Bool) (L t n : ℕ) : Prop := ∀ s < L, accWord n (t + s) = g s

instance (g : ℕ → Bool) (L t : ℕ) : DecidablePred (WindowMatch g L t) := fun n => by
  unfold WindowMatch; infer_instance

/-! ## One period, and any interval -/

/-- Letter `j` does not see adding `2^k` when `j < k`. -/
private theorem accWord_add_two_pow_of_lt' {j k : ℕ} (h : j < k) (r : ℕ) :
    accWord (r + 2 ^ k) j = accWord r j := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt h
  rw [show 2 ^ (j + c + 1) = 2 ^ c * 2 ^ (j + 1) by ring]
  exact accWord_add_mul_two_pow_succ r _ j

/-- The window does not see adding its period. -/
private theorem windowMatch_add_iff (g : ℕ → Bool) (L t r : ℕ) :
    WindowMatch g L t (r + 2 ^ (t + L)) ↔ WindowMatch g L t r :=
  forall₂_congr fun s hs => by rw [accWord_add_two_pow_of_lt' (by omega) r]

/-- A window of length `L + 1` is a window of length `L` and one more letter. -/
private theorem windowMatch_succ_iff (g : ℕ → Bool) (L t n : ℕ) :
    WindowMatch g (L + 1) t n ↔ WindowMatch g L t n ∧ accWord n (t + L) = g L := by
  constructor
  · exact fun h => ⟨fun s hs => h s (by omega), h L (by omega)⟩
  · rintro ⟨h, hl⟩ s hs
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | rfl
    · exact h s hs
    · exact hl

/-- **Terras, on a window.**  Exactly `2^t` of the `r < 2^(t+L)` have the prescribed letters at
`t, …, t + L − 1`. -/
theorem card_windowMatch (g : ℕ → Bool) (L t : ℕ) :
    ((Finset.range (2 ^ (t + L))).filter (WindowMatch g L t)).card = 2 ^ t := by
  induction L with
  | zero =>
    have : (Finset.range (2 ^ (t + 0))).filter (WindowMatch g 0 t) = Finset.range (2 ^ t) := by
      ext r
      simp [WindowMatch]
    rw [this, Finset.card_range]
  | succ L ih =>
    rw [← ih, show t + (L + 1) = t + L + 1 by ring, pow_succ, mul_two, Finset.card_filter,
      Finset.sum_range_add, ← Finset.sum_add_distrib, Finset.card_filter]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hr : WindowMatch g L t (2 ^ (t + L) + r) ↔ WindowMatch g L t r := by
      rw [add_comm]; exact windowMatch_add_iff g L t r
    have hlast : accWord (2 ^ (t + L) + r) (t + L) = !(accWord r (t + L)) := by
      rw [add_comm]; exact accWord_add_two_pow r (t + L)
    simp only [windowMatch_succ_iff, hr, hlast]
    by_cases h : WindowMatch g L t r <;> cases accWord r (t + L) <;> cases g L <;> simp [h]

/-- The window has period `2^(t+L)` in `n`. -/
theorem windowMatch_periodic (g : ℕ → Bool) (L t : ℕ) :
    Function.Periodic (WindowMatch g L t) (2 ^ (t + L)) := by
  intro r
  exact propext (windowMatch_add_iff g L t r)

/-- Interval counts add. -/
private theorem card_filter_Ico_add (P : ℕ → Prop) [DecidablePred P] (a b c : ℕ) :
    ((Finset.Ico a (a + b + c)).filter P).card =
      ((Finset.Ico a (a + b)).filter P).card + ((Finset.Ico (a + b) (a + b + c)).filter P).card := by
  rw [← Finset.Ico_union_Ico_eq_Ico (Nat.le_add_right a b) (Nat.le_add_right (a + b) c),
    Finset.filter_union, Finset.card_union_of_disjoint]
  exact Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive _ _ _)

/-- Every period window holds exactly `2^t` matches. -/
private theorem card_filter_Ico_period (g : ℕ → Bool) (L t a : ℕ) :
    ((Finset.Ico a (a + 2 ^ (t + L))).filter (WindowMatch g L t)).card = 2 ^ t := by
  rw [Nat.filter_Ico_card_eq_of_periodic a (2 ^ (t + L)) _ (windowMatch_periodic g L t),
    Nat.count_eq_card_filter_range, card_windowMatch]

/-- **Any interval.**  Over any `m` consecutive integers the window count is `m / 2^L` up to
`2^t`. -/
theorem abs_card_Ico_windowMatch_sub_le (g : ℕ → Bool) (L t a m : ℕ) :
    |(((Finset.Ico a (a + m)).filter (WindowMatch g L t)).card : ℝ) - (m : ℝ) / 2 ^ L| ≤
      2 ^ t := by
  set M := 2 ^ (t + L) with hM
  have hMpos : 0 < M := by positivity
  have hq : ∀ q a, ((Finset.Ico a (a + q * M)).filter (WindowMatch g L t)).card = q * 2 ^ t := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      intro a
      rw [show a + (q + 1) * M = a + q * M + M by ring, card_filter_Ico_add, ih,
        card_filter_Ico_period]
      ring
  have hdec : M * (m / M) + m % M = m := Nat.div_add_mod m M
  set q := m / M
  set r := m % M
  have hr : r < M := Nat.mod_lt _ hMpos
  have hsplit : a + m = a + q * M + r := by rw [← hdec]; ring
  have hcount : ((Finset.Ico a (a + m)).filter (WindowMatch g L t)).card =
      q * 2 ^ t + ((Finset.Ico (a + q * M) (a + q * M + r)).filter (WindowMatch g L t)).card := by
    rw [hsplit, card_filter_Ico_add, hq]
  have hp : ((Finset.Ico (a + q * M) (a + q * M + r)).filter (WindowMatch g L t)).card ≤ 2 ^ t := by
    rw [← card_filter_Ico_period g L t (a + q * M)]
    exact Finset.card_le_card (Finset.filter_subset_filter _
      (Finset.Ico_subset_Ico le_rfl (by omega)))
  set p := ((Finset.Ico (a + q * M) (a + q * M + r)).filter (WindowMatch g L t)).card
  have hpR : (p : ℝ) ≤ 2 ^ t := by exact_mod_cast hp
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  have h2L : (0 : ℝ) < 2 ^ L := by positivity
  have hMR : (M : ℝ) = 2 ^ t * 2 ^ L := by rw [hM]; push_cast; rw [pow_add]
  have hmR : (m : ℝ) = M * q + r := by exact_mod_cast hdec.symm
  have hrR : (r : ℝ) ≤ M := by exact_mod_cast hr.le
  have hmdiv : (m : ℝ) / 2 ^ L = q * 2 ^ t + r / 2 ^ L := by
    rw [hmR, hMR]; field_simp
  have hr0 : (0 : ℝ) ≤ r / 2 ^ L := by positivity
  have hr1 : (r : ℝ) / 2 ^ L ≤ 2 ^ t := by
    rw [div_le_iff₀ h2L, ← hMR]; exact hrR
  rw [hcount, hmdiv]
  push_cast
  rw [abs_le]
  constructor <;> linarith

/-! ## Reading occurrences in `𝒞_1` -/

/-- A window inside the word of `n + 1` is an occurrence in `𝒞_1`. -/
theorem occursAt_cum_iff (u : List Bool) (n i : ℕ) (hi : i + u.length ≤ Nat.size (n + 1)) :
    OccursAt (collatzChampernowne 1) u (cum (champLen 1) n + i) ↔
      WindowMatch (fun s => u.getD s false) u.length i (n + 1) := by
  have key : ∀ s, s < u.length →
      collatzChampernowne 1 (cum (champLen 1) n + i + s) = accWord (n + 1) (i + s) := by
    intro s hs
    rw [add_assoc]
    exact collatzChampernowne_apply 1 n (i + s) (by simp; omega)
  constructor
  · intro h s hs
    have := h ⟨s, hs⟩
    simp only at this
    rw [key s hs] at this
    rw [this]
    show u.get ⟨s, hs⟩ = u.getD s false
    rw [List.getD_eq_getElem _ _ hs]
    rfl
  · intro h j
    rw [key j j.isLt, h j j.isLt]
    show u.getD j false = u.get j
    rw [List.getD_eq_getElem _ _ j.isLt]
    rfl

/-- `occ` over `a + b` positions splits. -/
theorem occ_add (w : ℕ → Bool) (u : List Bool) (a b : ℕ) :
    occ w u (a + b) = occ w u a + ((Finset.range b).filter fun i => OccursAt w u (a + i)).card := by
  simp only [occ, Finset.card_filter, Finset.sum_range_add]

/-- The occurrences whose window lies inside a word of `n + 1 ≤ N`. -/
def interior (g : ℕ → Bool) (L N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range N, ((Finset.range (Nat.size (n + 1))).filter
    fun i => i + L ≤ Nat.size (n + 1) ∧ WindowMatch g L i (n + 1)).card

/-- The number of offsets whose window fits in the word of `n + 1 ≤ N`. -/
def windowCount (L N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range N, ((Finset.range (Nat.size (n + 1))).filter
    fun i => i + L ≤ Nat.size (n + 1)).card

/-- The occurrences starting in the word of `N + 1`, compared with its interior windows. -/
private theorem word_occ_bounds (u : List Bool) (N : ℕ) :
    ((Finset.range (Nat.size (N + 1))).filter fun i => i + u.length ≤ Nat.size (N + 1) ∧
        WindowMatch (fun s => u.getD s false) u.length i (N + 1)).card ≤
      ((Finset.range (Nat.size (N + 1))).filter fun i =>
        OccursAt (collatzChampernowne 1) u (cum (champLen 1) N + i)).card ∧
    ((Finset.range (Nat.size (N + 1))).filter fun i =>
        OccursAt (collatzChampernowne 1) u (cum (champLen 1) N + i)).card ≤
      ((Finset.range (Nat.size (N + 1))).filter fun i => i + u.length ≤ Nat.size (N + 1) ∧
        WindowMatch (fun s => u.getD s false) u.length i (N + 1)).card + u.length := by
  set z := Nat.size (N + 1) with hz
  constructor
  · refine Finset.card_le_card fun i hi => ?_
    simp only [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, (occursAt_cum_iff u N i hi.2.1).mpr hi.2.2⟩
  · have hsub : ((Finset.range z).filter fun i =>
        OccursAt (collatzChampernowne 1) u (cum (champLen 1) N + i)) ⊆
        ((Finset.range z).filter fun i => i + u.length ≤ z ∧
          WindowMatch (fun s => u.getD s false) u.length i (N + 1)) ∪
        Finset.Ico (z - u.length) z := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_Ico] at hi ⊢
      by_cases h : i + u.length ≤ z
      · exact Or.inl ⟨hi.1, h, (occursAt_cum_iff u N i h).mp hi.2⟩
      · exact Or.inr ⟨by omega, hi.1⟩
    refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
    rw [Nat.card_Ico]
    omega

/-- Interior windows are occurrences, and at most `L` positions per word straddle its end. -/
theorem occ_cum_le (u : List Bool) (N : ℕ) :
    interior (fun s => u.getD s false) u.length N ≤
        occ (collatzChampernowne 1) u (cum (champLen 1) N) ∧
      occ (collatzChampernowne 1) u (cum (champLen 1) N) ≤
        interior (fun s => u.getD s false) u.length N + u.length * N := by
  induction N with
  | zero => simp [interior, occ]
  | succ N ih =>
    have hb := word_occ_bounds u N
    rw [cum_succ, champLen_one, occ_add]
    have hi : interior (fun s => u.getD s false) u.length (N + 1) =
        interior (fun s => u.getD s false) u.length N +
        ((Finset.range (Nat.size (N + 1))).filter fun i =>
          i + u.length ≤ Nat.size (N + 1) ∧
            WindowMatch (fun s => u.getD s false) u.length i (N + 1)).card := by
      simp only [interior, Finset.sum_range_succ]
    rw [hi, mul_add, mul_one]
    constructor <;> omega

/-! ## Summing over offsets -/

/-- Swap a double count, the inner range being enlarged to a common `T`. -/
private theorem sum_card_filter_swap (N T : ℕ) (z : ℕ → ℕ) (hz : ∀ n < N, z n ≤ T)
    (Q : ℕ → ℕ → Prop) [∀ n i, Decidable (Q n i)] (hQ : ∀ n i, Q n i → i < z n) :
    ∑ n ∈ Finset.range N, ((Finset.range (z n)).filter (Q n)).card =
      ∑ t ∈ Finset.range T, ((Finset.range N).filter fun n => Q n t).card := by
  have h : ∀ n ∈ Finset.range N, ((Finset.range (z n)).filter (Q n)).card =
      ∑ t ∈ Finset.range T, if Q n t then 1 else 0 := by
    intro n hn
    rw [← Finset.card_filter]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    have := hz n (Finset.mem_range.mp hn)
    exact ⟨fun h => ⟨by omega, h.2⟩, fun h => ⟨hQ n i h.2, h.2⟩⟩
  rw [Finset.sum_congr rfl h, Finset.sum_comm]
  simp only [Finset.card_filter]

/-- For offset `t`, the `n < N` whose word holds the window are, shifted, an interval. -/
private theorem card_offset_eq (P : ℕ → Prop) [DecidablePred P] (L N t : ℕ) (hL : 1 ≤ L) :
    ((Finset.range N).filter fun n => t + L ≤ Nat.size (n + 1) ∧ P (n + 1)).card =
      ((Finset.Ico (2 ^ (t + L - 1)) (2 ^ (t + L - 1) + (N + 1 - 2 ^ (t + L - 1)))).filter P).card := by
  have hpos : 0 < 2 ^ (t + L - 1) := by positivity
  have hiff : ∀ n, t + L ≤ Nat.size (n + 1) ↔ 2 ^ (t + L - 1) ≤ n + 1 := fun n => by
    rw [← Nat.lt_size]
    omega
  refine Finset.card_bij (fun n _ => n + 1) ?_ (fun _ _ _ _ h => by omega) ?_
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hn ⊢
    have := (hiff n).mp hn.2.1
    exact ⟨⟨this, by omega⟩, hn.2.2⟩
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_Ico] at hb
    obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
    refine ⟨n, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, (hiff n).mpr hb.1.1, hb.2⟩

/-- Offset `t` contributes an error at most `2^t`. -/
private theorem offset_bound (g : ℕ → Bool) (L N t : ℕ) (hL : 1 ≤ L) :
    |(((Finset.range N).filter fun n => t + L ≤ Nat.size (n + 1) ∧
        WindowMatch g L t (n + 1)).card : ℝ) -
      (((Finset.range N).filter fun n => t + L ≤ Nat.size (n + 1)).card : ℝ) / 2 ^ L| ≤ 2 ^ t := by
  have hW : ((Finset.range N).filter fun n => t + L ≤ Nat.size (n + 1)).card =
      N + 1 - 2 ^ (t + L - 1) := by
    have := card_offset_eq (fun _ => True) L N t hL
    simpa using this
  rw [hW, card_offset_eq (WindowMatch g L t) L N t hL]
  exact abs_card_Ico_windowMatch_sub_le g L t _ _

/-- **All offsets.**  Swap the sums; offset `t` runs over the interval `[2^(t+L−1), N]`, with error
`2^t` (`abs_card_Ico_windowMatch_sub_le`), and `∑_{t < size N} 2^t ≤ 2N`. -/
theorem abs_interior_sub_main_le (g : ℕ → Bool) (L N : ℕ) (hL : 1 ≤ L) :
    |(interior g L N : ℝ) - (windowCount L N : ℝ) / 2 ^ L| ≤ 2 * N := by
  have hs : ∀ n < N, Nat.size (n + 1) ≤ Nat.size N := fun n hn => Nat.size_le_size hn
  have hI : interior g L N = ∑ t ∈ Finset.range (Nat.size N),
      ((Finset.range N).filter fun n => t + L ≤ Nat.size (n + 1) ∧ WindowMatch g L t (n + 1)).card :=
    sum_card_filter_swap N (Nat.size N) (fun n => Nat.size (n + 1)) hs
      (fun n i => i + L ≤ Nat.size (n + 1) ∧ WindowMatch g L i (n + 1))
      (fun n i h => by have := h.1; omega)
  have hW : windowCount L N = ∑ t ∈ Finset.range (Nat.size N),
      ((Finset.range N).filter fun n => t + L ≤ Nat.size (n + 1)).card :=
    sum_card_filter_swap N (Nat.size N) (fun n => Nat.size (n + 1)) hs
      (fun n i => i + L ≤ Nat.size (n + 1))
      (fun n i h => by omega)
  have hsum : ∀ T : ℕ, ∑ t ∈ Finset.range T, (2 : ℝ) ^ t + 1 = 2 ^ T := by
    intro T
    induction T with
    | zero => simp
    | succ T ih => rw [Finset.sum_range_succ, pow_succ]; linarith
  rw [hI, hW]
  push_cast
  rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun t _ => offset_bound g L N t hL).trans ?_
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have h1 : 1 ≤ Nat.size N := Nat.size_pos.mpr hN
    have h2 : 2 ^ (Nat.size N - 1) ≤ N := Nat.lt_size.mp (by omega)
    have h3 : (2 : ℝ) ^ Nat.size N ≤ 2 * N := by
      have h4 : (2 : ℝ) ^ Nat.size N = 2 * 2 ^ (Nat.size N - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      have h2' : (2 : ℝ) ^ (Nat.size N - 1) ≤ N := by exact_mod_cast h2
      linarith
    have := hsum (Nat.size N)
    linarith

/-- Each word loses at most `L` offsets to its end. -/
theorem abs_main_sub_cum_le (L N : ℕ) :
    |(windowCount L N : ℝ) / 2 ^ L - (cum (champLen 1) N : ℝ) / 2 ^ L| ≤ L * N := by
  have hb : windowCount L N ≤ cum (champLen 1) N ∧
      cum (champLen 1) N ≤ windowCount L N + L * N := by
    induction N with
    | zero => simp [windowCount]
    | succ N ih =>
      have hc : Nat.size (N + 1) - L ≤
          ((Finset.range (Nat.size (N + 1))).filter fun i => i + L ≤ Nat.size (N + 1)).card := by
        have : Finset.range (Nat.size (N + 1) - L) ⊆
            (Finset.range (Nat.size (N + 1))).filter fun i => i + L ≤ Nat.size (N + 1) := by
          intro i hi
          simp only [Finset.mem_range, Finset.mem_filter] at hi ⊢
          omega
        simpa using Finset.card_le_card this
      have hd : ((Finset.range (Nat.size (N + 1))).filter fun i =>
          i + L ≤ Nat.size (N + 1)).card ≤ Nat.size (N + 1) := by
        simpa using Finset.card_filter_le (Finset.range (Nat.size (N + 1)))
          (fun i => i + L ≤ Nat.size (N + 1))
      have hW : windowCount L (N + 1) = windowCount L N +
          ((Finset.range (Nat.size (N + 1))).filter fun i => i + L ≤ Nat.size (N + 1)).card := by
        simp only [windowCount, Finset.sum_range_succ]
      rw [hW, cum_succ, champLen_one, mul_add, mul_one]
      constructor <;> omega
  have h1 : (windowCount L N : ℝ) ≤ cum (champLen 1) N := by exact_mod_cast hb.1
  have h2 : (cum (champLen 1) N : ℝ) ≤ windowCount L N + L * N := by exact_mod_cast hb.2
  have h2L : (1 : ℝ) ≤ 2 ^ L := one_le_pow₀ (by norm_num)
  rw [← sub_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ L), div_le_iff₀ (by positivity)]
  have hLN : (0 : ℝ) ≤ L * N := by positivity
  have : |(windowCount L N : ℝ) - cum (champLen 1) N| ≤ L * N := by
    rw [abs_le]; constructor <;> linarith
  nlinarith

/-- **The discrepancy of `𝒞_1` at word ends.** -/
theorem abs_occ_cum_sub_le (u : List Bool) (hu : 1 ≤ u.length) (N : ℕ) :
    |(occ (collatzChampernowne 1) u (cum (champLen 1) N) : ℝ) -
        (cum (champLen 1) N : ℝ) / 2 ^ u.length| ≤ (2 * u.length + 2) * N := by
  obtain ⟨hl, hu'⟩ := occ_cum_le u N
  have h1 := abs_interior_sub_main_le (fun s => u.getD s false) u.length N hu
  have h3 := abs_main_sub_cum_le u.length N
  have hlR : (interior (fun s => u.getD s false) u.length N : ℝ) ≤
      occ (collatzChampernowne 1) u (cum (champLen 1) N) := by exact_mod_cast hl
  have huR : (occ (collatzChampernowne 1) u (cum (champLen 1) N) : ℝ) ≤
      interior (fun s => u.getD s false) u.length N + u.length * N := by exact_mod_cast hu'
  rw [abs_le] at h1 h3 ⊢
  have hLN : (0 : ℝ) ≤ u.length * N := by positivity
  constructor <;> nlinarith [h1.1, h1.2, h3.1, h3.2]

/-! ## Passing to every prefix -/

/-- Only `2^B` integers have fewer than `B` bits: `B N ≤ cum N + B 2^B`. -/
private theorem mul_le_cum_add (B N : ℕ) : B * N ≤ cum (champLen 1) N + B * 2 ^ B := by
  induction N with
  | zero => simp
  | succ N ih =>
    rcases Nat.lt_or_ge (2 ^ B) (N + 1) with h | h
    · have hsize : B ≤ Nat.size (N + 1) := (Nat.lt_size.mpr h.le).le
      rw [cum_succ, champLen_one, mul_add, mul_one]
      omega
    · have := Nat.mul_le_mul_left B h
      omega

/-- The word ends grow faster than the word count: `cum N ≥ B (N − 2^B)` for every `B`. -/
theorem tendsto_succ_div_cum :
    Tendsto (fun N : ℕ => ((N : ℝ) + 1) / (cum (champLen 1) N : ℝ)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨B, hB⟩ := exists_nat_gt (4 / ε)
  have hB' : 4 < ε * B := by rwa [div_lt_iff₀' hε] at hB
  refine ⟨2 ^ (B + 1) + 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (Nat.le_add_left 1 _) hN
  have hcpos : (0 : ℝ) < cum (champLen 1) N := by
    have := le_cum (champLen 1) (one_le_champLen 1) N
    exact_mod_cast (show 0 < cum (champLen 1) N by omega)
  have hmain : (B : ℝ) * N ≤ cum (champLen 1) N + B * 2 ^ B := by
    exact_mod_cast mul_le_cum_add B N
  have hpow : (2 : ℝ) * 2 ^ B ≤ N := by
    have : 2 * 2 ^ B ≤ N := by rw [pow_succ] at hN; omega
    exact_mod_cast this
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  have hc2 : (B : ℝ) * N ≤ 2 * cum (champLen 1) N := by nlinarith
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity), div_lt_iff₀ hcpos]
  have h4 : 4 * (N : ℝ) < ε * B * N := by nlinarith
  have h5 : ε * (B * N) ≤ ε * (2 * cum (champLen 1) N) := by
    exact mul_le_mul_of_nonneg_left hc2 hε.le
  nlinarith

/-- A prefix ending inside word `N` costs at most `N + 1` more, on each side. -/
theorem abs_occ_sub_le (u : List Bool) (hu : 1 ≤ u.length) (N K : ℕ)
    (h₁ : cum (champLen 1) N ≤ K) (h₂ : K < cum (champLen 1) (N + 1)) :
    |(occ (collatzChampernowne 1) u K : ℝ) - (K : ℝ) / 2 ^ u.length| ≤
      (2 * u.length + 4) * ((N : ℝ) + 1) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h₁
  have hd : d < Nat.size (N + 1) := by
    rw [cum_succ, champLen_one] at h₂; omega
  have hsize : Nat.size (N + 1) ≤ N + 1 := Nat.size_le.mpr Nat.lt_two_pow_self
  have hb := abs_occ_cum_sub_le u hu N
  have he : ((Finset.range d).filter fun i =>
      OccursAt (collatzChampernowne 1) u (cum (champLen 1) N + i)).card ≤ d := by
    simpa using Finset.card_filter_le (Finset.range d)
      (fun i => OccursAt (collatzChampernowne 1) u (cum (champLen 1) N + i))
  rw [occ_add]
  set e := ((Finset.range d).filter fun i =>
      OccursAt (collatzChampernowne 1) u (cum (champLen 1) N + i)).card
  have heR : (e : ℝ) ≤ d := by exact_mod_cast he
  have hdR : (d : ℝ) ≤ N + 1 := by exact_mod_cast (show d ≤ N + 1 by omega)
  have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg _
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have h2L : (1 : ℝ) ≤ 2 ^ u.length := one_le_pow₀ (by norm_num)
  have hdiv : (d : ℝ) / 2 ^ u.length ≤ d := div_le_self hd0 h2L
  have hdiv0 : (0 : ℝ) ≤ (d : ℝ) / 2 ^ u.length := by positivity
  push_cast
  rw [add_div]
  rw [abs_le] at hb ⊢
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hLN : (0 : ℝ) ≤ u.length * N := by positivity
  have hL0 : (0 : ℝ) ≤ u.length := Nat.cast_nonneg _
  constructor <;> nlinarith [hb.1, hb.2]

/-- Position `K` lies in word `wordIndex K`. -/
private theorem cum_le_wordIndex (K : ℕ) :
    cum (champLen 1) (wordIndex (champLen 1) (one_le_champLen 1) K) ≤ K ∧
      K < cum (champLen 1) (wordIndex (champLen 1) (one_le_champLen 1) K + 1) := by
  have hex := exists_lt_cum_succ (champLen 1) (one_le_champLen 1) K
  refine ⟨?_, Nat.find_spec hex⟩
  show cum (champLen 1) (Nat.find hex) ≤ K
  rcases hm : Nat.find hex with _ | m
  · simp
  · have := Nat.find_min hex (m := m) (by omega)
    omega

/-- **`𝒞_1` is normal**: Terras's bijection and a count, with no further Collatz input. -/
theorem collatzChampernowne_one_normal : Normal (collatzChampernowne 1) := by
  intro u
  rcases Nat.eq_zero_or_pos u.length with h0 | hu
  · have hu0 : u = [] := List.length_eq_zero_iff.mp h0
    subst hu0
    have hocc : ∀ k, occ (collatzChampernowne 1) [] k = k := by
      intro k
      have : (Finset.range k).filter (fun i => OccursAt (collatzChampernowne 1) [] i) =
          Finset.range k := by
        apply Finset.filter_true_of_mem
        intro i _ j
        exact j.elim0
      rw [occ, this, Finset.card_range]
    refine (tendsto_const_nhds (x := (1 : ℝ))).congr' ?_ |>.trans (by simp)
    filter_upwards [eventually_gt_atTop 0] with k hk
    rw [hocc, div_self (by exact_mod_cast hk.ne')]
  · set W := wordIndex (champLen 1) (one_le_champLen 1) with hW
    have hWtend : Tendsto W atTop atTop := by
      refine tendsto_atTop.mpr fun b => ?_
      filter_upwards [eventually_ge_atTop (cum (champLen 1) b)] with K hK
      by_contra hlt
      have h2 : K < cum (champLen 1) (W K + 1) := (cum_le_wordIndex K).2
      have := cum_mono (champLen 1) (show W K + 1 ≤ b by omega)
      omega
    have hg : Tendsto (fun K => (2 * (u.length : ℝ) + 4) *
        (((W K : ℝ) + 1) / (cum (champLen 1) (W K) : ℝ))) atTop (𝓝 0) := by
      simpa using (tendsto_succ_div_cum.comp hWtend).const_mul (2 * (u.length : ℝ) + 4)
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hg
    filter_upwards [hWtend.eventually_ge_atTop 1] with K hK1
    have hbr : cum (champLen 1) (W K) ≤ K ∧ K < cum (champLen 1) (W K + 1) := cum_le_wordIndex K
    obtain ⟨h₁, h₂⟩ := hbr
    have hcpos : 0 < cum (champLen 1) (W K) := by
      have := le_cum (champLen 1) (one_le_champLen 1) (W K)
      omega
    have hcR : (0 : ℝ) < cum (champLen 1) (W K) := by exact_mod_cast hcpos
    have hKR : (cum (champLen 1) (W K) : ℝ) ≤ K := by exact_mod_cast h₁
    have hKpos : (0 : ℝ) < K := lt_of_lt_of_le hcR hKR
    have hb := abs_occ_sub_le u hu (W K) K h₁ h₂
    have heq : (occ (collatzChampernowne 1) u K : ℝ) / K - (1 / 2 : ℝ) ^ u.length =
        ((occ (collatzChampernowne 1) u K : ℝ) - (K : ℝ) / 2 ^ u.length) / K := by
      rw [one_div, inv_pow]; field_simp
    rw [Real.dist_eq, heq, abs_div, abs_of_pos hKpos, ← mul_div_assoc]
    have hnum : (0 : ℝ) ≤ (2 * (u.length : ℝ) + 4) * ((W K : ℝ) + 1) := by positivity
    exact (div_le_div_of_nonneg_right hb hKpos.le).trans
      (div_le_div_of_nonneg_left hnum hcR hKR)

end CollatzMoonshot.Conjugacy
