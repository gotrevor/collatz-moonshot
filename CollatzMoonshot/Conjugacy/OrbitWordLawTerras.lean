/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.OrbitWordLawProb

/-!
# The orbit word law: Terras with constraints

`cardMatchSet_holds` proves `CardMatchSet`: among `r < 2^m`, prescribing the letters at any set
`S` of positions below `m` leaves `2^(m − |S|)` residues.  Adding `2^m` leaves the letters below
`m` alone and flips letter `m` (Terras), so each step of the induction either halves (`m ∈ S`) or
doubles nothing away (`m ∉ S`).  One and two windows (`cardMatchOne_holds`,
`cardMatchTwo_holds`) are the cases `S = [i, i + |u|)` and its union with `[i', i' + |u|)`.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord
open TaoCollatz

/-- Letter `j` does not see adding `2^k` when `j < k`. -/
theorem accWord_two_pow_add_of_lt {j k : ℕ} (h : j < k) (r : ℕ) :
    accWord (2 ^ k + r) j = accWord r j := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt h
  rw [add_comm, show 2 ^ (j + c + 1) = 2 ^ c * 2 ^ (j + 1) by ring]
  exact accWord_add_mul_two_pow_succ r _ j

/-- A constraint set splits off its top position. -/
theorem forall_mem_iff_erase (P : ℕ → Prop) (S : Finset ℕ) (m : ℕ) :
    (∀ s ∈ S, P s) ↔ (∀ s ∈ S.erase m, P s) ∧ (m ∈ S → P m) := by
  constructor
  · exact fun h => ⟨fun s hs => h s (Finset.mem_of_mem_erase hs), h m⟩
  · rintro ⟨h1, h2⟩ s hs
    by_cases hsm : s = m
    · exact hsm ▸ h2 (hsm ▸ hs)
    · exact h1 s (Finset.mem_erase.mpr ⟨hsm, hs⟩)

/-- **Terras with constraints** (`CardMatchSet`). -/
theorem cardMatchSet_holds : CardMatchSet := by
  intro g S m
  induction m generalizing S with
  | zero =>
    intro hS
    have hS0 : S = ∅ := Finset.eq_empty_of_forall_notMem fun s hs => by
      have := hS s hs
      omega
    subst hS0
    simp
  | succ m ih =>
    intro hS
    set S' := S.erase m with hS'def
    have hS' : ∀ s ∈ S', s < m := by
      intro s hs
      have := hS s (Finset.mem_of_mem_erase hs)
      have := Finset.ne_of_mem_erase hs
      omega
    have hcount := ih S' hS'
    rw [Finset.card_filter] at hcount ⊢
    rw [pow_succ, mul_two, Finset.sum_range_add, ← Finset.sum_add_distrib]
    have hpt : ∀ r ∈ Finset.range (2 ^ m),
        ((if ∀ s ∈ S, accWord r s = g s then 1 else 0) +
          (if ∀ s ∈ S, accWord (2 ^ m + r) s = g s then 1 else 0) : ℕ) =
        (if m ∈ S then 1 else 2) * (if ∀ s ∈ S', accWord r s = g s then 1 else 0) := by
      intro r _
      have hlow : (∀ s ∈ S', accWord (2 ^ m + r) s = g s) ↔ ∀ s ∈ S', accWord r s = g s :=
        forall₂_congr fun s hs => by rw [accWord_two_pow_add_of_lt (hS' s hs)]
      have htop : accWord (2 ^ m + r) m = !(accWord r m) := by
        rw [add_comm]; exact accWord_add_two_pow r m
      have e1 := forall_mem_iff_erase (fun s => accWord r s = g s) S m
      have e2 := forall_mem_iff_erase (fun s => accWord (2 ^ m + r) s = g s) S m
      rw [hlow, htop] at e2
      rw [← hS'def] at e1
      simp only [e1, e2]
      by_cases hm : m ∈ S <;> by_cases hP : ∀ s ∈ S', accWord r s = g s
      all_goals first
        | have hP' : (∀ s ∈ S', accWord r s = g s) = True := eq_true hP
          simp only [hP']
        | have hP' : (∀ s ∈ S', accWord r s = g s) = False := eq_false hP
          simp only [hP']
      all_goals cases accWord r m <;> cases g m <;> simp [hm]
    rw [Finset.sum_congr rfl hpt, ← Finset.mul_sum, hcount]
    by_cases hm : m ∈ S
    · have hc : S'.card = S.card - 1 := Finset.card_erase_of_mem hm
      have hc1 : 1 ≤ S.card := Finset.card_pos.mpr ⟨m, hm⟩
      rw [if_pos hm, one_mul, hc]
      congr 1
      omega
    · have hSS : S' = S := Finset.erase_eq_of_notMem hm
      have hle : S.card ≤ m := by
        rw [hSS] at hS'
        have : S ⊆ Finset.range m := fun s hs => Finset.mem_range.mpr (hS' s hs)
        simpa using Finset.card_le_card this
      rw [if_neg hm, hSS, show m + 1 - S.card = (m - S.card) + 1 by omega, pow_succ]
      ring

/-- The letters of a window at `i`, as a function of the position. -/
def winLetters (u : List Bool) (i : ℕ) : ℕ → Bool := fun s => u.getD (s - i) false

/-- A window is a constraint on the positions `[i, i + |u|)`. -/
theorem windowMatch_iff_forall (u : List Bool) (i r : ℕ) :
    WindowMatch (fun s => u.getD s false) u.length i r ↔
      ∀ s ∈ Finset.Ico i (i + u.length), accWord r s = winLetters u i s := by
  constructor
  · intro h s hs
    rw [Finset.mem_Ico] at hs
    have := h (s - i) (by omega)
    rwa [show i + (s - i) = s by omega] at this
  · intro h s hs
    have := h (i + s) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
    rw [this, winLetters, Nat.add_sub_cancel_left]

/-- **One window** (`CardMatchOne`). -/
theorem cardMatchOne_holds : CardMatchOne := by
  intro u m i him
  have := cardMatchSet_holds (winLetters u i) (Finset.Ico i (i + u.length)) m
    (fun s hs => by rw [Finset.mem_Ico] at hs; omega)
  rw [Nat.card_Ico, Nat.add_sub_cancel_left] at this
  rw [← this]
  congr 1
  exact Finset.filter_congr fun r _ => windowMatch_iff_forall u i r

/-- **Two disjoint windows** (`CardMatchTwo`). -/
theorem cardMatchTwo_holds : CardMatchTwo := by
  intro u m i i' hii' him
  set g : ℕ → Bool := fun s => if s < i' then winLetters u i s else winLetters u i' s with hg
  have hdisj : Disjoint (Finset.Ico i (i + u.length)) (Finset.Ico i' (i' + u.length)) :=
    Finset.disjoint_left.mpr fun s h1 h2 => by
      rw [Finset.mem_Ico] at h1 h2
      omega
  have := cardMatchSet_holds g (Finset.Ico i (i + u.length) ∪ Finset.Ico i' (i' + u.length)) m
    (fun s hs => by
      rw [Finset.mem_union, Finset.mem_Ico, Finset.mem_Ico] at hs
      omega)
  rw [Finset.card_union_of_disjoint hdisj, Nat.card_Ico, Nat.card_Ico, Nat.add_sub_cancel_left,
    Nat.add_sub_cancel_left, ← two_mul] at this
  rw [← this]
  congr 1
  refine Finset.filter_congr fun r _ => ?_
  rw [windowMatch_iff_forall, windowMatch_iff_forall]
  constructor
  · rintro ⟨h1, h2⟩ s hs
    rcases Finset.mem_union.mp hs with hs | hs
    · have hs' := Finset.mem_Ico.mp hs
      rw [h1 s hs, hg]
      simp only
      rw [if_pos (by omega)]
    · have hs' := Finset.mem_Ico.mp hs
      rw [h2 s hs, hg]
      simp only
      rw [if_neg (by omega)]
  · intro h
    refine ⟨fun s hs => ?_, fun s hs => ?_⟩
    · have hs' := Finset.mem_Ico.mp hs
      rw [h s (Finset.mem_union_left _ hs), hg]
      simp only
      rw [if_pos (by omega)]
    · have hs' := Finset.mem_Ico.mp hs
      rw [h s (Finset.mem_union_right _ hs), hg]
      simp only
      rw [if_neg (by omega)]

/-! ## The second moment over a block -/

/-- The centred indicator of a match of `u` at `i`. -/
noncomputable def cind (u : List Bool) (i r : ℕ) : ℝ :=
  (if WindowMatch (fun s => u.getD s false) u.length i r then 1 else 0) - (1 / 2 : ℝ) ^ u.length

/-- A deviation is the sum of the centred indicators. -/
theorem wdev_eq_sum_cind (u : List Bool) (r a b : ℕ) :
    wdev u r a b = ∑ i ∈ Finset.Ico a (a + b), cind u i r := by
  unfold wdev wcnt cind
  rw [Finset.card_filter, Finset.sum_sub_distrib]
  push_cast
  simp

/-- A centred indicator is at most `1` in size. -/
theorem abs_cind_le (u : List Bool) (i r : ℕ) : |cind u i r| ≤ 1 := by
  unfold cind
  have hp0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ u.length := by positivity
  have hp1 : (1 / 2 : ℝ) ^ u.length ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  rw [abs_le]
  split_ifs <;> constructor <;> linarith

/-- `2^(m − k) = 2^m 2^(−k)` for `k ≤ m`. -/
theorem two_pow_sub_eq {m k : ℕ} (h : k ≤ m) :
    ((2 ^ (m - k) : ℕ) : ℝ) = 2 ^ m * (1 / 2 : ℝ) ^ k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left]
  push_cast
  rw [pow_add, one_div_pow, mul_comm ((2 : ℝ) ^ k), mul_assoc, mul_one_div_cancel (by positivity),
    mul_one]

/-- Matches of `u` at `i` number `2^m 2^(−|u|)`. -/
theorem sum_match_eq (u : List Bool) {m i : ℕ} (h : i + u.length ≤ m) :
    ∑ r ∈ Finset.range (2 ^ m),
      (if WindowMatch (fun s => u.getD s false) u.length i r then (1 : ℝ) else 0) =
      2 ^ m * (1 / 2 : ℝ) ^ u.length := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, cardMatchOne_holds u m i h,
    two_pow_sub_eq (by omega)]

/-- Disjoint windows are uncorrelated. -/
theorem sum_cind_mul_eq_zero (u : List Bool) {m i j : ℕ} (hij : i + u.length ≤ j)
    (hj : j + u.length ≤ m) :
    ∑ r ∈ Finset.range (2 ^ m), cind u i r * cind u j r = 0 := by
  have hexp : ∀ r, cind u i r * cind u j r =
      (if WindowMatch (fun s => u.getD s false) u.length i r ∧
          WindowMatch (fun s => u.getD s false) u.length j r then (1 : ℝ) else 0) -
        (1 / 2 : ℝ) ^ u.length *
          (if WindowMatch (fun s => u.getD s false) u.length i r then (1 : ℝ) else 0) -
        (1 / 2 : ℝ) ^ u.length *
          (if WindowMatch (fun s => u.getD s false) u.length j r then (1 : ℝ) else 0) +
        ((1 / 2 : ℝ) ^ u.length) ^ 2 := by
    intro r
    unfold cind
    by_cases hA : WindowMatch (fun s => u.getD s false) u.length i r <;>
      by_cases hB : WindowMatch (fun s => u.getD s false) u.length j r <;>
      simp only [hA, hB, and_self, and_true, and_false, if_true, if_false] <;> ring
  simp only [hexp]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, sum_match_eq u (by omega), sum_match_eq u hj, ← Finset.sum_filter,
    Finset.sum_const, nsmul_eq_mul, mul_one, cardMatchTwo_holds u m i j hij hj,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, two_pow_sub_eq (by omega)]
  push_cast
  ring

/-- Each pair of positions contributes at most `2^m`, and nothing when the windows are disjoint. -/
theorem sum_cind_mul_le (u : List Bool) {m i j : ℕ} (hi : i + u.length ≤ m)
    (hj : j + u.length ≤ m) :
    ∑ r ∈ Finset.range (2 ^ m), cind u i r * cind u j r ≤
      if i < j + u.length ∧ j < i + u.length then (2 : ℝ) ^ m else 0 := by
  split_ifs with h
  · refine le_trans (Finset.sum_le_sum (g := fun _ => (1 : ℝ)) fun r _ => ?_) (le_of_eq ?_)
    · have := abs_mul (cind u i r) (cind u j r)
      have h1 := abs_cind_le u i r
      have h2 := abs_cind_le u j r
      have : |cind u i r| * |cind u j r| ≤ 1 := by
        nlinarith [abs_nonneg (cind u i r), abs_nonneg (cind u j r)]
      linarith [le_abs_self (cind u i r * cind u j r)]
    · simp
  · rw [not_and_or, not_lt, not_lt] at h
    rcases h with h | h
    · rw [show (∑ r ∈ Finset.range (2 ^ m), cind u i r * cind u j r) =
          ∑ r ∈ Finset.range (2 ^ m), cind u j r * cind u i r from
          Finset.sum_congr rfl fun r _ => mul_comm _ _, sum_cind_mul_eq_zero u h hi]
    · rw [sum_cind_mul_eq_zero u h hj]

/-- **The second moment over a block** (`SumSqWdevLe`). -/
theorem sumSqWdevLe_holds : SumSqWdevLe := by
  intro u m a b hm
  have hsq : ∀ r, (wdev u r a b) ^ 2 = ∑ i ∈ Finset.Ico a (a + b), ∑ j ∈ Finset.Ico a (a + b),
      cind u i r * cind u j r := by
    intro r
    rw [wdev_eq_sum_cind, sq, Finset.sum_mul_sum]
  simp only [hsq]
  rw [Finset.sum_comm]
  refine le_trans (Finset.sum_le_sum fun i hi => ?_) (le_of_eq (a := ∑ i ∈ Finset.Ico a (a + b),
    2 * (u.length : ℝ) * 2 ^ m) ?_)
  · rw [Finset.sum_comm]
    have hi' := Finset.mem_Ico.mp hi
    refine le_trans (Finset.sum_le_sum fun j hj => sum_cind_mul_le u (by omega)
      (by have := Finset.mem_Ico.mp hj; omega)) ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Finset.Ico a (a + b)).filter
        fun j => i < j + u.length ∧ j < i + u.length).card ≤ 2 * u.length := by
      refine le_trans (Finset.card_le_card (t := Finset.Ico (i + 1 - u.length) (i + u.length))
        fun j hj => ?_) ?_
      · rw [Finset.mem_filter] at hj
        rw [Finset.mem_Ico]
        omega
      · rw [Nat.card_Ico]
        omega
    have : (((Finset.Ico a (a + b)).filter
        fun j => i < j + u.length ∧ j < i + u.length).card : ℝ) ≤ 2 * u.length := by
      exact_mod_cast hcard
    have h2 : (0 : ℝ) ≤ 2 ^ m := by positivity
    nlinarith
  · rw [Finset.sum_const, Nat.card_Ico, Nat.add_sub_cancel_left, nsmul_eq_mul]
    ring

/-- **Chebyshev on a block** (`CardBadBlockLe`). -/
theorem cardBadBlockLe_holds : CardBadBlockLe := by
  intro u m a b ε hm hε hb
  set bad := (Finset.range (2 ^ m)).filter fun r => ε * b < |wdev u r a b| with hbad
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hεb : 0 < ε * b := by positivity
  have h1 : (bad.card : ℝ) * (ε * b) ^ 2 ≤ ∑ r ∈ Finset.range (2 ^ m), (wdev u r a b) ^ 2 := by
    calc (bad.card : ℝ) * (ε * b) ^ 2 = ∑ r ∈ bad, (ε * b) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ r ∈ bad, (wdev u r a b) ^ 2 := by
          refine Finset.sum_le_sum fun r hr => ?_
          rw [hbad, Finset.mem_filter] at hr
          rw [← sq_abs (wdev u r a b)]
          exact pow_le_pow_left₀ hεb.le hr.2.le 2
      _ ≤ ∑ r ∈ Finset.range (2 ^ m), (wdev u r a b) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun r _ _ => sq_nonneg _
  have h2 := sumSqWdevLe_holds u m a b hm
  rw [le_div_iff₀ (by positivity)]
  have : (bad.card : ℝ) * (ε * b) ^ 2 = (bad.card : ℝ) * (ε ^ 2 * b) * b := by ring
  have h3 : (bad.card : ℝ) * (ε ^ 2 * b) * b ≤ 2 * u.length * 2 ^ m * b := by
    nlinarith
  exact le_of_mul_le_mul_right h3 hbR

/-! ## Blocks give windows -/

/-- Good blocks give a good run of consecutive blocks. -/
theorem abs_wdev_blocks_le (u : List Bool) (n k b : ℕ) {ε : ℝ} :
    ∀ d : ℕ, (∀ i < d, |wdev u n ((k + i) * b) b| ≤ ε) → |wdev u n (k * b) (d * b)| ≤ d * ε
  | 0, _ => by simp [wdev, wcnt]
  | d + 1, h => by
    rw [add_mul, one_mul, wdev_add, show k * b + d * b = (k + d) * b by ring]
    have h1 := abs_wdev_blocks_le u n k b d fun i hi => h i (by omega)
    have h2 := h d (by omega)
    have := abs_add_le (wdev u n (k * b) (d * b)) (wdev u n ((k + d) * b) b)
    push_cast
    linarith

/-- **Blocks give windows** (`WinGoodOfBlocks`). -/
theorem winGoodOfBlocks_holds : WinGoodOfBlocks := by
  intro u δ H Λ K b n hδ hb hKb hbH hblk a ℓ ha hHℓ hℓΛ
  rcases le_or_gt 1 δ with hδ1 | hδ1
  · have := abs_wdev_le u n a ℓ
    have : (ℓ : ℝ) ≤ δ * ℓ := le_mul_of_one_le_left (Nat.cast_nonneg _) hδ1
    linarith
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hbℓR : 8 * (b : ℝ) ≤ ℓ := by
    have : (H : ℝ) ≤ ℓ := by exact_mod_cast hHℓ
    nlinarith
  have hbℓ : 8 * b ≤ ℓ := by exact_mod_cast hbℓR
  -- the first and last block boundaries inside the window
  obtain ⟨q₁, r₁, hqr₁, hr₁⟩ : ∃ q r, b * q + r = a + b - 1 ∧ r < b :=
    ⟨_, _, Nat.div_add_mod (a + b - 1) b, Nat.mod_lt _ hb⟩
  obtain ⟨q₂, r₂, hqr₂, hr₂⟩ : ∃ q r, b * q + r = a + ℓ ∧ r < b :=
    ⟨_, _, Nat.div_add_mod (a + ℓ) b, Nat.mod_lt _ hb⟩
  obtain ⟨c₁, hc₁⟩ : ∃ c, c = b * q₁ := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c, c = b * q₂ := ⟨_, rfl⟩
  rw [← hc₁] at hqr₁
  rw [← hc₂] at hqr₂
  have hlt : c₁ < c₂ := by omega
  have hq : q₁ < q₂ := by
    rw [hc₁, hc₂] at hlt
    exact Nat.lt_of_mul_lt_mul_left hlt
  have hqK : q₂ ≤ K := by
    have : b * q₂ ≤ b * K := by rw [← hc₂, mul_comm b K]; omega
    exact Nat.le_of_mul_le_mul_left this hb
  have hmid : c₂ - c₁ = (q₂ - q₁) * b := by
    rw [hc₁, hc₂, Nat.sub_mul, mul_comm q₂, mul_comm q₁]
  -- split the window
  have e : wdev u n a ℓ = wdev u n a (c₁ - a) + wdev u n c₁ (c₂ - c₁) +
      wdev u n c₂ (a + ℓ - c₂) := by
    have h1 := wdev_add u n a (c₁ - a) ((c₂ - c₁) + (a + ℓ - c₂))
    rw [show c₁ - a + (c₂ - c₁ + (a + ℓ - c₂)) = ℓ by omega, show a + (c₁ - a) = c₁ by omega]
      at h1
    rw [h1, wdev_add, show c₁ + (c₂ - c₁) = c₂ by omega, add_assoc]
  have hA := abs_wdev_le u n a (c₁ - a)
  have hC := abs_wdev_le u n c₂ (a + ℓ - c₂)
  have hAl : ((c₁ - a : ℕ) : ℝ) ≤ b := by exact_mod_cast (show c₁ - a ≤ b by omega)
  have hCl : ((a + ℓ - c₂ : ℕ) : ℝ) ≤ b := by exact_mod_cast (show a + ℓ - c₂ ≤ b by omega)
  have hB : |wdev u n c₁ (c₂ - c₁)| ≤ (q₂ - q₁ : ℕ) * (δ / 4 * b) := by
    rw [hmid, hc₁, mul_comm b q₁]
    refine abs_wdev_blocks_le u n q₁ b (q₂ - q₁) fun i hi => hblk (q₁ + i) (by omega)
  have hBl : ((q₂ - q₁ : ℕ) : ℝ) * b ≤ ℓ := by
    have : (q₂ - q₁) * b ≤ ℓ := by omega
    exact_mod_cast this
  have hB' : |wdev u n c₁ (c₂ - c₁)| ≤ δ / 4 * ℓ := by
    refine le_trans hB ?_
    have : ((q₂ - q₁ : ℕ) : ℝ) * (δ / 4 * b) = δ / 4 * (((q₂ - q₁ : ℕ) : ℝ) * b) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hBl (by positivity)
  rw [e]
  have := abs_add_le (wdev u n a (c₁ - a) + wdev u n c₁ (c₂ - c₁)) (wdev u n c₂ (a + ℓ - c₂))
  have := abs_add_le (wdev u n a (c₁ - a)) (wdev u n c₁ (c₂ - c₁))
  have : 2 * (b : ℝ) ≤ δ * ℓ / 4 := by
    have : (H : ℝ) ≤ ℓ := by exact_mod_cast hHℓ
    nlinarith
  linarith

/-! ## Window events are periodic -/

/-- **A window event sees only `n mod 2^m`** (`WinGoodModIff`). -/
theorem winGoodModIff_holds : WinGoodModIff := by
  intro u δ H Λ m hm n
  have hcnt : ∀ a ℓ, a ≤ Λ → ℓ ≤ Λ → wcnt u (n % 2 ^ m) a ℓ = wcnt u n a ℓ := by
    intro a ℓ ha hℓ
    unfold wcnt
    congr 1
    refine Finset.filter_congr fun i hi => ?_
    rw [Finset.mem_Ico] at hi
    refine forall₂_congr fun s hs => ?_
    rw [accWord_congr_mod (i + s) (s := n)
      (Nat.mod_mod_of_dvd n (pow_dvd_pow 2 (by omega)))]
  have hdev : ∀ a ℓ, a ≤ Λ → ℓ ≤ Λ → wdev u (n % 2 ^ m) a ℓ = wdev u n a ℓ := by
    intro a ℓ ha hℓ
    rw [wdev, wdev, hcnt a ℓ ha hℓ]
  constructor
  · intro h a ℓ ha hH hℓ
    rw [← hdev a ℓ ha hℓ]
    exact h a ℓ ha hH hℓ
  · intro h a ℓ ha hH hℓ
    rw [hdev a ℓ ha hℓ]
    exact h a ℓ ha hH hℓ

end CollatzMoonshot.Conjugacy
