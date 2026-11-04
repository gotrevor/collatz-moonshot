/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.OrbitStageLawRate

/-!
# The stage word law: the pullback

Inselmann's pullback (arXiv:2402.03276, Lemma 2.16), in the form of the research note §7.  Let
`k = size n`, `a = oddCount n k`, `M = T^k n`.

* `3^a n ≤ 2^k M` (`three_pow_mul_le`) and `2^k M ≤ 3^a n + ∑_(i<k) 2^i 3^(a − a_i)`
  (`two_pow_mul_le`).
* If no suffix of length `≥ ℓ₀` has more than `3/5` odd letters (`SufGood`), every term of the sum is
  at most `2^(k + ℓ₀)` (`sum_offset_le`).
* So given `a` and `M`, `n` lies in an interval of length `k 2^(k + ℓ₀) / 3^a` (`card_fiber_le`), and
  `M < 3^a (1 + k 2^ℓ₀)`.  Summing over `a ≥ k/4` and `M ∈ B` gives `card_pull_good_le`.

No residue of `M` is used, only its size.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord

/-! ## Odd counts -/

theorem oddCount_mono (n : ℕ) {i j : ℕ} (h : i ≤ j) : oddCount n i ≤ oddCount n j := by
  rw [oddCount_eq_sum, oddCount_eq_sum]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono h)

theorem oddCount_add_le (n i : ℕ) : ∀ d, oddCount n (i + d) ≤ oddCount n i + d
  | 0 => le_refl _
  | d + 1 => by
    rw [← add_assoc, oddCount_succ']
    have := oddCount_add_le n i d
    split_ifs <;> omega

/-! ## The affine bounds -/

/-- One step: `3^(odd) y ≤ 2 T y ≤ 3^(odd) y + 1`. -/
theorem tstep_bounds (y : ℕ) :
    (if y % 2 = 1 then 3 else 1) * y ≤ 2 * tstep y ∧
      2 * tstep y ≤ (if y % 2 = 1 then 3 else 1) * y + 1 := by
  unfold tstep
  split_ifs with h1 h2 <;> omega

/-- `3^a n ≤ 2^j T^j n`. -/
theorem three_pow_mul_le (n : ℕ) : ∀ j, 3 ^ oddCount n j * n ≤ 2 ^ j * tstep^[j] n
  | 0 => by rw [oddCount_zero]; simp
  | j + 1 => by
    rw [oddCount_succ', Function.iterate_succ_apply', pow_add, pow_succ]
    have ih := three_pow_mul_le n j
    have hb := (tstep_bounds (tstep^[j] n)).1
    split_ifs at hb ⊢ with h
    · calc 3 ^ oddCount n j * 3 ^ 1 * n = 3 * (3 ^ oddCount n j * n) := by ring
        _ ≤ 3 * (2 ^ j * tstep^[j] n) := Nat.mul_le_mul_left _ ih
        _ = 2 ^ j * (3 * tstep^[j] n) := by ring
        _ ≤ 2 ^ j * (2 * tstep (tstep^[j] n)) := Nat.mul_le_mul_left _ hb
        _ = 2 ^ j * 2 * tstep (tstep^[j] n) := by ring
    · calc 3 ^ oddCount n j * 3 ^ 0 * n = 3 ^ oddCount n j * n := by ring
        _ ≤ 2 ^ j * tstep^[j] n := ih
        _ = 2 ^ j * (1 * tstep^[j] n) := by ring
        _ ≤ 2 ^ j * (2 * tstep (tstep^[j] n)) := Nat.mul_le_mul_left _ hb
        _ = 2 ^ j * 2 * tstep (tstep^[j] n) := by ring

/-- `2^j T^j n ≤ 3^a n + ∑_(i<j) 2^i 3^(a − a_i)`. -/
theorem two_pow_mul_le (n : ℕ) : ∀ j, 2 ^ j * tstep^[j] n ≤
    3 ^ oddCount n j * n + ∑ i ∈ Finset.range j, 2 ^ i * 3 ^ (oddCount n j - oddCount n i)
  | 0 => by rw [oddCount_zero]; simp
  | j + 1 => by
    have ih := two_pow_mul_le n j
    have hb := (tstep_bounds (tstep^[j] n)).2
    have hmono : ∀ i ∈ Finset.range j, oddCount n i ≤ oddCount n j := fun i hi =>
      oddCount_mono n (Finset.mem_range.mp hi).le
    rw [Function.iterate_succ_apply', Finset.sum_range_succ, pow_succ]
    set y := tstep^[j] n
    set S := ∑ i ∈ Finset.range j, 2 ^ i * 3 ^ (oddCount n j - oddCount n i)
    rw [oddCount_succ']
    split_ifs at hb ⊢ with h
    · have hS : ∑ i ∈ Finset.range j, 2 ^ i * 3 ^ (oddCount n j + 1 - oddCount n i) = 3 * S := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [show oddCount n j + 1 - oddCount n i = (oddCount n j - oddCount n i) + 1 by
          have := hmono i hi; omega, pow_succ]
        ring
      rw [hS, show oddCount n j + 1 - oddCount n j = 1 by omega, pow_succ]
      calc 2 ^ j * 2 * tstep y = 2 ^ j * (2 * tstep y) := by ring
        _ ≤ 2 ^ j * (3 * y + 1) := Nat.mul_le_mul_left _ hb
        _ = 3 * (2 ^ j * y) + 2 ^ j := by ring
        _ ≤ 3 * (3 ^ oddCount n j * n + S) + 2 ^ j := by omega
        _ ≤ 3 ^ oddCount n j * 3 * n + (3 * S + 2 ^ j * (3 ^ 0 * 3)) := by ring_nf; omega
    · have hS : ∑ i ∈ Finset.range j, 2 ^ i * 3 ^ (oddCount n j + 0 - oddCount n i) = S := by
        simp only [add_zero]; rfl
      rw [hS, show oddCount n j + 0 - oddCount n j = 0 by omega, add_zero]
      calc 2 ^ j * 2 * tstep y = 2 ^ j * (2 * tstep y) := by ring
        _ ≤ 2 ^ j * (1 * y + 1) := Nat.mul_le_mul_left _ hb
        _ = 2 ^ j * y + 2 ^ j := by ring
        _ ≤ 3 ^ oddCount n j * n + S + 2 ^ j := by omega
        _ = 3 ^ oddCount n j * n + (S + 2 ^ j * 3 ^ 0) := by ring

/-- `5 d ≤ 3 ℓ` gives `3^d ≤ 2^ℓ`. -/
theorem three_pow_le_two_pow {d ℓ : ℕ} (h : 5 * d ≤ 3 * ℓ) : 3 ^ d ≤ 2 ^ ℓ := by
  have h5 : (3 ^ d) ^ 5 ≤ (2 ^ ℓ) ^ 5 := by
    rw [← pow_mul, ← pow_mul, mul_comm d, mul_comm ℓ]
    calc 3 ^ (5 * d) ≤ 3 ^ (3 * ℓ) := Nat.pow_le_pow_right (by norm_num) h
      _ = 27 ^ ℓ := by rw [pow_mul]; norm_num
      _ ≤ 32 ^ ℓ := Nat.pow_le_pow_left (by norm_num) ℓ
      _ = 2 ^ (5 * ℓ) := by rw [pow_mul]; norm_num
  exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h5

/-- **The offset bound.**  Under `SufGood ℓ₀ s n`, the offset sum is at most `s 2^(s + ℓ₀)`. -/
theorem sum_offset_le {ℓ₀ s n : ℕ} (h : SufGood ℓ₀ s n) :
    ∑ i ∈ Finset.range s, 2 ^ i * 3 ^ (oddCount n s - oddCount n i) ≤ s * 2 ^ (s + ℓ₀) := by
  have hterm : ∀ i ∈ Finset.range s, 2 ^ i * 3 ^ (oddCount n s - oddCount n i) ≤ 2 ^ (s + ℓ₀) := by
    intro i hi
    have his := Finset.mem_range.mp hi
    by_cases hl : i + ℓ₀ ≤ s
    · have h3 := three_pow_le_two_pow (h i hl)
      calc 2 ^ i * 3 ^ (oddCount n s - oddCount n i) ≤ 2 ^ i * 2 ^ (s - i) :=
            Nat.mul_le_mul_left _ h3
        _ = 2 ^ s := by rw [← pow_add]; congr 1; omega
        _ ≤ 2 ^ (s + ℓ₀) := Nat.pow_le_pow_right (by norm_num) (by omega)
    · have hd : oddCount n s - oddCount n i ≤ s - i := by
        have := oddCount_add_le n i (s - i)
        rw [show i + (s - i) = s by omega] at this
        omega
      calc 2 ^ i * 3 ^ (oddCount n s - oddCount n i) ≤ 2 ^ i * 4 ^ (s - i) := by
            refine Nat.mul_le_mul_left _ ?_
            exact le_trans (Nat.pow_le_pow_right (by norm_num) hd)
              (Nat.pow_le_pow_left (by norm_num) _)
        _ = 2 ^ (s + (s - i)) := by
            rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]; congr 1; omega
        _ ≤ 2 ^ (s + ℓ₀) := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc _ ≤ ∑ _i ∈ Finset.range s, 2 ^ (s + ℓ₀) := Finset.sum_le_sum hterm
    _ = s * 2 ^ (s + ℓ₀) := by simp

/-! ## The fibre count -/

/-- At most `R / c + 1` integers `n` have `c n ∈ [x − R, x]`. -/
theorem card_fiber_le (S : Finset ℕ) {c : ℕ} (hc : 0 < c) (x R : ℕ) :
    (S.filter fun n => c * n ≤ x ∧ x ≤ c * n + R).card ≤ R / c + 1 := by
  set F := S.filter fun n => c * n ≤ x ∧ x ≤ c * n + R
  rcases F.eq_empty_or_nonempty with hF | hF
  · rw [hF]; simp
  · set n₀ := F.min' hF
    have hn₀ : n₀ ∈ F := F.min'_mem hF
    have hsub : F ⊆ Finset.Icc n₀ (n₀ + R / c) := by
      intro n hn
      have hle : n₀ ≤ n := F.min'_le n hn
      have h1 := (Finset.mem_filter.mp hn).2.1
      have h2 := (Finset.mem_filter.mp hn₀).2.2
      have h3 : c * (n - n₀) ≤ R := by
        rw [Nat.mul_sub]; omega
      have h4 : n - n₀ ≤ R / c := (Nat.le_div_iff_mul_le hc).mpr (by rw [mul_comm]; exact h3)
      exact Finset.mem_Icc.mpr ⟨hle, by omega⟩
    calc F.card ≤ (Finset.Icc n₀ (n₀ + R / c)).card := Finset.card_le_card hsub
      _ = R / c + 1 := by rw [Nat.card_Icc, add_assoc, Nat.add_sub_cancel_left]

/-! ## The pullback count -/

/-- `2^(size X) ≤ 2 X` for `X ≥ 1`. -/
theorem two_pow_size_le {X : ℕ} (hX : 1 ≤ X) : 2 ^ Nat.size X ≤ 2 * X := by
  have h1 : 0 < Nat.size X := Nat.size_pos.mpr hX
  have h2 : 2 ^ (Nat.size X - 1) ≤ X := Nat.lt_size.mp (by omega)
  calc 2 ^ Nat.size X = 2 * 2 ^ (Nat.size X - 1) := by
        rw [← pow_succ']; congr 1; omega
    _ ≤ 2 * X := Nat.mul_le_mul_left _ h2

open Classical in
/-- The targets below `X` number at most `A 2X ρ^a`, when `X ≥ 2^a`. -/
theorem card_target_le {B : Set ℕ} {A ρ : ℝ} (hA : 0 ≤ A) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hB : ∀ K : ℕ, (((Finset.range (2 ^ K)).filter (· ∈ B)).card : ℝ) ≤ A * (2 * ρ) ^ K)
    {X a : ℕ} (hX : 2 ^ a ≤ X) :
    (((Finset.range X).filter (· ∈ B)).card : ℝ) ≤ A * (2 * X) * ρ ^ a := by
  have hX1 : 1 ≤ X := le_trans Nat.one_le_two_pow hX
  have hsz : a < Nat.size X := Nat.lt_size.mpr hX
  have hsub : (Finset.range X).filter (· ∈ B) ⊆ (Finset.range (2 ^ Nat.size X)).filter (· ∈ B) :=
    Finset.filter_subset_filter _ (Finset.range_mono (Nat.lt_size_self X).le)
  have h2 : ((2 ^ Nat.size X : ℕ) : ℝ) ≤ 2 * X := by exact_mod_cast two_pow_size_le hX1
  calc (((Finset.range X).filter (· ∈ B)).card : ℝ)
      ≤ (((Finset.range (2 ^ Nat.size X)).filter (· ∈ B)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ A * (2 * ρ) ^ Nat.size X := hB _
    _ = A * (2 ^ Nat.size X : ℕ) * ρ ^ Nat.size X := by push_cast; ring
    _ ≤ A * (2 * X) * ρ ^ a := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left h2 hA) ?_ (by positivity) (by positivity)
        exact pow_le_pow_of_le_one hρ0 hρ1 hsz.le

open Classical in
/-- **The pullback count.**  The good starts of stage `k` whose window lands in `B`. -/
theorem card_pull_good_le {B : Set ℕ} {A ρ : ℝ} (hA : 0 ≤ A) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hB : ∀ K : ℕ, (((Finset.range (2 ^ K)).filter (· ∈ B)).card : ℝ) ≤ A * (2 * ρ) ^ K)
    {k ℓ₀ : ℕ} (hk : 1 ≤ k) (hℓ : ℓ₀ ≤ k) :
    (((Finset.Ico (2 ^ (k - 1)) (2 ^ k)).filter fun n =>
        SufGood ℓ₀ k n ∧ OddLow (1 / 4) k n ∧ stageMap n ∈ B).card : ℝ) ≤
      4 * A * (k + 1) * ((1 + k * 2 ^ ℓ₀ : ℕ) * (k * 2 ^ (k + ℓ₀) : ℕ)) * ρ ^ (k / 4) := by
  set R := k * 2 ^ (k + ℓ₀) with hR
  set W := 1 + k * 2 ^ ℓ₀ with hW
  set I := Finset.Ico (2 ^ (k - 1)) (2 ^ k)
  set F := I.filter fun n => SufGood ℓ₀ k n ∧ OddLow (1 / 4) k n ∧ stageMap n ∈ B
  set Aset := (Finset.range (k + 1)).filter fun a => k ≤ 4 * a ∧ 5 * a ≤ 3 * k
  set fib : ℕ → ℕ → Finset ℕ := fun a M =>
    I.filter fun n => 3 ^ a * n ≤ 2 ^ k * M ∧ 2 ^ k * M ≤ 3 ^ a * n + R
  set T : ℕ → Finset ℕ := fun a => (Finset.range (3 ^ a * W)).filter (· ∈ B)
  have hsub : F ⊆ Aset.biUnion fun a => (T a).biUnion (fib a) := by
    intro n hn
    obtain ⟨hnI, hsuf, hodd, hBn⟩ := Finset.mem_filter.mp hn
    have hnI' := Finset.mem_Ico.mp hnI
    have hsize : Nat.size n = k := size_of_mem_stage hk hnI'.1 hnI'.2
    set a := oddCount n k
    have hak : a ≤ k := by simpa [oddCount_zero] using oddCount_add_le n 0 k
    have h5a : 5 * a ≤ 3 * k := by simpa [oddCount_zero] using hsuf 0 (by omega)
    have h4a : k ≤ 4 * a := by
      have : (1 / 2 - 1 / 4 : ℝ) * k ≤ a := hodd
      have : (k : ℝ) ≤ 4 * a := by linarith
      exact_mod_cast this
    have hlow := three_pow_mul_le n k
    have hup := le_trans (two_pow_mul_le n k) (Nat.add_le_add_left (sum_offset_le hsuf) _)
    have hM : stageMap n = tstep^[k] n := by rw [stageMap, hsize]
    have hMlt : tstep^[k] n < 3 ^ a * W := by
      have h1 : 3 ^ a * n < 3 ^ a * 2 ^ k := Nat.mul_lt_mul_of_pos_left hnI'.2 (by positivity)
      have h2 : 2 ^ k * tstep^[k] n < 2 ^ k * (3 ^ a + k * 2 ^ ℓ₀) := by
        calc 2 ^ k * tstep^[k] n ≤ 3 ^ a * n + R := hup
          _ < 3 ^ a * 2 ^ k + R := by omega
          _ = 2 ^ k * (3 ^ a + k * 2 ^ ℓ₀) := by rw [hR, pow_add]; ring
      have h3 := Nat.lt_of_mul_lt_mul_left h2
      have h4 : 1 ≤ 3 ^ a := Nat.one_le_pow _ _ (by norm_num)
      calc tstep^[k] n < 3 ^ a + k * 2 ^ ℓ₀ := h3
        _ ≤ 3 ^ a + 3 ^ a * (k * 2 ^ ℓ₀) := by
            have := Nat.le_mul_of_pos_left (k * 2 ^ ℓ₀) h4
            omega
        _ = 3 ^ a * W := by rw [hW]; ring
    refine Finset.mem_biUnion.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h4a, h5a⟩,
      Finset.mem_biUnion.mpr ⟨tstep^[k] n, Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr hMlt, hM ▸ hBn⟩, Finset.mem_filter.mpr ⟨hnI, hlow, hup⟩⟩⟩
  have hper : ∀ a ∈ Aset, (((T a).biUnion (fib a)).card : ℝ) ≤
      4 * A * (W * R : ℕ) * ρ ^ (k / 4) := by
    intro a ha
    obtain ⟨ha1, ha2, h5a⟩ := Finset.mem_filter.mp ha
    have ha1' := Finset.mem_range.mp ha1
    have hfib : ∀ M ∈ T a, (fib a M).card ≤ R / 3 ^ a + 1 := fun M _ =>
      card_fiber_le I (by positivity) _ _
    have h1 : ((T a).biUnion (fib a)).card ≤ (T a).card * (R / 3 ^ a + 1) := by
      calc ((T a).biUnion (fib a)).card ≤ ∑ M ∈ T a, (fib a M).card := Finset.card_biUnion_le
        _ ≤ ∑ _M ∈ T a, (R / 3 ^ a + 1) := Finset.sum_le_sum hfib
        _ = (T a).card * (R / 3 ^ a + 1) := by simp
    have h3a : 3 ^ a ≤ R := by
      calc 3 ^ a ≤ 2 ^ k := three_pow_le_two_pow h5a
        _ ≤ 2 ^ (k + ℓ₀) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ R := by rw [hR]; exact Nat.le_mul_of_pos_left _ hk
    have hW1 : 1 ≤ W := by omega
    have hX : 2 ^ a ≤ 3 ^ a * W :=
      le_trans (Nat.pow_le_pow_left (by norm_num) a) (Nat.le_mul_of_pos_right _ hW1)
    have hT := card_target_le hA hρ0 hρ1 hB hX
    have hdiv : ((R / 3 ^ a : ℕ) : ℝ) ≤ (R : ℝ) / 3 ^ a := by
      have := Nat.cast_div_le (m := R) (n := 3 ^ a) (α := ℝ)
      simpa using this
    have h3pos : (0 : ℝ) < 3 ^ a := by positivity
    have hkey : (3 : ℝ) ^ a * ((R : ℝ) / 3 ^ a + 1) ≤ 2 * R := by
      rw [mul_add, mul_div_cancel₀ _ h3pos.ne', mul_one]
      have : ((3 ^ a : ℕ) : ℝ) ≤ R := by exact_mod_cast h3a
      push_cast at this
      linarith
    have hρa : ρ ^ a ≤ ρ ^ (k / 4) := pow_le_pow_of_le_one hρ0 hρ1 (by omega)
    calc (((T a).biUnion (fib a)).card : ℝ) ≤ ((T a).card : ℝ) * ((R / 3 ^ a : ℕ) + 1) := by
          exact_mod_cast h1
      _ ≤ (A * (2 * ((3 ^ a * W : ℕ) : ℝ)) * ρ ^ a) * ((R : ℝ) / 3 ^ a + 1) :=
          mul_le_mul hT (by linarith) (by positivity) (by positivity)
      _ = 2 * A * W * ρ ^ a * ((3 : ℝ) ^ a * ((R : ℝ) / 3 ^ a + 1)) := by push_cast; ring
      _ ≤ 2 * A * W * ρ ^ a * (2 * R) := by
          refine mul_le_mul_of_nonneg_left hkey (by positivity)
      _ ≤ 4 * A * (W * R : ℕ) * ρ ^ (k / 4) := by
          push_cast
          have : 0 ≤ 4 * A * ((W : ℝ) * R) := by positivity
          nlinarith
  have hAset : (Aset.card : ℝ) ≤ k + 1 := by
    have : Aset.card ≤ k + 1 := le_trans (Finset.card_filter_le _ _) (by simp)
    exact_mod_cast this
  calc (F.card : ℝ) ≤ ((Aset.biUnion fun a => (T a).biUnion (fib a)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ a ∈ Aset, (((T a).biUnion (fib a)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ Aset, 4 * A * (W * R : ℕ) * ρ ^ (k / 4) := Finset.sum_le_sum hper
    _ = Aset.card * (4 * A * (W * R : ℕ) * ρ ^ (k / 4)) := by simp
    _ ≤ (k + 1) * (4 * A * (W * R : ℕ) * ρ ^ (k / 4)) :=
        mul_le_mul_of_nonneg_right hAset (by positivity)
    _ = 4 * A * (k + 1) * ((W : ℕ) * (R : ℕ)) * ρ ^ (k / 4) := by push_cast; ring

/-! ## The pullback -/

open Classical in
/-- **Terras tail for suffixes.**  Some suffix of length `≥ ℓ₀` has too many odd letters for at most
`(k + 1) 2^k τ^ℓ₀` residues `r < 2^k`. -/
def SufTail : Prop :=
  ∃ τ : ℝ, 0 < τ ∧ τ < 1 ∧ ∀ k ℓ₀ : ℕ,
    (((Finset.range (2 ^ k)).filter fun r => ¬ SufGood ℓ₀ k r).card : ℝ) ≤ (k + 1) * 2 ^ k * τ ^ ℓ₀

open Classical in
/-- **Terras tail for the odd count.**  Fewer than `(1/2 − γ) k` odd letters for at most `2^k τ^k`
residues `r < 2^k`. -/
def OddTail : Prop :=
  ∀ γ : ℝ, 0 < γ → ∃ τ : ℝ, 0 ≤ τ ∧ τ < 1 ∧ ∀ k : ℕ,
    (((Finset.range (2 ^ k)).filter fun r => ¬ OddLow γ k r).card : ℝ) ≤ 2 ^ k * τ ^ k

/-- A stage count is at most the count over all residues. -/
theorem card_stage_le_range (P : ℕ → Prop) [DecidablePred P] (k : ℕ) :
    (((Finset.Ico (2 ^ (k - 1)) (2 ^ k)).filter P).card : ℝ) ≤
      (((Finset.range (2 ^ k)).filter P).card : ℝ) := by
  have : (Finset.Ico (2 ^ (k - 1)) (2 ^ k)).filter P ⊆ (Finset.range (2 ^ k)).filter P :=
    Finset.filter_subset_filter _ fun n hn => Finset.mem_range.mpr (Finset.mem_Ico.mp hn).2
  exact_mod_cast Finset.card_le_card this

open Classical in
/-- **P2, the pullback** (Inselmann 2024, Lemma 2.16), from the two Terras tails. -/
theorem expSparse_preimage_of_tails (hS : SufTail) (hO : OddTail) {B : Set ℕ} (hB : ExpSparse B) :
    ExpSparse (stageMap ⁻¹' B) := by
  obtain ⟨A, ρ, hA, hρ34, hρ1, hpre⟩ := prefix_of_expSparse hB
  have hρ0 : 0 ≤ ρ := by linarith
  obtain ⟨N', hN'⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 8) hρ1
  have hN'1 : 1 ≤ N' := by
    rcases Nat.eq_zero_or_pos N' with h | h
    · rw [h] at hN'; norm_num at hN'
    · exact h
  set N := 4 * N'
  have hN1 : 1 ≤ N := by omega
  obtain ⟨τs, hτs0, hτs1, hτs⟩ := hS
  obtain ⟨σs, hσs0, hσs1, hσs⟩ := exists_pow_div_le hτs0 hτs1 hN1
  obtain ⟨τo, hτo0, hτo1, hτo⟩ := hO (1 / 4) (by norm_num)
  obtain ⟨σh, hσh0, hσh1, hσh⟩ := exists_pow_div_le (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num) hN1
  set σ := max σs (max τo σh)
  have hσ0 : 0 ≤ σ := le_max_of_le_left hσs0
  have hσ1 : σ < 1 := max_lt hσs1 (max_lt hτo1 hσh1)
  refine expSparse_of_poly (τs⁻¹ + 1 + 16 * A) 3 hσ0 hσ1 1 fun k hk => ?_
  set ℓ₀ := k / N
  have hℓ : ℓ₀ ≤ k := Nat.div_le_self _ _
  set I := Finset.Ico (2 ^ (k - 1)) (2 ^ k)
  have hsub : I.filter (· ∈ stageMap ⁻¹' B) ⊆ (I.filter fun n => ¬ SufGood ℓ₀ k n) ∪
      (I.filter fun n => ¬ OddLow (1 / 4) k n) ∪
      (I.filter fun n => SufGood ℓ₀ k n ∧ OddLow (1 / 4) k n ∧ stageMap n ∈ B) := by
    intro n hn
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hn
    simp only [Finset.mem_union, Finset.mem_filter, Set.mem_preimage] at h2 ⊢
    tauto
  have hc1 := le_trans (card_stage_le_range (fun n => ¬ SufGood ℓ₀ k n) k) (hτs k ℓ₀)
  have hc2 := le_trans (card_stage_le_range (fun n => ¬ OddLow (1 / 4) k n) k) (hτo k)
  have hc3 := card_pull_good_le hA hρ0 hρ1.le hpre hk hℓ
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpow : ∀ x : ℝ, 0 ≤ x → x ≤ σ → (2 * x) ^ k ≤ (2 * σ) ^ k := fun x hx hxσ =>
    pow_le_pow_left₀ (by positivity) (by linarith) k
  have hcub : ((k : ℝ) + 1) ≤ ((k : ℝ) + 1) ^ 3 := by
    nlinarith [sq_nonneg ((k : ℝ) + 1)]
  have hcub1 : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 3 := le_trans (by linarith) hcub
  -- the three terms
  have t1 : ((k : ℝ) + 1) * 2 ^ k * τs ^ ℓ₀ ≤ τs⁻¹ * ((k : ℝ) + 1) ^ 3 * (2 * σ) ^ k := by
    calc ((k : ℝ) + 1) * 2 ^ k * τs ^ ℓ₀ ≤ ((k : ℝ) + 1) * 2 ^ k * (τs⁻¹ * σs ^ k) :=
          mul_le_mul_of_nonneg_left (hσs k) (by positivity)
      _ = τs⁻¹ * ((k : ℝ) + 1) * (2 * σs) ^ k := by rw [mul_pow]; ring
      _ ≤ τs⁻¹ * ((k : ℝ) + 1) ^ 3 * (2 * σ) ^ k := by
          gcongr
          exact le_max_left _ _
  have t2 : (2 : ℝ) ^ k * τo ^ k ≤ 1 * ((k : ℝ) + 1) ^ 3 * (2 * σ) ^ k := by
    rw [← mul_pow, one_mul]
    calc (2 * τo) ^ k ≤ (2 * σ) ^ k := hpow τo hτo0 (le_trans (le_max_left _ _) (le_max_right _ _))
      _ ≤ ((k : ℝ) + 1) ^ 3 * (2 * σ) ^ k := le_mul_of_one_le_left (by positivity) hcub1
  have hWR : (((1 + k * 2 ^ ℓ₀ : ℕ) : ℝ) * ((k * 2 ^ (k + ℓ₀) : ℕ) : ℝ)) ≤
      2 * (k : ℝ) ^ 2 * 2 ^ k * 4 ^ ℓ₀ := by
    push_cast
    have h2 : (1 : ℝ) ≤ 2 ^ ℓ₀ := one_le_pow₀ (by norm_num)
    have h4 : (4 : ℝ) ^ ℓ₀ = 2 ^ ℓ₀ * 2 ^ ℓ₀ := by rw [← mul_pow]; norm_num
    rw [h4, pow_add]
    have : 1 + (k : ℝ) * 2 ^ ℓ₀ ≤ 2 * k * 2 ^ ℓ₀ := by nlinarith
    have hpos : (0 : ℝ) ≤ k * (2 ^ k * 2 ^ ℓ₀) := by positivity
    nlinarith
  have hρk : (4 : ℝ) ^ ℓ₀ * ρ ^ (k / 4) ≤ (1 / 2) ^ ℓ₀ := by
    have hNl : N' * ℓ₀ ≤ k / 4 := by
      have : ℓ₀ = k / 4 / N' := by rw [Nat.div_div_eq_div_mul]
      rw [this, mul_comm]; exact Nat.div_mul_le_self _ _
    calc (4 : ℝ) ^ ℓ₀ * ρ ^ (k / 4) ≤ 4 ^ ℓ₀ * ρ ^ (N' * ℓ₀) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hρ0 hρ1.le hNl) (by positivity)
      _ = (4 * ρ ^ N') ^ ℓ₀ := by rw [mul_pow, pow_mul]
      _ ≤ (1 / 2) ^ ℓ₀ := pow_le_pow_left₀ (by positivity) (by linarith) _
  have t3 : 4 * A * ((k : ℝ) + 1) * (((1 + k * 2 ^ ℓ₀ : ℕ) : ℝ) * ((k * 2 ^ (k + ℓ₀) : ℕ) : ℝ)) *
      ρ ^ (k / 4) ≤ 16 * A * ((k : ℝ) + 1) ^ 3 * (2 * σ) ^ k := by
    have hk2 : (k : ℝ) ^ 2 ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith
    calc 4 * A * ((k : ℝ) + 1) * (((1 + k * 2 ^ ℓ₀ : ℕ) : ℝ) * ((k * 2 ^ (k + ℓ₀) : ℕ) : ℝ)) *
          ρ ^ (k / 4) ≤ 4 * A * ((k : ℝ) + 1) * (2 * (k : ℝ) ^ 2 * 2 ^ k * 4 ^ ℓ₀) * ρ ^ (k / 4) := by
          gcongr
      _ = 8 * A * ((k : ℝ) + 1) * (k : ℝ) ^ 2 * 2 ^ k * (4 ^ ℓ₀ * ρ ^ (k / 4)) := by ring
      _ ≤ 8 * A * ((k : ℝ) + 1) * (k : ℝ) ^ 2 * 2 ^ k * ((1 / 2)⁻¹ * σh ^ k) := by
          exact mul_le_mul_of_nonneg_left (le_trans hρk (hσh k)) (by positivity)
      _ = 16 * A * (((k : ℝ) + 1) * (k : ℝ) ^ 2) * (2 * σh) ^ k := by
          rw [mul_pow]; ring
      _ ≤ 16 * A * ((k : ℝ) + 1) ^ 3 * (2 * σ) ^ k := by
          gcongr
          · nlinarith
          · exact le_trans (le_max_right _ _) (le_max_right _ _)
  calc ((I.filter (· ∈ stageMap ⁻¹' B)).card : ℝ)
      ≤ ((I.filter fun n => ¬ SufGood ℓ₀ k n).card : ℝ) +
        ((I.filter fun n => ¬ OddLow (1 / 4) k n).card : ℝ) +
        ((I.filter fun n => SufGood ℓ₀ k n ∧ OddLow (1 / 4) k n ∧ stageMap n ∈ B).card : ℝ) := by
        have := le_trans (Finset.card_le_card hsub)
          (le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right (Finset.card_union_le _ _) _))
        exact_mod_cast this
    _ ≤ τs⁻¹ * ((k : ℝ) + 1) ^ 3 * (2 * σ) ^ k + 1 * ((k : ℝ) + 1) ^ 3 * (2 * σ) ^ k +
        16 * A * ((k : ℝ) + 1) ^ 3 * (2 * σ) ^ k := by
        linarith [le_trans hc1 t1, le_trans hc2 t2, le_trans hc3 t3]
    _ = (τs⁻¹ + 1 + 16 * A) * ((k : ℝ) + 1) ^ 3 * (2 * σ) ^ k := by ring

end CollatzMoonshot.Conjugacy
