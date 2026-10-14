/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Amusical

/-!
# Counting square visits in a repetition-free orbit window

The pieces of `infinitelyManyOrbits_of_squareReturnConfinement`.

* `even_run_mul`, `even_run_len`: along a run of even inputs the orbit grows by exactly `3/2`
  per step, so a run from a value `≥ 1` to a value `≤ H²` has length `≤ 6 log (2 + H)`.
* `card_small_square_times_le`: under the SRC bound with constant `C`, a repetition-free window
  visits at most `(|C| + 12) log (2 + H) + 3` squares with roots in `[1, H]`.  Either three
  visits sit in three distinct `E`-blocks (SRC bounds the span), or all visits lie in two
  all-even runs (bounded by growth).
* `exists_injective_window`: any finite subset of an orbit lies in one repetition-free forward
  window.
-/

namespace CollatzMoonshot.Amusical

/-- Along an all-even run the orbit is multiplied by exactly `3/2` per step. -/
theorem even_run_mul (y : ℤ) (a : ℕ) : ∀ L : ℕ,
    (∀ i, a ≤ i → i < a + L → ¬ Odd (amusical^[i] y)) →
      2 ^ L * amusical^[a + L] y = 3 ^ L * amusical^[a] y := by
  intro L
  induction L with
  | zero => intro _; simp
  | succ L ih =>
    intro hev
    have h1 := ih (fun i hi hi' => hev i hi (by omega))
    have hodd := hev (a + L) (by omega) (by omega)
    have he : amusical^[a + L] y % 2 = 0 := by
      rcases Int.emod_two_eq_zero_or_one (amusical^[a + L] y) with h | h
      · exact h
      · exact absurd (Int.odd_iff.2 h) hodd
    have h2 := two_mul_amusical_of_even he
    rw [show a + (L + 1) = (a + L) + 1 by omega, Function.iterate_succ_apply', pow_succ,
      pow_succ]
    calc 2 ^ L * 2 * amusical (amusical^[a + L] y)
        = 2 ^ L * (2 * amusical (amusical^[a + L] y)) := by ring
      _ = 2 ^ L * (3 * amusical^[a + L] y) := by rw [h2]
      _ = 3 * (2 ^ L * amusical^[a + L] y) := by ring
      _ = 3 ^ L * 3 * amusical^[a] y := by rw [h1]; ring

/-- An all-even run from a value `≥ 1` to a value `≤ H²` has length `≤ 6 log (2 + H)`. -/
theorem even_run_len (y : ℤ) (a L H : ℕ)
    (hev : ∀ i, a ≤ i → i < a + L → ¬ Odd (amusical^[i] y))
    (h1 : 1 ≤ amusical^[a] y) (hH : amusical^[a + L] y ≤ (H : ℤ) ^ 2) :
    (L : ℝ) ≤ 6 * Real.log (2 + H) := by
  have hrun := even_run_mul y a L hev
  have hint : (3 : ℤ) ^ L ≤ 2 ^ L * (H : ℤ) ^ 2 := by
    calc (3 : ℤ) ^ L = 3 ^ L * 1 := by ring
      _ ≤ 3 ^ L * amusical^[a] y := by gcongr
      _ = 2 ^ L * amusical^[a + L] y := hrun.symm
      _ ≤ 2 ^ L * (H : ℤ) ^ 2 := by gcongr
  have hH0 : (0 : ℝ) ≤ H := H.cast_nonneg
  have hreal : (3 : ℝ) ^ L ≤ 2 ^ L * (2 + H) ^ 2 := by
    have : (((3 : ℤ) ^ L : ℤ) : ℝ) ≤ ((2 ^ L * (H : ℤ) ^ 2 : ℤ) : ℝ) := by exact_mod_cast hint
    push_cast at this
    calc (3 : ℝ) ^ L ≤ 2 ^ L * (H : ℝ) ^ 2 := this
      _ ≤ 2 ^ L * (2 + H) ^ 2 := by gcongr; linarith
  have hlog := Real.log_le_log (by positivity) hreal
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_pow] at hlog
  have h32 : (1 : ℝ) / 3 ≤ Real.log 3 - Real.log 2 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 3 / 2 by norm_num)
    norm_num at this ⊢; linarith
  have hL0 : (0 : ℝ) ≤ L := by positivity
  push_cast at hlog
  nlinarith [mul_le_mul_of_nonneg_left h32 hL0]

/-- `v` is a square with root in `[1, H]`. -/
def IsSmallSq (H : ℕ) (v : ℤ) : Prop := ∃ q : ℕ, 1 ≤ q ∧ q ≤ H ∧ v = (q : ℤ) ^ 2

theorem card_le_of_mem_Icc (J : Finset ℕ) (u v : ℕ) (hJ : ∀ m ∈ J, u ≤ m ∧ m ≤ v) :
    (J.card : ℝ) ≤ ((v - u : ℕ) : ℝ) + 1 := by
  have hsub : J ⊆ Finset.Icc u v := fun m hm => Finset.mem_Icc.2 (hJ m hm)
  have := Finset.card_le_card hsub
  rw [Nat.card_Icc] at this
  have h2 : J.card ≤ v - u + 1 := by omega
  exact_mod_cast h2

open Classical in
/-- **Square visits in a window.**  Under the SRC bound with constant `C` at height `H`, a
repetition-free window `y, U y, …, U^T y` visits at most `(|C| + 12) log (2 + H) + 3` squares
with roots in `[1, H]`. -/
theorem card_small_square_times_le (C : ℝ) (H : ℕ)
    (hC : ∀ (x : ℤ) (s t : ℕ), 0 < s → s < t →
      (∀ i j, i ≤ t → j ≤ t → amusical^[i] x = amusical^[j] x → i = j) →
      (∃ q ≤ H, x = (q : ℤ) ^ 2) → (∃ q ≤ H, amusical^[s] x = (q : ℤ) ^ 2) →
      (∃ q ≤ H, amusical^[t] x = (q : ℤ) ^ 2) →
      (∃ i < s, Odd (amusical^[i] x)) → (∃ i, s ≤ i ∧ i < t ∧ Odd (amusical^[i] x)) →
      (t : ℝ) ≤ C * Real.log (2 + H))
    (y : ℤ) (T : ℕ) (hinj : ∀ i j, i ≤ T → j ≤ T → amusical^[i] y = amusical^[j] y → i = j) :
    (((Finset.range (T + 1)).filter fun i => IsSmallSq H (amusical^[i] y)).card : ℝ) ≤
      (|C| + 12) * Real.log (2 + H) + 3 := by
  classical
  set I := (Finset.range (T + 1)).filter fun i => IsSmallSq H (amusical^[i] y) with hI
  have hH0 : (0 : ℝ) ≤ H := H.cast_nonneg
  have hlog0 : 0 ≤ Real.log (2 + H) := Real.log_nonneg (by linarith)
  have hCl : 0 ≤ |C| * Real.log (2 + H) := mul_nonneg (abs_nonneg C) hlog0
  rcases I.eq_empty_or_nonempty with hemp | hne
  · rw [hemp, Finset.card_empty, Nat.cast_zero]
    nlinarith
  have hmem : ∀ m ∈ I, m ≤ T ∧ IsSmallSq H (amusical^[m] y) := by
    intro m hm
    rw [hI, Finset.mem_filter, Finset.mem_range] at hm
    exact ⟨by omega, hm.2⟩
  have hsq : ∀ m ∈ I, ∃ q ≤ H, amusical^[m] y = (q : ℤ) ^ 2 := by
    intro m hm
    obtain ⟨q, -, hqH, hq⟩ := (hmem m hm).2
    exact ⟨q, hqH, hq⟩
  have hge1 : ∀ m ∈ I, 1 ≤ amusical^[m] y := by
    intro m hm
    obtain ⟨q, hq1, -, hq⟩ := (hmem m hm).2
    rw [hq]
    have : (1 : ℤ) ≤ q := by exact_mod_cast hq1
    nlinarith
  have hleH : ∀ m ∈ I, amusical^[m] y ≤ (H : ℤ) ^ 2 := by
    intro m hm
    obtain ⟨q, hq1, hqH, hq⟩ := (hmem m hm).2
    rw [hq]
    have : (q : ℤ) ≤ H := by exact_mod_cast hqH
    have : (0 : ℤ) ≤ q := by positivity
    nlinarith
  set a := I.min' hne with ha
  set b := I.max' hne with hb
  have haI : a ∈ I := I.min'_mem hne
  have hbI : b ∈ I := I.max'_mem hne
  have hab : ∀ m ∈ I, a ≤ m ∧ m ≤ b := fun m hm => ⟨I.min'_le m hm, I.le_max' m hm⟩
  have hshift : ∀ i, amusical^[i] (amusical^[a] y) = amusical^[i + a] y := fun i =>
    (Function.iterate_add_apply _ _ _ _).symm
  by_cases hA : ∃ m ∈ I, (∃ i, a ≤ i ∧ i < m ∧ Odd (amusical^[i] y)) ∧
      (∃ i, m ≤ i ∧ i < b ∧ Odd (amusical^[i] y))
  · obtain ⟨m, hmI, ⟨i1, hi1a, hi1m, hi1o⟩, ⟨i2, hi2m, hi2b, hi2o⟩⟩ := hA
    have hbT := (hmem b hbI).1
    have hma := (hab m hmI).1
    have hsrc := hC (amusical^[a] y) (m - a) (b - a) (by omega) (by omega)
      (by
        intro i j hi hj hij
        rw [hshift, hshift] at hij
        have := hinj (i + a) (j + a) (by omega) (by omega) hij
        omega)
      (hsq a haI)
      (by rw [hshift, show m - a + a = m by omega]; exact hsq m hmI)
      (by rw [hshift, show b - a + a = b by omega]; exact hsq b hbI)
      ⟨i1 - a, by omega, by rw [hshift, show i1 - a + a = i1 by omega]; exact hi1o⟩
      ⟨i2 - a, by omega, by omega, by rw [hshift, show i2 - a + a = i2 by omega]; exact hi2o⟩
    have hcard := card_le_of_mem_Icc I a b hab
    have hCC : C * Real.log (2 + H) ≤ |C| * Real.log (2 + H) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) hlog0
    nlinarith
  · have hB : ∀ m ∈ I, (∃ i, a ≤ i ∧ i < m ∧ Odd (amusical^[i] y)) →
        ∀ i, m ≤ i → i < b → ¬ Odd (amusical^[i] y) :=
      fun m hm h1 i hi1 hi2 ho => hA ⟨m, hm, h1, i, hi1, hi2, ho⟩
    set I1 := I.filter fun m => ∀ i, a ≤ i → i < m → ¬ Odd (amusical^[i] y) with hI1
    set I2 := I.filter fun m => ¬ ∀ i, a ≤ i → i < m → ¬ Odd (amusical^[i] y) with hI2
    have hsplit : I1.card + I2.card = I.card := Finset.card_filter_add_card_filter_not _
    have hI1ne : I1.Nonempty :=
      ⟨a, Finset.mem_filter.2 ⟨haI, fun i h1 h2 => absurd h2 (by omega)⟩⟩
    set m1 := I1.max' hI1ne with hm1def
    have hm1 : m1 ∈ I1 := I1.max'_mem hI1ne
    have hm1I : m1 ∈ I := (Finset.mem_filter.1 hm1).1
    have hc1 : (I1.card : ℝ) ≤ ((m1 - a : ℕ) : ℝ) + 1 :=
      card_le_of_mem_Icc I1 a m1 fun m hm =>
        ⟨(hab m (Finset.mem_filter.1 hm).1).1, I1.le_max' m hm⟩
    have hlen1 : ((m1 - a : ℕ) : ℝ) ≤ 6 * Real.log (2 + H) := by
      have ham1 := (hab m1 hm1I).1
      refine even_run_len y a (m1 - a) H
        (fun i h1 h2 => (Finset.mem_filter.1 hm1).2 i h1 (by omega)) (hge1 a haI) ?_
      rw [show a + (m1 - a) = m1 by omega]
      exact hleH m1 hm1I
    have hc2 : (I2.card : ℝ) ≤ 6 * Real.log (2 + H) + 1 := by
      rcases I2.eq_empty_or_nonempty with h2e | h2ne
      · rw [h2e, Finset.card_empty, Nat.cast_zero]
        linarith
      set m2 := I2.min' h2ne with hm2def
      have hm2 : m2 ∈ I2 := I2.min'_mem h2ne
      have hm2I : m2 ∈ I := (Finset.mem_filter.1 hm2).1
      have hm2b := (hab m2 hm2I).2
      have hodd : ∃ i, a ≤ i ∧ i < m2 ∧ Odd (amusical^[i] y) := by
        by_contra hno
        exact (Finset.mem_filter.1 hm2).2 fun i h1 h2 ho => hno ⟨i, h1, h2, ho⟩
      have hev := hB m2 hm2I hodd
      have hc : (I2.card : ℝ) ≤ ((b - m2 : ℕ) : ℝ) + 1 :=
        card_le_of_mem_Icc I2 m2 b fun m hm =>
          ⟨I2.min'_le m hm, (hab m (Finset.mem_filter.1 hm).1).2⟩
      have hlen : ((b - m2 : ℕ) : ℝ) ≤ 6 * Real.log (2 + H) := by
        refine even_run_len y m2 (b - m2) H (fun i h1 h2 => hev i h1 (by omega))
          (hge1 m2 hm2I) ?_
        rw [show m2 + (b - m2) = b by omega]
        exact hleH b hbI
      linarith
    have : (I.card : ℝ) = I1.card + I2.card := by rw [← hsplit]; push_cast; ring
    rw [this]
    nlinarith

/-- **Repetition-free window.**  Any finite subset of an orbit lies in a forward window
`y, U y, …, U^T y` without repetitions. -/
theorem exists_injective_window (x : ℤ) (S : Finset ℤ) (hS : ∀ s ∈ S, s ∈ amusicalOrbit x) :
    ∃ y : ℤ, ∃ T : ℕ, (∀ i j, i ≤ T → j ≤ T → amusical^[i] y = amusical^[j] y → i = j) ∧
      ∀ s ∈ S, ∃ i ≤ T, amusical^[i] y = s := by
  classical
  have hpow : ∀ (n : ℕ) (z : ℤ), (amusicalPerm ^ n) z = amusical^[n] z := by
    intro n z; rw [Equiv.Perm.coe_pow]; rfl
  have hcancel : ∀ (z : ℤ) (i j : ℕ), i < j → amusical^[i] z = amusical^[j] z →
      amusical^[j - i] z = z := by
    intro z i j hij h
    apply amusical_injective.iterate i
    rw [← Function.iterate_add_apply, show i + (j - i) = j by omega]
    exact h.symm
  have hS' : ∀ s ∈ S, ∃ k : ℤ, (amusicalPerm ^ k) x = s := fun s hs => hS s hs
  by_cases hper : ∃ p, 0 < p ∧ amusical^[p] x = x
  · set P := Nat.find hper with hPdef
    have hP : 0 < P ∧ amusical^[P] x = x := Nat.find_spec hper
    refine ⟨x, P - 1, ?_, ?_⟩
    · intro i j hi hj hij
      rcases lt_trichotomy i j with h | h | h
      · exact absurd ⟨by omega, hcancel x i j h hij⟩ (Nat.find_min hper (m := j - i) (by omega))
      · exact h
      · exact absurd ⟨by omega, hcancel x j i h hij.symm⟩
          (Nat.find_min hper (m := i - j) (by omega))
    · intro s hs
      obtain ⟨k, rfl⟩ := hS' s hs
      have hPpos : (0 : ℤ) < P := by exact_mod_cast hP.1
      have hPfix : (amusicalPerm ^ (P : ℤ)) x = x := by rw [zpow_natCast, hpow]; exact hP.2
      have hnn : 0 ≤ k % (P : ℤ) := Int.emod_nonneg _ hPpos.ne'
      have hlt : k % (P : ℤ) < P := Int.emod_lt_of_pos _ hPpos
      have hfix : ((amusicalPerm ^ (P : ℤ)) ^ (k / P)) x = x :=
        Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hPfix _
      refine ⟨(k % P).toNat, by omega, ?_⟩
      calc amusical^[(k % P).toNat] x = (amusicalPerm ^ (((k % P).toNat : ℕ) : ℤ)) x := by
            rw [zpow_natCast, hpow]
        _ = (amusicalPerm ^ (k % P)) x := by rw [Int.toNat_of_nonneg hnn]
        _ = (amusicalPerm ^ (k % P)) (((amusicalPerm ^ (P : ℤ)) ^ (k / P)) x) := by rw [hfix]
        _ = (amusicalPerm ^ k) x := by
            rw [← zpow_mul, ← Equiv.Perm.mul_apply, ← zpow_add, Int.emod_add_mul_ediv]
  · push Not at hper
    rcases S.eq_empty_or_nonempty with hSe | hSne
    · exact ⟨x, 0, fun i j hi hj _ => by omega, by simp [hSe]⟩
    choose! J hJ using hS'
    set j0 := S.inf' hSne J with hj0
    set j1 := S.sup' hSne J with hj1
    have hcomm : ∀ (n : ℕ) (z : ℤ),
        amusical^[n] ((amusicalPerm ^ j0) z) = (amusicalPerm ^ j0) (amusical^[n] z) := by
      intro n z
      rw [← hpow, ← hpow, ← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, ← zpow_natCast,
        ← zpow_add, ← zpow_add, add_comm]
    refine ⟨(amusicalPerm ^ j0) x, (j1 - j0).toNat, ?_, ?_⟩
    · have hne : ∀ i j : ℕ, i < j →
          amusical^[i] ((amusicalPerm ^ j0) x) ≠ amusical^[j] ((amusicalPerm ^ j0) x) := by
        intro i j hij h
        have h1 := hcancel _ i j hij h
        rw [hcomm] at h1
        exact hper (j - i) (by omega) ((amusicalPerm ^ j0).injective h1)
      intro i j _ _ hij
      rcases lt_trichotomy i j with h | h | h
      · exact absurd hij (hne i j h)
      · exact h
      · exact absurd hij.symm (hne j i h)
    · intro s hs
      have hle0 : j0 ≤ J s := Finset.inf'_le J hs
      have hle1 : J s ≤ j1 := Finset.le_sup' J hs
      refine ⟨(J s - j0).toNat, by omega, ?_⟩
      rw [← hpow, ← zpow_natCast, Int.toNat_of_nonneg (by omega), ← Equiv.Perm.mul_apply,
        ← zpow_add, sub_add_cancel, hJ s hs]

/-- `log` is sublinear: `K (A log (2 + H) + 3) < H` for some `H`. -/
theorem exists_nat_gt_log_bound (K A : ℝ) (hK : 0 ≤ K) (hA : 0 ≤ A) :
    ∃ H : ℕ, K * (A * Real.log (2 + H) + 3) < H := by
  set M := 2 * K * A + 3 * K + 3 with hM
  refine ⟨⌈M ^ 2⌉₊, ?_⟩
  set H : ℕ := ⌈M ^ 2⌉₊
  have hH0 : (0 : ℝ) ≤ H := H.cast_nonneg
  have hHM : M ^ 2 ≤ H := Nat.le_ceil _
  set u := Real.sqrt (2 + H) with hu
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = 2 + H := Real.sq_sqrt (by linarith)
  have hM3 : 3 ≤ M := by nlinarith [mul_nonneg hK hA]
  have huM : M ≤ u := by nlinarith
  have hlog : Real.log (2 + H) ≤ 2 * u := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < u by linarith)
    rw [hu, Real.log_sqrt (by linarith)] at h1
    rw [← hu] at h1
    linarith
  have h2 : K * (A * Real.log (2 + H) + 3) ≤ K * (A * (2 * u) + 3) := by
    gcongr
  have h3 : K * (A * (2 * u) + 3) ≤ (M - 3) * u := by
    rw [hM]; nlinarith [mul_nonneg hK hA]
  nlinarith

end CollatzMoonshot.Amusical
