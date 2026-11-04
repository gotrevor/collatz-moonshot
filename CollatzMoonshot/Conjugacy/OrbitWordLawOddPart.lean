/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.OrbitWordLawDensity

/-!
# The orbit word law: odd parts and large 2-adic valuation

* `logDens0OddPart_holds` proves `LogDens0OddPart`: the starts `2^a m` with `m` odd and in `B`
  carry log-weight at most `∑_a 2^(−a) ≤ 2` times that of the odd `m` in `B`.
* `summableLargeTwoAdic_holds` proves `SummableLargeTwoAdic`: writing `n = 2^a (2k + 1)`, the
  condition `ε size (2k + 1) < a` forces `2k + 1 < 2^⌈a/ε⌉`, so the weight at valuation `a` is at
  most `2^(−a) (1 + ⌈a/ε⌉)`, which is summable.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord
open TaoCollatz

/-- `ν₂(2^a m) = a` for odd `m`. -/
theorem padicValNat_two_pow_mul_odd (a : ℕ) {m : ℕ} (hm : m % 2 = 1) :
    padicValNat 2 (2 ^ a * m) = a := by
  rw [padicValNat.mul (by positivity) (by omega), padicValNat.prime_pow,
    padicValNat_two_of_odd hm, add_zero]

/-- The odd part of `2^a m` is `m`, for odd `m`. -/
theorem oddPart_two_pow_mul_odd (a : ℕ) {m : ℕ} (hm : m % 2 = 1) : oddPart (2 ^ a * m) = m := by
  rw [oddPart, padicValNat_two_pow_mul_odd a hm, Nat.mul_div_cancel_left _ (by positivity)]

/-- `(a, m) ↦ 2^a m` is injective on odd `m`. -/
theorem two_pow_mul_odd_inj {a a' m m' : ℕ} (hm : m % 2 = 1) (hm' : m' % 2 = 1)
    (h : 2 ^ a * m = 2 ^ a' * m') : a = a' ∧ m = m' := by
  have ha : a = a' := by
    rw [← padicValNat_two_pow_mul_odd a hm, h, padicValNat_two_pow_mul_odd a' hm']
  subst ha
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (by positivity) h⟩

/-! ## Odd parts -/

/-- **The log-weight of the starts with odd part in `B`** is at most twice that of the odd starts
in `B`. -/
theorem sum_oddPart_le (B : ℕ → Prop) [DecidablePred B] (X : ℕ) :
    ∑ n ∈ (Finset.Ico 1 X).filter (fun n => B (oddPart n)), (1 : ℝ) / n ≤
      2 * ∑ n ∈ (Finset.Ico 1 X).filter (fun n => n % 2 = 1 ∧ B n), (1 : ℝ) / n := by
  set F := (Finset.Ico 1 X).filter (fun n => n % 2 = 1 ∧ B n) with hF
  have hsub : (Finset.Ico 1 X).filter (fun n => B (oddPart n)) ⊆
      (Finset.range X ×ˢ F).image (fun p : ℕ × ℕ => 2 ^ p.1 * p.2) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ico] at hn
    obtain ⟨⟨h1, hX⟩, hB⟩ := hn
    have hpos : 0 < n := h1
    have hodd := oddPart_odd hpos
    have hmul := two_pow_mul_oddPart n
    have hm1 : 1 ≤ oddPart n := by omega
    have h2a : 2 ^ padicValNat 2 n ≤ n := by
      calc 2 ^ padicValNat 2 n = 2 ^ padicValNat 2 n * 1 := (mul_one _).symm
        _ ≤ 2 ^ padicValNat 2 n * oddPart n := Nat.mul_le_mul_left _ hm1
        _ = n := hmul
    have hmn : oddPart n ≤ n := by
      calc oddPart n = 1 * oddPart n := (one_mul _).symm
        _ ≤ 2 ^ padicValNat 2 n * oddPart n := Nat.mul_le_mul_right _ (Nat.one_le_two_pow)
        _ = n := hmul
    have haX : padicValNat 2 n < X :=
      lt_of_lt_of_le (Nat.lt_two_pow_self) (le_trans h2a (le_of_lt hX))
    simp only [Finset.mem_image, Finset.mem_product, Finset.mem_range, hF, Finset.mem_filter,
      Finset.mem_Ico]
    exact ⟨(padicValNat 2 n, oddPart n), ⟨haX, ⟨hm1, by omega⟩, hodd, hB⟩, hmul⟩
  have hinj : Set.InjOn (fun p : ℕ × ℕ => 2 ^ p.1 * p.2) (Finset.range X ×ˢ F : Finset _) := by
    intro p hp q hq h
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, hF, Finset.mem_filter] at hp hq
    obtain ⟨h1, h2⟩ := two_pow_mul_odd_inj hp.2.2.1 hq.2.2.1 h
    exact Prod.ext h1 h2
  calc ∑ n ∈ (Finset.Ico 1 X).filter (fun n => B (oddPart n)), (1 : ℝ) / n
      ≤ ∑ n ∈ (Finset.range X ×ˢ F).image (fun p : ℕ × ℕ => 2 ^ p.1 * p.2), (1 : ℝ) / n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => by positivity
    _ = ∑ p ∈ Finset.range X ×ˢ F, (1 : ℝ) / ((2 ^ p.1 * p.2 : ℕ) : ℝ) := Finset.sum_image hinj
    _ = (∑ a ∈ Finset.range X, (1 / 2 : ℝ) ^ a) * ∑ m ∈ F, (1 : ℝ) / m := by
        rw [Finset.sum_product, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        push_cast
        rw [div_pow, one_pow, div_mul_div_comm, one_mul]
    _ ≤ 2 * ∑ m ∈ F, (1 : ℝ) / m :=
        mul_le_mul_of_nonneg_right (sum_geometric_two_le X)
          (Finset.sum_nonneg fun m _ => by positivity)

/-- **Odd parts** (`LogDens0OddPart`). -/
theorem logDens0OddPart_holds : LogDens0OddPart := by
  classical
  intro B hB
  have h2 := hB.const_mul 2
  rw [mul_zero] at h2
  refine squeeze_zero (fun X => logWeight_nonneg _ X) (fun X => ?_) h2
  rw [← mul_div_assoc]
  refine div_le_div_of_nonneg_right ?_ (Real.log_natCast_nonneg X)
  calc _ = ∑ n ∈ (Finset.Ico 1 X).filter (fun n => B (oddPart n)), (1 : ℝ) / n := by congr
    _ ≤ 2 * ∑ n ∈ (Finset.Ico 1 X).filter (fun n => n % 2 = 1 ∧ B n), (1 : ℝ) / n :=
        sum_oddPart_le B X
    _ = _ := by congr

/-! ## Large 2-adic valuation -/

/-- The reciprocals of the odd numbers below `2^L` sum to at most `1 + L`. -/
theorem sum_inv_odd_le (L : ℕ) :
    ∑ k ∈ Finset.range (2 ^ L), (1 : ℝ) / (2 * k + 1) ≤ 1 + L := by
  have h1 : ∑ k ∈ Finset.range (2 ^ L), (1 : ℝ) / (2 * k + 1) ≤
      ∑ k ∈ Finset.range (2 ^ L), (1 : ℝ) / (k + 1) :=
    Finset.sum_le_sum fun k _ => one_div_le_one_div_of_le (by positivity) (by linarith
      [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  have h2 : ∑ k ∈ Finset.range (2 ^ L), (1 : ℝ) / (k + 1) = (harmonic (2 ^ L) : ℝ) := by
    rw [harmonic]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [one_div]
  have h3 := harmonic_le_one_add_log (2 ^ L)
  push_cast at h3
  rw [Real.log_pow] at h3
  have h4 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have h5 : (L : ℝ) * Real.log 2 ≤ L := mul_le_of_le_one_right (Nat.cast_nonneg _) h4
  linarith

/-- **Large 2-adic valuation has finite log-weight** (`SummableLargeTwoAdic`). -/
theorem summableLargeTwoAdic_holds : SummableLargeTwoAdic := by
  classical
  intro ε hε
  set f : ℕ → ℝ := fun n =>
    if ε * Nat.size (oddPart n) < padicValNat 2 n then (1 : ℝ) / n else 0 with hf
  set g : ℕ × ℕ → ℕ := fun p => 2 ^ p.1 * (2 * p.2 + 1) with hgdef
  have hg : Function.Injective g := fun p q h => by
    obtain ⟨h1, h2⟩ := two_pow_mul_odd_inj (by omega) (by omega) h
    exact Prod.ext h1 (by omega)
  have hf0 : ∀ n ∉ Set.range g, f n = 0 := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · simp [hf, h0]
    · exfalso
      apply hn
      refine ⟨(padicValNat 2 n, oddPart n / 2), ?_⟩
      have hodd := oddPart_odd hpos
      simp only [hgdef]
      rw [show 2 * (oddPart n / 2) + 1 = oddPart n by omega]
      exact two_pow_mul_oddPart n
  rw [← hg.summable_iff hf0]
  set h : ℕ × ℕ → ℝ := fun p => if ε * Nat.size (2 * p.2 + 1) < p.1 then
    (1 / 2 : ℝ) ^ p.1 * (1 / (2 * p.2 + 1)) else 0 with hhdef
  have hfg : f ∘ g = h := by
    funext p
    simp only [Function.comp_apply, hf, hgdef, hhdef]
    rw [oddPart_two_pow_mul_odd _ (by omega), padicValNat_two_pow_mul_odd _ (by omega)]
    split_ifs
    · push_cast
      rw [div_pow, one_pow, div_mul_div_comm, one_mul]
    · rfl
  rw [hfg]
  have hh0 : 0 ≤ h := fun p => by
    simp only [hhdef, Pi.zero_apply]
    split_ifs <;> positivity
  -- for fixed `a`, only `k < 2^L` contribute, `L = ⌈a/ε⌉`
  have hsupp : ∀ a k : ℕ, 2 ^ ⌈(a : ℝ) / ε⌉₊ ≤ k → h (a, k) = 0 := by
    intro a k hk
    simp only [hhdef]
    rw [if_neg]
    push Not
    have hsz : ⌈(a : ℝ) / ε⌉₊ < Nat.size (2 * k + 1) := Nat.lt_size.mpr (by omega)
    have hsz' : (a : ℝ) / ε < Nat.size (2 * k + 1) :=
      lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hsz)
    rw [div_lt_iff₀ hε] at hsz'
    linarith
  have hsum : ∀ a : ℕ, ∑' k, h (a, k) =
      ∑ k ∈ Finset.range (2 ^ ⌈(a : ℝ) / ε⌉₊), h (a, k) := fun a =>
    tsum_eq_sum fun k hk => hsupp a k (by simpa using hk)
  refine (summable_prod_of_nonneg hh0).2 ⟨fun a => ?_, ?_⟩
  · exact summable_of_ne_finset_zero (s := Finset.range (2 ^ ⌈(a : ℝ) / ε⌉₊))
      fun k hk => hsupp a k (by simpa using hk)
  · have hbound : ∀ a : ℕ, ∑' k, h (a, k) ≤ (1 / 2 : ℝ) ^ a * (2 + a / ε) := by
      intro a
      rw [hsum a]
      calc ∑ k ∈ Finset.range (2 ^ ⌈(a : ℝ) / ε⌉₊), h (a, k)
          ≤ ∑ k ∈ Finset.range (2 ^ ⌈(a : ℝ) / ε⌉₊), (1 / 2 : ℝ) ^ a * (1 / (2 * k + 1)) := by
            refine Finset.sum_le_sum fun k _ => ?_
            simp only [hhdef]
            split_ifs
            · exact le_rfl
            · positivity
        _ = (1 / 2 : ℝ) ^ a * ∑ k ∈ Finset.range (2 ^ ⌈(a : ℝ) / ε⌉₊), 1 / (2 * (k : ℝ) + 1) := by
            rw [Finset.mul_sum]
        _ ≤ (1 / 2 : ℝ) ^ a * (1 + ⌈(a : ℝ) / ε⌉₊) :=
            mul_le_mul_of_nonneg_left (sum_inv_odd_le _) (by positivity)
        _ ≤ (1 / 2 : ℝ) ^ a * (2 + a / ε) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ a / ε by positivity)
            linarith
    refine Summable.of_nonneg_of_le (fun a => tsum_nonneg fun k => hh0 (a, k)) hbound ?_
    have h1 : Summable fun a : ℕ => (1 / 2 : ℝ) ^ a * 2 := summable_geometric_two.mul_right 2
    have h2 : Summable fun a : ℕ => ((a : ℝ) ^ 1 * (1 / 2 : ℝ) ^ a) * (1 / ε) :=
      (summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num)).mul_right (1 / ε)
    refine (h1.add h2).congr fun a => ?_
    ring

end CollatzMoonshot.Conjugacy
