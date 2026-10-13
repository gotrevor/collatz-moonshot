/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Amusical
import CollatzMoonshot.AmusicalWindow.Count

/-!
# Window minima of the amusical permutation

`n` is an `L`-window minimum when no orbit point within `L` steps either way lies below it.
Every orbit minimum is one, so the density of `L`-window minima bounds the upper density of
orbit minima from above for each `L`: the unconditional half of `AmusicalMinimaDensity`.

For large `n` the first `L` forward branches of `n` depend only on `n mod 2^(2L)` (Matthews-Watts),
the first `L` backward branches only on `n mod 3^L`, and the CRT makes the two independent.  Each
forward step is `×3/2` or `×3/4` with frequency `1/2` each, each backward step `×2/3` or `×4/3`
with frequency `1/3, 2/3`, and for large `n` the window condition is that every prefix product
exceeds `1`.  The resulting density is `fwdSurv L * bwdSurv L`, the two survival probabilities
of the multiplicative walks.  Exact values: `δ₁ = 1/3` (Conway's "congruence paradox": the local
minima are `±2 mod 6`), `δ₂ = 2/9`, `δ₃ = 1/6`, `δ₄ = 4/27`; then `δ₁₀ ≈ 0.0883`,
`δ₂₀ ≈ 0.0676`, `δ₄₀ ≈ 0.0566`, decreasing to `p_f · p_b ≈ 0.0498`.  Empirical counts over
`1..2·10^5` agree to about `10^-4` for `L ≤ 20` (`scripts/amusical/window.py`).
-/

namespace CollatzMoonshot.Amusical

/-- No orbit point within `L` steps of `n`, in either direction, lies below `n`. -/
def IsWindowMin (L : ℕ) (n : ℤ) : Prop :=
  ∀ t : ℕ, 1 ≤ t → t ≤ L → n ≤ amusical^[t] n ∧ n ≤ amusicalInv^[t] n

theorem amusical_iterate_eq_perm_pow (t : ℕ) (n : ℤ) :
    amusical^[t] n = (amusicalPerm ^ (t : ℤ)) n := by
  rw [zpow_natCast]
  induction t generalizing n with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', ih, pow_succ', Equiv.Perm.mul_apply]; rfl

theorem amusicalInv_iterate_eq_perm_pow (t : ℕ) (n : ℤ) :
    amusicalInv^[t] n = (amusicalPerm ^ (-(t : ℤ))) n := by
  rw [zpow_neg, zpow_natCast]
  induction t generalizing n with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ, mul_inv_rev, Equiv.Perm.mul_apply]; rfl

/-! ## Residue-class affine structure

The next four lemmas are the algebraic core of the Matthews--Watts residue argument.  They
make no asymptotic approximation: on a class modulo `4^L` (respectively `3^L`), every iterate
through time `L` is an affine function of the class parameter, with positive integral slope.
-/

theorem amusical_add_four_mul (n k : ℤ) :
    amusical (n + 4 * k) = amusical n + (if n % 2 = 0 then 6 * k else 3 * k) := by
  unfold amusical
  split_ifs <;> omega

theorem amusicalInv_add_three_mul (n k : ℤ) :
    amusicalInv (n + 3 * k) = amusicalInv n + (if n % 3 = 0 then 2 * k else 4 * k) := by
  unfold amusicalInv
  split_ifs <;> omega

/-- Product of the exact translation factors encountered along a forward orbit prefix. -/
def amusicalForwardMultiplier : ℕ → ℤ → ℤ
  | 0, _ => 1
  | t + 1, n => (if n % 2 = 0 then 6 else 3) * amusicalForwardMultiplier t (amusical n)

/-- Product of the exact translation factors encountered along a backward orbit prefix. -/
def amusicalBackwardMultiplier : ℕ → ℤ → ℤ
  | 0, _ => 1
  | t + 1, n => (if n % 3 = 0 then 2 else 4) * amusicalBackwardMultiplier t (amusicalInv n)

/-- Number of even branches in a forward orbit prefix. -/
def amusicalForwardEvenCount : ℕ → ℤ → ℕ
  | 0, _ => 0
  | t + 1, n => (if n % 2 = 0 then 1 else 0) + amusicalForwardEvenCount t (amusical n)

/-- Number of `×4/3` branches in a backward orbit prefix. -/
def amusicalBackwardFourCount : ℕ → ℤ → ℕ
  | 0, _ => 0
  | t + 1, n => (if n % 3 = 0 then 0 else 1) + amusicalBackwardFourCount t (amusicalInv n)

/-- The forward branch word, with `true` marking a `×3/4` (odd) step. -/
def amusicalForwardWord (L : ℕ) (n : ℤ) (i : Fin L) : Bool :=
  decide (amusical^[i.val] n % 2 ≠ 0)

/-- The backward branch word, with `true` marking a `×4/3` step. -/
def amusicalBackwardWord (L : ℕ) (n : ℤ) (i : Fin L) : Bool :=
  decide (amusicalInv^[i.val] n % 3 ≠ 0)

/-- The recursive forward counter is exactly the number of even branches in the orbit trace. -/
theorem amusicalForwardEvenCount_eq_count (t : ℕ) (n : ℤ) :
    amusicalForwardEvenCount t n =
      Nat.count (fun i : ℕ => amusical^[i] n % 2 = 0) t := by
  induction t generalizing n with
  | zero => simp [amusicalForwardEvenCount]
  | succ t ih =>
      rw [amusicalForwardEvenCount, Nat.count_succ']
      rw [ih]
      simp only [Function.iterate_zero_apply]
      rw [add_comm]
      apply congrArg₂ (fun a b : ℕ => a + b)
      · rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
        apply congrArg Finset.card
        ext i
        simp [Function.iterate_succ_apply]
      · rfl

/-- The recursive backward counter is exactly the number of `×4/3` branches in the trace. -/
theorem amusicalBackwardFourCount_eq_count (t : ℕ) (n : ℤ) :
    amusicalBackwardFourCount t n =
      Nat.count (fun i : ℕ => amusicalInv^[i] n % 3 ≠ 0) t := by
  induction t generalizing n with
  | zero => simp [amusicalBackwardFourCount]
  | succ t ih =>
      rw [amusicalBackwardFourCount, Nat.count_succ']
      rw [ih]
      simp only [Function.iterate_zero_apply]
      rw [add_comm]
      apply congrArg₂ (fun a b : ℕ => a + b)
      · rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
        apply congrArg Finset.card
        ext i
        simp [Function.iterate_succ_apply]
      · by_cases h : n % 3 = 0 <;> simp [h]

/-- The marked forward letters and the even branches partition every prefix. -/
theorem amusicalForwardWord_true_card_add_evenCount (L t : ℕ) (ht : t ≤ L) (n : ℤ) :
    (Finset.univ.filter fun i : Fin L =>
      i.val < t ∧ amusicalForwardWord L n i = true).card +
        amusicalForwardEvenCount t n = t := by
  rw [amusicalForwardEvenCount_eq_count]
  have hcard := card_filter_fin_lt_eq_count L t ht
    (fun j => amusical^[j] n % 2 ≠ 0)
  have hword :
      (Finset.univ.filter fun i : Fin L =>
        i.val < t ∧ amusicalForwardWord L n i = true).card =
          Nat.count (fun j => amusical^[j] n % 2 ≠ 0) t := by
    rw [← hcard]
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro i _
    simp [amusicalForwardWord]
  rw [hword]
  exact count_not_add_count (fun j => amusical^[j] n % 2 = 0) t

/-- The number of marked backward letters is the recursive `×4/3` branch count. -/
theorem amusicalBackwardWord_true_card_eq_fourCount (L t : ℕ) (ht : t ≤ L) (n : ℤ) :
    (Finset.univ.filter fun i : Fin L =>
      i.val < t ∧ amusicalBackwardWord L n i = true).card =
        amusicalBackwardFourCount t n := by
  rw [amusicalBackwardFourCount_eq_count]
  rw [← card_filter_fin_lt_eq_count L t ht]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro i _
  simp [amusicalBackwardWord]

theorem amusicalForwardMultiplier_eq (t : ℕ) (n : ℤ) :
    amusicalForwardMultiplier t n =
      (3 : ℤ) ^ t * 2 ^ amusicalForwardEvenCount t n := by
  induction t generalizing n with
  | zero => simp [amusicalForwardMultiplier, amusicalForwardEvenCount]
  | succ t ih =>
      rw [amusicalForwardMultiplier, amusicalForwardEvenCount, ih, pow_succ]
      by_cases h : n % 2 = 0 <;> simp [h] <;> ring

theorem amusicalBackwardMultiplier_eq (t : ℕ) (n : ℤ) :
    amusicalBackwardMultiplier t n =
      (2 : ℤ) ^ (t + amusicalBackwardFourCount t n) := by
  induction t generalizing n with
  | zero => simp [amusicalBackwardMultiplier, amusicalBackwardFourCount]
  | succ t ih =>
      rw [amusicalBackwardMultiplier, amusicalBackwardFourCount, ih]
      by_cases h : n % 3 = 0 <;> simp [h] <;> ring

theorem amusicalForwardMultiplier_pos (t : ℕ) (n : ℤ) :
    0 < amusicalForwardMultiplier t n := by
  induction t generalizing n with
  | zero => simp [amusicalForwardMultiplier]
  | succ t ih =>
      simp only [amusicalForwardMultiplier]
      by_cases h : n % 2 = 0 <;> simp [h] <;> have := ih (amusical n) <;> omega

theorem amusicalBackwardMultiplier_pos (t : ℕ) (n : ℤ) :
    0 < amusicalBackwardMultiplier t n := by
  induction t generalizing n with
  | zero => simp [amusicalBackwardMultiplier]
  | succ t ih =>
      simp only [amusicalBackwardMultiplier]
      by_cases h : n % 3 = 0 <;> simp [h] <;> have := ih (amusicalInv n) <;> omega

/-- Exact forward affine slope on a residue class modulo `4^L`. -/
theorem amusical_iterate_add_pow_four_mul_exact (L t : ℕ) (ht : t ≤ L) (n k : ℤ) :
    amusical^[t] (n + (4 : ℤ) ^ L * k) = amusical^[t] n +
      (4 : ℤ) ^ (L - t) * amusicalForwardMultiplier t n * k := by
  induction L generalizing t n k with
  | zero =>
      obtain rfl : t = 0 := by omega
      simp [amusicalForwardMultiplier]
  | succ L ih =>
      cases t with
      | zero => simp [amusicalForwardMultiplier]
      | succ t =>
          have ht' : t ≤ L := by omega
          let d : ℤ := if n % 2 = 0 then 6 else 3
          have hih := ih t ht' (amusical n) (d * k)
          rw [Function.iterate_succ_apply, Function.iterate_succ_apply, pow_succ']
          rw [show n + 4 * 4 ^ L * k = n + 4 * (4 ^ L * k) by ring]
          rw [amusical_add_four_mul]
          by_cases h : n % 2 = 0 <;> simp [d, h, amusicalForwardMultiplier] at hih ⊢ <;>
            convert hih using 1 <;> ring

/-- Exact backward affine slope on a residue class modulo `3^L`. -/
theorem amusicalInv_iterate_add_pow_three_mul_exact (L t : ℕ) (ht : t ≤ L) (n k : ℤ) :
    amusicalInv^[t] (n + (3 : ℤ) ^ L * k) = amusicalInv^[t] n +
      (3 : ℤ) ^ (L - t) * amusicalBackwardMultiplier t n * k := by
  induction L generalizing t n k with
  | zero =>
      obtain rfl : t = 0 := by omega
      simp [amusicalBackwardMultiplier]
  | succ L ih =>
      cases t with
      | zero => simp [amusicalBackwardMultiplier]
      | succ t =>
          have ht' : t ≤ L := by omega
          let d : ℤ := if n % 3 = 0 then 2 else 4
          have hih := ih t ht' (amusicalInv n) (d * k)
          rw [Function.iterate_succ_apply, Function.iterate_succ_apply, pow_succ']
          rw [show n + 3 * 3 ^ L * k = n + 3 * (3 ^ L * k) by ring]
          rw [amusicalInv_add_three_mul]
          by_cases h : n % 3 = 0 <;> simp [d, h, amusicalBackwardMultiplier] at hih ⊢ <;>
            convert hih using 1 <;> ring

theorem amusical_iterate_add_pow_four_mul_slope (L t : ℕ) (ht : t ≤ L) (n k : ℤ) :
    amusical^[t] (n + (4 : ℤ) ^ L * k) = amusical^[t] n +
      (4 : ℤ) ^ (L - t) * 3 ^ t * 2 ^ amusicalForwardEvenCount t n * k := by
  rw [amusical_iterate_add_pow_four_mul_exact L t ht, amusicalForwardMultiplier_eq]
  ring

theorem amusicalInv_iterate_add_pow_three_mul_slope (L t : ℕ) (ht : t ≤ L) (n k : ℤ) :
    amusicalInv^[t] (n + (3 : ℤ) ^ L * k) = amusicalInv^[t] n +
      (3 : ℤ) ^ (L - t) * 2 ^ (t + amusicalBackwardFourCount t n) * k := by
  rw [amusicalInv_iterate_add_pow_three_mul_exact L t ht, amusicalBackwardMultiplier_eq]

/-- A residue modulo `4^L` fixes the complete forward branch word of length `L`. -/
theorem amusicalForwardWord_add_pow_four_mul (L : ℕ) (n k : ℤ) :
    amusicalForwardWord L (n + (4 : ℤ) ^ L * k) = amusicalForwardWord L n := by
  funext i
  unfold amusicalForwardWord
  rw [amusical_iterate_add_pow_four_mul_slope L i.val i.isLt.le]
  obtain ⟨d, hd⟩ : ∃ d, L - i.val = d + 1 := by
    use L - i.val - 1
    omega
  rw [hd, pow_succ]
  simp [Int.add_emod, Int.mul_emod]

/-- A residue modulo `3^L` fixes the complete backward branch word of length `L`. -/
theorem amusicalBackwardWord_add_pow_three_mul (L : ℕ) (n k : ℤ) :
    amusicalBackwardWord L (n + (3 : ℤ) ^ L * k) = amusicalBackwardWord L n := by
  funext i
  unfold amusicalBackwardWord
  rw [amusicalInv_iterate_add_pow_three_mul_slope L i.val i.isLt.le]
  obtain ⟨d, hd⟩ : ∃ d, L - i.val = d + 1 := by
    use L - i.val - 1
    omega
  rw [hd, pow_succ]
  simp [Int.add_emod, Int.mul_emod]

/-! ## Exact branch-word fibers -/

open Finset WindowCount

theorem amusicalForwardWord_succ (L : ℕ) (n : ℤ) :
    amusicalForwardWord (L + 1) n =
      Fin.cons (decide (n % 2 ≠ 0)) (amusicalForwardWord L (amusical n)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [amusicalForwardWord]
  · simp [amusicalForwardWord, Function.iterate_succ_apply]

theorem amusicalBackwardWord_succ (L : ℕ) (n : ℤ) :
    amusicalBackwardWord (L + 1) n =
      Fin.cons (decide (n % 3 ≠ 0)) (amusicalBackwardWord L (amusicalInv n)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [amusicalBackwardWord]
  · simp [amusicalBackwardWord, Function.iterate_succ_apply]

theorem amusicalForwardWord_emod (L : ℕ) (x : ℤ) :
    amusicalForwardWord L x = amusicalForwardWord L (x % 4 ^ L) := by
  conv_lhs => rw [← Int.emod_add_mul_ediv x (4 ^ L)]
  exact amusicalForwardWord_add_pow_four_mul L _ _

theorem amusicalBackwardWord_emod (L : ℕ) (x : ℤ) :
    amusicalBackwardWord L x = amusicalBackwardWord L (x % 3 ^ L) := by
  conv_lhs => rw [← Int.emod_add_mul_ediv x (3 ^ L)]
  exact amusicalBackwardWord_add_pow_three_mul L _ _

/-- An affine map with slope coprime to `N` is injective modulo `N` on `[0, N)`. -/
theorem injMod_affine (N : ℕ) (u e : ℤ) (hu : IsCoprime u (N : ℤ)) :
    ∀ a < N, ∀ b < N, (u * (a : ℤ) + e) % N = (u * (b : ℤ) + e) % N → a = b := by
  intro a ha b hb h
  have h1 : (N : ℤ) ∣ u * ((b : ℤ) - a) := by
    have hdiv := Int.ModEq.dvd h
    rw [show u * (b : ℤ) + e - (u * a + e) = u * ((b : ℤ) - a) by ring] at hdiv
    exact hdiv
  have h2 : (N : ℤ) ∣ (b : ℤ) - a := hu.symm.dvd_of_dvd_mul_left h1
  have h3 := Int.eq_zero_of_abs_lt_dvd h2 (by rw [abs_lt]; constructor <;> omega)
  omega

theorem count_congr' {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q]
    (h : ∀ n, p n ↔ q n) (X : ℕ) : Nat.count p X = Nat.count q X := by
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  exact congrArg _ (Finset.filter_congr fun n _ => h n)

theorem count_false' (X : ℕ) : Nat.count (fun _ => False) X = 0 := by
  rw [Nat.count_eq_card_filter_range]
  simp

/-- Every forward word of length `L` has exactly `2^L` residue classes modulo `4^L`. -/
theorem count_amusicalForwardWord_eq (L : ℕ) (w : Fin L → Bool) :
    Nat.count (fun r : ℕ => amusicalForwardWord L r = w) (4 ^ L) = 2 ^ L := by
  induction L with
  | zero =>
    simp only [pow_zero]
    rw [Nat.count_one]
    simp [Subsingleton.elim (amusicalForwardWord 0 0) w]
  | succ L ih =>
    obtain ⟨b, w', rfl⟩ : ∃ b w', w = Fin.cons b w' :=
      ⟨w 0, Fin.tail w, (Fin.cons_self_tail w).symm⟩
    set N := 4 ^ L with hN
    have hNpos : 0 < N := by positivity
    let g : ℤ → Prop := fun x => amusicalForwardWord L x = w'
    have hg : ∀ x, g x ↔ g (x % (N : ℕ)) := fun x => by
      simp only [g, hN]
      push_cast
      rw [← amusicalForwardWord_emod]
    have hcop : IsCoprime (3 : ℤ) (N : ℕ) := by
      rw [hN]
      push_cast
      exact IsCoprime.pow_right ⟨-1, 1, by norm_num⟩
    have key : ∀ e : ℤ, Nat.count (fun m : ℕ => g (3 * (m : ℤ) + e)) N = 2 ^ L :=
      fun e => by
        rw [count_comp_of_injMod N hNpos g hg _ (injMod_affine N 3 e hcop)]
        exact ih w'
    rw [pow_succ', count_four_mul_decomp, pow_succ]
    have hE : ∀ m : ℕ,
        (amusicalForwardWord (L + 1) ((2 * m : ℕ) : ℤ) = Fin.cons b w') ↔
          (b = false ∧ g (3 * (m : ℤ) + 0)) := fun m => by
      rw [amusicalForwardWord_succ, Fin.cons_inj]
      push_cast
      rw [amusical_two_mul, add_zero]
      simp only [g]
      constructor <;> rintro ⟨rfl, h2⟩ <;> refine ⟨?_, h2⟩ <;> simp
    have hO1 : ∀ m : ℕ,
        (amusicalForwardWord (L + 1) ((4 * m + 1 : ℕ) : ℤ) = Fin.cons b w') ↔
          (b = true ∧ g (3 * (m : ℤ) + 1)) := fun m => by
      rw [amusicalForwardWord_succ, Fin.cons_inj]
      push_cast
      rw [amusical_four_mul_add_one]
      simp only [g]
      constructor <;> rintro ⟨rfl, h2⟩ <;> refine ⟨?_, h2⟩ <;> simp <;> omega
    have hO3 : ∀ m : ℕ,
        (amusicalForwardWord (L + 1) ((4 * m + 3 : ℕ) : ℤ) = Fin.cons b w') ↔
          (b = true ∧ g (3 * (m : ℤ) + 2)) := fun m => by
      rw [amusicalForwardWord_succ, Fin.cons_inj]
      push_cast
      rw [amusical_four_mul_add_three]
      simp only [g]
      constructor <;> rintro ⟨rfl, h2⟩ <;> refine ⟨?_, h2⟩ <;> simp <;> omega
    rw [count_congr' hE, count_congr' hO1, count_congr' hO3]
    cases b
    · simp only [true_and, Bool.false_eq_true, false_and, count_false']
      rw [two_mul, Nat.count_add, key 0]
      have htail : Nat.count (fun m : ℕ => g (3 * ((N + m : ℕ) : ℤ) + 0)) N = 2 ^ L := by
        rw [← key (3 * N)]
        apply count_congr'
        intro m
        push_cast
        ring_nf
      rw [htail]
      ring
    · simp only [true_and, Bool.true_eq_false, false_and, count_false']
      rw [key 1, key 2]
      ring

/-- A backward word with `b` marked steps has exactly `2^b` residue classes modulo `3^L`. -/
theorem count_amusicalBackwardWord_eq (L : ℕ) (w : Fin L → Bool) :
    Nat.count (fun r : ℕ => amusicalBackwardWord L r = w) (3 ^ L) =
      2 ^ (Finset.univ.filter fun i : Fin L => w i = true).card := by
  induction L with
  | zero =>
    simp only [pow_zero]
    rw [Nat.count_one]
    simp [Subsingleton.elim (amusicalBackwardWord 0 0) w]
  | succ L ih =>
    obtain ⟨b, w', rfl⟩ : ∃ b w', w = Fin.cons b w' :=
      ⟨w 0, Fin.tail w, (Fin.cons_self_tail w).symm⟩
    set N := 3 ^ L with hN
    have hNpos : 0 < N := by positivity
    let g : ℤ → Prop := fun x => amusicalBackwardWord L x = w'
    have hg : ∀ x, g x ↔ g (x % (N : ℕ)) := fun x => by
      simp only [g, hN]
      push_cast
      rw [← amusicalBackwardWord_emod]
    have key : ∀ u e : ℤ, IsCoprime u (3 : ℤ) →
        Nat.count (fun m : ℕ => g (u * (m : ℤ) + e)) N =
          2 ^ (Finset.univ.filter fun i : Fin L => w' i = true).card := fun u e hu => by
      have hcop : IsCoprime u (N : ℕ) := by
        rw [hN]
        push_cast
        exact hu.pow_right
      rw [count_comp_of_injMod N hNpos g hg _ (injMod_affine N u e hcop)]
      exact ih w'
    rw [pow_succ', count_three_mul_decomp]
    have hE : ∀ m : ℕ,
        (amusicalBackwardWord (L + 1) ((3 * m : ℕ) : ℤ) = Fin.cons b w') ↔
          (b = false ∧ g (2 * (m : ℤ) + 0)) := fun m => by
      rw [amusicalBackwardWord_succ, Fin.cons_inj]
      push_cast
      have hform : amusicalInv (3 * (m : ℤ)) = 2 * m + 0 := by
        unfold amusicalInv
        split_ifs <;> omega
      rw [hform]
      simp only [g]
      constructor <;> rintro ⟨rfl, h2⟩ <;> refine ⟨?_, h2⟩ <;> simp
    have hO1 : ∀ m : ℕ,
        (amusicalBackwardWord (L + 1) ((3 * m + 1 : ℕ) : ℤ) = Fin.cons b w') ↔
          (b = true ∧ g (4 * (m : ℤ) + 1)) := fun m => by
      rw [amusicalBackwardWord_succ, Fin.cons_inj]
      push_cast
      have hform : amusicalInv (3 * (m : ℤ) + 1) = 4 * m + 1 := by
        unfold amusicalInv
        split_ifs <;> omega
      rw [hform]
      simp only [g]
      constructor <;> rintro ⟨rfl, h2⟩ <;> refine ⟨?_, h2⟩ <;> simp
    have hO2 : ∀ m : ℕ,
        (amusicalBackwardWord (L + 1) ((3 * m + 2 : ℕ) : ℤ) = Fin.cons b w') ↔
          (b = true ∧ g (4 * (m : ℤ) + 3)) := fun m => by
      rw [amusicalBackwardWord_succ, Fin.cons_inj]
      push_cast
      have hform : amusicalInv (3 * (m : ℤ) + 2) = 4 * m + 3 := by
        unfold amusicalInv
        split_ifs <;> omega
      rw [hform]
      simp only [g]
      constructor <;> rintro ⟨rfl, h2⟩ <;> refine ⟨?_, h2⟩ <;> simp
    rw [count_congr' hE, count_congr' hO1, count_congr' hO2, Fin.card_filter_univ_succ]
    cases b
    · simp only [true_and, Bool.false_eq_true, false_and, Fin.cons_zero, Fin.cons_succ,
        if_false, count_false']
      rw [key 2 0 ⟨-1, 1, by norm_num⟩]
      simp
    · simp only [true_and, Bool.true_eq_false, false_and, Fin.cons_zero, Fin.cons_succ,
        if_true, count_false']
      rw [key 4 1 ⟨1, -1, by norm_num⟩, key 4 3 ⟨1, -1, by norm_num⟩]
      ring

/-- The forward affine slope cannot equal the diagonal slope at a positive time. -/
theorem amusical_forward_slope_ne (L t e : ℕ) (ht1 : 1 ≤ t) :
    (4 : ℤ) ^ L ≠ (4 : ℤ) ^ (L - t) * 3 ^ t * 2 ^ e := by
  intro h
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  have hmod := congrArg (fun z : ℤ => z % 3) h
  have hfour : ∀ k : ℕ, (4 : ℤ) ^ k % 3 = 1 := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih => rw [pow_succ, Int.mul_emod, ih]; norm_num
  rw [hfour] at hmod
  rw [pow_succ, mul_assoc, Int.mul_emod] at hmod
  norm_num [Int.mul_emod] at hmod

/-- The backward affine slope cannot equal the diagonal slope at a positive time. -/
theorem amusical_backward_slope_ne (L t f : ℕ) (ht1 : 1 ≤ t) (ht : t ≤ L) :
    (3 : ℤ) ^ L ≠ (3 : ℤ) ^ (L - t) * 2 ^ (t + f) := by
  intro h
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  obtain ⟨d, hd⟩ : ∃ d, L = d + 1 := ⟨L - 1, by omega⟩
  subst L
  have hmod := congrArg (fun z : ℤ => z % 2) h
  have hthree : ∀ k : ℕ, (3 : ℤ) ^ k % 2 = 1 := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih => rw [pow_succ, Int.mul_emod, ih]; norm_num
  rw [hthree] at hmod
  rw [show s + 1 + f = (s + f) + 1 by omega, pow_succ] at hmod
  norm_num [Int.mul_emod] at hmod

/-- After cancelling the fixed residue-class factor, the forward slope inequality is exactly
the prefix-survival inequality used in `fwdSurv`. -/
theorem amusical_forward_slope_lt_iff (L t o e : ℕ) (ht : t ≤ L) (hoe : o + e = t) :
    (4 : ℤ) ^ L < 4 ^ (L - t) * 3 ^ t * 2 ^ e ↔ 2 ^ (t + o) < 3 ^ t := by
  have hpow : (4 : ℕ) ^ L = 4 ^ (L - t) * 4 ^ t := by
    rw [← pow_add, Nat.sub_add_cancel ht]
  have hfour : (4 : ℕ) ^ t = 2 ^ (t + o) * 2 ^ e := by
    rw [← pow_add, show t + o + e = 2 * t by omega, pow_mul]
    norm_num
  exact_mod_cast (show (4 : ℕ) ^ L < 4 ^ (L - t) * 3 ^ t * 2 ^ e ↔
      2 ^ (t + o) < 3 ^ t by
    rw [hpow, mul_assoc, Nat.mul_lt_mul_left (by positivity : 0 < 4 ^ (L - t))]
    rw [hfour, Nat.mul_lt_mul_right (by positivity : 0 < 2 ^ e)])

/-- After cancellation, the backward slope inequality is exactly the prefix-survival inequality
used in `bwdSurv`. -/
theorem amusical_backward_slope_lt_iff (L t f : ℕ) (ht : t ≤ L) :
    (3 : ℤ) ^ L < 3 ^ (L - t) * 2 ^ (t + f) ↔ 3 ^ t < 2 ^ (t + f) := by
  have hpow : (3 : ℕ) ^ L = 3 ^ (L - t) * 3 ^ t := by
    rw [← pow_add, Nat.sub_add_cancel ht]
  exact_mod_cast (show (3 : ℕ) ^ L < 3 ^ (L - t) * 2 ^ (t + f) ↔
      3 ^ t < 2 ^ (t + f) by
    rw [hpow, Nat.mul_lt_mul_left (by positivity : 0 < 3 ^ (L - t))])

/-! ## Stabilization on a residue class

The affine formula is useful for density only after identifying which side of the diagonal
its slope lies on.  The following elementary lemma packages the threshold argument once and
for all: two integral affine functions with distinct slopes have their eventual order decided
exactly by their slopes. -/

theorem eventually_affine_le_iff_slope_lt {a b c d : ℤ} (hab : a ≠ b) :
    ∃ K : ℤ, ∀ k : ℤ, K ≤ k → (c + a * k ≤ d + b * k ↔ a < b) := by
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · refine ⟨max 0 (c - d), fun k hk => ⟨fun _ => hlt, fun _ => ?_⟩⟩
    have hk0 : 0 ≤ k := le_trans (le_max_left _ _) hk
    have hkcd : c - d ≤ k := le_trans (le_max_right _ _) hk
    have hgap : 1 ≤ b - a := by omega
    have hmul : k ≤ (b - a) * k := by
      simpa [one_mul] using mul_le_mul_of_nonneg_right hgap hk0
    nlinarith
  · refine ⟨max 0 (d - c + 1), fun k hk => ⟨fun h => ?_, fun h => by omega⟩⟩
    have hk0 : 0 ≤ k := le_trans (le_max_left _ _) hk
    have hkdc : d - c + 1 ≤ k := le_trans (le_max_right _ _) hk
    have hgap : 1 ≤ a - b := by omega
    have hmul : k ≤ (a - b) * k := by
      simpa [one_mul] using mul_le_mul_of_nonneg_right hgap hk0
    nlinarith

/-- On one forward residue class, comparison with the starting point eventually depends only
on the exact forward slope. -/
theorem amusical_iterate_eventually_ge_iff_slope (L t : ℕ) (ht : t ≤ L) (n : ℤ)
    (hne : (4 : ℤ) ^ L ≠
      (4 : ℤ) ^ (L - t) * 3 ^ t * 2 ^ amusicalForwardEvenCount t n) :
    ∃ K : ℤ, ∀ k : ℤ, K ≤ k →
      (n + (4 : ℤ) ^ L * k ≤ amusical^[t] (n + (4 : ℤ) ^ L * k) ↔
        (4 : ℤ) ^ L <
          (4 : ℤ) ^ (L - t) * 3 ^ t * 2 ^ amusicalForwardEvenCount t n) := by
  obtain ⟨K, hK⟩ := eventually_affine_le_iff_slope_lt hne
  refine ⟨K, fun k hk => ?_⟩
  rw [amusical_iterate_add_pow_four_mul_slope L t ht]
  exact hK k hk

/-- On one backward residue class, comparison with the starting point eventually depends only
on the exact backward slope. -/
theorem amusicalInv_iterate_eventually_ge_iff_slope (L t : ℕ) (ht : t ≤ L) (n : ℤ)
    (hne : (3 : ℤ) ^ L ≠
      (3 : ℤ) ^ (L - t) * 2 ^ (t + amusicalBackwardFourCount t n)) :
    ∃ K : ℤ, ∀ k : ℤ, K ≤ k →
      (n + (3 : ℤ) ^ L * k ≤ amusicalInv^[t] (n + (3 : ℤ) ^ L * k) ↔
        (3 : ℤ) ^ L <
          (3 : ℤ) ^ (L - t) * 2 ^ (t + amusicalBackwardFourCount t n)) := by
  obtain ⟨K, hK⟩ := eventually_affine_le_iff_slope_lt hne
  refine ⟨K, fun k hk => ?_⟩
  rw [amusicalInv_iterate_add_pow_three_mul_slope L t ht]
  exact hK k hk

/-- The eventual forward comparison on a residue class is exactly the prefix condition appearing
in `fwdSurv`. -/
theorem amusical_iterate_eventually_ge_iff_word (L t : ℕ) (ht1 : 1 ≤ t) (ht : t ≤ L)
    (n : ℤ) :
    ∃ K : ℤ, ∀ k : ℤ, K ≤ k →
      (n + (4 : ℤ) ^ L * k ≤ amusical^[t] (n + (4 : ℤ) ^ L * k) ↔
        2 ^ (t + (Finset.univ.filter fun i : Fin L =>
          i.val < t ∧ amusicalForwardWord L n i = true).card) < 3 ^ t) := by
  obtain ⟨K, hK⟩ := amusical_iterate_eventually_ge_iff_slope L t ht n
    (amusical_forward_slope_ne L t (amusicalForwardEvenCount t n) ht1)
  refine ⟨K, fun k hk => (hK k hk).trans ?_⟩
  exact amusical_forward_slope_lt_iff L t _ _ ht
    (amusicalForwardWord_true_card_add_evenCount L t ht n)

/-- The eventual backward comparison on a residue class is exactly the prefix condition appearing
in `bwdSurv`. -/
theorem amusicalInv_iterate_eventually_ge_iff_word (L t : ℕ) (ht1 : 1 ≤ t) (ht : t ≤ L)
    (n : ℤ) :
    ∃ K : ℤ, ∀ k : ℤ, K ≤ k →
      (n + (3 : ℤ) ^ L * k ≤ amusicalInv^[t] (n + (3 : ℤ) ^ L * k) ↔
        3 ^ t < 2 ^ (t + (Finset.univ.filter fun i : Fin L =>
          i.val < t ∧ amusicalBackwardWord L n i = true).card)) := by
  obtain ⟨K, hK⟩ := amusicalInv_iterate_eventually_ge_iff_slope L t ht n
    (amusical_backward_slope_ne L t (amusicalBackwardFourCount t n) ht1 ht)
  refine ⟨K, fun k hk => (hK k hk).trans ?_⟩
  rw [amusicalBackwardWord_true_card_eq_fourCount L t ht n]
  exact amusical_backward_slope_lt_iff L t _ ht

theorem amusical_iterate_add_pow_four_mul (L t : ℕ) (ht : t ≤ L) (n k : ℤ) :
    ∃ a : ℤ, 0 < a ∧ amusical^[t] (n + (4 : ℤ) ^ L * k) = amusical^[t] n + a * k := by
  induction L generalizing t n k with
  | zero =>
      obtain rfl : t = 0 := by omega
      exact ⟨1, by omega, by simp⟩
  | succ L ih =>
      cases t with
      | zero => exact ⟨(4 : ℤ) ^ (L + 1), by positivity, by simp⟩
      | succ t =>
          have ht' : t ≤ L := by omega
          let d : ℤ := if n % 2 = 0 then 6 else 3
          obtain ⟨a, ha, hiter⟩ := ih t ht' (amusical n) (d * k)
          refine ⟨a * d, mul_pos ha ?_, ?_⟩
          · dsimp [d]; split <;> omega
          · rw [Function.iterate_succ_apply, Function.iterate_succ_apply, pow_succ']
            rw [show n + 4 * 4 ^ L * k = n + 4 * (4 ^ L * k) by ring]
            rw [amusical_add_four_mul]
            by_cases h : n % 2 = 0 <;> simp [d, h] at hiter ⊢ <;>
              convert hiter using 1 <;> ring

theorem amusicalInv_iterate_add_pow_three_mul (L t : ℕ) (ht : t ≤ L) (n k : ℤ) :
    ∃ a : ℤ, 0 < a ∧ amusicalInv^[t] (n + (3 : ℤ) ^ L * k) = amusicalInv^[t] n + a * k := by
  induction L generalizing t n k with
  | zero =>
      obtain rfl : t = 0 := by omega
      exact ⟨1, by omega, by simp⟩
  | succ L ih =>
      cases t with
      | zero => exact ⟨(3 : ℤ) ^ (L + 1), by positivity, by simp⟩
      | succ t =>
          have ht' : t ≤ L := by omega
          let d : ℤ := if n % 3 = 0 then 2 else 4
          obtain ⟨a, ha, hiter⟩ := ih t ht' (amusicalInv n) (d * k)
          refine ⟨a * d, mul_pos ha ?_, ?_⟩
          · dsimp [d]; split <;> omega
          · rw [Function.iterate_succ_apply, Function.iterate_succ_apply, pow_succ']
            rw [show n + 3 * 3 ^ L * k = n + 3 * (3 ^ L * k) by ring]
            rw [amusicalInv_add_three_mul]
            by_cases h : n % 3 = 0 <;> simp [d, h] at hiter ⊢ <;>
              convert hiter using 1 <;> ring

/-- Every orbit minimum is an `L`-window minimum. -/
theorem IsOrbitMin.isWindowMin {m : ℤ} (h : IsOrbitMin m) (L : ℕ) : IsWindowMin L m := by
  intro t _ _
  refine ⟨h _ ⟨(t : ℤ), (amusical_iterate_eq_perm_pow t m).symm⟩,
    h _ ⟨-(t : ℤ), (amusicalInv_iterate_eq_perm_pow t m).symm⟩⟩

/-- Survival probability of the forward walk for `L` steps: a pattern `w` marks the odd steps
(`×3/4`, probability `1/2`) against the even ones (`×3/2`, probability `1/2`); the prefix of
length `t` survives when `(3/2)^(t-o) (3/4)^o > 1`, i.e. `2^(t+o) < 3^t`. -/
def fwdSurv (L : ℕ) : ℚ :=
  ∑ w : Fin L → Bool,
    if ∀ t : ℕ, 1 ≤ t → t ≤ L →
        2 ^ (t + ((Finset.univ.filter fun i : Fin L => i.val < t ∧ w i = true).card)) < 3 ^ t
    then (1 / 2 : ℚ) ^ L else 0

/-- Survival probability of the backward walk for `L` steps: a pattern `w` marks the steps
`×4/3` (probability `2/3`) against `×2/3` (probability `1/3`); the prefix of length `t` survives
when `2^(t+b) > 3^t`, `b` the number of marked steps in it. -/
def bwdSurv (L : ℕ) : ℚ :=
  ∑ w : Fin L → Bool,
    if ∀ t : ℕ, 1 ≤ t → t ≤ L →
        3 ^ t < 2 ^ (t + ((Finset.univ.filter fun i : Fin L => i.val < t ∧ w i = true).card))
    then (2 / 3 : ℚ) ^ ((Finset.univ.filter fun i : Fin L => w i = true).card) *
      (1 / 3 : ℚ) ^ ((Finset.univ.filter fun i : Fin L => w i = false).card)
    else 0

/-- The first window densities, by kernel evaluation of the pattern sums. -/
theorem windowDensity_values :
    fwdSurv 1 * bwdSurv 1 = 1 / 3 ∧ fwdSurv 2 * bwdSurv 2 = 2 / 9 ∧
      fwdSurv 3 * bwdSurv 3 = 1 / 6 ∧ fwdSurv 4 * bwdSurv 4 = 4 / 27 := by
  decide +kernel

open Classical in
/-- The `L`-window minima among `0, …, X-1` have density `fwdSurv L * bwdSurv L`.
The proof uses Matthews--Watts residue classes for both directions, the CRT, and a size
threshold past which the additive offsets cannot flip a prefix comparison. -/
def WindowMinDensity (L : ℕ) : Prop :=
  Filter.Tendsto
    (fun X : ℕ => (((Finset.range X).filter fun n : ℕ => IsWindowMin L n).card : ℝ) / X)
    Filter.atTop (nhds ((fwdSurv L * bwdSurv L : ℚ) : ℝ))

open Classical in
/-- The window bound: if `L`-window minima have density `δ`, orbit minima have upper density at
most `δ`, in the form "eventually below `δ + ε`". -/
theorem orbitMin_density_le_of_windowMinDensity {L : ℕ} (h : WindowMinDensity L) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ X : ℕ in Filter.atTop,
      (((Finset.range X).filter fun m : ℕ => IsOrbitMin m).card : ℝ) / X ≤
        ((fwdSurv L * bwdSurv L : ℚ) : ℝ) + ε := by
  filter_upwards [h.eventually (gt_mem_nhds (lt_add_of_pos_right _ hε))] with X hX
  refine le_trans ?_ hX.le
  gcongr with m
  exact fun hm => hm.isWindowMin L

/-! ## The case `L = 1`: Conway's congruence paradox, exactly

Conway (2013, Appendix 2) observes that `n < U n` exactly when `n` is even and `n < U⁻¹ n`
exactly when `3 ∤ n`, so the local minima are the classes `±2 (mod 6)`, a third of all
integers.  `windowMinDensity_one` is that statement as a density. -/

theorem isWindowMin_one_iff (n : ℤ) :
    IsWindowMin 1 n ↔ n ≤ amusical n ∧ n ≤ amusicalInv n := by
  constructor
  · intro h; simpa using h 1 le_rfl le_rfl
  · intro h t h1 h2
    obtain rfl : t = 1 := by omega
    simpa using h

/-- On the naturals, the `1`-window minima are `0`, `1` and the classes `2, 4 (mod 6)`. -/
theorem isWindowMin_one_natCast_iff (n : ℕ) :
    IsWindowMin 1 (n : ℤ) ↔ n = 0 ∨ n = 1 ∨ n % 6 = 2 ∨ n % 6 = 4 := by
  rw [isWindowMin_one_iff]
  unfold amusical amusicalInv
  split_ifs <;> omega

/-- The predicate of `isWindowMin_one_natCast_iff`, decidably. -/
def windowOnePred (n : ℕ) : Prop := n = 0 ∨ n = 1 ∨ n % 6 = 2 ∨ n % 6 = 4

instance : DecidablePred windowOnePred := fun n => by unfold windowOnePred; infer_instance

theorem count_windowOnePred_six {a : ℕ} (ha : 2 ≤ a) :
    Nat.count (fun k => windowOnePred (a + k)) 6 = 2 := by
  have key : ∀ k, windowOnePred (a + k) ↔ ((a % 6 + k) % 6 = 2 ∨ (a % 6 + k) % 6 = 4) := by
    intro k; unfold windowOnePred; omega
  rw [Nat.count_eq_card_filter_range, Finset.filter_congr fun k _ => key k]
  have hr : a % 6 < 6 := Nat.mod_lt _ (by norm_num)
  generalize a % 6 = r at hr ⊢
  interval_cases r <;> decide

theorem count_windowOnePred_bound (X : ℕ) :
    3 * Nat.count windowOnePred X ≤ X + 8 ∧ X ≤ 3 * Nat.count windowOnePred X + 8 := by
  induction X using Nat.strong_induction_on with
  | _ X ih =>
    rcases Nat.lt_or_ge X 8 with hX | hX
    · interval_cases X <;> decide
    · have h6 := Nat.count_add windowOnePred (X - 6) 6
      rw [Nat.sub_add_cancel (by omega), count_windowOnePred_six (by omega)] at h6
      have := ih (X - 6) (by omega)
      omega

open Classical in
/-- **Conway's congruence paradox as a density.**  The `1`-window minima have density
`1/3 = fwdSurv 1 * bwdSurv 1`. -/
theorem windowMinDensity_one : WindowMinDensity 1 := by
  unfold WindowMinDensity
  have hval : ((fwdSurv 1 * bwdSurv 1 : ℚ) : ℝ) = 1 / 3 := by
    rw [windowDensity_values.1]; norm_num
  rw [hval]
  have hcard : ∀ X : ℕ, ((Finset.range X).filter fun n : ℕ => IsWindowMin 1 n).card =
      Nat.count windowOnePred X := by
    intro X
    rw [Nat.count_eq_card_filter_range]
    exact congrArg _ (Finset.filter_congr fun n _ => isWindowMin_one_natCast_iff n)
  simp only [hcard]
  have hlo : Filter.Tendsto (fun X : ℕ => (1 / 3 : ℝ) - 3 / X) Filter.atTop (nhds (1 / 3)) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (3 : ℝ))
  have hhi : Filter.Tendsto (fun X : ℕ => (1 / 3 : ℝ) + 3 / X) Filter.atTop (nhds (1 / 3)) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (3 : ℝ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 1] with X hX
    have hXpos : (0 : ℝ) < X := by exact_mod_cast hX
    have hb : (X : ℝ) ≤ 3 * (Nat.count windowOnePred X : ℝ) + 8 := by
      exact_mod_cast (count_windowOnePred_bound X).2
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hXpos]
    linarith
  · filter_upwards [Filter.eventually_ge_atTop 1] with X hX
    have hXpos : (0 : ℝ) < X := by exact_mod_cast hX
    have hb : 3 * (Nat.count windowOnePred X : ℝ) ≤ X + 8 := by
      exact_mod_cast (count_windowOnePred_bound X).1
    have hX' : ((1 : ℝ) / 3 + 3 / X) * X = X / 3 + 3 := by field_simp
    rw [div_le_iff₀ hXpos, hX']
    linarith

/-! ## Eventual periodic characterization -/

/-- The forward survival condition on a branch word. -/
abbrev FwdGood (L : ℕ) (w : Fin L → Bool) : Prop :=
  ∀ t : ℕ, 1 ≤ t → t ≤ L →
    2 ^ (t + ((Finset.univ.filter fun i : Fin L => i.val < t ∧ w i = true).card)) < 3 ^ t

/-- The backward survival condition on a branch word. -/
abbrev BwdGood (L : ℕ) (w : Fin L → Bool) : Prop :=
  ∀ t : ℕ, 1 ≤ t → t ≤ L →
    3 ^ t < 2 ^ (t + ((Finset.univ.filter fun i : Fin L => i.val < t ∧ w i = true).card))

/-- A uniform bound for all additive offsets over one complete joint residue system. -/
def windowBound (L : ℕ) : ℕ :=
  ∑ c ∈ Finset.range (4 ^ L * 3 ^ L), ∑ t ∈ Finset.range (L + 1),
    ((amusical^[t] (c : ℤ) - c).natAbs + (amusicalInv^[t] (c : ℤ) - c).natAbs)

theorem add_mul_le_add_mul_iff {α β k c y : ℤ} (hne : α ≠ β) (hk : |y - c| < k) :
    c + α * k ≤ y + β * k ↔ α < β := by
  have hk' := abs_lt.mp hk
  rcases lt_or_gt_of_ne hne with h | h
  · refine ⟨fun _ => h, fun _ => ?_⟩
    have : α * k + k ≤ β * k := by nlinarith
    linarith
  · refine ⟨fun h' => ?_, fun h' => absurd h' (not_lt.mpr h.le)⟩
    exfalso
    have : β * k + k ≤ α * k := by nlinarith
    linarith

/-- Above an explicit finite threshold, the window-minimum condition is exactly the conjunction
of the forward and backward survival tests on the two branch words. -/
theorem isWindowMin_iff_of_large (L n : ℕ)
    (hn : 4 ^ L * 3 ^ L * (windowBound L + 1) ≤ n) :
    IsWindowMin L n ↔ FwdGood L (amusicalForwardWord L n) ∧
      BwdGood L (amusicalBackwardWord L n) := by
  set M := 4 ^ L * 3 ^ L with hM
  have hMpos : 0 < M := by positivity
  set c := n % M with hc
  set q := n / M with hq
  have hcM : c < M := Nat.mod_lt _ hMpos
  have hqge : windowBound L + 1 ≤ q := (Nat.le_div_iff_mul_le hMpos).mpr (by linarith)
  have hnq : (n : ℤ) = c + M * q := by
    have h := Nat.mod_add_div n M
    exact_mod_cast h.symm
  have hnF : (n : ℤ) = c + 4 ^ L * (3 ^ L * q) := by
    rw [hnq, hM]
    push_cast
    ring
  have hnB : (n : ℤ) = c + 3 ^ L * (4 ^ L * q) := by
    rw [hnq, hM]
    push_cast
    ring
  have hpatF : amusicalForwardWord L n = amusicalForwardWord L c := by
    rw [hnF, amusicalForwardWord_add_pow_four_mul]
  have hpatB : amusicalBackwardWord L n = amusicalBackwardWord L c := by
    rw [hnB, amusicalBackwardWord_add_pow_three_mul]
  rw [hpatF, hpatB]
  have hbound : ∀ t, t ≤ L → |amusical^[t] (c : ℤ) - c| < q ∧
      |amusicalInv^[t] (c : ℤ) - c| < q := by
    intro t ht
    have h1 : (amusical^[t] (c : ℤ) - c).natAbs +
        (amusicalInv^[t] (c : ℤ) - c).natAbs ≤ windowBound L := by
      unfold windowBound
      refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.mpr hcM))
      exact Finset.single_le_sum
        (f := fun t => (amusical^[t] (c : ℤ) - c).natAbs +
          (amusicalInv^[t] (c : ℤ) - c).natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
    have h2 : ((amusical^[t] (c : ℤ) - c).natAbs : ℤ) +
        ((amusicalInv^[t] (c : ℤ) - c).natAbs : ℤ) ≤ windowBound L := by
      exact_mod_cast h1
    have h3 : (windowBound L : ℤ) + 1 ≤ q := by exact_mod_cast hqge
    rw [Int.natCast_natAbs, Int.natCast_natAbs] at h2
    have hf := abs_nonneg (amusical^[t] (c : ℤ) - c)
    have hb := abs_nonneg (amusicalInv^[t] (c : ℤ) - c)
    constructor <;> linarith
  have hq3 : (q : ℤ) ≤ 3 ^ L * q :=
    le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
  have hq4 : (q : ℤ) ≤ 4 ^ L * q :=
    le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
  have hF : ∀ t, 1 ≤ t → t ≤ L → ((n : ℤ) ≤ amusical^[t] n ↔
      2 ^ (t + ((Finset.univ.filter fun i : Fin L =>
        i.val < t ∧ amusicalForwardWord L c i = true).card)) < 3 ^ t) := by
    intro t ht1 ht
    rw [hnF, amusical_iterate_add_pow_four_mul_slope L t ht]
    rw [show (4 : ℤ) ^ (L - t) * 3 ^ t * 2 ^ amusicalForwardEvenCount t c * (3 ^ L * q) =
      (4 ^ (L - t) * 3 ^ t * 2 ^ amusicalForwardEvenCount t c) * (3 ^ L * q) by ring]
    rw [add_mul_le_add_mul_iff
      (amusical_forward_slope_ne L t (amusicalForwardEvenCount t c) ht1)
      (lt_of_lt_of_le (hbound t ht).1 hq3)]
    exact amusical_forward_slope_lt_iff L t _ _ ht
      (amusicalForwardWord_true_card_add_evenCount L t ht c)
  have hB : ∀ t, 1 ≤ t → t ≤ L → ((n : ℤ) ≤ amusicalInv^[t] n ↔
      3 ^ t < 2 ^ (t + ((Finset.univ.filter fun i : Fin L =>
        i.val < t ∧ amusicalBackwardWord L c i = true).card))) := by
    intro t ht1 ht
    rw [hnB, amusicalInv_iterate_add_pow_three_mul_slope L t ht]
    rw [add_mul_le_add_mul_iff
      (amusical_backward_slope_ne L t (amusicalBackwardFourCount t c) ht1 ht)
      (lt_of_lt_of_le (hbound t ht).2 hq4)]
    rw [amusicalBackwardWord_true_card_eq_fourCount L t ht c]
    exact amusical_backward_slope_lt_iff L t _ ht
  unfold IsWindowMin
  constructor
  · intro h
    exact ⟨fun t h1 h2 => (hF t h1 h2).mp (h t h1 h2).1,
      fun t h1 h2 => (hB t h1 h2).mp (h t h1 h2).2⟩
  · rintro ⟨h1, h2⟩ t ht1 ht2
    exact ⟨(hF t ht1 ht2).mpr (h1 t ht1 ht2),
      (hB t ht1 ht2).mpr (h2 t ht1 ht2)⟩

theorem amusicalForwardWord_natCast_mod (L n : ℕ) :
    amusicalForwardWord L (n : ℤ) = amusicalForwardWord L ((n % 4 ^ L : ℕ) : ℤ) := by
  rw [amusicalForwardWord_emod L (n : ℤ)]
  push_cast
  rfl

theorem amusicalBackwardWord_natCast_mod (L n : ℕ) :
    amusicalBackwardWord L (n : ℤ) = amusicalBackwardWord L ((n % 3 ^ L : ℕ) : ℤ) := by
  rw [amusicalBackwardWord_emod L (n : ℤ)]
  push_cast
  rfl

/-! ## Counting good residue classes -/

theorem count_fwdGood (L : ℕ) :
    Nat.count (fun r : ℕ => FwdGood L (amusicalForwardWord L r)) (4 ^ L) =
      ∑ w : Fin L → Bool, if FwdGood L w then 2 ^ L else 0 := by
  classical
  rw [Nat.count_eq_card_filter_range, Finset.card_eq_sum_card_fiberwise
    (f := fun r : ℕ => amusicalForwardWord L r) (t := Finset.univ)
      (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.filter_filter]
  split_ifs with hw
  · rw [← count_amusicalForwardWord_eq L w, Nat.count_eq_card_filter_range]
    congr 1
    apply Finset.filter_congr
    intro r _
    exact ⟨fun h => h.2, fun h => ⟨h ▸ hw, h⟩⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro r _ ⟨h1, h2⟩
    exact hw (h2 ▸ h1)

theorem count_bwdGood (L : ℕ) :
    Nat.count (fun r : ℕ => BwdGood L (amusicalBackwardWord L r)) (3 ^ L) =
      ∑ w : Fin L → Bool, if BwdGood L w then
        2 ^ (Finset.univ.filter fun i : Fin L => w i = true).card else 0 := by
  classical
  rw [Nat.count_eq_card_filter_range, Finset.card_eq_sum_card_fiberwise
    (f := fun r : ℕ => amusicalBackwardWord L r) (t := Finset.univ)
      (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.filter_filter]
  split_ifs with hw
  · rw [← count_amusicalBackwardWord_eq L w, Nat.count_eq_card_filter_range]
    congr 1
    apply Finset.filter_congr
    intro r _
    exact ⟨fun h => h.2, fun h => ⟨h ▸ hw, h⟩⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro r _ ⟨h1, h2⟩
    exact hw (h2 ▸ h1)

theorem fwdSurv_mul (L : ℕ) :
    (4 : ℚ) ^ L * fwdSurv L =
      (Nat.count (fun r : ℕ => FwdGood L (amusicalForwardWord L r)) (4 ^ L) : ℚ) := by
  classical
  rw [count_fwdGood]
  unfold fwdSurv
  rw [Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun w _ => ?_
  split_ifs
  · rw [← mul_pow]
    norm_num
  · simp

theorem bwdSurv_mul (L : ℕ) :
    (3 : ℚ) ^ L * bwdSurv L =
      (Nat.count (fun r : ℕ => BwdGood L (amusicalBackwardWord L r)) (3 ^ L) : ℚ) := by
  classical
  rw [count_bwdGood]
  unfold bwdSurv
  rw [Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun w _ => ?_
  split_ifs
  · have hab : (Finset.univ.filter fun i : Fin L => w i = true).card +
        (Finset.univ.filter fun i : Fin L => w i = false).card = L := by
      have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin L)))
        (fun i => w i = true)
      simpa using h
    set a := (Finset.univ.filter fun i : Fin L => w i = true).card
    set b := (Finset.univ.filter fun i : Fin L => w i = false).card
    have h3 : (3 : ℚ) ^ L = 3 ^ a * 3 ^ b := by rw [← pow_add, hab]
    rw [h3]
    calc
      (3 : ℚ) ^ a * 3 ^ b * ((2 / 3) ^ a * (1 / 3) ^ b) =
          (3 * (2 / 3)) ^ a * (3 * (1 / 3)) ^ b := by
            rw [mul_pow, mul_pow]
            ring
      _ = 2 ^ a := by norm_num
  · simp

/-- **The window-minimum density, for every `L`** (proved 2026-10-13 by treadmill from
`KICKOFF-2026-10-13-amusical-window.md`; axiom-clean).  Proof: on each residue class mod
`4^L · 3^L` the first `L` forward and backward branches are fixed, so `U^t` and `U^-t` are
affine there; past a size threshold the window condition is a congruence condition; the good
classes number `4^L · 3^L · fwdSurv L · bwdSurv L` (Haar counting per direction, CRT across). -/
theorem windowMinDensity (L : ℕ) : WindowMinDensity L := by
  classical
  unfold WindowMinDensity
  set M := 4 ^ L * 3 ^ L with hM
  have hMpos : 0 < M := by positivity
  set N₀ := M * (windowBound L + 1) with hN₀
  let F : ℕ → Prop := fun r => FwdGood L (amusicalForwardWord L r)
  let B : ℕ → Prop := fun r => BwdGood L (amusicalBackwardWord L r)
  let P : ℕ → Prop := fun n => F n ∧ B n
  have hPcrt : ∀ n, P n ↔ F (n % 4 ^ L) ∧ B (n % 3 ^ L) := fun n => by
    simp only [P, F, B]
    rw [← amusicalForwardWord_natCast_mod, ← amusicalBackwardWord_natCast_mod]
  have hPper : ∀ n, P n ↔ P (n % M) := fun n => by
    rw [hPcrt, hPcrt (n % M), Nat.mod_mod_of_dvd n (dvd_mul_right (4 ^ L) (3 ^ L)),
      Nat.mod_mod_of_dvd n (dvd_mul_left (3 ^ L) (4 ^ L))]
  have hG : Nat.count P M = Nat.count F (4 ^ L) * Nat.count B (3 ^ L) := by
    rw [count_congr' hPcrt]
    exact WindowCount.count_crt _ _ (Nat.Coprime.pow _ _ (by norm_num)) F B
  set G := Nat.count P M with hGdef
  have hq : (fwdSurv L * bwdSurv L : ℚ) = (G : ℚ) / M := by
    rw [eq_div_iff (by positivity), hG]
    push_cast
    rw [← fwdSurv_mul, ← bwdSurv_mul, hM]
    push_cast
    ring
  have hδ : ((fwdSurv L * bwdSurv L : ℚ) : ℝ) = (G : ℝ) / M := by
    rw [hq]
    push_cast
    rfl
  rw [hδ]
  have hcard : ∀ X : ℕ,
      ((Finset.range X).filter fun n : ℕ => IsWindowMin L n).card =
        Nat.count (fun n : ℕ => IsWindowMin L n) X := fun X => by
    rw [Nat.count_eq_card_filter_range]
  simp only [hcard]
  have hPadd : ∀ n : ℕ, P (n + M) ↔ P n := by
    intro n
    rw [hPper (n + M), hPper n]
    simp
  have hblock : ∀ a : ℕ, Nat.count (fun k => P (a + k)) M = G := by
    intro a
    rw [count_block_eq_of_add_periodic P hPadd a, hGdef]
  have hPdensity : Filter.Tendsto (fun X : ℕ => (Nat.count P X : ℝ) / X)
      Filter.atTop (nhds ((G : ℝ) / M)) :=
    tendsto_count_div_of_periodic_blocks P hMpos hblock
  apply tendsto_count_div_of_eventually_congr (fun n : ℕ => IsWindowMin L n) P
    (A := N₀) _ hPdensity
  intro n hn
  exact isWindowMin_iff_of_large L n hn

open Classical in
/-- **Unconditional window bound:** orbit minima have upper density at most
`fwdSurv L * bwdSurv L` for every `L`; the limit `p_f · p_b ≈ 0.0498` is `WindowDensityLimit`. -/
theorem orbitMin_density_le (L : ℕ) {ε : ℝ} (hε : 0 < ε) : ∀ᶠ X : ℕ in Filter.atTop,
    (((Finset.range X).filter fun m : ℕ => IsOrbitMin m).card : ℝ) / X ≤
      ((fwdSurv L * bwdSurv L : ℚ) : ℝ) + ε :=
  orbitMin_density_le_of_windowMinDensity (windowMinDensity L) hε

end CollatzMoonshot.Amusical
