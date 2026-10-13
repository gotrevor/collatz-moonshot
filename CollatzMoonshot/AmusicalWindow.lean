/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Amusical

/-!
# Window minima of the amusical permutation

`n` is an `L`-window minimum when no orbit point within `L` steps either way lies below it.
Every orbit minimum is one, so the density of `L`-window minima bounds the upper density of
orbit minima from above for each `L`: the unconditional half of `AmusicalMinimaDensity`.

For large `n` the first `L` forward branches of `n` depend only on `n mod 2^(2L)` (Matthews-Watts),
the first `L` backward branches only on `n mod 3^L`, and the CRT makes the two independent.  Each
forward step is `×3/2` or `×3/4` with frequency `1/2` each, each backward step `×2/3` or `×4/3`
with frequency `1/3, 2/3`, and for large `n` the window condition is that every prefix product
exceeds `1`.  So the density should be `fwdSurv L * bwdSurv L`, the two survival probabilities
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
/-- **Believed (~95%), proof not yet written: the window-minimum density.**  The `L`-window
minima among `0, …, X-1` have density `fwdSurv L * bwdSurv L`.  English proof in the module
docstring: Matthews-Watts residue classes for both directions, the CRT, and a size threshold
past which the additive offsets cannot flip a prefix comparison. -/
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

/-- **Target (treadmill, `KICKOFF-2026-10-13-amusical-window.md`).**  The window-minimum
density holds for every `L`.  Proof plan in the kickoff: on each residue class mod
`4^L · 3^L` the first `L` forward and backward branches are fixed, so `U^t` and `U^-t` are
affine there; past a size threshold the window condition is a congruence condition; the good
classes number `4^L · 3^L · fwdSurv L · bwdSurv L` (Haar counting per direction, CRT across). -/
theorem windowMinDensity (L : ℕ) : WindowMinDensity L := by
  sorry

open Classical in
/-- **Unconditional window bound** (modulo `windowMinDensity`): orbit minima have upper
density at most `fwdSurv L * bwdSurv L` for every `L`, hence at most `p_f · p_b ≈ 0.0498`. -/
theorem orbitMin_density_le (L : ℕ) {ε : ℝ} (hε : 0 < ε) : ∀ᶠ X : ℕ in Filter.atTop,
    (((Finset.range X).filter fun m : ℕ => IsOrbitMin m).card : ℝ) / X ≤
      ((fwdSurv L * bwdSurv L : ℚ) : ℝ) + ε :=
  orbitMin_density_le_of_windowMinDensity (windowMinDensity L) hε

end CollatzMoonshot.Amusical
