/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalConstant
import CollatzMoonshot.CycleDiophantine

/-!
# The window densities converge to `minimaConstant` (Sparre Andersen)

Target for a treadmill (`KICKOFF-2026-10-13-amusical-spitzer.md`): `windowDensityLimit`, after
which `orbitMin_density_le_minimaConstant` is unconditional.  The duality half is a termwise
identity: forward survival at time `k` and backward non-survival use the same binomial index set
`{o : 2^(k+o) < 3^k}`, with weights `C(k,o) 2^-k · 2^(k+o) 3^-k = C(k,o) 2^o 3^-k` on both sides.
The real content is Sparre Andersen's theorem for the two multiplicative walks.
-/

namespace CollatzMoonshot.Amusical

/-! ## Haar duality at one fixed time -/

/-- The probability that the forward multiplicative walk is at or below its start after `k`
steps.  There are `choose k o` words with `o` steps of type `×3/4`, each of mass `2⁻ᵏ`. -/
noncomputable def fwdNonposTerm (k : ℕ) : ℝ :=
  ∑ o ∈ Finset.range (k + 1),
    if 3 ^ k < 2 ^ (k + o) then (Nat.choose k o : ℝ) / 2 ^ k else 0

/-- The probability that the backward multiplicative walk is at or below its start after `k`
steps.  Haar tilting changes the forward mass `choose k o / 2^k` into
`choose k o * 2^o / 3^k` on the complementary side of the no-tie cut. -/
noncomputable def bwdNonposTerm (k : ℕ) : ℝ :=
  ∑ o ∈ Finset.range (k + 1),
    if 2 ^ (k + o) < 3 ^ k then (Nat.choose k o : ℝ) * 2 ^ o / 3 ^ k else 0

/-- The forward probability of finishing strictly above the start after `k` steps. -/
noncomputable def fwdPosTerm (k : ℕ) : ℝ :=
  ∑ o ∈ Finset.range (k + 1),
    if 2 ^ (k + o) < 3 ^ k then (Nat.choose k o : ℝ) / 2 ^ k else 0

/-- The backward probability of finishing strictly above the start after `k` steps. -/
noncomputable def bwdPosTerm (k : ℕ) : ℝ :=
  ∑ o ∈ Finset.range (k + 1),
    if 3 ^ k < 2 ^ (k + o) then (Nat.choose k o : ℝ) * 2 ^ o / 3 ^ k else 0

/-- No endpoint of either multiplicative walk is tied with its start at positive time. -/
theorem walk_endpoint_ne (k o : ℕ) (hk : 0 < k) :
    (2 : ℕ) ^ (k + o) ≠ 3 ^ k := by
  exact Ne.symm (three_pow_ne_two_pow (a := k) (b := k + o) hk)

/-- **Haar duality, termwise form.**  At each positive time, the Spitzer contribution splits
exactly into the forward and backward probabilities of finishing at or below the start. -/
theorem spitzerTerm_eq_fwdNonposTerm_add_bwdNonposTerm (k : ℕ) (hk : 0 < k) :
    spitzerTerm k = fwdNonposTerm k + bwdNonposTerm k := by
  rw [spitzerTerm, fwdNonposTerm, bwdNonposTerm, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro o ho
  have hone : (0 : ℝ) < 2 ^ k := by positivity
  have hthree : (0 : ℝ) < 3 ^ k := by positivity
  have hneNat : (2 : ℕ) ^ (k + o) ≠ 3 ^ k := walk_endpoint_ne k o hk
  rcases lt_or_gt_of_ne hneNat with hlt | hgt
  · rw [if_neg (by exact_mod_cast (not_lt_of_ge hlt.le)), if_pos (by exact_mod_cast hlt)]
    rw [min_eq_right (by
      apply (div_le_one hthree).2
      exact_mod_cast hlt.le)]
    field_simp
    ring
  · rw [if_pos (by exact_mod_cast hgt), if_neg (by exact_mod_cast (not_lt_of_ge hgt.le))]
    rw [min_eq_left (by
      apply (one_le_div hthree).2
      exact_mod_cast hgt.le)]
    ring

/-- At positive time, the forward endpoint is either strictly positive or nonpositive, and the
two binomial masses sum to one. -/
theorem fwdNonposTerm_add_fwdPosTerm (k : ℕ) (hk : 0 < k) :
    fwdNonposTerm k + fwdPosTerm k = 1 := by
  rw [fwdNonposTerm, fwdPosTerm, ← Finset.sum_add_distrib]
  calc
    _ = ∑ o ∈ Finset.range (k + 1), (Nat.choose k o : ℝ) / 2 ^ k := by
      apply Finset.sum_congr rfl
      intro o ho
      have hne : (2 : ℕ) ^ (k + o) ≠ 3 ^ k := walk_endpoint_ne k o hk
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [if_neg (by exact_mod_cast (not_lt_of_ge hlt.le)), if_pos (by exact_mod_cast hlt)]
        ring
      · rw [if_pos (by exact_mod_cast hgt), if_neg (by exact_mod_cast (not_lt_of_ge hgt.le))]
        ring
    _ = (∑ o ∈ Finset.range (k + 1), (Nat.choose k o : ℝ)) / 2 ^ k := by
      rw [Finset.sum_div]
    _ = 1 := by
      rw [← Nat.cast_sum, Nat.sum_range_choose]
      norm_num

/-- At positive time, the backward endpoint is either strictly positive or nonpositive, and the
two tilted binomial masses sum to one. -/
theorem bwdNonposTerm_add_bwdPosTerm (k : ℕ) (hk : 0 < k) :
    bwdNonposTerm k + bwdPosTerm k = 1 := by
  rw [bwdNonposTerm, bwdPosTerm, ← Finset.sum_add_distrib]
  calc
    _ = ∑ o ∈ Finset.range (k + 1), (Nat.choose k o : ℝ) * 2 ^ o / 3 ^ k := by
      apply Finset.sum_congr rfl
      intro o ho
      have hne : (2 : ℕ) ^ (k + o) ≠ 3 ^ k := walk_endpoint_ne k o hk
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [if_pos (by exact_mod_cast hlt), if_neg (by exact_mod_cast (not_lt_of_ge hlt.le))]
        ring
      · rw [if_neg (by exact_mod_cast (not_lt_of_ge hgt.le)), if_pos (by exact_mod_cast hgt)]
        ring
    _ = (∑ o ∈ Finset.range (k + 1), (Nat.choose k o : ℝ) * 2 ^ o) / 3 ^ k := by
      rw [Finset.sum_div]
    _ = 1 := by
      have hbinom := add_pow (2 : ℝ) 1 k
      simp only [one_pow, mul_one] at hbinom
      rw [add_comm] at hbinom
      have htotal : (3 : ℝ) ^ k =
          ∑ o ∈ Finset.range (k + 1), (Nat.choose k o : ℝ) * 2 ^ o := by
        norm_num [mul_comm] at hbinom ⊢
        exact hbinom
      rw [← htotal]
      norm_num

/-! ## Finite-word probability interface

The Sparre--Andersen recurrence is a weighted identity on finite words.  The following
regrouping lemma puts the endpoint binomial sums and the prefix-survival sums on that common
sample space. -/

/-- Number of marked (`true`) letters in a finite Boolean word. -/
def wordTrueCount {L : ℕ} (w : Fin L → Bool) : ℕ :=
  (Finset.univ.filter fun i => w i = true).card

theorem wordTrueCount_cons {L : ℕ} (b : Bool) (w : Fin L → Bool) :
    wordTrueCount (Fin.cons b w) = (if b then 1 else 0) + wordTrueCount w := by
  simp only [wordTrueCount]
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp

/-- Split a sum over Boolean words according to its first letter. -/
theorem sum_boolWords_succ {M : Type*} [AddCommMonoid M] (L : ℕ)
    (F : (Fin (L + 1) → Bool) → M) :
    (∑ w : Fin (L + 1) → Bool, F w) =
      ∑ b : Bool, ∑ w : Fin L → Bool, F (Fin.cons b w) := by
  calc
    _ = ∑ p : Bool × (Fin L → Bool),
          F ((Fin.consEquiv fun _ : Fin (L + 1) => Bool) p) :=
      ((Fin.consEquiv fun _ : Fin (L + 1) => Bool).sum_comp F).symm
    _ = _ := by rw [Fintype.sum_prod_type]; rfl

theorem sum_boolWords_by_trueCount_succ {M : Type*} [AddCommMonoid M]
    (L : ℕ) (f : ℕ → M) :
    (∑ w : Fin (L + 1) → Bool, f (wordTrueCount w)) =
      ∑ w : Fin L → Bool,
        (f (wordTrueCount w) + f (wordTrueCount w + 1)) := by
  rw [sum_boolWords_succ]
  simp [wordTrueCount_cons, add_comm, ← Finset.sum_add_distrib]

/-- Regroup any finite Boolean-word sum depending only on the number of marked letters into
the corresponding binomial sum. -/
theorem sum_boolWords_by_trueCount {M : Type*} [AddCommMonoid M]
    (L : ℕ) (f : ℕ → M) :
    (∑ w : Fin L → Bool, f (wordTrueCount w)) =
      ∑ o ∈ Finset.range (L + 1), L.choose o • f o := by
  induction L generalizing f with
  | zero => simp [wordTrueCount]
  | succ L ih =>
      rw [sum_boolWords_by_trueCount_succ]
      rw [Finset.sum_add_distrib, ih f, ih (fun o => f (o + 1))]
      rw [Finset.sum_range_succ' (fun o => L.choose o • f o) L,
        Finset.sum_range_succ (fun o => L.choose o • f (o + 1)) L,
        Finset.sum_range_succ (fun o => (L + 1).choose o • f o) (L + 1),
        Finset.sum_range_succ' (fun o => (L + 1).choose o • f o) L]
      simp only [Nat.choose_zero_right, Nat.choose_self, one_nsmul,
        Nat.choose_succ_succ, add_nsmul]
      calc
        _ = f 0 + f (L + 1) +
            ((∑ x ∈ Finset.range L, L.choose x • f (x + 1)) +
              ∑ x ∈ Finset.range L, L.choose (x + 1) • f (x + 1)) := by ac_rfl
        _ = f 0 + f (L + 1) +
            ∑ x ∈ Finset.range L,
              (L.choose x • f (x + 1) + L.choose (x + 1) • f (x + 1)) := by
          rw [Finset.sum_add_distrib]
        _ = _ := by simp only [Nat.succ_eq_add_one]; ac_rfl

/-- The forward positive-endpoint mass, expressed on the same Boolean-word sample space as
`fwdSurv`. -/
theorem fwdPosTerm_eq_word_sum (k : ℕ) :
    fwdPosTerm k = ∑ w : Fin k → Bool,
      if 2 ^ (k + wordTrueCount w) < 3 ^ k then (1 / 2 : ℝ) ^ k else 0 := by
  rw [sum_boolWords_by_trueCount k (fun o =>
    if 2 ^ (k + o) < 3 ^ k then (1 / 2 : ℝ) ^ k else 0)]
  unfold fwdPosTerm
  apply Finset.sum_congr rfl
  intro o ho
  simp only [nsmul_eq_mul]
  split_ifs
  · rw [one_div, inv_pow, div_eq_mul_inv]
  · simp

/-- The backward positive-endpoint mass, expressed on the same weighted Boolean-word sample
space as `bwdSurv`. -/
theorem bwdPosTerm_eq_word_sum (k : ℕ) :
    bwdPosTerm k = ∑ w : Fin k → Bool,
      if 3 ^ k < 2 ^ (k + wordTrueCount w) then
        (2 / 3 : ℝ) ^ wordTrueCount w * (1 / 3 : ℝ) ^ (k - wordTrueCount w) else 0 := by
  rw [sum_boolWords_by_trueCount k (fun o => if 3 ^ k < 2 ^ (k + o) then
    (2 / 3 : ℝ) ^ o * (1 / 3 : ℝ) ^ (k - o) else 0)]
  unfold bwdPosTerm
  apply Finset.sum_congr rfl
  intro o ho
  simp only [nsmul_eq_mul]
  split_ifs
  · have ho' : o ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp ho)
    rw [show k = o + (k - o) by omega, pow_add]
    rw [div_pow, div_pow]
    rw [show o + (k - o) - o = k - o by omega]
    ring
  · simp

/-- Forward survival, cast to reals, is its finite weighted sum over good Boolean words. -/
theorem fwdSurv_cast_eq_word_sum (k : ℕ) :
    (fwdSurv k : ℝ) = ∑ w : Fin k → Bool,
      if FwdGood k w then (1 / 2 : ℝ) ^ k else 0 := by
  unfold fwdSurv
  push_cast
  apply Finset.sum_congr rfl
  intro w hw
  split_ifs <;> norm_num

/-- Backward survival, cast to reals, is its finite weighted sum over good Boolean words. -/
theorem bwdSurv_cast_eq_word_sum (k : ℕ) :
    (bwdSurv k : ℝ) = ∑ w : Fin k → Bool,
      if BwdGood k w then
        (2 / 3 : ℝ) ^ wordTrueCount w * (1 / 3 : ℝ) ^ (k - wordTrueCount w) else 0 := by
  unfold bwdSurv wordTrueCount
  push_cast
  apply Finset.sum_congr rfl
  intro w hw
  split_ifs
  · have hcard := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin k))) (fun i => w i = true)
    have hfalse : (Finset.univ.filter fun i : Fin k => w i = false).card =
        k - (Finset.univ.filter fun i : Fin k => w i = true).card := by
      have hcard' : (Finset.univ.filter fun i : Fin k => w i = true).card +
          (Finset.univ.filter fun i : Fin k => w i = false).card = k := by
        simpa using hcard
      omega
    rw [hfalse]
    norm_num
  · norm_num

/-- **Target (treadmill).**  `fwdSurv L * bwdSurv L → minimaConstant`. -/
theorem windowDensityLimit : WindowDensityLimit := by
  sorry

open Classical in
/-- Orbit minima have upper density at most `minimaConstant ≈ 0.049780`. -/
theorem orbitMin_density_le_minimaConstant' {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in Filter.atTop,
      (((Finset.range X).filter fun m : ℕ => IsOrbitMin m).card : ℝ) / X ≤ minimaConstant + ε :=
  orbitMin_density_le_minimaConstant windowDensityLimit hε

end CollatzMoonshot.Amusical
