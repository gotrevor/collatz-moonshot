/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalConstant
import CollatzMoonshot.CycleDiophantine
import CollatzMoonshot.CyclicMinimum

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

/-! ## Summability of the Spitzer series -/

/-- The elementary square-root majorant used to obtain exponential decay of the Spitzer
terms. -/
theorem min_one_le_sqrt (x : ℝ) : min 1 x ≤ √x := by
  rcases le_total x 1 with hx | hx
  · rw [min_eq_right hx]
    exact Real.le_sqrt_self_iff.mpr hx
  · rw [min_eq_left hx]
    exact Real.one_le_sqrt.mpr hx

/-- Square root commutes with natural powers of a nonnegative real. -/
theorem sqrt_pow_of_nonneg (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    √(x ^ n) = (√x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Real.sqrt_mul (pow_nonneg hx n), ih, pow_succ]

/-- Factor the square root of a walk's Radon--Nikodym weight into its independent-step
factors. -/
theorem sqrt_walk_weight (k o : ℕ) :
    √((2 : ℝ) ^ (k + o) / 3 ^ k) =
      (√((2 : ℝ) / 3)) ^ k * (√(2 : ℝ)) ^ o := by
  calc
    √((2 : ℝ) ^ (k + o) / 3 ^ k) =
        √(((2 : ℝ) / 3) ^ k * 2 ^ o) := by
          congr 1
          rw [pow_add, div_pow]
          ring
    _ = √(((2 : ℝ) / 3) ^ k) * √((2 : ℝ) ^ o) := by
      rw [Real.sqrt_mul (by positivity)]
    _ = (√((2 : ℝ) / 3)) ^ k * (√(2 : ℝ)) ^ o := by
      rw [sqrt_pow_of_nonneg _ (by positivity), sqrt_pow_of_nonneg _ (by positivity)]

/-- A strict geometric rate dominating `spitzerTerm`.  Numerically this is about
`0.985598`. -/
noncomputable def spitzerRate : ℝ :=
  √((2 : ℝ) / 3) * (1 + √(2 : ℝ)) / 2

theorem spitzerRate_nonneg : 0 ≤ spitzerRate := by
  unfold spitzerRate
  positivity

theorem spitzerRate_lt_one : spitzerRate < 1 := by
  have hb : √(2 : ℝ) < 3 / 2 := by
    rw [Real.sqrt_lt (by norm_num) (by norm_num)]
    norm_num
  have ha_sq : (√((2 : ℝ) / 3)) ^ 2 = 2 / 3 :=
    Real.sq_sqrt (by norm_num)
  have hb_sq : (√(2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsq : (√((2 : ℝ) / 3) * (1 + √(2 : ℝ))) ^ 2 < (2 : ℝ) ^ 2 := by
    rw [mul_pow, ha_sq]
    nlinarith
  have hprod : √((2 : ℝ) / 3) * (1 + √(2 : ℝ)) < 2 :=
    (sq_lt_sq₀ (by positivity) (by positivity)).mp hsq
  unfold spitzerRate
  linarith

theorem spitzerTerm_nonneg (k : ℕ) : 0 ≤ spitzerTerm k := by
  unfold spitzerTerm
  apply Finset.sum_nonneg
  intro o ho
  positivity

/-- The Spitzer contributions decay geometrically, by the square-root moment of the walk. -/
theorem spitzerTerm_le_rate_pow (k : ℕ) : spitzerTerm k ≤ spitzerRate ^ k := by
  unfold spitzerTerm
  calc
    (∑ o ∈ Finset.range (k + 1),
        (Nat.choose k o : ℝ) / 2 ^ k * min 1 ((2 : ℝ) ^ (k + o) / 3 ^ k)) ≤
        ∑ o ∈ Finset.range (k + 1),
          (Nat.choose k o : ℝ) / 2 ^ k * √((2 : ℝ) ^ (k + o) / 3 ^ k) := by
      apply Finset.sum_le_sum
      intro o ho
      exact mul_le_mul_of_nonneg_left (min_one_le_sqrt _) (by positivity)
    _ = ∑ o ∈ Finset.range (k + 1),
          (Nat.choose k o : ℝ) / 2 ^ k *
            ((√((2 : ℝ) / 3)) ^ k * (√(2 : ℝ)) ^ o) := by
      apply Finset.sum_congr rfl
      intro o ho
      rw [sqrt_walk_weight]
    _ = ((√((2 : ℝ) / 3)) ^ k / 2 ^ k) *
          ∑ o ∈ Finset.range (k + 1),
            (Nat.choose k o : ℝ) * (√(2 : ℝ)) ^ o := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro o ho
      ring
    _ = ((√((2 : ℝ) / 3)) ^ k / 2 ^ k) * (1 + √(2 : ℝ)) ^ k := by
      have hbinom := add_pow (√(2 : ℝ)) 1 k
      simp only [one_pow, mul_one] at hbinom
      rw [add_comm] at hbinom
      congr 1
      simpa only [mul_comm] using hbinom.symm
    _ = spitzerRate ^ k := by
      unfold spitzerRate
      calc
        ((√((2 : ℝ) / 3)) ^ k / 2 ^ k) * (1 + √(2 : ℝ)) ^ k =
            (√((2 : ℝ) / 3) * (1 + √(2 : ℝ))) ^ k / 2 ^ k := by
          rw [mul_pow]
          ring
        _ = (√((2 : ℝ) / 3) * (1 + √(2 : ℝ)) / 2) ^ k := by
          rw [div_pow]

/-- The series appearing in the definition of `minimaConstant` is summable. -/
theorem summable_spitzerSeries :
    Summable (fun k : ℕ => spitzerTerm (k + 1) / (k + 1)) := by
  apply Summable.of_nonneg_of_le
  · intro k
    exact div_nonneg (spitzerTerm_nonneg _) (by positivity)
  · intro k
    calc
      spitzerTerm (k + 1) / (k + 1) ≤ spitzerTerm (k + 1) := by
        apply div_le_self
        · exact spitzerTerm_nonneg _
        · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega : k + 1 ≠ 0)
      _ ≤ spitzerRate ^ (k + 1) := spitzerTerm_le_rate_pow _
      _ ≤ spitzerRate ^ k := by
        rw [pow_succ]
        exact mul_le_of_le_one_right (pow_nonneg spitzerRate_nonneg k) spitzerRate_lt_one.le
  · exact summable_geometric_of_lt_one spitzerRate_nonneg spitzerRate_lt_one

theorem fwdNonposTerm_nonneg (k : ℕ) : 0 ≤ fwdNonposTerm k := by
  unfold fwdNonposTerm
  apply Finset.sum_nonneg
  intro o ho
  split_ifs <;> positivity

theorem bwdNonposTerm_nonneg (k : ℕ) : 0 ≤ bwdNonposTerm k := by
  unfold bwdNonposTerm
  apply Finset.sum_nonneg
  intro o ho
  split_ifs <;> positivity

theorem fwdNonposTerm_le_spitzerTerm (k : ℕ) (hk : 0 < k) :
    fwdNonposTerm k ≤ spitzerTerm k := by
  rw [spitzerTerm_eq_fwdNonposTerm_add_bwdNonposTerm k hk]
  exact le_add_of_nonneg_right (bwdNonposTerm_nonneg k)

theorem bwdNonposTerm_le_spitzerTerm (k : ℕ) (hk : 0 < k) :
    bwdNonposTerm k ≤ spitzerTerm k := by
  rw [spitzerTerm_eq_fwdNonposTerm_add_bwdNonposTerm k hk]
  exact le_add_of_nonneg_left (fwdNonposTerm_nonneg k)

/-- The forward nonpositive endpoint series is summable. -/
theorem summable_fwdNonposSeries :
    Summable (fun k : ℕ => fwdNonposTerm (k + 1) / (k + 1)) := by
  apply Summable.of_nonneg_of_le
  · intro k
    exact div_nonneg (fwdNonposTerm_nonneg _) (by positivity)
  · intro k
    exact div_le_div_of_nonneg_right
      (fwdNonposTerm_le_spitzerTerm _ (by omega)) (by positivity)
  · exact summable_spitzerSeries

/-- The backward nonpositive endpoint series is summable. -/
theorem summable_bwdNonposSeries :
    Summable (fun k : ℕ => bwdNonposTerm (k + 1) / (k + 1)) := by
  apply Summable.of_nonneg_of_le
  · intro k
    exact div_nonneg (bwdNonposTerm_nonneg _) (by positivity)
  · intro k
    exact div_le_div_of_nonneg_right
      (bwdNonposTerm_le_spitzerTerm _ (by omega)) (by positivity)
  · exact summable_spitzerSeries

/-- Pointwise Haar duality for the normalized Spitzer series. -/
theorem spitzerSeries_eq_fwd_add_bwd (k : ℕ) :
    spitzerTerm (k + 1) / (k + 1) =
      fwdNonposTerm (k + 1) / (k + 1) + bwdNonposTerm (k + 1) / (k + 1) := by
  rw [spitzerTerm_eq_fwdNonposTerm_add_bwdNonposTerm (k + 1) (by omega)]
  ring

/-- The two directional endpoint series merge exactly into the series defining
`minimaConstant`. -/
theorem tsum_spitzerSeries_eq_fwd_add_bwd :
    (∑' k : ℕ, spitzerTerm (k + 1) / (k + 1)) =
      (∑' k : ℕ, fwdNonposTerm (k + 1) / (k + 1)) +
        ∑' k : ℕ, bwdNonposTerm (k + 1) / (k + 1) := by
  rw [← Summable.tsum_add summable_fwdNonposSeries summable_bwdNonposSeries]
  apply tsum_congr
  exact spitzerSeries_eq_fwd_add_bwd

/-- The constant factors into the two directional Sparre--Andersen limits. -/
theorem minimaConstant_eq_directionalFactors :
    minimaConstant =
      Real.exp (-(∑' k : ℕ, fwdNonposTerm (k + 1) / (k + 1))) *
        Real.exp (-(∑' k : ℕ, bwdNonposTerm (k + 1) / (k + 1))) := by
  rw [minimaConstant, tsum_spitzerSeries_eq_fwd_add_bwd, neg_add, Real.exp_add]

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

/-- Permuting the positions of a Boolean word does not change its number of marked letters. -/
theorem wordTrueCount_comp_equiv {L : ℕ} (w : Fin L → Bool) (e : Fin L ≃ Fin L) :
    wordTrueCount (w ∘ e) = wordTrueCount w := by
  unfold wordTrueCount
  apply Finset.card_bijective e e.bijective
  intro i
  simp [Function.comp_apply]

/-- In particular, cyclic rotation preserves the number of marked letters. -/
theorem wordTrueCount_rotate {L : ℕ} (w : Fin L → Bool) :
    wordTrueCount (w ∘ finRotate L) = wordTrueCount w :=
  wordTrueCount_comp_equiv w (finRotate L)

/-- Product weight of a word for the forward walk. -/
noncomputable def fwdWordWeight {L : ℕ} (_w : Fin L → Bool) : ℝ :=
  (1 / 2 : ℝ) ^ L

/-- Product weight of a word for the backward walk. -/
noncomputable def bwdWordWeight {L : ℕ} (w : Fin L → Bool) : ℝ :=
  (2 / 3 : ℝ) ^ wordTrueCount w * (1 / 3 : ℝ) ^ (L - wordTrueCount w)

/-- The forward product weight of a word is invariant under any permutation of its letters. -/
theorem fwdWordWeight_comp_equiv {L : ℕ} (w : Fin L → Bool) (e : Fin L ≃ Fin L) :
    fwdWordWeight (w ∘ e) = fwdWordWeight w := rfl

/-- The backward product weight of a word is invariant under any permutation of its letters. -/
theorem bwdWordWeight_comp_equiv {L : ℕ} (w : Fin L → Bool) (e : Fin L ≃ Fin L) :
    bwdWordWeight (w ∘ e) = bwdWordWeight w := by
  unfold bwdWordWeight
  rw [wordTrueCount_comp_equiv]

theorem fwdWordWeight_rotate {L : ℕ} (w : Fin L → Bool) :
    fwdWordWeight (w ∘ finRotate L) = fwdWordWeight w :=
  fwdWordWeight_comp_equiv w (finRotate L)

theorem bwdWordWeight_rotate {L : ℕ} (w : Fin L → Bool) :
    bwdWordWeight (w ∘ finRotate L) = bwdWordWeight w :=
  bwdWordWeight_comp_equiv w (finRotate L)

/-- A block with `k` letters and `o` marked letters can never have multiplicative score one
when `k` is positive.  This applies to every nonempty contiguous block of either walk because
its score depends only on these two counts. -/
theorem wordBlock_endpoint_ne (k o : ℕ) (hk : 0 < k) :
    (2 : ℕ) ^ (k + o) ≠ 3 ^ k :=
  walk_endpoint_ne k o hk

/-- Every nonempty block has one of the two strict score signs. -/
theorem wordBlock_endpoint_lt_or_gt (k o : ℕ) (hk : 0 < k) :
    (2 : ℕ) ^ (k + o) < 3 ^ k ∨ 3 ^ k < 2 ^ (k + o) :=
  lt_or_gt_of_ne (wordBlock_endpoint_ne k o hk)

theorem wordTrueCount_cons {L : ℕ} (b : Bool) (w : Fin L → Bool) :
    wordTrueCount (Fin.cons b w) = (if b then 1 else 0) + wordTrueCount w := by
  simp only [wordTrueCount]
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp

/-- Marked-letter counts add under concatenation. -/
theorem wordTrueCount_append {m n : ℕ} (u : Fin m → Bool) (v : Fin n → Bool) :
    wordTrueCount (Fin.append u v) = wordTrueCount u + wordTrueCount v := by
  unfold wordTrueCount
  repeat' rw [Finset.card_filter]
  rw [Fin.sum_univ_add]
  simp

theorem wordTrueCount_le {L : ℕ} (w : Fin L → Bool) : wordTrueCount w ≤ L := by
  unfold wordTrueCount
  calc
    (Finset.univ.filter fun i => w i = true).card ≤ Finset.univ.card :=
      Finset.card_filter_le _ _
    _ = L := Fintype.card_fin L

/-- Taking a prefix turns the filtered count used in `FwdGood` and `BwdGood` into the
ordinary marked-letter count of a shorter word. -/
theorem wordTrueCount_take {L : ℕ} (w : Fin L → Bool) (t : ℕ) (ht : t ≤ L) :
    wordTrueCount (Fin.take t ht w) =
      (Finset.univ.filter fun i : Fin L => i.val < t ∧ w i = true).card := by
  unfold wordTrueCount
  refine Finset.card_bij (fun i _ => Fin.castLE ht i) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact ⟨i.isLt, hi⟩
  · intro i₁ hi₁ i₂ hi₂ h
    exact Fin.castLE_injective ht h
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    refine ⟨⟨i, hi.1⟩, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have heq : Fin.castLE ht ⟨i, hi.1⟩ = i := by ext; rfl
      simpa only [Fin.take_apply, heq] using hi.2
    · rfl

/-- A forward word finishes strictly above its starting point. -/
def FwdEndpointPositive {L : ℕ} (w : Fin L → Bool) : Prop :=
  2 ^ (L + wordTrueCount w) < 3 ^ L

/-- A backward word finishes strictly above its starting point. -/
def BwdEndpointPositive {L : ℕ} (w : Fin L → Bool) : Prop :=
  3 ^ L < 2 ^ (L + wordTrueCount w)

/-- Forward survival is exactly strict positivity of every nonempty prefix word. -/
theorem fwdGood_iff_prefix_positive {L : ℕ} (w : Fin L → Bool) :
    FwdGood L w ↔
      ∀ (t : ℕ) (ht0 : 0 < t) (htL : t ≤ L),
        FwdEndpointPositive (Fin.take t htL w) := by
  constructor
  · intro hw t ht0 htL
    simpa only [FwdEndpointPositive, wordTrueCount_take] using hw t ht0 htL
  · intro hw t ht0 htL
    simpa only [FwdEndpointPositive, wordTrueCount_take] using hw t ht0 htL

/-- Backward survival is exactly strict positivity of every nonempty prefix word. -/
theorem bwdGood_iff_prefix_positive {L : ℕ} (w : Fin L → Bool) :
    BwdGood L w ↔
      ∀ (t : ℕ) (ht0 : 0 < t) (htL : t ≤ L),
        BwdEndpointPositive (Fin.take t htL w) := by
  constructor
  · intro hw t ht0 htL
    simpa only [BwdEndpointPositive, wordTrueCount_take] using hw t ht0 htL
  · intro hw t ht0 htL
    simpa only [BwdEndpointPositive, wordTrueCount_take] using hw t ht0 htL

/-! ## Additive score interface for the cyclic-minimum lemma -/

/-- Additive logarithmic score of one forward letter. -/
noncomputable def fwdStepScore (b : Bool) : ℝ :=
  Real.log 3 - (if b then 2 else 1) * Real.log 2

/-- Additive logarithmic scores of the letters in a forward word. -/
noncomputable def fwdScoreList {L : ℕ} (w : Fin L → Bool) : List ℝ :=
  List.ofFn fun i => fwdStepScore (w i)

/-- Total additive logarithmic score of a forward word. -/
noncomputable def fwdScore {L : ℕ} (w : Fin L → Bool) : ℝ :=
  ∑ i, fwdStepScore (w i)

/-- The forward additive score written in terms of length and marked-letter count. -/
theorem fwdScore_eq {L : ℕ} (w : Fin L → Bool) :
    fwdScore w =
      (L : ℝ) * Real.log 3 - (L + wordTrueCount w : ℕ) * Real.log 2 := by
  induction L with
  | zero => simp [fwdScore, wordTrueCount]
  | succ L ih =>
      have hcount : wordTrueCount w =
          (if w 0 then 1 else 0) + wordTrueCount (Fin.tail w) := by
        rw [← Fin.cons_self_tail w, wordTrueCount_cons]
        simp
      rw [fwdScore, Fin.sum_univ_succ]
      change fwdStepScore (w 0) + fwdScore (Fin.tail w) = _
      rw [ih, hcount]
      cases w 0 <;> simp [fwdStepScore] <;> ring

theorem fwdScoreList_sum {L : ℕ} (w : Fin L → Bool) :
    (fwdScoreList w).sum =
      (L : ℝ) * Real.log 3 - (L + wordTrueCount w : ℕ) * Real.log 2 := by
  rw [fwdScoreList, List.sum_ofFn]
  exact fwdScore_eq w

theorem fwdScoreList_sum_eq_score {L : ℕ} (w : Fin L → Bool) :
    (fwdScoreList w).sum = fwdScore w := by
  rw [fwdScoreList, List.sum_ofFn]
  rfl

/-- The additive score has the same strict sign as the forward multiplicative score. -/
theorem fwdEndpointPositive_iff_score_pos {L : ℕ} (w : Fin L → Bool) :
    FwdEndpointPositive w ↔ 0 < fwdScore w := by
  rw [FwdEndpointPositive, fwdScore_eq]
  constructor
  · intro h
    have hR : (2 : ℝ) ^ (L + wordTrueCount w) < (3 : ℝ) ^ L := by
      exact_mod_cast h
    have hlog := Real.log_lt_log (by positivity) hR
    rw [Real.log_pow, Real.log_pow] at hlog
    push_cast at hlog ⊢
    linarith
  · intro h
    have hlog : Real.log ((2 : ℝ) ^ (L + wordTrueCount w)) <
        Real.log ((3 : ℝ) ^ L) := by
      rw [Real.log_pow, Real.log_pow]
      push_cast at h ⊢
      linarith
    have hR : (2 : ℝ) ^ (L + wordTrueCount w) < (3 : ℝ) ^ L :=
      (Real.log_lt_log_iff (by positivity) (by positivity)).mp hlog
    exact_mod_cast hR

theorem fwdScoreList_take {L t : ℕ} (ht : t ≤ L) (w : Fin L → Bool) :
    (fwdScoreList w).take t = fwdScoreList (Fin.take t ht w) := by
  unfold fwdScoreList
  rw [← Fin.ofFn_take_eq_take_ofFn ht (fun i => fwdStepScore (w i))]
  rfl

/-- Forward survival is strict positivity of every prefix of the additive score list. -/
theorem fwdGood_iff_strictlyPositivePrefixes {L : ℕ} (w : Fin L → Bool) :
    FwdGood L w ↔ CollatzMoonshot.StrictlyPositivePrefixes (fwdScoreList w) := by
  rw [fwdGood_iff_prefix_positive]
  constructor
  · intro hw t ht0 htlen
    have htL : t ≤ L := by simpa [fwdScoreList] using htlen
    rw [fwdScoreList_take htL, fwdScoreList_sum_eq_score]
    exact (fwdEndpointPositive_iff_score_pos _).mp (hw t ht0 htL)
  · intro hw t ht0 htL
    apply (fwdEndpointPositive_iff_score_pos _).mpr
    rw [← fwdScoreList_sum_eq_score, ← fwdScoreList_take htL]
    exact hw t ht0 (by simpa [fwdScoreList])

/-- The backward additive score reverses the forward logarithmic score. -/
noncomputable def bwdStepScore (b : Bool) : ℝ := -fwdStepScore b

/-- Additive logarithmic scores of the letters in a backward word. -/
noncomputable def bwdScoreList {L : ℕ} (w : Fin L → Bool) : List ℝ :=
  List.ofFn fun i => bwdStepScore (w i)

/-- Total additive logarithmic score of a backward word. -/
noncomputable def bwdScore {L : ℕ} (w : Fin L → Bool) : ℝ :=
  ∑ i, bwdStepScore (w i)

theorem bwdScore_eq_neg_fwdScore {L : ℕ} (w : Fin L → Bool) :
    bwdScore w = -fwdScore w := by
  simp [bwdScore, bwdStepScore, fwdScore]

theorem bwdScoreList_sum_eq_score {L : ℕ} (w : Fin L → Bool) :
    (bwdScoreList w).sum = bwdScore w := by
  rw [bwdScoreList, List.sum_ofFn]
  rfl

/-- The additive score has the same strict sign as the backward multiplicative score. -/
theorem bwdEndpointPositive_iff_score_pos {L : ℕ} (w : Fin L → Bool) :
    BwdEndpointPositive w ↔ 0 < bwdScore w := by
  rw [BwdEndpointPositive, bwdScore_eq_neg_fwdScore, fwdScore_eq]
  constructor
  · intro h
    have hR : (3 : ℝ) ^ L < (2 : ℝ) ^ (L + wordTrueCount w) := by
      exact_mod_cast h
    have hlog := Real.log_lt_log (by positivity) hR
    rw [Real.log_pow, Real.log_pow] at hlog
    push_cast at hlog ⊢
    linarith
  · intro h
    have hlog : Real.log ((3 : ℝ) ^ L) <
        Real.log ((2 : ℝ) ^ (L + wordTrueCount w)) := by
      rw [Real.log_pow, Real.log_pow]
      push_cast at h ⊢
      linarith
    have hR : (3 : ℝ) ^ L < (2 : ℝ) ^ (L + wordTrueCount w) :=
      (Real.log_lt_log_iff (by positivity) (by positivity)).mp hlog
    exact_mod_cast hR

theorem bwdScoreList_take {L t : ℕ} (ht : t ≤ L) (w : Fin L → Bool) :
    (bwdScoreList w).take t = bwdScoreList (Fin.take t ht w) := by
  unfold bwdScoreList
  rw [← Fin.ofFn_take_eq_take_ofFn ht (fun i => bwdStepScore (w i))]
  rfl

/-- Backward survival is strict positivity of every prefix of the additive score list. -/
theorem bwdGood_iff_strictlyPositivePrefixes {L : ℕ} (w : Fin L → Bool) :
    BwdGood L w ↔ CollatzMoonshot.StrictlyPositivePrefixes (bwdScoreList w) := by
  rw [bwdGood_iff_prefix_positive]
  constructor
  · intro hw t ht0 htlen
    have htL : t ≤ L := by simpa [bwdScoreList] using htlen
    rw [bwdScoreList_take htL, bwdScoreList_sum_eq_score]
    exact (bwdEndpointPositive_iff_score_pos _).mp (hw t ht0 htL)
  · intro hw t ht0 htL
    apply (bwdEndpointPositive_iff_score_pos _).mpr
    rw [← bwdScoreList_sum_eq_score, ← bwdScoreList_take htL]
    exact hw t ht0 (by simpa [bwdScoreList])

/-- Every nonempty forward word has nonzero additive score. -/
theorem fwdScore_ne_zero {L : ℕ} (w : Fin L → Bool) (hL : 0 < L) :
    fwdScore w ≠ 0 := by
  rcases wordBlock_endpoint_lt_or_gt L (wordTrueCount w) hL with hf | hb
  · exact ne_of_gt ((fwdEndpointPositive_iff_score_pos w).mp hf)
  · have hbpos : 0 < bwdScore w :=
      (bwdEndpointPositive_iff_score_pos w).mp hb
    rw [bwdScore_eq_neg_fwdScore] at hbpos
    exact ne_of_lt (by linarith)

theorem fwdScoreList_sum_ne_zero {L : ℕ} (w : Fin L → Bool) (hL : 0 < L) :
    (fwdScoreList w).sum ≠ 0 := by
  rw [fwdScoreList_sum_eq_score]
  exact fwdScore_ne_zero w hL

theorem fwdScoreList_eq_map {L : ℕ} (w : Fin L → Bool) :
    fwdScoreList w = (List.ofFn w).map fwdStepScore := by
  rw [fwdScoreList, List.map_ofFn]
  rfl

/-- Every nonempty contiguous block of a forward score list has nonzero sum. -/
theorem fwdScoreList_block_ne_zero {L : ℕ} (w : Fin L → Bool) (i n : ℕ)
    (hn : 0 < n) (hin : i + n ≤ L) :
    (((fwdScoreList w).drop i).take n).sum ≠ 0 := by
  let letters := ((List.ofFn w).drop i).take n
  have hlen : letters.length = n := by
    simp only [letters, List.length_take, List.length_drop, List.length_ofFn]
    rw [min_eq_left]
    omega
  have hv := fwdScoreList_sum_ne_zero letters.get (by simpa [hlen] using hn)
  rw [fwdScoreList_eq_map, List.ofFn_get] at hv
  rw [fwdScoreList_eq_map, ← List.map_drop, ← List.map_take]
  simpa only [letters] using hv

/-- Prefix sums of every forward score list are pairwise distinct. -/
theorem fwdScoreList_prefixSums_ne {L : ℕ} (w : Fin L → Bool) :
    ∀ i j : ℕ, i < j → j ≤ (fwdScoreList w).length →
      ((fwdScoreList w).take i).sum ≠ ((fwdScoreList w).take j).sum := by
  apply CollatzMoonshot.prefixSums_ne_of_blocks_ne_zero
  intro i n hn hin
  apply fwdScoreList_block_ne_zero w i n hn
  simpa [fwdScoreList] using hin

/-- Every nonempty backward word has nonzero additive score. -/
theorem bwdScore_ne_zero {L : ℕ} (w : Fin L → Bool) (hL : 0 < L) :
    bwdScore w ≠ 0 := by
  rw [bwdScore_eq_neg_fwdScore]
  exact neg_ne_zero.mpr (fwdScore_ne_zero w hL)

theorem bwdScoreList_sum_ne_zero {L : ℕ} (w : Fin L → Bool) (hL : 0 < L) :
    (bwdScoreList w).sum ≠ 0 := by
  rw [bwdScoreList_sum_eq_score]
  exact bwdScore_ne_zero w hL

theorem bwdScoreList_eq_map {L : ℕ} (w : Fin L → Bool) :
    bwdScoreList w = (List.ofFn w).map bwdStepScore := by
  rw [bwdScoreList, List.map_ofFn]
  rfl

/-- Every nonempty contiguous block of a backward score list has nonzero sum. -/
theorem bwdScoreList_block_ne_zero {L : ℕ} (w : Fin L → Bool) (i n : ℕ)
    (hn : 0 < n) (hin : i + n ≤ L) :
    (((bwdScoreList w).drop i).take n).sum ≠ 0 := by
  let letters := ((List.ofFn w).drop i).take n
  have hlen : letters.length = n := by
    simp only [letters, List.length_take, List.length_drop, List.length_ofFn]
    rw [min_eq_left]
    omega
  have hv := bwdScoreList_sum_ne_zero letters.get (by simpa [hlen] using hn)
  rw [bwdScoreList_eq_map, List.ofFn_get] at hv
  rw [bwdScoreList_eq_map, ← List.map_drop, ← List.map_take]
  simpa only [letters] using hv

/-- Prefix sums of every backward score list are pairwise distinct. -/
theorem bwdScoreList_prefixSums_ne {L : ℕ} (w : Fin L → Bool) :
    ∀ i j : ℕ, i < j → j ≤ (bwdScoreList w).length →
      ((bwdScoreList w).take i).sum ≠ ((bwdScoreList w).take j).sum := by
  apply CollatzMoonshot.prefixSums_ne_of_blocks_ne_zero
  intro i n hn hin
  apply bwdScoreList_block_ne_zero w i n hn
  simpa [bwdScoreList] using hin

/-- A forward-positive word has a cyclic score rotation with every prefix positive. -/
theorem fwdEndpointPositive_iff_exists_goodScoreRotation {L : ℕ} (w : Fin L → Bool) :
    FwdEndpointPositive w ↔
      ∃ r < L, CollatzMoonshot.StrictlyPositivePrefixes ((fwdScoreList w).rotate r) := by
  rw [fwdEndpointPositive_iff_score_pos, ← fwdScoreList_sum_eq_score]
  simpa [fwdScoreList] using
    (CollatzMoonshot.sum_pos_iff_exists_rotate_strictlyPositivePrefixes
      (fwdScoreList w) (fwdScoreList_prefixSums_ne w))

/-- A backward-positive word has a cyclic score rotation with every prefix positive. -/
theorem bwdEndpointPositive_iff_exists_goodScoreRotation {L : ℕ} (w : Fin L → Bool) :
    BwdEndpointPositive w ↔
      ∃ r < L, CollatzMoonshot.StrictlyPositivePrefixes ((bwdScoreList w).rotate r) := by
  rw [bwdEndpointPositive_iff_score_pos, ← bwdScoreList_sum_eq_score]
  simpa [bwdScoreList] using
    (CollatzMoonshot.sum_pos_iff_exists_rotate_strictlyPositivePrefixes
      (bwdScoreList w) (bwdScoreList_prefixSums_ne w))

/-- Rotate a finite word by rotating its list of letters. -/
def rotateWord {L : ℕ} (w : Fin L → Bool) (r : ℕ) : Fin L → Bool :=
  fun i => ((List.ofFn w).rotate r).get (Fin.cast (by simp) i)

theorem ofFn_rotateWord {L : ℕ} (w : Fin L → Bool) (r : ℕ) :
    List.ofFn (rotateWord w r) = (List.ofFn w).rotate r := by
  apply List.ext_get
  · simp
  · intro n h₁ h₂
    simp [rotateWord]

theorem fwdScoreList_rotateWord {L : ℕ} (w : Fin L → Bool) (r : ℕ) :
    fwdScoreList (rotateWord w r) = (fwdScoreList w).rotate r := by
  rw [fwdScoreList_eq_map, ofFn_rotateWord, fwdScoreList_eq_map, List.map_rotate]

theorem bwdScoreList_rotateWord {L : ℕ} (w : Fin L → Bool) (r : ℕ) :
    bwdScoreList (rotateWord w r) = (bwdScoreList w).rotate r := by
  rw [bwdScoreList_eq_map, ofFn_rotateWord, bwdScoreList_eq_map, List.map_rotate]

theorem wordTrueCount_eq_count_true {L : ℕ} (w : Fin L → Bool) :
    wordTrueCount w = (List.ofFn w).count true := by
  induction L with
  | zero => simp [wordTrueCount]
  | succ L ih =>
      rw [← Fin.cons_self_tail w, wordTrueCount_cons, List.ofFn_cons]
      simp only [List.count_cons]
      rw [ih]
      cases w 0 <;> simp [Nat.add_comm]

/-- Cyclic list rotation preserves the marked-letter count. -/
theorem wordTrueCount_rotateWord {L : ℕ} (w : Fin L → Bool) (r : ℕ) :
    wordTrueCount (rotateWord w r) = wordTrueCount w := by
  rw [wordTrueCount_eq_count_true, ofFn_rotateWord, wordTrueCount_eq_count_true]
  exact (List.rotate_perm (List.ofFn w) r).count_eq true

theorem fwdWordWeight_rotateWord {L : ℕ} (w : Fin L → Bool) (r : ℕ) :
    fwdWordWeight (rotateWord w r) = fwdWordWeight w := rfl

/-- Arbitrary cyclic list rotation preserves backward word weight. -/
theorem bwdWordWeight_rotateWord {L : ℕ} (w : Fin L → Bool) (r : ℕ) :
    bwdWordWeight (rotateWord w r) = bwdWordWeight w := by
  unfold bwdWordWeight
  rw [wordTrueCount_rotateWord]

/-- Concrete strict cyclic cover for forward words. -/
theorem fwdEndpointPositive_iff_exists_goodRotation {L : ℕ} (w : Fin L → Bool) :
    FwdEndpointPositive w ↔ ∃ r < L, FwdGood L (rotateWord w r) := by
  rw [fwdEndpointPositive_iff_exists_goodScoreRotation]
  constructor
  · rintro ⟨r, hr, hscore⟩
    refine ⟨r, hr, (fwdGood_iff_strictlyPositivePrefixes _).mpr ?_⟩
    rwa [fwdScoreList_rotateWord]
  · rintro ⟨r, hr, hgood⟩
    refine ⟨r, hr, ?_⟩
    rw [← fwdScoreList_rotateWord]
    exact (fwdGood_iff_strictlyPositivePrefixes _).mp hgood

/-- Concrete strict cyclic cover for backward words. -/
theorem bwdEndpointPositive_iff_exists_goodRotation {L : ℕ} (w : Fin L → Bool) :
    BwdEndpointPositive w ↔ ∃ r < L, BwdGood L (rotateWord w r) := by
  rw [bwdEndpointPositive_iff_exists_goodScoreRotation]
  constructor
  · rintro ⟨r, hr, hscore⟩
    refine ⟨r, hr, (bwdGood_iff_strictlyPositivePrefixes _).mpr ?_⟩
    rwa [bwdScoreList_rotateWord]
  · rintro ⟨r, hr, hgood⟩
    refine ⟨r, hr, ?_⟩
    rw [← bwdScoreList_rotateWord]
    exact (bwdGood_iff_strictlyPositivePrefixes _).mp hgood

/-- Concatenating two forward-positive blocks gives a forward-positive block. -/
theorem FwdEndpointPositive.append {m n : ℕ} {u : Fin m → Bool} {v : Fin n → Bool}
    (hu : FwdEndpointPositive u) (hv : FwdEndpointPositive v) :
    FwdEndpointPositive (Fin.append u v) := by
  unfold FwdEndpointPositive at hu hv ⊢
  rw [wordTrueCount_append]
  calc
    2 ^ (m + n + (wordTrueCount u + wordTrueCount v)) =
        2 ^ (m + wordTrueCount u) * 2 ^ (n + wordTrueCount v) := by
      rw [show m + n + (wordTrueCount u + wordTrueCount v) =
        (m + wordTrueCount u) + (n + wordTrueCount v) by omega, pow_add]
    _ < 3 ^ m * 3 ^ n := Nat.mul_lt_mul_of_lt_of_lt hu hv
    _ = 3 ^ (m + n) := (pow_add 3 m n).symm

/-- Concatenating two backward-positive blocks gives a backward-positive block. -/
theorem BwdEndpointPositive.append {m n : ℕ} {u : Fin m → Bool} {v : Fin n → Bool}
    (hu : BwdEndpointPositive u) (hv : BwdEndpointPositive v) :
    BwdEndpointPositive (Fin.append u v) := by
  unfold BwdEndpointPositive at hu hv ⊢
  rw [wordTrueCount_append]
  calc
    3 ^ (m + n) = 3 ^ m * 3 ^ n := pow_add 3 m n
    _ < 2 ^ (m + wordTrueCount u) * 2 ^ (n + wordTrueCount v) :=
      Nat.mul_lt_mul_of_lt_of_lt hu hv
    _ = 2 ^ ((m + wordTrueCount u) + (n + wordTrueCount v)) :=
      (pow_add 2 (m + wordTrueCount u) (n + wordTrueCount v)).symm
    _ = 2 ^ (m + n + (wordTrueCount u + wordTrueCount v)) := by
      congr 1
      omega

/-- Forward-surviving words are closed under concatenation.  This is the renewal
factorization needed after the first positive cyclic block is cut off. -/
theorem FwdGood.append {m n : ℕ} {u : Fin m → Bool} {v : Fin n → Bool}
    (hm : 0 < m) (hu : FwdGood m u) (hv : FwdGood n v) :
    FwdGood (m + n) (Fin.append u v) := by
  rw [fwdGood_iff_prefix_positive]
  intro t ht0 htL
  by_cases htm : t ≤ m
  · rw [Fin.take_append_left t htm]
    exact (fwdGood_iff_prefix_positive u).mp hu t ht0 htm
  · obtain ⟨s, rfl⟩ : ∃ s, t = m + s := ⟨t - m, by omega⟩
    have hs0 : 0 < s := by omega
    have hsn : s ≤ n := by omega
    rw [Fin.take_append_right s hsn]
    apply FwdEndpointPositive.append
    · simpa using (fwdGood_iff_prefix_positive u).mp hu m hm le_rfl
    · exact (fwdGood_iff_prefix_positive v).mp hv s hs0 hsn

/-- Backward-surviving words are closed under concatenation. -/
theorem BwdGood.append {m n : ℕ} {u : Fin m → Bool} {v : Fin n → Bool}
    (hm : 0 < m) (hu : BwdGood m u) (hv : BwdGood n v) :
    BwdGood (m + n) (Fin.append u v) := by
  rw [bwdGood_iff_prefix_positive]
  intro t ht0 htL
  by_cases htm : t ≤ m
  · rw [Fin.take_append_left t htm]
    exact (bwdGood_iff_prefix_positive u).mp hu t ht0 htm
  · obtain ⟨s, rfl⟩ : ∃ s, t = m + s := ⟨t - m, by omega⟩
    have hs0 : 0 < s := by omega
    have hsn : s ≤ n := by omega
    rw [Fin.take_append_right s hsn]
    apply BwdEndpointPositive.append
    · simpa using (bwdGood_iff_prefix_positive u).mp hu m hm le_rfl
    · exact (bwdGood_iff_prefix_positive v).mp hv s hs0 hsn

/-- The left block of a forward-surviving concatenation survives. -/
theorem FwdGood.of_append_left {m n : ℕ} {u : Fin m → Bool} {v : Fin n → Bool}
    (h : FwdGood (m + n) (Fin.append u v)) : FwdGood m u := by
  rw [fwdGood_iff_prefix_positive]
  intro t ht0 htm
  have htL : t ≤ m + n := by omega
  rw [← Fin.take_append_left t htm u v]
  exact (fwdGood_iff_prefix_positive (Fin.append u v)).mp h t ht0 htL

/-- The left block of a backward-surviving concatenation survives. -/
theorem BwdGood.of_append_left {m n : ℕ} {u : Fin m → Bool} {v : Fin n → Bool}
    (h : BwdGood (m + n) (Fin.append u v)) : BwdGood m u := by
  rw [bwdGood_iff_prefix_positive]
  intro t ht0 htm
  have htL : t ≤ m + n := by omega
  rw [← Fin.take_append_left t htm u v]
  exact (bwdGood_iff_prefix_positive (Fin.append u v)).mp h t ht0 htL

/-- Two forward cyclic starts at the endpoints of positive-length blocks both survive
exactly when the two intervening blocks survive separately.  This is the two-mark
intersection step in the cyclic inclusion--exclusion proof of Sparre--Andersen. -/
theorem fwdGood_append_and_swap_iff {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (u : Fin m → Bool) (v : Fin n → Bool) :
    (FwdGood (m + n) (Fin.append u v) ∧
      FwdGood (n + m) (Fin.append v u)) ↔
      FwdGood m u ∧ FwdGood n v := by
  constructor
  · rintro ⟨huv, hvu⟩
    exact ⟨FwdGood.of_append_left huv, FwdGood.of_append_left hvu⟩
  · rintro ⟨hu, hv⟩
    exact ⟨hu.append hm hv, hv.append hn hu⟩

/-- Backward analogue of `fwdGood_append_and_swap_iff`. -/
theorem bwdGood_append_and_swap_iff {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (u : Fin m → Bool) (v : Fin n → Bool) :
    (BwdGood (m + n) (Fin.append u v) ∧
      BwdGood (n + m) (Fin.append v u)) ↔
      BwdGood m u ∧ BwdGood n v := by
  constructor
  · rintro ⟨huv, hvu⟩
    exact ⟨BwdGood.of_append_left huv, BwdGood.of_append_left hvu⟩
  · rintro ⟨hu, hv⟩
    exact ⟨hu.append hm hv, hv.append hn hu⟩

/-! ## Arbitrarily many cyclic marks

The two-mark equivalences above are the first intersection term in cyclic
inclusion--exclusion.  The following list-level lemma packages the induction needed for every
intersection term: if a survival predicate restricts to an initial block and is preserved by
concatenating a nonempty surviving block, then simultaneous survival from all marked boundaries
is exactly separate survival on every intervening gap. -/

/-- Simultaneous survival from every boundary in a nonempty cyclic list of nonempty blocks is
equivalent to separate survival of all blocks.  This abstract form is the structural core of
all higher cyclic-intersection factorizations. -/
theorem cyclicBlocks_all_iff {α : Type*} (P : List α → Prop)
    (hleft : ∀ a b, P (a ++ b) → P a)
    (happend : ∀ a b, a ≠ [] → P a → P b → P (a ++ b))
    (blocks : List (List α)) (hblocks : blocks ≠ [])
    (hne : ∀ b ∈ blocks, b ≠ []) :
    (∀ r < blocks.length, P (blocks.rotate r).flatten) ↔
      ∀ b ∈ blocks, P b := by
  constructor
  · intro hrot b hb
    obtain ⟨pre, post, rfl⟩ := List.mem_iff_append.mp hb
    have h := hrot pre.length (by simp)
    rw [List.rotate_append_length_eq] at h
    have h' : P (b ++ (post ++ pre).flatten) := by simpa using h
    exact hleft b ((post ++ pre).flatten) h'
  · intro hall r _hr
    have hrot_nonempty : blocks.rotate r ≠ [] := by
      intro hnil
      exact hblocks (List.rotate_eq_nil_iff.mp hnil)
    have hrot_ne : ∀ b ∈ blocks.rotate r, b ≠ [] := by
      intro b hb
      exact hne b (List.mem_rotate.mp hb)
    have hrot_good : ∀ b ∈ blocks.rotate r, P b := by
      intro b hb
      exact hall b (List.mem_rotate.mp hb)
    have aux : ∀ (bs : List (List α)), bs ≠ [] →
        (∀ b ∈ bs, b ≠ []) → (∀ b ∈ bs, P b) → P bs.flatten := by
      intro bs hbs
      induction bs with
      | nil => contradiction
      | cons b bs ih =>
          intro hne' hall'
          cases bs with
          | nil => simpa using hall' b (by simp)
          | cons c cs =>
              rw [List.flatten_cons]
              apply happend b (c :: cs).flatten
              · exact hne' b (by simp)
              · exact hall' b (by simp)
              · apply ih
                · simp
                · intro d hd
                  exact hne' d (by simp [hd])
                · intro d hd
                  exact hall' d (by simp [hd])
    exact aux (blocks.rotate r) hrot_nonempty hrot_ne hrot_good

/-- Strict positivity of every nonempty prefix restricts to an initial block. -/
theorem strictlyPositivePrefixes_of_append_left (a b : List ℝ)
    (h : CollatzMoonshot.StrictlyPositivePrefixes (a ++ b)) :
    CollatzMoonshot.StrictlyPositivePrefixes a := by
  intro t ht0 hta
  have htab : t ≤ (a ++ b).length := by simp; omega
  have hp := h t ht0 htab
  simpa [List.take_append, hta] using hp

/-- Two strict-positive-prefix blocks concatenate to another such block when the first block is
nonempty. -/
theorem strictlyPositivePrefixes_append {a b : List ℝ} (ha0 : a ≠ [])
    (ha : CollatzMoonshot.StrictlyPositivePrefixes a)
    (hb : CollatzMoonshot.StrictlyPositivePrefixes b) :
    CollatzMoonshot.StrictlyPositivePrefixes (a ++ b) := by
  intro t ht0 htab
  by_cases hta : t ≤ a.length
  · have hp := ha t ht0 hta
    rw [List.take_append, Nat.sub_eq_zero_of_le hta]
    simpa using hp
  · have ha_sum : 0 < a.sum := by
      simpa using ha a.length (List.length_pos_of_ne_nil ha0) le_rfl
    have hsub0 : 0 < t - a.length := by omega
    have hsubb : t - a.length ≤ b.length := by
      simp only [List.length_append] at htab
      omega
    have hb_sum := hb (t - a.length) hsub0 hsubb
    rw [List.take_append, List.take_of_length_le (by omega), List.sum_append]
    exact add_pos ha_sum hb_sum

/-- Forward survival for a list word, in its additive-score form. -/
def FwdListGood (l : List Bool) : Prop :=
  CollatzMoonshot.StrictlyPositivePrefixes (l.map fwdStepScore)

/-- Backward survival for a list word, in its additive-score form. -/
def BwdListGood (l : List Bool) : Prop :=
  CollatzMoonshot.StrictlyPositivePrefixes (l.map bwdStepScore)

theorem fwdListGood_iff (l : List Bool) :
    FwdListGood l ↔ FwdGood l.length l.get := by
  simpa [FwdListGood, fwdScoreList_eq_map] using
    (fwdGood_iff_strictlyPositivePrefixes l.get).symm

theorem bwdListGood_iff (l : List Bool) :
    BwdListGood l ↔ BwdGood l.length l.get := by
  simpa [BwdListGood, bwdScoreList_eq_map] using
    (bwdGood_iff_strictlyPositivePrefixes l.get).symm

/-- Arbitrary forward cyclic-mark intersections factor at the proposition level into the
survival predicates of their positive-length gaps. -/
theorem fwdListGood_cyclicBlocks_iff (blocks : List (List Bool))
    (hblocks : blocks ≠ []) (hne : ∀ b ∈ blocks, b ≠ []) :
    (∀ r < blocks.length, FwdListGood (blocks.rotate r).flatten) ↔
      ∀ b ∈ blocks, FwdListGood b := by
  apply cyclicBlocks_all_iff FwdListGood
      (fun a b h => strictlyPositivePrefixes_of_append_left
        (a.map fwdStepScore) (b.map fwdStepScore) (by simpa [FwdListGood] using h))
      (fun a b ha0 ha hb => by
        change CollatzMoonshot.StrictlyPositivePrefixes
          ((a ++ b).map fwdStepScore)
        rw [List.map_append]
        apply strictlyPositivePrefixes_append
        · simpa using ha0
        · simpa [FwdListGood] using ha
        · simpa [FwdListGood] using hb)
      blocks hblocks hne

/-- Backward analogue of `fwdListGood_cyclicBlocks_iff`. -/
theorem bwdListGood_cyclicBlocks_iff (blocks : List (List Bool))
    (hblocks : blocks ≠ []) (hne : ∀ b ∈ blocks, b ≠ []) :
    (∀ r < blocks.length, BwdListGood (blocks.rotate r).flatten) ↔
      ∀ b ∈ blocks, BwdListGood b := by
  apply cyclicBlocks_all_iff BwdListGood
      (fun a b h => strictlyPositivePrefixes_of_append_left
        (a.map bwdStepScore) (b.map bwdStepScore) (by simpa [BwdListGood] using h))
      (fun a b ha0 ha hb => by
        change CollatzMoonshot.StrictlyPositivePrefixes
          ((a ++ b).map bwdStepScore)
        rw [List.map_append]
        apply strictlyPositivePrefixes_append
        · simpa using ha0
        · simpa [BwdListGood] using ha
        · simpa [BwdListGood] using hb)
      blocks hblocks hne

/-- The forward arbitrary-mark factorization in the original `FwdGood` interface. -/
theorem fwdGood_cyclicBlockLists_iff (blocks : List (List Bool))
    (hblocks : blocks ≠ []) (hne : ∀ b ∈ blocks, b ≠ []) :
    (∀ r < blocks.length,
      FwdGood (blocks.rotate r).flatten.length (blocks.rotate r).flatten.get) ↔
      ∀ b ∈ blocks, FwdGood b.length b.get := by
  simpa only [← fwdListGood_iff] using
    fwdListGood_cyclicBlocks_iff blocks hblocks hne

/-- The backward arbitrary-mark factorization in the original `BwdGood` interface. -/
theorem bwdGood_cyclicBlockLists_iff (blocks : List (List Bool))
    (hblocks : blocks ≠ []) (hne : ∀ b ∈ blocks, b ≠ []) :
    (∀ r < blocks.length,
      BwdGood (blocks.rotate r).flatten.length (blocks.rotate r).flatten.get) ↔
      ∀ b ∈ blocks, BwdGood b.length b.get := by
  simpa only [← bwdListGood_iff] using
    bwdListGood_cyclicBlocks_iff blocks hblocks hne

/-- Forward word weights multiply under concatenation. -/
theorem fwdWordWeight_append {m n : ℕ} (u : Fin m → Bool) (v : Fin n → Bool) :
    fwdWordWeight (Fin.append u v) = fwdWordWeight u * fwdWordWeight v := by
  unfold fwdWordWeight
  rw [pow_add]

/-- Backward word weights multiply under concatenation. -/
theorem bwdWordWeight_append {m n : ℕ} (u : Fin m → Bool) (v : Fin n → Bool) :
    bwdWordWeight (Fin.append u v) = bwdWordWeight u * bwdWordWeight v := by
  have hu := wordTrueCount_le u
  have hv := wordTrueCount_le v
  have hsub : m + n - (wordTrueCount u + wordTrueCount v) =
      (m - wordTrueCount u) + (n - wordTrueCount v) := by omega
  unfold bwdWordWeight
  rw [wordTrueCount_append, pow_add, hsub, pow_add]
  ring

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

/-! The same four identities in the named product-weight interface used by the cyclic
decomposition.  Keeping this interface separate leaves the ratified statements above unchanged. -/

theorem fwdPosTerm_eq_weighted_word_sum (k : ℕ) :
    fwdPosTerm k = ∑ w : Fin k → Bool,
      if 2 ^ (k + wordTrueCount w) < 3 ^ k then fwdWordWeight w else 0 := by
  rw [fwdPosTerm_eq_word_sum]
  rfl

theorem bwdPosTerm_eq_weighted_word_sum (k : ℕ) :
    bwdPosTerm k = ∑ w : Fin k → Bool,
      if 3 ^ k < 2 ^ (k + wordTrueCount w) then bwdWordWeight w else 0 := by
  rw [bwdPosTerm_eq_word_sum]
  rfl

theorem fwdSurv_cast_eq_weighted_word_sum (k : ℕ) :
    (fwdSurv k : ℝ) = ∑ w : Fin k → Bool,
      if FwdGood k w then fwdWordWeight w else 0 := by
  rw [fwdSurv_cast_eq_word_sum]
  rfl

theorem bwdSurv_cast_eq_weighted_word_sum (k : ℕ) :
    (bwdSurv k : ℝ) = ∑ w : Fin k → Bool,
      if BwdGood k w then bwdWordWeight w else 0 := by
  rw [bwdSurv_cast_eq_word_sum]
  rfl

/-- The weighted intersection of two forward survival events based at two cyclic marks
factors into the two block-survival masses. -/
theorem fwdTwoMarkIntersection_sum {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (∑ u : Fin m → Bool, ∑ v : Fin n → Bool,
      if FwdGood (m + n) (Fin.append u v) ∧
          FwdGood (n + m) (Fin.append v u) then
        fwdWordWeight (Fin.append u v) else 0) =
      (fwdSurv m : ℝ) * fwdSurv n := by
  rw [fwdSurv_cast_eq_weighted_word_sum, fwdSurv_cast_eq_weighted_word_sum,
    Fintype.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  simp only [fwdGood_append_and_swap_iff hm hn, fwdWordWeight_append]
  split_ifs <;> simp_all

/-- Backward analogue of `fwdTwoMarkIntersection_sum`. -/
theorem bwdTwoMarkIntersection_sum {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (∑ u : Fin m → Bool, ∑ v : Fin n → Bool,
      if BwdGood (m + n) (Fin.append u v) ∧
          BwdGood (n + m) (Fin.append v u) then
        bwdWordWeight (Fin.append u v) else 0) =
      (bwdSurv m : ℝ) * bwdSurv n := by
  rw [bwdSurv_cast_eq_weighted_word_sum, bwdSurv_cast_eq_weighted_word_sum,
    Fintype.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  simp only [bwdGood_append_and_swap_iff hm hn, bwdWordWeight_append]
  split_ifs <;> simp_all

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
