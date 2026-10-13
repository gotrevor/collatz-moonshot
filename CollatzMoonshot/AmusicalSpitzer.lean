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
