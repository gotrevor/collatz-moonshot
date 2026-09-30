/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Obstructions.MinimalRepairs

namespace CollatzMoonshot.Obstructions.ArithmeticLifts

/-- A two-odd-factor replacement in an arbitrary finite context. -/
def QuadraticMultiStep (s t : Multiset ℤ) : Prop :=
  ∃ (a b c d : ℤ) (r : Multiset ℤ),
    0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
    a % 2 = 1 ∧ b % 2 = 1 ∧ c % 2 = 1 ∧ d % 2 = 1 ∧
    pairRel a b c d ∧ s = {a,b} + r ∧ t = {c,d} + r

abbrev QuadraticMultiReach := Relation.ReflTransGen QuadraticMultiStep

/-! ### Symmetries of `pairRel`

`pairRel a b c d` says `(3(a+b)+1) * c * d = a * b * (3(c+d)+1)`, which is
symmetric in `a ↔ b`, in `c ↔ d`, and under exchanging the two pairs. -/

theorem pairRel_swap_left {a b c d : ℤ} (h : pairRel a b c d) : pairRel b a c d := by
  unfold pairRel at h ⊢; linear_combination h

theorem pairRel_swap_right {a b c d : ℤ} (h : pairRel a b c d) : pairRel a b d c := by
  unfold pairRel at h ⊢; linear_combination h

theorem pairRel_symm {a b c d : ℤ} (h : pairRel a b c d) : pairRel c d a b := by
  unfold pairRel at h ⊢; linear_combination -h

/-- The smaller label of a replacement pair is bounded.  This is the integral
core of the estimate `r_u = 2u/(3u+1) < 2/3`: no upper bound on the partner
label is assumed. -/
private theorem pair_smaller_bound (D A c d M : ℤ)
    (hD : 0 < D) (_hc : 0 < c) (hcd : c ≤ d)
    (h : D * c * d = 3 * A * (c + d) + A)
    (hm : 3 * A ≤ D * M) (hmq : 6 * A * M + A < D * M ^ 2) : c < M := by
  by_contra hn
  have hMc : M ≤ c := by omega
  have hdc : 0 ≤ d - c := by omega
  have hfac : 0 ≤ D * c - 3 * A := by nlinarith
  have hprod := mul_nonneg hdc hfac
  have hdiff : 0 ≤ c - M := by omega
  have hfac2 : 0 ≤ D * c + D * M - 6 * A := by nlinarith
  have hprod2 := mul_nonneg hdiff hfac2
  nlinarith

/-- For a small positive odd label `a`, the smaller new label is `< 2a+1`. -/
theorem pair_small_head_bound {a b c d : ℤ} (hapos : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hcd : c ≤ d) (h : pairRel a b c d) : c < 2 * a + 1 := by
  have heq : (3 * (a + b) + 1) * c * d = 3 * (a * b) * (c + d) + a * b := by
    unfold pairRel at h; linear_combination h
  exact pair_smaller_bound (3 * (a + b) + 1) (a * b) c d (2 * a + 1)
    (by nlinarith) hc hcd heq (by nlinarith) (by nlinarith)

/-- Fixing the first label pins the partner. -/
theorem pair_same_head {a b d : ℤ} (hapos : 0 < a) (h : pairRel a b a d) : d = b := by
  have h2 : a * ((3 * a + 1) * (d - b)) = 0 := by unfold pairRel at h; linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · omega
  · rcases mul_eq_zero.mp h3 with h4 | h4 <;> omega

/-- **Arithmetic core.**  If the first label of a quadratic replacement is one of
the three small generators `1, 3, 5`, the sorted replacement pair is the original
pair.  Quantified over all positive odd partners: no search height is assumed. -/
theorem pair_small_core (a b c d : ℤ) (ha : a = 1 ∨ a = 3 ∨ a = 5)
    (hb : 0 < b) (hbo : b % 2 = 1) (hc : 0 < c) (hcd : c ≤ d)
    (hco : c % 2 = 1) (hdo : d % 2 = 1) (h : pairRel a b c d) :
    (c = a ∧ d = b) ∨ (c = b ∧ d = a) := by
  have hapos : 0 < a := by rcases ha with rfl | rfl | rfl <;> norm_num
  have hd : 0 < d := lt_of_lt_of_le hc hcd
  have hcb : c < 2 * a + 1 := pair_small_head_bound hapos hb hc hcd h
  -- the pairRel equation, arranged as a bilinear relation in `b` and `d`
  have key : 3 * (a - c) * b * d + a * (3 * c + 1) * b = c * (3 * a + 1) * d := by
    unfold pairRel at h; linear_combination -h
  by_cases hca : c = a
  · subst hca
    exact Or.inl ⟨rfl, pair_same_head hapos h⟩
  · rcases lt_or_gt_of_ne hca with hlt | hgt
    · -- `c < a`: the partner `b` is bounded
      have hpos : 0 < a * (3 * c + 1) * b := by positivity
      have hmul : (3 * (a - c) * b) * d < (c * (3 * a + 1)) * d := by nlinarith [key, hpos]
      have hbound : 3 * (a - c) * b < c * (3 * a + 1) :=
        lt_of_mul_lt_mul_right hmul hd.le
      rcases ha with rfl | rfl | rfl <;> interval_cases c <;>
        (have hbb : b < 8 := by omega) <;> interval_cases b <;> omega
    · -- `a < c`: the new larger label `d` is bounded
      have hpos : 0 < c * (3 * a + 1) * d := by positivity
      have hmul : (3 * (c - a) * d) * b < (a * (3 * c + 1)) * b := by nlinarith [key, hpos]
      have hbound : 3 * (c - a) * d < a * (3 * c + 1) :=
        lt_of_mul_lt_mul_right hmul hb.le
      rcases ha with rfl | rfl | rfl <;> interval_cases c <;>
        (have hdb : d < 19 := by omega) <;> interval_cases d <;> omega

/-- With a small generator in the first slot, the replacement multiset is the
original multiset. -/
theorem pair_small_eq {a b c d : ℤ} (ha : a = 1 ∨ a = 3 ∨ a = 5)
    (hb : 0 < b) (hbo : b % 2 = 1) (hc : 0 < c) (hd : 0 < d)
    (hco : c % 2 = 1) (hdo : d % 2 = 1) (h : pairRel a b c d) :
    ({a, b} : Multiset ℤ) = {c, d} := by
  rcases le_total c d with hcd | hcd
  · rcases pair_small_core a b c d ha hb hbo hc hcd hco hdo h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2]; exact Multiset.pair_comm a b
  · rcases pair_small_core a b d c ha hb hbo hd hcd hdo hco (pairRel_swap_right h)
      with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact Multiset.pair_comm a b
    · rw [h1, h2]

/-- Whenever a small generator appears among the four labels of a quadratic
replacement, the replacement is trivial on the pair. -/
theorem step_pair_eq {a b c d : ℤ} (hapos : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hao : a % 2 = 1) (hbo : b % 2 = 1) (hco : c % 2 = 1) (hdo : d % 2 = 1)
    (h : pairRel a b c d) {x : ℤ} (hx : x = 1 ∨ x = 3 ∨ x = 5)
    (hmem : x = a ∨ x = b ∨ x = c ∨ x = d) :
    ({a, b} : Multiset ℤ) = {c, d} := by
  rcases hmem with rfl | rfl | rfl | rfl
  · exact pair_small_eq hx hb hbo hc hd hco hdo h
  · rw [Multiset.pair_comm]
    exact pair_small_eq hx hapos hao hc hd hco hdo (pairRel_swap_left h)
  · exact (pair_small_eq hx hd hdo hapos hb hao hbo (pairRel_symm h)).symm
  · have hpc := pair_small_eq hx hc hco hapos hb hao hbo
      (pairRel_swap_left (pairRel_symm h))
    rw [← hpc]; exact Multiset.pair_comm _ _

theorem count_pair_eq {a b c d x : ℤ} (hapos : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hao : a % 2 = 1) (hbo : b % 2 = 1) (hco : c % 2 = 1) (hdo : d % 2 = 1)
    (h : pairRel a b c d) (hx : x = 1 ∨ x = 3 ∨ x = 5) :
    ({a, b} : Multiset ℤ).count x = ({c, d} : Multiset ℤ).count x := by
  by_cases hmem : x = a ∨ x = b ∨ x = c ∨ x = d
  · rw [step_pair_eq hapos hb hc hd hao hbo hco hdo h hx hmem]
  · have h1 : x ∉ ({a, b} : Multiset ℤ) := by simp; tauto
    have h2 : x ∉ ({c, d} : Multiset ℤ) := by simp; tauto
    rw [Multiset.count_eq_zero_of_notMem h1, Multiset.count_eq_zero_of_notMem h2]

/-- The small generators are frozen under arbitrary quadratic replacements. -/
theorem small_generator_count_invariant (a : ℤ) (ha : a = 1 ∨ a = 3 ∨ a = 5)
    {s t : Multiset ℤ} (h : QuadraticMultiReach s t) : s.count a = t.count a := by
  induction h with
  | refl => rfl
  | tail hst hstep ih =>
      obtain ⟨p, q, u, v, r, hp, hq, hu, hv, hpo, hqo, huo, hvo, hrel, hs, ht⟩ := hstep
      rw [ih, hs, ht, Multiset.count_add, Multiset.count_add,
        count_pair_eq hp hq hu hv hpo hqo huo hvo hrel ha]

/-- Unlike the earlier cubic example, this identity has no quadratic
implementation even after adjoining any finite multiset of catalysts. -/
theorem no_catalyst_for_five_exchange (catalyst : Multiset ℤ) :
    ¬ QuadraticMultiReach ({5,55,83} + catalyst) ({11,13,17} + catalyst) := by
  intro h
  have hcount := small_generator_count_invariant 5 (by norm_num) h
  rw [Multiset.count_add, Multiset.count_add] at hcount
  have h1 : ({5,55,83} : Multiset ℤ).count 5 = 1 := by decide
  have h2 : ({11,13,17} : Multiset ℤ).count 5 = 0 := by decide
  omega

theorem five_exchange_value :
    certificateValue 0 [5,55,83] = certificateValue 0 [11,13,17] ∧
    certificateValue 0 [5,55,83] = (11 : ℚ)/40 := by native_decide

end CollatzMoonshot.Obstructions.ArithmeticLifts
