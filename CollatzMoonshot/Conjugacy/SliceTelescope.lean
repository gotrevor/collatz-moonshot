/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.Bridge3
import CollatzMoonshot.Conjugacy.SliceFourier

/-!
# SEC6S lap 1: the slice mixture identity (`SEC6S-PLAN.md` §2(a))

Reducing the slice law `(j, a)` modulo `3^{a'}` (`a' < a`) is a binomially weighted mixture of
the slice laws `(t − 1, a')`, `1 ≤ t ≤ j`:

    levelClass j a a' c = Σ_{t=1}^{j} C(j − t, a − a' − 1) · levelMass (t − 1) a' c.

Why: for `r < 2^j` with trace word `w` (`a` ones), `2^j · T^j r = 3^a · r + numer w`
(`tstep_iterate_identity`), and `numer (u ++ v) = 3^{ones v} · numer u + 2^{|u|} · numer v`
(induction on `v` from `numer_append_true` / `numer_append_false`).  Split `w = u ++ v` with `u`
the prefix through the `(a − a')`-th one (position `s`) and `v` the suffix (length
`t − 1 = j − s`, `a'` ones).  Then `3^a r + 3^{a'} numer u ≡ 0`, so
`T^j r ≡ 2^{−(t−1)} · numer v ≡ T^{t−1} r' (mod 3^{a'})`, where `r' < 2^{t−1}` is the start with
trace word `v`; and `T^{t−1} r' < 3^{a'}` (`tstep_iterate_lt_three_pow`), so the residue is the
value.  The prefix `u` (ending in a one, `a − a'` ones in all) has `C(s − 1, a − a' − 1)`
`= C(j − t, a − a' − 1)` choices.  Exact check: `experiments/conjugacy/mixture.py` (455 triples,
`j ≤ 13`, 0 mismatches; the off-by-one control fails 449/455).
-/

namespace CollatzMoonshot.Conjugacy

open Finset CollatzMoonshot.FrontB

/-! ## The Pascal recursion for class counts

Proof route: peel the FIRST step (kickoff route 4) rather than splitting trace words.  An even start
`2s` keeps the slice; an odd start `2s + 1` goes to `3s + 2`, whose residue `x` mod `2^j` runs over
`range (2^j)` bijectively (`affineThreeNat_injective/surjective`), and
`T^j (3s + 2) = T^j x + q · 3^{oddCount x j}` vanishes mod `3^m` in the `q` term once `m ≤ a`. -/

theorem levelClass_eq_sum_ite (j a m c : ℕ) :
    levelClass j a m c = ∑ s ∈ Finset.range (2 ^ j),
      if oddCount s j = a ∧ tstep^[j] s % 3 ^ m = c then 1 else 0 := by
  unfold levelClass levelSet
  rw [Finset.filter_filter, Finset.card_filter]

/-- **Pascal recursion for class counts.**  For `m ≤ a`, the class count of the slice
`(j + 1, a + 1)` mod `3^m` is the even-start part `(j, a + 1)` plus the odd-start part `(j, a)`. -/
theorem levelClass_succ_pascal (j a m c : ℕ) (hm : m ≤ a) :
    levelClass (j + 1) (a + 1) m c = levelClass j (a + 1) m c + levelClass j a m c := by
  rw [levelClass_eq_sum_ite, pow_succ, mul_comm, sum_range_two_mul, Finset.sum_add_distrib,
    levelClass_eq_sum_ite, levelClass_eq_sum_ite]
  congr 1
  · apply Finset.sum_congr rfl
    intro s _
    rw [oddCount_two_mul_succ, Function.iterate_succ_apply, tstep_two_mul]
  · apply Finset.sum_nbij (fun s => (3 * s + 2) % 2 ^ j)
    · intro s _
      exact Finset.mem_range.mpr (Nat.mod_lt _ (by positivity))
    · exact affineThreeNat_injective j
    · exact affineThreeNat_surjective j
    · intro s _
      rw [oddCount_two_mul_add_one_succ, Function.iterate_succ_apply, tstep_two_mul_add_one,
        oddCount_affineThree_mod j s]
      by_cases ha : oddCount ((3 * s + 2) % 2 ^ j) j = a
      · have hmod : tstep^[j] (3 * s + 2) % 3 ^ m = tstep^[j] ((3 * s + 2) % 2 ^ j) % 3 ^ m := by
          rw [tstep_iterate_affineThree_mod, ha]
          obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
          rw [pow_add, ← mul_assoc, mul_comm _ (3 ^ m), mul_assoc, Nat.add_mul_mod_self_left]
        simp only [ha, hmod, true_and]
      · have ha' : ¬ oddCount ((3 * s + 2) % 2 ^ j) j + 1 = a + 1 := by omega
        simp only [ha, ha', false_and, if_false]

/-- At `m = a` the class count is the mass: `T^j r < 3^a` on the slice, so the residue is the
value. -/
theorem levelClass_self (j a c : ℕ) : levelClass j a a c = levelMass j a c := by
  unfold levelClass levelMass
  congr 1
  apply Finset.filter_congr
  intro r hr
  have hr' := Finset.mem_filter.mp hr
  have hlt : tstep^[j] r < 3 ^ a := by
    rw [← hr'.2]; exact tstep_iterate_lt_three_pow (Finset.mem_range.mp hr'.1)
  rw [Nat.mod_eq_of_lt hlt]

theorem levelClass_zero_succ (a m c : ℕ) : levelClass 0 (a + 1) m c = 0 := by
  rw [levelClass_eq_sum_ite]
  simp [oddCount_zero]

theorem levelClass_add_succ_eq_sum (a' c : ℕ) : ∀ j k : ℕ,
    levelClass j (a' + k + 1) a' c =
      ∑ t ∈ Finset.Icc 1 j, (j - t).choose k * levelMass (t - 1) a' c := by
  intro j
  induction j with
  | zero => intro k; simp [levelClass_zero_succ]
  | succ j ih =>
    intro k
    rw [Finset.sum_Icc_succ_top (by omega), Nat.sub_self]
    cases k with
    | zero =>
      rw [levelClass_succ_pascal j (a' + 0) a' c (by omega), ih 0, Nat.add_zero, levelClass_self]
      simp only [Nat.choose_zero_right, Nat.add_sub_cancel, one_mul]
    | succ k =>
      have e : a' + (k + 1) + 1 = (a' + k + 1) + 1 := by ring
      rw [e, levelClass_succ_pascal j (a' + k + 1) a' c (by omega),
        show a' + k + 1 + 1 = a' + (k + 1) + 1 by ring, ih (k + 1), ih k,
        Nat.choose_zero_succ, zero_mul, add_zero, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t ht
      have ht' := Finset.mem_Icc.mp ht
      rw [show j + 1 - t = (j - t) + 1 by omega, Nat.choose_succ_succ, add_mul, add_comm]

/-- **Frozen.**  The slice mixture identity (SEC6S §2(a)): the class count of the slice `(j, a)`
modulo `3^{a'}` is the binomially weighted sum of the slice masses `(t − 1, a')`, `1 ≤ t ≤ j`. -/
theorem levelClass_eq_sum_levelMass (j a a' c : ℕ) (h : a' < a) :
    levelClass j a a' c =
      ∑ t ∈ Finset.Icc 1 j, (j - t).choose (a - a' - 1) * levelMass (t - 1) a' c := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h
  rw [show a' + k + 1 - a' - 1 = k by omega]
  exact levelClass_add_succ_eq_sum a' c j k

example : levelClass 5 3 1 1 =
    ∑ t ∈ Finset.Icc 1 5, (5 - t).choose 1 * levelMass (t - 1) 1 1 := by decide

end CollatzMoonshot.Conjugacy
