/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalOddRewire

/-!
# Finite-depth fusion (meta-theorem M1, research §55)

An argument that reads each point `n` of `U` only to a finite depth `D(n)`, and tolerates a sparse
set of exceptions, cannot decide whether `U` has infinitely many infinite orbits.

`exists_depthFusion`: for any depth function `D` and any budget `G` with `G(X)/D*(X) → ∞`
(`D*(X) = max_{n < X} D(n)`), there is a permutation `τ` of `ℕ` that keeps `U`'s even branch and
every finite orbit of `U`, fuses all infinite orbits of `U` into one, and agrees with `U` to depth
`D(n)` at every `n < X` outside a set of at most `G(X)` points, for all large `X`.  Theorem TT
(`tail_threshold`) is the infinite-depth version.

Proof idea: take the odd rewire `exists_oddRewire` with a change budget `F` small enough that the
changes below `B(X)` (the largest value on a depth-`D*(X)` segment from `n < X`) number at most
`G(X)/(2D*(X) + 1)`.  A disagreement at depth `d` at `n` needs a change of `τ` at some point of
`U`'s segment `U^i n`, `|i| ≤ d` (backward disagreements too: `τ⁻¹ y ≠ U⁻¹ y` makes `U⁻¹ y` a
change of `τ`), and each change point lies on at most `2D*(X) + 1` such segments.
-/

namespace CollatzMoonshot.Amusical

/-- `τ` and `U` disagree at depth `d` at `n`: `τ^j n ≠ U^j n` for some `|j| ≤ d`. -/
def DisagreeAtDepth (τ : Equiv.Perm ℕ) (d n : ℕ) : Prop :=
  ∃ j : ℤ, |j| ≤ d ∧ (τ ^ j) n ≠ (amusicalNatPerm ^ j) n

/-- The largest depth `max_{n < X} D(n)`. -/
def maxDepth (D : ℕ → ℕ) (X : ℕ) : ℕ :=
  (Finset.range X).sup D

open Finset

/-- If `τ` agrees with `σ` at every point `σ^i n`, `|i| ≤ d`, then `τ^j n = σ^j n` for `|j| ≤ d`. -/
theorem zpow_apply_eq_of_agree {α : Type*} (σ τ : Equiv.Perm α) (d : ℕ) (n : α)
    (H : ∀ i : ℤ, |i| ≤ d → τ ((σ ^ i) n) = σ ((σ ^ i) n)) (j : ℤ) (hj : |j| ≤ d) :
    (τ ^ j) n = (σ ^ j) n := by
  have hf : ∀ k : ℕ, k ≤ d → (τ ^ k) n = (σ ^ k) n := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      have h := H k (by rw [Nat.abs_cast]; omega)
      rw [zpow_natCast] at h
      rw [pow_succ', Equiv.Perm.mul_apply, ih (by omega), h, pow_succ', Equiv.Perm.mul_apply]
  have hb : ∀ k : ℕ, k ≤ d → ((τ ^ k)⁻¹) n = ((σ ^ k)⁻¹) n := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      have h := H (-((k + 1 : ℕ) : ℤ)) (by rw [abs_neg, Nat.abs_cast]; omega)
      rw [zpow_neg, zpow_natCast] at h
      rw [pow_succ, mul_inv_rev, Equiv.Perm.mul_apply, ih (by omega), Equiv.Perm.inv_eq_iff_eq, h,
        pow_succ, mul_inv_rev, Equiv.Perm.mul_apply]
      simp
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg j
  · rw [zpow_natCast, zpow_natCast]
    exact hf k (by rw [Nat.abs_cast] at hj; omega)
  · rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
    exact hb k (by rw [abs_neg, Nat.abs_cast] at hj; omega)

/-- A disagreement at depth `d` at `n` needs a change of `τ` on `σ`'s segment `σ^i n`, `|i| ≤ d`. -/
theorem exists_change_of_disagree {α : Type*} (σ τ : Equiv.Perm α) (d : ℕ) (n : α) (j : ℤ)
    (hj : |j| ≤ d) (h : (τ ^ j) n ≠ (σ ^ j) n) :
    ∃ i : ℤ, |i| ≤ d ∧ τ ((σ ^ i) n) ≠ σ ((σ ^ i) n) := by
  by_contra hc
  push Not at hc
  exact h (zpow_apply_eq_of_agree σ τ d n hc j hj)

/-- The largest value `U^i n` over `n < X` and `|i| ≤ D*(X)`. -/
noncomputable def segTop (D : ℕ → ℕ) (X : ℕ) : ℕ :=
  (range X ×ˢ Icc (-(maxDepth D X : ℤ)) (maxDepth D X)).sup fun p =>
    (amusicalNatPerm ^ p.2) p.1

theorem le_segTop (D : ℕ → ℕ) (X : ℕ) : X ≤ segTop D X + 1 := by
  rcases Nat.eq_zero_or_pos X with rfl | hX
  · omega
  unfold segTop
  have h := Finset.le_sup (f := fun p : ℕ × ℤ => (amusicalNatPerm ^ p.2) p.1)
    (s := range X ×ˢ Icc (-(maxDepth D X : ℤ)) (maxDepth D X)) (b := (X - 1, 0))
    (by simp; omega)
  simp only [zpow_zero, Equiv.Perm.one_apply] at h
  omega

open Classical in
/-- **Counting.**  Each change point below `segTop + 1` accounts for at most `2D*(X) + 1`
disagreements at points `n < X`. -/
theorem card_disagree_le (τ : Equiv.Perm ℕ) (D : ℕ → ℕ) (X : ℕ) :
    ((range X).filter fun n => DisagreeAtDepth τ (D n) n).card ≤
      (2 * maxDepth D X + 1) *
        ((range (segTop D X + 1)).filter fun c => τ c ≠ amusicalNatPerm c).card := by
  set σ := amusicalNatPerm
  set M := maxDepth D X
  set ch := (range (segTop D X + 1)).filter fun c => τ c ≠ σ c
  have hsub : ((range X).filter fun n => DisagreeAtDepth τ (D n) n) ⊆
      (Icc (-(M : ℤ)) M).biUnion fun i => ch.image fun c => (σ ^ (-i)) c := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnX, j, hj, hne⟩ := hn
    obtain ⟨i, hi, hc⟩ := exists_change_of_disagree σ τ (D n) n j hj hne
    have hDM : D n ≤ M := Finset.le_sup (f := D) (Finset.mem_range.2 hnX)
    have hiM : |i| ≤ M := hi.trans (by exact_mod_cast hDM)
    have hiI : i ∈ Icc (-(M : ℤ)) M := Finset.mem_Icc.2 (abs_le.1 hiM)
    rw [Finset.mem_biUnion]
    refine ⟨i, hiI, Finset.mem_image.2 ⟨(σ ^ i) n, ?_, ?_⟩⟩
    · refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le ?_), hc⟩
      exact Finset.le_sup (f := fun p : ℕ × ℤ => (σ ^ p.2) p.1) (b := (n, i))
        (s := range X ×ˢ Icc (-(M : ℤ)) M) (Finset.mem_product.2 ⟨Finset.mem_range.2 hnX, hiI⟩)
    · rw [← Equiv.Perm.mul_apply, ← zpow_add, neg_add_cancel, zpow_zero, Equiv.Perm.one_apply]
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ i ∈ Icc (-(M : ℤ)) M, (ch.image fun c => (σ ^ (-i)) c).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ Icc (-(M : ℤ)) M, ch.card := Finset.sum_le_sum fun _ _ => Finset.card_image_le
    _ = (2 * M + 1) * ch.card := by
      rw [Finset.sum_const, Int.card_Icc, smul_eq_mul]
      congr 1
      omega

open Classical in
/-- **M1, finite-depth fusion.**  If `G(X)/(D*(X) + 1) → ∞`, some permutation of `ℕ` with
`U`'s even branch and finite orbits, and a single infinite orbit through all infinite orbits of
`U`, agrees with `U` to depth `D(n)` at all but at most `G(X)` points `n < X`, for all large `X`. -/
theorem exists_depthFusion (D G : ℕ → ℕ)
    (hG : ∀ C : ℕ, ∀ᶠ X in Filter.atTop, C * (maxDepth D X + 1) ≤ G X) :
    ∃ τ : Equiv.Perm ℕ,
      (∀ m : ℕ, τ (2 * m) = 3 * m) ∧
      (∀ n : ℕ, (amusicalOrbit n).Finite → (τ n : ℤ) = amusical n) ∧
      (∀ a b : ℕ, (amusicalOrbit a).Infinite → (amusicalOrbit b).Infinite →
        ∃ j : ℤ, (τ ^ j) a = b) ∧
      ∀ᶠ X in Filter.atTop,
        ((Finset.range X).filter fun n => DisagreeAtDepth τ (D n) n).card ≤ G X := by
  set q : ℕ → ℕ := fun X => G X / (2 * maxDepth D X + 1)
  set B : ℕ → ℕ := fun X => segTop D X + 1
  set F : ℕ → ℕ := fun N => sInf (q '' {X | N ≤ B X})
  have hFle (X : ℕ) : F (B X) ≤ q X := Nat.sInf_le ⟨X, show B X ≤ B X from le_rfl, rfl⟩
  have hqtop (k : ℕ) : ∀ᶠ X in Filter.atTop, k ≤ q X := by
    filter_upwards [hG (2 * k)] with X hX
    have : k * (2 * maxDepth D X + 1) ≤ 2 * k * (maxDepth D X + 1) := by nlinarith
    exact (Nat.le_div_iff_mul_le (by omega)).2 (this.trans hX)
  have hF : Filter.Tendsto F Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro k
    obtain ⟨X₁, hX₁⟩ := Filter.eventually_atTop.1 (hqtop k)
    rw [Filter.eventually_atTop]
    refine ⟨(range X₁).sup B + 1, fun N hN => ?_⟩
    apply le_csInf (Set.Nonempty.image q ⟨N, show N ≤ B N from le_segTop D N⟩)
    rintro _ ⟨X, hX, rfl⟩
    apply hX₁
    by_contra hlt
    push Not at hlt
    have := Finset.le_sup (f := B) (Finset.mem_range.2 hlt)
    change N ≤ B X at hX
    omega
  obtain ⟨τ, h1, h2, h3, h4⟩ := exists_oddRewire F hF
  refine ⟨τ, h1, h2, h4, Filter.Eventually.of_forall fun X => ?_⟩
  calc _ ≤ _ := card_disagree_le τ D X
    _ ≤ (2 * maxDepth D X + 1) * F (B X) := by
      apply Nat.mul_le_mul_left
      refine le_trans (Finset.card_le_card fun c hc => ?_) (h3 (B X))
      simp only [Finset.mem_filter] at hc ⊢
      exact ⟨hc.1, fun h => hc.2 (Nat.cast_injective (by rw [h, amusicalNatPerm_apply_cast]))⟩
    _ ≤ (2 * maxDepth D X + 1) * q X := Nat.mul_le_mul_left _ (hFle X)
    _ ≤ G X := Nat.mul_div_le (G X) _

end CollatzMoonshot.Amusical
