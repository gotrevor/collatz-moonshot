/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Conjugacy.BeyondWordsLinearSharp
import CollatzMoonshot.FrontA.OrbitPacking

/-!
# Beyond-Terras uniformity on every aligned window `[q·2^j, (q+1)·2^j)`

`beyondTV j K` measures the first window `[0, 2^j)`.  For any aligned window the iterate identity
(`tstep_iterate_identity`, `traceWord_add_mul`) gives `T^j (r + q 2^j) = T^j r + 3^a q` on
`levelSet j a`, so per slice the residues mod `2^K` are the first window's residues shifted by a
slice constant; every per-slice residue-sum bound is shift-invariant (reindex `c`), and both
growing-depth theorems hold verbatim for every aligned window.  Ensemble statements over the
window's starts; nothing about any individual orbit.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB

/-- The beyond-Terras residue count on the aligned window `[A, A + 2^j)`. -/
def beyondCountAt (A j K c : ℕ) : ℕ :=
  ((Finset.Ico A (A + 2 ^ j)).filter (fun r => tstep^[j] r % 2 ^ K = c)).card

/-- Total-variation distance to uniform on `ℤ/2^K` of the beyond-Terras residues of the aligned
window `[A, A + 2^j)`. -/
noncomputable def beyondTVAt (A j K : ℕ) : ℝ :=
  ∑ c ∈ Finset.range (2 ^ K), |(beyondCountAt A j K c : ℝ) / 2 ^ j - 1 / 2 ^ K|

/-! ## The shift identity and shift invariance of residue sums -/

/-- **Shift identity.**  Adding `q · 2^j` to a start adds `3^a q` to its `j`-th iterate, where
`a = oddCount r j`: both starts share the length-`j` parity trace (`traceWord_add_mul`), so the
iterate identity (`tstep_iterate_identity`) differs only in the linear term. -/
theorem tstep_iterate_add_mul (j r q : ℕ) :
    tstep^[j] (r + q * 2 ^ j) = tstep^[j] r + 3 ^ oddCount r j * q := by
  have h1 := tstep_iterate_identity j (r + q * 2 ^ j)
  have h2 := tstep_iterate_identity j r
  rw [CollatzMoonshot.FrontA.OrbitPacking.traceWord_add_mul] at h1
  have hpos : 0 < 2 ^ j := by positivity
  apply Nat.eq_of_mul_eq_mul_left hpos
  unfold oddCount
  rw [mul_add, h2]
  rw [h1]
  ring

/-- For `c < N`, `y % N = c` iff `y = c` in `ZMod N`. -/
theorem mod_eq_iff_zmod {N y c : ℕ} (hc : c < N) : y % N = c ↔ (y : ZMod N) = c := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hc]

/-- **Shift invariance.**  Shifting every point of a family by the same `s` permutes the
residues mod `2^K`, so the total of the residue-sum norms over `c < 2^K` is unchanged. -/
theorem sum_norm_sum_resInd_add (K : ℕ) {ι : Type*} (S : Finset ι) (y : ι → ℕ) (s : ℕ) :
    ∑ c ∈ Finset.range (2 ^ K), ‖∑ r ∈ S, resInd K c (y r + s)‖ =
      ∑ c ∈ Finset.range (2 ^ K), ‖∑ r ∈ S, resInd K c (y r)‖ := by
  have : NeZero (2 ^ K) := ⟨by positivity⟩
  refine Finset.sum_nbij' (fun c => (((c : ℕ) : ZMod (2 ^ K)) - s).val)
    (fun c => (((c : ℕ) : ZMod (2 ^ K)) + s).val) ?_ ?_ ?_ ?_ ?_
  · intro c _
    exact Finset.mem_range.2 (ZMod.val_lt _)
  · intro c _
    exact Finset.mem_range.2 (ZMod.val_lt _)
  · intro c hc
    have hc' := Finset.mem_range.1 hc
    simp only [ZMod.natCast_val, ZMod.cast_id', id, sub_add_cancel, ZMod.val_natCast,
      Nat.mod_eq_of_lt hc']
  · intro c hc
    have hc' := Finset.mem_range.1 hc
    simp only [ZMod.natCast_val, ZMod.cast_id', id, add_sub_cancel_right, ZMod.val_natCast,
      Nat.mod_eq_of_lt hc']
  · intro c hc
    have hc' := Finset.mem_range.1 hc
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    unfold resInd
    congr 2
    apply propext
    rw [mod_eq_iff_zmod hc', mod_eq_iff_zmod (ZMod.val_lt _), ZMod.natCast_val, ZMod.cast_id',
      id, Nat.cast_add, eq_sub_iff_add_eq]

/-- Teeth: the window at `A = 0` is the original statistic. -/
theorem beyondTVAt_zero (j K : ℕ) : beyondTVAt 0 j K = beyondTV j K := by
  unfold beyondTVAt beyondTV beyondCountAt beyondCount
  rw [zero_add, ← Finset.range_eq_Ico]

/-! ## Total variation on an aligned window from the slices of a band -/

/-- The window's centred residue sum, read on offsets `r < 2^j`, is the centred window count. -/
theorem sum_resInd_window_eq (A j K c : ℕ) :
    ∑ r ∈ Finset.range (2 ^ j), resInd K c (tstep^[j] (A + r)) =
      (beyondCountAt A j K c : ℂ) - 2 ^ j * ((2 : ℂ) ^ K)⁻¹ := by
  have h := Finset.sum_Ico_eq_sum_range (fun r => resInd K c (tstep^[j] r)) A (A + 2 ^ j)
  rw [Nat.add_sub_cancel_left] at h
  rw [← h]
  unfold resInd beyondCountAt
  rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_const, Nat.card_Ico,
    Nat.add_sub_cancel_left, nsmul_eq_mul]
  push_cast
  ring

/-- On the window `[q 2^j, (q+1) 2^j)` the slice `a` contributes the first window's slice shifted
by `3^a q` (`tstep_iterate_add_mul`). -/
theorem sum_resInd_window_eq_sum_levelSet (q j K c : ℕ) :
    ∑ r ∈ Finset.range (2 ^ j), resInd K c (tstep^[j] (q * 2 ^ j + r)) =
      ∑ a ∈ Finset.range (j + 1), ∑ r ∈ levelSet j a, resInd K c (tstep^[j] r + 3 ^ a * q) := by
  rw [sum_range_eq_sum_levelSet j (fun r => resInd K c (tstep^[j] (q * 2 ^ j + r)))]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro r hr
  have hra : oddCount r j = a := (Finset.mem_filter.1 hr).2
  rw [add_comm (q * 2 ^ j) r, tstep_iterate_add_mul, hra]

/-- **Total variation on an aligned window from the slices of a band.**  The hypothesis is the
first window's per-slice bound, verbatim; shift invariance (`sum_norm_sum_resInd_add`) carries it
to every aligned window, and the off-band starts are charged as in `beyondTV_le_of_band`. -/
theorem beyondTVAt_le_of_band (q j K : ℕ) (P : ℕ → Prop) [DecidablePred P] {M : ℝ}
    (hM : 0 ≤ M)
    (hslice : ∀ a, P a →
      ∑ c ∈ Finset.range (2 ^ K), ‖∑ r ∈ levelSet j a, resInd K c (tstep^[j] r)‖ ≤
        M * (levelSet j a).card) :
    beyondTVAt (q * 2 ^ j) j K ≤
      M + 2 * (((Finset.range (2 ^ j)).filter (fun r => ¬ P (oddCount r j))).card : ℝ) /
        2 ^ j := by
  set E := ((Finset.range (2 ^ j)).filter (fun r => ¬ P (oddCount r j))).card with hE
  let I := Finset.range (j + 1)
  let L := I.filter P
  let H := I.filter (fun a => ¬ P a)
  let S : ℕ → ℕ → ℂ := fun c a => ∑ r ∈ levelSet j a, resInd K c (tstep^[j] r + 3 ^ a * q)
  have hpowpos : (0 : ℝ) < 2 ^ j := by positivity
  have hterm (c : ℕ) : |(beyondCountAt (q * 2 ^ j) j K c : ℝ) / 2 ^ j - 1 / 2 ^ K| =
      ‖∑ r ∈ Finset.range (2 ^ j), resInd K c (tstep^[j] (q * 2 ^ j + r))‖ / 2 ^ j := by
    rw [sum_resInd_window_eq]
    have hr := Complex.norm_real
      ((beyondCountAt (q * 2 ^ j) j K c : ℝ) - 2 ^ j * ((2 : ℝ) ^ K)⁻¹)
    push_cast at hr
    rw [hr, Real.norm_eq_abs]
    have heq : (beyondCountAt (q * 2 ^ j) j K c : ℝ) / 2 ^ j - 1 / 2 ^ K =
        ((beyondCountAt (q * 2 ^ j) j K c : ℝ) - 2 ^ j * ((2 : ℝ) ^ K)⁻¹) / 2 ^ j := by
      field_simp
    rw [heq, abs_div, abs_of_pos hpowpos]
  have hpartition (c : ℕ) :
      ∑ r ∈ Finset.range (2 ^ j), resInd K c (tstep^[j] (q * 2 ^ j + r)) =
        (∑ a ∈ L, S c a) + ∑ a ∈ H, S c a := by
    rw [sum_resInd_window_eq_sum_levelSet]
    exact (Finset.sum_filter_add_sum_filter_not I P (S c)).symm
  have hHnorm (c : ℕ) : ‖∑ a ∈ H, S c a‖ ≤
      ∑ a ∈ H, ∑ r ∈ levelSet j a, ‖resInd K c (tstep^[j] r + 3 ^ a * q)‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
  have hLcard : ∑ a ∈ L, ((levelSet j a).card : ℝ) ≤ 2 ^ j := by
    calc
      ∑ a ∈ L, ((levelSet j a).card : ℝ) ≤
          ∑ a ∈ I, ((levelSet j a).card : ℝ) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => by positivity)
      _ = 2 ^ j := by
        exact_mod_cast sum_levelSet_card j
  have hHcard : ∑ a ∈ H, ((levelSet j a).card : ℝ) = E := by
    exact_mod_cast sum_levelSet_card_filter j (fun a => ¬ P a)
  have hLsum : ∑ c ∈ Finset.range (2 ^ K), ∑ a ∈ L, ‖S c a‖ ≤ M * 2 ^ j := by
    rw [Finset.sum_comm]
    calc
      ∑ a ∈ L, ∑ c ∈ Finset.range (2 ^ K), ‖S c a‖ ≤
          ∑ a ∈ L, M * ((levelSet j a).card : ℝ) := by
        refine Finset.sum_le_sum fun a ha => ?_
        have hsh : ∑ c ∈ Finset.range (2 ^ K), ‖S c a‖ =
            ∑ c ∈ Finset.range (2 ^ K), ‖∑ r ∈ levelSet j a, resInd K c (tstep^[j] r)‖ :=
          sum_norm_sum_resInd_add K _ (fun r => tstep^[j] r) _
        rw [hsh]
        exact hslice a (Finset.mem_filter.mp ha).2
      _ = M * ∑ a ∈ L, ((levelSet j a).card : ℝ) := by rw [Finset.mul_sum]
      _ ≤ M * 2 ^ j := mul_le_mul_of_nonneg_left hLcard hM
  have hHsum : ∑ c ∈ Finset.range (2 ^ K),
      ∑ a ∈ H, ∑ r ∈ levelSet j a, ‖resInd K c (tstep^[j] r + 3 ^ a * q)‖ ≤ 2 * (E : ℝ) := by
    rw [Finset.sum_comm]
    calc
      ∑ a ∈ H, ∑ c ∈ Finset.range (2 ^ K),
          ∑ r ∈ levelSet j a, ‖resInd K c (tstep^[j] r + 3 ^ a * q)‖ =
          ∑ a ∈ H, ∑ r ∈ levelSet j a,
            ∑ c ∈ Finset.range (2 ^ K), ‖resInd K c (tstep^[j] r + 3 ^ a * q)‖ := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_comm]
      _ ≤ ∑ a ∈ H, ∑ _r ∈ levelSet j a, (2 : ℝ) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun r _ => sum_norm_resInd_le K _
      _ = 2 * ∑ a ∈ H, ((levelSet j a).card : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
      _ = 2 * (E : ℝ) := by rw [hHcard]
  unfold beyondTVAt
  calc
    ∑ c ∈ Finset.range (2 ^ K), |(beyondCountAt (q * 2 ^ j) j K c : ℝ) / 2 ^ j - 1 / 2 ^ K| =
        (∑ c ∈ Finset.range (2 ^ K),
          ‖∑ r ∈ Finset.range (2 ^ j), resInd K c (tstep^[j] (q * 2 ^ j + r))‖) / 2 ^ j := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun c _ => hterm c
    _ ≤ (∑ c ∈ Finset.range (2 ^ K), ((∑ a ∈ L, ‖S c a‖) +
          ∑ a ∈ H, ∑ r ∈ levelSet j a, ‖resInd K c (tstep^[j] r + 3 ^ a * q)‖)) / 2 ^ j := by
      gcongr with c hc
      rw [hpartition c]
      exact (norm_add_le _ _).trans (add_le_add (norm_sum_le _ _) (hHnorm c))
    _ ≤ (M * 2 ^ j + 2 * (E : ℝ)) / 2 ^ j := by
      gcongr
      rw [Finset.sum_add_distrib]
      exact add_le_add hLsum hHsum
    _ = M + 2 * (E : ℝ) / 2 ^ j := by
      field_simp

/-- **Frozen (2026-11-04).**  Log-depth uniformity on every aligned window, unconditional. -/
theorem beyondWordsUniformLogAt :
    ∀ C : ℝ, ∀ ε > (0 : ℝ), ∀ᶠ j : ℕ in atTop, ∀ K : ℕ, (K : ℝ) ≤ C * Real.logb 2 j →
      ∀ q : ℕ, beyondTVAt (q * 2 ^ j) j K ≤ ε := by
  sorry

/-- **Frozen (2026-11-04).**  Linear-depth uniformity on every aligned window, every
`κ < (log₂ 3)/2`, from the sliced Proposition 1.14 node. -/
theorem beyondWordsUniformLinearAt_of_sliceOscDecay_sharp (h : SliceOscDecay) (κ : ℝ)
    (hκ : κ < Real.logb 2 3 / 2) :
    ∀ ε > (0 : ℝ), ∀ᶠ j : ℕ in atTop, ∀ K : ℕ, (K : ℝ) ≤ κ * j →
      ∀ q : ℕ, beyondTVAt (q * 2 ^ j) j K ≤ ε := by
  sorry

end CollatzMoonshot.Conjugacy
