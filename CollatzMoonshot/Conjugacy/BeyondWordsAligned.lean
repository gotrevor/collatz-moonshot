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

**Status (2026-11-04).**  Proved.  `tstep_iterate_add_mul` (shift identity),
`sum_norm_sum_resInd_add` (shift invariance, via the bijection `c ↦ c − s` of `ZMod (2^K)`), and
`beyondTVAt_le_of_band` (the window form of `beyondTV_le_of_band`, same per-slice hypothesis) carry
the assemblies of `beyondWordsUniformLog` and `beyondWordsUniformLinear_of_sliceOscDecay_sharp` to
every window, uniformly in `q`.
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
  intro C ε hε
  have h := sliceCharDecay_of_pascalDampingDecay pascalDampingDecay
  obtain ⟨C', hC'pos, hslice⟩ := exists_norm_levelSum_le_rate h (⌈C⌉₊ + 2) (by omega)
  have hsmall := (tendsto_logMajorant C' ⌈C⌉₊).eventually (gt_mem_nhds (half_pos hε))
  have htail := (tendsto_const_div_atTop_nhds_zero_nat (200 : ℝ)).eventually
    (gt_mem_nhds (half_pos hε))
  filter_upwards [hsmall, htail, eventually_ge_atTop 4096] with j hjM hjt hj
  intro K hK q
  set N := ⌈C⌉₊ with hN
  have hjR1 : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
  have hjRpos : (0 : ℝ) < j := by linarith
  have h2K : (2 : ℝ) ^ K ≤ (j : ℝ) ^ N := by
    have hlog : (K : ℝ) ≤ Real.logb 2 ((j : ℝ) ^ N) := by
      rw [Real.logb_pow]
      have h0 : 0 ≤ Real.logb 2 (j : ℝ) := Real.logb_nonneg one_lt_two hjR1
      have hCN : C ≤ (N : ℝ) := Nat.le_ceil C
      nlinarith [mul_le_mul_of_nonneg_right hCN h0]
    rw [Real.le_logb_iff_rpow_le one_lt_two (by positivity), Real.rpow_natCast] at hlog
    exact hlog
  have hM0 : 0 ≤ logMajorant C' N j := by unfold logMajorant; positivity
  have hper : ∀ a, j ≤ 4 * a → a ≤ 11 * j / 20 →
      ∑ c ∈ Finset.range (2 ^ K), ‖∑ r ∈ levelSet j a, resInd K c (tstep^[j] r)‖ ≤
        logMajorant C' N j * (levelSet j a).card := by
    intro a hja haj
    let E : ℝ := (2 ^ (N + 2) * C' / (j : ℝ) ^ (N + 2) +
        (j : ℝ) * ((7 : ℝ) / 8) ^ (j / 16 - j / 32)) * (4 * (j + 1)) +
      ((3 : ℝ) ^ (j / 4096))⁻¹ * (4 * (j + 1))
    have hE0 : 0 ≤ E := by positivity
    have hcard : (0 : ℝ) ≤ (levelSet j a).card := by positivity
    have hpt : ∀ c ∈ Finset.range (2 ^ K),
        ‖∑ r ∈ levelSet j a, resInd K c (tstep^[j] r)‖ ≤ E * (levelSet j a).card := by
      intro c hc
      have hb := hslice j a hj hja haj (resInd K c) 1
        (layeredWeight_resInd (Finset.mem_range.mp hc) a)
      have haj' : (a : ℝ) + 1 ≤ (j : ℝ) + 1 := by
        have : a ≤ j := by omega
        have : (a : ℝ) ≤ j := by exact_mod_cast this
        linarith
      calc
        ‖∑ r ∈ levelSet j a, resInd K c (tstep^[j] r)‖ ≤ _ := hb
        _ ≤ E * (levelSet j a).card := by
          rw [one_mul]
          dsimp only [E]
          gcongr
    calc
      ∑ c ∈ Finset.range (2 ^ K), ‖∑ r ∈ levelSet j a, resInd K c (tstep^[j] r)‖ ≤
          ∑ _c ∈ Finset.range (2 ^ K), E * (levelSet j a).card := Finset.sum_le_sum hpt
      _ = (2 : ℝ) ^ K * (E * (levelSet j a).card) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
      _ ≤ (j : ℝ) ^ N * (E * (levelSet j a).card) := by gcongr
      _ = logMajorant C' N j * (levelSet j a).card := by
        simp only [logMajorant, E]
        ring
  have hTV := beyondTVAt_le_of_band q j K (fun a => j ≤ 4 * a ∧ a ≤ 11 * j / 20) hM0
    (fun a ha => hper a ha.1 ha.2)
  have hoffcard : ((Finset.range (2 ^ j)).filter
      (fun r => ¬ (j ≤ 4 * oddCount r j ∧ oddCount r j ≤ 11 * j / 20))).card =
        (outOddSet j).card := by
    unfold outOddSet
    congr 1
    ext r
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hoffcard] at hTV
  have hout := outOddSet_ratio_le j (by omega)
  have h2out : 2 * ((outOddSet j).card : ℝ) / 2 ^ j ≤ 200 / j := by
    rw [mul_div_assoc]
    have : (200 : ℝ) / j = 2 * (100 / j) := by ring
    rw [this]
    linarith
  linarith

/-- **Frozen (2026-11-04).**  Linear-depth uniformity on every aligned window, every
`κ < (log₂ 3)/2`, from the sliced Proposition 1.14 node. -/
theorem beyondWordsUniformLinearAt_of_sliceOscDecay_sharp (h : SliceOscDecay) (κ : ℝ)
    (hκ : κ < Real.logb 2 3 / 2) :
    ∀ ε > (0 : ℝ), ∀ᶠ j : ℕ in atTop, ∀ K : ℕ, (K : ℝ) ≤ κ * j →
      ∀ q : ℕ, beyondTVAt (q * 2 ^ j) j K ≤ ε := by
  classical
  intro ε hε
  obtain ⟨C, hCpos, hC⟩ := h 1 one_pos
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set k := max κ 0 with hkdef
  have hk0 : 0 ≤ k := le_max_right _ _
  have hκk : κ ≤ k := le_max_left _ _
  set t := k * Real.log 2 / Real.log 3 with htdef
  have ht0 : 0 ≤ t := by positivity
  have htl : t * Real.log 3 = k * Real.log 2 := by
    rw [htdef]
    field_simp
  have ht : t < 1 / 2 := by
    have hκ' : κ * Real.log 2 < Real.log 3 / 2 := by
      rw [Real.logb] at hκ
      have := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).1 hκ
      rw [lt_div_iff₀ hl2] at this
      linarith
    have hk' : k * Real.log 2 < Real.log 3 / 2 := by
      rcases le_total κ 0 with h0 | h0
      · rw [hkdef, max_eq_right h0]
        linarith
      · rw [hkdef, max_eq_left h0]
        exact hκ'
    rw [htdef, div_lt_iff₀ hl3]
    linarith
  set g := 1 / 2 - t with hgdef
  have hg : 0 < g := by linarith
  set δ := min (1 / 10 : ℝ) (g / 3) with hδdef
  have hδpos : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ10 : δ ≤ 1 / 10 := min_le_left _ _
  have hδg : δ ≤ g / 3 := min_le_right _ _
  set ρ := t + g / 3 with hρdef
  set η := g / 3 * Real.log 3 with hηdef
  have hη : 0 < η := by positivity
  have hηeq : ρ * Real.log 3 - k * Real.log 2 = η := by
    rw [hρdef, hηdef, ← htl]
    ring
  -- the three eventual thresholds
  have hgeo := (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos (-η)).le
    (Real.exp_lt_one_iff.2 (by linarith))).eventually (gt_mem_nhds (by positivity : 0 < ε / 4))
  have htail := (tendsto_const_div_atTop_nhds_zero_nat (1 / (2 * δ ^ 2))).eventually
    (gt_mem_nhds (by positivity : 0 < ε / 2))
  obtain ⟨N, hN⟩ := exists_nat_gt ((3 / g) * (2 + 8 * C / ε))
  filter_upwards [hgeo, htail, eventually_ge_atTop (N + 1)] with j hjgeo hjtail hjN
  intro K hK
  have hjpos : 0 < j := by omega
  have hjR : (0 : ℝ) < j := by exact_mod_cast hjpos
  have hKk : (K : ℝ) ≤ k * j := hK.trans (mul_le_mul_of_nonneg_right hκk hjR.le)
  have hjN' : (3 / g) * (2 + 8 * C / ε) < j := by
    have : (N : ℝ) + 1 ≤ j := by exact_mod_cast hjN
    linarith
  have hjbig : 2 + 8 * C / ε < g / 3 * j := by
    rw [div_mul_eq_mul_div, lt_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
    rw [div_mul_eq_mul_div, div_lt_iff₀ hg] at hjN'
    linarith
  set s := ⌈ρ * j⌉₊ with hsdef
  have hs1 : ρ * j ≤ s := Nat.le_ceil _
  have hs2 : (s : ℝ) < ρ * j + 1 := Nat.ceil_lt_add_one (by positivity)
  set P : ℕ → Prop := fun a => |(a : ℝ) - j / 2| ≤ δ * j with hPdef
  have hper : ∀ a, P a →
      ∑ c ∈ Finset.range (2 ^ K), ‖∑ r ∈ levelSet j a, resInd K c (tstep^[j] r)‖ ≤
        (ε / 2) * (levelSet j a).card := by
    intro a ha
    have ha' := abs_le.1 ha
    have haR1 : (1 / 2 - δ) * j ≤ a := by linarith [ha'.1]
    have haR2 : (a : ℝ) ≤ (1 / 2 + δ) * j := by linarith [ha'.2]
    -- the scale `m = a − s`
    have hgap : (g / 3) * j - 1 ≤ (a : ℝ) - s := by
      have h1 : ρ + g / 3 ≤ 1 / 2 - δ := by linarith
      have : (ρ + g / 3) * j ≤ (1 / 2 - δ) * j := mul_le_mul_of_nonneg_right h1 hjR.le
      linarith
    have hsa : s ≤ a := by
      have : (s : ℝ) ≤ a := by
        have : 0 ≤ 8 * C / ε := by positivity
        linarith
      exact_mod_cast this
    set m := a - s with hmdef
    have hmR : (m : ℝ) = a - s := by rw [hmdef, Nat.cast_sub hsa]
    have hm8 : 8 * C / ε ≤ m := by
      rw [hmR]
      linarith
    have hm1 : 1 ≤ m := by
      have : (1 : ℝ) ≤ m := by
        have : 0 ≤ 8 * C / ε := by positivity
        rw [hmR]
        linarith
      exact_mod_cast this
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
    have hδj : δ * j ≤ 1 / 10 * j := mul_le_mul_of_nonneg_right hδ10 hjR.le
    have hw1 : j ≤ 5 * a := by
      have : (j : ℝ) ≤ 5 * a := by linarith
      exact_mod_cast this
    have hw2 : 5 * a ≤ 3 * j := by
      have : (5 * a : ℝ) ≤ 3 * j := by linarith
      exact_mod_cast this
    have hb := sum_norm_levelSum_resInd_le j a m K (Nat.sub_le a s)
    have hosc := hC j a m hm1 (Nat.sub_le a s) hw1 hw2
    rw [Real.rpow_neg_one] at hosc
    have hcard : (0 : ℝ) ≤ (levelSet j a).card := by positivity
    have hCm : C * (m : ℝ)⁻¹ ≤ ε / 8 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hmpos]
      rw [div_le_iff₀ hε] at hm8
      linarith
    have hoscε : 2 * levelOsc j a m ≤ ε / 4 * (levelSet j a).card := by
      have : C * (m : ℝ)⁻¹ * (levelSet j a).card ≤ ε / 8 * (levelSet j a).card := by gcongr
      linarith
    have hgeoε : (2 : ℝ) ^ K * ((3 : ℝ) ^ m / 3 ^ a) ≤ ε / 4 := by
      have hpow : (3 : ℝ) ^ a = 3 ^ m * 3 ^ s := by
        rw [← pow_add, hmdef, Nat.sub_add_cancel hsa]
      have h1 : (2 : ℝ) ^ K * ((3 : ℝ) ^ m / 3 ^ a) = 2 ^ K / 3 ^ s := by
        rw [hpow]
        field_simp
      rw [h1]
      exact (two_pow_div_three_pow_le j K s hKk hs1 hηeq).trans hjgeo.le
    calc
      ∑ c ∈ Finset.range (2 ^ K), ‖∑ r ∈ levelSet j a, resInd K c (tstep^[j] r)‖ ≤
          2 * levelOsc j a m + 2 ^ K * ((3 : ℝ) ^ m / 3 ^ a) * (levelSet j a).card := hb
      _ ≤ ε / 4 * (levelSet j a).card + ε / 4 * (levelSet j a).card := by
        gcongr
      _ = (ε / 2) * (levelSet j a).card := by ring
  intro q
  have hTV := beyondTVAt_le_of_band q j K P (by positivity) hper
  have hoff := two_mul_card_offBand_div_le j hjpos hδpos
  have hjtail' : 1 / (2 * δ ^ 2) / j < ε / 2 := hjtail
  simp only [hPdef] at hTV
  linarith

end CollatzMoonshot.Conjugacy
