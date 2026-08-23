/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.FrontA.BackwardTwoThirdsRenewal
import CollatzMoonshot.FrontA.BackwardStopping

/-!
# The recursive exponent-`2/3` stopping-line construction

This file discharges `TwoThirdsRepeatOrStoppingGrowth`, the last pinned `def`
of the exponent-`2/3` renewal layer.  It is the five-state analogue of
`netHalfRepeatOrStoppingGrowth`: the construction expands a finite frontier of
`Fin 5 × ℕ` height states rooted at `(0, d)`, replacing every node with
endpoint at most `H` by its certified child set
(`exists_twoThirdsChildFinset`), and freezing every node whose endpoint exceeds
`H` as a first exit.

The two nonstandard ingredients are pure bookkeeping and are reused *verbatim*
from `BackwardStopping`, because they involve only natural-number values, not
the state labels: the value-based ancestor chain `StoppingChain` (with
`chain_agree`, `chain_reachesValuePos`, `StoppingChain.round_add_le`), the
band-propagation step `reusable_band_step`, and the collision-to-cycle splice
`reachesValuePos_self_iff_onCycle`.  Only the state-carrying wrappers
(`TwoThirdsStoppingNode`, `TwoThirdsStoppingFront`) and the three round lemmas
are re-derived here, over `InFiveHeightState`/`Fin 5` and the exact real edge
weight `((x)/(y))^(2/3)` telescoped by `twoThirdsEdgeWeight_mul`.
-/

namespace CollatzMoonshot.FrontA

open scoped Real

/-! ## The frontier invariant -/

/-- The per-node frontier invariant, five-state version. -/
def TwoThirdsStoppingNode (d H m : ℕ) (s : TwoThirdsNode) : Prop :=
  InFiveHeightState d s.1 s.2 ∧ s.2 % 2 = 1 ∧ ¬3 ∣ s.2 ∧ s.2 < 2 ^ 23 * H ∧
    ReachesInBand d (2 ^ 25 * H) s.2 ∧ StoppingChain d H m s.2

/-- The full frontier invariant at round `m`: value injectivity, per-node
state data, and strict telescoping exponent-`2/3` mass above the root
potential. -/
def TwoThirdsStoppingFront (d H m : ℕ) (F : Finset TwoThirdsNode) : Prop :=
  TwoThirdsValuesInjective F ∧ (∀ s ∈ F, TwoThirdsStoppingNode d H m s) ∧
    (twoThirdsPotential 0 d : ℝ) <
      ∑ s ∈ F, twoThirdsEdgeWeight d s.2 * (twoThirdsPotential s.1 s.2 : ℝ)

/-- The root state `(0, d)` sits in its own height floor `1`. -/
theorem inFiveHeightState_root (d : ℕ) : InFiveHeightState d 0 d := by
  simp only [InFiveHeightState, fiveHeightNum, fiveHeightDen]
  norm_num

/-- The round-`1` frontier: the certified child set of the root itself. -/
theorem twoThirdsFront_init {d H : ℕ} (hd : 2 ≤ d) (hdodd : d % 2 = 1)
    (hd3 : ¬3 ∣ d) (hdH : d ≤ H) : ∃ F, TwoThirdsStoppingFront d H 1 F := by
  obtain ⟨C, hCne, hCinj, hCchild, hCbound, hCmass⟩ :=
    exists_twoThirdsChildFinset (0 : Fin 5) hd hd hd3 (inFiveHeightState_root d)
  have hd25 : d ≤ 2 ^ 25 * H :=
    le_trans hdH (Nat.le_mul_of_pos_left H (by norm_num))
  have hrootband : ReachesInBand d (2 ^ 25 * H) d := by
    refine ⟨0, rfl, ?_⟩
    intro t ht
    have ht0 : t = 0 := Nat.le_zero.mp ht
    subst ht0
    simp only [Function.iterate_zero_apply]
    exact ⟨le_rfl, hd25⟩
  have hmul : 2 ^ 23 * d ≤ 2 ^ 23 * H := Nat.mul_le_mul_left _ hdH
  refine ⟨C, hCinj, ?_, hCmass⟩
  intro c hc
  have hchild := hCchild c hc
  have hrub : ReusableOddBlockChild d c.2 := hchild.1
  have hdc : d ≤ c.2 := hchild.2.le
  obtain ⟨j, hj1, hcodd, hc3, hblock⟩ := hrub
  have hboundH : 3 * c.2 < 2 ^ 23 * H := lt_of_lt_of_le (hCbound c hc) hmul
  have hdcstrict : d < c.2 :=
    ReusableOddBlockChild.lt_of_le hd ⟨j, hj1, hcodd, hc3, hblock⟩ hdc
  refine ⟨hchild.2, hcodd, hc3, by omega, ?_, ?_⟩
  · exact reusable_band_step (by omega) le_rfl hdH hdc hboundH
      ⟨j, hj1, hcodd, hc3, hblock⟩ hrootband
  · refine ⟨1, consChain c.2 fun _ => d, le_rfl, fun _ => rfl, rfl,
      by simp, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      rcases i with _ | i
      · simpa using hcodd
      · simpa using hdodd
    · intro i hi
      rcases i with _ | i
      · simpa using hdc
      · simp
    · intro i hi1 hi
      rcases i with _ | i
      · omega
      · simpa using hdH
    · intro i hi
      have hi0 : i = 0 := by omega
      subst hi0
      simpa using ⟨j, hj1, hcodd, hc3, hblock⟩
    · intro i k hik hk
      have hi0 : i = 0 := by omega
      have hk1 : k = 1 := by omega
      subst hi0; subst hk1
      simpa using (by omega : c.2 ≠ d)

/-- One expansion round: either some generated endpoint value collides with a
live frontier value or with its own ancestry, yielding an explicit positive
cycle above the floor, or the frontier advances one round with all invariants
intact. -/
theorem twoThirdsFront_step {d H m : ℕ} (hd : 2 ≤ d) (_hdH : d ≤ H)
    {F : Finset TwoThirdsNode} (hF : TwoThirdsStoppingFront d H m F)
    (hL : (F.filter fun s => s.2 ≤ H).Nonempty) :
    (∃ n, d ≤ n ∧ OnCycle n) ∨ ∃ F', TwoThirdsStoppingFront d H (m + 1) F' := by
  classical
  obtain ⟨hinj, hnode, hmass⟩ := hF
  set L := F.filter (fun s => s.2 ≤ H) with hLdef
  set E := F.filter (fun s => ¬s.2 ≤ H) with hEdef
  -- certified child sets for every low node
  have hcc : ∀ s : TwoThirdsNode, s ∈ F → s.2 ≤ H →
      ∃ C : Finset TwoThirdsNode, C.Nonempty ∧ TwoThirdsValuesInjective C ∧
        (∀ c ∈ C, TwoThirdsChildAt d s c) ∧
        (∀ c ∈ C, 3 * c.2 < 2 ^ 23 * s.2) ∧
        (twoThirdsPotential s.1 s.2 : ℝ) <
          ∑ c ∈ C, twoThirdsEdgeWeight s.2 c.2 *
            (twoThirdsPotential c.1 c.2 : ℝ) := by
    intro s hs _
    obtain ⟨hstate, _, h3, _, _, _⟩ := hnode s hs
    have hx2 : 2 ≤ s.2 := le_trans hd hstate.le
    exact exists_twoThirdsChildFinset s.1 hd hx2 h3 hstate
  choose! Cf hCne hCinj hCchild hCbound hCmass using hcc
  -- ancestor chains for every frontier node
  have hch : ∀ s : TwoThirdsNode, s ∈ F →
      ∃ r : ℕ, ∃ g : ℕ → ℕ, r ≤ m ∧ (s.2 ≤ H → r = m) ∧ g 0 = s.2 ∧
        g r = d ∧ (∀ i, i ≤ r → g i % 2 = 1) ∧ (∀ i, i ≤ r → d ≤ g i) ∧
        (∀ i, 1 ≤ i → i ≤ r → g i ≤ H) ∧
        (∀ i, i < r → ReusableOddBlockChild (g (i + 1)) (g i)) ∧
        (∀ i j, i < j → j ≤ r → g i ≠ g j) :=
    fun s hs => (hnode s hs).2.2.2.2.2
  choose! rk gk hrm hlowr hg0 hgr hgodd hgge hgleH hgedge hgne using hch
  by_cases hcol : ∃ s ∈ L, ∃ c ∈ Cf s,
      (∃ i, i ≤ rk s ∧ gk s i = c.2) ∨ ∃ t ∈ F, t.2 = c.2
  · -- a repeated value: extract an explicit cycle
    left
    obtain ⟨s, hsL, c, hcC, hcase⟩ := hcol
    have hsF : s ∈ F := (Finset.mem_filter.mp hsL).1
    have hsH : s.2 ≤ H := (Finset.mem_filter.mp hsL).2
    have hrs : rk s = m := hlowr s hsF hsH
    have hchild := hCchild s hsF hsH c hcC
    have hedge_c : ReusableOddBlockChild s.2 c.2 := hchild.1
    have hdc : d ≤ c.2 := hchild.2.le
    rcases hcase with ⟨i, hir, hgi⟩ | ⟨t, htF, htc⟩
    · -- the child value already lies on its own ancestor chain
      refine ⟨c.2, hdc, ?_⟩
      rw [← reachesValuePos_self_iff_onCycle]
      have h1 : ReachesValuePos c.2 s.2 := hedge_c.reachesValuePos
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · have hsc : s.2 = c.2 := by rw [← hgi, hg0 s hsF]
        rwa [hsc] at h1
      · have h2 : ReachesValuePos (gk s 0) (gk s i) :=
          chain_reachesValuePos (hgedge s hsF) 0 i hi0 hir
        rw [hg0 s hsF] at h2
        have h3 := h1.trans h2
        rwa [hgi] at h3
    · -- the child value equals a live frontier value: chains of two lengths
      have hrt : rk t ≤ m := hrm t htF
      set g' : ℕ → ℕ := consChain c.2 (gk s) with hg'def
      obtain ⟨j, hj1, hcodd, hc3, hblock⟩ := hedge_c
      have hg'odd : ∀ i, i ≤ m + 1 → g' i % 2 = 1 := by
        intro i hi
        rcases i with _ | i
        · simpa [hg'def] using hcodd
        · simpa [hg'def] using hgodd s hsF i (by omega)
      have hg'edge : ∀ i, i < m + 1 →
          ReusableOddBlockChild (g' (i + 1)) (g' i) := by
        intro i hi
        rcases i with _ | i
        · simp only [hg'def, consChain_succ, consChain_zero, hg0 s hsF]
          exact ⟨j, hj1, hcodd, hc3, hblock⟩
        · simp only [hg'def, consChain_succ]
          exact hgedge s hsF i (by omega)
      have hagree := chain_agree (r := m + 1) (r' := rk t)
        (by rw [hg'def, consChain_zero, hg0 t htF]; exact htc.symm)
        hg'odd (hgodd t htF) hg'edge (hgedge t htF)
      have hmid : g' (rk t) = d := by
        rw [hagree (rk t) (by omega) le_rfl, hgr t htF]
      have htop : g' (m + 1) = d := by
        have h := hgr s hsF
        rw [hrs] at h
        simpa [hg'def] using h
      refine ⟨d, le_rfl, ?_⟩
      rw [← reachesValuePos_self_iff_onCycle]
      have h := chain_reachesValuePos hg'edge (rk t) (m + 1) (by omega) le_rfl
      rwa [hmid, htop] at h
  · -- no collision: replace every low node by its child set
    right
    push Not at hcol
    refine ⟨E ∪ L.biUnion Cf, ?_, ?_, ?_⟩
    · -- value injectivity of the new frontier
      intro a ha b hb hab
      rcases Finset.mem_union.mp ha with haE | haB
      · have haF : a ∈ F := (Finset.mem_filter.mp haE).1
        rcases Finset.mem_union.mp hb with hbE | hbB
        · exact hinj a haF b ((Finset.mem_filter.mp hbE).1) hab
        · obtain ⟨s, hsL, hbC⟩ := Finset.mem_biUnion.mp hbB
          exact absurd hab ((hcol s hsL b hbC).2 a haF)
      · obtain ⟨s, hsL, haC⟩ := Finset.mem_biUnion.mp haB
        rcases Finset.mem_union.mp hb with hbE | hbB
        · have hbF : b ∈ F := (Finset.mem_filter.mp hbE).1
          exact absurd hab.symm ((hcol s hsL a haC).2 b hbF)
        · obtain ⟨s', hs'L, hbC⟩ := Finset.mem_biUnion.mp hbB
          have hsF : s ∈ F := (Finset.mem_filter.mp hsL).1
          have hsH : s.2 ≤ H := (Finset.mem_filter.mp hsL).2
          have hs'F : s' ∈ F := (Finset.mem_filter.mp hs'L).1
          have hs'H : s'.2 ≤ H := (Finset.mem_filter.mp hs'L).2
          have hss : s = s' := by
            apply hinj s hsF s' hs'F
            have h1 := (hCchild s hsF hsH a haC).1
            have h2 := (hCchild s' hs'F hs'H b hbC).1
            rw [hab] at h1
            exact reusableOddBlockChild_parent_eq (hnode s hsF).2.1
              (hnode s' hs'F).2.1 h1 h2
          subst hss
          exact hCinj s hsF hsH a haC b hbC hab
    · -- per-node invariants
      intro c hc
      rcases Finset.mem_union.mp hc with hcE | hcB
      · have hcF : c ∈ F := (Finset.mem_filter.mp hcE).1
        have hcH : ¬c.2 ≤ H := (Finset.mem_filter.mp hcE).2
        obtain ⟨hstate, hodd, h3, hlt, hband, _⟩ := hnode c hcF
        refine ⟨hstate, hodd, h3, hlt, hband,
          rk c, gk c, by have := hrm c hcF; omega, fun h => absurd h hcH,
          hg0 c hcF, hgr c hcF, hgodd c hcF, hgge c hcF, hgleH c hcF,
          hgedge c hcF, hgne c hcF⟩
      · obtain ⟨s, hsL, hcC⟩ := Finset.mem_biUnion.mp hcB
        have hsF : s ∈ F := (Finset.mem_filter.mp hsL).1
        have hsH : s.2 ≤ H := (Finset.mem_filter.mp hsL).2
        have hrs : rk s = m := hlowr s hsF hsH
        have hchild := hCchild s hsF hsH c hcC
        have hedge_c : ReusableOddBlockChild s.2 c.2 := hchild.1
        have hdc : d ≤ c.2 := hchild.2.le
        have hds : d ≤ s.2 := (hnode s hsF).1.le
        obtain ⟨j, hj1, hcodd, hc3, hblock⟩ := hedge_c
        have hmul : 2 ^ 23 * s.2 ≤ 2 ^ 23 * H := Nat.mul_le_mul_left _ hsH
        have hboundH : 3 * c.2 < 2 ^ 23 * H :=
          lt_of_lt_of_le (hCbound s hsF hsH c hcC) hmul
        refine ⟨hchild.2, hcodd, hc3, by omega, ?_, ?_⟩
        · exact reusable_band_step (by omega) hds hsH hdc hboundH
            ⟨j, hj1, hcodd, hc3, hblock⟩ (hnode s hsF).2.2.2.2.1
        · refine ⟨m + 1, consChain c.2 (gk s), le_rfl, fun _ => rfl,
            consChain_zero _ _, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · have h := hgr s hsF
            rw [hrs] at h
            simpa using h
          · intro i hi
            rcases i with _ | i
            · simpa using hcodd
            · simpa using hgodd s hsF i (by omega)
          · intro i hi
            rcases i with _ | i
            · simpa using hdc
            · simpa using hgge s hsF i (by omega)
          · intro i hi1 hi
            rcases i with _ | i
            · omega
            · rcases i with _ | i
              · have h := hg0 s hsF
                simpa [h] using hsH
              · simpa using hgleH s hsF (i + 1) (by omega) (by omega)
          · intro i hi
            rcases i with _ | i
            · simp only [consChain_succ, consChain_zero, hg0 s hsF]
              exact ⟨j, hj1, hcodd, hc3, hblock⟩
            · simp only [consChain_succ]
              exact hgedge s hsF i (by omega)
          · intro i k hik hk
            rcases i with _ | i
            · rcases k with _ | k
              · omega
              · simp only [consChain_zero, consChain_succ]
                exact fun h => (hcol s hsL c hcC).1 k (by omega) h.symm
            · rcases k with _ | k
              · omega
              · simp only [consChain_succ]
                exact hgne s hsF i k (by omega) (by omega)
    · -- strict mass growth
      have hLne : L.Nonempty := hL
      have hdisj : ∀ a ∈ L, ∀ b ∈ L, a ≠ b → Disjoint (Cf a) (Cf b) := by
        intro a ha b hb hab
        have haF : a ∈ F := (Finset.mem_filter.mp ha).1
        have haH : a.2 ≤ H := (Finset.mem_filter.mp ha).2
        have hbF : b ∈ F := (Finset.mem_filter.mp hb).1
        have hbH : b.2 ≤ H := (Finset.mem_filter.mp hb).2
        rw [Finset.disjoint_left]
        intro c hca hcb
        have h1 := (hCchild a haF haH c hca).1
        have h2 := (hCchild b hbF hbH c hcb).1
        exact hab (hinj a haF b hbF
          (reusableOddBlockChild_parent_eq (hnode a haF).2.1
            (hnode b hbF).2.1 h1 h2))
      have hexp := weighted_biUnion_expands L hLne Cf
        (fun s => twoThirdsEdgeWeight d s.2)
        (fun s => (twoThirdsPotential s.1 s.2 : ℝ))
        (fun s c => twoThirdsEdgeWeight s.2 c.2)
        hdisj
        (by
          intro s hs
          have hds : d ≤ s.2 := (hnode s ((Finset.mem_filter.mp hs).1)).1.le
          unfold twoThirdsEdgeWeight
          apply Real.rpow_pos_of_pos
          apply div_pos
          · exact_mod_cast (by omega : 0 < d)
          · exact_mod_cast (by omega : 0 < s.2))
        (by
          intro s hs
          exact hCmass s ((Finset.mem_filter.mp hs).1)
            ((Finset.mem_filter.mp hs).2))
        (by
          intro s hs c hc
          have hsF : s ∈ F := (Finset.mem_filter.mp hs).1
          have hsH : s.2 ≤ H := (Finset.mem_filter.mp hs).2
          have hds : d ≤ s.2 := (hnode s hsF).1.le
          have hdc : d ≤ c.2 := (hCchild s hsF hsH c hc).2.le
          exact twoThirdsEdgeWeight_mul (by omega) (by omega))
      have hEdisj : Disjoint E (L.biUnion Cf) := by
        rw [Finset.disjoint_left]
        intro c hcE hcB
        obtain ⟨s, hsL, hcC⟩ := Finset.mem_biUnion.mp hcB
        exact (hcol s hsL c hcC).2 c ((Finset.mem_filter.mp hcE).1) rfl
      have hsplit :
          (∑ s ∈ F, twoThirdsEdgeWeight d s.2 *
              (twoThirdsPotential s.1 s.2 : ℝ)) =
            (∑ s ∈ L, twoThirdsEdgeWeight d s.2 *
              (twoThirdsPotential s.1 s.2 : ℝ)) +
            ∑ s ∈ E, twoThirdsEdgeWeight d s.2 *
              (twoThirdsPotential s.1 s.2 : ℝ) := by
        rw [hLdef, hEdef,
          Finset.sum_filter_add_sum_filter_not F (fun s => s.2 ≤ H)]
      calc
        (twoThirdsPotential 0 d : ℝ) <
            ∑ s ∈ F, twoThirdsEdgeWeight d s.2 *
              (twoThirdsPotential s.1 s.2 : ℝ) := hmass
        _ = (∑ s ∈ L, twoThirdsEdgeWeight d s.2 *
              (twoThirdsPotential s.1 s.2 : ℝ)) +
            ∑ s ∈ E, twoThirdsEdgeWeight d s.2 *
              (twoThirdsPotential s.1 s.2 : ℝ) := hsplit
        _ < (∑ s ∈ L.biUnion Cf, twoThirdsEdgeWeight d s.2 *
              (twoThirdsPotential s.1 s.2 : ℝ)) +
            ∑ s ∈ E, twoThirdsEdgeWeight d s.2 *
              (twoThirdsPotential s.1 s.2 : ℝ) := by
              exact add_lt_add_of_lt_of_le hexp le_rfl
        _ = ∑ s ∈ E ∪ L.biUnion Cf, twoThirdsEdgeWeight d s.2 *
              (twoThirdsPotential s.1 s.2 : ℝ) := by
              rw [Finset.sum_union hEdisj]
              ring

/-- A frontier with no remaining low node is exactly the pinned exponent-`2/3`
stopping frontier. -/
theorem twoThirdsStoppingFrontier_of_no_low {d H m : ℕ}
    {F : Finset TwoThirdsNode} (hF : TwoThirdsStoppingFront d H m F)
    (hL : ¬(F.filter fun s => s.2 ≤ H).Nonempty) :
    TwoThirdsStoppingFrontier d H F := by
  obtain ⟨hinj, hnode, hmass⟩ := hF
  refine ⟨hinj, hmass, ?_⟩
  intro s hs
  have hsH : ¬s.2 ≤ H := fun h => hL ⟨s, Finset.mem_filter.mpr ⟨hs, h⟩⟩
  exact ⟨by omega, (hnode s hs).2.2.2.1, (hnode s hs).2.2.2.2.1⟩

/-- **The recursive exponent-`2/3` stopping-line theorem.**  Every odd reusable
root either exposes a positive Collatz cycle at or above its own floor, or
carries a finite first-exit frontier with the certified exponent-`2/3`
telescoping mass.  The fuel `H + 1` suffices because every expansion round
lengthens all live ancestor chains, and a low chain is a set of distinct values
in `[d, H]`. -/
theorem twoThirdsRepeatOrStoppingGrowth : TwoThirdsRepeatOrStoppingGrowth := by
  intro d H hd hdodd hd3 hdH
  obtain ⟨F₁, hF₁⟩ := twoThirdsFront_init hd hdodd hd3 hdH
  suffices h : ∀ k m (F : Finset TwoThirdsNode), TwoThirdsStoppingFront d H m F →
      H + 2 ≤ m + k →
      (∃ n, d ≤ n ∧ OnCycle n) ∨
        ∃ S : Finset TwoThirdsNode, TwoThirdsStoppingFrontier d H S by
    exact h (H + 1) 1 F₁ hF₁ (by omega)
  intro k
  induction k with
  | zero =>
      intro m F hF hm
      by_cases hL : (F.filter fun s => s.2 ≤ H).Nonempty
      · exfalso
        obtain ⟨s, hs⟩ := hL
        have hsF : s ∈ F := (Finset.mem_filter.mp hs).1
        have hsH : s.2 ≤ H := (Finset.mem_filter.mp hs).2
        have hchain := (hF.2.1 s hsF).2.2.2.2.2
        have := hchain.round_add_le hdH hsH
        omega
      · exact Or.inr ⟨F, twoThirdsStoppingFrontier_of_no_low hF hL⟩
  | succ k ih =>
      intro m F hF hm
      by_cases hL : (F.filter fun s => s.2 ≤ H).Nonempty
      · rcases twoThirdsFront_step hd hdH hF hL with hcyc | ⟨F', hF'⟩
        · exact Or.inl hcyc
        · exact ih (m + 1) F' hF' (by omega)
      · exact Or.inr ⟨F, twoThirdsStoppingFrontier_of_no_low hF hL⟩

/-! ## Eliminating the cycle alternative -/

/-- Once no nontrivial cycle exists, the repeat alternative in
`twoThirdsRepeatOrStoppingGrowth` is impossible for an odd unit root `d ≥ 2`. -/
theorem twoThirdsStoppingFrontier_of_noCycle (hnc : NoNontrivialCycle)
    {d H : ℕ} (hd : 2 ≤ d) (hdodd : d % 2 = 1) (hd3 : ¬3 ∣ d) (hdH : d ≤ H) :
    ∃ S : Finset TwoThirdsNode, TwoThirdsStoppingFrontier d H S := by
  rcases twoThirdsRepeatOrStoppingGrowth d H hd hdodd hd3 hdH with hcycle | hfront
  · obtain ⟨n, hdn, hncycle⟩ := hcycle
    have hn : 1 ≤ n := by omega
    rcases hnc n hn hncycle with rfl | rfl | rfl <;> omega
  · exact hfront

/-! ## A kernel-checked uniform lower bound on the potential -/

/-- Every unit residue of every floor has potential at least `100000`. -/
theorem twoThirdsPotential_ge_min_fin :
    ∀ i : Fin 5, ∀ r : Fin 81, r.1 % 3 ≠ 0 →
      100000 ≤ twoThirdsPotential i r.1 := by
  decide +kernel

/-- The frozen `2/3`-potential is uniformly at least `100000` on unit
residues. -/
theorem twoThirdsPotential_ge_min {x : ℕ} (h3 : ¬3 ∣ x) (i : Fin 5) :
    100000 ≤ twoThirdsPotential i x := by
  rw [← twoThirdsPotential_mod]
  have hr81 : x % 81 < 81 := Nat.mod_lt x (by norm_num)
  have hru : (x % 81) % 3 ≠ 0 := by
    rw [Nat.mod_mod_of_dvd x (by norm_num : 3 ∣ 81)]
    exact fun h0 => h3 (Nat.dvd_of_mod_eq_zero h0)
  exact twoThirdsPotential_ge_min_fin i ⟨x % 81, hr81⟩ hru

/-! ## The explicit exponent-`2/3` stopping-frontier cardinal corollary -/

/-- **Explicit exponent-`2/3` stopping cardinal.**  Assuming no nontrivial
cycle, every odd unit root `2 ≤ d ≤ H` has a finite value-injective first-exit
frontier whose cardinality strictly exceeds the explicit
`(100000 / 1051827) · (H/d)^(2/3)` bound, with every endpoint a first exit in
`(H, 2^23 H)` reached inside the band `[d, 2^25 H]`. -/
theorem twoThirds_stopping_card_bound (hnc : NoNontrivialCycle)
    {d H : ℕ} (hd : 2 ≤ d) (hdodd : d % 2 = 1) (hd3 : ¬3 ∣ d) (hdH : d ≤ H) :
    ∃ S : Finset TwoThirdsNode,
      (100000 : ℝ) <
        (S.card : ℝ) * (1051827 * ((d : ℝ) / (H : ℝ)) ^ (2 / 3 : ℝ)) ∧
      (∀ s ∈ S, ∀ t ∈ S, s.2 = t.2 → s = t) ∧
      ∀ s ∈ S, H < s.2 ∧ s.2 < 2 ^ 23 * H ∧
        ReachesInBand d (2 ^ 25 * H) s.2 := by
  obtain ⟨S, hS⟩ :=
    twoThirdsStoppingFrontier_of_noCycle hnc hd hdodd hd3 hdH
  have hb := hS.card_bound (by omega) (by omega)
  have hmin : (100000 : ℝ) ≤ (twoThirdsPotential 0 d : ℝ) := by
    exact_mod_cast twoThirdsPotential_ge_min hd3 0
  exact ⟨S, lt_of_le_of_lt hmin hb, hS.1, hS.2.2⟩

end CollatzMoonshot.FrontA
