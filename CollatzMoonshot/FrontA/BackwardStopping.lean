/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.FrontA.BackwardRenewal

/-!
# The recursive stopping-line construction

This file discharges `NetHalfRepeatOrStoppingGrowth`, the last pinned `def` of
the barriered renewal layer.  The construction expands a finite frontier of
height states rooted at `(false, d)`.  Every node with endpoint at most `H` is
replaced by its certified child set (`exists_netHalfChildFinset`), and every
node whose endpoint exceeds `H` is frozen as a first exit.

The two nonstandard ingredients are both bookkeeping, not new mathematics:

* **Ancestor chains.**  Every frontier node carries an odd-parent chain back
  to the root whose length equals its creation round.  Because `3y + 1` has a
  unique factorization `2^j · odd`, an odd-block child determines its odd
  parent; two chains from a common value therefore agree step by step.  If a
  newly generated endpoint value collides with any current frontier value or
  with any value on its own chain, the two chains splice into a forward
  Collatz path from some value above `d` back to itself: the `OnCycle`
  alternative.

* **Termination.**  In the no-collision branch, the chain of a node expanded
  at round `m` consists of `m` pairwise-distinct odd values in `[d, H]`, so
  `m + d ≤ H + 1`.  Running the expansion with fuel `H + 1` therefore always
  terminates in a frontier all of whose endpoints exceed `H`.

Strict mass growth is preserved exactly by `weighted_biUnion_expands` with the
telescoping edge weight `sqrt (parent / child)`.  Endpoint bounds come from
the certified child-size bound `3c < 2^23 x` and band composition.
-/

namespace CollatzMoonshot.FrontA

/-! ## Chain plumbing -/

/-- Prepend a value to an ancestor chain. -/
def consChain (v : ℕ) (g : ℕ → ℕ) : ℕ → ℕ :=
  fun i => if i = 0 then v else g (i - 1)

@[simp] theorem consChain_zero (v : ℕ) (g : ℕ → ℕ) : consChain v g 0 = v :=
  rfl

@[simp] theorem consChain_succ (v : ℕ) (g : ℕ → ℕ) (i : ℕ) :
    consChain v g (i + 1) = g i := by
  simp [consChain]

/-- Every strictly later chain entry is forward-reachable in positive time. -/
theorem chain_reachesValuePos {r : ℕ} {g : ℕ → ℕ}
    (he : ∀ i, i < r → ReusableOddBlockChild (g (i + 1)) (g i)) :
    ∀ i j, i < j → j ≤ r → ReachesValuePos (g i) (g j) := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base =>
      intro hjr
      exact (he i (by omega)).reachesValuePos
  | succ j hij ih =>
      intro hjr
      exact (ih (by omega)).trans (he j (by omega)).reachesValuePos

/-- Two odd-parent chains starting at the same value agree as far as both are
defined, by uniqueness of the odd parent of an odd-block child. -/
theorem chain_agree {r r' : ℕ} {g g' : ℕ → ℕ} (h0 : g 0 = g' 0)
    (hodd : ∀ i, i ≤ r → g i % 2 = 1) (hodd' : ∀ i, i ≤ r' → g' i % 2 = 1)
    (he : ∀ i, i < r → ReusableOddBlockChild (g (i + 1)) (g i))
    (he' : ∀ i, i < r' → ReusableOddBlockChild (g' (i + 1)) (g' i)) :
    ∀ i, i ≤ r → i ≤ r' → g i = g' i := by
  intro i
  induction i with
  | zero => intro _ _; exact h0
  | succ i ih =>
      intro hir hir'
      have hgi : g i = g' i := ih (by omega) (by omega)
      have h1 := he i (by omega)
      have h2 := he' i (by omega)
      rw [← hgi] at h2
      exact reusableOddBlockChild_parent_eq (hodd (i + 1) hir)
        (hodd' (i + 1) hir') h1 h2

/-- A reusable child of a parent above `1` cannot equal a value it is known to
dominate; in particular growing children are strictly larger and the `j = 1`
child of a parent `x ≥ 2` is strictly smaller. -/
theorem ReusableOddBlockChild.lt_of_le {x y : ℕ} (hx : 2 ≤ x)
    (h : ReusableOddBlockChild x y) (hxy : x ≤ y) : x < y := by
  obtain ⟨j, hj1, _, _, hblock⟩ := h
  rcases Nat.lt_or_ge j 2 with hj2 | hj2
  · have hj : j = 1 := by omega
    subst hj
    have hb : 3 * y + 1 = 2 * x := by simpa using hblock
    omega
  · have h4 : 2 ^ 2 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj2
    have h4x : 2 ^ 2 * x ≤ 2 ^ j * x := Nat.mul_le_mul_right x h4
    omega

/-! ## Band propagation across one reusable edge -/

/-- One reusable inverse edge below the working height extends a root band
witness: growing peaks are absorbed by the endpoint bound `3y < 2^23 H`, and
the shrinking `j = 1` peak `2x` is far below the `2^25 H` ceiling. -/
theorem reusable_band_step {d H x y : ℕ} (_hd : 1 ≤ d) (hdx : d ≤ x)
    (hxH : x ≤ H) (hdy : d ≤ y) (hbound : 3 * y < 2 ^ 23 * H)
    (h : ReusableOddBlockChild x y)
    (hband : ReachesInBand d (2 ^ 25 * H) x) :
    ReachesInBand d (2 ^ 25 * H) y := by
  obtain ⟨j, hj1, hyodd, hy3, hblock⟩ := h
  have hpow23 : (2 : ℕ) ^ 23 * H ≤ 2 ^ 25 * H :=
    Nat.mul_le_mul_right H (by norm_num)
  have hpow2 : 2 * H ≤ 2 ^ 25 * H := Nat.mul_le_mul_right H (by norm_num)
  rcases Nat.lt_or_ge j 2 with hj2 | hj2
  · have hj : j = 1 := by omega
    subst hj
    have hblock' : 3 * y + 1 = 2 * x := by simpa using hblock
    have hyx : y < x := by omega
    have hone : UnitOddBlockChildAtOne x y := ⟨hyodd, hy3, hyx, hblock'⟩
    have h1 := hone.reachesToInBand hdy
    have hY : 2 * x ≤ 2 ^ 25 * H := by omega
    exact reachesToInBand_trans h1 hband.toReachesToInBand hY le_rfl
  · have h4 : 2 ^ 2 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj2
    have h4x : 2 ^ 2 * x ≤ 2 ^ j * x := Nat.mul_le_mul_right x h4
    have hxy : x ≤ y := by omega
    have hup := reachesInBand_of_odd_block hyodd hxy hblock
    have hceil : 2 ^ j * x ≤ 2 ^ 25 * H := by omega
    have hup' := reachesInBand_mono_ceiling hceil hup
    have h1 := reachesToInBand_of_reachesInBand hdx hup'
    exact reachesToInBand_trans h1 hband.toReachesToInBand le_rfl le_rfl

/-! ## The frontier invariant -/

/-- An odd-parent ancestor chain of length exactly the creation round for low
values, recording oddness, the floor, the low ceiling on proper ancestors,
actual odd-block edges, and pairwise distinctness. -/
def StoppingChain (d H m v : ℕ) : Prop :=
  ∃ r : ℕ, ∃ g : ℕ → ℕ, r ≤ m ∧ (v ≤ H → r = m) ∧ g 0 = v ∧ g r = d ∧
    (∀ i, i ≤ r → g i % 2 = 1) ∧ (∀ i, i ≤ r → d ≤ g i) ∧
    (∀ i, 1 ≤ i → i ≤ r → g i ≤ H) ∧
    (∀ i, i < r → ReusableOddBlockChild (g (i + 1)) (g i)) ∧
    (∀ i j, i < j → j ≤ r → g i ≠ g j)

/-- The per-node frontier invariant. -/
def StoppingNode (d H m : ℕ) (s : NetHalfNode) : Prop :=
  InHeightState d s.1 s.2 ∧ s.2 % 2 = 1 ∧ ¬3 ∣ s.2 ∧ s.2 < 2 ^ 23 * H ∧
    ReachesInBand d (2 ^ 25 * H) s.2 ∧ StoppingChain d H m s.2

/-- The full frontier invariant at round `m`: value injectivity, per-node
state data, and strict telescoping mass above the root potential. -/
def StoppingFront (d H m : ℕ) (F : Finset NetHalfNode) : Prop :=
  NetHalfValuesInjective F ∧ (∀ s ∈ F, StoppingNode d H m s) ∧
    (netHalfStatePotential false d : ℝ) <
      ∑ s ∈ F, netHalfEdgeWeight d s.2 * netHalfStatePotential s.1 s.2

/-- The chain of a low value at round `m` consists of `m` pairwise-distinct
values in `[d, H]`, so the round index is absolutely bounded. -/
theorem StoppingChain.round_add_le {d H m v : ℕ} (hdH : d ≤ H) (hvH : v ≤ H)
    (h : StoppingChain d H m v) : m + d ≤ H + 1 := by
  obtain ⟨r, g, hrm, hlow, hg0, hgr, hodd, hge, hleH, hedge, hne⟩ := h
  have hrm' : r = m := hlow hvH
  subst hrm'
  have hsub : (Finset.range r).image (fun i => g (i + 1)) ⊆
      Finset.Icc d H := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    have hi' : i + 1 ≤ r := Finset.mem_range.mp hi
    exact Finset.mem_Icc.mpr ⟨hge (i + 1) hi', hleH (i + 1) (by omega) hi'⟩
  have hinj : Set.InjOn (fun i => g (i + 1)) (Finset.range r) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    by_contra hne'
    rcases Nat.lt_or_ge i j with hlt | hge'
    · exact hne (i + 1) (j + 1) (by omega) (by omega) hij
    · exact hne (j + 1) (i + 1) (by omega) (by omega) hij.symm
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_range, Nat.card_Icc]
    at hcard
  omega

/-- The round-`1` frontier: the certified child set of the root itself. -/
theorem stoppingFront_init {d H : ℕ} (hd : 2 ≤ d) (hdodd : d % 2 = 1)
    (hd3 : ¬3 ∣ d) (hdH : d ≤ H) : ∃ F, StoppingFront d H 1 F := by
  obtain ⟨C, hCne, hCinj, hCchild, hCbound, hCmass⟩ :=
    exists_netHalfChildFinset (d := d) false hd hd3 ⟨le_rfl, by simp⟩
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
  have hdc : d ≤ c.2 := hchild.2.1
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
theorem stoppingFront_step {d H m : ℕ} (hd : 2 ≤ d) (_hdH : d ≤ H)
    {F : Finset NetHalfNode} (hF : StoppingFront d H m F)
    (hL : (F.filter fun s => s.2 ≤ H).Nonempty) :
    (∃ n, d ≤ n ∧ OnCycle n) ∨ ∃ F', StoppingFront d H (m + 1) F' := by
  classical
  obtain ⟨hinj, hnode, hmass⟩ := hF
  set L := F.filter (fun s => s.2 ≤ H) with hLdef
  set E := F.filter (fun s => ¬s.2 ≤ H) with hEdef
  -- certified child sets for every low node
  have hcc : ∀ s : NetHalfNode, s ∈ F → s.2 ≤ H →
      ∃ C : Finset NetHalfNode, C.Nonempty ∧ NetHalfValuesInjective C ∧
        (∀ c ∈ C, NetHalfChildAt d s c) ∧
        (∀ c ∈ C, 3 * c.2 < 2 ^ 23 * s.2) ∧
        (netHalfStatePotential s.1 s.2 : ℝ) <
          ∑ c ∈ C, netHalfEdgeWeight s.2 c.2 *
            netHalfStatePotential c.1 c.2 := by
    intro s hs _
    obtain ⟨hstate, _, h3, _, _, _⟩ := hnode s hs
    have hx2 : 2 ≤ s.2 := le_trans hd hstate.1
    exact exists_netHalfChildFinset s.1 hx2 h3 hstate
  choose! Cf hCne hCinj hCchild hCbound hCmass using hcc
  -- ancestor chains for every frontier node
  have hch : ∀ s : NetHalfNode, s ∈ F →
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
    have hdc : d ≤ c.2 := hchild.2.1
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
        have hdc : d ≤ c.2 := hchild.2.1
        have hds : d ≤ s.2 := (hnode s hsF).1.1
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
        (fun s => netHalfEdgeWeight d s.2)
        (fun s => (netHalfStatePotential s.1 s.2 : ℝ))
        (fun s c => netHalfEdgeWeight s.2 c.2)
        hdisj
        (by
          intro s hs
          have hds : d ≤ s.2 := (hnode s ((Finset.mem_filter.mp hs).1)).1.1
          unfold netHalfEdgeWeight
          apply Real.sqrt_pos.mpr
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
          have hds : d ≤ s.2 := (hnode s hsF).1.1
          have hdc : d ≤ c.2 := (hCchild s hsF hsH c hc).2.1
          exact netHalfEdgeWeight_mul (by omega) (by omega))
      have hEdisj : Disjoint E (L.biUnion Cf) := by
        rw [Finset.disjoint_left]
        intro c hcE hcB
        obtain ⟨s, hsL, hcC⟩ := Finset.mem_biUnion.mp hcB
        exact (hcol s hsL c hcC).2 c ((Finset.mem_filter.mp hcE).1) rfl
      have hsplit :
          (∑ s ∈ F, netHalfEdgeWeight d s.2 *
              netHalfStatePotential s.1 s.2) =
            (∑ s ∈ L, netHalfEdgeWeight d s.2 *
              netHalfStatePotential s.1 s.2) +
            ∑ s ∈ E, netHalfEdgeWeight d s.2 *
              netHalfStatePotential s.1 s.2 := by
        rw [hLdef, hEdef,
          Finset.sum_filter_add_sum_filter_not F (fun s => s.2 ≤ H)]
      calc
        (netHalfStatePotential false d : ℝ) <
            ∑ s ∈ F, netHalfEdgeWeight d s.2 *
              netHalfStatePotential s.1 s.2 := hmass
        _ = (∑ s ∈ L, netHalfEdgeWeight d s.2 *
              netHalfStatePotential s.1 s.2) +
            ∑ s ∈ E, netHalfEdgeWeight d s.2 *
              netHalfStatePotential s.1 s.2 := hsplit
        _ < (∑ s ∈ L.biUnion Cf, netHalfEdgeWeight d s.2 *
              netHalfStatePotential s.1 s.2) +
            ∑ s ∈ E, netHalfEdgeWeight d s.2 *
              netHalfStatePotential s.1 s.2 := by
              exact add_lt_add_of_lt_of_le hexp le_rfl
        _ = ∑ s ∈ E ∪ L.biUnion Cf, netHalfEdgeWeight d s.2 *
              netHalfStatePotential s.1 s.2 := by
              rw [Finset.sum_union hEdisj]
              ring

/-- A frontier with no remaining low node is exactly the pinned stopping
frontier. -/
theorem stoppingFrontier_of_no_low {d H m : ℕ}
    {F : Finset NetHalfNode} (hF : StoppingFront d H m F)
    (hL : ¬(F.filter fun s => s.2 ≤ H).Nonempty) :
    NetHalfStoppingFrontier d H F := by
  obtain ⟨hinj, hnode, hmass⟩ := hF
  refine ⟨hinj, hmass, ?_⟩
  intro s hs
  have hsH : ¬s.2 ≤ H := fun h => hL ⟨s, Finset.mem_filter.mpr ⟨hs, h⟩⟩
  exact ⟨by omega, (hnode s hs).2.2.2.1, (hnode s hs).2.2.2.2.1⟩

/-- **The recursive stopping-line theorem.**  Every odd reusable root either
exposes a positive Collatz cycle at or above its own floor, or carries a
finite first-exit frontier with the certified square-root telescoping mass.
The fuel `H + 1` suffices because every expansion round lengthens all live
ancestor chains, and a low chain is a set of distinct values in `[d, H]`. -/
theorem netHalfRepeatOrStoppingGrowth : NetHalfRepeatOrStoppingGrowth := by
  intro d H hd hdodd hd3 hdH
  obtain ⟨F₁, hF₁⟩ := stoppingFront_init hd hdodd hd3 hdH
  suffices h : ∀ k m (F : Finset NetHalfNode), StoppingFront d H m F →
      H + 2 ≤ m + k →
      (∃ n, d ≤ n ∧ OnCycle n) ∨
        ∃ S : Finset (Bool × ℕ), NetHalfStoppingFrontier d H S by
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
      · exact Or.inr ⟨F, stoppingFrontier_of_no_low hF hL⟩
  | succ k ih =>
      intro m F hF hm
      by_cases hL : (F.filter fun s => s.2 ≤ H).Nonempty
      · rcases stoppingFront_step hd hdH hF hL with hcyc | ⟨F', hF'⟩
        · exact Or.inl hcyc
        · exact ih (m + 1) F' hF' (by omega)
      · exact Or.inr ⟨F, stoppingFrontier_of_no_low hF hL⟩

end CollatzMoonshot.FrontA
