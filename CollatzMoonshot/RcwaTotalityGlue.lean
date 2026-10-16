/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.RcwaOrbitCount

/-!
# Totality family, layer 1: an increment chain glued into a machine

The totality family `e ↦ F e` of `RcwaOrbitCount.TotalityFamily` is one fixed machine plus an
`e`-dependent chain of increments.  This file is the generic gluing layer (research note
`undec-lemma` §7-§8; kickoff `KICKOFF-2026-10-16-totality.md`).

1. **The chain.**  For a counter machine `U` on states `Q`, a state `hole` that no rule leaves and
   a state `back` that no rule enters, `glue U hole back i L` is `U` on the states `Q ⊕ Fin L`
   together with the chain `hole → 0 → 1 → ⋯ → L − 1 → back`, each link an increment of counter
   `i` (`L + 1` increments in all).  So a pass through the chain adds `L + 1` to counter `i`.
2. **Gluing commutes with the history wrapper**, for everything the compile needs.  The chain is
   glued *after* wrapping, at the boundary states `bnd hole → … → bnd back`, so it is not
   history-wrapped and the wrapper's labels stay those of the fixed `U`:
   * the glued wrapper is deterministic and reversible (`glueH_det`, `glueH_rev`);
   * its reverse is mortal (`glueH_revMortal`): the potential `(L + 2) · hist + position` rises
     along every boundary-to-boundary macro step (a wrapper macro step raises `hist`, a chain step
     raises the position);
   * it is mortal iff the glued `U` is (`glueH_mortal_iff`): Lemma M forward for garbage, and the
     history simulation for the converse.

So the `e`-dependence never passes through `histWrap`; `RcwaTotalityCompile` handles `godel` and
`double`.
-/

namespace CollatzMoonshot.CounterMachine

/-- Relabel the states of a quadruple. -/
def Quad.mapQ {Q Q' ι : Type*} (f : Q → Q') (ρ : Quad Q ι) : Quad Q' ι :=
  ⟨f ρ.src, ρ.op, f ρ.dst⟩

/-- Relabel the states of a machine: the images of its rules. -/
def CM.mapQ {Q Q' ι : Type*} (f : Q → Q') (M : CM Q ι) : CM Q' ι :=
  {ρ' | ∃ ρ ∈ M, ρ' = ρ.mapQ f}

end CollatzMoonshot.CounterMachine

namespace CollatzMoonshot.RcwaTotality

open CollatzMoonshot.CounterMachine CollatzMoonshot.RcwaHalting
open CollatzMoonshot.RcwaOrbitCount (Mortal)

/-! ## 1. The chain -/

section Glue

variable {Q ι : Type*}

/-- The first chain state: `0`, or `back` when the chain is empty. -/
def chainFirst (back : Q) (L : ℕ) : Q ⊕ Fin L :=
  if h : 0 < L then .inr ⟨0, h⟩ else .inl back

/-- The successor of chain state `k`: `k + 1`, or `back` after the last. -/
def chainNext (back : Q) {L : ℕ} (k : Fin L) : Q ⊕ Fin L :=
  if h : k.val + 1 < L then .inr ⟨k.val + 1, h⟩ else .inl back

/-- The chain `hole → 0 → ⋯ → L − 1 → back`, `L + 1` increments of counter `i`. -/
def chain (hole back : Q) (i : ι) (L : ℕ) : CM (Q ⊕ Fin L) ι :=
  {ρ | ρ = ⟨.inl hole, .inc i, chainFirst back L⟩ ∨
    ∃ k : Fin L, ρ = ⟨.inr k, .inc i, chainNext back k⟩}

/-- `U` with the chain glued from `hole` to `back`. -/
def glue (U : CM Q ι) (hole back : Q) (i : ι) (L : ℕ) : CM (Q ⊕ Fin L) ι :=
  U.mapQ Sum.inl ∪ chain hole back i L

variable {U : CM Q ι} {hole back : Q} {i : ι} {L : ℕ}

/-- A step of `U` is a step of the glued machine. -/
theorem glue_step_inl {q q' : Q} {v v' : ι → ℕ} (h : U.Step (q, v) (q', v')) :
    (glue U hole back i L).Step (.inl q, v) (.inl q', v') := by
  obtain ⟨ρ, hρ, h1, h2, h3⟩ := h
  exact ⟨ρ.mapQ Sum.inl, Or.inl ⟨ρ, hρ, rfl⟩, congrArg Sum.inl h1, congrArg Sum.inl h2, h3⟩

/-- Off `hole`, a step of the glued machine from a state of `U` is a step of `U`. -/
theorem glue_step_inl_inv {q : Q} {v : ι → ℕ} {d : Cfg (Q ⊕ Fin L) ι} (hq : q ≠ hole)
    (h : (glue U hole back i L).Step (.inl q, v) d) :
    ∃ q', d.1 = .inl q' ∧ U.Step (q, v) (q', d.2) := by
  obtain ⟨r, hr, h1, h2, h3⟩ := h
  rcases hr with ⟨ρ, hρ, rfl⟩ | hr
  · exact ⟨ρ.dst, h2, ρ, hρ, Sum.inl_injective h1, rfl, h3⟩
  · exfalso
    rcases hr with rfl | ⟨k, rfl⟩
    · exact hq (Sum.inl_injective h1)
    · cases h1

theorem act_inc_update [DecidableEq ι] (v : ι → ℕ) (i : ι) :
    (Op.inc i).Act v (Function.update v i (v i + 1)) :=
  ⟨by simp, fun j hj => by simp [hj]⟩

/-- The plug: `hole` to the first chain state. -/
theorem glue_step_plug [DecidableEq ι] (v : ι → ℕ) :
    (glue U hole back i L).Step (.inl hole, v)
      (chainFirst back L, Function.update v i (v i + 1)) :=
  ⟨_, Or.inr (Or.inl rfl), rfl, rfl, act_inc_update v i⟩

/-- A link: chain state `k` to its successor. -/
theorem glue_step_link [DecidableEq ι] (k : Fin L) (v : ι → ℕ) :
    (glue U hole back i L).Step (.inr k, v)
      (chainNext back k, Function.update v i (v i + 1)) :=
  ⟨_, Or.inr (Or.inr ⟨k, rfl⟩), rfl, rfl, act_inc_update v i⟩

theorem update_add_add [DecidableEq ι] (v : ι → ℕ) (i : ι) (a b : ℕ) :
    Function.update (Function.update v i (v i + a)) i
      (Function.update v i (v i + a) i + b) = Function.update v i (v i + (a + b)) := by
  rw [Function.update_idem, Function.update_self, Nat.add_assoc]

/-- From chain state `k` the glued machine reaches `back` with `L − k` added to counter `i`. -/
theorem glue_chain_reaches_of_inr [DecidableEq ι] (k : Fin L) (v : ι → ℕ) :
    Relation.TransGen (glue U hole back i L).Step (.inr k, v)
      (.inl back, Function.update v i (v i + (L - k.val))) := by
  suffices key : ∀ n (k : ℕ) (hk : k < L) (v : ι → ℕ), L - k = n →
      Relation.TransGen (glue U hole back i L).Step (.inr ⟨k, hk⟩, v)
        (.inl back, Function.update v i (v i + n)) from key _ k.val k.isLt v rfl
  intro n
  induction n with
  | zero => intro k hk v h; omega
  | succ n ih =>
    intro k hk v h
    have h1 := glue_step_link (U := U) (hole := hole) (back := back) (i := i) ⟨k, hk⟩ v
    by_cases hk1 : k + 1 < L
    · rw [chainNext, dif_pos hk1] at h1
      have h2 := ih (k + 1) hk1 (Function.update v i (v i + 1)) (by omega)
      rw [update_add_add, show 1 + n = n + 1 by omega] at h2
      exact Relation.TransGen.head h1 h2
    · rw [chainNext, dif_neg hk1] at h1
      obtain rfl : n = 0 := by omega
      exact .single h1

/-- **The chain adds `L + 1`.**  From `hole` the glued machine reaches `back` with `L + 1` added
to counter `i`. -/
theorem glue_chain_reaches [DecidableEq ι] (v : ι → ℕ) :
    Relation.TransGen (glue U hole back i L).Step (.inl hole, v)
      (.inl back, Function.update v i (v i + (L + 1))) := by
  by_cases hL : 0 < L
  · have h1 := glue_step_plug (U := U) (hole := hole) (back := back) (i := i) (L := L) v
    rw [chainFirst, dif_pos hL] at h1
    have h2 := glue_chain_reaches_of_inr (U := U) (hole := hole) (back := back) (i := i)
      ⟨0, hL⟩
      (Function.update v i (v i + 1))
    rw [update_add_add] at h2
    simpa [Nat.add_comm 1 L] using Relation.TransGen.head h1 h2
  · obtain rfl : L = 0 := by omega
    have h1 := glue_step_plug (U := U) (hole := hole) (back := back) (i := i) (L := 0) v
    rw [chainFirst, dif_neg (lt_irrefl 0)] at h1
    exact .single h1

/-- No configuration on the chain (`hole` included) is a halting ID. -/
theorem glue_not_stuck_chain {q : Q ⊕ Fin L} (hq : q = .inl hole ∨ ∃ k : Fin L, q = .inr k)
    (v : ι → ℕ) : ¬ (glue U hole back i L).Stuck (q, v) := by
  classical
  intro hs
  rcases hq with rfl | ⟨k, rfl⟩
  · exact hs _ (glue_step_plug v)
  · exact hs _ (glue_step_link k v)

/-- **Gluing keeps determinism** when no rule of `U` leaves `hole`. -/
theorem glue_det (hU : U.Det) (hhole : ∀ ρ ∈ U, ρ.src ≠ hole) :
    (glue U hole back i L).Det := by
  rintro r (⟨ρ, hρ, rfl⟩ | hr) r' (⟨ρ', hρ', rfl⟩ | hr') hne hsrc
  · exact hU ρ hρ ρ' hρ' (fun h => hne (h ▸ rfl)) (Sum.inl_injective hsrc)
  · exfalso
    rcases hr' with rfl | ⟨k, rfl⟩
    · exact hhole ρ hρ (Sum.inl_injective hsrc)
    · cases hsrc
  · exfalso
    rcases hr with rfl | ⟨k, rfl⟩
    · exact hhole ρ' hρ' (Sum.inl_injective hsrc).symm
    · cases hsrc
  · exfalso
    rcases hr with rfl | ⟨k, rfl⟩ <;> rcases hr' with rfl | ⟨k', rfl⟩
    · exact hne rfl
    · cases hsrc
    · cases hsrc
    · cases Sum.inr_injective hsrc
      exact hne rfl

/-- **Gluing keeps reversibility** when no rule of `U` enters `back`. -/
theorem glue_rev (hU : U.Rev) (hback : U.NormalAt back) : (glue U hole back i L).Rev := by
  have hF : ∀ q, chainFirst back L = .inl q → q = back := by
    intro q h; unfold chainFirst at h; split_ifs at h; exact (Sum.inl_injective h).symm
  have hN : ∀ (k : Fin L) q, chainNext back k = .inl q → q = back := by
    intro k q h; unfold chainNext at h; split_ifs at h; exact (Sum.inl_injective h).symm
  have hFN : ∀ k : Fin L, chainFirst back L ≠ chainNext back k := by
    intro k h
    unfold chainFirst chainNext at h
    have := k.isLt
    split_ifs at h with h1 h2 h2 <;> first | omega | cases h
  have hNN : ∀ k k' : Fin L, chainNext back k = chainNext back k' → k = k' := by
    intro k k' h
    unfold chainNext at h
    have := k.isLt; have := k'.isLt
    split_ifs at h with h1 h2 h2 <;>
      first | exact Fin.ext (by omega) | cases h |
        exact Fin.ext (by have := congrArg Fin.val (Sum.inr_injective h); simpa using this)
  rintro r (⟨ρ, hρ, rfl⟩ | hr) r' (⟨ρ', hρ', rfl⟩ | hr') hne hdst
  · exact hU ρ hρ ρ' hρ' (fun h => hne (h ▸ rfl)) (Sum.inl_injective hdst)
  · exfalso
    rcases hr' with rfl | ⟨k, rfl⟩
    · exact hback ρ hρ (hF _ hdst.symm)
    · exact hback ρ hρ (hN _ _ hdst.symm)
  · exfalso
    rcases hr with rfl | ⟨k, rfl⟩
    · exact hback ρ' hρ' (hF _ hdst)
    · exact hback ρ' hρ' (hN _ _ hdst)
  · exfalso
    rcases hr with rfl | ⟨k, rfl⟩ <;> rcases hr' with rfl | ⟨k', rfl⟩
    · exact hne rfl
    · exact hFN k' hdst
    · exact hFN k hdst.symm
    · cases hNN k k' hdst
      exact hne rfl

/-- (S1) passes to the glued machine, with the chain states and the boundary of `U` as
boundary. -/
theorem glue_lapsMixed [DecidableEq ι] {B : Set Q} (h : LapsMixed U B) (hhole : hole ∈ B) :
    LapsMixed (glue U hole back i L) (Sum.inl '' B ∪ Set.range Sum.inr) := by
  intro ρ m hm hmem hoff hchain hclose
  -- every rule of the walk is a mapped rule of `U`
  have hex : ∀ j, ∃ σ : Quad Q ι, j < m → σ ∈ U ∧ ρ j = σ.mapQ Sum.inl := by
    intro j
    by_cases hj : j < m
    · rcases hmem j hj with ⟨σ, hσ, h⟩ | hc
      · exact ⟨σ, fun _ => ⟨hσ, h⟩⟩
      · exfalso
        apply hoff j hj
        rcases hc with h | ⟨k, h⟩ <;> rw [h]
        · exact Or.inl ⟨hole, hhole, rfl⟩
        · exact Or.inr ⟨k, rfl⟩
    · obtain ⟨σ, -, -⟩ | hc := hmem 0 hm
      · exact ⟨σ, fun h => absurd h hj⟩
      · exfalso
        apply hoff 0 hm
        rcases hc with h | ⟨k, h⟩ <;> rw [h]
        · exact Or.inl ⟨hole, hhole, rfl⟩
        · exact Or.inr ⟨k, rfl⟩
  choose σ hσ using hex
  have hop : ∀ j, j < m → (ρ j).op = (σ j).op := fun j hj => by rw [(hσ j hj).2]; rfl
  have hsum : ∀ c, ∑ j ∈ Finset.range m, (ρ j).op.delta c =
      ∑ j ∈ Finset.range m, (σ j).op.delta c := fun c =>
    Finset.sum_congr rfl fun j hj => by rw [hop j (Finset.mem_range.1 hj)]
  simp only [hsum]
  refine h σ m hm (fun j hj => (hσ j hj).1) (fun j hj hB => hoff j hj ?_) (fun j hj => ?_) ?_
  · rw [(hσ j hj).2]; exact Or.inl ⟨_, hB, rfl⟩
  · have := hchain j hj
    rw [(hσ j (by omega)).2, (hσ (j + 1) hj).2] at this
    exact Sum.inl_injective this
  · have := hclose
    rw [(hσ _ (by omega)).2, (hσ 0 hm).2] at this
    exact Sum.inl_injective this

/-- **Macro steps of the glued machine.**  A boundary-to-boundary macro step is a macro step of
`U` (on states of `U`) or a single chain step. -/
theorem glue_macroStep_cases {B : Set Q} (hhole : hole ∈ B) (hback : back ∈ B)
    {b b' : Cfg (Q ⊕ Fin L) ι}
    (hm : RcwaMachine.MacroStep (Sum.inl '' B ∪ Set.range Sum.inr)
      (glue U hole back i L).Step b b') :
    (∃ c c' : Cfg Q ι, b = (.inl c.1, c.2) ∧ b' = (.inl c'.1, c'.2) ∧
      RcwaMachine.MacroStep B U.Step c c') ∨ (chain hole back i L).Step b b' := by
  obtain ⟨hb, hb', x, n, hn, hx0, hxn, hstep, hxoff⟩ := hm
  have hoffB : ∀ j, 0 < j → j < n → ∃ q, (x j).1 = .inl q ∧ q ∉ B := by
    intro j h1 h2
    have := hxoff j h1 h2
    rcases hx : (x j).1 with q | k
    · exact ⟨q, rfl, fun hq => this (hx ▸ Or.inl ⟨q, hq, rfl⟩)⟩
    · exact absurd (hx ▸ Or.inr ⟨k, rfl⟩) this
  have hBd : ∀ q, Sum.inl q ∈ (Sum.inl '' B ∪ Set.range Sum.inr : Set (Q ⊕ Fin L)) → q ∈ B := by
    rintro q (⟨q', hq', h⟩ | ⟨k, h⟩)
    · exact Sum.inl_injective h ▸ hq'
    · cases h
  obtain ⟨r, hr, h1, h2, h3⟩ := hstep 0 hn
  rcases hr with ⟨ρ, hρ, rfl⟩ | hr
  · -- a mapped first step: the whole run is a run of `U`
    left
    have hinl : ∀ j, ∃ q : Q, j ≤ n → (x j).1 = .inl q := by
      intro j
      by_cases hj : j ≤ n
      · rcases Nat.eq_zero_or_pos j with rfl | hj0
        · exact ⟨ρ.src, fun _ => h1⟩
        rcases Nat.lt_or_ge j n with hjn | hjn
        · obtain ⟨q, hq, -⟩ := hoffB j hj0 hjn
          exact ⟨q, fun _ => hq⟩
        · rw [show j = n by omega]
          by_cases hn1 : n = 1
          · subst hn1; exact ⟨ρ.dst, fun _ => h2⟩
          · obtain ⟨q, hq, hqB⟩ := hoffB (n - 1) (by omega) (by omega)
            have hs := hstep (n - 1) (by omega)
            rw [show n - 1 + 1 = n by omega] at hs
            rw [show x (n - 1) = (.inl q, (x (n - 1)).2) from Prod.ext hq rfl] at hs
            obtain ⟨q', hq', -⟩ := glue_step_inl_inv
              (fun h => hqB (by rw [h]; exact hhole)) hs
            exact ⟨q', fun _ => hq'⟩
      · exact ⟨ρ.src, fun h => absurd h hj⟩
    choose f hf using hinl
    have hx : ∀ j, j ≤ n → x j = (.inl (f j), (x j).2) := fun j hj => Prod.ext (hf j hj) rfl
    refine ⟨(f 0, (x 0).2), (f n, (x n).2), ?_, ?_, ?_⟩
    · rw [← hx0]; exact hx 0 (Nat.zero_le _)
    · rw [← hxn]; exact hx n le_rfl
    refine ⟨hBd _ (by rw [← hf 0 (Nat.zero_le _), hx0]; exact hb),
      hBd _ (by rw [← hf n le_rfl, hxn]; exact hb'),
      fun j => (f j, (x j).2), n, hn, rfl, rfl, fun j hj => ?_, fun j hj0 hjn => ?_⟩
    · have hs := hstep j hj
      rw [hx j hj.le, hx (j + 1) hj] at hs
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · refine ⟨ρ, hρ, Sum.inl_injective (β := Fin L) ?_,
          Sum.inl_injective (β := Fin L) ?_, ?_⟩
        · rw [← hf 0 (Nat.zero_le _)]; exact h1
        · rw [← hf 1 hj]; exact h2
        · exact h3
      · obtain ⟨q, hq, hqB⟩ := hoffB j hj0 hj
        have hfq : f j = q := Sum.inl_injective ((hf j hj.le).symm.trans hq)
        obtain ⟨q', hq', hst⟩ := glue_step_inl_inv
          (fun h => hqB (by rw [← hfq, h]; exact hhole)) hs
        cases Sum.inl_injective hq'
        exact hst
    · obtain ⟨q, hq, hqB⟩ := hoffB j hj0 hjn
      exact fun h => hqB (Sum.inl_injective ((hf j hjn.le).symm.trans hq) ▸ h)
  · -- a chain first step lands on the boundary, so the macro step is that one step
    right
    have hdst : (x 1).1 ∈ (Sum.inl '' B ∪ Set.range Sum.inr : Set (Q ⊕ Fin L)) := by
      have hF : ∀ s : Q ⊕ Fin L, (s = chainFirst back L ∨ ∃ k : Fin L, s = chainNext back k) →
          s ∈ (Sum.inl '' B ∪ Set.range Sum.inr : Set (Q ⊕ Fin L)) := by
        rintro s (rfl | ⟨k, rfl⟩)
        · unfold chainFirst; split_ifs
          · exact Or.inr ⟨_, rfl⟩
          · exact Or.inl ⟨back, hback, rfl⟩
        · unfold chainNext; split_ifs
          · exact Or.inr ⟨_, rfl⟩
          · exact Or.inl ⟨back, hback, rfl⟩
      rw [h2]
      rcases hr with rfl | ⟨k, rfl⟩
      · exact hF _ (Or.inl rfl)
      · exact hF _ (Or.inr ⟨k, rfl⟩)
    have hn1 : n = 1 := by
      by_contra hn1
      exact hxoff 1 one_pos (by omega) hdst
    subst hn1
    rw [← hx0, ← hxn]
    exact ⟨r, hr, h1, h2, h3⟩

end Glue

/-! ## 2. Gluing after the history wrapper -/

section GlueHist

variable {Q ι : Type*} {K : ℕ} {U : CM Q ι} {lab : Quad Q ι → Fin K} {hole back : Q} {i : ι}
  {L : ℕ}

/-- No rule of the wrapper leaves `bnd hole` when no rule of `U` leaves `hole`. -/
theorem histWrap_src_ne_bnd (hhole : ∀ ρ ∈ U, ρ.src ≠ hole) :
    ∀ r ∈ histWrap U lab, r.src ≠ .bnd hole := by
  intro r hr h
  cases hr <;> simp only [HState.bnd.injEq, reduceCtorEq] at h
  exact hhole _ ‹_› h

/-- The glued wrapper is deterministic. -/
theorem glueH_det (hU : U.Det) (hhole : ∀ ρ ∈ U, ρ.src ≠ hole) :
    (glue (histWrap U lab) (.bnd hole) (.bnd back) (.val i) L).Det :=
  glue_det (histWrap_det hU) (histWrap_src_ne_bnd hhole)

/-- The glued wrapper is reversible. -/
theorem glueH_rev (hU : U.Det) (hlab : ∀ ρ ∈ U, 1 ≤ (lab ρ).val)
    (hinj : ∀ ρ ∈ U, ∀ ρ' ∈ U, lab ρ = lab ρ' → ρ = ρ') (hback : U.NormalAt back) :
    (glue (histWrap U lab) (.bnd hole) (.bnd back) (.val i) L).Rev :=
  glue_rev (histWrap_rev hU hlab hinj) (histWrap_normalAt hback)

/-- The chain's first state, lifted to the wrapper. -/
theorem chainFirst_bnd (back : Q) (L : ℕ) :
    chainFirst (HState.bnd (ι := ι) (K := K) back) L =
      Sum.map HState.bnd id (chainFirst back L) := by
  unfold chainFirst; split_ifs <;> rfl

/-- The chain's next state, lifted to the wrapper. -/
theorem chainNext_bnd (back : Q) {L : ℕ} (k : Fin L) :
    chainNext (HState.bnd (ι := ι) (K := K) back) k = Sum.map HState.bnd id (chainNext back k) := by
  unfold chainNext; split_ifs <;> rfl

/-- The position used by the potential of `glueH_revMortal`. -/
def gpos [DecidableEq Q] (hole : Q) (L : ℕ) : HState Q ι K ⊕ Fin L → ℕ
  | .inl (.bnd s) => if s = hole then 0 else L + 1
  | .inl _ => 0
  | .inr k => k.val + 1

theorem gpos_le [DecidableEq Q] (s : HState Q ι K ⊕ Fin L) : gpos hole L s ≤ L + 1 := by
  rcases s with s | k
  · cases s <;> simp only [gpos] <;> first | omega | (split_ifs <;> omega)
  · simp only [gpos]; omega

/-- **The glued wrapper has a mortal reverse.**  Along every boundary macro step the potential
`(L + 2) · hist + pos` rises (`pos` is `0` at `bnd hole`, `k + 1` at chain state `k`, `L + 1` at
every other `bnd s`): a wrapper macro step raises `hist` (`histWrap_macro_hist`), a chain step
keeps `hist` and raises `pos`. -/
theorem glueH_revMortal [Fintype Q] [Fintype ι] [DecidableEq Q] [DecidableEq ι] (hU : U.Det)
    (hlab : ∀ ρ ∈ U, 1 ≤ (lab ρ).val) (hhb : hole ≠ back) :
    (glue (histWrap U lab) (.bnd hole) (.bnd back) (.val i) L).RevMortal := by
  refine revMortal_of_macro (glue_lapsMixed histWrap_lapsMixed ⟨hole, rfl⟩) ?_
  rintro ⟨b, hb⟩
  let Φ : Cfg (HState Q ι K ⊕ Fin L) (HCtr ι) → ℕ :=
    fun c => (L + 2) * c.2 .hist + gpos hole L c.1
  have hrise : ∀ n, Φ (b (n + 1)) < Φ (b n) := by
    intro n
    rcases glue_macroStep_cases (B := Set.range HState.bnd) ⟨hole, rfl⟩ ⟨back, rfl⟩ (hb n) with
      ⟨c, c', h1, h2, hm⟩ | hc
    · have hh := histWrap_macro_hist hU hlab hm
      have hp := gpos_le (hole := hole) (Sum.inl (β := Fin L) c.1)
      have hmul := Nat.mul_le_mul_left (L + 2) hh
      rw [Nat.mul_succ] at hmul
      simp only [Φ, h1, h2]
      omega
    · obtain ⟨r, hr, hs, hd, ha⟩ := hc
      have hhist := (map_act_inv (o := .inc i) (by rcases hr with rfl | ⟨k, rfl⟩ <;> exact ha)).2.1
      simp only [Φ, hhist]
      suffices gpos hole L (b (n + 1)).1 < gpos hole L (b n).1 by omega
      rcases hr with rfl | ⟨k, rfl⟩
      · rw [hs, hd, chainFirst_bnd]
        unfold chainFirst
        split_ifs <;> simp [gpos, Ne.symm hhb]
      · rw [hs, hd, chainNext_bnd]
        unfold chainNext
        split_ifs with hk
        · simp [gpos]
        · simp [gpos, Ne.symm hhb]
  have : ∀ n, Φ (b n) + n ≤ Φ (b 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => have := hrise n; omega
  have := this (Φ (b 0) + 1)
  omega

/-- A halting ID of `U` off `hole` is a halting ID of the glued machine. -/
theorem glue_stuck_of_stuck {Q ι : Type*} {U : CM Q ι} {hole back : Q} {i : ι} {L : ℕ} {q : Q}
    {v : ι → ℕ} (hq : q ≠ hole) (h : U.Stuck (q, v)) :
    (glue U hole back i L).Stuck (.inl q, v) := by
  intro d hd
  obtain ⟨q', -, hst⟩ := glue_step_inl_inv hq hd
  exact h _ hst

/-- `histWrap_halts_of_stuck`, with the halting ID located at `bnd s` or `act s`. -/
theorem histWrap_halts_of_stuck' {s : Q} {v : ι → ℕ} (hs : U.Stuck (s, v)) (h : ℕ) :
    ∃ d, (histWrap U lab).Reaches (.bnd s, hcfg v h) d ∧ (histWrap U lab).Stuck d ∧
      (d.1 = .bnd s ∨ d.1 = .act s) := by
  by_cases hex : ∃ ρ ∈ U, ρ.src = s
  · obtain ⟨ρ, hρ, rfl⟩ := hex
    refine ⟨(.act ρ.src, hcfg v h),
      .single ⟨_, .guard hρ, rfl, rfl, act_test _ _ (by simp [hcfg])⟩, ?_, Or.inr rfl⟩
    rintro d ⟨r, hr, h1, -, h3⟩
    cases hr <;> simp only [HState.act.injEq, reduceCtorEq] at h1
    rename_i ρ' hρ'
    exact hs (ρ'.dst, fun i => d.2 (.val i)) ⟨ρ', hρ', h1, rfl, (map_act_inv h3).1⟩
  · refine ⟨_, .refl, ?_, Or.inl rfl⟩
    rintro d ⟨r, hr, h1, -, -⟩
    cases hr <;> simp only [HState.bnd.injEq, reduceCtorEq] at h1
    exact hex ⟨_, ‹_›, h1.symm⟩

/-- **Mortality through the glued wrapper.**  The glued wrapper halts from every configuration
iff the glued `U` does. -/
theorem glueH_mortal_iff [Fintype Q] [Fintype ι] [DecidableEq ι] (hU : U.Det)
    (hhole : ∀ ρ ∈ U, ρ.src ≠ hole) :
    Mortal (glue (histWrap U lab) (.bnd hole) (.bnd back) (.val i) L) ↔
      Mortal (glue U hole back i L) := by
  classical
  have hdetA : (glue U hole back i L).Det := glue_det hU hhole
  have hdetB : (glue (histWrap U lab) (.bnd hole) (.bnd back) (.val i) L).Det :=
    glue_det (histWrap_det hU) (histWrap_src_ne_bnd hhole)
  let lift : Q ⊕ Fin L → HState Q ι K ⊕ Fin L := Sum.map HState.bnd id
  have hlift : Function.Injective lift :=
    Sum.map_injective.2 ⟨fun _ _ h => HState.bnd.inj h, Function.injective_id⟩
  let inlC : Cfg (HState Q ι K) (HCtr ι) → Cfg (HState Q ι K ⊕ Fin L) (HCtr ι) :=
    fun c => (.inl c.1, c.2)
  constructor
  · -- honest: the history simulation
    intro hB c
    have key := CM.halts_iff_of_sim (M := glue U hole back i L) hdetB
      (fun c b => ∃ h, b = (lift c.1, hcfg c.2 h)) ?_ ?_ (c := c)
      (c' := (lift c.1, hcfg c.2 0)) ⟨0, rfl⟩
    · exact key.1 (hB _)
    · rintro c d b ⟨r, hr, hs, hd, hact⟩ ⟨h, rfl⟩
      rcases hr with ⟨ρ, hρ, rfl⟩ | hr
      · refine ⟨(lift d.1, hcfg d.2 (K * h + (lab ρ).val)), ?_, _, rfl⟩
        have hm := macroStep_transGen (histWrap_macro (lab := lab) hρ hact h)
        have e1 : lift c.1 = .inl (.bnd ρ.src) := by rw [hs]; rfl
        have e2 : lift d.1 = .inl (.bnd ρ.dst) := by rw [hd]; rfl
        rw [e1, e2]
        exact hm.lift inlC
          (fun c d h => glue_step_inl h)
      · have ha : (Op.inc (HCtr.val i)).Act (hcfg c.2 h) (hcfg d.2 h) := by
          rcases hr with rfl | ⟨k, rfl⟩ <;>
          · rw [hcfg_eq, hcfg_eq]; exact act_map (o := .inc i) hact h 0
        refine ⟨(lift d.1, hcfg d.2 h), .single ?_, h, rfl⟩
        rcases hr with rfl | ⟨k, rfl⟩
        · refine ⟨_, Or.inr (Or.inl rfl), ?_, ?_, ha⟩
          · simp only [lift, hs]; rfl
          · simp only [hd, chainFirst_bnd, lift]
        · refine ⟨_, Or.inr (Or.inr ⟨k, rfl⟩), ?_, ?_, ha⟩
          · simp only [lift, hs]; rfl
          · simp only [hd, chainNext_bnd, lift]
    · rintro ⟨q, v⟩ b hst ⟨h, rfl⟩
      rcases q with q | k
      · by_cases hq : q = hole
        · subst hq; exact absurd hst (glue_not_stuck_chain (Or.inl rfl) v)
        · have hU' : U.Stuck (q, v) := fun d hd => hst _ (glue_step_inl hd)
          obtain ⟨d, hr, hds, hd1⟩ := histWrap_halts_of_stuck' (lab := lab) hU' h
          refine ⟨((Sum.inl d.1 : HState Q ι K ⊕ Fin L), d.2),
            hr.lift inlC
              (fun a b h => glue_step_inl h), glue_stuck_of_stuck ?_ hds⟩
          rcases hd1 with e | e <;> rw [e] <;> simp [hq]
      · exact absurd hst (glue_not_stuck_chain (Or.inr ⟨k, rfl⟩) v)
  · -- garbage: an infinite run of the glued wrapper projects to one of the glued `U`
    intro hA c
    by_contra hnh
    have hfin : Finite (HState Q ι K ⊕ Fin L) := inferInstance
    obtain ⟨b, hb⟩ := RcwaOrbitCount.exists_macro_chain
      (glue_lapsMixed (B := Set.range HState.bnd) histWrap_lapsMixed ⟨hole, rfl⟩) hnh
    have hex : ∀ n, ∃ a : Q ⊕ Fin L, (b n).1 = lift a := by
      intro n
      rcases (hb n).1 with ⟨_, ⟨s, rfl⟩, h⟩ | ⟨k, h⟩
      · exact ⟨.inl s, h.symm⟩
      · exact ⟨.inr k, h.symm⟩
    choose a ha using hex
    let x : ℕ → Cfg (Q ⊕ Fin L) ι := fun n => (a n, fun j => (b n).2 (.val j))
    have hx : ∀ n, (glue U hole back i L).Step (x n) (x (n + 1)) := by
      intro n
      rcases glue_macroStep_cases (B := Set.range HState.bnd) ⟨hole, rfl⟩ ⟨back, rfl⟩ (hb n) with
        ⟨c, c', h1, h2, hm⟩ | hc
      · obtain ⟨s, s', hs, hs', hst⟩ := RcwaOrbitCount.histWrap_macro_sound hU hm
        have e1 : a n = .inl s := hlift (by rw [← ha, h1, hs]; rfl)
        have e2 : a (n + 1) = .inl s' := hlift (by rw [← ha, h2, hs']; rfl)
        simp only [x, e1, e2, h1, h2]
        exact glue_step_inl hst
      · obtain ⟨r, hr, hs, hd, hact⟩ := hc
        rcases hr with rfl | ⟨k, rfl⟩
        · have e1 : a n = .inl hole := hlift (by rw [← ha, hs]; rfl)
          have e2 : a (n + 1) = chainFirst back L := hlift (by rw [← ha, hd, chainFirst_bnd])
          refine ⟨_, Or.inr (Or.inl rfl), ?_, ?_, (map_act_inv (o := .inc i) hact).1⟩
          · simp only [x, e1]
          · simp only [x, e2]
        · obtain ⟨k', hk'⟩ : ∃ k', a n = .inr k' := ⟨k, hlift (by rw [← ha, hs]; rfl)⟩
          have hk : k' = k := by
            have := ha n; rw [hk', hs] at this; exact (Sum.inr_injective this).symm
          subst hk
          have e2 : a (n + 1) = chainNext back k' := hlift (by rw [← ha, hd, chainNext_bnd])
          refine ⟨_, Or.inr (Or.inr ⟨k', rfl⟩), ?_, ?_, (map_act_inv (o := .inc i) hact).1⟩
          · simp only [x, hk']
          · simp only [x, e2]
    exact CM.not_halts_of_forever hdetA x hx (hA _)

end GlueHist

end CollatzMoonshot.RcwaTotality
