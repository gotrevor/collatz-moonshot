/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.RcwaHalting

/-!
# Theorem C, orbit count: one orbit iff the machine is mortal, otherwise infinitely many

The orbit-count half of Theorem C (research note `undec-lemma` §2, §8; `undec-r25` §6).  A valid
machine `M` (`RcwaSameOrbit.Machine.Valid`) gives the RCWA permutation `σ = sigmaPerm` of `ℤ`
with all slopes in `2^ℤ 3^ℤ`.  Its orbits are counted by `RcwaMachine.card_orbits`
(`1 + #divergent line sources`), and every machine configuration occurs at infinitely many engine
points (Lemma P junk), so the count is `1` or `ℵ₀`.

1. **Dichotomy.**  `σ` has one orbit iff every source of `M` halts (`SourcesHalt`), and otherwise
   infinitely many (`card_orbits_sigma_eq_one_iff`, `card_orbits_sigma_eq_aleph0_iff`); the same
   for the exact table `tableOf M` (`tableOf_orbits`).
2. **Mortality transfer.**  For every deterministic finite counter machine `U`, the compile
   `double (godel (histWrap U))` of `RcwaHalting` has all sources halting iff `U` halts from
   *every* configuration (`Mortal`).  Garbage is controlled by Lemma M forward
   (`RcwaMachine.immortal_iff_macro`): a non-halting run of a wrapped machine is an infinite
   chain of macro steps, each a step of the wrapped machine on decoded counters.  So
   `exists_table_iff_mortal`: an exact table whose permutation has one orbit iff `U` is mortal,
   infinitely many otherwise (hypothesis-free).
3. **Undecidability, conditional.**  `MortalityUndecidable` (deciding `SourcesHalt` on valid
   machines is not computable) gives that "one orbit" and "finitely many orbits" are not
   computable on exact bijective tables.
4. **Totality.**  `TotalityFamily` (a computable family of valid machines with
   `SourcesHalt (F e) ↔ φ_e total`; Lemma A of `undec-lemma`) gives Theorem C(1): a computable
   `e ↦ σ_e` with one orbit iff `φ_e` is total and infinitely many otherwise, and "one orbit" is
   neither r.e. nor co-r.e. on exact bijective tables (`Total` is neither, from Mathlib's halting
   problem).
-/

namespace CollatzMoonshot.RcwaOrbitCount

open CollatzMoonshot.CounterMachine CollatzMoonshot.RcwaEngineGen CollatzMoonshot.RcwaHalting
open CollatzMoonshot.RcwaSameOrbit (Rule Machine IsSource IsSink Halts RcwaTable Good sigmaPerm
  tableOf decode)

/-! ## 0. Vocabulary -/

/-- `σ` has a single orbit. -/
def OneOrbit {β : Type*} (σ : Equiv.Perm β) : Prop :=
  ∀ a b : β, σ.SameCycle a b

/-- Every source of the guarded-rule machine `M` halts. -/
def SourcesHalt (M : Machine) : Prop :=
  ∀ c : RcwaSameOrbit.Cfg, IsSource M.rules c → Halts M.rules c

/-- **Mortality** (Hooper): the counter machine halts from every configuration. -/
def Mortal {Q ι : Type*} (U : CM Q ι) : Prop :=
  ∀ c : Cfg Q ι, U.Halts c

/-! ## 1. The dichotomy for valid machines -/

section Dichotomy

variable {j : ℕ} {M : Machine} {hw : List (ℤ × ℤ)}

/-- The completion on `ℤ ⊕ Empty` and `σ` on `ℤ` have the same number of orbits. -/
theorem card_orbits_complete (h : Good j M hw) :
    Cardinal.mk (RcwaMachine.Orbits (RcwaMachine.complete h.eng h.tau h.theta)) =
      Cardinal.mk (RcwaMachine.Orbits (sigmaPerm h)) := by
  refine Cardinal.mk_congr (Quotient.congr (Equiv.sumEmpty ℤ Empty) ?_)
  rintro (a | e) (b | e')
  · exact h.sameCycle_iff
  · exact e'.elim
  · exact e.elim
  · exact e.elim

/-- **Junk multiplicity** (Lemma P).  A source of `M` whose run does not halt gives infinitely
many divergent engine sources, one for each junk value `1 + 6 · 5^j · k`. -/
theorem infinite_divergent (h : Good j M hw) {c : RcwaSameOrbit.Cfg} (hc : IsSource M.rules c)
    (hnh : ¬ Halts M.rules c) :
    Infinite {s : RcwaMachine.Src h.eng // RcwaMachine.Diverges h.eng s.1} := by
  have hj := h.one_le
  have hK : c.1 < M.K := by
    by_contra hK
    refine hnh ⟨0, c, rfl, ?_⟩
    rw [IsSink, RcwaSameOrbit.step, Option.map_eq_none_iff, List.find?_eq_none]
    intro ρ hρ hf
    have := h.wf.src_lt ρ hρ
    have hf' : ρ.Fires c := by simpa using hf
    have := hf'.1
    omega
  have hord : c.1 < orderOf (3 : ZMod (5 ^ j)) := lt_of_lt_of_le hK h.fits
  have hspec : ∀ k : ℕ, InEngine j (build j 0 0 (1 + 6 * 5 ^ j * k) c.1 c.2.1 c.2.2) ∧
      decode j (build j 0 0 (1 + 6 * 5 ^ j * k) c.1 c.2.1 c.2.2) = c ∧
      junk j (build j 0 0 (1 + 6 * 5 ^ j * k) c.1 c.2.1 c.2.2) =
        (0, 0, (1 + 6 * 5 ^ j * k : ℤ)) := by
    intro k
    have h2 : ¬ (2 : ℤ) ∣ 1 + 6 * 5 ^ j * k := by
      generalize (5 : ℤ) ^ j * k = t; rw [mul_assoc]; omega
    have h3 : ¬ (3 : ℤ) ∣ 1 + 6 * 5 ^ j * k := by
      generalize (5 : ℤ) ^ j * k = t; rw [mul_assoc]; omega
    have hu : (2 : ZMod (5 ^ j)) ^ 0 * 3 ^ 0 * ((1 + 6 * 5 ^ j * k : ℤ) : ZMod (5 ^ j)) = 1 := by
      have h5 : ((5 : ℤ) : ZMod (5 ^ j)) ^ j = 0 := by
        rw [show ((5 : ℤ) : ZMod (5 ^ j)) ^ j = ((5 ^ j : ℕ) : ZMod (5 ^ j)) by push_cast; rfl,
          ZMod.natCast_self]
      push_cast at h5 ⊢
      rw [h5]; ring
    obtain ⟨h0, h1, h2, h3, h4⟩ := build_spec hj (N_pos j) (N_pos j) hord h2 h3 hu c.2.1 c.2.2
    exact ⟨h0, by rw [decode, h1, h2, h3], h4⟩
  let f : ℕ → {s : RcwaMachine.Src h.eng // RcwaMachine.Diverges h.eng s.1} := fun k =>
    ⟨⟨build j 0 0 (1 + 6 * 5 ^ j * k) c.1 c.2.1 c.2.2,
      (RcwaSameOrbit.engine_symm_eq_none_iff _ _ _).2 (Or.inr (by rw [(hspec k).2.1]; exact hc))⟩,
      (h.diverges_iff (hspec k).1).2 (by rw [(hspec k).2.1]; exact hnh)⟩
  refine Infinite.of_injective f fun k k' hkk => ?_
  have he : build j 0 0 (1 + 6 * 5 ^ j * k) c.1 c.2.1 c.2.2 =
      build j 0 0 (1 + 6 * 5 ^ j * k') c.1 c.2.1 c.2.2 :=
    congrArg (fun s => s.1.1) hkk
  have hjk := congrArg (fun n => (junk j n).2.2) he
  simp only [(hspec k).2.2, (hspec k').2.2] at hjk
  have h5 : (5 : ℤ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
  have : (k : ℤ) = k' := by
    exact mul_left_cancel₀ (mul_ne_zero (by norm_num : (6 : ℤ) ≠ 0) h5)
      (by linarith : 6 * 5 ^ j * (k : ℤ) = 6 * 5 ^ j * k')
  exact_mod_cast this

/-- An engine source diverges only if some machine source does not halt. -/
theorem not_diverges_of_sourcesHalt (h : Good j M hw) (hs : SourcesHalt M)
    (s : RcwaMachine.Src h.eng) : ¬ RcwaMachine.Diverges h.eng s.1 := by
  by_cases hE : InEngine j s.1
  · have hsrc : IsSource M.rules (decode j s.1) :=
      ((RcwaSameOrbit.engine_symm_eq_none_iff _ _ _).1 s.2).resolve_left (not_not.2 hE)
    rw [h.diverges_iff hE, not_not]
    exact hs _ hsrc
  · intro hd
    exact hd 1 (RcwaMachine.fwd_succ_of_none (RcwaSameOrbit.F_of_not_inEngine j M.rules hE) 0)

/-- One orbit iff every source halts (`RcwaSameOrbit.sameCycle_all_iff`, renamed). -/
theorem oneOrbit_sigma_iff (h : Good j M hw) (h1 : RcwaSameOrbit.NoBiInfinite M.rules)
    (h2 : RcwaSameOrbit.EndToStart M.rules M.pairFn) :
    OneOrbit (sigmaPerm h) ↔ SourcesHalt M := by
  exact RcwaSameOrbit.sameCycle_all_iff h h1 h2

/-- **Exactly one orbit** iff every source halts. -/
theorem card_orbits_sigma_eq_one_iff (h : Good j M hw) (h1 : RcwaSameOrbit.NoBiInfinite M.rules)
    (h2 : RcwaSameOrbit.EndToStart M.rules M.pairFn) :
    Cardinal.mk (RcwaMachine.Orbits (sigmaPerm h)) = 1 ↔ SourcesHalt M := by
  rw [← card_orbits_complete h,
    RcwaMachine.card_orbits _ _ _ (h.noBiInfinite h1) (h.endToStart h2)]
  constructor
  · intro hone
    by_contra hs
    simp only [SourcesHalt, not_forall] at hs
    obtain ⟨c, hc, hnh⟩ := hs
    have hinf := Cardinal.infinite_iff.1 (infinite_divergent h hc hnh)
    have : Cardinal.aleph0 ≤ 1 := hone ▸ hinf.trans (self_le_add_left _ _)
    exact absurd this (not_le.2 Cardinal.one_lt_aleph0)
  · intro hs
    have : Cardinal.mk {s : RcwaMachine.Src h.eng // RcwaMachine.Diverges h.eng s.1} = 0 :=
      Cardinal.mk_eq_zero_iff.2 ⟨fun d => not_diverges_of_sourcesHalt h hs d.1 d.2⟩
    rw [this, add_zero]

/-- **Countably many orbits** iff some source does not halt. -/
theorem card_orbits_sigma_eq_aleph0_iff (h : Good j M hw)
    (h1 : RcwaSameOrbit.NoBiInfinite M.rules) (h2 : RcwaSameOrbit.EndToStart M.rules M.pairFn) :
    Cardinal.mk (RcwaMachine.Orbits (sigmaPerm h)) = Cardinal.aleph0 ↔ ¬ SourcesHalt M := by
  constructor
  · intro ha hs
    rw [(card_orbits_sigma_eq_one_iff h h1 h2).2 hs] at ha
    exact Cardinal.one_lt_aleph0.ne ha
  · intro hs
    simp only [SourcesHalt, not_forall] at hs
    obtain ⟨c, hc, hnh⟩ := hs
    refine le_antisymm ?_ ?_
    · exact (Cardinal.mk_le_of_surjective Quotient.mk_surjective).trans Cardinal.mk_int.le
    · rw [← card_orbits_complete h,
        RcwaMachine.card_orbits _ _ _ (h.noBiInfinite h1) (h.endToStart h2)]
      exact (Cardinal.infinite_iff.1 (infinite_divergent h hc hnh)).trans (self_le_add_left _ _)

/-- Infinitely many orbits iff some source does not halt. -/
theorem infinite_orbits_sigma_iff (h : Good j M hw) (h1 : RcwaSameOrbit.NoBiInfinite M.rules)
    (h2 : RcwaSameOrbit.EndToStart M.rules M.pairFn) :
    Infinite (RcwaMachine.Orbits (sigmaPerm h)) ↔ ¬ SourcesHalt M := by
  rw [Cardinal.infinite_iff]
  constructor
  · intro ha hs
    rw [(card_orbits_sigma_eq_one_iff h h1 h2).2 hs] at ha
    exact absurd ha (not_le.2 Cardinal.one_lt_aleph0)
  · intro hs
    exact ((card_orbits_sigma_eq_aleph0_iff h h1 h2).2 hs).ge

/-- **The dichotomy on tables.**  For a valid machine, `tableOf M` is exact, its map is a
bijection, and the permutation has one orbit iff every source halts, infinitely many otherwise. -/
theorem tableOf_orbits (hM : M.Valid) :
    (tableOf M).Exact ∧ ∃ hb : Function.Bijective (tableOf M).eval,
      (OneOrbit (Equiv.ofBijective _ hb) ↔ SourcesHalt M) ∧
        (Infinite (RcwaMachine.Orbits (Equiv.ofBijective _ hb)) ↔ ¬ SourcesHalt M) := by
  have hG := RcwaSameOrbit.good_of_valid hM
  obtain ⟨hex, hev⟩ := RcwaSameOrbit.tableOf_spec hM
  have hb : Function.Bijective (tableOf M).eval := hev ▸ RcwaSameOrbit.sigma_bijective hG
  have he : Equiv.ofBijective (tableOf M).eval hb = sigmaPerm hG := by
    ext x; simp [sigmaPerm, hev]
  refine ⟨hex, hb, ?_, ?_⟩
  · rw [he]; exact oneOrbit_sigma_iff hG hM.noBiInfinite hM.endToStart
  · rw [he]; exact infinite_orbits_sigma_iff hG hM.noBiInfinite hM.endToStart

end Dichotomy

/-! ## 2. Mortality transfer through the compile -/

section Transfer

variable {Q ι : Type*}

/-- (S1) gives the forward loop condition of `RcwaMachine`'s Lemma M (mirror of
`lapNotDown_of_lapsMixed`, using the negative lap entry). -/
theorem lapNotUp_of_lapsMixed [DecidableEq ι] {M : CM Q ι} {B : Set Q} (hlap : LapsMixed M B) :
    RcwaMachine.LapNotUp B M.Step := by
  intro x m n hmn hrun hq hle
  have hex : ∀ j, ∃ ρ : Quad Q ι, j < n - m → ρ ∈ M ∧ (x (m + j)).1 = ρ.src ∧
      (x (m + j + 1)).1 = ρ.dst ∧ ρ.op.Act (x (m + j)).2 (x (m + j + 1)).2 := by
    intro j
    by_cases hj : j < n - m
    · obtain ⟨ρ, hρ, h1, h2, h3⟩ := hrun.1 (m + j) (by omega) (by omega)
      exact ⟨ρ, fun _ => ⟨hρ, h1, h2, h3⟩⟩
    · exact ⟨⟨(x m).1, .nop, (x m).1⟩, fun h => absurd h hj⟩
  choose ρ hρ using hex
  have hsum : ∀ j k, k ≤ n - m → ∑ i ∈ Finset.range k, (ρ i).op.delta j =
      ((x (m + k)).2 j : ℤ) - (x m).2 j := by
    intro j k
    induction k with
    | zero => intro; simp
    | succ k ih =>
      intro hk
      have := Op.act_delta (hρ k (by omega)).2.2.2 j
      rw [Finset.sum_range_succ, ih (by omega), show m + (k + 1) = m + k + 1 by omega]
      omega
  obtain ⟨⟨j, hj⟩, -⟩ := hlap ρ (n - m) (by omega) (fun i hi => (hρ i hi).1)
    (fun i hi => by rw [← (hρ i hi).2.1]; exact hrun.2 _ (by omega) (by omega))
    (fun i hi => by
      rw [← (hρ i (by omega)).2.2.1, ← (hρ (i + 1) hi).2.1, Nat.add_assoc])
    (by
      rw [← (hρ _ (by omega)).2.2.1, ← (hρ 0 (by omega)).2.1,
        show m + (n - m - 1) + 1 = n by omega, Nat.add_zero, hq])
  rw [hsum j _ le_rfl, show m + (n - m) = n by omega] at hj
  have : (x m).2 j ≤ (x n).2 j := hle j
  omega

/-- A configuration that does not halt starts an infinite run. -/
theorem exists_forever_of_not_halts {M : CM Q ι} {c : Cfg Q ι} (h : ¬ M.Halts c) :
    ∃ x : ℕ → Cfg Q ι, x 0 = c ∧ ∀ n, M.Step (x n) (x (n + 1)) := by
  have hnext : ∀ d : {d : Cfg Q ι // ¬ M.Halts d}, ∃ d' : {d : Cfg Q ι // ¬ M.Halts d},
      M.Step d.1 d'.1 := by
    rintro ⟨d, hd⟩
    by_cases hst : M.Stuck d
    · exact absurd ⟨d, .refl, hst⟩ hd
    · simp only [CM.Stuck, not_forall, not_not] at hst
      obtain ⟨d', hd'⟩ := hst
      exact ⟨⟨d', fun ⟨e, he, hse⟩ => hd ⟨e, .head hd' he, hse⟩⟩, hd'⟩
  choose f hf using hnext
  refine ⟨fun n => (f^[n] ⟨c, h⟩).1, rfl, fun n => ?_⟩
  simp only [Function.iterate_succ_apply']
  exact hf _

/-- Under determinism, halting passes down a run. -/
theorem halts_of_reaches {M : CM Q ι} (hM : M.Det) {s c : Cfg Q ι} (hs : M.Halts s)
    (hr : M.Reaches s c) : M.Halts c := by
  induction hr with
  | refl => exact hs
  | tail _ hbc ih =>
    obtain ⟨d, hd, hst⟩ := ih
    rcases Relation.ReflTransGen.cases_head hd with rfl | ⟨b', hb', hr'⟩
    · exact absurd hbc (hst _)
    · rw [CM.step_functional hM hbc hb']
      exact ⟨d, hr', hst⟩

/-- With a mortal reverse, every configuration is reached from a source. -/
theorem exists_source_reaches {M : CM Q ι} (hM : M.RevMortal) (c : Cfg Q ι) :
    ∃ s, M.IsSource s ∧ M.Reaches s c := by
  by_contra hno
  push Not at hno
  have hprev : ∀ d : {d : Cfg Q ι // M.Reaches d c}, ∃ d' : {d : Cfg Q ι // M.Reaches d c},
      M.Step d'.1 d.1 := by
    rintro ⟨d, hd⟩
    have : ¬ M.IsSource d := fun hs => hno d hs hd
    simp only [CM.IsSource, not_forall, not_not] at this
    obtain ⟨d', hd'⟩ := this
    exact ⟨⟨d', .head hd' hd⟩, hd'⟩
  choose f hf using hprev
  refine hM ⟨fun n => (f^[n] ⟨c, .refl⟩).1, fun n => ?_⟩
  simp only [Function.iterate_succ_apply']
  exact hf _

/-- **Lemma M, forward, for counter machines.**  Under (S1), a configuration that does not halt
starts an infinite forward chain of macro steps. -/
theorem exists_macro_chain [Finite Q] [Finite ι] [DecidableEq ι] {M : CM Q ι} {B : Set Q}
    (hlap : LapsMixed M B) {c : Cfg Q ι} (h : ¬ M.Halts c) :
    ∃ b : ℕ → Cfg Q ι, ∀ n, RcwaMachine.MacroStep B M.Step (b n) (b (n + 1)) := by
  have := wellQuasiOrderedLE_pi (ι := ι)
  obtain ⟨x, -, hx⟩ := exists_forever_of_not_halts h
  exact (RcwaMachine.immortal_iff_macro B M.Step (lapNotUp_of_lapsMixed hlap)).1 ⟨x, hx⟩

end Transfer

section HistoryMortal

variable {Q ι : Type*} {K : ℕ} {U : CM Q ι} {lab : Quad Q ι → Fin K}

/-- **Soundness on garbage**, history wrapper.  Every macro step, from any configuration, is a
step of `U` on the `val` counters between boundary states. -/
theorem histWrap_macro_sound (hU : U.Det) {b b' : Cfg (HState Q ι K) (HCtr ι)}
    (hm : RcwaMachine.MacroStep (Set.range HState.bnd) (histWrap U lab).Step b b') :
    ∃ s s' : Q, b.1 = .bnd s ∧ b'.1 = .bnd s' ∧
      U.Step (s, fun i => b.2 (.val i)) (s', fun i => b'.2 (.val i)) := by
  have hm₀ := hm
  obtain ⟨hb, hb', x, n, hn, hx0, hxn, hstep, hoff⟩ := hm
  obtain ⟨s, hs⟩ := hb
  -- the first step is the guard
  obtain ⟨r, hr, h1, h2, h3⟩ := hstep 0 hn
  rw [hx0, ← hs] at h1
  cases hr <;> simp only [HState.bnd.injEq, reduceCtorEq] at h1
  rename_i ρ hρ
  obtain ⟨hw, hx1⟩ := h3
  rw [hx0] at hw hx1
  simp only [decide_eq_false_iff_not, not_lt, Nat.le_zero] at hw
  -- the second step is `op ρ'`
  have hn2 : 1 < n := by
    by_contra hc
    obtain rfl : n = 1 := by omega
    obtain ⟨t, ht⟩ := hb'
    rw [← hxn, h2] at ht
    cases ht
  obtain ⟨r', hr', h1', h2', h3'⟩ := hstep 1 hn2
  rw [h2] at h1'
  cases hr' <;> simp only [HState.act.injEq, reduceCtorEq] at h1'
  rename_i ρ' hρ'
  rw [hx1] at h3'
  obtain ⟨hact, -, -⟩ := map_act_inv h3'
  have hbeq : b = (.bnd ρ'.src, hcfg (fun i => b.2 (.val i)) (b.2 .hist)) := by
    refine Prod.ext (by rw [← hs, h1, h1']) (funext fun c => ?_)
    cases c <;> simp [hcfg, hw]
  have hmac := histWrap_macro (lab := lab) hρ' hact (b.2 .hist)
  rw [← hbeq] at hmac
  have := macroStep_functional (histWrap_det hU) hm₀ hmac
  refine ⟨ρ'.src, ρ'.dst, by rw [hbeq], by rw [this], ρ', hρ', rfl, rfl, ?_⟩
  rw [this]
  exact hact

/-- **Lemma H, mortality.**  The wrapper halts from every configuration iff `U` does. -/
theorem histWrap_mortal_iff [Fintype Q] [Fintype ι] [DecidableEq Q] [DecidableEq ι]
    (hU : U.Det) : Mortal (histWrap U lab) ↔ Mortal U := by
  constructor
  · intro hm c
    exact (histWrap_halts_iff hU c.1 c.2).1 (hm _)
  · intro hm c
    by_contra hnh
    obtain ⟨b, hb⟩ := exists_macro_chain histWrap_lapsMixed hnh
    choose s s' hs hs' hst using fun n => histWrap_macro_sound hU (hb n)
    have key : ∀ n, s' n = s (n + 1) := fun n =>
      HState.bnd.inj ((hs' n).symm.trans (hs (n + 1)))
    refine CM.not_halts_of_forever hU (fun n => (s n, fun i => (b n).2 (.val i)))
      (fun n => ?_) (hm _)
    have := hst n
    rw [key n] at this
    exact this

end HistoryMortal

section GodelMortal

variable {Q ι : Type*} {N : ℕ} {B : CM Q ι} {p : ι → ℕ}

/-- **Lemma G, mortality.**  The compile halts from every configuration iff `B` does. -/
theorem godel_mortal_iff [Fintype Q] [Fintype ι] [DecidableEq Q] (hB : B.Det) (hB' : B.Rev)
    (hp : PrimeData p N) : Mortal (godel B p N) ↔ Mortal B := by
  constructor
  · intro hm c
    exact (godel_halts_iff hB hB' hp c.1 c.2).1 (hm _)
  · intro hm c
    by_contra hnh
    obtain ⟨b, hb⟩ := exists_macro_chain (godel_lapsMixed hB hB' hp) hnh
    choose q q' v v' J hJ hJp h1 h2 hst using fun n => godel_macro_sound hB hB' hp (hb n)
    have key : ∀ n, q' n = q (n + 1) ∧ v' n = v (n + 1) := by
      intro n
      have e := (h2 n).symm.trans (h1 (n + 1))
      simp only [Prod.mk.injEq, GState.ent.injEq] at e
      exact ⟨e.1, (genc_inj hp (hJ n) (hJ (n + 1)) (hJp n) (hJp (n + 1)) e.2).2⟩
    refine CM.not_halts_of_forever hB (fun n => (q n, v n)) (fun n => ?_) (hm _)
    have := hst n
    rw [(key n).1, (key n).2] at this
    exact this

end GodelMortal

section DoubleMortal

variable {Q : Type*} [DecidableEq Q] {K : ℕ} {R : CM Q (Fin 2)} {rs : List (Quad Q (Fin 2))}

/-- **Lemma D, mortality.**  With a mortal reverse, every source of the doubling halts iff `R`
halts from every configuration. -/
theorem double_sourcesHalt_iff (e : Q × Bool ≃ Fin K) (hrs : ∀ ρ, ρ ∈ rs ↔ ρ ∈ R)
    (hdet : R.Det) (hrev : R.Rev) (hmort : R.RevMortal) :
    SourcesHalt (double rs e) ↔ Mortal R := by
  constructor
  · intro hS c
    obtain ⟨s, hs, hr⟩ := exists_source_reaches hmort c
    have := (double_halts_iff e hrs hdet hrev hs).1 (hS _ (double_isSource e hrs hdet hrev hs))
    exact halts_of_reaches hdet this hr
  · intro hM x hx
    by_cases hK : x.1 < K
    · obtain ⟨b, c, rfl⟩ := exists_dcfg e hK
      cases b with
      | false => exact absurd hx (double_not_isSource_bwd e hrs hdet hrev c)
      | true =>
        exact (double_halts_iff e hrs hdet hrev (isSource_of_double e hrs hdet hrev hx)).2 (hM c)
    · exact ⟨0, x, rfl, Option.eq_none_iff_forall_ne_some.2 fun y hy =>
        hK (double_step_lt e hy).1⟩

end DoubleMortal

/-- **The compiled machine, mortality form.**  A deterministic finite counter machine `U` gives a
valid machine all of whose sources halt iff `U` is mortal. -/
theorem exists_valid_machine_mortal {Q ι : Type} [Finite Q] [Finite ι] [DecidableEq ι]
    {U : CM Q ι} (hU : U.Det) : ∃ M : Machine, M.Valid ∧ (SourcesHalt M ↔ Mortal U) := by
  classical
  have := Fintype.ofFinite Q
  have := Fintype.ofFinite ι
  -- labels `1, …, card` of the rules
  let L := Fintype.card (Quad Q ι) + 1
  let lab : Quad Q ι → Fin L := fun ρ => ⟨Fintype.equivFin (Quad Q ι) ρ + 1, by
    have := (Fintype.equivFin (Quad Q ι) ρ).isLt; omega⟩
  have hlab : ∀ ρ ∈ U, 1 ≤ (lab ρ).val := fun ρ _ => by simp [lab]
  have hinj : ∀ ρ ∈ U, ∀ ρ' ∈ U, lab ρ = lab ρ' → ρ = ρ' := fun ρ _ ρ' _ h => by
    simp only [lab, Fin.mk.injEq, Nat.add_right_cancel_iff] at h
    exact (Fintype.equivFin _).injective (Fin.ext h)
  -- distinct primes for the wrapper's counters
  let p : HCtr ι → ℕ := fun c => Nat.nth Nat.Prime (Fintype.equivFin (HCtr ι) c)
  let N := ∑ c, p c
  have hp : PrimeData p N :=
    ⟨fun c => Nat.prime_nth_prime _,
      fun c c' h => (Fintype.equivFin _).injective
        (Fin.ext (Nat.nth_injective Nat.infinite_setOfPred_prime h)),
      fun c => Finset.single_le_sum (f := p) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)⟩
  let B := histWrap U lab
  have hBd : B.Det := histWrap_det hU
  have hBr : B.Rev := histWrap_rev hU hlab hinj
  have hBm : B.RevMortal := histWrap_revMortal hU hlab
  let R := godel B p N
  have hRd : R.Det := godel_det hBd hBr hp
  have hRr : R.Rev := godel_rev hBd hBr hp
  have hRm : R.RevMortal := godel_revMortal hBd hBr hp hBm
  let rs := (Finset.univ.filter (· ∈ R)).toList
  have hrs : ∀ ρ, ρ ∈ rs ↔ ρ ∈ R := fun ρ => by simp [rs]
  let e := Fintype.equivFin (GState (HState Q ι L) N × Bool)
  refine ⟨double rs e, double_valid e hrs hRd hRr hRm, ?_⟩
  exact (double_sourcesHalt_iff e hrs hRd hRr hRm).trans
    ((godel_mortal_iff hBd hBr hp).trans (histWrap_mortal_iff hU))

/-- **Theorem C(1), machine form (hypothesis-free).**  For every deterministic finite counter
machine `U` there is an exact table whose map is a permutation of `ℤ` (all slopes in
`2^ℤ 3^ℤ`) with one orbit if `U` is mortal and infinitely many orbits otherwise. -/
theorem exists_table_iff_mortal {Q ι : Type} [Finite Q] [Finite ι] [DecidableEq ι] {U : CM Q ι}
    (hU : U.Det) :
    ∃ T : RcwaTable, T.Exact ∧ ∃ hb : Function.Bijective T.eval,
      (OneOrbit (Equiv.ofBijective T.eval hb) ↔ Mortal U) ∧
        (Infinite (RcwaMachine.Orbits (Equiv.ofBijective T.eval hb)) ↔ ¬ Mortal U) := by
  obtain ⟨M, hM, hiff⟩ := exists_valid_machine_mortal hU
  obtain ⟨hex, hb, h1, h2⟩ := tableOf_orbits hM
  exact ⟨tableOf M, hex, hb, h1.trans hiff, h2.trans (not_congr hiff)⟩

/-! ## 3. Undecidability of the orbit count, given undecidable mortality -/

/-- The table map is computable. -/
theorem computable_tableOf : Computable tableOf := by
  exact (Computable.fst.comp (RcwaSameOrbit.computable_reduce.comp
    (Computable.pair Computable.id (Computable.const ((0, 0, 0) : RcwaSameOrbit.Cfg))))).of_eq
    fun _ => rfl

/-- **Interface** (a hypothesis, never an axiom): whether every source halts is not a
computable property of valid machines. -/
def MortalityUndecidable : Prop :=
  ¬ ∃ g : Machine → Bool, Computable g ∧
    ∀ M : Machine, M.Valid → (g M = true ↔ SourcesHalt M)

/-- **"One orbit" is undecidable** on exact tables with bijective evaluation, given
`MortalityUndecidable`. -/
theorem not_computable_oneOrbit (h : MortalityUndecidable) :
    ¬ ∃ g : RcwaTable → Bool, Computable g ∧
      ∀ (T : RcwaTable), T.Exact → ∀ hb : Function.Bijective T.eval,
        (g T = true ↔ OneOrbit (Equiv.ofBijective T.eval hb)) := by
  rintro ⟨g, hg, hspec⟩
  refine h ⟨g ∘ tableOf, hg.comp computable_tableOf, fun M hM => ?_⟩
  obtain ⟨hex, hb, h1, -⟩ := tableOf_orbits hM
  exact (hspec _ hex hb).trans h1

/-- **"Finitely many orbits" is undecidable** on the same tables, given `MortalityUndecidable`. -/
theorem not_computable_finiteOrbits (h : MortalityUndecidable) :
    ¬ ∃ g : RcwaTable → Bool, Computable g ∧
      ∀ (T : RcwaTable), T.Exact → ∀ hb : Function.Bijective T.eval,
        (g T = true ↔ Finite (RcwaMachine.Orbits (Equiv.ofBijective T.eval hb))) := by
  rintro ⟨g, hg, hspec⟩
  refine h ⟨g ∘ tableOf, hg.comp computable_tableOf, fun M hM => ?_⟩
  obtain ⟨hex, hb, -, h2⟩ := tableOf_orbits hM
  rw [Function.comp_apply, hspec _ hex hb, ← not_infinite_iff_finite, h2, not_not]

/-! ## 4. Totality: Theorem C(1) and its arithmetic strength, given a totality family -/

/-- `φ_e` is total. -/
def Total (e : ℕ) : Prop :=
  ∀ x, (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code e) x).Dom

/-- Computable predicates pull back along computable maps. -/
theorem computablePred_comp {α β : Type*} [Primcodable α] [Primcodable β] {p : β → Prop}
    {f : α → β} (hp : ComputablePred p) (hf : Computable f) : ComputablePred fun a => p (f a) := by
  obtain ⟨D, hD⟩ := hp
  exact ⟨fun a => D (f a), hD.comp hf⟩

/-- R.e. predicates pull back along computable maps. -/
theorem rePred_comp {α β : Type*} [Primcodable α] [Primcodable β] {p : β → Prop}
    {f : α → β} (hp : REPred p) (hf : Computable f) : REPred fun a => p (f a) :=
  hp.comp hf

/-- **s-m-n.**  A partial recursive `G` on `Code × ℕ` is `φ_{r c}` for a computable `r`. -/
theorem exists_index {G : Nat.Partrec.Code × ℕ →. ℕ} (hG : Partrec G) :
    ∃ r : Nat.Partrec.Code → ℕ, Computable r ∧ ∀ c x,
      Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code (r c)) x = G (c, x) := by
  have hH : Partrec fun m : ℕ =>
      G (Denumerable.ofNat Nat.Partrec.Code m.unpair.1, m.unpair.2) :=
    hG.comp (((Computable.ofNat _).comp (Computable.fst.comp Computable.unpair)).pair
      (Computable.snd.comp Computable.unpair))
  obtain ⟨d, hd⟩ := Nat.Partrec.Code.exists_code.1 (Partrec.nat_iff.1 hH)
  refine ⟨fun c => Encodable.encode (Nat.Partrec.Code.curry d (Encodable.encode c)), ?_,
    fun c x => ?_⟩
  · exact Computable.encode.comp (Nat.Partrec.Code.primrec₂_curry.to_comp.comp
      (Computable.const d) Computable.encode)
  · rw [Denumerable.ofNat_encode, Nat.Partrec.Code.eval_curry, hd]
    simp [Nat.unpair_pair, Denumerable.ofNat_encode]

/-- Totality is not computable (Rice). -/
theorem total_not_computable : ¬ ComputablePred Total := by
  intro h
  have hC : ComputablePred fun c : Nat.Partrec.Code =>
      Nat.Partrec.Code.eval c ∈ {f : ℕ →. ℕ | ∀ x, (f x).Dom} :=
    (computablePred_comp h Computable.encode).of_eq fun c => by
      simp [Total, Denumerable.ofNat_encode]
  have := ComputablePred.rice _ hC (f := fun _ => Part.some 0) (g := fun _ => Part.none)
    Nat.Partrec.zero Nat.Partrec.none (fun _ => trivial)
  exact this 0

/-- Totality is not r.e. (the complement of the halting problem reduces to it). -/
theorem total_not_re : ¬ REPred Total := by
  intro h
  have hG : Partrec fun p : Nat.Partrec.Code × ℕ =>
      cond (Nat.Partrec.Code.evaln p.2 p.1 0).isSome (Part.none : Part ℕ) (Part.some 0) :=
    Partrec.cond (Primrec.option_isSome.comp (Nat.Partrec.Code.primrec_evaln.comp
      ((Primrec.snd.pair Primrec.fst).pair (Primrec.const 0)))).to_comp Partrec.none
      (Computable.const 0).partrec
  obtain ⟨r, hr, hre⟩ := exists_index hG
  refine ComputablePred.halting_problem_not_re 0 ((rePred_comp h hr).of_eq fun c => ?_)
  simp only [Total, hre]
  constructor
  · intro hall hd
    obtain ⟨y, hy⟩ := Part.dom_iff_mem.1 hd
    obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.1 hy
    have := hall k
    rw [show Nat.Partrec.Code.evaln k c 0 = some y from hk] at this
    simp at this
  · intro hnd x
    cases he : Nat.Partrec.Code.evaln x c 0 with
    | none => simp
    | some y => exact absurd (Part.dom_iff_mem.2 ⟨y, Nat.Partrec.Code.evaln_sound he⟩) hnd

/-- Non-totality is not r.e. (the halting problem reduces to totality). -/
theorem total_not_coRE : ¬ REPred fun e => ¬ Total e := by
  intro h
  have hG : Partrec fun p : Nat.Partrec.Code × ℕ => Nat.Partrec.Code.eval p.1 0 :=
    Nat.Partrec.Code.eval_part.comp Computable.fst (Computable.const 0)
  obtain ⟨r, hr, hre⟩ := exists_index hG
  refine ComputablePred.halting_problem_not_re 0 ((rePred_comp h hr).of_eq fun c => ?_)
  simp only [Total, hre]
  exact ⟨fun h1 h2 => h1 fun _ => h2, fun h1 h2 => h1 (h2 0)⟩

/-- **Interface** (a hypothesis, never an axiom; Lemma A of `undec-lemma` with a uniform
compile): a computable family of valid machines whose sources all halt iff `φ_e` is total. -/
def TotalityFamily : Prop :=
  ∃ F : ℕ → Machine, Computable F ∧ ∀ e, (F e).Valid ∧ (SourcesHalt (F e) ↔ Total e)

/-- A totality family makes mortality undecidable. -/
theorem mortalityUndecidable_of_totalityFamily (h : TotalityFamily) : MortalityUndecidable := by
  obtain ⟨F, hF, hFe⟩ := h
  rintro ⟨g, hg, hspec⟩
  refine total_not_computable (ComputablePred.computable_iff.2
    ⟨fun e => g (F e), hg.comp hF, funext fun e => propext ?_⟩)
  exact ((hFe e).2.symm.trans (hspec _ (hFe e).1).symm)

/-- **Theorem C(1)**, given a totality family: a computable `e ↦ T e` of exact tables whose maps
are permutations of `ℤ` with one orbit if `φ_e` is total and infinitely many otherwise. -/
theorem orbit_count_family (h : TotalityFamily) :
    ∃ T : ℕ → RcwaTable, Computable T ∧ ∀ e, (T e).Exact ∧
      ∃ hb : Function.Bijective (T e).eval,
        (OneOrbit (Equiv.ofBijective _ hb) ↔ Total e) ∧
          (¬ Total e → Infinite (RcwaMachine.Orbits (Equiv.ofBijective _ hb))) := by
  obtain ⟨F, hF, hFe⟩ := h
  refine ⟨fun e => tableOf (F e), computable_tableOf.comp hF, fun e => ?_⟩
  obtain ⟨hex, hb, h1, h2⟩ := tableOf_orbits (hFe e).1
  exact ⟨hex, hb, h1.trans (hFe e).2, fun ht => h2.2 fun hs => ht ((hFe e).2.1 hs)⟩

/-- **"One orbit" is not r.e.** on exact bijective tables, given a totality family. -/
theorem oneOrbit_not_re (h : TotalityFamily) :
    ¬ ∃ P : RcwaTable → Prop, REPred P ∧
      ∀ (T : RcwaTable), T.Exact → ∀ hb : Function.Bijective T.eval,
        (P T ↔ OneOrbit (Equiv.ofBijective T.eval hb)) := by
  rintro ⟨P, hP, hspec⟩
  obtain ⟨T, hT, hTe⟩ := orbit_count_family h
  refine total_not_re ((rePred_comp hP hT).of_eq fun e => ?_)
  obtain ⟨hex, hb, h1, -⟩ := hTe e
  exact (hspec _ hex hb).trans h1

/-- **"More than one orbit" is not r.e.** on exact bijective tables, given a totality family. -/
theorem oneOrbit_not_coRE (h : TotalityFamily) :
    ¬ ∃ P : RcwaTable → Prop, REPred P ∧
      ∀ (T : RcwaTable), T.Exact → ∀ hb : Function.Bijective T.eval,
        (P T ↔ ¬ OneOrbit (Equiv.ofBijective T.eval hb)) := by
  rintro ⟨P, hP, hspec⟩
  obtain ⟨T, hT, hTe⟩ := orbit_count_family h
  refine total_not_coRE ((rePred_comp hP hT).of_eq fun e => ?_)
  obtain ⟨hex, hb, h1, -⟩ := hTe e
  exact (hspec _ hex hb).trans (not_congr h1)

end CollatzMoonshot.RcwaOrbitCount
