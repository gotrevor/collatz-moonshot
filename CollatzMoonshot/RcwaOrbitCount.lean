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
  sorry

/-- **Junk multiplicity** (Lemma P).  A source of `M` whose run does not halt gives infinitely
many divergent engine sources, one for each junk value `1 + 6 · 5^j · k`. -/
theorem infinite_divergent (h : Good j M hw) {c : RcwaSameOrbit.Cfg} (hc : IsSource M.rules c)
    (hnh : ¬ Halts M.rules c) :
    Infinite {s : RcwaMachine.Src h.eng // RcwaMachine.Diverges h.eng s.1} := by
  sorry

/-- An engine source diverges only if some machine source does not halt. -/
theorem not_diverges_of_sourcesHalt (h : Good j M hw) (hs : SourcesHalt M)
    (s : RcwaMachine.Src h.eng) : ¬ RcwaMachine.Diverges h.eng s.1 := by
  sorry

/-- One orbit iff every source halts (`RcwaSameOrbit.sameCycle_all_iff`, renamed). -/
theorem oneOrbit_sigma_iff (h : Good j M hw) (h1 : RcwaSameOrbit.NoBiInfinite M.rules)
    (h2 : RcwaSameOrbit.EndToStart M.rules M.pairFn) :
    OneOrbit (sigmaPerm h) ↔ SourcesHalt M := by
  sorry

/-- **Exactly one orbit** iff every source halts. -/
theorem card_orbits_sigma_eq_one_iff (h : Good j M hw) (h1 : RcwaSameOrbit.NoBiInfinite M.rules)
    (h2 : RcwaSameOrbit.EndToStart M.rules M.pairFn) :
    Cardinal.mk (RcwaMachine.Orbits (sigmaPerm h)) = 1 ↔ SourcesHalt M := by
  sorry

/-- **Countably many orbits** iff some source does not halt. -/
theorem card_orbits_sigma_eq_aleph0_iff (h : Good j M hw)
    (h1 : RcwaSameOrbit.NoBiInfinite M.rules) (h2 : RcwaSameOrbit.EndToStart M.rules M.pairFn) :
    Cardinal.mk (RcwaMachine.Orbits (sigmaPerm h)) = Cardinal.aleph0 ↔ ¬ SourcesHalt M := by
  sorry

/-- Infinitely many orbits iff some source does not halt. -/
theorem infinite_orbits_sigma_iff (h : Good j M hw) (h1 : RcwaSameOrbit.NoBiInfinite M.rules)
    (h2 : RcwaSameOrbit.EndToStart M.rules M.pairFn) :
    Infinite (RcwaMachine.Orbits (sigmaPerm h)) ↔ ¬ SourcesHalt M := by
  sorry

/-- **The dichotomy on tables.**  For a valid machine, `tableOf M` is exact, its map is a
bijection, and the permutation has one orbit iff every source halts, infinitely many otherwise. -/
theorem tableOf_orbits (hM : M.Valid) :
    (tableOf M).Exact ∧ ∃ hb : Function.Bijective (tableOf M).eval,
      (OneOrbit (Equiv.ofBijective _ hb) ↔ SourcesHalt M) ∧
        (Infinite (RcwaMachine.Orbits (Equiv.ofBijective _ hb)) ↔ ¬ SourcesHalt M) := by
  sorry

end Dichotomy

/-! ## 2. Mortality transfer through the compile -/

section Transfer

variable {Q ι : Type*}

/-- (S1) gives the forward loop condition of `RcwaMachine`'s Lemma M (mirror of
`lapNotDown_of_lapsMixed`, using the negative lap entry). -/
theorem lapNotUp_of_lapsMixed [DecidableEq ι] {M : CM Q ι} {B : Set Q} (hlap : LapsMixed M B) :
    RcwaMachine.LapNotUp B M.Step := by
  sorry

/-- A configuration that does not halt starts an infinite run. -/
theorem exists_forever_of_not_halts {M : CM Q ι} {c : Cfg Q ι} (h : ¬ M.Halts c) :
    ∃ x : ℕ → Cfg Q ι, x 0 = c ∧ ∀ n, M.Step (x n) (x (n + 1)) := by
  sorry

/-- Under determinism, halting passes down a run. -/
theorem halts_of_reaches {M : CM Q ι} (hM : M.Det) {s c : Cfg Q ι} (hs : M.Halts s)
    (hr : M.Reaches s c) : M.Halts c := by
  sorry

/-- With a mortal reverse, every configuration is reached from a source. -/
theorem exists_source_reaches {M : CM Q ι} (hM : M.RevMortal) (c : Cfg Q ι) :
    ∃ s, M.IsSource s ∧ M.Reaches s c := by
  sorry

/-- **Lemma M, forward, for counter machines.**  Under (S1), a configuration that does not halt
starts an infinite forward chain of macro steps. -/
theorem exists_macro_chain [Finite Q] [Finite ι] [DecidableEq ι] {M : CM Q ι} {B : Set Q}
    (hlap : LapsMixed M B) {c : Cfg Q ι} (h : ¬ M.Halts c) :
    ∃ b : ℕ → Cfg Q ι, ∀ n, RcwaMachine.MacroStep B M.Step (b n) (b (n + 1)) := by
  sorry

end Transfer

section HistoryMortal

variable {Q ι : Type*} {K : ℕ} {U : CM Q ι} {lab : Quad Q ι → Fin K}

/-- **Soundness on garbage**, history wrapper.  Every macro step, from any configuration, is a
step of `U` on the `val` counters between boundary states. -/
theorem histWrap_macro_sound (hU : U.Det) {b b' : Cfg (HState Q ι K) (HCtr ι)}
    (hm : RcwaMachine.MacroStep (Set.range HState.bnd) (histWrap U lab).Step b b') :
    ∃ s s' : Q, b.1 = .bnd s ∧ b'.1 = .bnd s' ∧
      U.Step (s, fun i => b.2 (.val i)) (s', fun i => b'.2 (.val i)) := by
  sorry

/-- **Lemma H, mortality.**  The wrapper halts from every configuration iff `U` does. -/
theorem histWrap_mortal_iff [Fintype Q] [Fintype ι] [DecidableEq Q] [DecidableEq ι]
    (hU : U.Det) : Mortal (histWrap U lab) ↔ Mortal U := by
  sorry

end HistoryMortal

section GodelMortal

variable {Q ι : Type*} {N : ℕ} {B : CM Q ι} {p : ι → ℕ}

/-- **Lemma G, mortality.**  The compile halts from every configuration iff `B` does. -/
theorem godel_mortal_iff [Fintype Q] [Fintype ι] [DecidableEq Q] (hB : B.Det) (hB' : B.Rev)
    (hp : PrimeData p N) : Mortal (godel B p N) ↔ Mortal B := by
  sorry

end GodelMortal

section DoubleMortal

variable {Q : Type*} [DecidableEq Q] {K : ℕ} {R : CM Q (Fin 2)} {rs : List (Quad Q (Fin 2))}

/-- **Lemma D, mortality.**  With a mortal reverse, every source of the doubling halts iff `R`
halts from every configuration. -/
theorem double_sourcesHalt_iff (e : Q × Bool ≃ Fin K) (hrs : ∀ ρ, ρ ∈ rs ↔ ρ ∈ R)
    (hdet : R.Det) (hrev : R.Rev) (hmort : R.RevMortal) :
    SourcesHalt (double rs e) ↔ Mortal R := by
  sorry

end DoubleMortal

/-- **The compiled machine, mortality form.**  A deterministic finite counter machine `U` gives a
valid machine all of whose sources halt iff `U` is mortal. -/
theorem exists_valid_machine_mortal {Q ι : Type} [Finite Q] [Finite ι] [DecidableEq ι]
    {U : CM Q ι} (hU : U.Det) : ∃ M : Machine, M.Valid ∧ (SourcesHalt M ↔ Mortal U) := by
  sorry

/-- **Theorem C(1), machine form (hypothesis-free).**  For every deterministic finite counter
machine `U` there is an exact table whose map is a permutation of `ℤ` (all slopes in
`2^ℤ 3^ℤ`) with one orbit if `U` is mortal and infinitely many orbits otherwise. -/
theorem exists_table_iff_mortal {Q ι : Type} [Finite Q] [Finite ι] [DecidableEq ι] {U : CM Q ι}
    (hU : U.Det) :
    ∃ T : RcwaTable, T.Exact ∧ ∃ hb : Function.Bijective T.eval,
      (OneOrbit (Equiv.ofBijective T.eval hb) ↔ Mortal U) ∧
        (Infinite (RcwaMachine.Orbits (Equiv.ofBijective T.eval hb)) ↔ ¬ Mortal U) := by
  sorry

/-! ## 3. Undecidability of the orbit count, given undecidable mortality -/

/-- The table map is computable. -/
theorem computable_tableOf : Computable tableOf := by
  sorry

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
  sorry

/-- **"Finitely many orbits" is undecidable** on the same tables, given `MortalityUndecidable`. -/
theorem not_computable_finiteOrbits (h : MortalityUndecidable) :
    ¬ ∃ g : RcwaTable → Bool, Computable g ∧
      ∀ (T : RcwaTable), T.Exact → ∀ hb : Function.Bijective T.eval,
        (g T = true ↔ Finite (RcwaMachine.Orbits (Equiv.ofBijective T.eval hb))) := by
  sorry

/-! ## 4. Totality: Theorem C(1) and its arithmetic strength, given a totality family -/

/-- `φ_e` is total. -/
def Total (e : ℕ) : Prop :=
  ∀ x, (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code e) x).Dom

/-- Totality is not computable (Rice). -/
theorem total_not_computable : ¬ ComputablePred Total := by
  sorry

/-- Totality is not r.e. (the complement of the halting problem reduces to it). -/
theorem total_not_re : ¬ REPred Total := by
  sorry

/-- Non-totality is not r.e. (the halting problem reduces to totality). -/
theorem total_not_coRE : ¬ REPred fun e => ¬ Total e := by
  sorry

/-- **Interface** (a hypothesis, never an axiom; Lemma A of `undec-lemma` with a uniform
compile): a computable family of valid machines whose sources all halt iff `φ_e` is total. -/
def TotalityFamily : Prop :=
  ∃ F : ℕ → Machine, Computable F ∧ ∀ e, (F e).Valid ∧ (SourcesHalt (F e) ↔ Total e)

/-- A totality family makes mortality undecidable. -/
theorem mortalityUndecidable_of_totalityFamily (h : TotalityFamily) : MortalityUndecidable := by
  sorry

/-- **Theorem C(1)**, given a totality family: a computable `e ↦ T e` of exact tables whose maps
are permutations of `ℤ` with one orbit if `φ_e` is total and infinitely many otherwise. -/
theorem orbit_count_family (h : TotalityFamily) :
    ∃ T : ℕ → RcwaTable, Computable T ∧ ∀ e, (T e).Exact ∧
      ∃ hb : Function.Bijective (T e).eval,
        (OneOrbit (Equiv.ofBijective _ hb) ↔ Total e) ∧
          (¬ Total e → Infinite (RcwaMachine.Orbits (Equiv.ofBijective _ hb))) := by
  sorry

/-- **"One orbit" is not r.e.** on exact bijective tables, given a totality family. -/
theorem oneOrbit_not_re (h : TotalityFamily) :
    ¬ ∃ P : RcwaTable → Prop, REPred P ∧
      ∀ (T : RcwaTable), T.Exact → ∀ hb : Function.Bijective T.eval,
        (P T ↔ OneOrbit (Equiv.ofBijective T.eval hb)) := by
  sorry

/-- **"More than one orbit" is not r.e.** on exact bijective tables, given a totality family. -/
theorem oneOrbit_not_coRE (h : TotalityFamily) :
    ¬ ∃ P : RcwaTable → Prop, REPred P ∧
      ∀ (T : RcwaTable), T.Exact → ∀ hb : Function.Bijective T.eval,
        (P T ↔ ¬ OneOrbit (Equiv.ofBijective T.eval hb)) := by
  sorry

end CollatzMoonshot.RcwaOrbitCount
