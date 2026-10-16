/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.RcwaTotalityCompile
import CollatzMoonshot.RcwaTotalityRestart

/-!
# The totality family; Theorem C(1) hypothesis-free

Discharges the interface `RcwaOrbitCount.TotalityFamily` (kickoff
`KICKOFF-2026-10-16-totality.md`):

* `restart u` is one fixed counter machine (Lemma A's restart wrapper around the universal
  `U₂ u`), `B₀ := histWrap (restart u) lab` its history wrapper;
* the input `e` enters only as the length `L e = 1 + 5 · inputNum e` of an increment chain glued
  into `B₀` from `bnd hole` to `bnd back` (`RcwaTotalityGlue`);
* `RcwaTotalityCompile` numbers `godel` of the glued wrapper computably in `L` and doubles it.

So `F e := G (L e)`, valid, with all sources halting iff the glued restart machine is mortal
(`godel_mortal_iff`, `glueH_mortal_iff`), iff `φ_e` is total (`mortal_iff_total`).

Corollaries, all hypothesis-free: Theorem C(1) as a computable family of `{2,3}`-slope RCWA
permutations of `ℤ` with one orbit iff `φ_e` is total and infinitely many otherwise
(`orbit_count_family'`), "one orbit" neither r.e. nor co-r.e. on exact bijective tables
(`oneOrbit_not_re'`, `oneOrbit_not_coRE'`), and neither "one orbit" nor "finitely many orbits"
computable (`not_computable_oneOrbit'`, `not_computable_finiteOrbits'`).
-/

namespace CollatzMoonshot.RcwaTotality

open CollatzMoonshot.CounterMachine CollatzMoonshot.RcwaHalting
open CollatzMoonshot.RcwaOrbitCount
open CollatzMoonshot.RcwaSameOrbit (Machine RcwaTable)

/-- Injective rule labels `≥ 1` for a finite machine type. -/
theorem exists_lab (Q ι : Type) [Fintype Q] [Fintype ι] [DecidableEq Q] [DecidableEq ι] :
    ∃ (K : ℕ) (lab : Quad Q ι → Fin K), (∀ ρ, 1 ≤ (lab ρ).val) ∧ Function.Injective lab := by
  refine ⟨Fintype.card (Quad Q ι) + 1, fun ρ => ⟨Fintype.equivFin (Quad Q ι) ρ + 1, by
    have := (Fintype.equivFin (Quad Q ι) ρ).isLt; omega⟩, fun ρ => by simp, fun ρ ρ' h => ?_⟩
  simp only [Fin.mk.injEq, Nat.add_right_cancel_iff] at h
  exact (Fintype.equivFin _).injective (Fin.ext h)

/-- Distinct primes for finitely many counters. -/
theorem exists_primeData (ι : Type) [Fintype ι] : ∃ (p : ι → ℕ) (N : ℕ), PrimeData p N := by
  let p : ι → ℕ := fun c => Nat.nth Nat.Prime (Fintype.equivFin ι c)
  exact ⟨p, ∑ c, p c, fun c => Nat.prime_nth_prime _,
    fun c c' h => (Fintype.equivFin _).injective
      (Fin.ext (Nat.nth_injective Nat.infinite_setOfPred_prime h)),
    fun c => Finset.single_le_sum (f := p) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)⟩

/-- **The totality family.**  A computable family of valid machines whose sources all halt iff
`φ_e` is total. -/
theorem totalityFamily : TotalityFamily := by
  classical
  obtain ⟨u, hu⟩ := exists_universal₂
  have := finite_aState u
  have : Fintype (AState u) := Fintype.ofFinite _
  obtain ⟨K, lab, hlab, hinj⟩ := exists_lab (AState u) ACtr
  obtain ⟨p, N, hp⟩ := exists_primeData (HCtr ACtr)
  obtain ⟨G, hG, hGL⟩ := exists_computable_compile N (histWrap (restart u) lab) (.bnd .hole)
    (.bnd .back) (.val (.sim (some Turing.PartrecToTM2.K'.main))) p
  have hL : Computable fun e => 1 + 5 * CounterMachineUniversal.inputNum e :=
    Primrec.nat_add.to_comp.comp (Computable.const 1)
      (Primrec.nat_mul.to_comp.comp (Computable.const 5)
        CounterMachineUniversal.computable_inputNum)
  refine ⟨fun e => G (1 + 5 * CounterMachineUniversal.inputNum e), hG.comp hL, fun e => ?_⟩
  have hd := glueH_det (lab := lab) (back := AState.back)
    (i := ACtr.sim (some Turing.PartrecToTM2.K'.main))
    (L := 1 + 5 * CounterMachineUniversal.inputNum e) (restart_det u) (restart_src_ne_hole u)
  have hr := glueH_rev (hole := AState.hole) (i := ACtr.sim (some Turing.PartrecToTM2.K'.main))
    (L := 1 + 5 * CounterMachineUniversal.inputNum e) (restart_det u) (fun ρ _ => hlab ρ)
    (fun ρ _ ρ' _ h => hinj h) (restart_normalAt_back u)
  have hm := glueH_revMortal (lab := lab) (i := ACtr.sim (some Turing.PartrecToTM2.K'.main))
    (L := 1 + 5 * CounterMachineUniversal.inputNum e) (restart_det u) (fun ρ _ => hlab ρ)
    (show (AState.hole : AState u) ≠ AState.back by intro h; cases h)
  obtain ⟨hv, hs⟩ := hGL _ (godel_det hd hr hp) (godel_rev hd hr hp)
    (godel_revMortal hd hr hp hm)
  refine ⟨hv, hs.trans ?_⟩
  rw [godel_mortal_iff hd hr hp, glueH_mortal_iff (restart_det u) (restart_src_ne_hole u)]
  exact mortal_iff_total hu e

/-- Mortality of valid machines is undecidable. -/
theorem mortalityUndecidable : MortalityUndecidable :=
  mortalityUndecidable_of_totalityFamily totalityFamily

/-- **Theorem C(1), hypothesis-free.**  A computable `e ↦ T e` of exact tables whose maps are
permutations of `ℤ` (all slopes in `2^ℤ 3^ℤ`) with one orbit if `φ_e` is total and infinitely
many otherwise. -/
theorem orbit_count_family' :
    ∃ T : ℕ → RcwaTable, Computable T ∧ ∀ e, (T e).Exact ∧
      ∃ hb : Function.Bijective (T e).eval,
        (OneOrbit (Equiv.ofBijective _ hb) ↔ Total e) ∧
          (¬ Total e → Infinite (RcwaMachine.Orbits (Equiv.ofBijective _ hb))) :=
  orbit_count_family totalityFamily

/-- **"One orbit" is not r.e.** on exact bijective tables. -/
theorem oneOrbit_not_re' :
    ¬ ∃ P : RcwaTable → Prop, REPred P ∧
      ∀ (T : RcwaTable), T.Exact → ∀ hb : Function.Bijective T.eval,
        (P T ↔ OneOrbit (Equiv.ofBijective T.eval hb)) :=
  oneOrbit_not_re totalityFamily

/-- **"More than one orbit" is not r.e.** on exact bijective tables. -/
theorem oneOrbit_not_coRE' :
    ¬ ∃ P : RcwaTable → Prop, REPred P ∧
      ∀ (T : RcwaTable), T.Exact → ∀ hb : Function.Bijective T.eval,
        (P T ↔ ¬ OneOrbit (Equiv.ofBijective T.eval hb)) :=
  oneOrbit_not_coRE totalityFamily

/-- **"One orbit" is undecidable** on exact bijective tables. -/
theorem not_computable_oneOrbit' :
    ¬ ∃ g : RcwaTable → Bool, Computable g ∧
      ∀ (T : RcwaTable), T.Exact → ∀ hb : Function.Bijective T.eval,
        (g T = true ↔ OneOrbit (Equiv.ofBijective T.eval hb)) :=
  not_computable_oneOrbit mortalityUndecidable

/-- **"Finitely many orbits" is undecidable** on exact bijective tables. -/
theorem not_computable_finiteOrbits' :
    ¬ ∃ g : RcwaTable → Bool, Computable g ∧
      ∀ (T : RcwaTable), T.Exact → ∀ hb : Function.Bijective T.eval,
        (g T = true ↔ Finite (RcwaMachine.Orbits (Equiv.ofBijective T.eval hb))) :=
  not_computable_finiteOrbits mortalityUndecidable

end CollatzMoonshot.RcwaTotality
