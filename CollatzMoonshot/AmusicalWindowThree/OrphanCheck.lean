/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalWindowThree.CycleCheck

/-! Nine-state automaton check of the 216 window-three orphan words. -/

namespace CollatzMoonshot.Amusical.WindowThreeFinite

open WindowThreeCertificate

def advancePairs (f : Symbol → Symbol → Symbol → Symbol) (out : Symbol)
    (states : Finset (Symbol × Symbol)) : Finset (Symbol × Symbol) :=
  ((states ×ˢ (Finset.univ : Finset Symbol)).filter fun x =>
      f x.2 x.1.2 x.1.1 = out).image fun x => (x.1.2, x.2)

def reachablePairs (f : Symbol → Symbol → Symbol → Symbol)
    (u : List Symbol) : Finset (Symbol × Symbol) :=
  u.foldl (fun states out => advancePairs f out states) Finset.univ

def orphanWordAt (i : Fin 24) (x y : Symbol) : List Symbol :=
  (orphanWords.getD i.val []).getD (3 * x.val + y.val) []

local instance orphanFiniteDecidableForall {A : Type} [Fintype A] {p : A → Prop}
    [DecidablePred p] : Decidable (∀ a, p a) :=
  Fintype.decidableForallFintype

set_option maxRecDepth 10000 in
theorem orphanCertificateCheck :
    ∀ i : Fin 24, ∀ x y : Symbol,
      reachablePairs (completedRule i x y) (orphanWordAt i x y) = ∅ := by
  decide +kernel

end CollatzMoonshot.Amusical.WindowThreeFinite
