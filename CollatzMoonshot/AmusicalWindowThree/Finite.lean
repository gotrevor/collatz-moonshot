/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalEscape
import CollatzMoonshot.AmusicalWindowThree.Certificate

/-! Computable finite objects used by the window-three reversor certificate. -/

namespace CollatzMoonshot.Amusical.WindowThreeFinite

open WindowThreeCertificate

local instance finiteDecidableForall {A : Type} [Fintype A] {p : A → Prop}
    [DecidablePred p] : Decidable (∀ a, p a) :=
  Fintype.decidableForallFintype

local instance finiteDecidableExists {A : Type} [Fintype A] {p : A → Prop}
    [DecidablePred p] : Decidable (∃ a, p a) :=
  Fintype.decidableExistsFintype

abbrev WindowConstraint := Block × Symbol

def knownCycleList : List ℤ :=
  [0, 1, 2, 3, 4, 5, 6, 7, 9, 44, 59, 62, 66, 70, 74, 79, 83, 93, 99, 105, 111]

def signedKnownCycleList : List ℤ :=
  (knownCycleList ++ knownCycleList.map fun n => -n).dedup

def HasBoundedExactAmusicalPeriod (p : ℕ) (n : ℤ) : Prop :=
  amusical^[p] n = n ∧
    ∀ q : Fin p, q.val = 0 ∨ amusical^[q.val] n ≠ n

instance (p : ℕ) (n : ℤ) : Decidable (HasBoundedExactAmusicalPeriod p n) := by
  unfold HasBoundedExactAmusicalPeriod
  exact instDecidableAnd

def exactPeriodCandidates (p : ℕ) : List ℤ :=
  signedKnownCycleList.filter fun n => decide (HasBoundedExactAmusicalPeriod p n)

def OrbitsDisjoint (p : ℕ) (x y : ℤ) : Prop :=
  ∀ j k : Fin p, amusicalInv^[j.val] x ≠ amusicalInv^[k.val] y

instance (p : ℕ) (x y : ℤ) : Decidable (OrbitsDisjoint p x y) := by
  unfold OrbitsDisjoint
  exact @Fintype.decidableForallFintype (Fin p)
    (fun j => ∀ k : Fin p, amusicalInv^[j.val] x ≠ amusicalInv^[k.val] y)
    (fun _ => Fintype.decidableForallFintype) inferInstance

def pairAssignments (p : ℕ) : List (ℤ × ℤ) :=
  (exactPeriodCandidates p).flatMap fun x =>
    ((exactPeriodCandidates p).filter fun y => decide (OrbitsDisjoint p x y)).map
      fun y => (x, y)

def fixedAssignments : List ((ℤ × ℤ) × ℤ) :=
  ((exactPeriodCandidates 1).flatMap fun x =>
    (exactPeriodCandidates 1).flatMap fun y =>
      (exactPeriodCandidates 1).map fun z => ((x, y), z)).filter fun a =>
        decide (OrbitsDisjoint 1 a.1.1 a.1.2 ∧
          OrbitsDisjoint 1 a.1.1 a.2 ∧ OrbitsDisjoint 1 a.1.2 a.2)

def cycleWindow (n : ℤ) : Block :=
  (stepSym (amusicalInv n), stepSym n, stepSym (amusical n))

def cycleConstraints (p : ℕ) (source target : ℤ) : List WindowConstraint :=
  (List.range p).map fun j =>
    (cycleWindow (amusical^[j] source), stepSym (amusicalInv^[j] target))

def fixedConstraints (a : (ℤ × ℤ) × ℤ) : List WindowConstraint :=
  cycleConstraints 1 0 a.1.1 ++
    cycleConstraints 1 1 a.1.2 ++ cycleConstraints 1 (-1) a.2

def pairConstraints (p : ℕ) (x y : ℤ) (a : ℤ × ℤ) :
    List WindowConstraint :=
  cycleConstraints p x a.1 ++ cycleConstraints p y a.2

def ConstraintsConsistent (cs : List WindowConstraint) : Prop :=
  cs.Pairwise fun x y => x.1 = y.1 → x.2 = y.2

instance : DecidableRel (fun x y : WindowConstraint => x.1 = y.1 → x.2 = y.2) :=
  fun _ _ => inferInstance

instance (cs : List WindowConstraint) : Decidable (ConstraintsConsistent cs) := by
  unfold ConstraintsConsistent
  infer_instance

def evalBlock (f : Symbol → Symbol → Symbol → Symbol) (b : Block) : Symbol :=
  f b.1 b.2.1 b.2.2

def fixedConstraintOptions : List (List WindowConstraint) :=
  ((fixedAssignments.map fixedConstraints).filter fun cs =>
    decide (ConstraintsConsistent cs)).dedup

def pairConstraintOptions (p : ℕ) (x y : ℤ) : List (List WindowConstraint) :=
  (((pairAssignments p).map (pairConstraints p x y)).filter fun cs =>
    decide (ConstraintsConsistent cs)).dedup

def constrainedBlockAt (j : Fin 25) : Block :=
  constrainedBlocks.getD j.val (0, 0, 0)

def partialRuleValue (i : Fin 24) (j : Fin 25) : Symbol :=
  (partialRules.getD i.val []).getD j.val 0

def ConstraintsEncodeRule (cs : List WindowConstraint) (i : Fin 24) : Prop :=
  ∀ j : Fin 25, (constrainedBlockAt j, partialRuleValue i j) ∈ cs

instance (cs : List WindowConstraint) (i : Fin 24) :
    Decidable (ConstraintsEncodeRule cs i) := by
  unfold ConstraintsEncodeRule
  exact Fintype.decidableForallFintype

instance (cs : List WindowConstraint) :
    Decidable (∃ i : Fin 24, ConstraintsEncodeRule cs i) :=
  Fintype.decidableExistsFintype

def constrainedIndex (a b c : Symbol) : Fin 25 :=
  let k := 9 * a.val + 3 * b.val + c.val
  ⟨if k < 14 then k else if k < 25 then k - 1 else 24, by
    have ha := a.isLt
    have hb := b.isLt
    have hc := c.isLt
    by_cases h14 : k < 14
    · simp [h14]
      omega
    · by_cases h25 : k < 25
      · simp [h14, h25]
        omega
      · simp [h14, h25]⟩

def completedRule (i : Fin 24) (x y : Symbol) :
    Symbol → Symbol → Symbol → Symbol := fun a b c =>
  if (a, b, c) = (1, 1, 2) then x
  else if (a, b, c) = (2, 2, 1) then y
  else partialRuleValue i (constrainedIndex a b c)

def combinedConstraints (fixed two five twelve : List WindowConstraint) :
    List WindowConstraint :=
  ((fixed ++ two) ++ five) ++ twelve

end CollatzMoonshot.Amusical.WindowThreeFinite
