/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Obstructions.CatalyticRepair
import CollatzMoonshot.Obstructions.RepairPalette
import CollatzMoonshot.Obstructions.Repair71Data

/-!
# The frozen 71 repair under the restricted palette

`AllowedMove` is the restricted action language: positive-odd quadratic
replacements that preserve `certificateValue`, insertion/removal of the three
fixed units `U2`, `U8`, `U13`, and the fixed cubic `C5 : {5,55,83} <-> {11,13,17}`.
There is deliberately no constructor that inserts an arbitrary value-one word:
the large borrowed word `W` of the catalytic repair has to be *built* out of
the units by legal quadratic moves and then *returned* by reversing that
construction.

The proof is an executable interpreter (`step`, `run`) over the finite action
word `repairCode`, plus a soundness theorem (`step_sound`, `run_sound`) that
turns each accepted interpreter step into an `AllowedMove` constructor.  The
interpreter re-derives availability and legality from the *current* multiset;
the JSON data is only a proposal.
-/

namespace CollatzMoonshot.Obstructions.ArithmeticLifts.RestrictedRepair

abbrev RepairState := ℕ × Multiset ℕ

def allowedUnit (u : RepairState) : Prop :=
  u = (1, {1}) ∨ u = (3, (unitEight : Multiset ℕ)) ∨
    u = (5, (unitThirteen : Multiset ℕ))

inductive AllowedMove : RepairState → RepairState → Prop where
  | quadratic (t : ℕ) (rest : Multiset ℕ) (m : PairMove)
      (h : legalPairMove m.1 m = true) :
      AllowedMove (t, rest + (m.1 : Multiset ℕ)) (t, rest + (m.2 : Multiset ℕ))
  | insert (s : RepairState) (u : RepairState) (h : allowedUnit u) :
      AllowedMove s (s.1 + u.1, s.2 + u.2)
  | erase (s : RepairState) (u : RepairState) (h : allowedUnit u) :
      AllowedMove (s.1 + u.1, s.2 + u.2) s
  | cubic (t : ℕ) (rest : Multiset ℕ) :
      AllowedMove (t, rest + {5,55,83}) (t, rest + {11,13,17})
  | cubicReverse (t : ℕ) (rest : Multiset ℕ) :
      AllowedMove (t, rest + {11,13,17}) (t, rest + {5,55,83})

/-! ## The three allowed units -/

def unitTwos : ℕ → ℕ
  | 0 => 1
  | 1 => 3
  | _ => 5

def unitOdds : ℕ → List ℕ
  | 0 => [1]
  | 1 => unitEight
  | _ => unitThirteen

def unitOf (i : ℕ) : RepairState := (unitTwos i, (unitOdds i : Multiset ℕ))

theorem allowedUnit_unitOf (i : ℕ) : allowedUnit (unitOf i) := by
  match i with
  | 0 => exact Or.inl rfl
  | 1 => exact Or.inr (Or.inl rfl)
  | (_ + 2) => exact Or.inr (Or.inr rfl)

/-! ## Availability: removing an explicit list from a multiset -/

/-- Remove the entries of `l` from `m` one at a time, failing as soon as one of
them is not available.  On success the returned remainder `m'` satisfies
`m' + l = m`, which is exactly the context shape that `AllowedMove` needs. -/
def eraseList (m : Multiset ℕ) : List ℕ → Option (Multiset ℕ)
  | [] => some m
  | a :: t => if a ∈ m then eraseList (m.erase a) t else none

theorem eraseList_spec :
    ∀ (l : List ℕ) (m m' : Multiset ℕ), eraseList m l = some m' →
      m' + (l : Multiset ℕ) = m := by
  intro l
  induction l with
  | nil =>
      intro m m' h
      simp only [eraseList] at h
      rw [← Option.some.inj h]
      simp
  | cons a t ih =>
      intro m m' h
      simp only [eraseList] at h
      split at h
      · rename_i hmem
        have hrest := ih (m.erase a) m' h
        have hcons : ((a :: t : List ℕ) : Multiset ℕ) = a ::ₘ (t : Multiset ℕ) := rfl
        rw [hcons, Multiset.add_cons, hrest, Multiset.cons_erase hmem]
      · exact absurd h (by simp)

/-! ## The interpreter -/

/-- One action of the restricted language, as consumed by `step`. -/
inductive Act where
  | quad : List ℕ → List ℕ → Act
  | ins : ℕ → Act
  | era : ℕ → Act
  | cub : Act
  | cubRev : Act

def decodeAct : List ℕ → Act
  | [a, b, c, d] => Act.quad [a, b] [c, d]
  | [0, i] => Act.ins i
  | [1, i] => Act.era i
  | [3] => Act.cubRev
  | _ => Act.cub

/-- Executable one-step interpreter.  Every branch re-checks legality and
availability against the current state; nothing is taken on faith. -/
def step (s : RepairState) : Act → Option RepairState
  | Act.quad rem inss =>
      if legalPairMove rem (rem, inss) = true then
        (eraseList s.2 rem).map (fun rest => (s.1, rest + (inss : Multiset ℕ)))
      else none
  | Act.ins i => some (s.1 + (unitOf i).1, s.2 + (unitOf i).2)
  | Act.era i =>
      if unitTwos i ≤ s.1 then
        (eraseList s.2 (unitOdds i)).map (fun rest => (s.1 - unitTwos i, rest))
      else none
  | Act.cub => (eraseList s.2 [5, 55, 83]).map (fun rest => (s.1, rest + {11, 13, 17}))
  | Act.cubRev => (eraseList s.2 [11, 13, 17]).map (fun rest => (s.1, rest + {5, 55, 83}))

def run : RepairState → List Act → Option RepairState
  | s, [] => some s
  | s, a :: as => (step s a).bind (fun s' => run s' as)

/-! ## Soundness of the interpreter -/

theorem step_sound {s s' : RepairState} {a : Act} (h : step s a = some s') :
    AllowedMove s s' := by
  obtain ⟨t, m⟩ := s
  cases a with
  | quad rem inss =>
      simp only [step] at h
      split at h
      · rename_i hleg
        rcases hopt : eraseList m rem with _ | rest
        · rw [hopt] at h; simp at h
        · rw [hopt] at h
          simp only [Option.map_some] at h
          have hm : rest + (rem : Multiset ℕ) = m := eraseList_spec rem m rest hopt
          have hmove : AllowedMove (t, rest + ((rem, inss) : PairMove).1)
              (t, rest + ((rem, inss) : PairMove).2) :=
            AllowedMove.quadratic t rest (rem, inss) hleg
          simp only at hmove
          rw [hm] at hmove
          rw [← Option.some.inj h]
          exact hmove
      · exact absurd h (by simp)
  | ins i =>
      rw [← Option.some.inj h]
      exact AllowedMove.insert (t, m) (unitOf i) (allowedUnit_unitOf i)
  | era i =>
      simp only [step] at h
      split at h
      · rename_i hle
        rcases hopt : eraseList m (unitOdds i) with _ | rest
        · rw [hopt] at h; simp at h
        · rw [hopt] at h
          simp only [Option.map_some] at h
          have hm : rest + ((unitOdds i : List ℕ) : Multiset ℕ) = m :=
            eraseList_spec _ m rest hopt
          have hmove : AllowedMove
              ((t - unitTwos i, rest).1 + (unitOf i).1, (t - unitTwos i, rest).2 + (unitOf i).2)
              (t - unitTwos i, rest) :=
            AllowedMove.erase (t - unitTwos i, rest) (unitOf i) (allowedUnit_unitOf i)
          simp only [unitOf] at hmove
          rw [Nat.sub_add_cancel hle, hm] at hmove
          rw [← Option.some.inj h]
          exact hmove
      · exact absurd h (by simp)
  | cub =>
      simp only [step] at h
      rcases hopt : eraseList m [5, 55, 83] with _ | rest
      · rw [hopt] at h; simp at h
      · rw [hopt] at h
        simp only [Option.map_some] at h
        have hm : rest + (([5, 55, 83] : List ℕ) : Multiset ℕ) = m :=
          eraseList_spec _ m rest hopt
        have hmove := AllowedMove.cubic t rest
        rw [show ({5, 55, 83} : Multiset ℕ) = (([5, 55, 83] : List ℕ) : Multiset ℕ) from rfl,
          hm] at hmove
        rw [← Option.some.inj h]
        exact hmove
  | cubRev =>
      simp only [step] at h
      rcases hopt : eraseList m [11, 13, 17] with _ | rest
      · rw [hopt] at h; simp at h
      · rw [hopt] at h
        simp only [Option.map_some] at h
        have hm : rest + (([11, 13, 17] : List ℕ) : Multiset ℕ) = m :=
          eraseList_spec _ m rest hopt
        have hmove := AllowedMove.cubicReverse t rest
        rw [show ({11, 13, 17} : Multiset ℕ) = (([11, 13, 17] : List ℕ) : Multiset ℕ) from rfl,
          hm] at hmove
        rw [← Option.some.inj h]
        exact hmove

theorem run_sound : ∀ (as : List Act) (s s' : RepairState), run s as = some s' →
    Relation.ReflTransGen AllowedMove s s' := by
  intro as
  induction as with
  | nil => intro s s' h; rw [← Option.some.inj h]
  | cons a as ih =>
      intro s s' h
      simp only [run] at h
      rcases hopt : step s a with _ | s₁
      · rw [hopt] at h; simp at h
      · rw [hopt] at h
        simp only [Option.bind_some] at h
        exact Relation.ReflTransGen.head (step_sound hopt) (ih s₁ s' h)

/-! ## The frozen certificate -/

/-- The decoded action word: build `W`, run the 269 main actions, return `W`. -/
def repairActs : List Act := repairCode.map decodeAct

set_option maxRecDepth 8000 in
/-- The interpreter accepts the frozen word and lands exactly on the actual
65-step path certificate of 71, powers of two included. -/
theorem repairActs_run :
    run (16, (certificate71 : Multiset ℕ)) repairActs =
      some (28, ((seventyOnePrefix.filter (fun u => u % 2 == 1) : List ℕ) : Multiset ℕ)) := by
  native_decide

theorem seventyOne_repair_restricted :
    Relation.ReflTransGen AllowedMove
      (16, (certificate71 : Multiset ℕ))
      (28, ((seventyOnePrefix.filter (fun u => u % 2 == 1) : List ℕ) : Multiset ℕ)) :=
  run_sound repairActs _ _ repairActs_run

end CollatzMoonshot.Obstructions.ArithmeticLifts.RestrictedRepair
