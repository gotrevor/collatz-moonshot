/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalWindowThree

/-!
# Finite certificate for the window-two commuting tables

The commuting map sends the cycles through `44` and `-44` to periodic points of period
dividing twelve.  Their two-symbol windows restrict the local table to the seven expected
possibilities.  The finite checks below range only over indexed cycle data; in particular, they
never enumerate the function type `Fin 3 → Fin 3 → Fin 3`.
-/

namespace CollatzMoonshot.Amusical

def windowTwoPeriodicPoint : Fin 31 → ℤ :=
  ![0, 1, -1, 2, -2, 3, -3, 44, -44, 59, -59, 62, -62, 66, -66, 70,
    -70, 74, -74, 79, -79, 83, -83, 93, -93, 99, -99, 105, -105, 111, -111]

private def periodicTwelveWord : Fin 31 → Fin 12 → Fin 3 :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
    ![2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2],
    ![0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2],
    ![0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    ![2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0],
    ![1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0],
    ![0, 0, 2, 0, 2, 2, 0, 1, 0, 1, 2, 2],
    ![0, 0, 1, 0, 1, 1, 0, 2, 0, 2, 1, 1],
    ![2, 0, 0, 2, 0, 2, 2, 0, 1, 0, 1, 2],
    ![1, 0, 0, 1, 0, 1, 1, 0, 2, 0, 2, 1],
    ![0, 1, 0, 1, 2, 2, 0, 0, 2, 0, 2, 2],
    ![0, 2, 0, 2, 1, 1, 0, 0, 1, 0, 1, 1],
    ![0, 2, 0, 2, 2, 0, 1, 0, 1, 2, 2, 0],
    ![0, 1, 0, 1, 1, 0, 2, 0, 2, 1, 1, 0],
    ![0, 1, 2, 2, 0, 0, 2, 0, 2, 2, 0, 1],
    ![0, 2, 1, 1, 0, 0, 1, 0, 1, 1, 0, 2],
    ![0, 2, 2, 0, 1, 0, 1, 2, 2, 0, 0, 2],
    ![0, 1, 1, 0, 2, 0, 2, 1, 1, 0, 0, 1],
    ![2, 2, 0, 0, 2, 0, 2, 2, 0, 1, 0, 1],
    ![1, 1, 0, 0, 1, 0, 1, 1, 0, 2, 0, 2],
    ![2, 0, 1, 0, 1, 2, 2, 0, 0, 2, 0, 2],
    ![1, 0, 2, 0, 2, 1, 1, 0, 0, 1, 0, 1],
    ![1, 0, 1, 2, 2, 0, 0, 2, 0, 2, 2, 0],
    ![2, 0, 2, 1, 1, 0, 0, 1, 0, 1, 1, 0],
    ![2, 0, 2, 2, 0, 1, 0, 1, 2, 2, 0, 0],
    ![1, 0, 1, 1, 0, 2, 0, 2, 1, 1, 0, 0],
    ![1, 2, 2, 0, 0, 2, 0, 2, 2, 0, 1, 0],
    ![2, 1, 1, 0, 0, 1, 0, 1, 1, 0, 2, 0],
    ![2, 2, 0, 1, 0, 1, 2, 2, 0, 0, 2, 0],
    ![1, 1, 0, 2, 0, 2, 1, 1, 0, 0, 1, 0]]

private theorem periodicTwelveWord_spec :
    ∀ j : Fin 31, ∀ i : Fin 12,
      stepSym (amusical^[i] (windowTwoPeriodicPoint j)) = periodicTwelveWord j i := by
  decide +kernel

private def cycle44First : Fin 12 → Fin 3 :=
  ![0, 0, 2, 0, 2, 2, 0, 1, 0, 1, 2, 2]

private def cycle44Second : Fin 12 → Fin 3 :=
  ![0, 2, 0, 2, 2, 0, 1, 0, 1, 2, 2, 0]

private def cycleNeg44First : Fin 12 → Fin 3 :=
  ![0, 0, 1, 0, 1, 1, 0, 2, 0, 2, 1, 1]

private def cycleNeg44Second : Fin 12 → Fin 3 :=
  ![0, 1, 0, 1, 1, 0, 2, 0, 2, 1, 1, 0]

private theorem cycle44Window_spec : ∀ i : Fin 12,
    stepSym (amusical^[i] 44) = cycle44First i ∧
      stepSym (amusical^[i + 1] 44) = cycle44Second i := by
  decide +kernel

private theorem cycleNeg44Window_spec : ∀ i : Fin 12,
    stepSym (amusical^[i] (-44)) = cycleNeg44First i ∧
      stepSym (amusical^[i + 1] (-44)) = cycleNeg44Second i := by
  decide +kernel

private def applyWindowTable (f : Fin 3 → Fin 3 → Fin 3)
    (p : Fin 3 × Fin 3) : Fin 3 :=
  f p.1 p.2

private def cycle44Window (i : Fin 12) : Fin 3 × Fin 3 :=
  (cycle44First i, cycle44Second i)

private def cycleNeg44Window (i : Fin 12) : Fin 3 × Fin 3 :=
  (cycleNeg44First i, cycleNeg44Second i)

private def windowRepeatLeft : Fin 5 → Fin 12 :=
  ![1, 2, 2, 4, 6]

private def windowRepeatRight : Fin 5 → Fin 12 :=
  ![3, 5, 11, 10, 8]

private theorem cycle44Window_repeat (k : Fin 5) :
    cycle44Window (windowRepeatLeft k) = cycle44Window (windowRepeatRight k) := by
  fin_cases k <;> rfl

private theorem cycleNeg44Window_repeat (k : Fin 5) :
    cycleNeg44Window (windowRepeatLeft k) =
      cycleNeg44Window (windowRepeatRight k) := by
  fin_cases k <;> rfl

private def windowCrossPlus : Fin 5 → Fin 12 :=
  ![0, 6, 1, 7, 2]

private def windowCrossMinus : Fin 5 → Fin 12 :=
  ![0, 1, 6, 2, 7]

private theorem cycleWindow_cross (k : Fin 5) :
    cycle44Window (windowCrossPlus k) = cycleNeg44Window (windowCrossMinus k) := by
  fin_cases k <;> decide +kernel

private theorem cycle44Window_four : cycle44Window 4 = (2, 2) := by
  rfl

private theorem cycle44_closed : amusical^[12] 44 = 44 := by
  norm_num [amusical, Function.iterate_succ_apply']

private theorem cycleNeg44_closed : amusical^[12] (-44) = -44 := by
  norm_num [amusical, Function.iterate_succ_apply']

private theorem commute_iterate {g : ℤ → ℤ}
    (hg : ∀ n, g (amusical n) = amusical (g n)) :
    ∀ k n, g (amusical^[k] n) = amusical^[k] (g n) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      intro n
      rw [Function.iterate_succ_apply', hg, ih, Function.iterate_succ_apply']

private theorem table_on_iterate (f : Fin 3 → Fin 3 → Fin 3) {g : ℤ → ℤ}
    (hg : ∀ n, g (amusical n) = amusical (g n))
    (hloc : ∀ n, stepSym (g n) = f (stepSym n) (stepSym (amusical n)))
    (x : ℤ) (i : ℕ) :
    stepSym (amusical^[i] (g x)) =
      f (stepSym (amusical^[i] x)) (stepSym (amusical^[i + 1] x)) := by
  calc
    stepSym (amusical^[i] (g x)) = stepSym (g (amusical^[i] x)) := by
      rw [commute_iterate hg]
    _ = f (stepSym (amusical^[i] x)) (stepSym (amusical^[i + 1] x)) := by
      simpa only [Function.iterate_succ_apply'] using hloc (amusical^[i] x)

private def windowTwoStateSym : Fin 7 → Fin 3 :=
  ![0, 2, 1, 2, 1, 1, 2]

private def windowTwoStatePlus : Fin 7 → Fin 31 :=
  ![0, 7, 8, 13, 14, 1, 2]

private def windowTwoStateMinus : Fin 7 → Fin 31 :=
  ![0, 8, 7, 14, 13, 1, 2]

private def windowTwoPlusCompatible (s : Fin 3) (j : Fin 31) : Prop :=
  periodicTwelveWord j 4 = s ∧
    periodicTwelveWord j 1 = periodicTwelveWord j 3 ∧
    periodicTwelveWord j 2 = periodicTwelveWord j 5 ∧
    periodicTwelveWord j 2 = periodicTwelveWord j 11 ∧
    periodicTwelveWord j 4 = periodicTwelveWord j 10 ∧
    periodicTwelveWord j 6 = periodicTwelveWord j 8

private theorem windowTwoPlusCompatible_classify : ∀ (s : Fin 3) (j : Fin 31),
    windowTwoPlusCompatible s j →
      ∃ c : Fin 7, s = windowTwoStateSym c ∧ j = windowTwoStatePlus c := by
  unfold windowTwoPlusCompatible windowTwoStateSym windowTwoStatePlus
  unfold periodicTwelveWord
  decide +kernel

private theorem windowTwoMinusCompatible_classify : ∀ (c : Fin 7) (j : Fin 31),
    periodicTwelveWord j 1 = periodicTwelveWord j 3 →
    periodicTwelveWord j 2 = periodicTwelveWord j 5 →
    periodicTwelveWord j 2 = periodicTwelveWord j 11 →
    periodicTwelveWord j 4 = periodicTwelveWord j 10 →
    periodicTwelveWord j 6 = periodicTwelveWord j 8 →
    periodicTwelveWord (windowTwoStatePlus c) 0 = periodicTwelveWord j 0 →
    periodicTwelveWord (windowTwoStatePlus c) 6 = periodicTwelveWord j 1 →
    periodicTwelveWord (windowTwoStatePlus c) 1 = periodicTwelveWord j 6 →
    periodicTwelveWord (windowTwoStatePlus c) 7 = periodicTwelveWord j 2 →
    periodicTwelveWord (windowTwoStatePlus c) 2 = periodicTwelveWord j 7 →
    j = windowTwoStateMinus c := by
  unfold windowTwoStatePlus windowTwoStateMinus periodicTwelveWord
  decide +kernel

private def windowTwoCandidate : Fin 7 → Fin 3 → Fin 3 → Fin 3 :=
  ![(fun _ _ => 0), (fun a _ => a), (fun a _ => -a), (fun _ b => b),
    (fun _ b => -b), (fun _ _ => 1), (fun _ _ => 2)]

private def windowTwoUsePositive : Fin 3 → Fin 3 → Bool :=
  ![![true, true, true], ![true, false, true], ![true, false, true]]

private def windowTwoInputIndex : Fin 3 → Fin 3 → Fin 12 :=
  ![![0, 6, 1], ![7, 4, 9], ![2, 9, 4]]

private def windowTwoSourceFirst (a b : Fin 3) : Fin 3 :=
  if windowTwoUsePositive a b = true then
    cycle44First (windowTwoInputIndex a b)
  else
    cycleNeg44First (windowTwoInputIndex a b)

private def windowTwoSourceSecond (a b : Fin 3) : Fin 3 :=
  if windowTwoUsePositive a b = true then
    cycle44Second (windowTwoInputIndex a b)
  else
    cycleNeg44Second (windowTwoInputIndex a b)

private def windowTwoSourceOutput (c : Fin 7) (a b : Fin 3) : Fin 3 :=
  if windowTwoUsePositive a b = true then
    periodicTwelveWord (windowTwoStatePlus c) (windowTwoInputIndex a b)
  else
    periodicTwelveWord (windowTwoStateMinus c) (windowTwoInputIndex a b)

private theorem windowTwoSourceFirst_spec :
    ∀ a b, windowTwoSourceFirst a b = a := by
  intro a b
  fin_cases a <;> fin_cases b <;> rfl

private theorem windowTwoSourceSecond_spec :
    ∀ a b, windowTwoSourceSecond a b = b := by
  intro a b
  fin_cases a <;> fin_cases b <;> rfl

private theorem windowTwoSourceOutput_spec :
    ∀ c a b, windowTwoSourceOutput c a b = windowTwoCandidate c a b := by
  intro c a b
  fin_cases c <;> fin_cases a <;> fin_cases b <;> rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- A commuting two-symbol local rule is constant, signed projection, or signed successor. -/
theorem windowTwo_table_classify
    (hperiodic : ∀ y, amusical^[12] y = y →
      ∃ j : Fin 31, y = windowTwoPeriodicPoint j)
    (f : Fin 3 → Fin 3 → Fin 3) {g : ℤ → ℤ}
    (hg : ∀ n, g (amusical n) = amusical (g n))
    (hloc : ∀ n, stepSym (g n) = f (stepSym n) (stepSym (amusical n))) :
    f = (fun _ _ => 0) ∨ f = (fun a _ => a) ∨ f = (fun a _ => -a) ∨
      f = (fun _ b => b) ∨ f = (fun _ b => -b) ∨ f = (fun _ _ => 1) ∨
      f = (fun _ _ => 2) := by
  have hpfix : amusical^[12] (g 44) = g 44 := by
    rw [← commute_iterate hg, cycle44_closed]
  obtain ⟨jp, hjp⟩ := hperiodic (g 44) hpfix
  have hnfix : amusical^[12] (g (-44)) = g (-44) := by
    rw [← commute_iterate hg, cycleNeg44_closed]
  obtain ⟨jn, hjn⟩ := hperiodic (g (-44)) hnfix
  have hs := hloc (-1)
  change stepSym (g (-1)) = f 2 2 at hs
  have hp : ∀ i : Fin 12, periodicTwelveWord jp i =
      applyWindowTable f (cycle44Window i) := by
    intro i
    calc
      periodicTwelveWord jp i =
          stepSym (amusical^[i] (windowTwoPeriodicPoint jp)) :=
        (periodicTwelveWord_spec jp i).symm
      _ = stepSym (amusical^[i] (g 44)) := by rw [hjp]
      _ = f (stepSym (amusical^[i] 44)) (stepSym (amusical^[i + 1] 44)) :=
        table_on_iterate f hg hloc 44 i
      _ = applyWindowTable f (cycle44Window i) := by
        rw [(cycle44Window_spec i).1, (cycle44Window_spec i).2]
        rfl
  have hn : ∀ i : Fin 12, periodicTwelveWord jn i =
      applyWindowTable f (cycleNeg44Window i) := by
    intro i
    calc
      periodicTwelveWord jn i =
          stepSym (amusical^[i] (windowTwoPeriodicPoint jn)) :=
        (periodicTwelveWord_spec jn i).symm
      _ = stepSym (amusical^[i] (g (-44))) := by rw [hjn]
      _ = f (stepSym (amusical^[i] (-44)))
          (stepSym (amusical^[i + 1] (-44))) :=
        table_on_iterate f hg hloc (-44) i
      _ = applyWindowTable f (cycleNeg44Window i) := by
        rw [(cycleNeg44Window_spec i).1, (cycleNeg44Window_spec i).2]
        rfl
  have hplus : windowTwoPlusCompatible (stepSym (g (-1))) jp := by
    have hpRepeat (k : Fin 5) :
        periodicTwelveWord jp (windowRepeatLeft k) =
          periodicTwelveWord jp (windowRepeatRight k) :=
      (hp (windowRepeatLeft k)).trans <|
        (congrArg (applyWindowTable f) (cycle44Window_repeat k)).trans <|
          (hp (windowRepeatRight k)).symm
    refine ⟨?_, hpRepeat 0, hpRepeat 1, hpRepeat 2, hpRepeat 3, hpRepeat 4⟩
    exact (hp 4).trans <|
      (congrArg (applyWindowTable f) cycle44Window_four).trans hs.symm
  obtain ⟨c, hsc, hjpc⟩ :=
    windowTwoPlusCompatible_classify (stepSym (g (-1))) jp hplus
  have hpState := hp
  rw [hjpc] at hpState
  have hjnc : jn = windowTwoStateMinus c := by
    apply windowTwoMinusCompatible_classify c jn
    all_goals first
      | exact (hn (windowRepeatLeft 0)).trans <|
          (congrArg (applyWindowTable f) (cycleNeg44Window_repeat 0)).trans <|
            (hn (windowRepeatRight 0)).symm
      | exact (hn (windowRepeatLeft 1)).trans <|
          (congrArg (applyWindowTable f) (cycleNeg44Window_repeat 1)).trans <|
            (hn (windowRepeatRight 1)).symm
      | exact (hn (windowRepeatLeft 2)).trans <|
          (congrArg (applyWindowTable f) (cycleNeg44Window_repeat 2)).trans <|
            (hn (windowRepeatRight 2)).symm
      | exact (hn (windowRepeatLeft 3)).trans <|
          (congrArg (applyWindowTable f) (cycleNeg44Window_repeat 3)).trans <|
            (hn (windowRepeatRight 3)).symm
      | exact (hn (windowRepeatLeft 4)).trans <|
          (congrArg (applyWindowTable f) (cycleNeg44Window_repeat 4)).trans <|
            (hn (windowRepeatRight 4)).symm
      | exact (hpState (windowCrossPlus 0)).trans <|
          (congrArg (applyWindowTable f) (cycleWindow_cross 0)).trans <|
            (hn (windowCrossMinus 0)).symm
      | exact (hpState (windowCrossPlus 1)).trans <|
          (congrArg (applyWindowTable f) (cycleWindow_cross 1)).trans <|
            (hn (windowCrossMinus 1)).symm
      | exact (hpState (windowCrossPlus 2)).trans <|
          (congrArg (applyWindowTable f) (cycleWindow_cross 2)).trans <|
            (hn (windowCrossMinus 2)).symm
      | exact (hpState (windowCrossPlus 3)).trans <|
          (congrArg (applyWindowTable f) (cycleWindow_cross 3)).trans <|
            (hn (windowCrossMinus 3)).symm
      | exact (hpState (windowCrossPlus 4)).trans <|
          (congrArg (applyWindowTable f) (cycleWindow_cross 4)).trans <|
            (hn (windowCrossMinus 4)).symm
  have hf : f = windowTwoCandidate c := by
    funext a b
    calc
      f a b = f (windowTwoSourceFirst a b) (windowTwoSourceSecond a b) := by
        rw [windowTwoSourceFirst_spec, windowTwoSourceSecond_spec]
      _ = windowTwoSourceOutput c a b := by
        unfold windowTwoSourceFirst windowTwoSourceSecond windowTwoSourceOutput
        by_cases hpos : windowTwoUsePositive a b = true
        · simp only [hpos, if_true]
          simpa only [applyWindowTable, cycle44Window, hjpc] using
            (hp (windowTwoInputIndex a b)).symm
        · simp only [hpos, Bool.false_eq_true, if_false]
          simpa only [applyWindowTable, cycleNeg44Window, hjnc] using
            (hn (windowTwoInputIndex a b)).symm
      _ = windowTwoCandidate c a b := windowTwoSourceOutput_spec c a b
  fin_cases c
  · left
    simpa [windowTwoCandidate] using hf
  · right; left
    simpa [windowTwoCandidate] using hf
  · right; right; left
    simpa [windowTwoCandidate] using hf
  · right; right; right; left
    simpa [windowTwoCandidate] using hf
  · right; right; right; right; left
    simpa [windowTwoCandidate] using hf
  · right; right; right; right; right; left
    simpa [windowTwoCandidate] using hf
  · right; right; right; right; right; right
    simpa [windowTwoCandidate] using hf

end CollatzMoonshot.Amusical
