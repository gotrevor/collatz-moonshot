import CollatzMoonshot.Obstructions.QuadraticInvariants

namespace CollatzMoonshot.Obstructions.ArithmeticLifts

abbrev PaletteState := ℤ × Multiset ℤ

def paletteIndex (s : PaletteState) : ℤ :=
  5 * s.1 - 3 * (s.2.card : ℤ) - (s.2.count 5 : ℤ) - 2 * (s.2.count 1 : ℤ)

def paletteUnit : PaletteState → Prop
  | s => s = (1, {1}) ∨ s = (3, {19,25,29,55,83}) ∨
      s = (5, {5,7,7,11,17,55,65,83})

def addPalette (s u : PaletteState) : PaletteState := (s.1 + u.1, s.2 + u.2)

theorem paletteIndex_add (s u : PaletteState) :
    paletteIndex (addPalette s u) = paletteIndex s + paletteIndex u := by
  simp only [paletteIndex, addPalette, Multiset.card_add, Multiset.count_add, Nat.cast_add]
  ring

theorem paletteUnit_index {u : PaletteState} (hu : paletteUnit u) : paletteIndex u = 0 := by
  rcases hu with rfl | rfl | rfl <;> native_decide

theorem quadratic_paletteIndex (t : ℤ) {s u : Multiset ℤ} (h : QuadraticMultiStep s u) :
    paletteIndex (t,s) = paletteIndex (t,u) := by
  have h1 := small_generator_count_invariant 1 (by norm_num) (Relation.ReflTransGen.single h)
  have h5 := small_generator_count_invariant 5 (by norm_num) (Relation.ReflTransGen.single h)
  have hcard : s.card = u.card := by
    obtain ⟨a,b,c,d,r,_,_,_,_,_,_,_,_,_,rfl,rfl⟩ := h
    simp
  simp only [paletteIndex, hcard, h1, h5]

inductive PaletteStep : PaletteState → PaletteState → Prop where
  | quadratic {t s u} : QuadraticMultiStep s u → PaletteStep (t,s) (t,u)
  | insert (s) {u} : paletteUnit u → PaletteStep s (addPalette s u)
  | erase (s) {u} : paletteUnit u → PaletteStep (addPalette s u) s

theorem paletteStep_index {s t : PaletteState} (h : PaletteStep s t) :
    paletteIndex s = paletteIndex t := by
  cases h with
  | quadratic h => exact quadratic_paletteIndex _ h
  | insert s hu => rw [paletteIndex_add, paletteUnit_index hu, add_zero]
  | erase s hu => rw [paletteIndex_add, paletteUnit_index hu, add_zero]

theorem paletteReach_index {s t : PaletteState} (h : Relation.ReflTransGen PaletteStep s t) :
    paletteIndex s = paletteIndex t := by
  induction h with
  | refl => rfl
  | tail h step ih => exact ih.trans (paletteStep_index step)

def virtualSeventyOne : PaletteState :=
  (16, {25,19,29,11,17,13,5,355,533,7,7,11,17,55,65,83})

def actualSeventyOne : PaletteState :=
  (28, {71,107,161,121,91,137,103,155,233,175,263,395,593,445,167,251,
    377,283,425,319,479,719,1079,1619,2429,911,1367,2051,3077,577,433,
    325,61,23,35,53,5})


open CollatzMoonshot.FrontB

def seventyOnePrefix : List ℕ := (List.range 65).map (fun j => (tstep^[j]) 71)

/-- The target multiset is the actual 65-step path odd list, with the
displayed number of even edges.  The earlier no-short-path theorem and
65-step hitting certificate supply the separate length obstruction. -/
theorem actualSeventyOne_trace :
    ((seventyOnePrefix.filter (fun u => u % 2 == 0)).length = 28) ∧
    (((seventyOnePrefix.filter (fun u => u % 2 == 1)).map Int.ofNat : Multiset ℤ) =
      actualSeventyOne.2) ∧
    certificateValue 28 (seventyOnePrefix.filter (fun u => u % 2 == 1)) = 71 ∧
    (tstep^[65]) 71 = 1 := by
  native_decide

theorem seventy_one_indices :
    paletteIndex virtualSeventyOne = 31 ∧ paletteIndex actualSeventyOne = 28 := by
  native_decide

theorem initial_palette_cannot_repair_seventy_one :
    ¬ Relation.ReflTransGen PaletteStep virtualSeventyOne actualSeventyOne := by
  intro h
  have heq := paletteReach_index h
  have hi := seventy_one_indices
  omega

theorem essential_cubic_changes_index :
    paletteIndex (0, {11,13,17}) - paletteIndex (0, {5,55,83}) = 1 ∧
    paletteIndex (5, {7,7,11,11,13,17,17,65}) = 1 := by
  native_decide

end CollatzMoonshot.Obstructions.ArithmeticLifts
