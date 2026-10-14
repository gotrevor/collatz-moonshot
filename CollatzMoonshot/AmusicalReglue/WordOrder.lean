/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-! A key into a linear order with finite intervals and no ends enumerates its domain by `ℤ`. -/

namespace CollatzMoonshot.Amusical

theorem exists_equiv_int_of_key {C L : Type*} [LinearOrder L] (κ : C → L)
    (hinj : Function.Injective κ) (hfin : ∀ a b : C, {c | κ a ≤ κ c ∧ κ c ≤ κ b}.Finite)
    (hmax : ∀ a, ∃ b, κ a < κ b) (hmin : ∀ a, ∃ b, κ b < κ a) [hne : Nonempty C] :
    ∃ e : C ≃ ℤ, ∀ a b, κ a < κ b ↔ e a < e b := by
  let _ : LinearOrder C := LinearOrder.lift' κ hinj
  let _ : LocallyFiniteOrder C := LocallyFiniteOrder.ofFiniteIcc fun a b => hfin a b
  let _ : SuccOrder C := LinearLocallyFiniteOrder.succOrder C
  let _ : PredOrder C := LinearLocallyFiniteOrder.predOrder C
  have _ : NoMaxOrder C := ⟨fun a => hmax a⟩
  have _ : NoMinOrder C := ⟨fun a => hmin a⟩
  let o : C ≃o ℤ := orderIsoIntOfLinearSuccPredArch
  exact ⟨o.toEquiv, fun a b => o.lt_iff_lt.symm⟩

end CollatzMoonshot.Amusical
