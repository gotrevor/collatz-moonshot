/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalCycleBound.MinBound

/-!
# A kernel checker for the orbit-minimum search

`searchCheck X H` checks, for every `n ∈ [1, X]` outside `{1, 2, 4, 44}`, that `n` dips below
itself within `H` steps forward or backward, or that its first `H` forward iterates avoid both
`n` and `V^H n`.  `searchCheck_sound` turns a `true` into the unfolded body of
`CycleMinSearch X H`.  The orbit is run in `ℕ` (`natU`, `natV`), with the same kernel-friendly
shape as `minBoundCheck`: bare `Nat.rec` recursion and `Nat` primitives only.
-/

namespace CollatzMoonshot.Amusical

/-- `U` on `ℕ`, written with kernel-accelerated primitives. -/
def natU (x : ℕ) : ℕ :=
  cond (Nat.beq (Nat.mod x 2) 0) (Nat.mul 3 (Nat.div x 2))
    (cond (Nat.beq (Nat.mod x 4) 1) (Nat.add (Nat.mul 3 (Nat.div x 4)) 1)
      (Nat.add (Nat.mul 3 (Nat.div x 4)) 2))

/-- `V = U⁻¹` on `ℕ`, written with kernel-accelerated primitives. -/
def natV (x : ℕ) : ℕ :=
  cond (Nat.beq (Nat.mod x 3) 0) (Nat.mul 2 (Nat.div x 3))
    (cond (Nat.beq (Nat.mod x 3) 1) (Nat.add (Nat.mul 4 (Nat.div x 3)) 1)
      (Nat.add (Nat.mul 4 (Nat.div x 3)) 3))

theorem natU_cast (x : ℕ) : ((natU x : ℕ) : ℤ) = amusical x := by
  have e : natU x = cond (Nat.beq (x % 2) 0) (3 * (x / 2))
      (cond (Nat.beq (x % 4) 1) (3 * (x / 4) + 1) (3 * (x / 4) + 2)) := rfl
  rw [e]
  unfold amusical
  simp only [Bool.cond_eq_ite, Nat.beq_eq]
  split_ifs <;> push_cast <;> omega

theorem natV_cast (x : ℕ) : ((natV x : ℕ) : ℤ) = amusicalInv x := by
  have e : natV x = cond (Nat.beq (x % 3) 0) (2 * (x / 3))
      (cond (Nat.beq (x % 3) 1) (4 * (x / 3) + 1) (4 * (x / 3) + 3)) := rfl
  rw [e]
  unfold amusicalInv
  simp only [Bool.cond_eq_ite, Nat.beq_eq]
  split_ifs <;> push_cast <;> omega

theorem natU_iterate_cast (x j : ℕ) : ((natU^[j] x : ℕ) : ℤ) = amusical^[j] x := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', natU_cast, ih]

theorem natV_iterate_cast (x j : ℕ) : ((natV^[j] x : ℕ) : ℤ) = amusicalInv^[j] x := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', natV_cast, ih]

/-- `g^[f] x`, by a bare `Nat.rec`. -/
def iterN (g : ℕ → ℕ) (f : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun x => x) (fun _ ih x => ih (g x)) f

theorem iterN_eq (g : ℕ → ℕ) (f x : ℕ) : iterN g f x = g^[f] x := by
  induction f generalizing x with
  | zero => rfl
  | succ f ih => exact ih (g x)

/-- Some `g^[j] x` with `1 ≤ j ≤ f` is below `n`. -/
def anyLt (g : ℕ → ℕ) (n f : ℕ) : ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → Bool) (fun _ => false)
    (fun _ ih x => (fun y => Nat.blt y n || ih y) (g x)) f

/-- Every `g^[j] x` with `1 ≤ j ≤ f` differs from both `n` and `t`. -/
def allNe (g : ℕ → ℕ) (n t f : ℕ) : ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun _ ih x => (fun y => !Nat.beq y n && !Nat.beq y t && ih y) (g x)) f

theorem anyLt_sound {g : ℕ → ℕ} {n f x : ℕ} (h : anyLt g n f x = true) :
    ∃ j, 1 ≤ j ∧ j ≤ f ∧ g^[j] x < n := by
  induction f generalizing x with
  | zero => exact absurd h (by simp [anyLt])
  | succ f ih =>
    change (Nat.blt (g x) n || anyLt g n f (g x)) = true at h
    rw [Bool.or_eq_true, Nat.blt_eq] at h
    rcases h with h | h
    · exact ⟨1, le_rfl, by omega, h⟩
    · obtain ⟨j, hj1, hjf, hj⟩ := ih h
      exact ⟨j + 1, by omega, by omega, by rwa [Function.iterate_succ_apply]⟩

theorem allNe_sound {g : ℕ → ℕ} {n t f x : ℕ} (h : allNe g n t f x = true) :
    ∀ j, 1 ≤ j → j ≤ f → g^[j] x ≠ n ∧ g^[j] x ≠ t := by
  induction f generalizing x with
  | zero => intro j hj1 hjf; omega
  | succ f ih =>
    change (!Nat.beq (g x) n && !Nat.beq (g x) t && allNe g n t f (g x)) = true at h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨hn, ht⟩, hrest⟩ := h
    replace hn := Nat.ne_of_beq_eq_false hn
    replace ht := Nat.ne_of_beq_eq_false ht
    intro j hj1 hjf
    rcases Nat.eq_or_lt_of_le hj1 with rfl | hj
    · exact ⟨hn, ht⟩
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [Function.iterate_succ_apply]
      exact ih hrest j' (by omega) (by omega)

/-- The search condition at one `n`. -/
def searchOkN (H n : ℕ) : Bool :=
  Nat.beq n 1 || Nat.beq n 2 || Nat.beq n 4 || Nat.beq n 44 ||
    anyLt natU n H n || anyLt natV n H n || allNe natU n (iterN natV H n) H n

/-- The search condition at every `n ∈ [1, X]`. -/
noncomputable def searchCheck (H X : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => searchOkN H (Nat.succ k) && ih) X

theorem searchCheck_succ (H X : ℕ) :
    searchCheck H (X + 1) = (searchOkN H (X + 1) && searchCheck H X) := rfl

theorem searchOkN_of_check {H X : ℕ} (h : searchCheck H X = true) :
    ∀ n, 1 ≤ n → n ≤ X → searchOkN H n = true := by
  induction X with
  | zero => intro n hn hnX; omega
  | succ X ih =>
    rw [searchCheck_succ, Bool.and_eq_true] at h
    intro n hn hnX
    rcases Nat.lt_or_ge n (X + 1) with hlt | hge
    · exact ih h.2 n hn (by omega)
    · rw [show n = X + 1 by omega]; exact h.1

/-- **Soundness.**  A passing check gives the body of `CycleMinSearch X H`. -/
theorem searchCheck_sound {H X : ℕ} (h : searchCheck H X = true) :
    ∀ n : ℤ, 1 ≤ n → n ≤ X → n ∉ ({1, 2, 4, 44} : Finset ℤ) →
      (∃ j, 1 ≤ j ∧ j ≤ H ∧ (amusical^[j] n < n ∨ amusicalInv^[j] n < n)) ∨
      ((∀ j, 1 ≤ j → j ≤ H → amusical^[j] n ≠ n) ∧
        ∀ a, 1 ≤ a → a ≤ H → amusical^[a] n ≠ amusicalInv^[H] n) := by
  intro n hn1 hnX hknown
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, by omega⟩
  have hok := searchOkN_of_check h m (by omega) (by omega)
  unfold searchOkN at hok
  simp only [Bool.or_eq_true, Nat.beq_eq] at hok
  rcases hok with (((((h1 | h2) | h4) | h44) | hU) | hV) | hN
  · exact absurd (by simp [h1]) hknown
  · exact absurd (by simp [h2]) hknown
  · exact absurd (by simp [h4]) hknown
  · exact absurd (by simp [h44]) hknown
  · obtain ⟨j, hj1, hjH, hj⟩ := anyLt_sound hU
    refine Or.inl ⟨j, hj1, hjH, Or.inl ?_⟩
    rw [← natU_iterate_cast]; exact_mod_cast hj
  · obtain ⟨j, hj1, hjH, hj⟩ := anyLt_sound hV
    refine Or.inl ⟨j, hj1, hjH, Or.inr ?_⟩
    rw [← natV_iterate_cast]; exact_mod_cast hj
  · have hall := allNe_sound hN
    rw [iterN_eq] at hall
    refine Or.inr ⟨fun j hj1 hjH => ?_, fun a ha1 haH => ?_⟩
    · rw [← natU_iterate_cast]; exact_mod_cast (hall j hj1 hjH).1
    · rw [← natU_iterate_cast, ← natV_iterate_cast]; exact_mod_cast (hall a ha1 haH).2

/-- The single kernel computation for the length-`199` bound: the cycle-minimum bound
`M(p, e) ≤ 4964` for `p ≤ 199`, and the search over `[1, 4964]` with `H = 100`.  Measured
2026-10-14: the small instance (`P = 12`, `X = 173`, `H = 6`) takes 15 ms of kernel time; this
one takes 6.5 s and about 1.1 GB over the 6.4 GB import baseline. -/
theorem cycleCheck_199 : (minBoundCheck 4964 199 && searchCheck 100 4964) = true := by
  decide +kernel

/-- Control: without the exemption the check fails at `44`, the minimum of the 12-cycle. -/
theorem searchOkN_fortyFour_fails :
    (anyLt natU 44 100 44 || anyLt natV 44 100 44 ||
      allNe natU 44 (iterN natV 100 44) 100 44) = false := by
  decide +kernel

theorem searchCheck_4964 : searchCheck 100 4964 = true :=
  (Bool.and_eq_true _ _ ▸ cycleCheck_199).2

/-- **Proved.**  `M(p, e) ≤ 4964` for every `p ≤ 199` and `p < e ≤ 2p`. -/
theorem natMinBound_le_199 (p e : ℕ) (hp : 1 ≤ p) (hpP : p ≤ 199) (hpe : p < e)
    (he : e ≤ 2 * p) : natMinBound p e ≤ 4964 :=
  natMinBound_le_of_okP hp (by omega) hpe he
    (minBoundOkP_of_check (Bool.and_eq_true _ _ ▸ cycleCheck_199).1 p hp hpP)

end CollatzMoonshot.Amusical
