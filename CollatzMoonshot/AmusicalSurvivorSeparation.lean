/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalGlobal

/-!
# Forward survivors divisible by `3` separate orbits

The 2026-10-14 "q1sharp" agent found that one-sided survival suffices for Klamkin (a).  The
simplest form needs nothing but `U(2m) = 3m`.

**`fwdSurvivor_three_separation`.**  If `n < n'` are forward survivors on one orbit and `3 ∣ n'`,
then `3n ≤ 2n'`.  Paper proof: `n'` is not before `n` (else `n' ≤ n`), so `n` lies on the backward
orbit of `n'`, whose first step is `U⁻¹ n' = 2n'/3`; and `n` survives up to that point.

**`infinitelyManyOrbits_of_fwdSurvivors_three`.**  So forward survivors divisible by `3` in a window
`[X, 3X/2)` lie on pairwise distinct infinite orbits (`fwdSurvivor_three_not_periodic`).  If such
windows hold unboundedly many of them, `U` has infinitely many orbits.  It suffices that `FS ∩ 3ℤ ∩ [1, X]` is not `O(log X)`.  The
measured density of `FS` is about `0.21` (research §20); proving any lower bound is the typicality
wall.  The rewired `τ` (§14) satisfies `U(2m) = 3m` on all but a density-0 set, so the lemma's
input is genuinely global.

Paper proofs: agent report `q1sharp.md`, summarized in
`RESEARCH-2026-10-13-amusical-single-chain.md` §26.
-/

namespace CollatzMoonshot.Amusical

theorem amusicalPerm_pow_nat_apply (t : ℕ) (x : ℤ) :
    (amusicalPerm ^ (t : ℤ)) x = amusical^[t] x := by
  rw [zpow_natCast, Equiv.Perm.coe_pow]; rfl

theorem amusicalPerm_pow_neg_nat_apply (t : ℕ) (x : ℤ) :
    (amusicalPerm ^ (-(t : ℤ))) x = amusicalInv^[t] x := by
  rw [zpow_neg, zpow_natCast, ← inv_pow, Equiv.Perm.coe_pow]; rfl

/-- **Proved.**  Two forward survivors `n < n'` on one orbit with `3 ∣ n'` satisfy `3n ≤ 2n'`. -/
theorem fwdSurvivor_three_separation {n n' : ℤ} (hn : FwdSurvivor n) (hn' : FwdSurvivor n')
    (hlt : n < n') (h3 : 3 ∣ n') (horb : n' ∈ amusicalOrbit n) : 3 * n ≤ 2 * n' := by
  obtain ⟨k, hk⟩ := horb
  obtain ⟨m, rfl⟩ := h3
  rcases Int.eq_nat_or_neg k with ⟨t, rfl | rfl⟩
  · simp only at hk
    rw [amusicalPerm_pow_nat_apply] at hk
    rcases t with _ | s
    · simp at hk; omega
    · rw [Function.iterate_succ_apply'] at hk
      have hy : amusical^[s] n = 2 * m :=
        amusical_injective (hk.trans (amusical_two_mul m).symm)
      rcases s with _ | s
      · simp at hy; omega
      · have := hn (s + 1) (by omega)
        omega
  · simp only at hk
    rw [amusicalPerm_pow_neg_nat_apply] at hk
    have hback : amusical^[t] (3 * m) = n := by
      rw [← hk]
      exact (Function.LeftInverse.iterate amusical_amusicalInv t) n
    rcases t with _ | t
    · simp at hback; omega
    · have := hn' (t + 1) (by omega)
      omega

/-- **Proved.**  In a window `[X, 3X/2)`, a forward survivor divisible by `3` is on a different
orbit from every smaller forward survivor of the window. -/
theorem fwdSurvivor_three_not_mem_orbit {X n n' : ℤ} (hn : FwdSurvivor n) (hn' : FwdSurvivor n')
    (hXn : X ≤ n) (hlt : n < n') (hn'X : 2 * n' < 3 * X) (h3 : 3 ∣ n') :
    n' ∉ amusicalOrbit n := fun horb => by
  have := fwdSurvivor_three_separation hn hn' hlt h3 horb
  omega

/-- **Proved.**  If windows `[X, 3X/2)` hold unboundedly many forward survivors divisible by `3`,
then `U` has infinitely many orbits on `ℕ`. -/
theorem infinitelyManyOrbits_of_fwdSurvivors_three
    (h : ∀ B : ℕ, ∃ X : ℤ, 0 < X ∧ ∃ S : Finset ℤ, B < S.card ∧
      ∀ n ∈ S, X ≤ n ∧ 2 * n < 3 * X ∧ FwdSurvivor n ∧ 3 ∣ n) :
    AmusicalInfinitelyManyOrbits := by
  intro hfin
  obtain ⟨X, hX, S, hcard, hS⟩ := h hfin.toFinset.card
  have hmaps : ∀ n ∈ S, amusicalOrbit n ∈ hfin.toFinset := by
    intro n hn
    rw [Set.Finite.mem_toFinset]
    exact ⟨n, by linarith [(hS n hn).1], rfl⟩
  have hinj : Set.InjOn amusicalOrbit S := by
    intro a ha b hb hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have hmem : b ∈ amusicalOrbit a := hab ▸ mem_amusicalOrbit_self b
      exact fwdSurvivor_three_not_mem_orbit (hS a ha).2.2.1 (hS b hb).2.2.1 (hS a ha).1 h
        (hS b hb).2.1 (hS b hb).2.2.2 hmem
    · have hmem : a ∈ amusicalOrbit b := hab.symm ▸ mem_amusicalOrbit_self a
      exact fwdSurvivor_three_not_mem_orbit (hS b hb).2.2.1 (hS a ha).2.2.1 (hS b hb).1 h
        (hS a ha).2.1 (hS a ha).2.2.2 hmem
  have := Finset.card_le_card_of_injOn amusicalOrbit hmaps hinj
  omega

/-- **Proved.**  A positive forward survivor divisible by `3` lies on an infinite orbit: its
predecessor `2n/3` is below it, and a cycle would bring the orbit back to that predecessor. -/
theorem fwdSurvivor_three_not_periodic {n : ℤ} (hn : FwdSurvivor n) (h3 : 3 ∣ n) (hpos : 0 < n) :
    n ∉ Function.periodicPts amusical := by
  rintro ⟨p, hp, hper⟩
  obtain ⟨m, rfl⟩ := h3
  obtain ⟨s, rfl⟩ : ∃ s, p = s + 1 := ⟨p - 1, by omega⟩
  have hstep : amusical (amusical^[s] (3 * m)) = 3 * m := by
    rw [← Function.iterate_succ_apply' amusical s]; exact hper.eq
  have hy : amusical^[s] (3 * m) = 2 * m :=
    amusical_injective (hstep.trans (amusical_two_mul m).symm)
  rcases s with _ | s
  · simp at hy; omega
  · have := hn (s + 1) (by omega)
    omega

end CollatzMoonshot.Amusical
