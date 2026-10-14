/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalRewireRatio
import CollatzMoonshot.AmusicalSurvivorSeparation
import CollatzMoonshot.AmusicalOddRewire.Glue

/-!
# Rewiring the odd branch: the tail threshold (Theorem TT) and `τ_odd` (T1★)

The 2026-10-14 "oddbranch" agent (research §33) made §30's `τ_odd` an unconditional no-go and found
its exact size.

**Gluing (GL).**  Rewiring `U` only at points of a set `S` fuses into one orbit every chain that
meets `S` at unboundedly late and unboundedly early times.  Cut each chain at stage-`k` points of
`S ∩ [Y_k, ∞)`, and chain the pieces into one `ℤ`-indexed trail (the construction behind
`rewire_single_orbit`, with the cut predicate as a parameter).  Only cut points change.

**`tail_threshold` (Theorem TT).**  For every `S`: every permutation agreeing with `U` off `S`
has infinitely many infinite orbits **iff** infinitely many infinite orbits of `U` have a forward
tail, or infinitely many a backward tail, that never meets `S`.  (⇐: disjoint forward rays never
share an orbit.  ⇒: glue the rest by GL.)  So a proof of Klamkin (a) that consults `U` only off
`S` is the same thing as a proof that infinitely many whole tails avoid `S`.

**`exists_oddRewire` (T1★).**  With `S` = the odd numbers no tail survives: a forward `E`-run from
`x` lasts `v₂(x)` steps, and every increase of `U⁻¹` lands on `4q + 1` or `4q + 3`.  So for every
`F → ∞` some `τ` agrees with `U` on every even number (`τ(2m) = 3m`) and on every cycle, changes at
most `F(N)` points below `N`, and fuses all chains into one orbit.  `τ` keeps the separation lemma
(`fwdSurvivor_three_separation_of` needs only `τ(2m) = 3m`), staircases, P3, and every window
statistic.  Any proof of (a) must use `U`'s odd branch exactly along entire tails.

Paper proofs: agent report `oddbranch.md` §A (A.5 has a lemma decomposition).
-/

namespace CollatzMoonshot.Amusical

/-- `n` is a forward survivor for the map `f`. -/
def FwdSurvivorOf (f : ℤ → ℤ) (n : ℤ) : Prop :=
  ∀ t : ℕ, 1 ≤ t → n ≤ f^[t] n

theorem perm_int_pow_nat_apply (τ : Equiv.Perm ℤ) (t : ℕ) (x : ℤ) :
    (τ ^ (t : ℤ)) x = (⇑τ)^[t] x := by
  rw [zpow_natCast, Equiv.Perm.coe_pow]

theorem perm_int_iterate_pow_neg_nat (τ : Equiv.Perm ℤ) (t : ℕ) (x : ℤ) :
    (⇑τ)^[t] ((τ ^ (-(t : ℤ))) x) = x := by
  rw [← Equiv.Perm.coe_pow, ← zpow_natCast, ← Equiv.Perm.mul_apply, ← zpow_add]
  simp

/-- **Proved.**  The separation lemma needs only the even branch: for any permutation `τ` of `ℤ`
with `τ(2m) = 3m`, two forward survivors `n < n'` on one orbit with `3 ∣ n'` satisfy `3n ≤ 2n'`. -/
theorem fwdSurvivor_three_separation_of (τ : Equiv.Perm ℤ) (h2 : ∀ m : ℤ, τ (2 * m) = 3 * m)
    {n n' : ℤ} (hn : FwdSurvivorOf τ n) (hn' : FwdSurvivorOf τ n') (hlt : n < n')
    (h3 : 3 ∣ n') (horb : ∃ k : ℤ, (τ ^ k) n = n') : 3 * n ≤ 2 * n' := by
  obtain ⟨k, hk⟩ := horb
  obtain ⟨m, rfl⟩ := h3
  rcases Int.eq_nat_or_neg k with ⟨t, rfl | rfl⟩
  · rw [perm_int_pow_nat_apply] at hk
    rcases t with _ | s
    · simp at hk; omega
    · rw [Function.iterate_succ_apply'] at hk
      have hy : (⇑τ)^[s] n = 2 * m := τ.injective (hk.trans (h2 m).symm)
      rcases s with _ | s
      · simp at hy; omega
      · have := hn (s + 1) (by omega)
        omega
  · have hback : (⇑τ)^[t] (3 * m) = n := by
      rw [← hk]
      exact perm_int_iterate_pow_neg_nat τ t n
    rcases t with _ | t
    · simp at hback; omega
    · have := hn' (t + 1) (by omega)
      omega

/-- **Target (Theorem TT).**  Every permutation of `ℕ` agreeing with `U` off `S` has infinitely
many infinite orbits iff infinitely many infinite orbits of `U` have an `S`-free forward tail, or
infinitely many an `S`-free backward tail. -/
theorem tail_threshold (S : Set ℤ) :
    (∀ τ : Equiv.Perm ℕ, (∀ n : ℕ, (n : ℤ) ∉ S → (τ n : ℤ) = amusical n) →
      {O : Set ℕ | ∃ x : ℕ, O = Set.range (fun j : ℤ => (τ ^ j) x) ∧ O.Infinite}.Infinite) ↔
    ({O : Set ℤ | ∃ y : ℕ, O = amusicalOrbit y ∧ O.Infinite ∧
        ∀ j : ℕ, amusical^[j] (y : ℤ) ∉ S}.Infinite ∨
      {O : Set ℤ | ∃ y : ℕ, O = amusicalOrbit y ∧ O.Infinite ∧
        ∀ j : ℕ, 1 ≤ j → amusicalInv^[j] (y : ℤ) ∉ S}.Infinite) := by
  sorry

/-- **Target (T1★).**  For every `F → ∞` there is a permutation of `ℕ` that agrees with `U` on
every even number and every finite orbit, changes at most `F N` points below `N`, and fuses all
infinite orbits of `U` into one. -/
theorem exists_oddRewire (F : ℕ → ℕ) (hF : Filter.Tendsto F Filter.atTop Filter.atTop) :
    ∃ τ : Equiv.Perm ℕ,
      (∀ m : ℕ, τ (2 * m) = 3 * m) ∧
      (∀ n : ℕ, (amusicalOrbit n).Finite → (τ n : ℤ) = amusical n) ∧
      (∀ N : ℕ, ((Finset.range N).filter fun n => (τ n : ℤ) ≠ amusical n).card ≤ F N) ∧
      ∀ a b : ℕ, (amusicalOrbit a).Infinite → (amusicalOrbit b).Infinite →
        ∃ j : ℤ, (τ ^ j) a = b := by
  sorry

end CollatzMoonshot.Amusical
