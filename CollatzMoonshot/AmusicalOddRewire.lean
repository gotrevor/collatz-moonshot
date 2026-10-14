/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalRewireRatio
import CollatzMoonshot.AmusicalSurvivorSeparation
import CollatzMoonshot.AmusicalOddRewire.Threshold

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

Paper proofs: agent report `oddbranch.md` §A (A.5 has a lemma decomposition).  Kernel-checked
2026-10-14: GL is `exists_glue` (`AmusicalOddRewire/Glue.lean`, on the cut-set reconnection
`IsCutSet.glue`); the odd tails are `exists_late_odd` and `exists_early_odd`.
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

/-- **Proved (Theorem TT).**  Every permutation of `ℕ` agreeing with `U` off `S` has infinitely
many infinite orbits iff infinitely many infinite orbits of `U` have an `S`-free forward tail, or
infinitely many an `S`-free backward tail. -/
theorem tail_threshold (S : Set ℤ) :
    (∀ τ : Equiv.Perm ℕ, (∀ n : ℕ, (n : ℤ) ∉ S → (τ n : ℤ) = amusical n) →
      {O : Set ℕ | ∃ x : ℕ, O = Set.range (fun j : ℤ => (τ ^ j) x) ∧ O.Infinite}.Infinite) ↔
    ({O : Set ℤ | ∃ y : ℕ, O = amusicalOrbit y ∧ O.Infinite ∧
        ∀ j : ℕ, amusical^[j] (y : ℤ) ∉ S}.Infinite ∨
      {O : Set ℤ | ∃ y : ℕ, O = amusicalOrbit y ∧ O.Infinite ∧
        ∀ j : ℕ, 1 ≤ j → amusicalInv^[j] (y : ℤ) ∉ S}.Infinite) := by
  classical
  constructor
  · intro H
    by_contra hAB
    rw [not_or, Set.not_infinite, Set.not_infinite] at hAB
    obtain ⟨hA, hB⟩ := hAB
    obtain ⟨τ, hchg, -, hconn⟩ :=
      exists_glue amusicalNatPerm {n : ℕ | (n : ℤ) ∈ S} id Filter.tendsto_id
    have hτ : ∀ n : ℕ, (n : ℤ) ∉ S → (τ n : ℤ) = amusical n := by
      intro n hn
      by_contra h
      exact hn (hchg n fun h' => h (by rw [h', amusicalNatPerm_apply_cast])).1
    apply H τ hτ
    have hG : {P : Set ℕ | ∃ x, GluePt amusicalNatPerm {n : ℕ | (n : ℤ) ∈ S} x ∧
        P = Set.range fun j : ℤ => (τ ^ j) x}.Finite := by
      apply Set.Subsingleton.finite
      rintro P ⟨a, ha, rfl⟩ Q ⟨b, hb, rfl⟩
      obtain ⟨j, hj⟩ := hconn a b ha hb
      rw [← hj, perm_zpow_range_apply_zpow]
    refine (hG.union ((hA.union hB).image fun O : Set ℤ => (Nat.cast : ℕ → ℤ) ⁻¹' O)).subset ?_
    rintro P ⟨x, rfl, hPinf⟩
    by_cases hx : GluePt amusicalNatPerm {n : ℕ | (n : ℤ) ∈ S} x
    · exact Or.inl ⟨x, hx, rfl⟩
    · have hzp := zpow_eq_of_not_gluePt (fun n h => (hchg n h).2) hx
      have hP : (Set.range fun j : ℤ => (τ ^ j) x) =
          Set.range fun j : ℤ => (amusicalNatPerm ^ j) x := by simp only [hzp]
      rw [hP] at hPinf ⊢
      obtain ⟨y, hyO, hy⟩ := exists_tail_of_not_gluePt hPinf hx
      have hOinf : (amusicalOrbit (y : ℤ)).Infinite := hyO ▸ (natOrbit_infinite_iff x).1 hPinf
      refine Or.inr ⟨amusicalOrbit y, ?_, ?_⟩
      · rcases hy with hy | hy
        · exact Or.inl ⟨y, rfl, hOinf, hy⟩
        · exact Or.inr ⟨y, rfl, hOinf, hy⟩
      · rw [hyO, amusicalOrbit_natCast_eq]
        exact Set.preimage_image_eq _ Nat.cast_injective
  · intro hAB τ hτ
    rcases hAB with hA | hB
    · refine infinite_tauOrbits_of_rays τ 1 (by norm_num) _ hA ?_
      rintro O ⟨y, rfl, hinf, hy⟩
      exact ⟨y, rfl, hinf, fun j => by simpa using tau_pow_nat_eq_of_fwdTail hτ hy j⟩
    · refine infinite_tauOrbits_of_rays τ (-1) (by norm_num) _ hB ?_
      rintro O ⟨y, rfl, hinf, hy⟩
      exact ⟨y, rfl, hinf, fun j => by simpa using tau_pow_neg_eq_of_bwdTail hτ hy j⟩

/-- **Proved (T1★).**  For every `F → ∞` there is a permutation of `ℕ` that agrees with `U` on
every even number and every finite orbit, changes at most `F N` points below `N`, and fuses all
infinite orbits of `U` into one. -/
theorem exists_oddRewire (F : ℕ → ℕ) (hF : Filter.Tendsto F Filter.atTop Filter.atTop) :
    ∃ τ : Equiv.Perm ℕ,
      (∀ m : ℕ, τ (2 * m) = 3 * m) ∧
      (∀ n : ℕ, (amusicalOrbit n).Finite → (τ n : ℤ) = amusical n) ∧
      (∀ N : ℕ, ((Finset.range N).filter fun n => (τ n : ℤ) ≠ amusical n).card ≤ F N) ∧
      ∀ a b : ℕ, (amusicalOrbit a).Infinite → (amusicalOrbit b).Infinite →
        ∃ j : ℤ, (τ ^ j) a = b := by
  obtain ⟨τ, hchg, hcount, hconn⟩ := exists_glue amusicalNatPerm {n | Odd n} F hF
  have heq (n : ℕ) (h : (τ n : ℤ) ≠ amusical n) : τ n ≠ amusicalNatPerm n := fun h' =>
    h (by rw [h', amusicalNatPerm_apply_cast])
  refine ⟨τ, fun m => ?_, fun n hn => ?_, fun N => ?_, fun a b ha hb => ?_⟩
  · by_cases h : τ (2 * m) = amusicalNatPerm (2 * m)
    · apply Nat.cast_injective (R := ℤ)
      rw [h, amusicalNatPerm_apply_cast]
      push_cast
      exact amusical_two_mul m
    · exact absurd (hchg _ h).1 (by simp)
  · by_contra h
    exact (natOrbit_infinite_iff n).1 (hchg n (heq n h)).2.1 hn
  · refine le_trans (Finset.card_le_card fun n hn => ?_) (hcount N)
    simp only [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, heq n hn.2⟩
  · exact hconn a b (gluePt_odd_of_infinite ((natOrbit_infinite_iff a).2 ha))
      (gluePt_odd_of_infinite ((natOrbit_infinite_iff b).2 hb))

end CollatzMoonshot.Amusical
