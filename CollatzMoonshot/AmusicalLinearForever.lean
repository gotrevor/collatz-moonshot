/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalAntiKohl

/-!
# Linear-forever points force infinitely many orbits (Theorem W)

The 2026-10-13 "logic" Fable agent isolated the one mechanism behind every provable
"infinitely many orbits" certificate for an RCWA permutation so far.

**Theorem W (`infinitelyManyOrbits_of_linearForever`).**  Suppose some `x ≠ 0` has a forward orbit
that only ever uses zero-offset pieces (`b = 0`, so `c · σ y = a · y`).  Then, for every
`u ≡ 1 (mod m)` coprime to every slope numerator and denominator, `u x` does too, with
`σᵏ (u x) = u σᵏ x`.  Distinct such `u` give distinct orbits: a collision would make `u'/u` a
product of slopes.  So `σ` has infinitely many orbits.
* The ping-pong engine of `PP(0)` (`AmusicalPingPong.lean`) is such a point, and this proves its
  infinitely many orbits in one line.
* `U`'s only linear piece is `2n ↦ 3n`, and no orbit stays in it (`amusical_not_eventually_linear`).
  So Theorem W is vacuous on `U`, as the no-go test demands.

The agent's complexity results are paper proofs, recorded in research §22.
* For RCWA permutations given by tables, "some orbit is infinite" is `Σ⁰₂`-complete and "all
  orbits finite" is `Π⁰₂`-complete.
* "Finitely many orbits" is `Π⁰₂`-hard, and its naive upper bound is `Π⁰₃`.
* There is a computable RCWA permutation whose orbit count is finite iff `Con(ZFC)`.
* The `Σ⁰₂`/`Π⁰₃` gap is exactly universal *additive* computation, which is `U`'s class.  Every
  counter-based hardness route ends at Theorem W's `Σ⁰₂` certificate.
-/

namespace CollatzMoonshot.Amusical

/-- **Proved (Theorem W).**  A nonzero point whose forward orbit stays on zero-offset pieces forces
infinitely many orbits.  Paper proof in the module docstring (agent report `logic.md` §1). -/
theorem infinitelyManyOrbits_of_linearForever (σ : Equiv.Perm ℤ) {m : ℕ} {a b c : ℤ → ℤ}
    (hσ : IsRCWA σ m a b c) {x : ℤ} (hx : x ≠ 0)
    (hlin : ∀ k : ℕ, b ((σ^[k] x) % m) = 0) :
    {O : Set ℤ | ∃ y, O = permOrbit σ y}.Infinite := by
  have hm : (m : ℤ) ≠ 0 := by exact_mod_cast hσ.pos.ne'
  -- the product of all slope numerators and denominators
  set P : ℤ := ∏ r ∈ Finset.range m, (a r * c r) with hP
  have hdvd : ∀ z : ℤ, a (z % m) ∣ P ∧ c (z % m) ∣ P := by
    intro z
    have h0 : 0 ≤ z % m := Int.emod_nonneg z hm
    have hlt : (z % m).toNat ∈ Finset.range m := by
      simp only [Finset.mem_range]
      have := Int.emod_lt_of_pos z (by exact_mod_cast hσ.pos : (0 : ℤ) < m)
      omega
    have hz : ((z % m).toNat : ℤ) = z % m := Int.toNat_of_nonneg h0
    have hmem := Finset.dvd_prod_of_mem (fun r : ℕ => a r * c r) hlt
    rw [hz] at hmem
    exact ⟨(dvd_mul_right _ _).trans hmem, (dvd_mul_left _ _).trans hmem⟩
  -- one step and iterates commute with scaling by u ≡ 1 mod m
  have step : ∀ u y : ℤ, u ≡ 1 [ZMOD m] → b (y % m) = 0 → σ (u * y) = u * σ y := by
    intro u y hu hb
    have hmod : (u * y) % m = y % m := by
      have := (hu.mul_right y)
      simpa [Int.ModEq] using this
    have e1 := hσ.eqn (u * y)
    have e2 := hσ.eqn y
    rw [hmod, hb, add_zero] at e1
    rw [hb, add_zero] at e2
    have hc : c (y % m) ≠ 0 := (hσ.coeff _).1.ne'
    apply mul_left_cancel₀ hc
    rw [e1, show c (y % m) * (u * σ y) = u * (c (y % m) * σ y) by ring, e2]
    ring
  have iter : ∀ u : ℤ, u ≡ 1 [ZMOD m] → ∀ n : ℕ, σ^[n] (u * x) = u * σ^[n] x := by
    intro u hu n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, step u _ hu (hlin n)]
  -- slope products along the orbit of x
  let A : ℕ → ℤ := fun n => ∏ i ∈ Finset.range n, a ((σ^[i] x) % m)
  let C : ℕ → ℤ := fun n => ∏ i ∈ Finset.range n, c ((σ^[i] x) % m)
  have rel : ∀ n : ℕ, C n * σ^[n] x = A n * x := by
    intro n
    induction n with
    | zero => simp [A, C]
    | succ n ih =>
        have e := hσ.eqn (σ^[n] x)
        rw [hlin n, add_zero] at e
        simp only [A, C, Finset.prod_range_succ, Function.iterate_succ_apply']
        calc (∏ i ∈ Finset.range n, c ((σ^[i] x) % m)) * c ((σ^[n] x) % m) * σ (σ^[n] x)
            = (∏ i ∈ Finset.range n, c ((σ^[i] x) % m)) * (c ((σ^[n] x) % m) * σ (σ^[n] x)) := by
              ring
          _ = (∏ i ∈ Finset.range n, c ((σ^[i] x) % m)) * (a ((σ^[n] x) % m) * σ^[n] x) := by
              rw [e]
          _ = a ((σ^[n] x) % m) * (C n * σ^[n] x) := by simp only [C]; ring
          _ = _ := by rw [ih]; simp only [A]; ring
  have hA : ∀ n, A n ∣ P ^ n := fun n => by
    simpa [A, Finset.prod_const, Finset.card_range] using
      Finset.prod_dvd_prod_of_dvd (s := Finset.range n) (fun i => a ((σ^[i] x) % m)) (fun _ => P)
        (fun i _ => (hdvd (σ^[i] x)).1)
  have hC : ∀ n, C n ∣ P ^ n := fun n => by
    simpa [C, Finset.prod_const, Finset.card_range] using
      Finset.prod_dvd_prod_of_dvd (s := Finset.range n) (fun i => c ((σ^[i] x) % m)) (fun _ => P)
        (fun i _ => (hdvd (σ^[i] x)).2)
  -- the multipliers
  let u : ℕ → ℤ := fun k => 1 + (k : ℤ) * m * P ^ 2
  have hu1 : ∀ k, u k ≡ 1 [ZMOD m] := by
    intro k
    simp only [u, Int.ModEq]
    rw [show (1 : ℤ) + k * m * P ^ 2 = 1 + m * (k * P ^ 2) by ring]
    simp
  have hupos : ∀ k, 0 < u k := by
    intro k; simp only [u]; positivity
  have hcop : ∀ k n, IsCoprime (u k) (P ^ n) := by
    intro k n
    apply IsCoprime.pow_right
    exact ⟨1, -((k : ℤ) * m * P), by simp only [u]; ring⟩
  -- forward collisions force equal multipliers
  have key : ∀ k k' : ℕ, ∀ n : ℕ, σ^[n] (u k * x) = u k' * x → u k = u k' := by
    intro k k' n h
    rw [iter _ (hu1 k)] at h
    have h2 : C n * u k' * x = u k * A n * x := by
      calc C n * u k' * x = C n * (u k' * x) := by ring
        _ = C n * (u k * σ^[n] x) := by rw [h]
        _ = u k * (C n * σ^[n] x) := by ring
        _ = u k * A n * x := by rw [rel n]; ring
    have h3 : C n * u k' = u k * A n := mul_right_cancel₀ hx h2
    have d1 : u k ∣ u k' := by
      have : u k ∣ C n * u k' := ⟨A n, by rw [h3]⟩
      exact ((hcop k n).of_isCoprime_of_dvd_right (hC n)).dvd_of_dvd_mul_left this
    have d2 : u k' ∣ u k := by
      have : u k' ∣ u k * A n := ⟨C n, by rw [← h3]; ring⟩
      exact ((hcop k' n).of_isCoprime_of_dvd_right (hA n)).dvd_of_dvd_mul_right this
    exact Int.dvd_antisymm (hupos k).le (hupos k').le d1 d2
  have hPne : P ≠ 0 := by
    rw [hP, Finset.prod_ne_zero_iff]
    intro r _
    exact mul_ne_zero (hσ.coeff r).2 (hσ.coeff r).1.ne'
  have uinj : Function.Injective u := by
    intro k k' h
    simp only [u] at h
    have : ((k : ℤ) - k') * (m * P ^ 2) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h1 | h1
    · exact_mod_cast sub_eq_zero.mp h1
    · exact absurd h1 (mul_ne_zero hm (pow_ne_zero 2 hPne))
  -- orbits of u k * x are pairwise distinct
  have orbinj : Function.Injective fun k : ℕ => permOrbit σ (u k * x) := by
    intro k k' h
    apply uinj
    have hmem : u k' * x ∈ permOrbit σ (u k * x) := by
      have h' : permOrbit σ (u k * x) = permOrbit σ (u k' * x) := h
      rw [h']; exact ⟨0, by simp⟩
    obtain ⟨j, hj⟩ := hmem
    simp only at hj
    rcases j with n | n
    · rw [Int.ofNat_eq_natCast, zpow_natCast, ← Equiv.Perm.iterate_eq_pow] at hj
      exact key k k' n hj
    · rw [zpow_negSucc, Equiv.Perm.inv_eq_iff_eq, ← Equiv.Perm.iterate_eq_pow] at hj
      exact (key k' k (n + 1) hj.symm).symm
  exact Set.infinite_of_injective_forall_mem orbinj (fun k => ⟨_, rfl⟩)

end CollatzMoonshot.Amusical
