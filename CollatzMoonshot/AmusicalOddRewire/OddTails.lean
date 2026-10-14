/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalRewireRatio.Restriction
import CollatzMoonshot.AmusicalSurvivorSeparation
import CollatzMoonshot.AmusicalOddRewire.Glue

/-!
# No infinite orbit of `U` has an odd-free tail

Forward: from `2ᵃ b` with `b` odd, `U` takes `a` even steps to the odd `3ᵃ b`.  Backward: `U⁻¹ m`
is even only for `3 ∣ m`, where `U⁻¹ m = 2m/3 ≤ m`; so an odd-free backward tail is bounded,
which an infinite orbit is not.  Hence every infinite orbit of `U` on `ℕ` is gluable at the odd
numbers (`gluePt_odd_of_infinite`).
-/

namespace CollatzMoonshot.Amusical

open CollatzMoonshot.Obstructions.Amusical

/-- The orbit of `n` under `U` is the cast of its orbit under `U` restricted to `ℕ`. -/
theorem amusicalOrbit_natCast_eq (n : ℕ) :
    amusicalOrbit (n : ℤ) =
      (Nat.cast : ℕ → ℤ) '' Set.range fun j : ℤ => (amusicalNatPerm ^ j) n := by
  ext y
  simp [amusicalOrbit]

theorem natOrbit_infinite_iff (n : ℕ) :
    (Set.range fun j : ℤ => (amusicalNatPerm ^ j) n).Infinite ↔ (amusicalOrbit (n : ℤ)).Infinite :=
  by rw [amusicalOrbit_natCast_eq, Set.infinite_image_iff Nat.cast_injective.injOn]

theorem amusicalNatPerm_pow_nat_cast (k x : ℕ) :
    (((amusicalNatPerm ^ (k : ℤ)) x : ℕ) : ℤ) = amusical^[k] x := by
  rw [amusicalNatPerm_zpow_apply_cast, amusicalPerm_pow_nat_apply]

theorem amusicalNatPerm_pow_neg_nat_cast (k x : ℕ) :
    (((amusicalNatPerm ^ (-(k : ℤ))) x : ℕ) : ℤ) = amusicalInv^[k] x := by
  rw [amusicalNatPerm_zpow_apply_cast, amusicalPerm_pow_neg_nat_apply]

theorem amusical_iterate_two_pow_mul (a : ℕ) (b : ℤ) : amusical^[a] (2 ^ a * b) = 3 ^ a * b := by
  induction a generalizing b with
  | zero => simp
  | succ a ih =>
      rw [Function.iterate_succ_apply, pow_succ, mul_comm (2 ^ a) 2, mul_assoc,
        amusical_two_mul, show 3 * (2 ^ a * b) = 2 ^ a * (3 * b) by ring, ih]
      ring

/-- **Forward.**  A positive integer reaches an odd number after `v₂` steps of `U`. -/
theorem exists_late_odd {y : ℕ} (hy : y ≠ 0) : ∃ j : ℕ, Odd (amusical^[j] (y : ℤ)) := by
  obtain ⟨a, b, hb, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hy
  refine ⟨a, ?_⟩
  push_cast
  rw [amusical_iterate_two_pow_mul]
  exact (Odd.pow (by decide : Odd (3 : ℤ))).mul (Int.odd_coe_nat b |>.2 hb)

theorem amusicalInv_le_of_even {m : ℤ} (hm : 0 ≤ m) (he : Even (amusicalInv m)) :
    amusicalInv m ≤ m := by
  obtain ⟨r, hr⟩ := he
  unfold amusicalInv at hr ⊢
  split_ifs at hr ⊢ <;> omega

/-- **Backward.**  On an infinite orbit, some backward iterate of each point is odd. -/
theorem exists_early_odd {z : ℕ}
    (hinf : (Set.range fun j : ℤ => (amusicalNatPerm ^ j) z).Infinite) :
    ∃ t : ℕ, Odd (amusicalInv^[t + 1] (z : ℤ)) := by
  by_contra h
  push Not at h
  have hle : ∀ t : ℕ, amusicalInv^[t] (z : ℤ) ≤ z := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
        have h0 : 0 ≤ amusicalInv^[t] (z : ℤ) := by
          rw [← amusicalNatPerm_pow_neg_nat_cast]; exact Int.natCast_nonneg _
        have he : Even (amusicalInv (amusicalInv^[t] (z : ℤ))) := by
          rw [← Function.iterate_succ_apply' amusicalInv]; exact Int.not_odd_iff_even.1 (h t)
        rw [Function.iterate_succ_apply']
        exact (amusicalInv_le_of_even h0 he).trans ih
  obtain ⟨k, hk⟩ := (exists_nat_iterate_gt hinf z).2
  have := hle k
  rw [← amusicalNatPerm_pow_neg_nat_cast] at this
  omega

/-- **Every infinite orbit of `U` meets the odd numbers at unboundedly late and early times.** -/
theorem gluePt_odd_of_infinite {x : ℕ}
    (hinf : (Set.range fun j : ℤ => (amusicalNatPerm ^ j) x).Infinite) :
    GluePt amusicalNatPerm {n | Odd n} x := by
  refine ⟨hinf, fun K => ?_, fun K => ?_⟩
  · obtain ⟨k, hk, hpos⟩ := (exists_nat_iterate_gt_after hinf 0 K.toNat).1
    obtain ⟨j, hj⟩ := exists_late_odd (Nat.pos_iff_ne_zero.1 hpos)
    refine ⟨((j + k : ℕ) : ℤ), by omega, ?_⟩
    show Odd _
    rw [← Int.odd_coe_nat, amusicalNatPerm_pow_nat_cast, Function.iterate_add_apply,
      ← amusicalNatPerm_pow_nat_cast k x]
    exact hj
  · obtain ⟨t, ht⟩ := exists_early_odd (z := (amusicalNatPerm ^ (-((-K).toNat : ℤ))) x)
      (by rwa [perm_zpow_range_apply_zpow])
    refine ⟨-(((t + 1 + (-K).toNat : ℕ)) : ℤ), by omega, ?_⟩
    show Odd _
    rw [← Int.odd_coe_nat, amusicalNatPerm_pow_neg_nat_cast, Function.iterate_add_apply,
      ← amusicalNatPerm_pow_neg_nat_cast]
    exact ht

end CollatzMoonshot.Amusical
