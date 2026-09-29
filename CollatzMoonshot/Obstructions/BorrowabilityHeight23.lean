import Mathlib

/-!
Finite certificate for the failure of strict quadratic height descent at 23.
Only `c,d : Fin 23` are checked by finite decision.  The companion `b` is
unbounded, including all positive odd companions of an actual odd factor.
-/

namespace CollatzMoonshot.Obstructions.ArithmeticLifts

private def smallDen23 (c d : Fin 23) : Nat :=
  23 * (3 * (c.val + d.val) + 1) - 3 * c.val * d.val

private theorem smallDen23_pos :
    ∀ c d : Fin 23,
      0 < c.val → 0 < d.val →
      c.val % 2 = 1 → d.val % 2 = 1 →
      0 < smallDen23 c d := by
  native_decide

/-- The bounded operands guarantee that Nat subtraction did not truncate. -/
private theorem smallDen23_add :
    ∀ c d : Fin 23,
      smallDen23 c d + 3 * c.val * d.val =
        23 * (3 * (c.val + d.val) + 1) := by
  native_decide

private theorem smallDen23_not_dvd :
    ∀ c d : Fin 23,
      0 < c.val → 0 < d.val →
      c.val % 2 = 1 → d.val % 2 = 1 →
      ¬ smallDen23 c d ∣ 70 * c.val * d.val := by
  native_decide

theorem no_strict_quadratic_height_descent_23
    (c d : Fin 23) (b : Nat)
    (hc : 0 < c.val) (hd : 0 < d.val)
    (hcodd : c.val % 2 = 1) (hdodd : d.val % 2 = 1) :
    smallDen23 c d * b ≠ 70 * c.val * d.val := by
  intro h
  exact (smallDen23_not_dvd c d hc hd hcodd hdodd) ⟨b, h.symm⟩

/-- No quadratic replacement of `r_23 * r_b` by `r_c * r_d` can have both
positive odd replacement labels strictly below 23.  The cross-multiplied
identity is excluded for every natural companion `b`, without a height bound
or a parity premise on `b`. -/
theorem no_quadratic_cross_identity_23
    (c d : Fin 23) (b : Nat)
    (hc : 0 < c.val) (hd : 0 < d.val)
    (hcodd : c.val % 2 = 1) (hdodd : d.val % 2 = 1) :
    23 * b * (3 * c.val + 1) * (3 * d.val + 1) ≠
      70 * c.val * d.val * (3 * b + 1) := by
  intro hcross
  have hden := smallDen23_add c d
  have hdenb :
      (smallDen23 c d + 3 * c.val * d.val) * b =
        (23 * (3 * (c.val + d.val) + 1)) * b :=
    congrArg (fun x : Nat => x * b) hden
  have hdiv : smallDen23 c d * b = 70 * c.val * d.val := by
    nlinarith [hdenb, hcross]
  exact no_strict_quadratic_height_descent_23 c d b hc hd hcodd hdodd hdiv

end CollatzMoonshot.Obstructions.ArithmeticLifts
