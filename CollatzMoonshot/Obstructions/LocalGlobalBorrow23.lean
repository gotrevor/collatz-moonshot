import CollatzMoonshot.Obstructions.BorrowabilityHeight23

/-!
# Local solvability versus a global integer companion at `u = 23`

The cross equation at `u = 23` for input labels `c, d < 23` and companion `b`
is `23 * b * (3c+1) * (3d+1) = 70 * c * d * (3b+1)`.

* For `c = d = 1` it reduces to `79 * b = 35`.
* For `c = 13, d = 17` it reduces to `11 * b = 119`.

Both reduced equations have *no* integer solution, but each is solvable
modulo any prime power whose prime avoids the leading coefficient: pick the
pair `(1,1)` unless `p = 79`, in which case pick `(13,17)`.  Writing
`b = 5 + 6t` (resp. `b = 1 + 6t`) keeps the companion positive, odd and
3-free, and the residual linear congruence `79 t ≡ -60` (resp. `11 t ≡ 18`)
is solved by a modular inverse.

The quantifier order matters: the witnesses `c, d, b` are allowed to depend
on `p` and `k`.  Nothing here asserts a single `(c,d,b)` working for all
moduli simultaneously — indeed a *finite joint* modulus already blocks every
small input pair.  This is therefore not a failure of CRT, and it is not
evidence that local-to-global reasoning fails in general.
-/

namespace CollatzMoonshot.Obstructions.ArithmeticLifts

/-- A linear congruence with coefficient coprime to the modulus is solvable. -/
private lemma exists_linear_sol (n a : ℕ) (h : Nat.Coprime a n) (y : ZMod n) :
    ∃ t : ZMod n, (a : ZMod n) * t = y := by
  obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime a n).2 h
  refine ⟨((u⁻¹ : (ZMod n)ˣ) : ZMod n) * y, ?_⟩
  rw [← hu, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

/-- Each prime-power modulus separately admits positive, odd, 3-free
operands with both input labels below 23.  The operands may depend on p,k. -/
theorem each_prime_power_has_small_inputs_23 (p k : ℕ) (hp : p.Prime) :
    ∃ (c d : Fin 23) (b : ℕ),
      0 < c.val ∧ 0 < d.val ∧
      c.val % 2 = 1 ∧ d.val % 2 = 1 ∧
      c.val % 3 ≠ 0 ∧ d.val % 3 ≠ 0 ∧
      0 < b ∧ b % 2 = 1 ∧ b % 3 ≠ 0 ∧
      Nat.ModEq (p ^ k)
        (23 * b * (3 * c.val + 1) * (3 * d.val + 1))
        (70 * c.val * d.val * (3 * b + 1)) := by
  have : NeZero (p ^ k) := ⟨pow_ne_zero k hp.pos.ne'⟩
  by_cases h79 : p = 79
  · -- `p = 79` blocks the pair `(1,1)`; use `(13,17)` with `11 * b ≡ 119`.
    have hcop : Nat.Coprime 11 (p ^ k) := by
      subst h79
      exact Nat.Coprime.pow_right _ (by norm_num)
    obtain ⟨t, ht⟩ := exists_linear_sol (p ^ k) 11 hcop 18
    refine ⟨⟨13, by norm_num⟩, ⟨17, by norm_num⟩, 1 + 6 * t.val,
      by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
      by omega, by omega, by omega, ?_⟩
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast [Fin.val_mk, ZMod.natCast_val, ZMod.cast_id]
    linear_combination (780 : ZMod (p ^ k)) * ht
  · -- Otherwise the pair `(1,1)` works, with `79 * b ≡ 35`.
    have hcop : Nat.Coprime 79 (p ^ k) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_primes (by norm_num) hp).2 (Ne.symm h79))
    obtain ⟨t, ht⟩ := exists_linear_sol (p ^ k) 79 hcop (-60)
    refine ⟨⟨1, by norm_num⟩, ⟨1, by norm_num⟩, 5 + 6 * t.val,
      by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
      by omega, by omega, by omega, ?_⟩
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast [Fin.val_mk, ZMod.natCast_val, ZMod.cast_id]
    linear_combination (12 : ZMod (p ^ k)) * ht

/-- Nevertheless there is no integer companion at all for positive odd
inputs below 23, as proved by the existing finite divisibility obstruction. -/
theorem no_global_small_inputs_23 :
    ¬ ∃ (c d : Fin 23) (b : ℕ),
      0 < c.val ∧ 0 < d.val ∧ c.val % 2 = 1 ∧ d.val % 2 = 1 ∧
      23 * b * (3 * c.val + 1) * (3 * d.val + 1) =
        70 * c.val * d.val * (3 * b + 1) := by
  rintro ⟨c, d, b, hc, hd, hco, hdo, heq⟩
  exact no_quadratic_cross_identity_23 c d b hc hd hco hdo heq

end CollatzMoonshot.Obstructions.ArithmeticLifts
