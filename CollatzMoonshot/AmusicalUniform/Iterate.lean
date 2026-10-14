/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalAntiKohl

/-!
# Iterates of an RCWA map are affine on deep residue classes

For an RCWA map `σ` with modulus `m` and denominators `c`, put `D = m · ∏_{r < m} c r`.  If
`Dⁱ · E ∣ d`, then `σⁱ (x + d) − σⁱ x` is divisible by `E` and equals the product of the first
`i` piece slopes along the orbit of `x`, times `d` (`rcwa_iterate_diff`).  This is the cylinder
lemma behind Theorem NR_p and the Island Lemma in `AmusicalUniform.lean`.
-/

namespace CollatzMoonshot.Amusical

/-- The common modulus `m · ∏_{r < m} c r` of an RCWA coefficient table. -/
def rcwaDen (m : ℕ) (c : ℤ → ℤ) : ℤ := m * ∏ r ∈ Finset.range m, c r

theorem rcwaDen_pos {σ : ℤ → ℤ} {m : ℕ} {a b c : ℤ → ℤ} (hσ : IsRCWA σ m a b c) :
    0 < rcwaDen m c := by
  unfold rcwaDen
  have hm : (0 : ℤ) < m := by exact_mod_cast hσ.pos
  exact mul_pos hm (Finset.prod_pos fun r _ => (hσ.coeff r).1)

theorem rcwaDen_dvd {σ : ℤ → ℤ} {m : ℕ} {a b c : ℤ → ℤ} (hσ : IsRCWA σ m a b c) (x : ℤ) :
    (m : ℤ) * c (x % m) ∣ rcwaDen m c := by
  have hm : (0 : ℤ) < m := by exact_mod_cast hσ.pos
  have h0 : 0 ≤ x % m := Int.emod_nonneg _ hm.ne'
  have h1 : x % m < m := Int.emod_lt_of_pos _ hm
  obtain ⟨r, hr⟩ : ∃ r : ℕ, (r : ℤ) = x % m := ⟨(x % m).toNat, Int.toNat_of_nonneg h0⟩
  have hrm : r ∈ Finset.range m := by rw [Finset.mem_range]; omega
  rw [← hr]
  exact mul_dvd_mul_left _ (Finset.dvd_prod_of_mem (fun r : ℕ => c r) hrm)

/-- One step of an RCWA map on a deep class. -/
theorem rcwa_step_diff {σ : ℤ → ℤ} {m : ℕ} {a b c : ℤ → ℤ} (hσ : IsRCWA σ m a b c)
    (x d E : ℤ) (hd : rcwaDen m c * E ∣ d) :
    E ∣ σ (x + d) - σ x ∧ c (x % m) * (σ (x + d) - σ x) = a (x % m) * d := by
  obtain ⟨u, hu⟩ := rcwaDen_dvd hσ x
  obtain ⟨v, hv⟩ := hd
  have hmd : (m : ℤ) ∣ d := ⟨c (x % m) * u * E * v, by rw [hv, hu]; ring⟩
  have hmod : (x + d) % m = x % m := by
    obtain ⟨q, hq⟩ := hmd
    rw [hq, Int.add_mul_emod_self_left]
  have heq : c (x % m) * (σ (x + d) - σ x) = a (x % m) * d := by
    have h1 := hσ.eqn (x + d)
    have h2 := hσ.eqn x
    rw [hmod] at h1
    linear_combination h1 - h2
  refine ⟨⟨a (x % m) * m * u * v, ?_⟩, heq⟩
  have hc : c (x % m) ≠ 0 := (hσ.coeff _).1.ne'
  apply mul_left_cancel₀ hc
  rw [heq, hv, hu]
  ring

/-- **Cylinder lemma.**  On the class `x + Dⁱ E ℤ`, the `i`-th iterate of an RCWA map is affine
with slope the product of the piece slopes along the orbit of `x`, and moves the class into
`σⁱ x + E ℤ`. -/
theorem rcwa_iterate_diff {σ : ℤ → ℤ} {m : ℕ} {a b c : ℤ → ℤ} (hσ : IsRCWA σ m a b c) :
    ∀ (i : ℕ) (x d E : ℤ), rcwaDen m c ^ i * E ∣ d →
      E ∣ σ^[i] (x + d) - σ^[i] x ∧
      ((σ^[i] (x + d) - σ^[i] x : ℤ) : ℚ) =
        (∏ l ∈ Finset.range i, ((a (σ^[l] x % m) : ℚ) / c (σ^[l] x % m))) * d := by
  intro i
  induction i with
  | zero =>
    intro x d E hd
    simp only [pow_zero, one_mul] at hd
    simp only [Function.iterate_zero, id, add_sub_cancel_left, Finset.range_zero,
      Finset.prod_empty, one_mul]
    exact ⟨hd, trivial⟩
  | succ i ih =>
    intro x d E hd
    have hd' : rcwaDen m c * (rcwaDen m c ^ i * E) ∣ d := by
      rw [pow_succ] at hd
      have : rcwaDen m c * (rcwaDen m c ^ i * E) = rcwaDen m c ^ i * rcwaDen m c * E := by ring
      rw [this]
      exact hd
    obtain ⟨hdiv, heq⟩ := rcwa_step_diff hσ x d (rcwaDen m c ^ i * E) hd'
    have hx : σ (x + d) = σ x + (σ (x + d) - σ x) := by ring
    obtain ⟨ih1, ih2⟩ := ih (σ x) (σ (x + d) - σ x) E hdiv
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hx]
    refine ⟨ih1, ?_⟩
    rw [ih2, Finset.prod_range_succ']
    simp only [Function.iterate_succ_apply, Function.iterate_zero, id]
    have hc : (c (x % m) : ℚ) ≠ 0 := by exact_mod_cast (hσ.coeff _).1.ne'
    have hq : ((σ (x + d) - σ x : ℤ) : ℚ) = a (x % m) / c (x % m) * d := by
      have heqQ : (c (x % m) : ℚ) * ((σ (x + d) - σ x : ℤ) : ℚ) = a (x % m) * d := by
        exact_mod_cast heq
      rw [div_mul_eq_mul_div, eq_div_iff hc]
      linear_combination heqQ
    rw [hq]
    ring

/-- The `p`-adic valuation of a product of nonzero rationals, bounded above termwise. -/
theorem padicValRat_prod_le {p : ℕ} [Fact p.Prime] (f : ℕ → ℚ) (hf : ∀ l, f l ≠ 0)
    (B : ℕ → ℤ) (hB : ∀ l, padicValRat p (f l) ≤ B l) :
    ∀ k, (∏ l ∈ Finset.range k, f l) ≠ 0 ∧
      padicValRat p (∏ l ∈ Finset.range k, f l) ≤ ∑ l ∈ Finset.range k, B l := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨h0, h1⟩ := ih
    rw [Finset.prod_range_succ, Finset.sum_range_succ]
    refine ⟨mul_ne_zero h0 (hf k), ?_⟩
    rw [padicValRat.mul h0 (hf k)]
    exact add_le_add h1 (hB k)

end CollatzMoonshot.Amusical
