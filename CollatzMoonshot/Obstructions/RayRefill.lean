import CollatzMoonshot.Obstructions.CoefficientRay

/-! Two local six-step returns to the inherited fixed-offset signature.
These are actual positive `tstep` pairs, not a hard-family CRT lifting theorem. -/

namespace CollatzMoonshot.Obstructions.ArithmeticLifts.RestrictedRepair

open CollatzMoonshot.FrontB

def refill0A (t : ℕ) : ℕ := 499 + 4608 * t
def refill0B (t : ℕ) : ℕ := 8 + 64 * t
def refill1A (t : ℕ) : ℕ := 9715 + 13824 * t
def refill1B (t : ℕ) : ℕ := 46 + 64 * t


private theorem tstep_chain6 {a b c d e f g : ℕ}
    (h1 : tstep a = b) (h2 : tstep b = c) (h3 : tstep c = d)
    (h4 : tstep d = e) (h5 : tstep e = f) (h6 : tstep f = g) :
    tstep^[6] a = g := by
  show tstep (tstep (tstep (tstep (tstep (tstep a))))) = g
  rw [h1, h2, h3, h4, h5, h6]

/-- The first return has source multiplier 72 and target multiplier 216. -/
theorem refill0_actual (t : ℕ) :
    0 < refill0A t ∧ 0 < refill0B t ∧
    tstep^[6] (refill0A t) = 211 + 1944 * t ∧
    tstep^[6] (refill0B t) = 2 + 9 * t ∧
    refill0A t + 5 = 72 * (refill0B t - 1) ∧
    tstep^[6] (refill0A t) + 5 =
      216 * (tstep^[6] (refill0B t) - 1) ∧
    tstep^[6] (refill0A t) < refill0A t ∧
    tstep^[6] (refill0B t) < refill0B t := by
  have hA : tstep^[6] (499 + 4608 * t) = 211 + 1944 * t := by
    have s1 : tstep (499 + 4608 * t) = 749 + 6912 * t := by
      simp only [tstep]; split <;> omega
    have s2 : tstep (749 + 6912 * t) = 1124 + 10368 * t := by
      simp only [tstep]; split <;> omega
    have s3 : tstep (1124 + 10368 * t) = 562 + 5184 * t := by
      simp only [tstep]; split <;> omega
    have s4 : tstep (562 + 5184 * t) = 281 + 2592 * t := by
      simp only [tstep]; split <;> omega
    have s5 : tstep (281 + 2592 * t) = 422 + 3888 * t := by
      simp only [tstep]; split <;> omega
    have s6 : tstep (422 + 3888 * t) = 211 + 1944 * t := by
      simp only [tstep]; split <;> omega
    exact tstep_chain6 s1 s2 s3 s4 s5 s6
  have hB : tstep^[6] (8 + 64 * t) = 2 + 9 * t := by
    have s1 : tstep (8 + 64 * t) = 4 + 32 * t := by
      simp only [tstep]; split <;> omega
    have s2 : tstep (4 + 32 * t) = 2 + 16 * t := by
      simp only [tstep]; split <;> omega
    have s3 : tstep (2 + 16 * t) = 1 + 8 * t := by
      simp only [tstep]; split <;> omega
    have s4 : tstep (1 + 8 * t) = 2 + 12 * t := by
      simp only [tstep]; split <;> omega
    have s5 : tstep (2 + 12 * t) = 1 + 6 * t := by
      simp only [tstep]; split <;> omega
    have s6 : tstep (1 + 6 * t) = 2 + 9 * t := by
      simp only [tstep]; split <;> omega
    exact tstep_chain6 s1 s2 s3 s4 s5 s6
  simp only [refill0A, refill0B]
  rw [hA, hB]
  refine ⟨by omega, by omega, rfl, rfl, by omega, by omega, by omega, by omega⟩

/-- The second return keeps multiplier 216, while both vertices shrink. -/
theorem refill1_actual (t : ℕ) :
    0 < refill1A t ∧ 0 < refill1B t ∧
    tstep^[6] (refill1A t) = 4099 + 5832 * t ∧
    tstep^[6] (refill1B t) = 20 + 27 * t ∧
    refill1A t + 5 = 216 * (refill1B t - 1) ∧
    tstep^[6] (refill1A t) + 5 =
      216 * (tstep^[6] (refill1B t) - 1) ∧
    tstep^[6] (refill1A t) < refill1A t ∧
    tstep^[6] (refill1B t) < refill1B t := by
  have hA : tstep^[6] (9715 + 13824 * t) = 4099 + 5832 * t := by
    have s1 : tstep (9715 + 13824 * t) = 14573 + 20736 * t := by
      simp only [tstep]; split <;> omega
    have s2 : tstep (14573 + 20736 * t) = 21860 + 31104 * t := by
      simp only [tstep]; split <;> omega
    have s3 : tstep (21860 + 31104 * t) = 10930 + 15552 * t := by
      simp only [tstep]; split <;> omega
    have s4 : tstep (10930 + 15552 * t) = 5465 + 7776 * t := by
      simp only [tstep]; split <;> omega
    have s5 : tstep (5465 + 7776 * t) = 8198 + 11664 * t := by
      simp only [tstep]; split <;> omega
    have s6 : tstep (8198 + 11664 * t) = 4099 + 5832 * t := by
      simp only [tstep]; split <;> omega
    exact tstep_chain6 s1 s2 s3 s4 s5 s6
  have hB : tstep^[6] (46 + 64 * t) = 20 + 27 * t := by
    have s1 : tstep (46 + 64 * t) = 23 + 32 * t := by
      simp only [tstep]; split <;> omega
    have s2 : tstep (23 + 32 * t) = 35 + 48 * t := by
      simp only [tstep]; split <;> omega
    have s3 : tstep (35 + 48 * t) = 53 + 72 * t := by
      simp only [tstep]; split <;> omega
    have s4 : tstep (53 + 72 * t) = 80 + 108 * t := by
      simp only [tstep]; split <;> omega
    have s5 : tstep (80 + 108 * t) = 40 + 54 * t := by
      simp only [tstep]; split <;> omega
    have s6 : tstep (40 + 54 * t) = 20 + 27 * t := by
      simp only [tstep]; split <;> omega
    exact tstep_chain6 s1 s2 s3 s4 s5 s6
  simp only [refill1A, refill1B]
  rw [hA, hB]
  refine ⟨by omega, by omega, rfl, rfl, by omega, by omega, by omega, by omega⟩

/-- A deterministic parameter class with arbitrarily many fresh binary digits. -/
def refillT : ℕ → ℕ
  | 0 => 0
  | k + 1 => 64 * refillT k + 7

theorem refillT_formula (k : ℕ) : 9 * refillT k + 1 = 64 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show 9 * (64 * refillT k + 7) + 1 = 64 ^ (k + 1)
    rw [pow_succ]
    omega

/-- Old auxiliary difference is odd, while the actual six-step output has
`6*k` binary digits in its auxiliary difference and the exact new relation. -/
theorem refill0_fuel (k : ℕ) :
    (refill0B (refillT k) - 1) % 2 = 1 ∧
    tstep^[6] (refill0B (refillT k)) - 1 = 64 ^ k ∧
    tstep^[6] (refill0A (refillT k)) + 5 = 216 * 64 ^ k := by
  obtain ⟨-, -, hA, hB, -, -, -, -⟩ := refill0_actual (refillT k)
  have hf := refillT_formula k
  simp only [refill0A, refill0B] at hA hB ⊢
  rw [hA, hB]
  refine ⟨by omega, by omega, by omega⟩

end CollatzMoonshot.Obstructions.ArithmeticLifts.RestrictedRepair
