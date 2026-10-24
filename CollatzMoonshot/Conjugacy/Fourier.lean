/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.Ladder

/-!
# The beyond-Terras sign on the Fourier side: decay of fixed frequencies suffices

The beyond-Terras sign `g_j(r) = (−1)^{tstep^[j] r}` depends only on `r mod 2^(j+1)` and is
`2^j`-antiperiodic, so its Fourier coefficients
`G_j(ξ) = 2^{−(j+1)} Σ_{r < 2^(j+1)} g_j(r) e(ξ r / 2^(j+1))` (`fourierCoeff`) live on odd `ξ`.
The research note (§10.6) gave a weighted sufficient condition for `BiasDecays`; this module
replaces it by a weaker, pointwise one and records the recursion it lives on.

* **The reduction** (`bias_div_le_lowFreq_add_tail`): for every `K ≥ 1`,
  `|bias j| / 2^j ≤ Σ_{odd ξ ≤ K} 2‖G_j(ξ)‖/ξ + √(2/K)`.  Parseval (`Σ_ξ ‖G_j(ξ)‖² = 1`,
  `sum_norm_sq_fourierCoeff`) controls every frequency above `K` at once.
* **Pointwise decay suffices** (`LowFreqDecay`, `biasDecays_of_lowFreqDecay`): if each fixed odd
  frequency's coefficient tends to `0`, then `BiasDecays`.  The node needs no uniformity in `ξ`,
  which matters: on the chain `ξ = 3^k` the coefficients rise before they fall (§10.6's
  resonance), so a uniform statement is false at the scale `1/j`.
* **The mirror recursion** (`fourierCoeff_succ`): `G_{j+1}(ξ) = ½ G_j(ξ) + ½ e(ξ(1−4u)/2^{j+2})
  G_j(uξ)` with `3u ≡ 1 (mod 2^(j+1))`, the parity split `g_{j+1}(2s) = g_j(s)`,
  `g_{j+1}(2s+1) = g_j(3s+2)`.
* **Magnitudes alone prove nothing.**  The recursion bounds `‖G_{j+1}(ξ)‖` by the average of
  `‖G_j(ξ)‖` and `‖G_j(uξ)‖`; starting from `‖G_0‖ = 1` on its one odd class this gives only
  `‖G_j‖ ≤ 1`.  So a proof of `LowFreqDecay` must use the phases: it is an exponential-sum
  statement, not a positivity one.  (Measured, `experiments/conjugacy/wbranch.py`: one level of
  the triangle inequality does contract the weighted sum, by `0.88–0.96` for `j ≥ 11`, but only
  because the actual `‖G_j‖` already carries earlier cancellation.)
* **Closure under `ξ ↦ ξ/3`** (`TwoAdicFreqDecay`, `lowFreqDecay_of_twoAdicFreqDecay`):
  unrolling the first branch, `‖G_j(ξ)‖ ≤ Σ_m 2^{−m} ‖G_{j−m}(ξ/3)‖ + 2^{−j}` with `ξ/3` read in
  `ℤ₂`, so the natural node is decay at every fixed odd 2-adic frequency, a family closed under
  division by `3` that contains the integer frequencies.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord

/-- The beyond-Terras sign `(−1)^{tstep^[j] r}` as a real number. -/
def beyondSign (j r : ℕ) : ℝ := if tstep^[j] r % 2 = 0 then 1 else -1

/-- The beyond-Terras sign depends only on its `(j+1)`-bit input truncation. -/
theorem beyondSign_congr_mod {r s : ℕ} (j : ℕ)
    (h : r % 2 ^ (j + 1) = s % 2 ^ (j + 1)) :
    beyondSign j r = beyondSign j s := by
  have ha := accWord_congr_mod j h
  simp only [accWord, decide_eq_decide] at ha
  unfold beyondSign
  rcases Nat.mod_two_eq_zero_or_one (tstep^[j] r) with hr | hr <;>
    rcases Nat.mod_two_eq_zero_or_one (tstep^[j] s) with hs | hs <;>
    simp [hr, hs] at ha ⊢

/-- The Fourier coefficient `G_j(ξ) = 2^{−(j+1)} Σ_{r < 2^(j+1)} g_j(r) e(ξ r / 2^(j+1))` of the
beyond-Terras sign on `ℤ / 2^(j+1)`. -/
noncomputable def fourierCoeff (j ξ : ℕ) : ℂ :=
  ((2 : ℂ) ^ (j + 1))⁻¹ * ∑ r ∈ Finset.range (2 ^ (j + 1)),
    (beyondSign j r : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ξ * r / 2 ^ (j + 1))

/-- The Fourier coefficient at level `j` is periodic in the frequency with period `2^(j+1)`. -/
theorem fourierCoeff_add_period (j ξ k : ℕ) :
    fourierCoeff j (ξ + 2 ^ (j + 1) * k) = fourierCoeff j ξ := by
  unfold fourierCoeff
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  push_cast
  rw [show
      2 * Real.pi * Complex.I * (ξ + 2 ^ (j + 1) * k) * r / 2 ^ (j + 1) =
        2 * Real.pi * Complex.I * ξ * r / 2 ^ (j + 1) +
          ((k * r : ℕ) : ℂ) * (2 * Real.pi * Complex.I) by
    push_cast
    field_simp]
  rw [Complex.exp_add, Complex.exp_periodic.nat_mul_eq]
  simp

/-- Orthogonality of the standard characters, in the normalization used below. -/
private theorem zmodParseval (n : ℕ) [NeZero n] (f : ZMod n → ℂ) :
    ∑ k : ZMod n, Complex.normSq (∑ r : ZMod n, ZMod.stdAddChar (r * k) * f r) =
      n * ∑ r : ZMod n, Complex.normSq (f r) := by
  apply Complex.ofReal_injective
  push_cast
  have hchar (r s k : ZMod n) :
      (starRingEnd ℂ) (ZMod.stdAddChar (r * k)) * ZMod.stdAddChar (s * k) =
        ZMod.stdAddChar ((s - r) * k) := by
    rw [← AddChar.inv_apply_eq_conj, ← AddChar.map_neg_eq_inv,
      ← AddChar.map_add_eq_mul]
    congr 1
    ring
  have horth (a : ZMod n) :
      ∑ k : ZMod n, ZMod.stdAddChar (k * a) =
        (if a = 0 then n else 0 : ℂ) := by
    simpa using AddChar.sum_mulShift a (ZMod.isPrimitive_stdAddChar n)
  simp_rw [Complex.normSq_eq_conj_mul_self, map_sum, map_mul]
  simp_rw [Finset.sum_mul_sum]
  calc
    _ = ∑ r : ZMod n, ∑ s : ZMod n,
        (starRingEnd ℂ) (f r) * f s *
          ∑ k : ZMod n, ZMod.stdAddChar (k * (s - r)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [mul_comm k, ← hchar]
      ring
    _ = ∑ r : ZMod n, ∑ s : ZMod n,
        (starRingEnd ℂ) (f r) * f s * (if s - r = 0 then n else 0 : ℂ) := by
      simp_rw [horth]
    _ = (n : ℂ) * ∑ r : ZMod n, (starRingEnd ℂ) (f r) * f r := by
      simp [sub_eq_zero, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring

/-- `ZMod.finEquiv` sends a bounded natural to its residue class. -/
private theorem finEquiv_apply_cast (n : ℕ) [NeZero n] (r : Fin n) :
    (ZMod.finEquiv n).toEquiv r = (r : ZMod n) := by
  cases n with
  | zero => exact Fin.elim0 r
  | succ n =>
      apply Fin.ext
      change r.val = r.val % (n + 1)
      exact (Nat.mod_eq_of_lt r.isLt).symm

/-- Reindex the defining range sum as a sum over `ZMod`. -/
private theorem fourierCoeff_eq_zmod (j ξ : ℕ) :
    fourierCoeff j ξ =
      let n : ℕ := 2 ^ (j + 1)
      (n : ℂ)⁻¹ * ∑ r : ZMod n,
        ZMod.stdAddChar ((ξ : ZMod n) * r) * (beyondSign j r.val : ℂ) := by
  let n : ℕ := 2 ^ (j + 1)
  letI : NeZero n := ⟨by simp [n]⟩
  unfold fourierCoeff
  dsimp only
  rw [show (2 : ℂ) ^ (j + 1) = (n : ℂ) by simp [n]]
  congr 1
  change (∑ r ∈ Finset.range n,
    (beyondSign j r : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ξ * r / n)) = _
  rw [← Fin.sum_univ_eq_sum_range]
  rw [← Equiv.sum_comp (ZMod.finEquiv n).toEquiv]
  apply Finset.sum_congr rfl
  intro r hr
  rw [finEquiv_apply_cast]
  rw [show (ξ : ZMod n) * (r : ZMod n) = (((ξ * r : ℕ) : ℤ) : ZMod n) by
    norm_cast]
  rw [ZMod.stdAddChar_coe]
  simp only [ZMod.val_natCast]
  have hrn : (r : ℕ) < 2 ^ (j + 1) := by simpa [n] using r.isLt
  rw [Nat.mod_eq_of_lt hrn]
  rw [show
    2 * Real.pi * Complex.I * (((ξ * r : ℕ) : ℤ) : ℂ) / (n : ℂ) =
      2 * Real.pi * Complex.I * (ξ : ℂ) * (r : ℂ) / (n : ℂ) by
    push_cast
    ring]
  ring

/-- **Parseval.**  The sign has unit modulus, so the squared Fourier coefficients over one period
sum to `1`.  Orthogonality of the characters `r ↦ e(ξ r / 2^(j+1))` on `ℤ / 2^(j+1)`. -/
theorem sum_norm_sq_fourierCoeff (j : ℕ) :
    ∑ ξ ∈ Finset.range (2 ^ (j + 1)), ‖fourierCoeff j ξ‖ ^ 2 = 1 := by
  let n : ℕ := 2 ^ (j + 1)
  letI : NeZero n := ⟨by simp [n]⟩
  let f : ZMod n → ℂ := fun r => (beyondSign j r.val : ℂ)
  have hcoeff (k : ZMod n) :
      fourierCoeff j k.val =
        (n : ℂ)⁻¹ * ∑ r : ZMod n, ZMod.stdAddChar (k * r) * f r := by
    rw [fourierCoeff_eq_zmod]
    dsimp only
    rw [ZMod.natCast_zmod_val]
  change ∑ ξ ∈ Finset.range n, ‖fourierCoeff j ξ‖ ^ 2 = 1
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ k : ZMod n, ‖fourierCoeff j k.val‖ ^ 2 := by
      rw [← Equiv.sum_comp (ZMod.finEquiv n).toEquiv]
      apply Finset.sum_congr rfl
      intro k hk
      rw [finEquiv_apply_cast, ZMod.val_natCast_of_lt k.isLt]
    _ = ∑ k : ZMod n, Complex.normSq
        ((n : ℂ)⁻¹ * ∑ r : ZMod n, ZMod.stdAddChar (r * k) * f r) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hcoeff, ← Complex.normSq_eq_norm_sq]
      congr 2
      apply Finset.sum_congr rfl
      intro r hr
      rw [mul_comm r k]
    _ = 1 := by
      simp only [map_mul]
      rw [← Finset.mul_sum]
      rw [zmodParseval]
      simp only [Complex.normSq_inv, Complex.normSq_natCast]
      have hf (r : ZMod n) : Complex.normSq (f r) = 1 := by
        dsimp only [f, beyondSign]
        split_ifs <;> norm_num [Complex.normSq_ofReal]
      simp_rw [hf]
      simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
      apply inv_mul_cancel₀
      apply mul_ne_zero <;> exact_mod_cast (NeZero.ne n)

/-- The beyond-Terras sign flips on translation by half of its period. -/
private theorem beyondSign_add_half_period (j r : ℕ) :
    beyondSign j (r + 2 ^ j) = -beyondSign j r := by
  have h := accWord_add_two_pow r j
  simp only [accWord, decide_eq_decide] at h
  unfold beyondSign
  rcases Nat.mod_two_eq_zero_or_one (tstep^[j] r) with hr | hr <;>
    rcases Nat.mod_two_eq_zero_or_one (tstep^[j] (r + 2 ^ j)) with hs | hs <;>
    simp [hr, hs] at h ⊢

/-- Jordan's inequality gives the needed bound for a half-period geometric sum. -/
private theorem norm_half_geom_sum_le (N k : ℕ) (hN : 0 < N) (hk : 1 ≤ k)
    (hkN : k ≤ N) (hodd : Odd k) :
    ‖∑ r ∈ Finset.range N,
        Complex.exp (-2 * Real.pi * Complex.I * k * r / (2 * N))‖ ≤ (N : ℝ) / k := by
  let q : ℂ := Complex.exp (-2 * Real.pi * Complex.I * k / (2 * N))
  have hterm (r : ℕ) :
      Complex.exp (-2 * Real.pi * Complex.I * k * r / (2 * N)) = q ^ r := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp [show (N : ℂ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hN)]
  simp_rw [hterm]
  have hqpow : q ^ N = -1 := by
    obtain ⟨a, rfl⟩ := hodd
    rw [← Complex.exp_nat_mul]
    rw [show
        (N : ℂ) * (-2 * Real.pi * Complex.I * (((2 * a + 1 : ℕ) : ℂ)) / (2 * N)) =
          -(Real.pi * Complex.I) + (-(a : ℂ)) * (2 * Real.pi * Complex.I) by
      push_cast
      field_simp [show (N : ℂ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hN)]
      ring]
    rw [Complex.exp_add]
    rw [show Complex.exp (-(Real.pi * Complex.I)) = -1 by
      rw [Complex.exp_neg, Complex.exp_pi_mul_I]
      norm_num]
    rw [show (-(a : ℂ)) * (2 * Real.pi * Complex.I) =
        -((a : ℂ) * (2 * Real.pi * Complex.I)) by ring,
      Complex.exp_neg, Complex.exp_periodic.nat_mul_eq]
    norm_num
  have hprod := geom_sum_mul q N
  rw [hqpow] at hprod
  have hnormprod := congrArg norm hprod
  simp only [norm_mul, norm_sub_rev] at hnormprod
  have hqsub :
      ‖1 - q‖ = 2 * Real.sin (Real.pi * k / (2 * N)) := by
    rw [norm_sub_rev]
    rw [show q = Complex.exp (Complex.I * (-(Real.pi * k / N) : ℝ)) by
      dsimp [q]
      congr 1
      push_cast
      field_simp [show (N : ℂ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hN)]]
    rw [Complex.norm_exp_I_mul_ofReal_sub_one]
    norm_cast
    rw [show -(Real.pi * (k : ℝ) / N) / 2 = -(Real.pi * k / (2 * N)) by ring]
    have harg_le : Real.pi * (k : ℝ) / (2 * N) ≤ Real.pi / 2 := by
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * N)
        (by positivity : (0 : ℝ) < 2)).2
      nlinarith [Real.pi_pos, show (k : ℝ) ≤ N by exact_mod_cast hkN]
    have hsin0 : 0 ≤ Real.sin (Real.pi * k / (2 * N)) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
        (harg_le.trans (half_le_self Real.pi_pos.le))
    rw [Real.sin_neg, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hsin0]
    norm_num
  have hsin : (k : ℝ) / N ≤ Real.sin (Real.pi * k / (2 * N)) := by
    have harg0 : 0 ≤ Real.pi * (k : ℝ) / (2 * N) := by positivity
    have harg_le : Real.pi * (k : ℝ) / (2 * N) ≤ Real.pi / 2 := by
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * N)
        (by positivity : (0 : ℝ) < 2)).2
      nlinarith [Real.pi_pos, show (k : ℝ) ≤ N by exact_mod_cast hkN]
    have := Real.mul_le_sin harg0 harg_le
    convert this using 1 <;> field_simp <;> ring
  rw [hqsub] at hnormprod
  have hkR : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hqpos : 0 < 2 * Real.sin (Real.pi * k / (2 * N)) := by
    have : 0 < Real.sin (Real.pi * k / (2 * N)) :=
      lt_of_lt_of_le (div_pos hkR hNR) hsin
    positivity
  norm_num at hnormprod
  have hsumeq : ‖∑ i ∈ Finset.range N, q ^ i‖ =
      2 / (2 * Real.sin (Real.pi * k / (2 * N))) :=
    (eq_div_iff hqpos.ne').2 hnormprod
  rw [hsumeq]
  apply (div_le_div_of_nonneg_left (by norm_num)
    (mul_pos (by norm_num) (div_pos hkR hNR))
    (mul_le_mul_of_nonneg_left hsin (by norm_num))).trans_eq
  field_simp

/-- The repository normalization is the inverse `ZMod` DFT of the sign. -/
private theorem invDFT_beyondSign (j : ℕ) :
    let n : ℕ := 2 ^ (j + 1)
    let f : ZMod n → ℂ := fun r => (beyondSign j r.val : ℂ)
    ∀ k : ZMod n, ZMod.dft.symm f k = fourierCoeff j k.val := by
  dsimp only
  let n : ℕ := 2 ^ (j + 1)
  letI : NeZero n := ⟨by simp [n]⟩
  intro k
  rw [ZMod.invDFT_apply, fourierCoeff_eq_zmod]
  dsimp only
  rw [ZMod.natCast_zmod_val]
  simp only [smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  rw [mul_comm r k]

/-- Fourier inversion paired with the indicator of the first half-period. -/
private theorem bias_eq_fourier_window (j : ℕ) :
    let N : ℕ := 2 ^ j
    let n : ℕ := 2 ^ (j + 1)
    (bias j : ℂ) = ∑ k : ZMod n, fourierCoeff j k.val *
      ∑ r ∈ Finset.range N, ZMod.stdAddChar (-((r : ZMod n) * k)) := by
  dsimp only
  let N : ℕ := 2 ^ j
  let n : ℕ := 2 ^ (j + 1)
  letI : NeZero n := ⟨by simp [n, N]⟩
  let f : ZMod n → ℂ := fun r => (beyondSign j r.val : ℂ)
  have hG (k : ZMod n) : ZMod.dft.symm f k = fourierCoeff j k.val := by
    exact invDFT_beyondSign j k
  calc
    (bias j : ℂ) = ∑ r ∈ Finset.range N, f (r : ZMod n) := by
      unfold bias
      rw [Int.cast_sum]
      apply Finset.sum_congr rfl
      intro r hr
      have hNn : N ≤ n := by
        have hp : 0 < 2 ^ j := by positivity
        simp only [N, n, pow_succ]
        omega
      have hrn : r < n := (Finset.mem_range.mp hr).trans_le hNn
      simp only [f, ZMod.val_natCast_of_lt hrn, beyondSign]
      split_ifs <;> norm_num
    _ = ∑ r ∈ Finset.range N, ZMod.dft (ZMod.dft.symm f) (r : ZMod n) := by
      rw [LinearEquiv.apply_symm_apply]
    _ = ∑ r ∈ Finset.range N, ∑ k : ZMod n,
        ZMod.stdAddChar (-((r : ZMod n) * k)) * fourierCoeff j k.val := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [ZMod.dft_apply]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [smul_eq_mul, hG]
      rw [mul_comm k]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring

/-- Half-period antiperiodicity kills every even Fourier frequency. -/
private theorem fourierCoeff_eq_zero_of_even (j ξ : ℕ) (hξ : Even ξ) :
    fourierCoeff j ξ = 0 := by
  let N : ℕ := 2 ^ j
  have hN : 0 < N := by simp [N]
  have hn : 2 ^ (j + 1) = N + N := by
    simp only [N, pow_succ]
    omega
  have hnC : (2 : ℂ) ^ (j + 1) = ((N + N : ℕ) : ℂ) := by
    exact_mod_cast hn
  unfold fourierCoeff
  rw [hn, hnC, Finset.sum_range_add]
  push_cast
  have hsecond (s : ℕ) :
      (beyondSign j (N + s) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ξ * (N + s) / (N + N)) =
        -((beyondSign j s : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ξ * s / (N + N))) := by
    rw [show beyondSign j (N + s) = -beyondSign j s by
      simpa [add_comm] using beyondSign_add_half_period j s]
    have hphase :
        Complex.exp (2 * Real.pi * Complex.I * ξ * (N + s) / (N + N)) =
          Complex.exp (2 * Real.pi * Complex.I * ξ * s / (N + N)) := by
      obtain ⟨a, ha⟩ := hξ
      rw [ha]
      rw [show
          2 * Real.pi * Complex.I * (((a + a : ℕ) : ℂ)) *
                ((N : ℂ) + (s : ℂ)) /
              ((N : ℂ) + (N : ℂ)) =
            2 * Real.pi * Complex.I * (((a + a : ℕ) : ℂ)) * (s : ℂ) /
                ((N : ℂ) + (N : ℂ)) +
              (a : ℂ) * (2 * Real.pi * Complex.I) by
        push_cast
        field_simp [show (N : ℂ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hN)]
        ring]
      rw [Complex.exp_add, Complex.exp_periodic.nat_mul_eq]
      simp
    rw [hphase]
    push_cast
    ring
  have hsumsecond :
      ∑ s ∈ Finset.range N,
          (beyondSign j (N + s) : ℂ) *
            Complex.exp (2 * Real.pi * Complex.I * ξ * (N + s) / (N + N)) =
        -∑ s ∈ Finset.range N,
          (beyondSign j s : ℂ) *
            Complex.exp (2 * Real.pi * Complex.I * ξ * s / (N + N)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun s _ => hsecond s
  rw [hsumsecond, add_neg_cancel, mul_zero]

/-- The Fourier transform of the real-valued sign has conjugate-symmetric magnitudes. -/
private theorem norm_fourierCoeff_sub_period (j k : ℕ) (hk : k ≤ 2 ^ (j + 1)) :
    ‖fourierCoeff j (2 ^ (j + 1) - k)‖ = ‖fourierCoeff j k‖ := by
  let n : ℕ := 2 ^ (j + 1)
  letI : NeZero n := ⟨by simp [n]⟩
  have hcast : ((n - k : ℕ) : ZMod n) = -(k : ZMod n) := by
    rw [Nat.cast_sub (by simpa [n] using hk)]
    simp
  have hconj : fourierCoeff j (n - k) = (starRingEnd ℂ) (fourierCoeff j k) := by
    rw [fourierCoeff_eq_zmod, fourierCoeff_eq_zmod]
    dsimp only
    rw [hcast]
    simp only [neg_mul, AddChar.map_neg_eq_inv, AddChar.inv_apply_eq_conj, map_mul, map_sum,
      map_inv₀, map_natCast]
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    rw [show (starRingEnd ℂ) (beyondSign j r.val : ℂ) =
        (beyondSign j r.val : ℂ) by
      push_cast
      simp]
  simp only [n] at hconj ⊢
  rw [hconj]
  exact Complex.norm_conj _

/-- Natural-number form of the half-window Fourier inversion identity. -/
private theorem bias_eq_sum_range_fourier_window (j : ℕ) :
    let N : ℕ := 2 ^ j
    let n : ℕ := 2 ^ (j + 1)
    (bias j : ℂ) = ∑ k ∈ Finset.range n, fourierCoeff j k *
      ∑ r ∈ Finset.range N,
        Complex.exp (-2 * Real.pi * Complex.I * k * r / n) := by
  dsimp only
  let N : ℕ := 2 ^ j
  let n : ℕ := 2 ^ (j + 1)
  letI : NeZero n := ⟨by simp [n]⟩
  rw [bias_eq_fourier_window]
  change (∑ k : ZMod n, fourierCoeff j k.val *
    ∑ r ∈ Finset.range N, ZMod.stdAddChar (-((r : ZMod n) * k))) = _
  rw [← Fin.sum_univ_eq_sum_range]
  rw [← Equiv.sum_comp (ZMod.finEquiv n).toEquiv]
  apply Finset.sum_congr rfl
  intro k hk
  rw [finEquiv_apply_cast]
  rw [ZMod.val_natCast_of_lt k.isLt]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  rw [show -((r : ZMod n) * (k : ZMod n)) =
      (((-((r * k : ℕ) : ℤ)) : ℤ) : ZMod n) by
    push_cast
    ring]
  rw [ZMod.stdAddChar_coe]
  congr 1
  dsimp [n]
  push_cast
  field_simp

/-- The two signed representatives of a frequency give conjugate half-window sums. -/
private theorem norm_fourierWindow_sub_period (j k : ℕ) (hk : k ≤ 2 ^ (j + 1)) :
    let N : ℕ := 2 ^ j
    let n : ℕ := 2 ^ (j + 1)
    ‖∑ r ∈ Finset.range N,
        Complex.exp (-2 * Real.pi * Complex.I * (n - k) * r / n)‖ =
      ‖∑ r ∈ Finset.range N,
        Complex.exp (-2 * Real.pi * Complex.I * k * r / n)‖ := by
  dsimp only
  let n : ℕ := 2 ^ (j + 1)
  have hn : 0 < n := by simp [n]
  have hterm (r : ℕ) :
      Complex.exp (-2 * Real.pi * Complex.I * (n - k) * r / n) =
        (starRingEnd ℂ) (Complex.exp (-2 * Real.pi * Complex.I * k * r / n)) := by
    rw [show
        -2 * Real.pi * Complex.I * ((n : ℂ) - (k : ℂ)) * (r : ℂ) / (n : ℂ) =
          2 * Real.pi * Complex.I * (k : ℂ) * (r : ℂ) / (n : ℂ) +
            (((-(r : ℤ) : ℤ) : ℂ)) * (2 * Real.pi * Complex.I) by
      push_cast
      field_simp [show (n : ℂ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hn)]
      ring]
    rw [Complex.exp_add, Complex.exp_periodic.int_mul_eq, Complex.exp_zero, mul_one]
    rw [← Complex.exp_conj]
    congr 1
    push_cast
    simp [map_ofNat]
  have hsum :
      ∑ r ∈ Finset.range (2 ^ j),
          Complex.exp (-2 * Real.pi * Complex.I * (n - k) * r / n) =
        ∑ r ∈ Finset.range (2 ^ j),
          (starRingEnd ℂ) (Complex.exp (-2 * Real.pi * Complex.I * k * r / n)) := by
    exact Finset.sum_congr rfl fun r _ => hterm r
  rw [hsum]
  rw [← map_sum]
  exact Complex.norm_conj _

/-- Fourier inversion, paired signed frequencies, and Jordan's inequality. -/
private theorem bias_div_le_weighted_fourier (j : ℕ) :
    |(bias j : ℝ)| / 2 ^ j ≤
      ∑ k ∈ Finset.Icc 1 (2 ^ j), 2 * ‖fourierCoeff j k‖ / k := by
  let N : ℕ := 2 ^ j
  let n : ℕ := 2 ^ (j + 1)
  let W : ℕ → ℂ := fun k => ∑ r ∈ Finset.range N,
    Complex.exp (-2 * Real.pi * Complex.I * k * r / n)
  let A : ℕ → ℝ := fun k => ‖fourierCoeff j k‖ * ‖W k‖
  have hN : 0 < N := by simp [N]
  have hn : n = 2 * N := by simp [n, N, pow_succ, mul_comm]
  have hA0 : A 0 = 0 := by
    simp [A, fourierCoeff_eq_zero_of_even j 0 (by simp)]
  have hAsymm (k : ℕ) (hk : k ≤ n) : A (n - k) = A k := by
    dsimp only [A, W]
    rw [show n = 2 ^ (j + 1) by simp [n], norm_fourierCoeff_sub_period j k (by simpa [n] using hk)]
    congr 1
    rw [Nat.cast_sub (by simpa [n] using hk)]
    simpa [n, N] using norm_fourierWindow_sub_period j k (by simpa [n] using hk)
  have hAbound (k : ℕ) (hk : k ∈ Finset.Icc 1 N) :
      A k ≤ (N : ℝ) * (‖fourierCoeff j k‖ / k) := by
    simp only [Finset.mem_Icc] at hk
    dsimp only [A]
    rcases Nat.even_or_odd k with heven | hodd
    · rw [fourierCoeff_eq_zero_of_even j k heven]
      simp
    · dsimp only [W]
      have hw := norm_half_geom_sum_le N k hN hk.1 hk.2 hodd
      have hw' :
          ‖∑ r ∈ Finset.range N,
              Complex.exp (-2 * Real.pi * Complex.I * k * r / n)‖ ≤ (N : ℝ) / k := by
        simpa [hn] using hw
      calc
        _ ≤ ‖fourierCoeff j k‖ * ((N : ℝ) / k) :=
          mul_le_mul_of_nonneg_left hw' (norm_nonneg _)
        _ = _ := by
          have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hk.1)
          field_simp
  have hbias : |(bias j : ℝ)| ≤ ∑ k ∈ Finset.range n, A k := by
    have hfourier := bias_eq_sum_range_fourier_window j
    change (bias j : ℂ) = ∑ k ∈ Finset.range n, fourierCoeff j k * W k at hfourier
    calc
      |(bias j : ℝ)| = ‖(bias j : ℂ)‖ := by simp [Real.norm_eq_abs]
      _ = ‖∑ k ∈ Finset.range n, fourierCoeff j k * W k‖ := by rw [hfourier]
      _ ≤ ∑ k ∈ Finset.range n, ‖fourierCoeff j k * W k‖ := norm_sum_le _ _
      _ = ∑ k ∈ Finset.range n, A k := by
        apply Finset.sum_congr rfl
        intro k hk
        simp [A, norm_mul]
  have hpair : ∑ k ∈ Finset.range n, A k ≤
      2 * ∑ k ∈ Finset.Icc 1 N, A k := by
    have hNn : N + 1 ≤ n := by omega
    have hn1 : 1 ≤ n := by omega
    have hreflect : ∑ k ∈ Finset.Ico (N + 1) n, A k =
        ∑ k ∈ Finset.Ico 1 N, A k := by
      have href := Finset.sum_Ico_reflect A 1 (m := N) (n := n) (by omega)
      have hleft : ∑ k ∈ Finset.Ico 1 N, A (n - k) =
          ∑ k ∈ Finset.Ico 1 N, A k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hAsymm k]
        simp only [Finset.mem_Ico] at hk
        omega
      rw [hleft] at href
      rw [hn] at href ⊢
      have hlo : 2 * N + 1 - N = N + 1 := by omega
      have hhi : 2 * N + 1 - 1 = 2 * N := by omega
      rw [hlo, hhi] at href
      exact href.symm
    have hsub : ∑ k ∈ Finset.Ico 1 N, A k ≤
        ∑ k ∈ Finset.Ico 1 (N + 1), A k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        simp only [Finset.mem_Ico] at hk ⊢
        omega
      · intro k hk hnot
        positivity
    rw [← Finset.sum_range_add_sum_Ico A hn1]
    simp only [Finset.sum_range_one, hA0, zero_add]
    rw [← Finset.sum_Ico_consecutive A (by omega : 1 ≤ N + 1) hNn]
    rw [hreflect]
    have hIcc : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
      ext k
      simp
    rw [hIcc]
    linarith
  have hweighted : ∑ k ∈ Finset.Icc 1 N, A k ≤
      (N : ℝ) * ∑ k ∈ Finset.Icc 1 N, ‖fourierCoeff j k‖ / k := by
    calc
      _ ≤ ∑ k ∈ Finset.Icc 1 N,
          (N : ℝ) * (‖fourierCoeff j k‖ / k) :=
        Finset.sum_le_sum fun k hk => hAbound k hk
      _ = _ := by rw [Finset.mul_sum]
  change |(bias j : ℝ)| / (2 : ℝ) ^ j ≤
    ∑ k ∈ Finset.Icc 1 N, 2 * ‖fourierCoeff j k‖ / k
  rw [show (2 : ℝ) ^ j = (N : ℝ) by norm_cast]
  calc
    |(bias j : ℝ)| / (N : ℝ) ≤
        (2 * ∑ k ∈ Finset.Icc 1 N, A k) / N :=
      div_le_div_of_nonneg_right (hbias.trans hpair) (by positivity)
    _ ≤ (2 * ((N : ℝ) * ∑ k ∈ Finset.Icc 1 N,
        ‖fourierCoeff j k‖ / k)) / N := by
      gcongr
    _ = ∑ k ∈ Finset.Icc 1 N, 2 * ‖fourierCoeff j k‖ / k := by
      field_simp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring

/-- At most half of the Parseval energy lies in the strictly positive half-spectrum. -/
private theorem two_mul_sum_sq_fourierCoeff_Ico_le (j : ℕ) :
    2 * ∑ k ∈ Finset.Ico 1 (2 ^ j), ‖fourierCoeff j k‖ ^ 2 ≤ 1 := by
  let N : ℕ := 2 ^ j
  let n : ℕ := 2 ^ (j + 1)
  let Q : ℕ → ℝ := fun k => ‖fourierCoeff j k‖ ^ 2
  have hN : 0 < N := by simp [N]
  have hn : n = 2 * N := by simp [n, N, pow_succ, mul_comm]
  have hNn : N + 1 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hreflect : ∑ k ∈ Finset.Ico (N + 1) n, Q k =
      ∑ k ∈ Finset.Ico 1 N, Q k := by
    have href := Finset.sum_Ico_reflect Q 1 (m := N) (n := n) (by omega)
    have hleft : ∑ k ∈ Finset.Ico 1 N, Q (n - k) =
        ∑ k ∈ Finset.Ico 1 N, Q k := by
      apply Finset.sum_congr rfl
      intro k hk
      dsimp only [Q]
      rw [norm_fourierCoeff_sub_period j k]
      simp only [Finset.mem_Ico] at hk
      omega
    rw [hleft] at href
    rw [hn] at href ⊢
    have hlo : 2 * N + 1 - N = N + 1 := by omega
    have hhi : 2 * N + 1 - 1 = 2 * N := by omega
    rw [hlo, hhi] at href
    exact href.symm
  have hdecomp :
      1 = Q 0 + ((∑ k ∈ Finset.Ico 1 N, Q k) + Q N) +
        ∑ k ∈ Finset.Ico (N + 1) n, Q k := by
    calc
      1 = ∑ k ∈ Finset.range n, Q k := by
        simpa only [Q, n] using (sum_norm_sq_fourierCoeff j).symm
      _ = (∑ k ∈ Finset.range 1, Q k) + ∑ k ∈ Finset.Ico 1 n, Q k :=
        (Finset.sum_range_add_sum_Ico Q hn1).symm
      _ = Q 0 + ∑ k ∈ Finset.Ico 1 n, Q k := by simp
      _ = Q 0 + ((∑ k ∈ Finset.Ico 1 (N + 1), Q k) +
          ∑ k ∈ Finset.Ico (N + 1) n, Q k) := by
        rw [Finset.sum_Ico_consecutive Q (by omega : 1 ≤ N + 1) hNn]
      _ = _ := by
        rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ N)]
        ring
  change 2 * ∑ k ∈ Finset.Ico 1 N, Q k ≤ 1
  rw [hreflect] at hdecomp
  have hq0 : 0 ≤ Q 0 := by positivity
  have hqN : 0 ≤ Q N := by positivity
  linarith

/-- **The reduction.**  For every `K ≥ 1`,
`|bias j| / 2^j ≤ Σ_{odd ξ ≤ K} 2 ‖G_j(ξ)‖ / ξ + √(2/K)`.

Proof.  Write `n = 2^(j+1)`.  The window `[0, 2^j)` is half a period, so by Parseval
`bias j = n Σ_ξ G_j(ξ) · conj(H(ξ))` with `H` the Fourier coefficient of the window's indicator;
`|H(ξ)| = n⁻¹ / |sin(π ξ / n)|` at odd `ξ`, and `G_j` vanishes at even `ξ` by antiperiodicity.
So `|bias j| / 2^j ≤ 2^{−j} Σ_{odd ξ} ‖G_j(ξ)‖ / |sin(π ξ / n)|`.  Take signed representatives
`ξ ∈ (−n/2, n/2]`; Jordan's inequality gives `2^{−j} / |sin(π ξ / n)| ≤ 1/|ξ|`.  The frequencies
with `|ξ| ≤ K` contribute at most `Σ_{odd ξ ≤ K} (‖G_j(ξ)‖ + ‖G_j(−ξ)‖)/ξ`, and
`‖G_j(−ξ)‖ = ‖G_j(ξ)‖` because the sign is real.  The rest is at most
`2^{−j} (Σ ‖G_j‖²)^{1/2} (Σ_{|ξ| > K} (n / 2|ξ|)²)^{1/2} ≤ 2^{−j} · 1 · n / √(2K) = √(2/K)`
by Cauchy–Schwarz, Parseval and `Σ_{m > K} m⁻² ≤ 1/K`.

Evidence with control (`experiments/conjugacy/lowfreq.py`, `j ≤ 24`, `K` up to `729`): the
inequality holds with positive slack at every `(j, K)`, and with the `√(2/K)` term deleted it
fails from `j = 13` on, so the tail term is load-bearing.  Confidence 97%. -/
theorem bias_div_le_lowFreq_add_tail (j K : ℕ) (hK : 1 ≤ K) :
    |(bias j : ℝ)| / 2 ^ j ≤
      (∑ ξ ∈ (Finset.range (K + 1)).filter Odd, 2 * ‖fourierCoeff j ξ‖ / ξ) +
        Real.sqrt (2 / K) := by
  let N : ℕ := 2 ^ j
  let F : ℕ → ℝ := fun k => 2 * ‖fourierCoeff j k‖ / k
  let O := (Finset.Icc 1 N).filter Odd
  let T := O.filter fun k => K < k
  have hweighted := bias_div_le_weighted_fourier j
  change |(bias j : ℝ)| / 2 ^ j ≤ _ at hweighted
  have hoddSum : ∑ k ∈ Finset.Icc 1 N, F k = ∑ k ∈ O, F k := by
    symm
    apply Finset.sum_subset
    · intro k hk
      exact (Finset.mem_filter.mp hk).1
    intro k hk hko
    simp only [O, Finset.mem_filter] at hko
    rcases Nat.even_or_odd k with heven | hodd
    · simp [F, fourierCoeff_eq_zero_of_even j k heven]
    · exact (hko ⟨hk, hodd⟩).elim
  have hlow : ∑ k ∈ O.filter (fun k => ¬K < k), F k ≤
      ∑ k ∈ (Finset.range (K + 1)).filter Odd, F k := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      simp only [O, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at hk ⊢
      exact ⟨by omega, hk.1.2⟩
    · intro k hk hnot
      positivity
  have htail : ∑ k ∈ T, F k ≤ Real.sqrt (2 / K) := by
    by_cases hKN : K ≤ N
    · have hTsub : T ⊆ Finset.Ico 1 N := by
        intro k hk
        simp only [T, O, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico] at hk ⊢
        refine ⟨hk.1.1.1, ?_⟩
        cases j with
        | zero =>
            simp [N] at hk
            omega
        | succ j =>
            have hevenN : (N % 2) = 0 := by simp [N, pow_succ]
            rw [Nat.odd_iff] at hk
            omega
      have henergy : ∑ k ∈ T, ‖fourierCoeff j k‖ ^ 2 ≤ (1 / 2 : ℝ) := by
        have hsub : ∑ k ∈ T, ‖fourierCoeff j k‖ ^ 2 ≤
            ∑ k ∈ Finset.Ico 1 N, ‖fourierCoeff j k‖ ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hTsub
          intro k hk hnot
          positivity
        have hhalf := two_mul_sum_sq_fourierCoeff_Ico_le j
        change 2 * ∑ k ∈ Finset.Ico 1 N, ‖fourierCoeff j k‖ ^ 2 ≤ 1 at hhalf
        linarith
      have hrecip : ∑ k ∈ T, ((k : ℝ)⁻¹) ^ 2 ≤ (K : ℝ)⁻¹ := by
        calc
          _ ≤ ∑ k ∈ Finset.Ioc K N, ((k : ℝ)⁻¹) ^ 2 := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro k hk
              simp only [T, O, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at hk ⊢
              exact ⟨hk.2, hk.1.1.2⟩
            · intro k hk hnot
              positivity
          _ = ∑ k ∈ Finset.Ioc K N, (((k : ℝ) ^ 2)⁻¹) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [inv_pow]
          _ ≤ (K : ℝ)⁻¹ - (N : ℝ)⁻¹ :=
            sum_Ioc_inv_sq_le_sub (by omega) hKN
          _ ≤ (K : ℝ)⁻¹ := sub_le_self _ (by positivity)
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq T
        (fun k => ‖fourierCoeff j k‖) (fun k => (k : ℝ)⁻¹)
      have hbase :
          (∑ k ∈ T, ‖fourierCoeff j k‖ / k) ^ 2 ≤ 1 / (2 * K : ℝ) := by
        calc
          _ = (∑ k ∈ T, ‖fourierCoeff j k‖ * (k : ℝ)⁻¹) ^ 2 := by
            rfl
          _ ≤ (∑ k ∈ T, ‖fourierCoeff j k‖ ^ 2) *
              ∑ k ∈ T, ((k : ℝ)⁻¹) ^ 2 := hcs
          _ ≤ (1 / 2 : ℝ) * (K : ℝ)⁻¹ := by
            exact mul_le_mul henergy hrecip (by positivity) (by positivity)
          _ = 1 / (2 * K : ℝ) := by
            have hKR : (K : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hK)
            field_simp
      have hbase0 : 0 ≤ ∑ k ∈ T, ‖fourierCoeff j k‖ / k := by positivity
      have hsqrt : 2 * (∑ k ∈ T, ‖fourierCoeff j k‖ / k) ≤
          Real.sqrt (2 / K) := by
        apply (Real.le_sqrt (by positivity) (by positivity)).2
        have hKR : (0 : ℝ) < K := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hK)
        calc
          (2 * ∑ k ∈ T, ‖fourierCoeff j k‖ / k) ^ 2 ≤
              4 * (1 / (2 * K : ℝ)) := by nlinarith
          _ = 2 / K := by field_simp; ring
      calc
        _ = 2 * ∑ k ∈ T, ‖fourierCoeff j k‖ / k := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          simp only [F]
          ring
        _ ≤ _ := hsqrt
    · have hTempty : T = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro k hk
        simp only [T, O, Finset.mem_filter, Finset.mem_Icc] at hk
        omega
      rw [hTempty]
      simp
      positivity
  calc
    |(bias j : ℝ)| / 2 ^ j ≤ ∑ k ∈ Finset.Icc 1 N, F k := by
      simpa only [F, N] using hweighted
    _ = (∑ k ∈ T, F k) + ∑ k ∈ O.filter (fun k => ¬K < k), F k := by
      rw [hoddSum, Finset.sum_filter_add_sum_filter_not O (fun k => K < k) F]
    _ ≤ Real.sqrt (2 / K) +
        ∑ k ∈ (Finset.range (K + 1)).filter Odd, F k := add_le_add htail hlow
    _ = (∑ k ∈ (Finset.range (K + 1)).filter Odd,
        2 * ‖fourierCoeff j k‖ / k) + Real.sqrt (2 / K) := by
      simp only [F]
      ring

/-- **Node: decay of every fixed odd frequency.**  For each fixed odd `ξ`, the Fourier coefficient
`G_j(ξ)` of the beyond-Terras sign tends to `0` as `j → ∞`.

Evidence with control (`experiments/conjugacy/lowfreq.py`, `j ≤ 24`): off the powers of `3`,
`‖G_j(ξ)‖ · 2^{j/2}` stays in `[0.04, 2.8]` for `ξ = 1, 3, 5, 7, 15`, i.e. square-root
cancellation.  On the chain `ξ = 3^k` the normalised value rises and then falls (`ξ = 27` peaks
at `7.8` at `j = 13`, `ξ = 81` at `16.9` at `j = 22`), still decaying for each fixed `ξ`.  The
probe's control is §10.6's weighted sum `W_j`, reproduced to three figures at
`j = 8, 10, …, 22` by `wbranch.py` from the same coefficients.  Implies `BiasDecays`
(`biasDecays_of_lowFreqDecay`).  Confidence 85%. -/
def LowFreqDecay : Prop :=
  ∀ ξ : ℕ, Odd ξ → Tendsto (fun j => ‖fourierCoeff j ξ‖) atTop (𝓝 0)

/-- **Edge: pointwise decay of the fixed frequencies implies `BiasDecays`.**  Given `ε > 0`,
choose `K` with `√(2/K) < ε/2`; the finitely many odd `ξ ≤ K` have `2 ‖G_j(ξ)‖ / ξ → 0`, so
their sum is eventually below `ε/2`; conclude by `bias_div_le_lowFreq_add_tail`.  Confidence
99% given the reduction. -/
theorem biasDecays_of_lowFreqDecay (h : LowFreqDecay) : BiasDecays := by
  sorry

private theorem affineThreeMod_left (n u s : ℕ) (hn : 2 ≤ n)
    (hu : 3 * u % n = 1) (hs : s < n) :
    (u * ((3 * s + 2) % n + n - 2)) % n = s := by
  have hu' : 3 * u ≡ 1 [MOD n] := by
    show (3 * u) % n = 1 % n
    rw [hu, Nat.mod_eq_of_lt (by omega)]
  have hf : 3 * s + 2 ≡ (3 * s + 2) % n [MOD n] := (Nat.mod_modEq _ _).symm
  have hfn : (3 * s + 2) % n ≡ (3 * s + 2) % n + n [MOD n] := by
    simp [Nat.ModEq]
  have hsum : 3 * s + 2 ≡ ((3 * s + 2) % n + n - 2) + 2 [MOD n] := by
    have heq : (3 * s + 2) % n + n = ((3 * s + 2) % n + n - 2) + 2 := by
      omega
    rw [← heq]
    exact hf.trans hfn
  have hbase : 3 * s ≡ (3 * s + 2) % n + n - 2 [MOD n] :=
    Nat.ModEq.add_right_cancel (Nat.ModEq.refl 2) hsum
  have huv : u * (3 * s) ≡ s [MOD n] := by
    calc
      u * (3 * s) = (3 * u) * s := by ring
      _ ≡ 1 * s [MOD n] := hu'.mul (Nat.ModEq.refl s)
      _ = s := by simp
  have hmod : u * ((3 * s + 2) % n + n - 2) ≡ s [MOD n] :=
    (hbase.mul_left u).symm.trans huv
  show (u * ((3 * s + 2) % n + n - 2)) % n = s
  change (u * ((3 * s + 2) % n + n - 2)) % n = s % n at hmod
  simpa [Nat.mod_eq_of_lt hs] using hmod

private theorem affineThreeMod_right (n u t : ℕ) (hn : 2 ≤ n)
    (hu : 3 * u % n = 1) (ht : t < n) :
    (3 * ((u * (t + n - 2)) % n) + 2) % n = t := by
  have hu' : 3 * u ≡ 1 [MOD n] := by
    show (3 * u) % n = 1 % n
    rw [hu, Nat.mod_eq_of_lt (by omega)]
  have hg : (u * (t + n - 2)) % n ≡ u * (t + n - 2) [MOD n] := Nat.mod_modEq _ _
  have hmul : 3 * ((u * (t + n - 2)) % n) ≡ t + n - 2 [MOD n] := by
    calc
      3 * ((u * (t + n - 2)) % n) ≡ 3 * (u * (t + n - 2)) [MOD n] :=
        hg.mul_left 3
      _ = (3 * u) * (t + n - 2) := by ring
      _ ≡ 1 * (t + n - 2) [MOD n] := hu'.mul (Nat.ModEq.refl _)
      _ = t + n - 2 := by simp
  have hadd := hmul.add_right 2
  have heq : t + n - 2 + 2 = t + n := by omega
  rw [heq] at hadd
  have htn : t + n ≡ t [MOD n] := by
    simp [Nat.ModEq]
  have hmod := hadd.trans htn
  show (3 * ((u * (t + n - 2)) % n) + 2) % n = t
  change (3 * ((u * (t + n - 2)) % n) + 2) % n = t % n at hmod
  simpa [Nat.mod_eq_of_lt ht] using hmod

/-- If `3u = 1 (mod n)`, the affine map `s ↦ 3s+2` permutes the residues modulo `n`. -/
theorem sum_affineThreeMod {M : Type*} [AddCommMonoid M]
    (F : ℕ → M) (n u : ℕ) (hn : 2 ≤ n) (hu : 3 * u % n = 1) :
    ∑ s ∈ Finset.range n, F ((3 * s + 2) % n) = ∑ t ∈ Finset.range n, F t := by
  apply Finset.sum_nbij' (fun s => (3 * s + 2) % n) (fun t => (u * (t + n - 2)) % n)
  · intro s hs
    simp only [Finset.mem_range] at hs ⊢
    exact Nat.mod_lt _ (by omega)
  · intro t ht
    simp only [Finset.mem_range] at ht ⊢
    exact Nat.mod_lt _ (by omega)
  · intro s hs
    simp only [Finset.mem_range] at hs
    exact affineThreeMod_left n u s hn hu hs
  · intro t ht
    simp only [Finset.mem_range] at ht
    exact affineThreeMod_right n u t hn hu ht
  · intro s hs
    rfl

private theorem fourierChar_arg_add_period (n ξ r k : ℕ) (hn : 0 < n) :
    Complex.exp (2 * Real.pi * Complex.I * ξ * (r + n * k) / n) =
      Complex.exp (2 * Real.pi * Complex.I * ξ * r / n) := by
  rw [show
      2 * Real.pi * Complex.I * (ξ : ℂ) * ((r : ℂ) + (n : ℂ) * (k : ℂ)) / (n : ℂ) =
        2 * Real.pi * Complex.I * (ξ : ℂ) * (r : ℂ) / (n : ℂ) +
          ((ξ * k : ℕ) : ℂ) * (2 * Real.pi * Complex.I) by
    push_cast
    field_simp [show (n : ℂ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hn)]]
  rw [Complex.exp_add, Complex.exp_periodic.nat_mul_eq]
  simp

private theorem fourierChar_arg_congr_mod (n ξ r s : ℕ) (hn : 0 < n)
    (h : r % n = s % n) :
    Complex.exp (2 * Real.pi * Complex.I * ξ * r / n) =
      Complex.exp (2 * Real.pi * Complex.I * ξ * s / n) := by
  conv_lhs => rw [← Nat.mod_add_div r n]
  conv_rhs => rw [← Nat.mod_add_div s n]
  push_cast
  rw [fourierChar_arg_add_period _ _ _ _ hn, fourierChar_arg_add_period _ _ _ _ hn, h]

private theorem fourierOddPhase (n ξ u s : ℕ) (hn : 0 < n) (hu : 3 * u % n = 1) :
    Complex.exp (2 * Real.pi * Complex.I * ξ * (2 * s + 1) / (2 * n)) =
      Complex.exp (2 * Real.pi * Complex.I * ξ * (1 - 4 * (u : ℂ)) / (2 * n)) *
        Complex.exp (2 * Real.pi * Complex.I * (u * ξ) * (3 * s + 2) / n) := by
  have hq : 3 * u = 1 + n * (3 * u / n) := by
    conv_lhs => rw [← Nat.mod_add_div (3 * u) n]
    rw [hu]
  have hqC : (3 : ℂ) * (u : ℂ) = 1 + (n : ℂ) * (3 * u / n : ℕ) := by
    exact_mod_cast hq
  rw [← Complex.exp_add]
  rw [show
      2 * Real.pi * Complex.I * (ξ : ℂ) * (1 - 4 * (u : ℂ)) / (2 * (n : ℂ)) +
          2 * Real.pi * Complex.I * ((u : ℂ) * (ξ : ℂ)) * (3 * (s : ℂ) + 2) / (n : ℂ) =
        2 * Real.pi * Complex.I * (ξ : ℂ) * (2 * (s : ℂ) + 1) / (2 * (n : ℂ)) +
          ((ξ * s * (3 * u / n) : ℕ) : ℂ) * (2 * Real.pi * Complex.I) by
    push_cast
    field_simp [show (n : ℂ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hn)]
    linear_combination (2 * (ξ : ℂ) * (s : ℂ)) * hqC]
  rw [Complex.exp_add, Complex.exp_periodic.nat_mul_eq]
  simp

private theorem sum_range_even_odd {M : Type*} [AddCommMonoid M] (g : ℕ → M) (n : ℕ) :
    ∑ r ∈ Finset.range (2 * n), g r = ∑ s ∈ Finset.range n, (g (2 * s) + g (2 * s + 1)) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ,
      add_assoc]

private theorem beyondSign_succ_even (j s : ℕ) :
    beyondSign (j + 1) (2 * s) = beyondSign j s := by
  unfold beyondSign
  rw [Function.iterate_succ_apply]
  have ht : tstep (2 * s) = s := by
    unfold tstep
    split_ifs <;> omega
  rw [ht]

private theorem beyondSign_succ_odd (j s : ℕ) :
    beyondSign (j + 1) (2 * s + 1) = beyondSign j (3 * s + 2) := by
  unfold beyondSign
  rw [Function.iterate_succ_apply]
  have ht : tstep (2 * s + 1) = 3 * s + 2 := by
    unfold tstep
    split_ifs <;> omega
  rw [ht]

/-- **The mirror recursion.**  With `3u ≡ 1 (mod 2^(j+1))`,
`G_{j+1}(ξ) = ½ G_j(ξ) + ½ e(ξ (1 − 4u) / 2^(j+2)) G_j(u ξ)`.

Proof.  Split `r < 2^(j+2)` by parity.  `tstep (2s) = s`, so the even half is
`½ G_j(ξ)` (with `e(ξ · 2s / 2^(j+2)) = e(ξ s / 2^(j+1))`).  `tstep (2s+1) = 3s + 2`; put
`t = 3s + 2 mod 2^(j+1)`, so `s ≡ u(t − 2)` and `2s + 1 ≡ 2ut − 4u + 1 (mod 2^(j+2))`, and the
odd half is `½ e(ξ(1 − 4u)/2^(j+2)) G_j(uξ)`.  Uses that `beyondSign j` depends only on
`r mod 2^(j+1)` (`accWord_congr_mod`, Ladder.lean) and that `fourierCoeff j` is periodic in `ξ`
mod `2^(j+1)`.

Evidence with control (`experiments/conjugacy/recurcheck.py`, `j ≤ 17`, every `ξ < 2^(j+2)`):
maximum error `1.8e-11`; with the phase deleted the error is `0.65`.  Confidence 97%. -/
theorem fourierCoeff_succ (j ξ u : ℕ) (hu : 3 * u % 2 ^ (j + 1) = 1) :
    fourierCoeff (j + 1) ξ =
      (1 / 2 : ℂ) * fourierCoeff j ξ +
        (1 / 2 : ℂ) *
            Complex.exp (2 * Real.pi * Complex.I * ξ * (1 - 4 * (u : ℂ)) / 2 ^ (j + 2)) *
          fourierCoeff j (u * ξ) := by
  let n := 2 ^ (j + 1)
  have hn : 0 < n := by simp [n]
  have hn2 : 2 ≤ n := by
    have hp : 0 < 2 ^ j := Nat.pow_pos (n := j) (by omega)
    simp only [n, pow_succ]
    omega
  let A : ℂ := Complex.exp
    (2 * Real.pi * Complex.I * ξ * (1 - 4 * (u : ℂ)) / (2 * n))
  let F : ℕ → ℂ := fun t =>
    (beyondSign j t : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (u * ξ) * t / n)
  have hFmod (r : ℕ) : F (r % n) = F r := by
    unfold F
    congr 1
    · exact_mod_cast beyondSign_congr_mod j (by simp [n])
    · simpa only [Nat.cast_mul] using
        fourierChar_arg_congr_mod n (u * ξ) (r % n) r hn (Nat.mod_mod r n)
  have hodd :
      ∑ s ∈ Finset.range n,
          (beyondSign (j + 1) (2 * s + 1) : ℂ) *
            Complex.exp (2 * Real.pi * Complex.I * ξ * (2 * s + 1) / (2 * n)) =
        A * ∑ t ∈ Finset.range n, F t := by
    rw [Finset.mul_sum]
    calc
      _ = ∑ s ∈ Finset.range n, A * F (3 * s + 2) := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [beyondSign_succ_odd, fourierOddPhase n ξ u s hn hu]
        simp only [A, F]
        push_cast
        ring
      _ = ∑ s ∈ Finset.range n, A * F ((3 * s + 2) % n) := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [hFmod]
      _ = _ := by
        simpa only [Finset.mul_sum] using
          congrArg (A * ·) (sum_affineThreeMod F n u hn2 hu)
  have heven :
      ∑ s ∈ Finset.range n,
          (beyondSign (j + 1) (2 * s) : ℂ) *
            Complex.exp (2 * Real.pi * Complex.I * ξ * (2 * s) / (2 * n)) =
        ∑ s ∈ Finset.range n,
          (beyondSign j s : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ξ * s / n) := by
    apply Finset.sum_congr rfl
    intro s hs
    rw [beyondSign_succ_even]
    congr 1
    congr 1
    field_simp [show (n : ℂ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hn)]
  unfold fourierCoeff
  have hpowN : 2 ^ (j + 2) = 2 * n := by simp [n, pow_succ, mul_comm]
  have hbaseN : 2 ^ (j + 1) = n := rfl
  have hnC : (2 : ℂ) ^ (j + 1) = (n : ℂ) := by simp [n]
  have hpowC : (2 : ℂ) ^ (j + 2) = 2 * (n : ℂ) := by
    rw [pow_succ, hnC]
    ring
  change
    ((2 : ℂ) ^ (j + 2))⁻¹ *
        ∑ r ∈ Finset.range (2 ^ (j + 2)),
          (beyondSign (j + 1) r : ℂ) *
            Complex.exp (2 * Real.pi * Complex.I * ξ * r / 2 ^ (j + 2)) = _
  rw [hpowN, hpowC, hnC, hbaseN]
  rw [sum_range_even_odd, Finset.sum_add_distrib]
  push_cast
  rw [heven, hodd]
  simp only [A, F, n]
  simp only [mul_inv_rev]
  ring

/-- **Node: decay at every fixed odd 2-adic frequency.**  For each `2`-adic unit `η`, the
coefficient at its truncation `η mod 2^(j+1)` tends to `0`.  Unrolling the first branch of
`fourierCoeff_succ` gives `‖G_j(ξ)‖ ≤ Σ_m 2^{−m} ‖G_{j−m}(ξ/3 mod 2^{j−m+1})‖ + 2^{−j}`, so decay at
an integer frequency is fed by decay at the 2-adic frequency `ξ/3` (the "third points", where
`ξ/3 mod 2^(j+1)` sits near `2^(j+1)/3` or `2^(j+2)/3`).  This family is closed under `η ↦ η/3`
and contains the integer frequencies (`lowFreqDecay_of_twoAdicFreqDecay`).

Evidence with control (`experiments/conjugacy/twoadicfreq.py`, `j ≤ 24`): for
`η = 1/3, −1/3, 1/9, 5/7, 1/27` and a random 64-bit unit, `‖G_j(η)‖ · 2^{j/2}` stays in
`[0.14, 1.6]`; the pair `±1/3` agrees to every digit, as conjugate symmetry requires.
Confidence 80%. -/
def TwoAdicFreqDecay : Prop :=
  ∀ η : ℤ_[2], IsUnit η →
    Tendsto (fun j => ‖fourierCoeff j (PadicInt.appr η (j + 1))‖) atTop (𝓝 0)

/-- The canonical natural approximant to an embedded natural is its remainder modulo `2^n`. -/
theorem padicInt_appr_natCast (ξ n : ℕ) :
    PadicInt.appr (ξ : ℤ_[2]) n = ξ % 2 ^ n := by
  have hz :
      ((PadicInt.appr (ξ : ℤ_[2]) n : ℕ) : ZMod (2 ^ n)) =
        (ξ : ZMod (2 ^ n)) := by
    change PadicInt.toZModPow n (ξ : ℤ_[2]) = (ξ : ZMod (2 ^ n))
    simp
  have hm := (ZMod.natCast_eq_natCast_iff _ _ _).mp hz
  rw [Nat.ModEq, Nat.mod_eq_of_lt (PadicInt.appr_lt _ _)] at hm
  exact hm

/-- **Edge: the 2-adic node contains the integer one.**  For odd `ξ : ℕ`, `(ξ : ℤ_[2])` is a unit
and its approximant mod `2^(j+1)` is `ξ mod 2^(j+1)`; `fourierCoeff j` is periodic in the
frequency mod `2^(j+1)`.  Confidence 99%. -/
theorem lowFreqDecay_of_twoAdicFreqDecay (h : TwoAdicFreqDecay) : LowFreqDecay := by
  intro ξ hξ
  have hunit : IsUnit (ξ : ℤ_[2]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff,
      Nat.prime_two.coprime_iff_not_dvd]
    intro hdvd
    rw [Nat.dvd_iff_mod_eq_zero] at hdvd
    rw [Nat.odd_iff] at hξ
    omega
  apply (h (ξ : ℤ_[2]) hunit).congr'
  filter_upwards [] with j
  congr 1
  rw [padicInt_appr_natCast]
  symm
  conv_lhs => rw [← Nat.mod_add_div ξ (2 ^ (j + 1))]
  exact fourierCoeff_add_period j _ _

end CollatzMoonshot.Conjugacy
