/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.Fourier

/-!
# The Fourier coefficient at one frequency is a lattice sum

The mirror recursion `fourierCoeff_succ` sends a frequency `f` only to `f` and `f/3`.  So the
coefficient `G_j(ξ)` at one odd frequency involves only the frequencies `ξ · 3^{−m}`, `m ≤ j`,
at each level: a lattice of size `~ j²`, not the `2^{j+1}`-term sum.  Since
`1 − 4u ≡ −3⁻¹`, the phase on the step from level `n + 1` to `n` at orbit position `m` is
`e(−⟨ξ · 3^{−(m+1)}⟩_{n+2})`, where `⟨x⟩_k = (x mod 2^k)/2^k` reads the top bits of the
`k`-bit truncation of the `2`-adic number `x`.  Unrolled: `G_j(ξ)` is the expectation, over a
uniform random subset `S = {s₁ > s₂ > ⋯}` of `{0, …, j−1}`, of `e(−Σ_t ⟨ξ · 3^{−t}⟩_{s_t + 2})`,
a multiplicative functional of a simple random walk in the space-time environment of the
`2`-adic digits of `ξ · 3^{−t}`.  So `LowFreqDecay` is a weighted equidistribution statement
about binary digits of powers of `3`.

Evidence with control (`experiments/conjugacy/latticedp.py`): the lattice recursion reproduces
the FFT coefficients at every `j ≤ 18` for ten frequencies each, maximum error `2.6e-16`;
**teeth**: with the phase deleted the error is `1.23`.  The recursion makes the coefficients
cheap: `latticerun.py` measures them to `j = 4000`.
-/

namespace CollatzMoonshot.Conjugacy

/-- Fourier coefficients at level `j` depend only on the frequency modulo `2^(j+1)`. -/
private theorem fourierCoeff_congr_mod (j a b : ℕ)
    (h : a % 2 ^ (j + 1) = b % 2 ^ (j + 1)) :
    fourierCoeff j a = fourierCoeff j b := by
  conv_lhs => rw [← Nat.mod_add_div a (2 ^ (j + 1))]
  conv_rhs => rw [← Nat.mod_add_div b (2 ^ (j + 1))]
  rw [fourierCoeff_add_period, fourierCoeff_add_period, h]

/-- Reduction from `2^(n+2)` to `2^(n+1)` preserves the inverse of three. -/
private theorem cast_inv_three (n : ℕ) :
    (ZMod.castHom (pow_dvd_pow 2 (by omega : n + 1 ≤ n + 2))
      (ZMod (2 ^ (n + 1)))) ((3 : ZMod (2 ^ (n + 2)))⁻¹) =
        (3 : ZMod (2 ^ (n + 1)))⁻¹ := by
  let f := ZMod.castHom (pow_dvd_pow 2 (by omega : n + 1 ≤ n + 2))
    (ZMod (2 ^ (n + 1)))
  have hcop : Nat.Coprime 3 (2 ^ (n + 2)) :=
    Nat.Coprime.pow_right (n + 2) (by decide)
  have hunit : IsUnit (3 : ZMod (2 ^ (n + 2))) :=
    (ZMod.isUnit_iff_coprime 3 (2 ^ (n + 2))).2 hcop
  have hinv := ZMod.mul_inv_of_unit (3 : ZMod (2 ^ (n + 2))) hunit
  have hmap := congrArg f hinv
  have hmul : (3 : ZMod (2 ^ (n + 1))) *
      f ((3 : ZMod (2 ^ (n + 2)))⁻¹) = 1 := by
    simpa only [map_mul, map_ofNat, map_one] using hmap
  exact (ZMod.inv_eq_of_mul_eq_one _ _ _ hmul).symm

/-- Exponentials with integer numerators agree when those numerators are congruent modulo the
denominator. -/
private theorem exp_int_congr (N : ℕ) (hN : 0 < N) (a b : ℤ)
    (h : a ≡ b [ZMOD (N : ℤ)]) :
    Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / N) =
      Complex.exp (2 * Real.pi * Complex.I * (b : ℂ) / N) := by
  rw [Int.modEq_iff_dvd] at h
  obtain ⟨k, hk⟩ := h
  have hb : b = a + N * k := by omega
  rw [hb]
  rw [show
      2 * Real.pi * Complex.I * ((a + (N : ℤ) * k : ℤ) : ℂ) / (N : ℂ) =
        2 * Real.pi * Complex.I * (a : ℂ) / N +
          (k : ℂ) * (2 * Real.pi * Complex.I) by
    push_cast
    field_simp [show (N : ℂ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hN)]]
  rw [Complex.exp_add, Complex.exp_periodic.int_mul_eq]
  simp

/-- The phase on the lattice step from level `n + 1` to level `n` at orbit position `m`:
`e(−⟨ξ · 3^{−(m+1)}⟩_{n+2})`. -/
noncomputable def latticePhase (ξ n m : ℕ) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I *
    ((((3 : ZMod (2 ^ (n + 2)))⁻¹ ^ (m + 1) * ξ).val : ℕ) : ℂ) / 2 ^ (n + 2)))

/-- The lattice values: `latticeCoeff ξ n m = G_n(ξ · 3^{−m})` (`fourierCoeff_eq_latticeCoeff`). -/
noncomputable def latticeCoeff (ξ : ℕ) : ℕ → ℕ → ℂ
  | 0, _ => 1
  | n + 1, m => (1 / 2 : ℂ) * latticeCoeff ξ n m +
      (1 / 2 : ℂ) * latticePhase ξ n m * latticeCoeff ξ n (m + 1)

/-- **The lattice formula.**  For odd `ξ`, the coefficient at the frequency `ξ · 3^{−m}` (read
mod `2^(n+1)`) is the lattice value.

Proof sketch.  Induction on `n`.  At `n = 0`, `G_0 = 1` at every odd frequency, and
`ξ · 3^{−m}` is odd.  The step is `fourierCoeff_succ` with `u = 3⁻¹`, using
`u · (ξ 3^{−m}) = ξ 3^{−(m+1)}`, `ξ 3^{−m} (1 − 4u) ≡ −ξ 3^{−(m+1)} (mod 2^(n+2))` (because
`3 (1 − 4u) ≡ −1`), `1`-periodicity of `e`, and periodicity of `fourierCoeff n` in the
frequency mod `2^(n+1)`.  Confidence 97% (the numerics above match it to `2.6e-16`). -/
theorem fourierCoeff_eq_latticeCoeff (ξ n m : ℕ) (hξ : Odd ξ) :
    fourierCoeff n (((3 : ZMod (2 ^ (n + 1)))⁻¹ ^ m * ξ).val) = latticeCoeff ξ n m := by
  induction n generalizing m with
  | zero =>
      have hxmod : ξ % 2 = 1 := Nat.odd_iff.mp hξ
      have hx : (ξ : ZMod 2) = 1 := by
        rw [← ZMod.natCast_mod ξ 2, hxmod]
        norm_num
      have h3 : (3 : ZMod 2) = 1 := by decide
      have hfreq : (((3 : ZMod (2 ^ (0 + 1)))⁻¹ ^ m * ξ).val) = 1 := by
        change (((3 : ZMod 2)⁻¹ ^ m * ξ).val) = 1
        rw [h3, inv_one, one_pow, one_mul, hx]
        rfl
      rw [hfreq]
      simp only [latticeCoeff]
      simp [fourierCoeff, beyondSign, Finset.sum_range_succ]
      rw [show (2 : ℂ) * Real.pi * Complex.I / 2 = Real.pi * Complex.I by ring,
        Complex.exp_pi_mul_I]
      norm_num
  | succ n ih =>
      let N : ℕ := 2 ^ (n + 2)
      let M : ℕ := 2 ^ (n + 1)
      let a : ZMod N := (3 : ZMod N)⁻¹
      let x : ZMod N := a ^ m * ξ
      let u : ℕ := a.val
      let f : ℕ := x.val
      let t : ℕ := (a ^ (m + 1) * ξ).val
      have hN : 0 < N := by simp [N]
      have hM : 0 < M := by simp [M]
      have hMdivN : M ∣ N := pow_dvd_pow 2 (by omega)
      let c := ZMod.castHom hMdivN (ZMod M)
      have hcop : Nat.Coprime 3 N := by
        dsimp only [N]
        exact Nat.Coprime.pow_right (n + 2) (by decide)
      have hunit : IsUnit (3 : ZMod N) :=
        (ZMod.isUnit_iff_coprime 3 N).2 hcop
      have h3a : (3 : ZMod N) * a = 1 := ZMod.mul_inv_of_unit _ hunit
      have hN3 : 3 < N := by
        have hp : 0 < 2 ^ n := by positivity
        dsimp only [N]
        rw [show n + 2 = 2 + n by omega, pow_add]
        norm_num
        omega
      have huN : (u : ZMod N) = a := ZMod.natCast_zmod_val a
      have hfN : (f : ZMod N) = x := ZMod.natCast_zmod_val x
      have htN : (t : ZMod N) = a ^ (m + 1) * ξ := ZMod.natCast_zmod_val _
      have huFull : 3 * u % N = 1 := by
        letI : Fact (1 < N) := ⟨by omega⟩
        have hv := congrArg ZMod.val h3a
        have hval3 : ZMod.val (3 : ZMod N) = 3 := ZMod.val_natCast_of_lt hN3
        have hval1 : ZMod.val (1 : ZMod N) = 1 := ZMod.val_one N
        rw [ZMod.val_mul, hval3, hval1] at hv
        simpa only [u] using hv
      have hu : 3 * u % 2 ^ (n + 1) = 1 := by
        change 3 * u % M = 1
        rw [← Nat.mod_mod_of_dvd (3 * u) hMdivN, huFull]
        exact Nat.mod_eq_of_lt (by omega)
      have haSmall : c a = (3 : ZMod M)⁻¹ := by
        simpa only [c, a, N, M] using cast_inv_three n
      have huSmall : (u : ZMod M) = (3 : ZMod M)⁻¹ := by
        calc
          (u : ZMod M) = c (u : ZMod N) := by simp [c]
          _ = c a := by rw [huN]
          _ = _ := haSmall
      have hxSmall : (f : ZMod M) = (3 : ZMod M)⁻¹ ^ m * ξ := by
        calc
          (f : ZMod M) = c (f : ZMod N) := by simp [c]
          _ = c x := by rw [hfN]
          _ = _ := by simp [x, haSmall]
      have hfirstMod : f % M =
          (((3 : ZMod M)⁻¹ ^ m * ξ).val) % M := by
        apply (ZMod.natCast_eq_natCast_iff f _ M).mp
        rw [hxSmall, ZMod.natCast_zmod_val]
      have hsecondSmall : ((u * f : ℕ) : ZMod M) =
          (3 : ZMod M)⁻¹ ^ (m + 1) * ξ := by
        push_cast
        rw [huSmall, hxSmall, pow_succ]
        ring
      have hsecondMod : (u * f) % M =
          (((3 : ZMod M)⁻¹ ^ (m + 1) * ξ).val) % M := by
        apply (ZMod.natCast_eq_natCast_iff (u * f) _ M).mp
        rw [hsecondSmall, ZMod.natCast_zmod_val]
      have hphaseZ :
          (((f : ℤ) * (1 - 4 * (u : ℤ)) : ℤ) : ZMod N) =
            ((-(t : ℤ) : ℤ) : ZMod N) := by
        push_cast
        rw [hfN, huN, htN, show (1 : ZMod N) = 3 * a by exact h3a.symm]
        rw [pow_succ]
        ring
      have hphaseMod : (f : ℤ) * (1 - 4 * (u : ℤ)) ≡ -(t : ℤ) [ZMOD (N : ℤ)] :=
        (ZMod.intCast_eq_intCast_iff _ _ N).mp hphaseZ
      have hphaseExp := exp_int_congr N hN ((f : ℤ) * (1 - 4 * (u : ℤ)))
        (-(t : ℤ)) hphaseMod
      have hphase :
          Complex.exp (2 * Real.pi * Complex.I * f * (1 - 4 * (u : ℂ)) / N) =
            latticePhase ξ n m := by
        unfold latticePhase
        have htdef : (((3 : ZMod (2 ^ (n + 2)))⁻¹ ^ (m + 1) * ξ).val) = t := by
          rfl
        rw [htdef]
        rw [← show (N : ℂ) = (2 : ℂ) ^ (n + 2) by norm_cast]
        change Complex.exp (2 * Real.pi * Complex.I * (f : ℂ) *
            (1 - 4 * (u : ℂ)) / N) =
          Complex.exp (-(2 * Real.pi * Complex.I * (t : ℂ) / N))
        convert hphaseExp using 1 <;> push_cast <;> ring
      change fourierCoeff (n + 1) f = latticeCoeff ξ (n + 1) m
      rw [fourierCoeff_succ n f u hu]
      simp only [latticeCoeff]
      rw [fourierCoeff_congr_mod n f
          (((3 : ZMod M)⁻¹ ^ m * ξ).val) hfirstMod,
        ih m]
      rw [fourierCoeff_congr_mod n (u * f)
          (((3 : ZMod M)⁻¹ ^ (m + 1) * ξ).val) hsecondMod,
        ih (m + 1)]
      have hphase' : Complex.exp (2 * Real.pi * Complex.I * f * (1 - 4 * (u : ℂ)) /
          2 ^ (n + 2)) = latticePhase ξ n m := by
        convert hphase using 1 <;> norm_cast
      rw [hphase']

/-- **Corollary at `m = 0`.**  `G_j(ξ) = latticeCoeff ξ j 0` for odd `ξ`. -/
theorem fourierCoeff_eq_latticeCoeff_zero (ξ j : ℕ) (hξ : Odd ξ) :
    fourierCoeff j ξ = latticeCoeff ξ j 0 := by
  calc
    fourierCoeff j ξ = fourierCoeff j ((ξ : ZMod (2 ^ (j + 1))).val) := by
      apply fourierCoeff_congr_mod
      simp [ZMod.val_natCast]
    _ = latticeCoeff ξ j 0 := by
      simpa using fourierCoeff_eq_latticeCoeff ξ j 0 hξ

end CollatzMoonshot.Conjugacy
