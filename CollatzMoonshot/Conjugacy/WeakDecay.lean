/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Conjugacy.C1
import CollatzMoonshot.Conjugacy.WeakDecayAux
import CollatzMoonshot.Conjugacy.WeakDecayTwist
import CollatzMoonshot.Conjugacy.WeakDecayTwistBound
import CollatzMoonshot.Conjugacy.WeakDecaySec7P

/-!
# C1⁺: decay at every 3-adic scale (`WeakDecayOnZ3`), via over-precision slice sums

`WeakDecayOnZ3` (`Recursion.lean`) asks that every residue class of the *start* mod `3^k` carry
`o(2^m)` of the signed mass `Σ_{y < 2^m} (−1)^{T^m y}`.  Its `k = 0` case is C1 (`biasDecays`).

**The reduction (exact).**  Expand the class indicator in characters `e(η r / 3^k)` of `ℤ/3^k`.
`η = 0` is `bias / 3^k`, handled by C1.  For `η ≠ 0` split the starts into slices
`levelSet j a`.  On a slice, the iterate identity gives `3^a r = 2^j y − N_r` with
`y = T^j r < 3^a` and `N_r = 2^j T^j r − 3^a r`, so `e(η r / 3^k) = e(η (2^j y − N_r) / 3^{a+k})`
exactly.  Expand `g_η(y) = (−1)^y e(η 2^j y / 3^{a+k})` on `[0, 3^a)` in characters of `ℤ/3^a`.
Comparison with the ordinary parity coefficients at the fine modulus gives
`Σ_ξ |ĝ_η(ξ)| ≤ 3^k · 4(a+k+1)`, hence `O_k(a)`.  Since `y ≡ 2^{−j} N_r`
(mod `3^a`), each frequency becomes `e(ζ N_r / 3^{a+k})` with `ζ = 3^k ξ 2^{−j} − η`.  Its
3-adic valuation is `v₃(η) < k` whatever `ξ` is.  So every term is an **over-precision** slice
sum `overPrecChar j a k' ζ'` with `k' = k − v₃(η) ≥ 1` and `3 ∤ ζ'`, on the *same* slice.  No
sub-slices appear.  Checked exactly against brute-force Collatz starts
(`experiments/conjugacy/c1plus_twistcheck.py`, six `(j, a, k, η)`, error `< 1e−10`).

**Why the over-precision sums decay (Sec7P absorbs it).**  In Tao's ordering,
`N_r · 2^{−j} mod 3^{a+k}` is the Syracuse sum at level `n = a + k` with only its first `a`
terms.  The exact pairing argument therefore produces a partial `(7.5)` damping with `a/2`
pair coordinates but character arithmetic at level `n`.  Pad the missing pair sums by the fixed
value `2`: every added `fPair` has norm exactly one, while its Pascal weight is `p² ≥ 1/25` on
the central window.  Thus the partial damping is at most `25^d` times the established full
level-`n` damping, where `d = ⌊n/2⌋ − ⌊a/2⌋ ≤ k`.  This is a constant for fixed `k`.

**Measured** (`experiments/conjugacy/overprec_charfn.py`, an exact DP over odd times; control equals brute
force): `max_{ζ ∈ {1,2,5,7,11}} |overPrecChar| / #slice` at `a/j = 0.45` is
`6.9e−7, 5.8e−12, 1.3e−18, 1.2e−33` for `k = 0` and `1.2e−4, 2.2e−8, 9.6e−16, 1.1e−30` for
`k = 3`, at `j = 40, 80, 160, 320`.  The rate is the same, and the constant is worse by about
`10^k`.  The rays `a/j = 0.3, 0.55` behave the same way.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB

/-- The over-precision slice character sum: `Σ_{r ∈ levelSet j a} e(ξ · N_r / 3^{a+k})`, where
`N_r = 2^j T^j r − 3^a r` is the numerator of the parity word (`tstep_iterate_identity`;
the natural subtraction is exact).  At `k = 0` it is the slice character sum at frequency
`ξ 2^j`. -/
noncomputable def overPrecChar (j a k ξ : ℕ) : ℂ :=
  ∑ r ∈ levelSet j a,
    Complex.exp (2 * Real.pi * Complex.I *
      ((ξ * (2 ^ j * tstep^[j] r - 3 ^ a * r) : ℕ) : ℂ) / (3 ^ (a + k) : ℂ))

/-- **Node: over-precision slice character decay.**  For each fixed extra precision `k`, on
the window `1/5 ≤ a/j ≤ 3/5` and for `ξ` coprime to `3`, the normalized sum is `O_{k,A}(j^{−A})`.
Its `k = 0` case is `SliceCharDecay` (up to the unit `2^j`).  Confidence 85% true, 70% that
it follows from Sec7P as sketched in the module docstring. -/
def OverPrecSliceCharDecay : Prop :=
  ∀ k : ℕ, ∀ A > (0 : ℝ), ∃ C > (0 : ℝ), ∀ j a ξ : ℕ, 1 ≤ j → j ≤ 5 * a → 5 * a ≤ 3 * j →
    ¬ 3 ∣ ξ → ‖overPrecChar j a k ξ‖ ≤ C * (j : ℝ) ^ (-A) * (levelSet j a).card

/-- **Edge: over-precision decay gives C1⁺.**  The reduction in the module docstring: characters
of the start class mod `3^k`, the `η = 0` term by `biasDecays`, slices outside
`[1/4, 11/20]` by the binomial tails (`outOddSet`, `Bridge3Aux.lean`), and on each main slice
the `O(a)` Fourier weight of `g_η` times `OverPrecSliceCharDecay` at `A = 3`. -/
theorem weakDecayOnZ3_of_overPrecSliceCharDecay (h : OverPrecSliceCharDecay) :
    WeakDecayOnZ3 := by
  rw [WeakDecayOnZ3]
  intro k c
  by_cases hc : c < 3 ^ k
  · have hdecay := h
    rw [OverPrecSliceCharDecay] at hdecay
    have htwist : ∀ η : ZMod (3 ^ k), η ≠ 0 →
        Tendsto (fun m => ‖startTwist m k η‖ / (2 : ℝ) ^ m) atTop (𝓝 0) := by
      intro η hη
      let v := padicValNat 3 η.val
      obtain ⟨C, hCpos, hC⟩ := hdecay (k - v) 2 (by norm_num)
      let D : ℝ := 12 * (3 : ℝ) ^ k * C
      have hone : Tendsto (fun m : ℕ => (1 : ℝ) / m) atTop (𝓝 0) :=
        tendsto_one_div_atTop_nhds_zero_nat
      have hmajor : Tendsto
          (fun m : ℕ => D * ((1 : ℝ) / m) + 100 * ((1 : ℝ) / m))
          atTop (𝓝 0) := by
        simpa using (hone.const_mul D).add (hone.const_mul 100)
      apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) _ hmajor
      filter_upwards [eventually_ge_atTop (max 1 k)] with m hm
      have hm1 : 1 ≤ m := le_trans (le_max_left _ _) hm
      have hkm : k ≤ m := le_trans (le_max_right _ _) hm
      have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
      have hrpow2 : (m : ℝ) ^ (-(2 : ℝ)) = ((m : ℝ) ^ 2)⁻¹ := by
        rw [Real.rpow_neg hmpos.le, Real.rpow_two]
      have hslice : ∀ a, m ≤ 4 * a → a ≤ 11 * m / 20 →
          ‖sliceStartTwist m a k η‖ ≤ (D / m) * (levelSet m a).card := by
        intro a hma ham
        have ham' : a ≤ m := by omega
        have hj5a : m ≤ 5 * a := by omega
        have h5a3j : 5 * a ≤ 3 * m := by omega
        have hinner : ∀ ξ : ZMod (3 ^ a),
            ‖∑ r ∈ levelSet m a,
              Complex.exp ((2 * Real.pi * Complex.I *
                ((overPrecFrequencyUnit a k η ξ *
                    (2 ^ m * tstep^[m] r - 3 ^ a * r) : ℕ) : ℂ)) /
                  (3 ^ (a + (k - padicValNat 3 η.val)) : ℂ))‖ ≤
              C * (m : ℝ) ^ (-(2 : ℝ)) * (levelSet m a).card := by
          intro ξ
          have hfreq := overPrecFrequencyNat_normalize ξ hη
          have hb := hC m a (overPrecFrequencyUnit a k η ξ) hm1 hj5a h5a3j hfreq.2.2
          unfold overPrecChar at hb
          simpa [v] using hb
        have hs := norm_sliceStartTwist_le_of_normalized hη
          (show 0 ≤ C * (m : ℝ) ^ (-(2 : ℝ)) * (levelSet m a).card by positivity)
          hinner
        have hak : a + k + 1 ≤ 3 * m := by omega
        have hakR : (a : ℝ) + (k : ℝ) + 1 ≤ 3 * (m : ℝ) := by exact_mod_cast hak
        have hbase :
            (3 : ℝ) ^ k * (4 * (a + k + 1)) * C ≤ D * m := by
          dsimp [D]
          calc
            (3 : ℝ) ^ k * (4 * (a + k + 1)) * C ≤
                (3 : ℝ) ^ k * (4 * (3 * m)) * C := by
              gcongr
            _ = (12 * (3 : ℝ) ^ k * C) * m := by ring
        calc
          ‖sliceStartTwist m a k η‖ ≤
              ((3 : ℝ) ^ k * (4 * (a + k + 1))) *
                (C * (m : ℝ) ^ (-(2 : ℝ)) * (levelSet m a).card) := hs
          _ = (((3 : ℝ) ^ k * (4 * (a + k + 1)) * C) /
                (m : ℝ) ^ 2) * (levelSet m a).card := by
            rw [hrpow2]
            field_simp
          _ ≤ ((D * m) / (m : ℝ) ^ 2) * (levelSet m a).card := by
            gcongr
          _ = (D / m) * (levelSet m a).card := by
            field_simp
      have hstart := norm_startTwist_le_of_slice m k η
        (show 0 ≤ D / m by positivity) hslice
      have hpowpos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
      have hratio :
          ‖startTwist m k η‖ / (2 : ℝ) ^ m ≤
            D / m + ((outOddSet m).card : ℝ) / (2 : ℝ) ^ m := by
        apply (div_le_iff₀ hpowpos).2
        calc
          ‖startTwist m k η‖ ≤
              (D / m) * (2 : ℝ) ^ m + (outOddSet m).card := hstart
          _ = (D / m + ((outOddSet m).card : ℝ) / (2 : ℝ) ^ m) *
                (2 : ℝ) ^ m := by field_simp
      have htail := outOddSet_ratio_le m (by omega)
      calc
        ‖startTwist m k η‖ / (2 : ℝ) ^ m ≤
            D / m + ((outOddSet m).card : ℝ) / (2 : ℝ) ^ m := hratio
        _ ≤ D / m + 100 / (m : ℝ) := add_le_add (le_refl _) htail
        _ = D * ((1 : ℝ) / m) + 100 * ((1 : ℝ) / m) := by ring
    have hbiasR : Tendsto (fun m => (bias m : ℝ) / (2 : ℝ) ^ m) atTop (𝓝 0) := by
      simpa [BiasDecays] using biasDecays
    have hbiasC : Tendsto (fun m => (((bias m : ℝ) / (2 : ℝ) ^ m : ℝ) : ℂ))
        atTop (𝓝 0) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp hbiasR
    have hterm : ∀ η : ZMod (3 ^ k), Tendsto
        (fun m => (((3 ^ k : ℕ) : ℂ)⁻¹ *
          ZMod.stdAddChar (- (η * (c : ZMod (3 ^ k)))) * startTwist m k η) /
            (2 : ℂ) ^ m) atTop (𝓝 0) := by
      intro η
      by_cases hη : η = 0
      · subst η
        have ht := hbiasC.const_mul (((3 ^ k : ℕ) : ℂ)⁻¹)
        have ht0 : Tendsto
            (fun m => (((3 ^ k : ℕ) : ℂ)⁻¹ *
              (((bias m : ℝ) / (2 : ℝ) ^ m : ℝ) : ℂ)))
            atTop (𝓝 0) := by simpa using ht
        apply ht0.congr'
        filter_upwards with m
        rw [startTwist_zero]
        simp
        ring
      · have hnorm := htwist η hη
        have hcomplex : Tendsto
            (fun m => startTwist m k η / (2 : ℂ) ^ m)
            atTop (𝓝 0) := by
          rw [tendsto_zero_iff_norm_tendsto_zero]
          simpa [norm_div, norm_pow] using hnorm
        let q : ℂ := ((3 ^ k : ℕ) : ℂ)⁻¹ *
          ZMod.stdAddChar (- (η * (c : ZMod (3 ^ k))))
        have ht := hcomplex.const_mul q
        have ht0 : Tendsto (fun m => q * (startTwist m k η / (2 : ℂ) ^ m))
            atTop (𝓝 0) := by simpa using ht
        apply ht0.congr'
        filter_upwards with m
        dsimp [q]
        ring
    have hsum : Tendsto
        (fun m => ∑ η : ZMod (3 ^ k),
          ((((3 ^ k : ℕ) : ℂ)⁻¹ *
            ZMod.stdAddChar (- (η * (c : ZMod (3 ^ k)))) * startTwist m k η) /
              (2 : ℂ) ^ m)) atTop (𝓝 0) := by
      simpa using tendsto_finsetSum Finset.univ (fun η _ => hterm η)
    have hclassC : Tendsto
        (fun m => ((biasClassPow m k c : ℂ) / (2 : ℂ) ^ m))
        atTop (𝓝 0) := by
      apply hsum.congr'
      filter_upwards with m
      rw [biasClassPow_cast_eq_fourier m k c hc, Finset.sum_div]
    have hre := Complex.continuous_re.continuousAt.tendsto.comp hclassC
    apply hre.congr'
    filter_upwards with m
    have heq :
        ((((biasClassPow m k c : ℝ) / (2 : ℝ) ^ m : ℝ) : ℂ)) =
          (biasClassPow m k c : ℂ) / (2 : ℂ) ^ m := by
      push_cast
      rfl
    change ((biasClassPow m k c : ℂ) / (2 : ℂ) ^ m).re =
      (biasClassPow m k c : ℝ) / (2 : ℝ) ^ m
    calc
      ((biasClassPow m k c : ℂ) / (2 : ℂ) ^ m).re =
          ((((biasClassPow m k c : ℝ) / (2 : ℝ) ^ m : ℝ) : ℂ)).re :=
        congrArg Complex.re heq.symm
      _ = (biasClassPow m k c : ℝ) / (2 : ℝ) ^ m :=
        Complex.ofReal_re _
  · have hc' : 3 ^ k ≤ c := Nat.le_of_not_gt hc
    simpa [biasClassPow_eq_zero_of_pow_le _ _ _ hc'] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

/-- **Edge: Sec7P gives over-precision decay.**  The fine-modulus pairing theorem in
`WeakDecaySec7P.lean` gives a partial Pascal damping.  Padding its omitted pair sums by `2`
embeds it into the proved full level-`(a+k)` damping at a fixed-`k` cost at most `25^k`. -/
theorem overPrecSliceCharDecay : OverPrecSliceCharDecay := by
  rw [OverPrecSliceCharDecay]
  intro k A hA
  obtain ⟨C, hC, hdecay⟩ := numeratorExpSum_add_decay k A hA
  refine ⟨C, hC, ?_⟩
  intro j a ξ hj hja haj hξ
  unfold overPrecChar
  simpa only [div_eq_mul_inv, mul_assoc] using hdecay j a ξ hj hja haj hξ

/-- **C1⁺ holds**: every residue class of the start mod `3^k` carries `o(2^m)` signed mass. -/
theorem weakDecayOnZ3 : WeakDecayOnZ3 :=
  weakDecayOnZ3_of_overPrecSliceCharDecay overPrecSliceCharDecay

end CollatzMoonshot.Conjugacy
