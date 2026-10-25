/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.SliceDecay
import CollatzMoonshot.Conjugacy.SliceSeven

/-!
# C1 directly from slice character decay (2026-10-25)

A shortcut past `TruncatedSyracMixing` and Tao's §6.  For `r ∈ levelSet j a`, `y = T^j r < 3^a` is a
least residue mod `M = 3^a`, so the slice's signed count is `Σ_y mass(y)·g(y)`, with `g(y) = (−1)^y`
on `[0, M)`.  Expand `g` in additive characters of `ℤ/M`:
`ĝ(ξ) = (1/M)·2/(1 + e(−ξ/M))`, so `|ĝ(ξ)| = 1/(M·|cos(πξ/M)|)`, because `M` is odd.

* **Weights.**  `Σ_ξ |ĝ(ξ)| = O(log M) = O(a)`.  The frequencies with `v₃(ξ) = k` carry weight
  `O(3^{−k}·(a − k + 1))`.
* **Frequencies `ξ = 3^k u`, `3 ∤ u`.**  Here `F(ξ) = Σ_r e(u·T^j r / 3^{a−k})` is the character sum of
  the slice reduced mod `3^{a−k}`.  Given the `(a−k+1)`-th odd time `t`, that is the slice `(t−1, a−k)`.
  So `F(ξ)` is a mixture of `sliceChar (t−1) (a−k) u`.  The sub-slice ratios concentrate at `a/j`, and
  the exceptional `t` have binomially small mass.
* **Bound.**  `|levelSign j a|/#slice ≤ 3^{−a} + O(a)·sup_{k ≤ K} C·j^{−A} + O(a·3^{−K})`.  Take
  `K = ⌈2 log₃ j⌉` and `A = 2`.  The slices with `a/j` outside `[1/4, 11/20]` are the binomial tails
  already bounded in `Bridge3.lean` (`outOddSet`).
* **Checked** (`experiments/conjugacy/fourier_bias_check.py`):
  - the identity `levelSign = Σ_ξ conj(ĝ(ξ))·F(ξ)` is exact against brute-force Collatz at
    `(j,a) = (8,3), (10,5), (12,6), (12,7)`;
  - `Σ|ĝ| ≈ (2/π) ln M + 1`;
  - the level-`k` weights fall by about `3×` per level.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB

/-! ## Pascal recursion and sub-slices -/

/-- The positive additive character occurring in `sliceChar`, separated out so its change of
modulus and periodicity can be used without unfolding the whole slice sum. -/
noncomputable def slicePhase (a ξ y : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((ξ * y : ℕ) : ℂ) / (3 ^ a : ℂ))

theorem slicePhase_scale (a ξ y : ℕ) :
    slicePhase (a + 1) (3 * ξ) y = slicePhase a ξ y := by
  unfold slicePhase
  congr 1
  push_cast
  rw [pow_succ]
  field_simp

theorem slicePhase_add_mul_pow (a ξ y c : ℕ) :
    slicePhase a ξ (y + c * 3 ^ a) = slicePhase a ξ y := by
  unfold slicePhase
  rw [show
      2 * Real.pi * Complex.I * (((ξ * (y + c * 3 ^ a) : ℕ) : ℂ)) / (3 ^ a : ℂ) =
        2 * Real.pi * Complex.I * (((ξ * y : ℕ) : ℂ)) / (3 ^ a : ℂ) +
          (ξ * c : ℕ) * (2 * Real.pi * Complex.I) by
    push_cast
    field_simp]
  rw [Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

theorem oddCount_two_mul_succ (s j : ℕ) :
    oddCount (2 * s) (j + 1) = oddCount s j := by
  rw [oddCount_succ, tstep_two_mul]
  norm_num

theorem oddCount_two_mul_add_one_succ (s j : ℕ) :
    oddCount (2 * s + 1) (j + 1) = oddCount (3 * s + 2) j + 1 := by
  rw [oddCount_succ, tstep_two_mul_add_one]
  norm_num

/-- Split the next slice by the parity of its starting residue. -/
theorem sliceChar_succ_split (j a ξ : ℕ) :
    sliceChar (j + 1) (a + 1) (3 * ξ) =
      (∑ s ∈ Finset.range (2 ^ j),
        if oddCount s j = a + 1 then slicePhase (a + 1) (3 * ξ) (tstep^[j] s) else 0) +
      ∑ s ∈ Finset.range (2 ^ j),
        if oddCount (3 * s + 2) j = a then
          slicePhase (a + 1) (3 * ξ) (tstep^[j] (3 * s + 2)) else 0 := by
  unfold sliceChar levelSet slicePhase
  rw [Finset.sum_filter, pow_succ, mul_comm, sum_range_two_mul, Finset.sum_add_distrib]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro s hs
    rw [oddCount_two_mul_succ, Function.iterate_succ_apply, tstep_two_mul]
  · apply Finset.sum_congr rfl
    intro s hs
    rw [oddCount_two_mul_add_one_succ, Function.iterate_succ_apply, tstep_two_mul_add_one]
    simp only [Nat.add_right_cancel_iff]

theorem sliceChar_eq_sum_phase (j a ξ : ℕ) :
    sliceChar j a ξ = ∑ s ∈ Finset.range (2 ^ j),
      if oddCount s j = a then slicePhase a ξ (tstep^[j] s) else 0 := by
  unfold sliceChar levelSet slicePhase
  rw [Finset.sum_filter]

/-- Multiplication by three followed by addition of two permutes the residues modulo `2^j`. -/
noncomputable def affineThreeEquiv (j : ℕ) : ZMod (2 ^ j) ≃ ZMod (2 ^ j) :=
  (Units.mulLeft (ZMod.unitOfCoprime 3
    (Nat.Coprime.pow_right j (by decide : Nat.Coprime 3 2)))).trans
      (Equiv.addRight (2 : ZMod (2 ^ j)))

theorem affineThreeEquiv_apply (j : ℕ) (x : ZMod (2 ^ j)) :
    affineThreeEquiv j x = 3 * x + 2 := by
  simp [affineThreeEquiv, Units.mulLeft, ZMod.coe_unitOfCoprime]

theorem affineThreeEquiv_val (j : ℕ) (x : ZMod (2 ^ j)) :
    (affineThreeEquiv j x).val = (3 * x.val + 2) % 2 ^ j := by
  rw [affineThreeEquiv_apply, ZMod.val_add, ZMod.val_mul]
  rw [ZMod.val_ofNat, ZMod.val_ofNat]
  have hmul : (3 % 2 ^ j * x.val) % 2 ^ j = (3 * x.val) % 2 ^ j :=
    (Nat.mod_modEq 3 (2 ^ j)).mul_right x.val
  rw [hmul, ← Nat.add_mod]

theorem oddCount_affineThree_mod (j s : ℕ) :
    oddCount (3 * s + 2) j = oddCount ((3 * s + 2) % 2 ^ j) j := by
  let y := 3 * s + 2
  let x := y % 2 ^ j
  let c := y / 2 ^ j
  have hy : y = x + c * 2 ^ j := by
    calc
      y = y % 2 ^ j + 2 ^ j * (y / 2 ^ j) := (Nat.mod_add_div y (2 ^ j)).symm
      _ = x + c * 2 ^ j := by dsimp [x, c]; ring
  change oddCount y j = oddCount x j
  rw [hy, oddCount_add_mul_two_pow]

theorem tstep_iterate_affineThree_mod (j s : ℕ) :
    tstep^[j] (3 * s + 2) =
      tstep^[j] ((3 * s + 2) % 2 ^ j) +
        ((3 * s + 2) / 2 ^ j) * 3 ^ oddCount ((3 * s + 2) % 2 ^ j) j := by
  let y := 3 * s + 2
  let x := y % 2 ^ j
  let c := y / 2 ^ j
  have hy : y = x + c * 2 ^ j := by
    calc
      y = y % 2 ^ j + 2 ^ j * (y / 2 ^ j) := (Nat.mod_add_div y (2 ^ j)).symm
      _ = x + c * 2 ^ j := by dsimp [x, c]; ring
  change tstep^[j] y = tstep^[j] x + c * 3 ^ oddCount x j
  rw [hy, tstep_iterate_add_mul_two_pow]

theorem affineThreeNat_injective (j : ℕ) :
    Set.InjOn (fun s => (3 * s + 2) % 2 ^ j) (Finset.range (2 ^ j)) := by
  intro s hs t ht hst
  have hslt : s < 2 ^ j := Finset.mem_range.mp hs
  have htlt : t < 2 ^ j := Finset.mem_range.mp ht
  change (3 * s + 2) % 2 ^ j = (3 * t + 2) % 2 ^ j at hst
  have he : affineThreeEquiv j (s : ZMod (2 ^ j)) =
      affineThreeEquiv j (t : ZMod (2 ^ j)) := by
    apply ZMod.val_injective
    rw [affineThreeEquiv_val, affineThreeEquiv_val,
      ZMod.val_natCast_of_lt hslt, ZMod.val_natCast_of_lt htlt, hst]
  have hcast : (s : ZMod (2 ^ j)) = (t : ZMod (2 ^ j)) :=
    (affineThreeEquiv j).injective he
  have hval := congrArg ZMod.val hcast
  simpa [ZMod.val_natCast_of_lt hslt, ZMod.val_natCast_of_lt htlt] using hval

theorem affineThreeNat_surjective (j : ℕ) :
    Set.SurjOn (fun s => (3 * s + 2) % 2 ^ j)
      (Finset.range (2 ^ j)) (Finset.range (2 ^ j)) := by
  intro x hx
  have hxlt : x < 2 ^ j := Finset.mem_range.mp hx
  let q : ZMod (2 ^ j) := (affineThreeEquiv j).symm (x : ZMod (2 ^ j))
  refine ⟨q.val, Finset.mem_range.mpr (ZMod.val_lt q), ?_⟩
  have he : affineThreeEquiv j q = (x : ZMod (2 ^ j)) := by
    simp [q]
  have hval := congrArg ZMod.val he
  rw [affineThreeEquiv_val, ZMod.val_natCast_of_lt hxlt] at hval
  exact hval

theorem slicePhase_affineThree_mod {j a ξ s : ℕ}
    (ha : oddCount (3 * s + 2) j = a) :
    slicePhase (a + 1) (3 * ξ) (tstep^[j] (3 * s + 2)) =
      slicePhase a ξ (tstep^[j] ((3 * s + 2) % 2 ^ j)) := by
  rw [slicePhase_scale, tstep_iterate_affineThree_mod,
    ← oddCount_affineThree_mod j s, ha, slicePhase_add_mul_pow]

theorem sliceChar_odd_succ (j a ξ : ℕ) :
    (∑ s ∈ Finset.range (2 ^ j),
      if oddCount (3 * s + 2) j = a then
        slicePhase (a + 1) (3 * ξ) (tstep^[j] (3 * s + 2)) else 0) =
      sliceChar j a ξ := by
  rw [sliceChar_eq_sum_phase]
  apply Finset.sum_nbij (fun s => (3 * s + 2) % 2 ^ j)
  · intro s hs
    exact Finset.mem_range.mpr (Nat.mod_lt _ (by positivity))
  · exact affineThreeNat_injective j
  · exact affineThreeNat_surjective j
  · intro s hs
    rw [← oddCount_affineThree_mod j s]
    split_ifs with ha
    · exact slicePhase_affineThree_mod ha
    · rfl

/-- **Pascal recursion.**  The slice with one extra odd step splits into even starts, which keep
the modulus-`3^(a+1)` slice, and odd starts, whose affine images permute `ℤ/2^j`. -/
theorem sliceChar_pascal (j a ξ : ℕ) :
    sliceChar (j + 1) (a + 1) (3 * ξ) =
      sliceChar j (a + 1) (3 * ξ) + sliceChar j a ξ := by
  rw [sliceChar_succ_split, sliceChar_odd_succ]
  congr 1
  exact (sliceChar_eq_sum_phase j (a + 1) (3 * ξ)).symm

/-- The closed form obtained by iterating `sliceChar_pascal` through `k` powers of three.  The
index `t=s-1` is exactly the positive-time indexing; starting the sum at `s=0` would introduce a
spurious term when `k=1`. -/
noncomputable def subsliceSum (j a k u : ℕ) : ℂ :=
  ∑ t ∈ Finset.range j,
    (t.choose (k - 1) : ℂ) * sliceChar (j - 1 - t) (a - k) u

/-- **Sub-slice decomposition.**  A frequency divisible by `3^k` is the binomially weighted sum
of the slices seen immediately after the `k`-th odd step. -/
theorem sliceChar_eq_subsliceSum (j a k u : ℕ) (hk : 1 ≤ k) (hka : k ≤ a) :
    sliceChar j a (3 ^ k * u) = subsliceSum j a k u := by
  induction j generalizing a k with
  | zero =>
      have ha : a ≠ 0 := by omega
      have h0a : ¬ 0 = a := by omega
      simp [subsliceSum, sliceChar, levelSet, oddCount_zero, h0a]
  | succ j ih =>
      cases a with
      | zero => omega
      | succ a =>
          cases k with
          | zero => omega
          | succ k =>
              have hfreq : 3 ^ (k + 1) * u = 3 * (3 ^ k * u) := by
                rw [pow_succ']
                ring
              rw [hfreq, sliceChar_pascal, ← hfreq]
              cases k with
              | zero =>
                  simp only [pow_zero, one_mul]
                  rw [ih (a + 1) 1 (by omega) (by omega)]
                  simp only [subsliceSum, Nat.add_sub_cancel, Nat.reduceSubDiff,
                    Nat.choose_zero_right, Nat.cast_one, one_mul, Finset.sum_range_succ']
                  congr 1
                  apply Finset.sum_congr rfl
                  intro t ht
                  have htj : t < j := Finset.mem_range.mp ht
                  apply congrArg (fun n => sliceChar n a u)
                  omega
              | succ k =>
                  rw [ih (a + 1) (k + 2) (by omega) (by omega),
                    ih a (k + 1) (by omega) (by omega)]
                  unfold subsliceSum
                  rw [Finset.sum_range_succ']
                  rw [show k + 2 - 1 = k + 1 by omega,
                    show k + 1 - 1 = k by omega,
                    show a + 1 - (k + 2) = a - (k + 1) by omega]
                  simp only [Nat.choose_zero_succ, Nat.cast_zero, zero_mul, add_zero,
                    Nat.add_sub_cancel, Nat.sub_zero]
                  rw [← Finset.sum_add_distrib]
                  apply Finset.sum_congr rfl
                  intro t ht
                  have htj : t < j := Finset.mem_range.mp ht
                  rw [show j - (t + 1) = j - 1 - t by omega, Nat.choose_succ_succ]
                  push_cast
                  ring

/-! ## Concentration of the sub-slice weights -/

/-- The zero-frequency slice character is the cardinality of its slice. -/
theorem sliceChar_zero (j a : ℕ) :
    sliceChar j a 0 = ((levelSet j a).card : ℂ) := by
  unfold sliceChar
  simp

/-- The cardinality weight of the sub-slice immediately after the `k`-th odd step at time
`t+1`. -/
def subsliceWeight (j a k t : ℕ) : ℕ :=
  t.choose (k - 1) * (j - 1 - t).choose (a - k)

/-- The sub-slice weights partition the whole level set.  This is Vandermonde's identity in the
positive-time indexing forced by `sliceChar_eq_subsliceSum`. -/
theorem sum_subsliceWeight (j a k : ℕ) (hk : 1 ≤ k) (hka : k ≤ a) :
    ∑ t ∈ Finset.range j, subsliceWeight j a k t = j.choose a := by
  have hdecomp := sliceChar_eq_subsliceSum j a k 0 hk hka
  simp only [mul_zero] at hdecomp
  rw [sliceChar_zero, card_levelSet_eq_choose] at hdecomp
  unfold subsliceSum at hdecomp
  simp_rw [sliceChar_zero, card_levelSet_eq_choose] at hdecomp
  have hcast :
      ((∑ t ∈ Finset.range j, subsliceWeight j a k t : ℕ) : ℂ) =
        (j.choose a : ℂ) := by
    simpa [subsliceWeight, Nat.cast_mul] using hdecomp.symm
  exact_mod_cast hcast

/-- Well after its mode, the time of the `k`-th odd step has a uniform geometric tail.  The
generous separation `4096k ≤ j` makes the two binomial consecutive-term ratios at most `9/8`
and `7/9`, respectively. -/
theorem subsliceWeight_succ_le {j a k t : ℕ}
    (hjlow : 4096 * k ≤ j) (hja : j ≤ 4 * a) (hk : 1 ≤ k) (hka : k ≤ a)
    (htlow : j / 32 ≤ t) (htj : t + 1 < j) :
    8 * subsliceWeight j a k (t + 1) ≤ 7 * subsliceWeight j a k t := by
  by_cases hzero : j - 1 - (t + 1) < a - k
  · rw [subsliceWeight, Nat.choose_eq_zero_of_lt hzero]
    simp
  have hrle : a - k ≤ j - 1 - (t + 1) := Nat.le_of_not_gt hzero
  have hkt : k ≤ t + 1 := by omega
  have hA := Nat.choose_mul_succ_eq t (k - 1)
  have hAarg : t + 1 - (k - 1) = t + 2 - k := by omega
  rw [hAarg] at hA
  have hB := Nat.choose_mul_succ_eq (j - 1 - (t + 1)) (a - k)
  have hn : j - 1 - (t + 1) + 1 = j - 1 - t := by omega
  rw [hn] at hB
  have hfirst : 9 * k ≤ t + 10 := by omega
  have hfac1 : 8 * (t + 1) ≤ 9 * (t + 2 - k) := by omega
  have hk9 : 9 * k ≤ a := by omega
  have hfac2 : 9 * (j - 1 - t - (a - k)) ≤ 7 * (j - 1 - t) := by omega
  have hfac :
      8 * (t + 1) * (j - 1 - t - (a - k)) ≤
        7 * (t + 2 - k) * (j - 1 - t) := by
    calc
      8 * (t + 1) * (j - 1 - t - (a - k)) ≤
          (9 * (t + 2 - k)) * (j - 1 - t - (a - k)) :=
        Nat.mul_le_mul_right _ hfac1
      _ = (t + 2 - k) * (9 * (j - 1 - t - (a - k))) := by ring
      _ ≤ (t + 2 - k) * (7 * (j - 1 - t)) :=
        Nat.mul_le_mul_left _ hfac2
      _ = 7 * (t + 2 - k) * (j - 1 - t) := by ring
  have hE1 : 0 < t + 2 - k := by omega
  have hE2 : 0 < j - 1 - t := by omega
  have hE : 0 < (t + 2 - k) * (j - 1 - t) := Nat.mul_pos hE1 hE2
  apply Nat.le_of_mul_le_mul_right _ hE
  calc
    (8 * subsliceWeight j a k (t + 1)) * ((t + 2 - k) * (j - 1 - t)) =
        8 * ((t + 1).choose (k - 1) * (t + 2 - k)) *
          ((j - 1 - (t + 1)).choose (a - k) * (j - 1 - t)) := by
      simp only [subsliceWeight]
      ring
    _ = 8 * (t.choose (k - 1) * (t + 1)) *
          ((j - 1 - t).choose (a - k) * (j - 1 - t - (a - k))) := by
      rw [← hA, hB]
    _ = (t.choose (k - 1) * (j - 1 - t).choose (a - k)) *
          (8 * (t + 1) * (j - 1 - t - (a - k))) := by ring
    _ ≤ (t.choose (k - 1) * (j - 1 - t).choose (a - k)) *
          (7 * (t + 2 - k) * (j - 1 - t)) :=
      Nat.mul_le_mul_left _ hfac
    _ = (7 * subsliceWeight j a k t) * ((t + 2 - k) * (j - 1 - t)) := by
      simp only [subsliceWeight]
      ring

theorem subsliceWeight_antitone {j a k m t : ℕ}
    (hjlow : 4096 * k ≤ j) (hja : j ≤ 4 * a) (hk : 1 ≤ k) (hka : k ≤ a)
    (hmlow : j / 32 ≤ m) (hmt : m ≤ t) (htj : t < j) :
    subsliceWeight j a k t ≤ subsliceWeight j a k m := by
  refine Nat.le_induction (fun _ => le_rfl) (fun n hmn ih hn1j => ?_) t hmt htj
  have hs := subsliceWeight_succ_le hjlow hja hk hka
    (le_trans hmlow hmn) (by omega : n + 1 < j)
  have hstep : subsliceWeight j a k (n + 1) ≤ subsliceWeight j a k n := by omega
  exact hstep.trans (ih (by omega))

/-- Iteration of the `7/8` consecutive-weight contraction. -/
theorem subsliceWeight_geom (j a k r : ℕ)
    (hjlow : 4096 * k ≤ j) (hja : j ≤ 4 * a) (hk : 1 ≤ k) (hka : k ≤ a)
    (hr : j / 32 + r < j) :
    8 ^ r * subsliceWeight j a k (j / 32 + r) ≤
      7 ^ r * subsliceWeight j a k (j / 32) := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hr' : j / 32 + r < j := by omega
      have hs := subsliceWeight_succ_le hjlow hja hk hka
        (show j / 32 ≤ j / 32 + r by omega) (by omega : j / 32 + r + 1 < j)
      calc
        8 ^ (r + 1) * subsliceWeight j a k (j / 32 + (r + 1)) =
            8 ^ r * (8 * subsliceWeight j a k (j / 32 + r + 1)) := by
          simp only [pow_succ, Nat.add_assoc]
          ring
        _ ≤ 8 ^ r * (7 * subsliceWeight j a k (j / 32 + r)) :=
          Nat.mul_le_mul_left _ hs
        _ = 7 * (8 ^ r * subsliceWeight j a k (j / 32 + r)) := by ring
        _ ≤ 7 * (7 ^ r * subsliceWeight j a k (j / 32)) :=
          Nat.mul_le_mul_left _ (ih hr')
        _ = 7 ^ (r + 1) * subsliceWeight j a k (j / 32) := by
          rw [pow_succ]
          ring

/-- The mass of sub-slices whose `k`-th odd step occurs after time `m`. -/
def subsliceTail (j a k m : ℕ) : ℕ :=
  ∑ t ∈ (Finset.range j).filter (fun t => m ≤ t), subsliceWeight j a k t

/-- **Sub-slice concentration.**  In the central slice window, every `k` with `4096k ≤ j` has an
exponentially small late tail.  This direct consecutive-weight proof avoids a separate partial
Vandermonde identity. -/
theorem subslice_tail_le (j a k : ℕ) (hj : 32 ≤ j)
    (hjlow : 4096 * k ≤ j) (hja : j ≤ 4 * a) (hk : 1 ≤ k) (hka : k ≤ a) :
    8 ^ (j / 16 - j / 32) * subsliceTail j a k (j / 16) ≤
      j * 7 ^ (j / 16 - j / 32) * j.choose a := by
  let m := j / 16
  let t0 := j / 32
  let r := m - t0
  have hjpos : 0 < j := lt_of_lt_of_le (by norm_num) hj
  have ht0m : t0 ≤ m := by dsimp [t0, m]; omega
  have hmj : m < j := by
    dsimp [m]
    exact Nat.div_lt_self hjpos (by norm_num)
  have ht0j : t0 < j := lt_of_le_of_lt ht0m hmj
  have htail : subsliceTail j a k m ≤ j * subsliceWeight j a k m := by
    calc
      subsliceTail j a k m ≤
          ∑ _t ∈ (Finset.range j).filter (fun t => m ≤ t), subsliceWeight j a k m := by
        unfold subsliceTail
        apply Finset.sum_le_sum
        intro t ht
        exact subsliceWeight_antitone hjlow hja hk hka
          (le_trans (show t0 ≤ m from ht0m) (by rfl))
          (Finset.mem_filter.mp ht).2
          (Finset.mem_range.mp (Finset.mem_filter.mp ht).1)
      _ = ((Finset.range j).filter (fun t => m ≤ t)).card * subsliceWeight j a k m := by
        simp
      _ ≤ j * subsliceWeight j a k m := by
        gcongr
        exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range j)
  have ht0r : t0 + r = m := Nat.add_sub_of_le ht0m
  have hgeom : 8 ^ r * subsliceWeight j a k m ≤ 7 ^ r * subsliceWeight j a k t0 := by
    have := subsliceWeight_geom j a k r hjlow hja hk hka
      (by rw [ht0r]; exact hmj)
    simpa [t0, ht0r] using this
  have hterm : subsliceWeight j a k t0 ≤ j.choose a := by
    have hsingle : subsliceWeight j a k t0 ≤
        ∑ t ∈ Finset.range j, subsliceWeight j a k t := by
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr ht0j)
    simpa [sum_subsliceWeight j a k hk hka] using hsingle
  change 8 ^ r * subsliceTail j a k m ≤ j * 7 ^ r * j.choose a
  calc
    8 ^ r * subsliceTail j a k m ≤ 8 ^ r * (j * subsliceWeight j a k m) :=
      Nat.mul_le_mul_left _ htail
    _ = j * (8 ^ r * subsliceWeight j a k m) := by ring
    _ ≤ j * (7 ^ r * subsliceWeight j a k t0) := Nat.mul_le_mul_left _ hgeom
    _ ≤ j * (7 ^ r * j.choose a) := by gcongr
    _ = j * 7 ^ r * j.choose a := by ring

/-! ## Fourier expansion of least-residue parity -/

/-- The normalized Fourier coefficient of least-residue parity on `ℤ/(3^a)`. -/
noncomputable def gHatZ (a : ℕ) (ξ : ZMod (3 ^ a)) : ℂ :=
  ((3 ^ a : ℕ) : ℂ)⁻¹ * ∑ y : ZMod (3 ^ a),
    (paritySign y.val : ℂ) * ZMod.stdAddChar (-(ξ * y))

theorem slicePhase_eq_stdAddChar (a ξ y : ℕ) :
    slicePhase a ξ y = ZMod.stdAddChar ((ξ : ZMod (3 ^ a)) * (y : ZMod (3 ^ a))) := by
  rw [show (ξ : ZMod (3 ^ a)) * (y : ZMod (3 ^ a)) =
      ((ξ * y : ℕ) : ZMod (3 ^ a)) by norm_cast]
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_natCast]
  unfold slicePhase
  push_cast
  rfl

/-- The exponential in `sliceChar` is mathlib's standard additive character. -/
theorem sliceChar_eq_zmod_sum (j a ξ : ℕ) :
    sliceChar j a ξ = ∑ r ∈ levelSet j a,
      ZMod.stdAddChar ((ξ : ZMod (3 ^ a)) * (tstep^[j] r : ZMod (3 ^ a))) := by
  rw [sliceChar_eq_sum_phase]
  unfold levelSet
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r hr
  split_ifs
  · exact slicePhase_eq_stdAddChar a ξ (tstep^[j] r)
  · rfl

/-- Fourier inversion on the odd cyclic group `ℤ/(3^a)`, in the normalization used by `gHatZ`. -/
theorem zmod_fourier_inversion (a : ℕ) (f : ZMod (3 ^ a) → ℂ) (y : ZMod (3 ^ a)) :
    ∑ ξ : ZMod (3 ^ a),
      (((3 ^ a : ℕ) : ℂ)⁻¹ * ∑ z : ZMod (3 ^ a),
        f z * ZMod.stdAddChar (-(ξ * z))) * ZMod.stdAddChar (ξ * y) = f y := by
  let M := 3 ^ a
  have hM : (M : ℂ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero a (by norm_num : (3 : ℕ) ≠ 0))
  have horth (z : ZMod M) :
      ∑ ξ : ZMod M, ZMod.stdAddChar (ξ * (y - z)) =
        if y = z then (M : ℂ) else 0 := by
    rw [AddChar.sum_mulShift (y - z) (ZMod.isPrimitive_stdAddChar M)]
    simp [sub_eq_zero, ZMod.card, M]
  change ∑ ξ : ZMod M,
      ((M : ℂ)⁻¹ * ∑ z : ZMod M, f z * ZMod.stdAddChar (-(ξ * z))) *
        ZMod.stdAddChar (ξ * y) = f y
  calc
    _ = ∑ z : ZMod M, ∑ ξ : ZMod M,
          (M : ℂ)⁻¹ * (f z * ZMod.stdAddChar (-(ξ * z))) *
            ZMod.stdAddChar (ξ * y) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = (M : ℂ)⁻¹ * ∑ z : ZMod M, f z *
          ∑ ξ : ZMod M, ZMod.stdAddChar (ξ * (y - z)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ξ hξ
      have hc : ZMod.stdAddChar (-(ξ * z)) * ZMod.stdAddChar (ξ * y) =
          ZMod.stdAddChar (ξ * (y - z)) := by
        rw [← AddChar.map_add_eq_mul]
        congr 1
        ring
      rw [show (M : ℂ)⁻¹ * (f z * ZMod.stdAddChar (-(ξ * z))) *
          ZMod.stdAddChar (ξ * y) =
          (M : ℂ)⁻¹ * f z *
            (ZMod.stdAddChar (-(ξ * z)) * ZMod.stdAddChar (ξ * y)) by ring, hc]
      ring
    _ = (M : ℂ)⁻¹ * ((M : ℂ) * f y) := by
      congr 1
      simp_rw [horth]
      simp
      ring
    _ = f y := by field_simp

/-- **Fourier identity.**  Since every slice iterate is the least representative below `3^a`,
Fourier inversion of least-residue parity turns the signed slice count into its complete family
of slice characters. -/
theorem levelSign_eq_fourier_slice (j a : ℕ) :
    (levelSign j a : ℂ) =
      ∑ ξ : ZMod (3 ^ a), gHatZ a ξ * sliceChar j a ξ.val := by
  rw [show (levelSign j a : ℂ) =
      ∑ r ∈ levelSet j a, (paritySign (tstep^[j] r) : ℂ) by
    unfold levelSign
    push_cast
    apply Finset.sum_congr rfl
    intro r hr
    rw [paritySign_eq_ite]
    split_ifs <;> norm_num]
  simp_rw [sliceChar_eq_zmod_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  unfold gHatZ
  have hinv := zmod_fourier_inversion a (fun y => (paritySign y.val : ℂ))
    (tstep^[j] r : ZMod (3 ^ a))
  have hlt : tstep^[j] r < 3 ^ a := by
    have h := tstep_iterate_lt_three_pow
      (Finset.mem_range.mp (Finset.mem_filter.mp hr).1)
    simpa [(Finset.mem_filter.mp hr).2] using h
  rw [ZMod.val_natCast_of_lt hlt] at hinv
  simpa only [ZMod.natCast_zmod_val] using hinv.symm

/-! ## Exact Fourier weights -/

/-- Reindex a sum over `ZMod M` by the least representatives in `[0,M)`. -/
theorem sum_zmod_eq_sum_range {M : ℕ} [NeZero M] {R : Type*} [AddCommMonoid R]
    (f : ZMod M → R) :
    (∑ y : ZMod M, f y) = ∑ n ∈ Finset.range M, f n := by
  apply Finset.sum_bij (fun y _ => y.val)
  · intro y hy
    exact Finset.mem_range.mpr y.val_lt
  · intro y₁ h₁ y₂ h₂ h
    exact ZMod.val_injective M h
  · intro n hn
    refine ⟨(n : ZMod M), Finset.mem_univ _, ?_⟩
    exact ZMod.val_natCast_of_lt (Finset.mem_range.mp hn)
  · intro y hy
    rw [ZMod.natCast_zmod_val]

theorem parity_addChar_term (a n : ℕ) (ξ : ZMod (3 ^ a)) :
    (paritySign n : ℂ) * ZMod.stdAddChar (-(ξ * (n : ZMod (3 ^ a)))) =
      (-ZMod.stdAddChar (-ξ)) ^ n := by
  rw [show -(ξ * (n : ZMod (3 ^ a))) = n • (-ξ) by
    simp only [nsmul_eq_mul]
    ring]
  rw [AddChar.map_nsmul_eq_pow]
  rw [show (paritySign n : ℂ) = (-1 : ℂ) ^ n by simp [paritySign]]
  rw [← mul_pow]
  congr 1
  ring

/-- The parity transform is a geometric sum of odd length `3^a`. -/
theorem gHatZ_eq_geom (a : ℕ) (ξ : ZMod (3 ^ a)) :
    gHatZ a ξ = ((3 ^ a : ℕ) : ℂ)⁻¹ *
      ∑ n ∈ Finset.range (3 ^ a), (-ZMod.stdAddChar (-ξ)) ^ n := by
  unfold gHatZ
  congr 1
  rw [sum_zmod_eq_sum_range]
  apply Finset.sum_congr rfl
  intro n hn
  rw [ZMod.val_natCast_of_lt (Finset.mem_range.mp hn)]
  exact parity_addChar_term a n ξ

theorem stdAddChar_pow_card (a : ℕ) (ξ : ZMod (3 ^ a)) :
    ZMod.stdAddChar (-ξ) ^ (3 ^ a) = 1 := by
  rw [← AddChar.map_nsmul_eq_pow]
  have : (3 ^ a) • (-ξ) = 0 := by
    simp only [nsmul_eq_mul]
    have hcast : ((3 ^ a : ℕ) : ZMod (3 ^ a)) = 0 := ZMod.natCast_self _
    rw [hcast]
    simp
  rw [this]
  simp

/-- A character of an odd cyclic group cannot take the value `-1`. -/
theorem stdAddChar_ne_neg_one (a : ℕ) (ξ : ZMod (3 ^ a)) :
    ZMod.stdAddChar (-ξ) ≠ -1 := by
  intro h
  have hp := stdAddChar_pow_card a ξ
  rw [h] at hp
  have hodd : Odd (3 ^ a) := (show Odd 3 by norm_num).pow
  rw [hodd.neg_one_pow] at hp
  norm_num at hp

/-- Closed form for the normalized Fourier coefficient of least-residue parity. -/
theorem gHatZ_closed (a : ℕ) (ξ : ZMod (3 ^ a)) :
    gHatZ a ξ = 2 / (((3 ^ a : ℕ) : ℂ) * (1 + ZMod.stdAddChar (-ξ))) := by
  rw [gHatZ_eq_geom, geom_sum_eq]
  · have hodd : Odd (3 ^ a) := (show Odd 3 by norm_num).pow
    have hpow : (-ZMod.stdAddChar (-ξ)) ^ (3 ^ a) = -1 := by
      rw [neg_pow, hodd.neg_one_pow, stdAddChar_pow_card]
      ring
    rw [hpow]
    have hM : (((3 ^ a : ℕ) : ℂ)) ≠ 0 := by
      exact_mod_cast (pow_ne_zero a (by norm_num : (3 : ℕ) ≠ 0))
    have hq : (1 + ZMod.stdAddChar (-ξ)) ≠ 0 := by
      intro hz
      apply stdAddChar_ne_neg_one a ξ
      exact eq_neg_of_add_eq_zero_right hz
    have hden : -ZMod.stdAddChar (-ξ) - 1 ≠ 0 := by
      intro hz
      apply hq
      linear_combination -hz
    calc
      ((3 ^ a : ℕ) : ℂ)⁻¹ * ((-1 - 1) / (-ZMod.stdAddChar (-ξ) - 1)) =
          ((3 ^ a : ℕ) : ℂ)⁻¹ * (2 / (1 + ZMod.stdAddChar (-ξ))) := by
            congr 1
            field_simp [hden, hq]
            ring
      _ = 2 / (((3 ^ a : ℕ) : ℂ) * (1 + ZMod.stdAddChar (-ξ))) := by
        field_simp
  · intro h
    have := congrArg Neg.neg h
    simp only [neg_neg] at this
    exact stdAddChar_ne_neg_one a ξ this

theorem norm_gHatZ_closed (a : ℕ) (ξ : ZMod (3 ^ a)) :
    ‖gHatZ a ξ‖ = 2 / ((3 ^ a : ℝ) * ‖1 + ZMod.stdAddChar (-ξ)‖) := by
  rw [gHatZ_closed, norm_div, norm_mul]
  norm_num

theorem stdAddChar_neg_eq_exp (a : ℕ) (ξ : ZMod (3 ^ a)) :
    ZMod.stdAddChar (-ξ) =
      Complex.exp (-(2 * Real.pi * Complex.I * (ξ.val : ℂ) / (3 ^ a : ℂ))) := by
  rw [show -ξ = ((-(ξ.val : ℤ)) : ZMod (3 ^ a)) by
    simpa only [Int.cast_neg, Int.cast_natCast] using
      (congrArg Neg.neg (ZMod.natCast_zmod_val ξ)).symm]
  have h := ZMod.stdAddChar_coe (N := 3 ^ a) (-(ξ.val : ℤ))
  convert h using 1 <;> push_cast <;> ring

theorem one_add_exp_neg_two_mul_I (x : ℝ) :
    1 + Complex.exp (-(2 * x * Complex.I)) =
      (2 * Real.cos x : ℂ) * Complex.exp (-(x * Complex.I)) := by
  rw [show -(2 * x * Complex.I) = ((-2 * x : ℝ) : ℂ) * Complex.I by
    push_cast
    ring]
  rw [show -(x * Complex.I) = ((-x : ℝ) : ℂ) * Complex.I by
    push_cast
    ring]
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  simp_rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [show -2 * x = -(2 * x) by ring]
  simp only [Real.cos_neg, Real.sin_neg]
  rw [Real.cos_two_mul, Real.sin_two_mul]
  push_cast
  ring

/-- The character denominator has exactly the expected half-angle norm. -/
theorem norm_one_add_stdAddChar (a : ℕ) (ξ : ZMod (3 ^ a)) :
    ‖1 + ZMod.stdAddChar (-ξ)‖ =
      2 * |Real.cos (Real.pi * ξ.val / 3 ^ a)| := by
  rw [stdAddChar_neg_eq_exp]
  let x : ℝ := Real.pi * ξ.val / 3 ^ a
  have he : -(2 * Real.pi * Complex.I * (ξ.val : ℂ) / (3 ^ a : ℂ)) =
      -(2 * x * Complex.I) := by
    dsimp [x]
    push_cast
    ring
  rw [he, one_add_exp_neg_two_mul_I]
  rw [norm_mul]
  rw [show (2 : ℂ) * (Real.cos x : ℂ) = ((2 * Real.cos x : ℝ) : ℂ) by norm_num]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
  have hn : ‖Complex.exp (-(x * Complex.I))‖ = 1 := by
    rw [show -(x * Complex.I) = ((-x : ℝ) : ℂ) * Complex.I by
      push_cast
      ring]
    exact Complex.norm_exp_ofReal_mul_I (-x)
  rw [hn, mul_one]
  simp [x]

/-- Exact norm of a Fourier weight, the starting point for the odd harmonic bound. -/
theorem norm_gHatZ_cos (a : ℕ) (ξ : ZMod (3 ^ a)) :
    ‖gHatZ a ξ‖ =
      1 / ((3 ^ a : ℝ) * |Real.cos (Real.pi * ξ.val / 3 ^ a)|) := by
  rw [norm_gHatZ_closed, norm_one_add_stdAddChar]
  ring

/-- The zero frequency is exactly the normalized slice cardinality coefficient. -/
theorem gHatZ_zero (a : ℕ) :
    gHatZ a 0 = (((3 ^ a : ℕ) : ℂ))⁻¹ := by
  rw [gHatZ_closed]
  simp
  ring

/-- Jordan's inequality bounds the distance from the middle of an odd character group by the
corresponding cosine denominator. -/
theorem abs_two_mul_sub_le_pow_mul_abs_cos (a n : ℕ) (hn : n < 3 ^ a) :
    |(2 * (n : ℝ) - (3 ^ a : ℝ))| ≤
      (3 ^ a : ℝ) * |Real.cos (Real.pi * n / 3 ^ a)| := by
  let M : ℝ := (3 ^ a : ℕ)
  let x : ℝ := Real.pi / 2 - Real.pi * n / M
  have hM : 0 < M := by positivity
  have hnle : (n : ℝ) ≤ M := by
    simpa [M] using (show (n : ℝ) ≤ ((3 ^ a : ℕ) : ℝ) by
      exact_mod_cast (Nat.le_of_lt hn))
  have hratio0 : 0 ≤ (n : ℝ) / M := div_nonneg (by positivity) hM.le
  have hratio1 : (n : ℝ) / M ≤ 1 := (div_le_one hM).2 hnle
  have hy0 : 0 ≤ Real.pi * (n : ℝ) / M := by positivity
  have hypi : Real.pi * (n : ℝ) / M ≤ Real.pi := by
    calc
      Real.pi * (n : ℝ) / M = Real.pi * ((n : ℝ) / M) := by ring
      _ ≤ Real.pi * 1 := mul_le_mul_of_nonneg_left hratio1 Real.pi_pos.le
      _ = Real.pi := mul_one _
  have hxabs : |x| ≤ Real.pi / 2 := by
    rw [abs_le]
    constructor <;> dsimp [x] <;> linarith
  have hj := Real.mul_abs_le_abs_sin hxabs
  have hxform : x = Real.pi / (2 * M) * (M - 2 * (n : ℝ)) := by
    dsimp [x]
    field_simp [hM.ne', Real.pi_ne_zero]
  have hleft : M * (2 / Real.pi * |x|) = |2 * (n : ℝ) - M| := by
    rw [hxform, abs_mul]
    have hcoef : 0 ≤ Real.pi / (2 * M) := by positivity
    rw [abs_of_nonneg hcoef, abs_sub_comm]
    field_simp [hM.ne', Real.pi_ne_zero]
  have hsin : |Real.sin x| = |Real.cos (Real.pi * n / M)| := by
    dsimp [x]
    rw [Real.sin_pi_div_two_sub]
  have hmain : |2 * (n : ℝ) - M| ≤ M * |Real.cos (Real.pi * n / M)| := by
    rw [← hleft, ← hsin]
    exact mul_le_mul_of_nonneg_left hj hM.le
  simpa [M] using hmain

/-- Pointwise comparison of a parity Fourier weight with its odd harmonic denominator. -/
theorem norm_gHatZ_le_inv_abs (a : ℕ) (ξ : ZMod (3 ^ a)) :
    ‖gHatZ a ξ‖ ≤ 1 / |(2 : ℝ) * ξ.val - 3 ^ a| := by
  rw [norm_gHatZ_cos]
  apply one_div_le_one_div_of_le
  · have hne : (2 : ℕ) * ξ.val ≠ 3 ^ a := by
      intro h
      rcases (show Odd (3 ^ a) from (show Odd 3 by norm_num).pow) with ⟨k, hk⟩
      omega
    have hneR : (2 : ℝ) * ξ.val ≠ (3 ^ a : ℝ) := by exact_mod_cast hne
    exact abs_pos.mpr (sub_ne_zero.mpr hneR)
  · exact abs_two_mul_sub_le_pow_mul_abs_cos a ξ.val ξ.val_lt

/-- An injective family of positive integer denominators bounded by `N` has reciprocal sum at
most the `N`-th harmonic number. -/
theorem sum_inv_nat_le_harmonic_of_injOn {s : Finset ℕ} {f : ℕ → ℕ} {N : ℕ}
    (hinj : Set.InjOn f s) (hmem : ∀ n ∈ s, f n ∈ Finset.Icc 1 N) :
    ∑ n ∈ s, (1 : ℝ) / f n ≤ (harmonic N : ℝ) := by
  have hsubset : s.image f ⊆ Finset.Icc 1 N := by
    intro y hy
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hy
    exact hmem n hn
  calc
    ∑ n ∈ s, (1 : ℝ) / f n = ∑ y ∈ s.image f, (1 : ℝ) / y :=
      (Finset.sum_image (f := fun y : ℕ => (1 : ℝ) / y) hinj).symm
    _ ≤ ∑ y ∈ Finset.Icc 1 N, (1 : ℝ) / y := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => by positivity)
    _ = (harmonic N : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      simp only [div_eq_mul_inv, one_mul]

/-- For odd `M`, the denominators `|2n-M|` split into two injective families of positive
integers, so their reciprocal sum is bounded by two harmonic numbers. -/
theorem sum_inv_abs_two_mul_sub_le_two_harmonic (M : ℕ) (hM : Odd M) :
    ∑ n ∈ Finset.range M, (1 : ℝ) / |(2 : ℝ) * n - M| ≤
      2 * (harmonic M : ℝ) := by
  let L := (Finset.range M).filter (fun n => 2 * n < M)
  let H := (Finset.range M).filter (fun n => M < 2 * n)
  have hne (n : ℕ) : 2 * n ≠ M := by
    rcases hM with ⟨k, hk⟩
    omega
  have hnotL : (Finset.range M).filter (fun n => ¬2 * n < M) = H := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, H]
    constructor
    · rintro ⟨hnM, hn⟩
      exact ⟨hnM, lt_of_le_of_ne (Nat.le_of_not_gt hn) (Ne.symm (hne n))⟩
    · rintro ⟨hnM, hn⟩
      exact ⟨hnM, Nat.not_lt.mpr hn.le⟩
  have hpartition :
      (∑ n ∈ Finset.range M, (1 : ℝ) / |(2 : ℝ) * n - M|) =
        (∑ n ∈ L, (1 : ℝ) / |(2 : ℝ) * n - M|) +
          ∑ n ∈ H, (1 : ℝ) / |(2 : ℝ) * n - M| := by
    have hs := Finset.sum_filter_add_sum_filter_not (Finset.range M)
      (fun n => 2 * n < M) (fun n => (1 : ℝ) / |(2 : ℝ) * n - M|)
    rw [hnotL] at hs
    exact hs.symm
  have hL : (∑ n ∈ L, (1 : ℝ) / |(2 : ℝ) * n - M|) ≤ (harmonic M : ℝ) := by
    calc
      (∑ n ∈ L, (1 : ℝ) / |(2 : ℝ) * n - M|) =
          ∑ n ∈ L, (1 : ℝ) / ((M - 2 * n : ℕ) : ℝ) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hlt : 2 * n < M := (Finset.mem_filter.mp hn).2
        have hneg : (2 : ℝ) * n - M < 0 := by
          apply sub_neg.mpr
          exact_mod_cast hlt
        rw [abs_of_neg hneg]
        rw [Nat.cast_sub (Nat.le_of_lt hlt)]
        norm_num
      _ ≤ (harmonic M : ℝ) := by
        apply sum_inv_nat_le_harmonic_of_injOn
        · intro n hn m hm heq
          change M - 2 * n = M - 2 * m at heq
          have hnlt : 2 * n < M := (Finset.mem_filter.mp hn).2
          have hmlt : 2 * m < M := (Finset.mem_filter.mp hm).2
          have hnsub : M - 2 * n + 2 * n = M := Nat.sub_add_cancel hnlt.le
          have hmsub : M - 2 * m + 2 * m = M := Nat.sub_add_cancel hmlt.le
          omega
        · intro n hn
          have hnlt : 2 * n < M := (Finset.mem_filter.mp hn).2
          simp only [Finset.mem_Icc]
          omega
  have hH : (∑ n ∈ H, (1 : ℝ) / |(2 : ℝ) * n - M|) ≤ (harmonic M : ℝ) := by
    calc
      (∑ n ∈ H, (1 : ℝ) / |(2 : ℝ) * n - M|) =
          ∑ n ∈ H, (1 : ℝ) / ((2 * n - M : ℕ) : ℝ) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hlt : M < 2 * n := (Finset.mem_filter.mp hn).2
        have hpos : 0 < (2 : ℝ) * n - M := by
          apply sub_pos.mpr
          exact_mod_cast hlt
        rw [abs_of_pos hpos]
        rw [Nat.cast_sub hlt.le]
        norm_num
      _ ≤ (harmonic M : ℝ) := by
        apply sum_inv_nat_le_harmonic_of_injOn
        · intro n hn m hm heq
          change 2 * n - M = 2 * m - M at heq
          have hnlt : M < 2 * n := (Finset.mem_filter.mp hn).2
          have hmlt : M < 2 * m := (Finset.mem_filter.mp hm).2
          have hnsub : M + (2 * n - M) = 2 * n := Nat.add_sub_of_le hnlt.le
          have hmsub : M + (2 * m - M) = 2 * m := Nat.add_sub_of_le hmlt.le
          omega
        · intro n hn
          have hnM : n < M := Finset.mem_range.mp (Finset.mem_filter.mp hn).1
          have hnlt : M < 2 * n := (Finset.mem_filter.mp hn).2
          simp only [Finset.mem_Icc]
          omega
  rw [hpartition]
  linarith

/-- Reindex the multiples of `d` below `d*N` by their quotient. -/
theorem sum_filter_range_dvd_eq {R : Type*} [AddCommMonoid R] (f : ℕ → R)
    (d N : ℕ) (hd : 0 < d) :
    (∑ n ∈ (Finset.range (d * N)).filter (fun n => d ∣ n), f n) =
      ∑ u ∈ Finset.range N, f (d * u) := by
  symm
  apply Finset.sum_bij (fun u _ => d * u)
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.mul_lt_mul_of_pos_left (Finset.mem_range.mp hu) hd, dvd_mul_right d u⟩
  · intro u hu v hv huv
    exact Nat.eq_of_mul_eq_mul_left hd huv
  · intro n hn
    obtain ⟨hnrange, hndvd⟩ := Finset.mem_filter.mp hn
    obtain ⟨u, rfl⟩ := hndvd
    refine ⟨u, Finset.mem_range.mpr ?_, rfl⟩
    exact Nat.lt_of_mul_lt_mul_left (Finset.mem_range.mp hnrange)
  · intro u hu
    rfl

/-- The odd harmonic denominators modulo `3^b` have total weight at most `4(b+1)`. -/
theorem sum_inv_abs_three_pow_le (b : ℕ) :
    ∑ n ∈ Finset.range (3 ^ b),
        (1 : ℝ) / |(2 : ℝ) * n - ((3 ^ b : ℕ) : ℝ)| ≤ 4 * (b + 1) := by
  calc
    _ ≤ 2 * (harmonic (3 ^ b) : ℝ) :=
      sum_inv_abs_two_mul_sub_le_two_harmonic (3 ^ b) ((show Odd 3 by norm_num).pow)
    _ ≤ 4 * (b + 1) := by
      have hh := harmonic_le_one_add_log (3 ^ b)
      have hlog3 : Real.log (3 : ℝ) ≤ 2 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
        norm_num at this ⊢
        exact this
      have hlogpow : Real.log ((3 ^ b : ℕ) : ℝ) ≤ 2 * b := by
        rw [show (((3 ^ b : ℕ) : ℝ)) = (3 : ℝ) ^ b by norm_num, Real.log_pow]
        have hb : (0 : ℝ) ≤ b := by positivity
        nlinarith
      norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hh hlogpow
      have hh' : (harmonic (3 ^ b) : ℝ) ≤ 1 + 2 * (b : ℝ) := by
        exact hh.trans (by simpa [add_comm] using add_le_add_left hlogpow 1)
      nlinarith

/-- The complete family of parity Fourier weights has total mass at most `4(a+1)`. -/
theorem sum_norm_gHatZ_le (a : ℕ) :
    (∑ ξ : ZMod (3 ^ a), ‖gHatZ a ξ‖) ≤ 4 * (a + 1) := by
  calc
    (∑ ξ : ZMod (3 ^ a), ‖gHatZ a ξ‖) =
        ∑ n ∈ Finset.range (3 ^ a), ‖gHatZ a (n : ZMod (3 ^ a))‖ := by
      rw [sum_zmod_eq_sum_range]
    _ ≤ ∑ n ∈ Finset.range (3 ^ a),
        (1 : ℝ) / |(2 : ℝ) * n - ((3 ^ a : ℕ) : ℝ)| := by
      apply Finset.sum_le_sum
      intro n hn
      have hnlt : n < 3 ^ a := Finset.mem_range.mp hn
      simpa [ZMod.val_natCast_of_lt hnlt] using
        norm_gHatZ_le_inv_abs a (n : ZMod (3 ^ a))
    _ ≤ 4 * (a + 1) := sum_inv_abs_three_pow_le a

/-- Frequencies divisible by `3^K` carry at most a `3^(-K)` fraction of the total harmonic
weight, uniformly in the ambient modulus. -/
theorem sum_norm_gHatZ_dvd_le (a K : ℕ) (hKa : K ≤ a) :
    (∑ ξ : ZMod (3 ^ a), if 3 ^ K ∣ ξ.val then ‖gHatZ a ξ‖ else 0) ≤
      ((3 : ℝ) ^ K)⁻¹ * (4 * (a + 1)) := by
  let d := 3 ^ K
  let N := 3 ^ (a - K)
  have hd : 0 < d := by positivity
  have hNodd : Odd N := by
    exact (show Odd 3 by norm_num).pow
  have hpow : 3 ^ a = d * N := by
    dsimp [d, N]
    rw [← pow_add, Nat.add_sub_of_le hKa]
  have hreindex :
      (∑ ξ : ZMod (3 ^ a), if d ∣ ξ.val then ‖gHatZ a ξ‖ else 0) =
        ∑ n ∈ Finset.range (3 ^ a),
          if d ∣ n then ‖gHatZ a (n : ZMod (3 ^ a))‖ else 0 := by
    rw [sum_zmod_eq_sum_range]
    apply Finset.sum_congr rfl
    intro n hn
    rw [ZMod.val_natCast_of_lt (Finset.mem_range.mp hn)]
  change (∑ ξ : ZMod (3 ^ a), if d ∣ ξ.val then ‖gHatZ a ξ‖ else 0) ≤ _
  rw [hreindex, ← Finset.sum_filter]
  calc
    (∑ n ∈ (Finset.range (3 ^ a)).filter (fun n => d ∣ n),
        ‖gHatZ a (n : ZMod (3 ^ a))‖) ≤
        ∑ n ∈ (Finset.range (3 ^ a)).filter (fun n => d ∣ n),
          (1 : ℝ) / |(2 : ℝ) * n - ((3 ^ a : ℕ) : ℝ)| := by
      apply Finset.sum_le_sum
      intro n hn
      have hnlt : n < 3 ^ a := Finset.mem_range.mp (Finset.mem_filter.mp hn).1
      simpa [ZMod.val_natCast_of_lt hnlt] using
        norm_gHatZ_le_inv_abs a (n : ZMod (3 ^ a))
    _ = ∑ u ∈ Finset.range N,
          (1 : ℝ) / |(2 : ℝ) * (d * u) - ((d * N : ℕ) : ℝ)| := by
      rw [hpow, sum_filter_range_dvd_eq _ d N hd]
      simp only [Nat.cast_mul]
    _ = ((d : ℕ) : ℝ)⁻¹ *
          ∑ u ∈ Finset.range N, (1 : ℝ) / |(2 : ℝ) * u - N| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      have hdR : (0 : ℝ) < d := by exact_mod_cast hd
      have hneNat : 2 * u ≠ N := by
        rcases hNodd with ⟨k, hk⟩
        omega
      have hneR : (2 : ℝ) * u - N ≠ 0 := by
        apply sub_ne_zero.mpr
        exact_mod_cast hneNat
      rw [show (2 : ℝ) * (d * u) - ((d * N : ℕ) : ℝ) =
          (d : ℝ) * ((2 : ℝ) * u - N) by push_cast; ring]
      rw [abs_mul, abs_of_pos hdR]
      field_simp [hdR.ne', hneR]
    _ ≤ ((d : ℕ) : ℝ)⁻¹ * (4 * (((a - K) + 1 : ℕ) : ℝ)) := by
      apply mul_le_mul_of_nonneg_left
      · simpa [N] using sum_inv_abs_three_pow_le (a - K)
      · positivity
    _ ≤ ((3 : ℝ) ^ K)⁻¹ * (4 * (a + 1)) := by
      norm_num only [d, Nat.cast_pow, Nat.cast_ofNat]
      have hsub : a - K + 1 ≤ a + 1 := Nat.add_le_add_right (Nat.sub_le a K) 1
      have hsubR : (((a - K) + 1 : ℕ) : ℝ) ≤ (a : ℝ) + 1 := by
        exact_mod_cast hsub
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsubR (by norm_num)) (by positivity)

/-- **Edge: slice character decay gives C1 directly** (no fine-scale mixing, no Tao §6).  Proof owed,
plan in the module docstring.  With `sliceCharDecay_of_pascalDampingDecay` (SliceSeven.lean) this
makes `BiasDecays` follow from `PascalDampingDecay` alone.  Confidence 75%. -/
theorem biasDecays_of_sliceCharDecay (h : SliceCharDecay) : BiasDecays := by
  sorry

end CollatzMoonshot.Conjugacy
