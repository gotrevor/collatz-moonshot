/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalContinuousReversor
import CollatzMoonshot.FrontA.PowSeparation

/-!
# Escape: a non-periodic orbit cannot spend too many bits

Each step of `U` multiplies by `3` and divides by `2^b`, where `b = stepBits` is `1` on the
even branch and `2` on the odd ones, up to an additive `±1`.  A non-periodic orbit of the
permutation `U` consists of distinct integers, so it leaves every bounded set; hence it cannot
spend more than `log₂ 3` bits per step forever, or it would shrink to `0`
(`escape_forward`).  Backward, `U⁻¹` multiplies by `2^b / 3`, so a non-periodic backward
orbit spends at least `log₂ 3` bits per step infinitely often (`escape_backward`).

**Theorem N** (agent report `q1.md`, 2026-10-13).  A reversor `ι` (`ι ∘ U = U⁻¹ ∘ ι`) carries
the backward itinerary of `n` to the forward itinerary of `ι n`.  If `ι` is determined by
residues, the even steps of `ι n` are read off `n`'s backward itinerary by a sliding block code
`f`, and every bijective such `ι` has a *balanced* `f` (Lemma S(b) and Hedlund's theorem on
surjective cellular automata; not yet in Lean).  If the backward itinerary of a single
non-periodic integer is normal, a balanced code gives the forward orbit of `ι n` even-step
frequency `1/3`, i.e. `5/3 > log₂ 3` bits per step, so `ι n` is periodic by escape, and then so
is `n` by injectivity.  So `AmusicalNoContinuousReversor` reduces to normality of one integer's
backward itinerary (`not_reversor_of_backwardNormal`); this is where `2 ≠ 3` enters, since a
balanced code outputs the uniform law, never the dyadic law `(1/2, 1/4, 1/4)`.

The normality hypothesis is open for every integer (it is a Collatz-type typicality statement),
so this is a reduction, not a proof.  Paper proofs: `q1.md` §2–§3.  Treadmill target
(`KICKOFF-2026-10-13-amusical-escape.md`): close every `sorry` here.
-/

namespace CollatzMoonshot.Amusical

/-- The number of halvings in the step of `U` at `n`: `1` if `n` is even, else `2`. -/
def stepBits (n : ℤ) : ℕ :=
  if n % 2 = 0 then 1 else 2

/-- The bits spent by the first `k` forward steps from `m`. -/
def fwdBits (m : ℤ) (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range k, stepBits (amusical^[j] m)

/-- The bits spent by the first `k` backward steps from `m`, landing on `U⁻¹ m, …, U⁻ᵏ m`. -/
def bwdBits (m : ℤ) (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range k, stepBits (amusicalInv^[j + 1] m)

/-- The forward branch bound `|U x| ≤ (3|x| + 1) / 2^b`. -/
theorem abs_amusical_le (x : ℤ) : 2 ^ stepBits x * |amusical x| ≤ 3 * |x| + 1 := by
  unfold stepBits amusical
  split_ifs <;> norm_num <;> rcases abs_cases x with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only [h1] <;>
    (try rw [abs_of_nonneg (by omega)]) <;> (try rw [abs_of_neg (by omega)]) <;> omega

/-- The backward branch bound `|U⁻¹ x| ≤ (2^b |x| + 1) / 3`, with `b` the bits of `U⁻¹ x`. -/
theorem abs_amusicalInv_le (x : ℤ) :
    3 * |amusicalInv x| ≤ 2 ^ stepBits (amusicalInv x) * |x| + 1 := by
  unfold stepBits amusicalInv
  split_ifs <;> norm_num <;> rcases abs_cases x with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only [h1] <;>
    (try rw [abs_of_nonneg (by omega)]) <;> (try rw [abs_of_neg (by omega)]) <;> omega

/-- The nonnegative iterates of an injective map through an aperiodic point are distinct. -/
theorem iterate_orbit_injective_of_aperiodic {α : Type*} (f : α → α)
    (hf : Function.Injective f) (x : α) (hx : ∀ k ≥ 1, f^[k] x ≠ x) :
    Function.Injective fun k : ℕ => f^[k] x := by
  intro i j hij
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · apply hx (j - i) (by omega)
    apply (hf.iterate i)
    rw [← Function.iterate_add_apply, Nat.add_sub_of_le hlt.le]
    exact hij.symm
  · apply hx (i - j) (by omega)
    apply (hf.iterate j)
    rw [← Function.iterate_add_apply, Nat.add_sub_of_le hgt.le]
    exact hij

/-- An injective integer sequence eventually leaves every bounded interval. -/
theorem eventually_abs_ge_of_injective (u : ℕ → ℤ) (hu : Function.Injective u) (X : ℕ) :
    ∀ᶠ k in Filter.atTop, (X : ℤ) ≤ |u k| := by
  have hsmall : ({z : ℤ | |z| < (X : ℤ)} : Set ℤ).Finite := by
    apply (Set.finite_Icc (-(X : ℤ)) (X : ℤ)).subset
    intro z hz
    change |z| < (X : ℤ) at hz
    change -(X : ℤ) ≤ z ∧ z ≤ (X : ℤ)
    rw [abs_lt] at hz
    exact ⟨hz.1.le, hz.2.le⟩
  have hpre : (u ⁻¹' {z : ℤ | |z| < (X : ℤ)}).Finite :=
    hsmall.preimage hu.injOn
  rw [← Nat.cofinite_eq_atTop, Filter.eventually_cofinite]
  simp only [not_le]
  change ({k : ℕ | |u k| < (X : ℤ)} : Set ℕ).Finite
  exact hpre

/-- A large absolute-value threshold makes both affine errors logarithmically negligible. -/
theorem exists_escape_threshold (δ : ℝ) (hδ : 0 < δ) :
    ∃ X : ℕ, 1 ≤ X ∧
      Real.logb 2 (3 + 1 / (X : ℝ)) < Real.logb 2 3 + δ / 2 ∧
      Real.logb 2 (1 + (1 / 2 : ℝ) * (1 / X)) < δ / 2 := by
  have hinv : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
      Filter.atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hforwardArg : Filter.Tendsto (fun n : ℕ => (3 : ℝ) + 1 / ((n : ℝ) + 1))
      Filter.atTop (nhds 3) := by
    simpa using (tendsto_const_nhds.add hinv : Filter.Tendsto
      (fun n : ℕ => (3 : ℝ) + 1 / ((n : ℝ) + 1)) Filter.atTop (nhds (3 + 0)))
  have hbackwardArg : Filter.Tendsto
      (fun n : ℕ => (1 : ℝ) + (1 / 2) * (1 / ((n : ℝ) + 1)))
      Filter.atTop (nhds 1) := by
    have hhalf : Filter.Tendsto
      (fun n : ℕ => (1 / 2 : ℝ) * (1 / ((n : ℝ) + 1)))
      Filter.atTop (nhds 0) := by
      simpa using (tendsto_const_nhds.mul hinv : Filter.Tendsto
        (fun n : ℕ => (1 / 2 : ℝ) * (1 / ((n : ℝ) + 1)))
        Filter.atTop (nhds ((1 / 2 : ℝ) * 0)))
    simpa using (tendsto_const_nhds.add hhalf : Filter.Tendsto
      (fun n : ℕ => (1 : ℝ) + (1 / 2) * (1 / ((n : ℝ) + 1)))
      Filter.atTop (nhds (1 + 0)))
  have hforward : Filter.Tendsto
      (fun n : ℕ => Real.logb 2 (3 + 1 / ((n : ℝ) + 1)))
      Filter.atTop (nhds (Real.logb 2 3)) :=
    (Real.continuousAt_logb (b := 2) (x := 3) (by norm_num)).tendsto.comp hforwardArg
  have hbackward : Filter.Tendsto
      (fun n : ℕ => Real.logb 2 (1 + (1 / 2) * (1 / ((n : ℝ) + 1))))
      Filter.atTop (nhds 0) := by
    simpa only [Function.comp_def, Real.logb_one] using
      (Real.continuousAt_logb (b := 2) (x := 1) (by norm_num)).tendsto.comp hbackwardArg
  have hevForward : ∀ᶠ n : ℕ in Filter.atTop,
      Real.logb 2 (3 + 1 / ((n : ℝ) + 1)) < Real.logb 2 3 + δ / 2 := by
    exact hforward (Iio_mem_nhds (by linarith))
  have hevBackward : ∀ᶠ n : ℕ in Filter.atTop,
      Real.logb 2 (1 + (1 / 2) * (1 / ((n : ℝ) + 1))) < δ / 2 := by
    exact hbackward (Iio_mem_nhds (by linarith))
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.1 (hevForward.and hevBackward)
  have hn' := hn n le_rfl
  refine ⟨n + 1, by omega, ?_, ?_⟩
  · simpa only [Nat.cast_add, Nat.cast_one] using hn'.1
  · simpa only [Nat.cast_add, Nat.cast_one] using hn'.2

/-- Above a fixed threshold, one forward step satisfies the logarithmic bit ledger. -/
theorem forward_log_ledger_step (x : ℤ) (X : ℕ) (hX : 1 ≤ X) (hx : (X : ℤ) ≤ |x|) :
    Real.logb 2 |(amusical x : ℝ)| + stepBits x ≤
      Real.logb 2 |(x : ℝ)| + Real.logb 2 (3 + 1 / (X : ℝ)) := by
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    simp at hx
    omega
  have hzero : amusical 0 = 0 := by norm_num [amusical]
  have hnext0 : amusical x ≠ 0 := by
    intro h
    apply hx0
    apply amusical_injective
    rw [h, hzero]
  have hxpos : (0 : ℝ) < |(x : ℝ)| := abs_pos.mpr (by exact_mod_cast hx0)
  have hnextpos : (0 : ℝ) < |(amusical x : ℝ)| :=
    abs_pos.mpr (by exact_mod_cast hnext0)
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hxR : (X : ℝ) ≤ |(x : ℝ)| := by exact_mod_cast hx
  have hinv : (1 : ℝ) ≤ (1 / X) * |(x : ℝ)| := by
    rw [one_div_mul_eq_div, le_div_iff₀ hXR]
    simpa [mul_comm] using hxR
  have hbound : (2 : ℝ) ^ stepBits x * |(amusical x : ℝ)| ≤
      3 * |(x : ℝ)| + 1 := by
    exact_mod_cast abs_amusical_le x
  have hfactor : (2 : ℝ) ^ stepBits x * |(amusical x : ℝ)| ≤
      (3 + 1 / (X : ℝ)) * |(x : ℝ)| := by
    calc
      _ ≤ 3 * |(x : ℝ)| + 1 := hbound
      _ ≤ (3 + 1 / (X : ℝ)) * |(x : ℝ)| := by
        rw [add_mul]
        linarith
  have hfactorPos : (0 : ℝ) < 3 + 1 / (X : ℝ) := by positivity
  have hlog := (Real.logb_le_logb (b := 2) (by norm_num)
    (mul_pos (pow_pos (by norm_num) _) hnextpos) (mul_pos hfactorPos hxpos)).2 hfactor
  calc
    Real.logb 2 |(amusical x : ℝ)| + stepBits x =
        Real.logb 2 ((2 : ℝ) ^ stepBits x * |(amusical x : ℝ)|) := by
      rw [Real.logb_mul (pow_ne_zero _ (by norm_num)) hnextpos.ne', Real.logb_pow,
        Real.logb_self_eq_one (by norm_num)]
      ring
    _ ≤ Real.logb 2 ((3 + 1 / (X : ℝ)) * |(x : ℝ)|) := hlog
    _ = Real.logb 2 |(x : ℝ)| + Real.logb 2 (3 + 1 / (X : ℝ)) := by
      rw [Real.logb_mul hfactorPos.ne' hxpos.ne']
      ring

theorem fwdBits_succ (m : ℤ) (k : ℕ) :
    fwdBits m (k + 1) = fwdBits m k + stepBits (amusical^[k] m) := by
  simp [fwdBits, Finset.sum_range_succ]

/-- The forward logarithmic ledger telescopes along any large orbit tail. -/
theorem forward_log_ledger_from (m : ℤ) (X J n : ℕ) (hX : 1 ≤ X)
    (hlarge : ∀ j ≥ J, (X : ℤ) ≤ |amusical^[j] m|) :
    Real.logb 2 |(amusical^[J + n] m : ℝ)| + (fwdBits m (J + n) : ℝ) ≤
      Real.logb 2 |(amusical^[J] m : ℝ)| + (fwdBits m J : ℝ) +
        n * Real.logb 2 (3 + 1 / (X : ℝ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hs := forward_log_ledger_step (amusical^[J + n] m) X hX
        (hlarge (J + n) (by omega))
      calc
        Real.logb 2 |(amusical^[J + (n + 1)] m : ℝ)| +
            (fwdBits m (J + (n + 1)) : ℝ) =
            (Real.logb 2 |(amusical (amusical^[J + n] m) : ℝ)| +
              stepBits (amusical^[J + n] m)) + (fwdBits m (J + n) : ℝ) := by
          rw [show J + (n + 1) = (J + n) + 1 by omega,
            Function.iterate_succ_apply', fwdBits_succ]
          push_cast
          ring
        _ ≤ (Real.logb 2 |(amusical^[J + n] m : ℝ)| +
              Real.logb 2 (3 + 1 / (X : ℝ))) + (fwdBits m (J + n) : ℝ) :=
          add_le_add_left hs _
        _ = (Real.logb 2 |(amusical^[J + n] m : ℝ)| +
              (fwdBits m (J + n) : ℝ)) + Real.logb 2 (3 + 1 / (X : ℝ)) := by ring
        _ ≤ (Real.logb 2 |(amusical^[J] m : ℝ)| + (fwdBits m J : ℝ) +
              n * Real.logb 2 (3 + 1 / (X : ℝ))) +
              Real.logb 2 (3 + 1 / (X : ℝ)) := add_le_add_left ih _
        _ = Real.logb 2 |(amusical^[J] m : ℝ)| + (fwdBits m J : ℝ) +
              ((n + 1 : ℕ) : ℝ) * Real.logb 2 (3 + 1 / (X : ℝ)) := by
          rw [Nat.cast_add, Nat.cast_one]
          ring

/-- **Target (Lemma E).**  A non-periodic forward orbit spends at most `log₂ 3 + δ` bits per
step infinitely often. -/
theorem escape_forward (m : ℤ) (hm : ∀ k ≥ 1, amusical^[k] m ≠ m) (δ : ℝ) (hδ : 0 < δ)
    (K : ℕ) : ∃ k ≥ K, (fwdBits m k : ℝ) ≤ (Real.logb 2 3 + δ) * k := by
  by_contra hcontra
  push Not at hcontra
  obtain ⟨X, hX, hforward, _⟩ := exists_escape_threshold δ hδ
  have horbit := iterate_orbit_injective_of_aperiodic amusical amusical_injective m hm
  obtain ⟨J₀, hJ₀⟩ := Filter.eventually_atTop.1
    (eventually_abs_ge_of_injective (fun j => amusical^[j] m) horbit X)
  let J := max K J₀
  have hKJ : K ≤ J := le_max_left _ _
  have hJ₀J : J₀ ≤ J := le_max_right _ _
  have hlarge : ∀ j ≥ J, (X : ℤ) ≤ |amusical^[j] m| := by
    intro j hj
    exact hJ₀ j (hJ₀J.trans hj)
  let theta := Real.logb 2 3
  let c := Real.logb 2 (3 + 1 / (X : ℝ))
  let A := Real.logb 2 |(amusical^[J] m : ℝ)| + (fwdBits m J : ℝ)
  let C := A - (theta + δ) * (J : ℝ)
  have hc : c < theta + δ / 2 := by simpa [c, theta] using hforward
  have hδ2 : 0 < δ / 2 := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (C / (δ / 2))
  have hnC : C < (n : ℝ) * (δ / 2) := (div_lt_iff₀ hδ2).mp hn
  have hmul : (n : ℝ) * c ≤ (n : ℝ) * (theta + δ / 2) :=
    mul_le_mul_of_nonneg_left hc.le (Nat.cast_nonneg n)
  have hupper : A + (n : ℝ) * c < (theta + δ) * ((J + n : ℕ) : ℝ) := by
    calc
      A + (n : ℝ) * c ≤ A + (n : ℝ) * (theta + δ / 2) := add_le_add_right hmul A
      _ = (theta + δ) * ((J + n : ℕ) : ℝ) + (C - (n : ℝ) * (δ / 2)) := by
        dsimp [C]
        push_cast
        ring
      _ < (theta + δ) * ((J + n : ℕ) : ℝ) := by linarith only [hnC]
  have hled := forward_log_ledger_from m X J n hX hlarge
  have hled' : Real.logb 2 |(amusical^[J + n] m : ℝ)| +
      (fwdBits m (J + n) : ℝ) ≤ A + (n : ℝ) * c := by
    simpa only [A, c] using hled
  have hbits : (theta + δ) * ((J + n : ℕ) : ℝ) < (fwdBits m (J + n) : ℝ) := by
    simpa only [theta] using hcontra (J + n) (hKJ.trans (Nat.le_add_right J n))
  have habsZ : (1 : ℤ) ≤ |amusical^[J + n] m| := by
    have hOneX : (1 : ℤ) ≤ X := by exact_mod_cast hX
    exact hOneX.trans (hlarge (J + n) (Nat.le_add_right J n))
  have habsR : (1 : ℝ) ≤ |(amusical^[J + n] m : ℝ)| := by exact_mod_cast habsZ
  have hlog : 0 ≤ Real.logb 2 |(amusical^[J + n] m : ℝ)| :=
    Real.logb_nonneg (by norm_num) habsR
  have hlt : Real.logb 2 |(amusical^[J + n] m : ℝ)| +
      (fwdBits m (J + n) : ℝ) < (fwdBits m (J + n) : ℝ) :=
    hled'.trans_lt (hupper.trans hbits)
  linarith only [hlog, hlt]

theorem amusicalInv_injective : Function.Injective amusicalInv := by
  intro x y h
  have hi := congrArg amusical h
  simpa only [amusical_amusicalInv] using hi

/-- Above a fixed threshold, one backward step satisfies the logarithmic bit ledger. -/
theorem backward_log_ledger_step (x : ℤ) (X : ℕ) (hX : 1 ≤ X) (hx : (X : ℤ) ≤ |x|) :
    Real.logb 2 |(amusicalInv x : ℝ)| + Real.logb 2 3 ≤
      Real.logb 2 |(x : ℝ)| + stepBits (amusicalInv x) +
        Real.logb 2 (1 + (1 / 2 : ℝ) * (1 / X)) := by
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    simp at hx
    omega
  have hzero : amusicalInv 0 = 0 := by norm_num [amusicalInv]
  have hnext0 : amusicalInv x ≠ 0 := by
    intro h
    apply hx0
    apply amusicalInv_injective
    rw [h, hzero]
  have hxpos : (0 : ℝ) < |(x : ℝ)| := abs_pos.mpr (by exact_mod_cast hx0)
  have hnextpos : (0 : ℝ) < |(amusicalInv x : ℝ)| :=
    abs_pos.mpr (by exact_mod_cast hnext0)
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hxR : (X : ℝ) ≤ |(x : ℝ)| := by exact_mod_cast hx
  have hinv : (1 : ℝ) ≤ (1 / X) * |(x : ℝ)| := by
    rw [one_div_mul_eq_div, le_div_iff₀ hXR]
    simpa [mul_comm] using hxR
  have hpow : (2 : ℝ) ≤ 2 ^ stepBits (amusicalInv x) := by
    unfold stepBits
    split_ifs <;> norm_num
  have hhalf : (1 : ℝ) ≤ (2 : ℝ) ^ stepBits (amusicalInv x) * (1 / 2) := by
    nlinarith only [hpow]
  have hextra : (1 : ℝ) ≤
      (2 : ℝ) ^ stepBits (amusicalInv x) * ((1 / 2) * (1 / X)) * |(x : ℝ)| := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ ((2 : ℝ) ^ stepBits (amusicalInv x) * (1 / 2)) *
          ((1 / X) * |(x : ℝ)|) :=
        mul_le_mul hhalf hinv (by norm_num) (by positivity)
      _ = (2 : ℝ) ^ stepBits (amusicalInv x) * ((1 / 2) * (1 / X)) *
          |(x : ℝ)| := by ring
  have hbound : (3 : ℝ) * |(amusicalInv x : ℝ)| ≤
      2 ^ stepBits (amusicalInv x) * |(x : ℝ)| + 1 := by
    exact_mod_cast abs_amusicalInv_le x
  have hfactor : (3 : ℝ) * |(amusicalInv x : ℝ)| ≤
      ((2 : ℝ) ^ stepBits (amusicalInv x) * (1 + (1 / 2) * (1 / X))) *
        |(x : ℝ)| := by
    calc
      _ ≤ (2 : ℝ) ^ stepBits (amusicalInv x) * |(x : ℝ)| + 1 := hbound
      _ ≤ (2 : ℝ) ^ stepBits (amusicalInv x) * |(x : ℝ)| +
          (2 : ℝ) ^ stepBits (amusicalInv x) * ((1 / 2) * (1 / X)) *
            |(x : ℝ)| := add_le_add_right hextra _
      _ = ((2 : ℝ) ^ stepBits (amusicalInv x) * (1 + (1 / 2) * (1 / X))) *
          |(x : ℝ)| := by ring
  have hfactorPos : (0 : ℝ) < 1 + (1 / 2 : ℝ) * (1 / X) := by positivity
  have hlog := (Real.logb_le_logb (b := 2) (by norm_num)
    (mul_pos (by norm_num) hnextpos)
    (mul_pos (mul_pos (pow_pos (by norm_num) _) hfactorPos) hxpos)).2 hfactor
  calc
    Real.logb 2 |(amusicalInv x : ℝ)| + Real.logb 2 3 =
        Real.logb 2 ((3 : ℝ) * |(amusicalInv x : ℝ)|) := by
      rw [Real.logb_mul (by norm_num) hnextpos.ne']
      ring
    _ ≤ Real.logb 2 (((2 : ℝ) ^ stepBits (amusicalInv x) *
          (1 + (1 / 2) * (1 / X))) * |(x : ℝ)|) := hlog
    _ = Real.logb 2 |(x : ℝ)| + stepBits (amusicalInv x) +
          Real.logb 2 (1 + (1 / 2 : ℝ) * (1 / X)) := by
      rw [Real.logb_mul
        (mul_ne_zero (pow_ne_zero _ (by norm_num)) hfactorPos.ne') hxpos.ne',
        Real.logb_mul (pow_ne_zero _ (by norm_num)) hfactorPos.ne', Real.logb_pow,
        Real.logb_self_eq_one (by norm_num)]
      ring

theorem bwdBits_succ (m : ℤ) (k : ℕ) :
    bwdBits m (k + 1) = bwdBits m k + stepBits (amusicalInv^[k + 1] m) := by
  simp [bwdBits, Finset.sum_range_succ]

/-- The backward logarithmic ledger telescopes along any large inverse-orbit tail. -/
theorem backward_log_ledger_from (m : ℤ) (X J n : ℕ) (hX : 1 ≤ X)
    (hlarge : ∀ j ≥ J, (X : ℤ) ≤ |amusicalInv^[j] m|) :
    Real.logb 2 |(amusicalInv^[J + n] m : ℝ)| + n * Real.logb 2 3 +
        (bwdBits m J : ℝ) ≤
      Real.logb 2 |(amusicalInv^[J] m : ℝ)| + (bwdBits m (J + n) : ℝ) +
        n * Real.logb 2 (1 + (1 / 2 : ℝ) * (1 / X)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hs := backward_log_ledger_step (amusicalInv^[J + n] m) X hX
        (hlarge (J + n) (by omega))
      calc
        Real.logb 2 |(amusicalInv^[J + (n + 1)] m : ℝ)| +
              ((n + 1 : ℕ) : ℝ) * Real.logb 2 3 + (bwdBits m J : ℝ) =
            (Real.logb 2 |(amusicalInv (amusicalInv^[J + n] m) : ℝ)| +
              Real.logb 2 3) + ((n : ℝ) * Real.logb 2 3 + (bwdBits m J : ℝ)) := by
          rw [show J + (n + 1) = (J + n) + 1 by omega,
            Function.iterate_succ_apply', Nat.cast_add, Nat.cast_one]
          ring
        _ ≤ (Real.logb 2 |(amusicalInv^[J + n] m : ℝ)| +
              stepBits (amusicalInv (amusicalInv^[J + n] m)) +
              Real.logb 2 (1 + (1 / 2 : ℝ) * (1 / X))) +
              ((n : ℝ) * Real.logb 2 3 + (bwdBits m J : ℝ)) :=
          add_le_add_left hs _
        _ = (Real.logb 2 |(amusicalInv^[J + n] m : ℝ)| +
              (n : ℝ) * Real.logb 2 3 + (bwdBits m J : ℝ)) +
              stepBits (amusicalInv^[J + n + 1] m) +
              Real.logb 2 (1 + (1 / 2 : ℝ) * (1 / X)) := by
          rw [Function.iterate_succ_apply']
          ring
        _ ≤ (Real.logb 2 |(amusicalInv^[J] m : ℝ)| +
              (bwdBits m (J + n) : ℝ) +
              (n : ℝ) * Real.logb 2 (1 + (1 / 2 : ℝ) * (1 / X))) +
              stepBits (amusicalInv^[J + n + 1] m) +
              Real.logb 2 (1 + (1 / 2 : ℝ) * (1 / X)) :=
          add_le_add_left (add_le_add_left ih _) _
        _ = Real.logb 2 |(amusicalInv^[J] m : ℝ)| +
              (bwdBits m (J + (n + 1)) : ℝ) +
              ((n + 1 : ℕ) : ℝ) *
                Real.logb 2 (1 + (1 / 2 : ℝ) * (1 / X)) := by
          rw [show J + (n + 1) = (J + n) + 1 by omega, bwdBits_succ,
            Nat.cast_add]
          push_cast
          ring

/-- **Target (Lemma E′).**  A non-periodic backward orbit spends at least `log₂ 3 − δ` bits per
step infinitely often. -/
theorem escape_backward (m : ℤ) (hm : ∀ k ≥ 1, amusical^[k] m ≠ m) (δ : ℝ) (hδ : 0 < δ)
    (K : ℕ) : ∃ k ≥ K, (Real.logb 2 3 - δ) * k ≤ (bwdBits m k : ℝ) := by
  by_contra hcontra
  push Not at hcontra
  obtain ⟨X, hX, _, hbackward⟩ := exists_escape_threshold δ hδ
  have hmInv : ∀ k ≥ 1, amusicalInv^[k] m ≠ m := by
    intro k hk hperiod
    apply hm k hk
    have hi := congrArg (amusical^[k]) hperiod
    rw [amusical_iterate_amusicalInv_iterate] at hi
    exact hi.symm
  have horbit :=
    iterate_orbit_injective_of_aperiodic amusicalInv amusicalInv_injective m hmInv
  obtain ⟨J₀, hJ₀⟩ := Filter.eventually_atTop.1
    (eventually_abs_ge_of_injective (fun j => amusicalInv^[j] m) horbit X)
  let J := max K J₀
  have hKJ : K ≤ J := le_max_left _ _
  have hJ₀J : J₀ ≤ J := le_max_right _ _
  have hlarge : ∀ j ≥ J, (X : ℤ) ≤ |amusicalInv^[j] m| := by
    intro j hj
    exact hJ₀ j (hJ₀J.trans hj)
  let theta := Real.logb 2 3
  let d := Real.logb 2 (1 + (1 / 2 : ℝ) * (1 / X))
  let L := Real.logb 2 |(amusicalInv^[J] m : ℝ)|
  let B := (bwdBits m J : ℝ)
  let C := L - B + (theta - δ) * (J : ℝ)
  have hd : d < δ / 2 := by simpa [d] using hbackward
  have hδ2 : 0 < δ / 2 := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (C / (δ / 2))
  have hnC : C < (n : ℝ) * (δ / 2) := (div_lt_iff₀ hδ2).mp hn
  have hmul : (n : ℝ) * d ≤ (n : ℝ) * (δ / 2) :=
    mul_le_mul_of_nonneg_left hd.le (Nat.cast_nonneg n)
  have hled := backward_log_ledger_from m X J n hX hlarge
  have hled' : Real.logb 2 |(amusicalInv^[J + n] m : ℝ)| +
        (n : ℝ) * theta + B ≤
      L + (bwdBits m (J + n) : ℝ) + (n : ℝ) * d := by
    simpa only [theta, d, L, B] using hled
  have hbits : (bwdBits m (J + n) : ℝ) <
      (theta - δ) * ((J + n : ℕ) : ℝ) := by
    simpa only [theta] using hcontra (J + n) (hKJ.trans (Nat.le_add_right J n))
  have hsum : L + (bwdBits m (J + n) : ℝ) + (n : ℝ) * d <
      L + (theta - δ) * ((J + n : ℕ) : ℝ) + (n : ℝ) * (δ / 2) :=
    add_lt_add_of_lt_of_le (add_lt_add_right hbits L) hmul
  have hcap : L + (theta - δ) * ((J + n : ℕ) : ℝ) + (n : ℝ) * (δ / 2) <
      (n : ℝ) * theta + B := by
    calc
      _ = (n : ℝ) * theta + B + (C - (n : ℝ) * (δ / 2)) := by
        dsimp [C]
        push_cast
        ring
      _ < (n : ℝ) * theta + B := by linarith only [hnC]
  have habsZ : (1 : ℤ) ≤ |amusicalInv^[J + n] m| := by
    have hOneX : (1 : ℤ) ≤ X := by exact_mod_cast hX
    exact hOneX.trans (hlarge (J + n) (Nat.le_add_right J n))
  have habsR : (1 : ℝ) ≤ |(amusicalInv^[J + n] m : ℝ)| := by exact_mod_cast habsZ
  have hlog : 0 ≤ Real.logb 2 |(amusicalInv^[J + n] m : ℝ)| :=
    Real.logb_nonneg (by norm_num) habsR
  have hlt : Real.logb 2 |(amusicalInv^[J + n] m : ℝ)| +
      (n : ℝ) * theta + B < (n : ℝ) * theta + B :=
    hled'.trans_lt (hsum.trans hcap)
  linarith only [hlog, hlt]

private theorem stepBits_add_evenIndicator (x : ℤ) :
    stepBits x + (if stepSym x = 0 then 1 else 0) = 2 := by
  unfold stepBits stepSym
  split_ifs <;> simp_all

private theorem fwdBits_add_evenCount (m : ℤ) (k : ℕ) :
    fwdBits m k + ((Finset.range k).filter fun j => stepSym (amusical^[j] m) = 0).card =
      2 * k := by
  induction k with
  | zero => simp [fwdBits]
  | succ k ih =>
      rw [← Nat.count_eq_card_filter_range] at ih ⊢
      rw [fwdBits, Finset.sum_range_succ, Nat.count_succ]
      rw [fwdBits] at ih
      have hs := stepBits_add_evenIndicator (amusical^[k] m)
      split_ifs at hs ⊢ <;> omega

/-- **Target.**  An orbit whose even steps have limiting frequency `c < 2 − log₂ 3` spends
`2 − c > log₂ 3` bits per step, so it is periodic by `escape_forward`. -/
theorem periodic_of_evenFrequency_lt (m : ℤ) (c : ℝ) (hc : c < 2 - Real.logb 2 3)
    (h : Filter.Tendsto (fun k : ℕ =>
      (((Finset.range k).filter fun j => stepSym (amusical^[j] m) = 0).card : ℝ) / k)
      Filter.atTop (nhds c)) :
    ∃ p ≥ 1, amusical^[p] m = m := by
  by_contra hn
  push Not at hn
  let δ := (2 - c - Real.logb 2 3) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hbits : Filter.Tendsto (fun k : ℕ => (fwdBits m k : ℝ) / k)
      Filter.atTop (nhds (2 - c)) := by
    apply (tendsto_const_nhds.sub h).congr'
    filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    have hid := fwdBits_add_evenCount m k
    have hidR : (fwdBits m k : ℝ) +
        ((Finset.range k).filter fun j => stepSym (amusical^[j] m) = 0).card = 2 * k := by
      exact_mod_cast hid
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    field_simp
    linarith
  have hev : ∀ᶠ k : ℕ in Filter.atTop,
      Real.logb 2 3 + δ < (fwdBits m k : ℝ) / k := by
    have hlim : Real.logb 2 3 + δ = (2 - c) - δ := by dsimp [δ]; ring
    apply hbits.eventually
    apply lt_mem_nhds
    rw [hlim]
    linarith
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 hev
  obtain ⟨k, hkK, hk⟩ := escape_forward m hn δ hδ (max K 1)
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (le_trans (le_max_right _ _) hkK)
  have hlow := hK k (le_trans (le_max_left _ _) hkK)
  rw [lt_div_iff₀ hkpos] at hlow
  exact (not_lt_of_ge hk) hlow

/-- **Target (Theorem N, core).**  No injective reversor sends a non-periodic `n` to a point
whose even steps have limiting frequency `c < 2 − log₂ 3`.  Paper proof: `ι (U⁻ʲ n) = Uʲ (ι n)`,
so `ι n` is periodic by `periodic_of_evenFrequency_lt`, say `Uᵖ (ι n) = ι n`; then
`ι (U⁻ᵖ n) = ι n`, so `U⁻ᵖ n = n` by injectivity, so `Uᵖ n = n`. -/
theorem not_reversor_of_evenFrequency_lt {ι : ℤ → ℤ} (hrev : IsAmusicalReversor ι)
    (hinj : Function.Injective ι) (n : ℤ) (hn : ∀ k ≥ 1, amusical^[k] n ≠ n) (c : ℝ)
    (hc : c < 2 - Real.logb 2 3)
    (hfreq : Filter.Tendsto (fun k : ℕ =>
      (((Finset.range k).filter fun j => stepSym (ι (amusicalInv^[j] n)) = 0).card : ℝ) / k)
      Filter.atTop (nhds c)) : False := by
  have hback (x : ℤ) : ι (amusicalInv x) = amusical (ι x) := by
    calc
      ι (amusicalInv x) = amusical (amusicalInv (ι (amusicalInv x))) :=
        (amusical_amusicalInv _).symm
      _ = amusical (ι (amusical (amusicalInv x))) := by rw [hrev]
      _ = amusical (ι x) := by rw [amusical_amusicalInv]
  have hiter : ∀ j : ℕ, ι (amusicalInv^[j] n) = amusical^[j] (ι n) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        rw [Function.iterate_succ_apply', hback, ih]
        exact (Function.iterate_succ_apply' _ _ _).symm
  obtain ⟨p, hp1, hp⟩ := periodic_of_evenFrequency_lt (ι n) c hc
    (by simpa only [hiter] using hfreq)
  apply hn p hp1
  have hbi : amusicalInv^[p] n = n := by
    apply hinj
    rw [hiter, hp]
  have hi := congrArg (amusical^[p]) hbi
  rw [amusical_iterate_amusicalInv_iterate] at hi
  exact hi.symm

/-- The backward itinerary of `n` is *normal*: each block `b` of length `w` occurs as
`stepSym (U⁻ʲ⁻¹ n), …, stepSym (U⁻ʲ⁻ʷ n)` with limiting frequency `3⁻ʷ`.  Open for every
integer; `3`-adic-Haar-almost every point of `ℤ₃` has it. -/
def BackwardNormal (n : ℤ) : Prop :=
  ∀ (w : ℕ) (b : Fin w → Fin 3), Filter.Tendsto (fun k : ℕ =>
    (((Finset.range k).filter fun j =>
      ∀ i : Fin w, stepSym (amusicalInv^[j + 1 + i] n) = b i).card : ℝ) / k)
    Filter.atTop (nhds ((3 : ℝ)⁻¹ ^ w))

/-- **Target (Theorem N, bridge).**  A balanced sliding block code `f` (a third of the blocks
map to `0`) reading a normal backward itinerary outputs `0` with limiting frequency `1/3`.
Paper proof: the frequency is `∑ b ∈ f⁻¹(0), 3⁻ʷ = 3^(w−1) · 3⁻ʷ`; the first `s` terms do not
affect the limit. -/
theorem evenFrequency_of_backwardNormal (ι : ℤ → ℤ) (n : ℤ) (hn : BackwardNormal n)
    (s w : ℕ) (hw : 1 ≤ w) (f : (Fin w → Fin 3) → Fin 3)
    (hf : ∀ j ≥ s, stepSym (ι (amusicalInv^[j] n)) =
      f (fun i => stepSym (amusicalInv^[j - s + 1 + i] n)))
    (hbal : (Finset.univ.filter fun b => f b = 0).card = 3 ^ (w - 1)) :
    Filter.Tendsto (fun k : ℕ =>
      (((Finset.range k).filter fun j => stepSym (ι (amusicalInv^[j] n)) = 0).card : ℝ) / k)
      Filter.atTop (nhds (1 / 3)) := by
  let block : ℕ → (Fin w → Fin 3) :=
    fun j i => stepSym (amusicalInv^[j + 1 + i] n)
  let good : Finset (Fin w → Fin 3) := Finset.univ.filter fun b => f b = 0
  have hcount (k : ℕ) :
      Nat.count (fun j => f (block j) = 0) k =
        ∑ b ∈ good, Nat.count (fun j => ∀ i, block j i = b i) k := by
    rw [Nat.count_eq_card_filter_range]
    rw [Finset.card_eq_sum_card_fiberwise
      (s := (Finset.range k).filter fun j => f (block j) = 0)
      (t := good) (f := block) (by
        intro j hj
        have hj' : j ∈ Finset.range k ∧ f (block j) = 0 := Finset.mem_filter.mp hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'.2⟩)]
    apply Finset.sum_congr rfl
    intro b hb
    rw [Nat.count_eq_card_filter_range]
    congr 1
    ext j
    have hfb : f b = 0 := by simpa [good] using hb
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨hjk, _⟩, hjb⟩
      exact ⟨hjk, fun i => congrFun hjb i⟩
    · rintro ⟨hjk, hjb⟩
      have heq : block j = b := funext hjb
      exact ⟨⟨hjk, by rw [heq, hfb]⟩, heq⟩
  have hblocks : Filter.Tendsto (fun k : ℕ =>
      ∑ b ∈ good, (Nat.count (fun j => ∀ i, block j i = b i) k : ℝ) / k)
      Filter.atTop (nhds (∑ _b ∈ good, (3 : ℝ)⁻¹ ^ w)) := by
    apply tendsto_finsetSum good
    intro b hb
    simpa only [block, Nat.count_eq_card_filter_range] using hn w b
  have hgood : Filter.Tendsto (fun k : ℕ =>
      (Nat.count (fun j => f (block j) = 0) k : ℝ) / k)
      Filter.atTop (nhds (1 / 3)) := by
    have hlim : (∑ _b ∈ good, (3 : ℝ)⁻¹ ^ w) = 1 / 3 := by
      have hcard : good.card = 3 ^ (w - 1) := by simpa [good] using hbal
      rw [Finset.sum_const, nsmul_eq_mul, hcard]
      push_cast
      rw [show w = (w - 1) + 1 by omega, pow_add]
      have hpow : (3 : ℝ) ^ (w - 1) * (3 : ℝ)⁻¹ ^ (w - 1) = 1 := by
        rw [← mul_pow]
        norm_num
      have he : w - 1 + 1 - 1 = w - 1 := by omega
      rw [he, pow_one, ← mul_assoc, hpow]
      norm_num
    rw [← hlim]
    convert hblocks using 1
    funext k
    rw [hcount]
    push_cast
    exact Finset.sum_div good
      (fun b => (Nat.count (fun j => ∀ i, block j i = b i) k : ℝ)) k
  let out : ℕ → Prop := fun j => stepSym (ι (amusicalInv^[j] n)) = 0
  have hshift (k : ℕ) : Nat.count out (s + k) =
      Nat.count out s + Nat.count (fun j => f (block j) = 0) k := by
    rw [Nat.count_add]
    congr 1
    congr 1
    funext j
    simp only [out]
    rw [hf (s + j) (by omega)]
    simp only [Nat.add_sub_cancel_left]
    rfl
  simp_rw [← Nat.count_eq_card_filter_range]
  apply (Filter.tendsto_add_atTop_iff_nat s).1
  have hzero : Filter.Tendsto (fun k : ℕ => (Nat.count out s : ℝ) / (s + k))
      Filter.atTop (nhds 0) := by
    simpa [Nat.cast_add, add_comm] using (Filter.tendsto_add_atTop_iff_nat s).2
      (tendsto_const_div_atTop_nhds_zero_nat (Nat.count out s : ℝ))
  have hscale : Filter.Tendsto (fun k : ℕ => (k : ℝ) / (k + s))
      Filter.atTop (nhds 1) := tendsto_natCast_div_add_atTop (s : ℝ)
  have ht := hzero.add (hgood.mul hscale)
  have ht' : Filter.Tendsto (fun k : ℕ =>
      (Nat.count out (k + s) : ℝ) / (k + s)) Filter.atTop (nhds (1 / 3)) := by
    have hev : (fun k : ℕ => (Nat.count out s : ℝ) / (s + k) +
        (Nat.count (fun j => f (block j) = 0) k : ℝ) / k * ((k : ℝ) / (k + s)))
        =ᶠ[Filter.atTop] fun k => (Nat.count out (k + s) : ℝ) / (k + s) := by
      filter_upwards [Filter.eventually_ge_atTop 1] with k hk
      rw [add_comm k s, hshift]
      push_cast
      have hk0 : (k : ℝ) ≠ 0 := by positivity
      field_simp
      ring
    convert ht.congr' hev using 1
    all_goals norm_num
  simpa only [out, Nat.cast_add] using ht'

/-- **Target (Theorem N).**  An injective reversor whose even steps are a balanced block code of
the backward itinerary forces every non-periodic integer's backward itinerary to be abnormal.
Paper proof: `evenFrequency_of_backwardNormal`, then `not_reversor_of_evenFrequency_lt` with
`c = 1/3 < 2 − log₂ 3` (`3³ < 2⁵`). -/
theorem not_reversor_of_backwardNormal {ι : ℤ → ℤ} (hrev : IsAmusicalReversor ι)
    (hinj : Function.Injective ι) (n : ℤ) (hn : ∀ k ≥ 1, amusical^[k] n ≠ n)
    (hnorm : BackwardNormal n) (s w : ℕ) (hw : 1 ≤ w) (f : (Fin w → Fin 3) → Fin 3)
    (hf : ∀ j ≥ s, stepSym (ι (amusicalInv^[j] n)) =
      f (fun i => stepSym (amusicalInv^[j - s + 1 + i] n)))
    (hbal : (Finset.univ.filter fun b => f b = 0).card = 3 ^ (w - 1)) : False := by
  apply not_reversor_of_evenFrequency_lt hrev hinj n hn (1 / 3)
  · have hlog : Real.logb 2 3 < (5 : ℝ) / 3 := by
      exact (CollatzMoonshot.FrontA.logb_two_three_lt_iff 5 3 (by norm_num)).2 (by norm_num)
    linarith
  · exact evenFrequency_of_backwardNormal ι n hnorm s w hw f hf hbal

end CollatzMoonshot.Amusical
