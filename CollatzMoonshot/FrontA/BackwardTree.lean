/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.FrontA.Threads

/-!
# Barriered backward trees

Finite vocabulary for Route A2 of `FRONT-A-ROUTES.md`.  A path counted by
`ReachesInBand d X m` reaches `d` without ever leaving `[d, X]`; the ceiling is
part of the finite exhaustion, not a claim about the full backward basin.

The elementary exact result here is a useful control on every census: if
`3 ∣ d`, then *every* predecessor of `d` is on the pure doubling spine.  The
experiment in `experiments/barrier_tree.py` found approximately linear scaled
harmonic mass for sampled seeds with `3 ∤ d`; the two growth propositions below
pin that observation without promoting it to an axiom or theorem.
-/

namespace CollatzMoonshot.FrontA

open Filter

/-- `m` reaches `d`, and the entire witnessing path stays in the closed band
`[d, X]`. -/
def ReachesInBand (d X m : ℕ) : Prop :=
  ∃ k, step^[k] m = d ∧
    ∀ j, j ≤ k → d ≤ step^[j] m ∧ step^[j] m ≤ X

/-- The finite floor-and-ceiling-truncated backward tree used by the census. -/
noncomputable def barrieredPreimages (d p : ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.Icc d ((2 : ℕ) ^ p * d)).filter
      fun m => ReachesInBand d ((2 : ℕ) ^ p * d) m

/-- Harmonic mass of the finite barriered tree. -/
noncomputable def barrierHarmonicMass (d p : ℕ) : ℝ :=
  ∑ m ∈ barrieredPreimages d p, (m : ℝ)⁻¹

/-- A value divisible by `3` cannot have an odd Collatz predecessor. -/
theorem eq_two_mul_of_step_eq_of_three_dvd {m x : ℕ} (hx : 3 ∣ x)
    (hmx : step m = x) : m = 2 * x := by
  unfold step at hmx
  split at hmx
  next hEven => omega
  next hOdd =>
    obtain ⟨q, hq⟩ := hx
    omega

/-- Iterating backwards from a multiple of `3` forces a pure doubling word. -/
theorem eq_pow_two_mul_of_iterate_eq_of_three_dvd (k : ℕ) :
    ∀ {m d : ℕ}, 3 ∣ d → step^[k] m = d → m = 2 ^ k * d := by
  induction k with
  | zero =>
      intro m d hd hmd
      simpa using hmd
  | succ k ih =>
      intro m d hd hmd
      have htail : step^[k] (step m) = d := by
        simpa [Function.iterate_succ_apply] using hmd
      have hstep : step m = 2 ^ k * d := ih hd htail
      have hdiv : 3 ∣ step m := by
        rw [hstep]
        exact dvd_mul_of_dvd_right hd _
      have hm : m = 2 * step m :=
        eq_two_mul_of_step_eq_of_three_dvd hdiv rfl
      calc
        m = 2 * (2 ^ k * d) := by rw [hm, hstep]
        _ = 2 ^ (k + 1) * d := by rw [pow_succ]; ring

@[simp] theorem step_two_mul (n : ℕ) : step (2 * n) = n := by
  unfold step
  simp

/-- Once an orbit is a unit modulo `3`, every later iterate remains a unit.
Even steps divide by the unit `2`; odd steps land at `1 mod 3`. -/
theorem three_not_dvd_step_of_three_not_dvd {n : ℕ} (h3 : ¬3 ∣ n) :
    ¬3 ∣ step n := by
  intro hs
  obtain ⟨q, hq⟩ := hs
  unfold step at hq
  split at hq
  next hEven =>
    apply h3
    use 2 * q
    omega
  next hOdd => omega

/-- Unit status modulo `3` is invariant along the whole forward orbit. -/
theorem three_not_dvd_iterate {n : ℕ} (h3 : ¬3 ∣ n) (k : ℕ) :
    ¬3 ∣ step^[k] n := by
  induction k with
  | zero => simpa using h3
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact three_not_dvd_step_of_three_not_dvd ih

/-- The forward half of the exact doubling-spine description. -/
theorem iterate_pow_two_mul (k d : ℕ) : step^[k] (2 ^ k * d) = d := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply]
      rw [show 2 ^ (k + 1) * d = 2 * (2 ^ k * d) by rw [pow_succ]; ring]
      rw [step_two_mul, ih]

/-- The full backward basin of a multiple of `3` is exactly its doubling spine.
This is stronger than the barriered-tree control: no floor assumption is used. -/
theorem reachesValue_iff_eq_pow_two_mul_of_three_dvd {m d : ℕ} (hd : 3 ∣ d) :
    ReachesValue m d ↔ ∃ k, m = 2 ^ k * d := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, eq_pow_two_mul_of_iterate_eq_of_three_dvd k hd hk⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, iterate_pow_two_mul k d⟩

/-- In particular, every member of a band-truncated tree rooted at a multiple
of `3` lies on the exact doubling spine. -/
theorem eq_pow_two_mul_of_reachesInBand_of_three_dvd {m d X : ℕ} (hd : 3 ∣ d)
    (hband : ReachesInBand d X m) : ∃ k, m = 2 ^ k * d := by
  obtain ⟨k, hk, _⟩ := hband
  exact ⟨k, eq_pow_two_mul_of_iterate_eq_of_three_dvd k hd hk⟩

/-- **Experiment-suggested target.**  Every fixed non-multiple-of-`3` seed has
positive asymptotic scaled harmonic growth in its floor-preserving backward
tree.  This is proposed mathematics, hence a `def`, not an axiom. -/
def PointwiseBarrierHarmonicGrowth : Prop :=
  ∀ d : ℕ, 1 ≤ d → ¬3 ∣ d →
    ∃ c : ℝ, 0 < c ∧ ∃ p₀ : ℕ, ∀ p, p₀ ≤ p →
      c * (p : ℝ) ≤ (d : ℝ) * barrierHarmonicMass d p

/-- The stronger uniform form initially suggested (but certainly not
established) by the consecutive-seed census.  The nested 3-adic stress test in
`experiments/barrier_adversary.py` drives the observed constants downward, so
this target may be false even if the pointwise form is true.  In any case it
does not imply `FloorPreservingSaturation`: after undoing the scaling, one seed
supplies only order `log R / d` harmonic mass, and moving high-floor seeds force
`d → ∞`. -/
def UniformBarrierHarmonicGrowth : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ p₀ : ℕ, ∀ d : ℕ, 1 ≤ d → ¬3 ∣ d →
    ∀ p, p₀ ≤ p → c * (p : ℝ) ≤ (d : ℝ) * barrierHarmonicMass d p

/-- A second piece of new mathematics that naive moving-seed aggregation would
need: the reciprocals of the values on any divergent orbit have infinite total
mass.  Finite long-excursion proxies in `experiments/barrier_tail.py` give no
support for assuming this for free.  Even this pin plus uniform tree growth
would still require an overlap/annular-packing theorem. -/
def DivergentTailHarmonicBudget : Prop :=
  ∀ n : ℕ, 1 ≤ n → Diverges n →
    Tendsto (fun K => ∑ k ∈ Finset.range K, ((step^[k] n : ℕ) : ℝ)⁻¹) atTop atTop

/-- The uniform experimental target specializes to the pointwise one. -/
theorem pointwiseBarrierHarmonicGrowth_of_uniform
    (h : UniformBarrierHarmonicGrowth) : PointwiseBarrierHarmonicGrowth := by
  obtain ⟨c, hc, p₀, hgrowth⟩ := h
  intro d hd h3
  exact ⟨c, hc, p₀, hgrowth d hd h3⟩

end CollatzMoonshot.FrontA
