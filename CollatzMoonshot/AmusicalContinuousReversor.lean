/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalContinuousReversor.Cylinder
import CollatzMoonshot.AmusicalContinuousReversor.Itinerary

/-!
# Reversors of `U` that are determined by residues

`infinitelyManyOrbits_iff_reversor` turns Klamkin's problem (a) into the existence of a reversing
involution with infinitely many fixed points, and Theorem NR (`no_piecewiseAffine_reversor`) rules
out piecewise-affine ones.  This file goes one step further, to reversors that are continuous for
the `(2,3)`-adic topology on `ℤ`: the last few base-2 and base-3 digits of `ι n` are fixed by the
last few base-2 and base-3 digits of `n`.  Such a reversor is determined by one finite table
(`reversor_eq_of_stepSym_eq`: a reversor is determined by the step symbols of its values).

* `reversor_const_of_twoAdicContinuous`, `reversor_const_of_threeAdicContinuous`: continuity for one
  prime alone forces a constant reversor (Theorems A, A′).  These are facts about the full shift,
  not about the integers, so they mark the limit of soft arguments.
* `no_continuous_linear_reversor`: no injective reversor determined by residues grows at most
  linearly (Theorem C).  The future step symbols of `ι n` are a block function of the past symbols
  of `n`, which are uniform on three letters, so the frequency of even steps is a fraction with a
  power of `3` in the denominator, never the `1/2` that linear growth would force.  For the
  Gaussian relative `H` the analogous count balances (both laws have powers of `5`), which is where
  the argument stops applying.
* `AmusicalNoContinuousReversor`: no bijective residue-determined reversor at all.  Believed
  (~93%), open.

Paper proofs: agent report `reversor.md` (2026-10-13), summarized in
`RESEARCH-2026-10-13-amusical-single-chain.md` §9.  Treadmill target
(`KICKOFF-2026-10-13-amusical-contrev.md`): close every `sorry` here.
-/

namespace CollatzMoonshot.Amusical

/-- The step symbol of `n`, which says which branch of `U` applies: `0` if `n` is even, `1` if
`n ≡ 1 (mod 4)`, `2` if `n ≡ 3 (mod 4)`. -/
def stepSym (n : ℤ) : Fin 3 :=
  if n % 2 = 0 then 0 else if n % 4 = 1 then 1 else 2

/-- `ι` reverses `U` pointwise: `ι ∘ U = U⁻¹ ∘ ι`.  No bijectivity is assumed. -/
def IsAmusicalReversor (ι : ℤ → ℤ) : Prop :=
  ∀ n, ι (amusical n) = amusicalInv (ι n)

/-- **Target (Lemma S).**  A reversor is determined by the step symbols of its values: the forward
itinerary of `ι n` is `stepSym (ι (U⁻ᵏ n))`, and the forward itinerary fixes an integer. -/
theorem reversor_eq_of_stepSym_eq {ι ι' : ℤ → ℤ} (h : IsAmusicalReversor ι)
    (h' : IsAmusicalReversor ι') (hs : ∀ n, stepSym (ι n) = stepSym (ι' n)) : ι = ι' := by
  have back {κ : ℤ → ℤ} (hκ : IsAmusicalReversor κ) (n : ℤ) :
      κ (amusicalInv n) = amusical (κ n) := by
    calc
      κ (amusicalInv n) = amusical (amusicalInv (κ (amusicalInv n))) :=
        (amusical_amusicalInv _).symm
      _ = amusical (κ (amusical (amusicalInv n))) := by rw [hκ]
      _ = amusical (κ n) := by rw [amusical_amusicalInv]
  have iterBack {κ : ℤ → ℤ} (hκ : IsAmusicalReversor κ) :
      ∀ k n, κ (amusicalInv^[k] n) = amusical^[k] (κ n) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        intro n
        rw [Function.iterate_succ_apply']
        rw [back hκ, ih]
        exact (Function.iterate_succ_apply' _ k _).symm
  funext n
  apply eq_of_stepSym_iterate_eq
  intro i
  change stepSym (amusical^[i] (ι n)) = stepSym (amusical^[i] (ι' n))
  rw [← iterBack h i n, ← iterBack h' i n]
  exact hs _

/-- **Target (Theorem A).**  A reversor that is continuous 2-adically alone is constant, with
value `-1`, `0` or `1` (the fixed points of `U⁻¹` among constants).  Paper proof: a forward
cylinder of length `k` around `n` is mapped by `Uᵏ` onto a class mod `3ᵏ`, which meets every class
mod `2^c`; pull a point agreeing with `Uᵏ y` 2-adically back, and use `ι = Uᵏ ∘ ι ∘ Uᵏ` with each
`U`-step losing at most two bits. -/
theorem reversor_const_of_twoAdicContinuous {ι : ℤ → ℤ} (h : IsAmusicalReversor ι)
    (hc : ∀ b : ℕ, ∃ c : ℕ, ∀ n n' : ℤ, n ≡ n' [ZMOD 2 ^ c] → ι n ≡ ι n' [ZMOD 2 ^ b]) :
    ∃ v : ℤ, (v = -1 ∨ v = 0 ∨ v = 1) ∧ ∀ n, ι n = v := by
  sorry

/-- **Target (Theorem A′).**  The 3-adic mirror of Theorem A: backward cylinders are classes mod
`3ᵏ`, `U⁻ᵏ` maps them onto classes mod a power of `2`, and each `U⁻¹`-step loses one trit. -/
theorem reversor_const_of_threeAdicContinuous {ι : ℤ → ℤ} (h : IsAmusicalReversor ι)
    (hc : ∀ b : ℕ, ∃ c : ℕ, ∀ n n' : ℤ, n ≡ n' [ZMOD 3 ^ c] → ι n ≡ ι n' [ZMOD 3 ^ b]) :
    ∃ v : ℤ, (v = -1 ∨ v = 0 ∨ v = 1) ∧ ∀ n, ι n = v := by
  sorry

/-- **Target (Theorem C).**  No injective reversor whose step symbols are determined by residues
mod `2^c₀ 3^d₀` grows at most linearly.  (Residue-determined step symbols are equivalent to
`(2,3)`-adic uniform continuity, by Lemma S.)  Paper proof: for `k ≥ c₀` the step symbol of
`Uᵏ (ι n) = ι (U⁻ᵏ n)` is a fixed function `f` of the backward symbols `k−c₀+1, …, k+d₀` of `n`,
which are i.i.d. uniform on three letters over classes mod powers of `3`.  The share `q` of
windows with `f = even` is a fraction over a power of `3`, so `q ≠ 1/2`; let `ρ = max(q, 1−q)`.
Along `L` disjoint windows the event "every chosen future symbol of `ι n` lies on the `ρ` side"
has density `ρ^L` in `n`, while the same event for an integer `m` has density `2^{−L}` (forward
symbols are i.i.d. `(1/2, 1/4, 1/4)` over classes mod powers of `2`).  Injectivity and
`|ι n| ≤ C|n| + D` give `ρ^L ≤ C · 2^{−L}`, false for large `L`. -/
theorem no_continuous_linear_reversor :
    ¬ ∃ (ι : ℤ → ℤ) (c₀ d₀ C D : ℕ), Function.Injective ι ∧ IsAmusicalReversor ι ∧
      (∀ n n' : ℤ, n ≡ n' [ZMOD 2 ^ c₀ * 3 ^ d₀] → stepSym (ι n) = stepSym (ι n')) ∧
      ∀ n, |ι n| ≤ C * |n| + D := by
  sorry

/-- **Believed (~93%), open: no bijective reversor of `U` is determined by residues.**  By
`reversor_eq_of_stepSym_eq` the candidates are countably many, one per finite table mod
`2^c₀ 3^d₀` (equivalently flip ∘ a surjective cellular automaton on the Matthews–Watts shift), and
each must send every integer to an integer.  Evidence (2026-10-13, agent report `reversor.md`):
every table of window at most `2` sends some integer cycle to a non-integral one (the pure flip
sends the `12`-cycle through `44` to the cycle through `693999/7153`, `7153 = 3¹² − 2¹⁹`), and the
`60` possibly-surjective window-`3` tables passing the cycle test send one of `8, 10, …, 16`
outside the integers below `10¹⁵`. -/
def AmusicalNoContinuousReversor : Prop :=
  ¬ ∃ (ι : Equiv.Perm ℤ) (c₀ d₀ : ℕ), IsAmusicalReversor ι ∧
      ∀ n n' : ℤ, n ≡ n' [ZMOD 2 ^ c₀ * 3 ^ d₀] → stepSym (ι n) = stepSym (ι n')

end CollatzMoonshot.Amusical
