/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Obstructions.Amusical

/-!
# The anti-Kohl conjecture and transient cones

Kohl's permutation `ω` has a single orbit containing residue-class tails, built from slope-`1`
pieces.  `U` has none: every slope `3/2^k` has `3`-adic valuation exactly `1`, so the slope of
`Uˡ` has valuation `ℓ`.  The 2026-10-13 "global" agent isolated the hypothesis that survives every
proved counter-model:

**Anti-Kohl conjecture** (`AntiKohlConjecture p`, believed ~93%).  A residue-class-wise affine
permutation of `ℤ` whose slopes all have `p`-adic valuation `1` has no orbit containing a
residue-class tail.  For `p = 3` it gives `U` a seventh orbit (`atLeastSevenOrbits_of_antiKohl`).

The "antikohl" agent (same day) proved it for explicit wild members of the class via
**Theorem T** (`orbit_densityZero_of_transientCone`).  Suppose `σ(S) ⊆ S`, and both the forward
core `σⁿ(S)` and the never-entering set `{x : σʲ x ∉ S, j ≤ n}` have densities tending to `0`.  Then
every finite union of orbits has density `0`.  So:

* `κ` (modulus `6`, slopes `2`, `2/3`, cone `odd ∪ 12ℤ`) has only density-`0` orbits;
* `σ_τ = τ ∘ U`, with `τ` the class transposition `2k+1 ↔ 4k+2`, does too (cone `2 + 4ℤ`, on which
  `σ_τ x = 3x`).  This holds for `31` of the `32` single-class-transposition perturbations of `U`
  that have a cone.

For `U` itself the method is vacuous: no union of residue classes is a cone
(`amusical_no_periodic_cone`).  "One fixed prime" is essential.  Conjugating translation by an
RCWA map gives slopes `3/2` and `2/3` only, valuation `1` at *some* prime on every piece, and one
orbit (`mixedPrime_single_orbit`).

Paper proofs: agent report `antikohl.md` (2026-10-13), summarized in
`RESEARCH-2026-10-13-amusical-single-chain.md` §15.  Core densities re-checked by box counting
(`scripts/amusical/cores.py`); cone-freeness of `U` for moduli up to `200` by
`scripts/amusical/cone.py`.  Treadmill target (`KICKOFF-2026-10-13-amusical-antikohl.md`): close
every `sorry` here.
-/

namespace CollatzMoonshot.Amusical

open CollatzMoonshot.Obstructions.Amusical

/-- `σ` is residue-class-wise affine with modulus `m`: on the class of `r`,
`c r * σ x = a r * x + b r`. -/
structure IsRCWA (σ : ℤ → ℤ) (m : ℕ) (a b c : ℤ → ℤ) : Prop where
  pos : 0 < m
  coeff : ∀ r, 0 < c r ∧ a r ≠ 0
  eqn : ∀ x, c (x % m) * σ x = a (x % m) * x + b (x % m)

/-- Every slope `a r / c r` has `p`-adic valuation exactly `1`. -/
def SlopeValOne (p m : ℕ) (a c : ℤ → ℤ) : Prop :=
  ∀ r : ℤ, 0 ≤ r → r < m → padicValRat p ((a r : ℚ) / c r) = 1

/-- The two-sided orbit of `x` under a permutation `σ`. -/
def permOrbit (σ : Equiv.Perm ℤ) (x : ℤ) : Set ℤ :=
  Set.range fun n : ℤ => (σ ^ n) x

/-- `O` contains a tail `{y ≡ r (mod M), y ≥ N}` of a residue class. -/
def ContainsClassTail (O : Set ℤ) : Prop :=
  ∃ M r N : ℤ, 0 < M ∧ ∀ y, y ≡ r [ZMOD M] → N ≤ y → y ∈ O

/-- **Believed (~93%), open: the anti-Kohl conjecture at the prime `p`.** -/
def AntiKohlConjecture (p : ℕ) : Prop :=
  ∀ (σ : Equiv.Perm ℤ) (m : ℕ) (a b c : ℤ → ℤ), IsRCWA σ m a b c → SlopeValOne p m a c →
    ∀ x, ¬ ContainsClassTail (permOrbit σ x)

/-- **Target.**  `U` belongs to the anti-Kohl class at `p = 3`: modulus `4`, `a = 3`,
`c ∈ {2, 4}`, `b ∈ {0, 1, −1}`. -/
theorem amusical_antiKohl_class :
    ∃ a b c : ℤ → ℤ, IsRCWA amusical 4 a b c ∧ SlopeValOne 3 4 a c := by
  sorry

/-- **Target.**  The anti-Kohl conjecture at `3` gives `U` a seventh orbit.  Paper proof: without a
seventh orbit, the orbit of `8` contains every nonnegative integer off the twenty known cycle
members (`AmusicalChains`: the six orbits cover `ℕ`), so it contains the class tail
`{y ≥ 112}`; `permOrbit amusicalPerm 8 = amusicalOrbit 8`. -/
theorem atLeastSevenOrbits_of_antiKohl (h : AntiKohlConjecture 3) :
    AmusicalAtLeastSevenOrbits := by
  sorry

/-- **Target (the gate).**  `U` has no periodic cone: a union of residue classes mod `M` that `U`
maps into itself is empty or everything.  Paper proof: the residue graph of `U` mod `M` (edge
`r → s` when `U` maps some `x ≡ r` to `s`) is strongly connected (agent report `seventh.md`, T4);
a forward-closed class union is a union of strongly connected components with no exit. -/
theorem amusical_no_periodic_cone (M : ℕ) (hM : 0 < M) (R : Set (ZMod M))
    (h : ∀ n : ℤ, (n : ZMod M) ∈ R → ((amusical n : ℤ) : ZMod M) ∈ R) :
    R = ∅ ∨ R = Set.univ := by
  sorry

/-! ## Theorem T -/

open Classical in
/-- `A` has density `0` in the symmetric boxes `[−X, X]`. -/
def IntDensityZero (A : Set ℤ) : Prop :=
  Filter.Tendsto (fun X : ℕ => (((Finset.Icc (-(X : ℤ)) X).filter (· ∈ A)).card : ℝ) / X)
    Filter.atTop (nhds 0)

open Classical in
/-- `A` has upper density at most `ε` in the symmetric boxes, eventually. -/
def IntDensityLE (A : Set ℤ) (ε : ℝ) : Prop :=
  ∀ᶠ X : ℕ in Filter.atTop, (((Finset.Icc (-(X : ℤ)) X).filter (· ∈ A)).card : ℝ) ≤ ε * X

/-- **Target (Theorem T).**  A cone `S` (`σ S ⊆ S`) whose forward cores `σⁿ S` and never-entering
sets `{x : σʲ x ∉ S, j ≤ n}` both have density tending to `0` makes every finite union of orbits
density `0`.  Paper proof: an orbit is inside `S`, inside the complement, or a backward ray in the
complement followed by a forward ray in `S`; in each case all but `2n` of its points lie in `σⁿ S`
or in the `n`-th never-entering set. -/
theorem orbit_densityZero_of_transientCone (σ : Equiv.Perm ℤ) (S : Set ℤ)
    (hS : ∀ x ∈ S, σ x ∈ S)
    (hfwd : ∀ ε > 0, ∃ n : ℕ, IntDensityLE ((σ ^ n) '' S) ε)
    (hbwd : ∀ ε > 0, ∃ n : ℕ, IntDensityLE {x | ∀ j ≤ n, (σ ^ j) x ∉ S} ε)
    (F : Finset ℤ) : IntDensityZero (⋃ x ∈ F, permOrbit σ x) := by
  sorry

/-- **Target.**  Under Theorem T's hypotheses `σ` has infinitely many orbits and none contains a
residue-class tail.  Paper proof: finitely many orbits would cover `ℤ`, of density `1`; a class
tail has density `1/(2M)` in the symmetric boxes. -/
theorem infinitelyManyOrbits_of_transientCone (σ : Equiv.Perm ℤ) (S : Set ℤ)
    (hS : ∀ x ∈ S, σ x ∈ S)
    (hfwd : ∀ ε > 0, ∃ n : ℕ, IntDensityLE ((σ ^ n) '' S) ε)
    (hbwd : ∀ ε > 0, ∃ n : ℕ, IntDensityLE {x | ∀ j ≤ n, (σ ^ j) x ∉ S} ε) :
    {O : Set ℤ | ∃ x, O = permOrbit σ x}.Infinite ∧ ∀ x, ¬ ContainsClassTail (permOrbit σ x) := by
  sorry

/-! ## `κ`: an explicit member of the class at `p = 2` -/

/-- `κ(6k) = 12k+5`, `κ(6k+1) = 4k+3`, `κ(6k+2) = 4k+2`, `κ(6k+3) = 12k+1`, `κ(6k+4) = 4k`,
`κ(6k+5) = 12k+9`: slopes `2` and `2/3`. -/
def kappa (x : ℤ) : ℤ :=
  if x % 6 = 0 then 2 * x + 5
  else if x % 6 = 1 then (2 * x + 7) / 3
  else if x % 6 = 2 then (2 * x + 2) / 3
  else if x % 6 = 3 then 2 * x - 5
  else if x % 6 = 4 then (2 * x - 8) / 3
  else 2 * x - 1

/-- The inverse of `κ`, by image class. -/
def kappaInv (y : ℤ) : ℤ :=
  if y % 4 = 0 then (3 * y + 8) / 2
  else if y % 4 = 2 then (3 * y - 2) / 2
  else if y % 4 = 3 then (3 * y - 7) / 2
  else if y % 12 = 5 then (y - 5) / 2
  else if y % 12 = 1 then (y + 5) / 2
  else (y + 1) / 2

theorem kappaInv_kappa (x : ℤ) : kappaInv (kappa x) = x := by
  have h : x % 6 = 0 ∨ x % 6 = 1 ∨ x % 6 = 2 ∨ x % 6 = 3 ∨ x % 6 = 4 ∨ x % 6 = 5 := by omega
  rcases h with h | h | h | h | h | h <;> simp only [kappa, h] <;> norm_num <;>
    unfold kappaInv <;> split_ifs <;> omega

theorem kappa_kappaInv (y : ℤ) : kappa (kappaInv y) = y := by
  have h : y % 4 = 0 ∨ y % 4 = 2 ∨ y % 4 = 3 ∨ y % 12 = 5 ∨ y % 12 = 1 ∨ y % 12 = 9 := by omega
  rcases h with h | h | h | h | h | h
  · rw [kappaInv, if_pos h]; unfold kappa; split_ifs <;> omega
  · rw [kappaInv, if_neg (by omega), if_pos h]; unfold kappa; split_ifs <;> omega
  · rw [kappaInv, if_neg (by omega), if_neg (by omega), if_pos h]; unfold kappa
    split_ifs <;> omega
  · rw [kappaInv, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h]
    unfold kappa; split_ifs <;> omega
  · rw [kappaInv, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_pos h]
    unfold kappa; split_ifs <;> omega
  · rw [kappaInv, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
    unfold kappa; split_ifs <;> omega

/-- `κ` as a permutation of `ℤ`. -/
def kappaPerm : Equiv.Perm ℤ where
  toFun := kappa
  invFun := kappaInv
  left_inv := kappaInv_kappa
  right_inv := kappa_kappaInv

/-- The cone `odd ∪ 12ℤ` is mapped into the odds. -/
theorem kappa_cone (x : ℤ) (h : x % 2 = 1 ∨ x % 12 = 0) : kappa x % 2 = 1 := by
  unfold kappa; split_ifs <;> omega

/-- **Target.**  `κ` is in the anti-Kohl class at `p = 2`. -/
theorem kappa_antiKohl_class :
    ∃ a b c : ℤ → ℤ, IsRCWA kappa 6 a b c ∧ SlopeValOne 2 6 a c := by
  sorry

/-- **Target.**  Every orbit of `κ` has density `0`, so `κ` has infinitely many orbits and none
contains a class tail.  Paper proof: Theorem T with `S = odd ∪ 12ℤ`.
* Backward core: survival forces `y_j = κʲ x / 2 ∉ 3ℤ`, where `y ↦ (2y+1)/3` or `(2y−4)/3`, and
  each branch maps a class mod `2^a · 3` onto a class mod `2^(a+1)`, equidistributed mod `3`; so the
  density is exactly `(5/12)(2/3)ⁿ`.
* Forward core: on odds `x = 2y+1`, `κ` acts as `y ↦ (2y+3)/3, 2y−2, 2y` by `y mod 3`.  The image
  classes have `v₃(modulus) ≤ 1`, and their masses by type (3-free / `0, 1, 2 mod 3`) evolve
  linearly with spectral radius `0.9196…`, the root of `8λ³ − 4λ² − 2λ − 1`. -/
theorem kappa_orbit_densityZero (x : ℤ) : IntDensityZero (permOrbit kappaPerm x) := by
  sorry

/-! ## `σ_τ`: `U` followed by one class transposition -/

/-- The class transposition `2k+1 ↔ 4k+2`, fixing `4ℤ`. -/
def ctau (x : ℤ) : ℤ :=
  if x % 2 = 1 then 2 * x else if x % 4 = 2 then x / 2 else x

theorem ctau_ctau (x : ℤ) : ctau (ctau x) = x := by
  unfold ctau; split_ifs <;> omega

/-- `τ` as an involutive permutation. -/
def ctauPerm : Equiv.Perm ℤ where
  toFun := ctau
  invFun := ctau
  left_inv := ctau_ctau
  right_inv := ctau_ctau

/-- `σ_τ = τ ∘ U`. -/
def sigmaTauPerm : Equiv.Perm ℤ :=
  amusicalPerm.trans ctauPerm

/-- On the cone `2 + 4ℤ`, `σ_τ` is multiplication by `3`. -/
theorem sigmaTau_two_mod_four (x : ℤ) (h : x % 4 = 2) : sigmaTauPerm x = 3 * x := by
  show ctau (amusical x) = 3 * x
  unfold ctau amusical; split_ifs <;> omega

/-- **Target.**  Every orbit of `σ_τ = τ ∘ U` has density `0`.  Paper proof: Theorem T with
`S = 2 + 4ℤ`.  The forward core is `3ⁿ (2 + 4ℤ)`, of density `3⁻ⁿ/4`.  The backward core
`{x : σ_τʲ x ∉ S, j ≤ n}` has density `(1/2)(3/4)ⁿ⁻¹`.  This comes from a closed 13-type
automaton on image classes typed by known `2`-adic digits and residue mod `3`, with
characteristic polynomial `λ¹²(4λ − 3)/4` (agent scripts `typeauto.py`, `typeauto2.py`). -/
theorem sigmaTau_orbit_densityZero (x : ℤ) : IntDensityZero (permOrbit sigmaTauPerm x) := by
  sorry

/-! ## One fixed prime is essential -/

/-- `h(6k+r) = 5k+r` (`r ∈ {0, 2, 4}`), `h(4k+r) = 5k+r` (`r ∈ {1, 3}`). -/
def hFive (x : ℤ) : ℤ :=
  if x % 2 = 0 then 5 * (x / 6) + x % 6 else 5 * (x / 4) + x % 4

/-- **Target.**  `hFive` is a bijection of `ℤ` (images: `5k + {0, 2, 4}` from evens, `5k + {1, 3}`
from odds). -/
theorem hFive_bijective : Function.Bijective hFive := by
  sorry

/-- **Target.**  `h ∘ (· + 1) ∘ h⁻¹` has modulus `30` and only the slopes `3/2` and `2/3` (the
parity of `h⁻¹ y` flips under `+1`), so each slope has valuation `1` at `3` or at `2`; being
conjugate to a translation, it has a single orbit. -/
theorem mixedPrime_single_orbit :
    let σ := (Equiv.ofBijective hFive hFive_bijective).symm.trans
      ((Equiv.addRight (1 : ℤ)).trans (Equiv.ofBijective hFive hFive_bijective))
    (∃ a b c : ℤ → ℤ, IsRCWA σ 30 a b c ∧
      ∀ r, (a r : ℚ) / c r = 3 / 2 ∨ (a r : ℚ) / c r = 2 / 3) ∧
      ∀ x y : ℤ, ∃ n : ℤ, (σ ^ n) x = y := by
  sorry

end CollatzMoonshot.Amusical
