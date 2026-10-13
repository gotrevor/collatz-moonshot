/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalContinuousReversor.Cylinder
import CollatzMoonshot.AmusicalContinuousReversor.Counting
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
(`KICKOFF-2026-10-13-amusical-contrev.md`): close every proof hole here.
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
cylinder of length `k` around `n` is mapped by `Uᵏ` onto a class mod `3ᵏ`, which meets every
class mod `2^c`; pull a point agreeing with `Uᵏ y` 2-adically back, and use
`ι = Uᵏ ∘ ι ∘ Uᵏ` with each
`U`-step losing at most two bits. -/
theorem reversor_const_of_twoAdicContinuous {ι : ℤ → ℤ} (h : IsAmusicalReversor ι)
    (hc : ∀ b : ℕ, ∃ c : ℕ, ∀ n n' : ℤ,
      n ≡ n' [ZMOD 2 ^ c] → ι n ≡ ι n' [ZMOD 2 ^ b]) :
    ∃ v : ℤ, (v = -1 ∨ v = 0 ∨ v = 1) ∧ ∀ n, ι n = v := by
  have back (n : ℤ) : ι (amusicalInv n) = amusical (ι n) := by
    calc
      ι (amusicalInv n) = amusical (amusicalInv (ι (amusicalInv n))) :=
        (amusical_amusicalInv _).symm
      _ = amusical (ι (amusical (amusicalInv n))) := by rw [h]
      _ = amusical (ι n) := by rw [amusical_amusicalInv]
  have iterBack : ∀ t n, ι (amusicalInv^[t] n) = amusical^[t] (ι n) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
        intro n
        rw [Function.iterate_succ_apply']
        rw [back, ih]
        exact (Function.iterate_succ_apply' _ t _).symm
  have hconst : ∀ n y, ι n = ι y := by
    intro n y
    let B := (ι y - ι n).natAbs
    obtain ⟨t, ht⟩ := hc B
    obtain ⟨c, hc'⟩ := hc (B + 2 * t)
    have hcop : IsCoprime ((2 : ℤ) ^ c) ((3 : ℤ) ^ t) :=
      (show IsCoprime (2 : ℤ) 3 from ⟨-1, 1, by norm_num⟩).pow
    obtain ⟨q, hq⟩ := exists_mul_modEq_of_isCoprime hcop
      (d := amusical^[t] y - amusical^[t] n)
    let z := n + amusicalForwardPeriod t n * q
    have hnz : n ≡ z [ZMOD 2 ^ t] := by
      obtain ⟨d, hd⟩ := pow_two_dvd_amusicalForwardPeriod t n
      rw [Int.modEq_iff_add_fac]
      refine ⟨d * q, ?_⟩
      dsimp only [z]
      rw [hd]
      ring
    have hzy : amusical^[t] z ≡ amusical^[t] y [ZMOD 2 ^ c] := by
      dsimp only [z]
      rw [amusical_iterate_add_forwardPeriod_mul]
      convert hq.add_left (amusical^[t] n) using 1 <;> ring
    have hizn : ι n ≡ ι z [ZMOD 2 ^ B] := ht n z hnz
    have hizy : ι z ≡ ι y [ZMOD 2 ^ B] := by
      have hi := hc' _ _ hzy
      have hi' := amusical_iterate_modEq_two B t hi
      have hz := iterBack t (amusical^[t] z)
      have hy := iterBack t (amusical^[t] y)
      rw [amusicalInv_iterate_amusical_iterate] at hz hy
      rw [← hz, ← hy] at hi'
      exact hi'
    have hmod : ι n ≡ ι y [ZMOD 2 ^ B] := hizn.trans hizy
    have hlt : |ι y - ι n| < (2 : ℤ) ^ B := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast (Nat.lt_two_pow_self : B < 2 ^ B)
    have hzero := Int.eq_zero_of_abs_lt_dvd hmod.dvd hlt
    omega
  let v := ι 0
  refine ⟨v, ?_, fun n => hconst n 0⟩
  have hv : v = amusicalInv v := by simpa [v, amusical] using h 0
  unfold amusicalInv at hv
  split_ifs at hv <;> omega

/-- **Target (Theorem A′).**  The 3-adic mirror of Theorem A: backward cylinders are classes
mod `3ᵏ`; `U⁻ᵏ` maps them onto classes mod a power of `2`, and each `U⁻¹`-step loses one
trit. -/
theorem reversor_const_of_threeAdicContinuous {ι : ℤ → ℤ} (h : IsAmusicalReversor ι)
    (hc : ∀ b : ℕ, ∃ c : ℕ, ∀ n n' : ℤ,
      n ≡ n' [ZMOD 3 ^ c] → ι n ≡ ι n' [ZMOD 3 ^ b]) :
    ∃ v : ℤ, (v = -1 ∨ v = 0 ∨ v = 1) ∧ ∀ n, ι n = v := by
  have iterForward : ∀ t n, ι (amusical^[t] n) = amusicalInv^[t] (ι n) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
        intro n
        rw [Function.iterate_succ_apply']
        rw [h, ih]
        exact (Function.iterate_succ_apply' _ t _).symm
  have hconst : ∀ n y, ι n = ι y := by
    intro n y
    let B := (ι y - ι n).natAbs
    obtain ⟨t, ht⟩ := hc B
    obtain ⟨c, hc'⟩ := hc (B + t)
    have hcop : IsCoprime ((3 : ℤ) ^ c) (amusicalBackwardMultiplier t n) := by
      rw [amusicalBackwardMultiplier_eq]
      exact (show IsCoprime (3 : ℤ) 2 from ⟨1, -1, by norm_num⟩).pow
    obtain ⟨q, hq⟩ := exists_mul_modEq_of_isCoprime hcop
      (d := amusicalInv^[t] y - amusicalInv^[t] n)
    let z := n + (3 : ℤ) ^ t * q
    have hnz : n ≡ z [ZMOD 3 ^ t] := by
      rw [Int.modEq_iff_add_fac]
      exact ⟨q, rfl⟩
    have hzy : amusicalInv^[t] z ≡ amusicalInv^[t] y [ZMOD 3 ^ c] := by
      dsimp only [z]
      rw [amusicalInv_iterate_add_pow_three_mul_exact t t le_rfl]
      simp only [Nat.sub_self, pow_zero, one_mul]
      convert hq.add_left (amusicalInv^[t] n) using 1 <;> ring
    have hizn : ι n ≡ ι z [ZMOD 3 ^ B] := ht n z hnz
    have hizy : ι z ≡ ι y [ZMOD 3 ^ B] := by
      have hi := hc' _ _ hzy
      have hi' := amusicalInv_iterate_modEq_three B t hi
      have hz := iterForward t (amusicalInv^[t] z)
      have hy := iterForward t (amusicalInv^[t] y)
      rw [amusical_iterate_amusicalInv_iterate] at hz hy
      rw [← hz, ← hy] at hi'
      exact hi'
    have hmod : ι n ≡ ι y [ZMOD 3 ^ B] := hizn.trans hizy
    have hlt : |ι y - ι n| < (3 : ℤ) ^ B := by
      rw [← Int.natCast_natAbs]
      have hnat : B < 3 ^ B := lt_of_lt_of_le (Nat.lt_two_pow_self : B < 2 ^ B)
        (Nat.pow_le_pow_left (by norm_num) B)
      exact_mod_cast hnat
    have hzero := Int.eq_zero_of_abs_lt_dvd hmod.dvd hlt
    omega
  let v := ι 0
  refine ⟨v, ?_, fun n => hconst n 0⟩
  have hv : v = amusicalInv v := by simpa [v, amusical] using h 0
  unfold amusicalInv at hv
  split_ifs at hv <;> omega

/-- **Target (Theorem C).**  No injective reversor whose step symbols are determined by residues
mod `2^c₀ 3^d₀` grows at most linearly.  (Residue-determined step symbols are equivalent to
`(2,3)`-adic uniform continuity, by Lemma S.)  Paper proof: for `k ≥ c₀` the step symbol of
`Uᵏ (ι n) = ι (U⁻ᵏ n)` is a fixed function `f` of the backward symbols
`k−c₀+1, …, k+d₀` of `n`,
which are i.i.d. uniform on three letters over classes mod powers of `3`.  The share `q` of
windows with `f = even` is a fraction over a power of `3`, so `q ≠ 1/2`; let `ρ = max(q, 1−q)`.
Along `L` disjoint windows the event "every chosen future symbol of `ι n` lies on the `ρ` side"
has density `ρ^L` in `n`, while the same event for an integer `m` has density `2^{−L}` (forward
symbols are i.i.d. `(1/2, 1/4, 1/4)` over classes mod powers of `2`).  Injectivity and
`|ι n| ≤ C|n| + D` give `ρ^L ≤ C · 2^{−L}`, false for large `L`. -/
theorem no_continuous_linear_reversor :
    ¬ ∃ (ι : ℤ → ℤ) (c₀ d₀ C D : ℕ),
      Function.Injective ι ∧ IsAmusicalReversor ι ∧
      (∀ n n' : ℤ, n ≡ n' [ZMOD 2 ^ c₀ * 3 ^ d₀] → stepSym (ι n) = stepSym (ι n')) ∧
      ∀ n, |ι n| ≤ C * |n| + D := by
  classical
  rintro ⟨φ, c, d, C, D, hφ, hrev, htable, hgrowth⟩
  have iterBack : ∀ t n, φ (amusicalInv^[t] n) = amusical^[t] (φ n) := by
    have back (n : ℤ) : φ (amusicalInv n) = amusical (φ n) := by
      calc
        φ (amusicalInv n) = amusical (amusicalInv (φ (amusicalInv n))) :=
          (amusical_amusicalInv _).symm
        _ = amusical (φ (amusical (amusicalInv n))) := by rw [hrev]
        _ = amusical (φ n) := by rw [amusical_amusicalInv]
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
        intro n
        rw [Function.iterate_succ_apply', back, ih]
        exact (Function.iterate_succ_apply' _ t _).symm
  by_cases hw0 : c + d = 0
  · have hφ01 : φ 0 = φ 1 := by
      apply eq_of_stepSym_iterate_eq
      intro i
      rw [← iterBack i 0, ← iterBack i 1]
      apply htable
      simp [show c = 0 by omega, show d = 0 by omega, Int.ModEq]
    have := hφ hφ01
    norm_num at this
  have hw : 0 < c + d := by omega
  have htableRaw : ∀ x y : ℤ, x ≡ y [ZMOD (2 : ℤ) ^ c * 3 ^ d] →
      continuousRawStepSym (φ x) = continuousRawStepSym (φ y) := by
    intro x y hxy
    exact htable x y hxy
  let F : (Fin (c + d) → Fin 3) → Bool := fun u =>
    continuousStepBit (continuousBlockOutput φ c d u)
  obtain ⟨b, a, ha, hmajor⟩ := continuous_exists_majority_bit (c + d) F
  let x := 3 ^ (c + d)
  let y := 2 * a
  let K := 2 * C + 1
  let L := K * x
  have hx : 1 ≤ x := by
    dsimp only [x]
    exact one_le_pow₀ (by norm_num)
  have hxy : x < y := by simpa only [x, y] using hmajor
  have hp0 := continuous_const_mul_pow_lt_pow hx hxy K
  let A := 3 ^ (L * (c + d))
  have hA : A = x ^ L := by
    dsimp only [A, x]
    rw [Nat.mul_comm L (c + d), pow_mul]
  have hp : K * A < y ^ L := by simpa only [L, hA] using hp0
  let N := continuousOutputLength c d L
  let B := 4 ^ N
  let k := 2 * (D + 1 + B) + 1
  let X := A * k
  let Y := C * X + D + 1
  let P : ℕ → Prop := continuousInputEvent φ c d b L
  let Q : ℕ → Prop := continuousOutputEvent c d b L
  have hPbase : Nat.count P A = a ^ L := by
    dsimp only [P, A]
    apply continuous_count_inputEvent φ c d htableRaw b L a
    simpa only [F] using ha
  have hPmod : ∀ n, P n ↔ P (n % A) := by
    intro n
    simpa only [P, A] using continuousInputEvent_mod φ c d htableRaw b L n
  have hPcount : Nat.count P X = k * a ^ L := by
    rw [show X = A * k by rfl, WindowCount.count_periodic_mul P A hPmod, hPbase]
  have hmap : ∀ n, P n → Q (φ n).natAbs := by
    intro n hn
    change continuousInputEvent φ c d b L n at hn
    change continuousOutputEvent c d b L (φ n).natAbs
    rw [← continuousOutputEventInt_natAbs]
    unfold continuousInputEvent at hn
    unfold continuousOutputEventInt
    intro i
    rw [← iterBack (i.val * (c + d)) n,
      ← iterBack c (amusicalInv^[i.val * (c + d)] n)]
    exact hn i
  have himage : Nat.count P X ≤ 2 * Nat.count Q Y := by
    simpa only [Y] using
      continuous_count_le_two_count_of_injective_natAbs φ hφ C D hgrowth P Q hmap X
  have hQmod : ∀ n, Q n ↔ Q (n % B) := by
    intro n
    simpa only [Q, B, N] using continuousOutputEvent_mod c d b L hw n
  have hBpos : 0 < B := by positivity
  have hQbound : Nat.count Q Y ≤ (Y / B + 1) * Nat.count Q B :=
    (WindowCount.count_periodic_bounds Q B hBpos hQmod Y).2
  have hQB : Nat.count Q B * 2 ^ L = B := by
    simpa only [Q, B, N] using continuous_count_outputEvent_mul c d b L hw
  have hchain : k * a ^ L ≤ 2 * ((Y / B + 1) * Nat.count Q B) := by
    rw [← hPcount]
    exact himage.trans (Nat.mul_le_mul_left 2 hQbound)
  have hdiv : (Y / B + 1) * B ≤ Y + B := by
    rw [Nat.add_mul]
    simpa using Nat.add_le_add_right (Nat.div_mul_le_self Y B) B
  have hmain : k * y ^ L ≤ 2 * (Y + B) := by
    calc
      k * y ^ L = (k * a ^ L) * 2 ^ L := by
        dsimp only [y]
        rw [mul_pow]
        ring
      _ ≤ (2 * ((Y / B + 1) * Nat.count Q B)) * 2 ^ L :=
        Nat.mul_le_mul_right _ hchain
      _ = 2 * (Y / B + 1) * B := by
        rw [show (2 * ((Y / B + 1) * Nat.count Q B)) * 2 ^ L =
          2 * (Y / B + 1) * (Nat.count Q B * 2 ^ L) by ring, hQB]
      _ ≤ 2 * (Y + B) := by
        simpa [mul_assoc] using Nat.mul_le_mul_left 2 hdiv
  have hApos : 0 < A := by positivity
  have hkpos : 0 < k := by dsimp only [k]; omega
  have hscaled : k * (K * A) < k * y ^ L := (Nat.mul_lt_mul_left hkpos).2 hp
  have hlow : 2 * (C * (A * k) + D + 1 + B) < k * (K * A) := by
    dsimp only [k, K]
    nlinarith
  have hupper : k * y ^ L ≤ 2 * (C * (A * k) + D + 1 + B) := by
    simpa only [Y, X] using hmain
  exact (not_lt_of_ge hupper) (hlow.trans hscaled)

/-- **Believed (~93%), open: no bijective reversor of `U` is determined by residues.**  By
`reversor_eq_of_stepSym_eq` the candidates are countably many, one per finite table mod
`2^c₀ 3^d₀` (equivalently flip ∘ a surjective cellular automaton on the Matthews–Watts
shift), and
each must send every integer to an integer.  Evidence (2026-10-13, agent report `reversor.md`):
every table of window at most `2` sends some integer cycle to a non-integral one (the pure flip
sends the `12`-cycle through `44` to the cycle through `693999/7153`,
`7153 = 3¹² − 2¹⁹`), and the
`60` possibly-surjective window-`3` tables passing the cycle test send one of `8, 10, …, 16`
outside the integers below `10¹⁵`. -/
def AmusicalNoContinuousReversor : Prop :=
  ¬ ∃ (ι : Equiv.Perm ℤ) (c₀ d₀ : ℕ), IsAmusicalReversor ι ∧
      ∀ n n' : ℤ, n ≡ n' [ZMOD 2 ^ c₀ * 3 ^ d₀] → stepSym (ι n) = stepSym (ι n')

end CollatzMoonshot.Amusical
