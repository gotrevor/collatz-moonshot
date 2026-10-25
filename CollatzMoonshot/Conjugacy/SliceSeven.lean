/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.SliceDecay
import CollatzMoonshot.Conjugacy.Digits

/-!
# Tao 2019 §7 at the pair-sum law `Pascal(p)`: the input for `SliceCharDecay`

`SliceDecay.lean` (personal-c5) reduces `BiasDecays` to `SliceCharDecay`, the sliced Tao 1.17.
Two facts carry Tao's §7 pairing to slices: given the pair sums, each pair of gaps of a uniform
`a`-subset is uniform over its splits (the same conditional law as under iid `Geom(p)` gaps, for
every `p`), and conditioning on the slice event `T_a ≤ j < T_{a+1}` reweights each gap vector by
`(1−p)^{j − T_a} ≤ 1`.  So the normalised slice character sum is at most
`damping a p ξ / P_p(slice)`, and at `p = a/j` the slice probability is `≍ j^{−1/2}`.  What is
needed is therefore Tao's (7.5) damping bound at `Pascal(p)`, **uniformly in `p`** on the window.

**Tao's proof transfers at the paper level** (read from Tao 2019 §7, research note §12–§11 and
`experiments/conjugacy/BRIDGE3-SLICE-RECURSION.md`).  The deterministic half (the field
`θ(j, l)`, Lemma 7.4's triangles, the white points) does not involve `p`.  The pair factor
`|f(x, 3)| = |cos πθ|` (Lemma 7.2) does not involve `p`.  The holding time becomes
`Hold = (1, 3) + Σ_{i < K−1} (1, b′_i)` with `K ~ Geom(q)`, `q = P(b = 3) = 2p²(1−p)`, and `b′`
the pair sum conditioned `≠ 3`; so `E Hold = (1/q)·(1, 2/p)` (Tao's `(4, 16)` at `p = 1/2`), with
the same support, hence the same aperiodicity, and exponential tails.  Lemma 7.7's first-passage
location is `j ≈ s·p/2` instead of `s/4`.  Every slope-sensitive step (Case 2 after (7.50),
"`¼ log 9 < log 2`"; Case 3 after (7.52), "`0.8 > ¼ log 9/log 2`"; the line after (7.64)) reduces
to the single condition `p log₂ 3 < 1` (personal-c5: it is slice contraction `3^a < 2^j`), with
Tao's `0.8, 0.9` replaced by thresholds strictly between `p log₂ 3` and `1`.  At `p = 3/5`,
`p log₂ 3 = 0.951`.  The constants depend continuously on `p`, hence are uniform on `[1/5, 3/5]`.

**Measured** (`experiments/conjugacy/pascal_damping.py`, personal-c5, exact DP checked against
brute force): `sup_ξ damping` at `n = 4, 8, 12, 14` is `0.655, 0.546, 0.478, 0.452` at `p = 0.6`
and `0.310 … 0.071` at `p = 0.35`, with a steady per-2-step ratio for `p ≤ 0.65` (`0.945` at
`p = 0.6`), drifting toward `1` at `p = 0.7, 0.8`.  The refutation probe for the node below.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB
open scoped ComplexConjugate

/-- `e(−x/3^n)` for `x ∈ ℤ/3^n`. -/
noncomputable def charZ (n : ℕ) (x : ZMod (3 ^ n)) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I * ((x.val : ℕ) : ℂ) / 3 ^ n))

/-- `charZ` is the inverse of mathlib's standard additive character. -/
theorem charZ_eq_inv_stdAddChar (n : ℕ) (x : ZMod (3 ^ n)) :
    charZ n x = (ZMod.stdAddChar x)⁻¹ := by
  unfold charZ
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  simp only [Complex.exp_neg]
  push_cast
  congr 2

@[simp] theorem charZ_zero (n : ℕ) : charZ n 0 = 1 := by
  rw [charZ_eq_inv_stdAddChar]
  simp

theorem charZ_add (n : ℕ) (x y : ZMod (3 ^ n)) :
    charZ n (x + y) = charZ n x * charZ n y := by
  simp only [charZ_eq_inv_stdAddChar, AddChar.map_add_eq_mul, mul_inv_rev]
  rw [mul_comm]

theorem charZ_sum {ι : Type*} (n : ℕ) (s : Finset ι) (f : ι → ZMod (3 ^ n)) :
    charZ n (∑ i ∈ s, f i) = ∏ i ∈ s, charZ n (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, charZ_add, ih]

theorem norm_charZ (n : ℕ) (x : ZMod (3 ^ n)) : ‖charZ n x‖ = 1 := by
  rw [charZ_eq_inv_stdAddChar, norm_inv, ZMod.stdAddChar_apply]
  rw [Circle.norm_coe, inv_one]

/-- Tao's pair factor (7.4): `f(x, b) = (b−1)⁻¹ Σ_{a=1}^{b−1} e(−x(2^a + 3)/3^n)`, the conditional
expectation of the pair's character given its sum `b` (uniform over the `b − 1` splits, for any
gap law `Geom(p)`). -/
noncomputable def fPair (n : ℕ) (x : ZMod (3 ^ n)) (b : ℕ) : ℂ :=
  ((b : ℂ) - 1)⁻¹ * ∑ a ∈ Finset.Icc 1 (b - 1), charZ n (x * (2 ^ a + 3))

/-- Clearing the normalising factor in `fPair`.  Every genuine pair sum has `b ≥ 2`, so its
`b - 1` possible positive splits contribute exactly `(b - 1) * fPair`. -/
theorem sum_charZ_splits_eq_mul_fPair (n : ℕ) (x : ZMod (3 ^ n)) {b : ℕ} (hb : 2 ≤ b) :
    ∑ a ∈ Finset.Icc 1 (b - 1), charZ n (x * (2 ^ a + 3)) =
      ((b : ℂ) - 1) * fPair n x b := by
  unfold fPair
  have hne : (b : ℂ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast (show b ≠ 1 by omega))
  rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]

theorem norm_sum_charZ_splits (n : ℕ) (x : ZMod (3 ^ n)) {b : ℕ} (hb : 2 ≤ b) :
    ‖∑ a ∈ Finset.Icc 1 (b - 1), charZ n (x * (2 ^ a + 3))‖ =
      ((b : ℝ) - 1) * ‖fPair n x b‖ := by
  rw [sum_charZ_splits_eq_mul_fPair n x hb, norm_mul]
  congr 1
  rw [Complex.norm_def, Complex.normSq_apply]
  simp
  have : (1 : ℝ) ≤ b := by exact_mod_cast hb.trans' (by omega)
  rw [← sq, Real.sqrt_sq (sub_nonneg.mpr this)]

/-- The argument `x_j = ξ · 3^{2j} · 2^{−s}` at prefix pair-sum `s` (0-indexed `j`). -/
noncomputable def xArg (n ξ j s : ℕ) : ZMod (3 ^ n) :=
  (ξ : ZMod (3 ^ n)) * 3 ^ (2 * j) * (2 : ZMod (3 ^ n))⁻¹ ^ s

/-- The pair-sum law `Pascal(p)`: the sum of two iid `Geom(p)` gaps on `{1, 2, …}`,
`P(b) = (b−1) p² (1−p)^{b−2}` for `b ≥ 2`. -/
noncomputable def pascalWeight (p : ℝ) (b : ℕ) : ℝ :=
  if 2 ≤ b then ((b : ℝ) - 1) * p ^ 2 * (1 - p) ^ (b - 2) else 0

theorem pascalWeight_of_two_le (p : ℝ) {b : ℕ} (hb : 2 ≤ b) :
    pascalWeight p b = ((b : ℝ) - 1) * p ^ 2 * (1 - p) ^ (b - 2) := by
  simp [pascalWeight, hb]

theorem pascalWeight_nonneg {p : ℝ} (hp1 : p ≤ 1) (b : ℕ) :
    0 ≤ pascalWeight p b := by
  unfold pascalWeight
  split_ifs with hb
  · have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb.trans' (by omega)
    have hp' : 0 ≤ 1 - p := sub_nonneg.mpr hp1
    positivity
  · exact le_rfl

/-- The unnormalised weight of any positive split of a fixed pair sum is independent of the
split.  This is the elementary reason conditioning two geometric gaps on their sum is uniform. -/
theorem geom_split_weight_eq {p : ℝ} {g₀ g₁ b : ℕ} (hg₀ : 1 ≤ g₀) (hg₁ : 1 ≤ g₁)
    (hadd : g₀ + g₁ = b) :
    (p * (1 - p) ^ (g₀ - 1)) * (p * (1 - p) ^ (g₁ - 1)) =
      p ^ 2 * (1 - p) ^ (b - 2) := by
  have hexp : g₀ - 1 + (g₁ - 1) = g₀ + g₁ - 2 := by omega
  calc
    (p * (1 - p) ^ (g₀ - 1)) * (p * (1 - p) ^ (g₁ - 1)) =
        p ^ 2 * ((1 - p) ^ (g₀ - 1) * (1 - p) ^ (g₁ - 1)) := by ring
    _ = p ^ 2 * (1 - p) ^ (b - 2) := by rw [← pow_add, hexp, hadd]

/-- The binomial mass of the `a`-slice among `j` geometric trials. -/
noncomputable def binomialSliceWeight (j a : ℕ) (p : ℝ) : ℝ :=
  (j.choose a : ℝ) * p ^ a * (1 - p) ^ (j - a)

theorem sum_binomialSliceWeight (j : ℕ) (p : ℝ) :
    ∑ a ∈ Finset.range (j + 1), binomialSliceWeight j a p = 1 := by
  calc
    ∑ a ∈ Finset.range (j + 1), binomialSliceWeight j a p =
        ∑ a ∈ Finset.range (j + 1),
          p ^ a * (1 - p) ^ (j - a) * (j.choose a : ℝ) := by
      apply Finset.sum_congr rfl
      intro a _
      unfold binomialSliceWeight
      ring
    _ = (p + (1 - p)) ^ j := (add_pow p (1 - p) j).symm
    _ = 1 := by ring

/-- **Tao's (7.5) damping at `Pascal(p)`**:
`E_{b ~ Pascal(p)^{⌊n/2⌋}} ∏_j |f(x_j, b_j)|` with `x_j = ξ 3^{2j} 2^{−(b_0 + ⋯ + b_j)}`.
At `p = 1/2` this is the quantity Tao bounds by `n^{−A}` (his Props 7.1, 7.3). -/
noncomputable def pascalDamping (n : ℕ) (p : ℝ) (ξ : ℕ) : ℝ :=
  ∑' b : Fin (n / 2) → ℕ, (∏ j, pascalWeight p (b j)) *
    ∏ j : Fin (n / 2),
      ‖fPair n (xArg n ξ j (∑ i ∈ Finset.univ.filter (fun i : Fin (n / 2) => i ≤ j), b i)) (b j)‖

/-- **Node: Tao's damping bound at `Pascal(p)`, uniformly on `p ∈ [1/5, 3/5]`.**  The analogue of
Tao 2019 Prop 7.1 (via 7.3) with the pair-sum law tilted.  Evidence: the paper-level transfer in
the module docstring (every `p`-sensitive step reduces to `p log₂ 3 < 1`), and the measured decay.
Confidence 80% true; 60% that the `tao-collatz` §7 Lean proof generalises by re-parametrising its
probabilistic half (`HoldBasics`, `HoldLocal`, `Holding`, `FpLocation`, `BlackEdge`, `Case3`,
`ManyTriangles`, `Monotone`, `Unroll`, `Reduction`, `Bridge`) with the deterministic half
(`Setup`, `Triangles`, `White`) unchanged. -/
def PascalDampingDecay : Prop :=
  ∀ A > (0 : ℝ), ∃ C > (0 : ℝ), ∀ p : ℝ, 1 / 5 ≤ p → p ≤ 3 / 5 → ∀ n ξ : ℕ, 1 ≤ n → ¬ 3 ∣ ξ →
    pascalDamping n p ξ ≤ C * (n : ℝ) ^ (-A)

/-! ## The exact slice law -/

/-- The character attached to a set of odd-step positions.  Terras's bijection identifies the
`a`-slice with the `a`-element subsets of `[0,j)`, and the shortcut iterate is the least residue
of `wordNumer u · 2⁻ʲ` modulo `3ᵃ`. -/
noncomputable def subsetCharTerm (j a ξ : ℕ) (u : Finset ℕ) : ℂ :=
  Complex.exp
    (2 * Real.pi * Complex.I *
      ((ξ * (((wordNumer u : ZMod (3 ^ a)) *
        (2 : ZMod (3 ^ a))⁻¹ ^ j).val) : ℕ) : ℂ) / (3 ^ a : ℂ))

/-- `subsetCharTerm` is mathlib's standard positive additive character evaluated at the exact
slice residue. -/
theorem subsetCharTerm_eq_stdAddChar (j a ξ : ℕ) (u : Finset ℕ) :
    subsetCharTerm j a ξ u = ZMod.stdAddChar
      ((ξ : ZMod (3 ^ a)) *
        ((wordNumer u : ZMod (3 ^ a)) * (2 : ZMod (3 ^ a))⁻¹ ^ j)) := by
  have hcast :
      ((ξ * (((wordNumer u : ZMod (3 ^ a)) *
          (2 : ZMod (3 ^ a))⁻¹ ^ j).val) : ℕ) : ZMod (3 ^ a)) =
        (ξ : ZMod (3 ^ a)) *
          ((wordNumer u : ZMod (3 ^ a)) * (2 : ZMod (3 ^ a))⁻¹ ^ j) := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [← hcast, ZMod.stdAddChar_apply, ZMod.toCircle_natCast]
  unfold subsetCharTerm
  push_cast
  rfl

/-- Equivalently, the positive slice character is the inverse of `charZ`. -/
theorem subsetCharTerm_eq_inv_charZ (j a ξ : ℕ) (u : Finset ℕ) :
    subsetCharTerm j a ξ u =
      (charZ a ((ξ : ZMod (3 ^ a)) *
        ((wordNumer u : ZMod (3 ^ a)) * (2 : ZMod (3 ^ a))⁻¹ ^ j)))⁻¹ := by
  rw [subsetCharTerm_eq_stdAddChar, charZ_eq_inv_stdAddChar, inv_inv]

/-- The residue form of the slice character, indexed by `a`-subsets of `[0,j)`. -/
noncomputable def subsetChar (j a ξ : ℕ) : ℂ :=
  ∑ u ∈ (Finset.range j).powersetCard a, subsetCharTerm j a ξ u

/-- The shortcut iterate has the advertised truncated-Syracuse residue.  This is the exact
algebraic part of kickoff step 1; the remaining pairing argument only sees the ordered elements
of `onesSet r j`. -/
theorem tstep_iterate_cast_eq_wordNumer_inv {j a r : ℕ} (ha : oddCount r j = a) :
    (tstep^[j] r : ZMod (3 ^ a)) =
      (wordNumer (onesSet r j) : ZMod (3 ^ a)) * (2 : ZMod (3 ^ a))⁻¹ ^ j := by
  have hmod := tstep_iterate_modEq j r
  rw [ha, ← wordNumer_onesSet] at hmod
  have hz : (2 ^ j : ZMod (3 ^ a)) * (tstep^[j] r : ZMod (3 ^ a)) =
      (wordNumer (onesSet r j) : ZMod (3 ^ a)) := by
    have hc : ((2 ^ j * tstep^[j] r : ℕ) : ZMod (3 ^ a)) =
        (wordNumer (onesSet r j) : ZMod (3 ^ a)) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hc
  have hcop : Nat.Coprime 2 (3 ^ a) :=
    Nat.Coprime.pow_right a (by decide : Nat.Coprime 2 3)
  have hcancel : (2 : ZMod (3 ^ a))⁻¹ * 2 = 1 := by
    simpa [mul_comm] using ZMod.coe_mul_inv_eq_one 2 hcop
  calc
    (tstep^[j] r : ZMod (3 ^ a)) = 1 * (tstep^[j] r : ZMod (3 ^ a)) := by rw [one_mul]
    _ = (((2 : ZMod (3 ^ a))⁻¹ * 2) ^ j) * (tstep^[j] r : ZMod (3 ^ a)) := by
      rw [hcancel, one_pow]
    _ = (2 : ZMod (3 ^ a))⁻¹ ^ j *
        ((2 ^ j : ZMod (3 ^ a)) * (tstep^[j] r : ZMod (3 ^ a))) := by ring
    _ = (2 : ZMod (3 ^ a))⁻¹ ^ j * (wordNumer (onesSet r j) : ZMod (3 ^ a)) := by rw [hz]
    _ = (wordNumer (onesSet r j) : ZMod (3 ^ a)) * (2 : ZMod (3 ^ a))⁻¹ ^ j := by ring

/-- **Terras reindexing of the slice law.**  The dynamical character sum is exactly the sum over
`a`-subsets of odd-step positions of the truncated-Syracuse residue character. -/
theorem sliceChar_eq_subsetChar (j a ξ : ℕ) : sliceChar j a ξ = subsetChar j a ξ := by
  unfold sliceChar subsetChar
  refine Finset.sum_nbij (fun r => onesSet r j) ?_ ?_ ?_ ?_
  · intro r hr
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.mem_powerset.mp (onesSet_mem_powerset r j),
      card_onesSet r j |>.trans (Finset.mem_filter.mp hr).2⟩
  · intro r hr s hs hrs
    exact onesSet_injOn j
      (Finset.mem_coe.mpr (Finset.mem_filter.mp hr).1)
      (Finset.mem_coe.mpr (Finset.mem_filter.mp hs).1) hrs
  · intro u hu
    have hu' := Finset.mem_coe.mp hu
    rw [Finset.mem_powersetCard] at hu'
    rcases onesSet_surjOn j
      (Finset.mem_coe.mpr (Finset.mem_powerset.mpr hu'.1)) with ⟨r, hr, hru⟩
    refine ⟨r, ?_, hru⟩
    apply Finset.mem_coe.mpr
    rw [levelSet, Finset.mem_filter]
    refine ⟨Finset.mem_coe.mp hr, ?_⟩
    change onesSet r j = u at hru
    rw [← card_onesSet r j, hru, hu'.2]
  · intro r hr
    have hrange : r < 2 ^ j := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
    have ha : oddCount r j = a := (Finset.mem_filter.mp hr).2
    have hlt : tstep^[j] r < 3 ^ a := by
      simpa [ha] using tstep_iterate_lt_three_pow hrange
    unfold subsetCharTerm
    rw [← ZMod.val_natCast_of_lt hlt, tstep_iterate_cast_eq_wordNumer_inv ha]

/-- Terras's bijection also identifies the size of a slice with the corresponding binomial
coefficient. -/
theorem card_levelSet_eq_choose (j a : ℕ) : (levelSet j a).card = j.choose a := by
  calc
    (levelSet j a).card = ((Finset.range j).powersetCard a).card := by
      apply Finset.card_bij (fun r _ => onesSet r j)
      · intro r hr
        rw [Finset.mem_powersetCard]
        exact ⟨Finset.mem_powerset.mp (onesSet_mem_powerset r j),
          card_onesSet r j |>.trans (Finset.mem_filter.mp hr).2⟩
      · intro r hr s hs hrs
        exact onesSet_injOn j
          (Finset.mem_coe.mpr (Finset.mem_filter.mp hr).1)
          (Finset.mem_coe.mpr (Finset.mem_filter.mp hs).1) hrs
      · intro u hu
        rw [Finset.mem_powersetCard] at hu
        rcases onesSet_surjOn j
          (Finset.mem_coe.mpr (Finset.mem_powerset.mpr hu.1)) with ⟨r, hr, hru⟩
        refine ⟨r, ?_, hru⟩
        rw [levelSet, Finset.mem_filter]
        refine ⟨Finset.mem_coe.mp hr, ?_⟩
        change onesSet r j = u at hru
        rw [← card_onesSet r j, hru, hu.2]
    _ = j.choose a := by rw [Finset.card_powersetCard, Finset.card_range]

/-- For `u = {t₁ < ⋯ < tₐ} ⊆ [0,j)`, these are the reversed times
`Tₘ = j - tₐ₋₁₋ₘ`.  They are the partial sums of the positive gaps used in the
Pascal pairing. -/
def reverseOddTime (j : ℕ) (u : Finset ℕ) {a : ℕ} (hu : u.card = a) (i : Fin a) : ℕ :=
  j - u.orderEmbOfFin hu (Fin.rev i)

theorem reverseOddTime_pos {j a : ℕ} {u : Finset ℕ} (hsub : u ⊆ Finset.range j)
    (hu : u.card = a) (i : Fin a) : 0 < reverseOddTime j u hu i := by
  have hmem : u.orderEmbOfFin hu (Fin.rev i) ∈ u := Finset.orderEmbOfFin_mem u hu _
  have hlt : u.orderEmbOfFin hu (Fin.rev i) < j := Finset.mem_range.mp (hsub hmem)
  unfold reverseOddTime
  omega

theorem reverseOddTime_le (j : ℕ) (u : Finset ℕ) {a : ℕ} (hu : u.card = a)
    (i : Fin a) : reverseOddTime j u hu i ≤ j := by
  unfold reverseOddTime
  omega

theorem reverseOddTime_strictMono {j a : ℕ} {u : Finset ℕ} (hsub : u ⊆ Finset.range j)
    (hu : u.card = a) : StrictMono (reverseOddTime j u hu) := by
  intro i k hik
  have himem : u.orderEmbOfFin hu (Fin.rev i) ∈ u := Finset.orderEmbOfFin_mem u hu _
  have hkmem : u.orderEmbOfFin hu (Fin.rev k) ∈ u := Finset.orderEmbOfFin_mem u hu _
  have hil : u.orderEmbOfFin hu (Fin.rev i) < j := Finset.mem_range.mp (hsub himem)
  have hkl : u.orderEmbOfFin hu (Fin.rev k) < j := Finset.mem_range.mp (hsub hkmem)
  have hrev : Fin.rev k < Fin.rev i := Fin.rev_lt_rev.mpr hik
  have hord : u.orderEmbOfFin hu (Fin.rev k) < u.orderEmbOfFin hu (Fin.rev i) :=
    (u.orderEmbOfFin hu).lt_iff_lt.mpr hrev
  unfold reverseOddTime
  omega

/-- The positive gaps whose prefix sums are the reverse odd-step times. -/
def subsetGap (j : ℕ) (u : Finset ℕ) {a : ℕ} (hu : u.card = a + 1) : Fin (a + 1) → ℕ :=
  Fin.cases (reverseOddTime j u hu 0)
    (fun i => reverseOddTime j u hu i.succ - reverseOddTime j u hu i.castSucc)

theorem subsetGap_pos {j a : ℕ} {u : Finset ℕ} (hsub : u ⊆ Finset.range j)
    (hu : u.card = a + 1) (i : Fin (a + 1)) : 0 < subsetGap j u hu i := by
  refine Fin.cases ?_ (fun k => ?_) i
  · simpa [subsetGap] using reverseOddTime_pos hsub hu (0 : Fin (a + 1))
  · simp only [subsetGap, Fin.cases_succ]
    have hmono := reverseOddTime_strictMono hsub hu
      (show k.castSucc < k.succ from Fin.castSucc_lt_succ)
    omega

/-- The gap vector extended by zero outside its natural index range. -/
def subsetGapNat (j : ℕ) (u : Finset ℕ) {a : ℕ} (hu : u.card = a + 1) (m : ℕ) : ℕ :=
  if hm : m < a + 1 then subsetGap j u hu ⟨m, hm⟩ else 0

theorem subsetGapNat_of_lt {j a m : ℕ} {u : Finset ℕ} (hu : u.card = a + 1)
    (hm : m < a + 1) : subsetGapNat j u hu m = subsetGap j u hu ⟨m, hm⟩ := by
  simp [subsetGapNat, hm]

/-- The gaps telescope: their prefix through `k` is exactly `Tₖ`. -/
theorem sum_subsetGapNat_eq_reverseOddTime {j a : ℕ} {u : Finset ℕ}
    (hsub : u ⊆ Finset.range j) (hu : u.card = a + 1) (k : ℕ) (hk : k < a + 1) :
    ∑ m ∈ Finset.range (k + 1), subsetGapNat j u hu m =
      reverseOddTime j u hu ⟨k, hk⟩ := by
  induction k with
  | zero => simp [subsetGapNat, subsetGap]
  | succ k ih =>
      rw [Finset.sum_range_succ, ih (by omega)]
      rw [subsetGapNat_of_lt hu (by omega)]
      have hi : (⟨k + 1, hk⟩ : Fin (a + 1)) = Fin.succ ⟨k, by omega⟩ := Fin.ext rfl
      rw [hi]
      simp only [subsetGap, Fin.cases_succ]
      have hmono := reverseOddTime_strictMono hsub hu
        (show (Fin.castSucc ⟨k, by omega⟩ : Fin (a + 1)) <
          (Fin.succ ⟨k, by omega⟩ : Fin (a + 1)) from Fin.castSucc_lt_succ)
      have hfin : (⟨k, by omega⟩ : Fin (a + 1)) =
          (Fin.castSucc ⟨k, by omega⟩ : Fin (a + 1)) := Fin.ext rfl
      rw [hfin]
      omega

/-- The last partial sum lies in the slice budget `j`. -/
theorem sum_subsetGapNat_le {j a : ℕ} {u : Finset ℕ} (hsub : u ⊆ Finset.range j)
    (hu : u.card = a + 1) : ∑ m ∈ Finset.range (a + 1), subsetGapNat j u hu m ≤ j := by
  rw [sum_subsetGapNat_eq_reverseOddTime hsub hu a (by omega)]
  exact reverseOddTime_le j u hu ⟨a, by omega⟩

/-- Positive gaps are faithful coordinates on a fixed-cardinality slice. -/
theorem subsetGap_injective {j a : ℕ} {u v : Finset ℕ}
    (husub : u ⊆ Finset.range j) (hvsub : v ⊆ Finset.range j)
    (hu : u.card = a + 1) (hv : v.card = a + 1)
    (hgap : subsetGap j u hu = subsetGap j v hv) : u = v := by
  have htime : reverseOddTime j u hu = reverseOddTime j v hv := by
    funext k
    rw [← sum_subsetGapNat_eq_reverseOddTime husub hu k (by omega),
      ← sum_subsetGapNat_eq_reverseOddTime hvsub hv k (by omega)]
    apply Finset.sum_congr rfl
    intro m hm
    have hm' : m < a + 1 := by
      have : m < (k : ℕ) + 1 := Finset.mem_range.mp hm
      omega
    rw [subsetGapNat_of_lt hu hm', subsetGapNat_of_lt hv hm', hgap]
  have hord : u.orderEmbOfFin hu = v.orderEmbOfFin hv := by
    ext i
    have hru := congr_fun htime (Fin.rev i)
    have humem : u.orderEmbOfFin hu i ∈ u := u.orderEmbOfFin_mem hu i
    have hvmem : v.orderEmbOfFin hv i ∈ v := v.orderEmbOfFin_mem hv i
    have hult : u.orderEmbOfFin hu i < j := Finset.mem_range.mp (husub humem)
    have hvlt : v.orderEmbOfFin hv i < j := Finset.mem_range.mp (hvsub hvmem)
    simp only [reverseOddTime, Fin.rev_rev] at hru
    omega
  rw [← u.image_orderEmbOfFin_univ hu, ← v.image_orderEmbOfFin_univ hv, hord]

/-! ## The inverse gap coordinates -/

/-- Extend a finite positive-gap vector by zero. -/
def gapAtNat {a : ℕ} (g : Fin a → ℕ) (m : ℕ) : ℕ :=
  if hm : m < a then g ⟨m, hm⟩ else 0

theorem gapAtNat_of_lt {a m : ℕ} (g : Fin a → ℕ) (hm : m < a) :
    gapAtNat g m = g ⟨m, hm⟩ := by
  simp [gapAtNat, hm]

/-- The prefix time represented by a positive-gap vector. -/
def gapTime {a : ℕ} (g : Fin a → ℕ) (i : Fin a) : ℕ :=
  ∑ m ∈ Finset.range ((i : ℕ) + 1), gapAtNat g m

theorem gapTime_zero {a : ℕ} (g : Fin (a + 1) → ℕ) :
    gapTime g 0 = g 0 := by
  simp [gapTime, gapAtNat]

theorem gapTime_succ_sub {a : ℕ} (g : Fin (a + 1) → ℕ) (i : Fin a) :
    gapTime g i.succ - gapTime g i.castSucc = g i.succ := by
  simp only [gapTime, Fin.val_succ, Fin.val_castSucc, Finset.sum_range_succ]
  rw [Nat.add_sub_cancel_left]
  rw [gapAtNat_of_lt g (by omega)]
  congr

theorem gapTime_succ {a : ℕ} (g : Fin (a + 1) → ℕ) (i : Fin a) :
    gapTime g i.succ = gapTime g i.castSucc + g i.succ := by
  simp only [gapTime, Fin.val_succ, Fin.val_castSucc, Finset.sum_range_succ]
  simp [gapAtNat]
  apply congrArg g
  exact Fin.ext rfl

theorem gapTime_pos {a : ℕ} {g : Fin a → ℕ} (hg : ∀ i, 0 < g i) (i : Fin a) :
    0 < gapTime g i := by
  have hterm : 0 < gapAtNat g (i : ℕ) := by
    rw [gapAtNat_of_lt g i.isLt]
    exact hg i
  exact hterm.trans_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.mpr (by omega)))

theorem gapTime_le_sum {a : ℕ} (g : Fin a → ℕ) (i : Fin a) :
    gapTime g i ≤ ∑ k, g k := by
  have hfull : ∑ m ∈ Finset.range a, gapAtNat g m = ∑ k, g k := by
    calc
      ∑ m ∈ Finset.range a, gapAtNat g m =
          ∑ k : Fin a, gapAtNat g (k : ℕ) := by rw [Fin.sum_univ_eq_sum_range]
      _ = ∑ k, g k := by
        apply Finset.sum_congr rfl
        intro k _
        rw [gapAtNat_of_lt g k.isLt]
  rw [← hfull]
  unfold gapTime
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) ?_
  intro m _ _
  exact Nat.zero_le _

theorem gapTime_strictMono {a : ℕ} {g : Fin a → ℕ} (hg : ∀ i, 0 < g i) :
    StrictMono (gapTime g) := by
  cases a with
  | zero => exact fun i => Fin.elim0 i
  | succ a =>
      rw [Fin.strictMono_iff_lt_succ]
      intro i
      simp only [gapTime, Fin.val_castSucc, Fin.val_succ, Finset.sum_range_succ]
      have hpos : 0 < gapAtNat g ((i : ℕ) + 1) := by
        rw [gapAtNat_of_lt g (by omega)]
        exact hg i.succ
      omega

/-- Recover the original odd-step positions from a positive-gap vector. -/
def gapPosition (j : ℕ) {a : ℕ} (g : Fin a → ℕ) (i : Fin a) : ℕ :=
  j - gapTime g (Fin.rev i)

theorem gapPosition_strictMono {j a : ℕ} {g : Fin a → ℕ} (hg : ∀ i, 0 < g i)
    (hsum : ∑ i, g i ≤ j) : StrictMono (gapPosition j g) := by
  intro i k hik
  have hrev : Fin.rev k < Fin.rev i := Fin.rev_lt_rev.mpr hik
  have htime : gapTime g (Fin.rev k) < gapTime g (Fin.rev i) := gapTime_strictMono hg hrev
  have hile : gapTime g (Fin.rev i) ≤ j := (gapTime_le_sum g _).trans hsum
  have hkle : gapTime g (Fin.rev k) ≤ j := (gapTime_le_sum g _).trans hsum
  unfold gapPosition
  omega

/-- The subset of odd-step positions represented by a positive-gap vector. -/
def gapSubset (j : ℕ) {a : ℕ} (g : Fin a → ℕ) : Finset ℕ :=
  Finset.image (gapPosition j g) Finset.univ

theorem card_gapSubset {j a : ℕ} {g : Fin a → ℕ} (hg : ∀ i, 0 < g i)
    (hsum : ∑ i, g i ≤ j) : (gapSubset j g).card = a := by
  unfold gapSubset
  rw [Finset.card_image_of_injective _ (gapPosition_strictMono hg hsum).injective,
    Finset.card_univ, Fintype.card_fin]

theorem gapSubset_subset_range {j a : ℕ} {g : Fin a → ℕ} (hg : ∀ i, 0 < g i)
    (hsum : ∑ i, g i ≤ j) : gapSubset j g ⊆ Finset.range j := by
  intro t ht
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ht
  rw [Finset.mem_range]
  have hpos := gapTime_pos hg (Fin.rev i)
  have hle : gapTime g (Fin.rev i) ≤ j := (gapTime_le_sum g _).trans hsum
  unfold gapPosition
  omega

theorem orderEmbOfFin_gapSubset {j a : ℕ} {g : Fin a → ℕ} (hg : ∀ i, 0 < g i)
    (hsum : ∑ i, g i ≤ j) :
    (gapSubset j g).orderEmbOfFin (card_gapSubset hg hsum) =
      OrderEmbedding.ofStrictMono (gapPosition j g) (gapPosition_strictMono hg hsum) := by
  symm
  apply Finset.orderEmbOfFin_unique'
  intro i
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

theorem reverseOddTime_gapSubset {j a : ℕ} {g : Fin a → ℕ} (hg : ∀ i, 0 < g i)
    (hsum : ∑ i, g i ≤ j) (i : Fin a) :
    reverseOddTime j (gapSubset j g) (card_gapSubset hg hsum) i = gapTime g i := by
  have hle : gapTime g i ≤ j := (gapTime_le_sum g i).trans hsum
  unfold reverseOddTime
  rw [orderEmbOfFin_gapSubset hg hsum]
  simp only [OrderEmbedding.coe_ofStrictMono, gapPosition, Fin.rev_rev]
  omega

/-- `gapSubset` is a right inverse to the positive-gap coordinate map. -/
theorem subsetGap_gapSubset {j a : ℕ} {g : Fin (a + 1) → ℕ} (hg : ∀ i, 0 < g i)
    (hsum : ∑ i, g i ≤ j) :
    subsetGap j (gapSubset j g) (card_gapSubset hg hsum) = g := by
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · simp only [subsetGap, Fin.cases_zero]
    rw [reverseOddTime_gapSubset hg hsum, gapTime_zero]
  · simp only [subsetGap, Fin.cases_succ]
    rw [reverseOddTime_gapSubset hg hsum, reverseOddTime_gapSubset hg hsum,
      gapTime_succ_sub]

/-- The finite set of positive `a`-gap vectors whose total is at most `j`. -/
def gapVectorFinset (j a : ℕ) : Finset (Fin a → ℕ) :=
  (Fintype.piFinset fun _ : Fin a => Finset.Icc 1 j).filter (fun g => ∑ i, g i ≤ j)

theorem mem_gapVectorFinset {j a : ℕ} {g : Fin a → ℕ} :
    g ∈ gapVectorFinset j a ↔ (∀ i, 0 < g i) ∧ ∑ i, g i ≤ j := by
  simp only [gapVectorFinset, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
  constructor
  · rintro ⟨hg, hsum⟩
    exact ⟨fun i => Nat.zero_lt_of_lt (hg i).1, hsum⟩
  · rintro ⟨hg, hsum⟩
    refine ⟨fun i => ⟨hg i, ?_⟩, hsum⟩
    exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hsum

theorem sum_gapAtNat {a : ℕ} (g : Fin a → ℕ) :
    ∑ m ∈ Finset.range a, gapAtNat g m = ∑ i, g i := by
  calc
    ∑ m ∈ Finset.range a, gapAtNat g m =
        ∑ i : Fin a, gapAtNat g (i : ℕ) := by rw [Fin.sum_univ_eq_sum_range]
    _ = ∑ i, g i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [gapAtNat_of_lt g i.isLt]

/-- The positive gaps of an `a`-element subset, indexed directly by `Fin a`.  This version avoids
the successor-shaped index in `subsetGap` and is convenient for the global reindexing. -/
def subsetGaps (j : ℕ) (u : Finset ℕ) {a : ℕ} (hu : u.card = a) (i : Fin a) : ℕ :=
  if hi : (i : ℕ) = 0 then reverseOddTime j u hu i
  else reverseOddTime j u hu i -
    reverseOddTime j u hu ⟨(i : ℕ) - 1, by omega⟩

theorem subsetGaps_zero {j a : ℕ} (u : Finset ℕ) (hu : u.card = a + 1) :
    subsetGaps j u hu 0 = reverseOddTime j u hu 0 := by
  simp [subsetGaps]

theorem subsetGaps_succ {j a : ℕ} (u : Finset ℕ) (hu : u.card = a + 1) (i : Fin a) :
    subsetGaps j u hu i.succ =
      reverseOddTime j u hu i.succ - reverseOddTime j u hu i.castSucc := by
  simp only [subsetGaps, Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false,
    ↓reduceDIte]
  congr 2

theorem subsetGaps_pos {j a : ℕ} {u : Finset ℕ} (hsub : u ⊆ Finset.range j)
    (hu : u.card = a) (i : Fin a) : 0 < subsetGaps j u hu i := by
  unfold subsetGaps
  split_ifs with hi
  · exact reverseOddTime_pos hsub hu i
  · have hprev : (⟨(i : ℕ) - 1, by omega⟩ : Fin a) < i := by
      change (i : ℕ) - 1 < (i : ℕ)
      omega
    exact Nat.sub_pos_of_lt (reverseOddTime_strictMono hsub hu hprev)

theorem gapTime_subsetGaps {j a : ℕ} {u : Finset ℕ} (hsub : u ⊆ Finset.range j)
    (hu : u.card = a) (i : Fin a) :
    gapTime (subsetGaps j u hu) i = reverseOddTime j u hu i := by
  cases a with
  | zero => exact Fin.elim0 i
  | succ a =>
      induction i using Fin.induction with
      | zero => rw [gapTime_zero, subsetGaps_zero]
      | succ i ih =>
          rw [gapTime_succ, ih, subsetGaps_succ]
          have hmono := reverseOddTime_strictMono hsub hu
            (show i.castSucc < i.succ from Fin.castSucc_lt_succ)
          omega

theorem subsetGaps_mem_gapVectorFinset {j a : ℕ} {u : Finset ℕ}
    (hsub : u ⊆ Finset.range j) (hu : u.card = a) :
    subsetGaps j u hu ∈ gapVectorFinset j a := by
  rw [mem_gapVectorFinset]
  refine ⟨subsetGaps_pos hsub hu, ?_⟩
  by_cases ha : a = 0
  · subst a
    let : IsEmpty (Fin u.card) := by rw [ha]; infer_instance
    rw [Fintype.sum_empty]
    exact Nat.zero_le j
  · have ha' : 0 < a := Nat.pos_of_ne_zero ha
    let last : Fin a := ⟨a - 1, by omega⟩
    have htime := gapTime_subsetGaps hsub hu last
    have hle := reverseOddTime_le j u hu last
    rw [← sum_gapAtNat (subsetGaps j u hu)]
    have hfull : ∑ m ∈ Finset.range a, gapAtNat (subsetGaps j u hu) m =
        gapTime (subsetGaps j u hu) last := by
      unfold gapTime last
      congr 2
      dsimp
      omega
    rw [hfull, htime]
    exact hle

theorem subsetGaps_injective {j a : ℕ} {u v : Finset ℕ}
    (husub : u ⊆ Finset.range j) (hvsub : v ⊆ Finset.range j)
    (hu : u.card = a) (hv : v.card = a)
    (hgap : subsetGaps j u hu = subsetGaps j v hv) : u = v := by
  have htime : reverseOddTime j u hu = reverseOddTime j v hv := by
    funext i
    rw [← gapTime_subsetGaps husub hu i, ← gapTime_subsetGaps hvsub hv i, hgap]
  have hord : u.orderEmbOfFin hu = v.orderEmbOfFin hv := by
    ext i
    have hru := congr_fun htime (Fin.rev i)
    have humem : u.orderEmbOfFin hu i ∈ u := u.orderEmbOfFin_mem hu i
    have hvmem : v.orderEmbOfFin hv i ∈ v := v.orderEmbOfFin_mem hv i
    have hult : u.orderEmbOfFin hu i < j := Finset.mem_range.mp (husub humem)
    have hvlt : v.orderEmbOfFin hv i < j := Finset.mem_range.mp (hvsub hvmem)
    simp only [reverseOddTime, Fin.rev_rev] at hru
    omega
  rw [← u.image_orderEmbOfFin_univ hu, ← v.image_orderEmbOfFin_univ hv, hord]

theorem subsetGaps_gapSubset {j a : ℕ} {g : Fin a → ℕ} (hg : ∀ i, 0 < g i)
    (hsum : ∑ i, g i ≤ j) :
    subsetGaps j (gapSubset j g) (card_gapSubset hg hsum) = g := by
  funext i
  cases a with
  | zero => exact Fin.elim0 i
  | succ a =>
      induction i using Fin.induction with
      | zero =>
          rw [subsetGaps_zero, reverseOddTime_gapSubset hg hsum, gapTime_zero]
      | succ i =>
          rw [subsetGaps_succ, reverseOddTime_gapSubset hg hsum,
            reverseOddTime_gapSubset hg hsum, gapTime_succ_sub]

/-- Reconstructing a slice subset from its positive gaps returns the subset. -/
theorem gapSubset_subsetGaps {j a : ℕ} {u : Finset ℕ}
    (hsub : u ⊆ Finset.range j) (hu : u.card = a) :
    gapSubset j (subsetGaps j u hu) = u := by
  have hmem := subsetGaps_mem_gapVectorFinset hsub hu
  have hg := (mem_gapVectorFinset.mp hmem).1
  have hsum := (mem_gapVectorFinset.mp hmem).2
  apply subsetGaps_injective (gapSubset_subset_range hg hsum) hsub
    (card_gapSubset hg hsum) hu
  exact subsetGaps_gapSubset hg hsum

/-- The exact Terras subset/gap-coordinate bijection on a slice. -/
noncomputable def sliceGapEquiv (j a : ℕ) :
    ↥((Finset.range j).powersetCard a) ≃ ↥(gapVectorFinset j a) where
  toFun u :=
    ⟨subsetGaps j u.1 (Finset.mem_powersetCard.mp u.2).2,
      subsetGaps_mem_gapVectorFinset
        (Finset.mem_powersetCard.mp u.2).1 (Finset.mem_powersetCard.mp u.2).2⟩
  invFun g :=
    ⟨gapSubset j g.1, Finset.mem_powersetCard.mpr
      ⟨gapSubset_subset_range (mem_gapVectorFinset.mp g.2).1 (mem_gapVectorFinset.mp g.2).2,
        card_gapSubset (mem_gapVectorFinset.mp g.2).1 (mem_gapVectorFinset.mp g.2).2⟩⟩
  left_inv u := by
    apply Subtype.ext
    exact gapSubset_subsetGaps
      (Finset.mem_powersetCard.mp u.2).1 (Finset.mem_powersetCard.mp u.2).2
  right_inv g := by
    apply Subtype.ext
    exact subsetGaps_gapSubset (mem_gapVectorFinset.mp g.2).1
      (mem_gapVectorFinset.mp g.2).2

/-- Cancellation of a positive power of `2` against a longer inverse power modulo `3^a`. -/
theorem two_pow_mul_inv_pow {a d j : ℕ} (hd : d ≤ j) :
    (2 : ZMod (3 ^ a)) ^ d * (2 : ZMod (3 ^ a))⁻¹ ^ j =
      (2 : ZMod (3 ^ a))⁻¹ ^ (j - d) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hd
  have hcop : Nat.Coprime 2 (3 ^ a) :=
    Nat.Coprime.pow_right a (by decide : Nat.Coprime 2 3)
  have hunit : (2 : ZMod (3 ^ a)) * (2 : ZMod (3 ^ a))⁻¹ = 1 :=
    ZMod.coe_mul_inv_eq_one 2 hcop
  rw [Nat.add_sub_cancel_left, pow_add]
  calc
    (2 : ZMod (3 ^ a)) ^ d *
        ((2 : ZMod (3 ^ a))⁻¹ ^ d * (2 : ZMod (3 ^ a))⁻¹ ^ t) =
        ((2 : ZMod (3 ^ a)) * (2 : ZMod (3 ^ a))⁻¹) ^ d *
          (2 : ZMod (3 ^ a))⁻¹ ^ t := by ring
    _ = (2 : ZMod (3 ^ a))⁻¹ ^ t := by rw [hunit, one_pow, one_mul]

/-- Pair consecutive gaps. -/
def gapPairSum (g : ℕ → ℕ) (q : ℕ) : ℕ := g (2 * q) + g (2 * q + 1)

/-- Prefix sums of pair sums are the corresponding even-length prefix sums of gaps. -/
theorem sum_gapPairSum_range (g : ℕ → ℕ) (q : ℕ) :
    ∑ i ∈ Finset.range q, gapPairSum g i = ∑ m ∈ Finset.range (2 * q), g m := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Finset.sum_range_succ, ih, Nat.mul_add, Nat.mul_one,
        Finset.sum_range_succ, Finset.sum_range_succ]
      unfold gapPairSum
      ring

/-- Algebra behind one paired character factor.  If the two gaps are `g₀,g₁` after an earlier
prefix of length `s`, the two consecutive residue summands combine into the factor
`2^g₁ + 3` at the end of the pair. -/
theorem two_residue_terms_eq_pairFactor (n q s g₀ g₁ : ℕ) :
    (3 : ZMod (3 ^ n)) ^ (2 * q) *
          (2 : ZMod (3 ^ n))⁻¹ ^ (s + g₀) +
        (3 : ZMod (3 ^ n)) ^ (2 * q + 1) *
          (2 : ZMod (3 ^ n))⁻¹ ^ (s + g₀ + g₁) =
      (3 : ZMod (3 ^ n)) ^ (2 * q) *
        (2 : ZMod (3 ^ n))⁻¹ ^ (s + g₀ + g₁) *
          ((2 : ZMod (3 ^ n)) ^ g₁ + 3) := by
  have hle : g₁ ≤ s + g₀ + g₁ := by omega
  have hcancel := two_pow_mul_inv_pow (a := n) hle
  have hsub : s + g₀ + g₁ - g₁ = s + g₀ := by omega
  rw [hsub] at hcancel
  rw [pow_succ]
  calc
    (3 : ZMod (3 ^ n)) ^ (2 * q) * (2 : ZMod (3 ^ n))⁻¹ ^ (s + g₀) +
        ((3 : ZMod (3 ^ n)) ^ (2 * q) * 3) *
          (2 : ZMod (3 ^ n))⁻¹ ^ (s + g₀ + g₁) =
      (3 : ZMod (3 ^ n)) ^ (2 * q) *
        ((2 : ZMod (3 ^ n))⁻¹ ^ (s + g₀) +
          3 * (2 : ZMod (3 ^ n))⁻¹ ^ (s + g₀ + g₁)) := by ring
    _ = (3 : ZMod (3 ^ n)) ^ (2 * q) *
        ((2 : ZMod (3 ^ n)) ^ g₁ *
            (2 : ZMod (3 ^ n))⁻¹ ^ (s + g₀ + g₁) +
          3 * (2 : ZMod (3 ^ n))⁻¹ ^ (s + g₀ + g₁)) := by rw [hcancel]
    _ = (3 : ZMod (3 ^ n)) ^ (2 * q) *
        (2 : ZMod (3 ^ n))⁻¹ ^ (s + g₀ + g₁) *
          ((2 : ZMod (3 ^ n)) ^ g₁ + 3) := by ring

/-- One adjacent pair of gap-character factors is exactly a summand appearing in `fPair`. -/
theorem charZ_two_gap_terms (n ξ q s g₀ g₁ : ℕ) :
    charZ n ((ξ : ZMod (3 ^ n)) * (3 : ZMod (3 ^ n)) ^ (2 * q) *
        (2 : ZMod (3 ^ n))⁻¹ ^ (s + g₀)) *
      charZ n ((ξ : ZMod (3 ^ n)) * (3 : ZMod (3 ^ n)) ^ (2 * q + 1) *
        (2 : ZMod (3 ^ n))⁻¹ ^ (s + g₀ + g₁)) =
    charZ n (xArg n ξ q (s + g₀ + g₁) *
      ((2 : ZMod (3 ^ n)) ^ g₁ + 3)) := by
  rw [← charZ_add]
  apply congrArg (charZ n)
  calc
    (ξ : ZMod (3 ^ n)) * 3 ^ (2 * q) * 2⁻¹ ^ (s + g₀) +
        (ξ : ZMod (3 ^ n)) * 3 ^ (2 * q + 1) * 2⁻¹ ^ (s + g₀ + g₁) =
      (ξ : ZMod (3 ^ n)) *
        (3 ^ (2 * q) * 2⁻¹ ^ (s + g₀) +
          3 ^ (2 * q + 1) * 2⁻¹ ^ (s + g₀ + g₁)) := by ring
    _ = (ξ : ZMod (3 ^ n)) *
        (3 ^ (2 * q) * 2⁻¹ ^ (s + g₀ + g₁) * (2 ^ g₁ + 3)) := by
      rw [two_residue_terms_eq_pairFactor]
    _ = xArg n ξ q (s + g₀ + g₁) * (2 ^ g₁ + 3) := by
      unfold xArg
      ring

/-- The pair-sum vector attached to a slice subset. -/
def subsetPairSum (j : ℕ) (u : Finset ℕ) {a : ℕ} (hu : u.card = a) : Fin (a / 2) → ℕ :=
  fun q =>
    have ha : 0 < a := by have := q.isLt; omega
    gapPairSum (subsetGapNat j u (show u.card = (a - 1) + 1 by omega)) q

theorem subsetPairSum_two_le {j a : ℕ} {u : Finset ℕ} (hsub : u ⊆ Finset.range j)
    (hu : u.card = a) (q : Fin (a / 2)) : 2 ≤ subsetPairSum j u hu q := by
  have ha : 0 < a := by have := q.isLt; omega
  have hcard : u.card = (a - 1) + 1 := by omega
  have h0 : 2 * (q : ℕ) < a := by omega
  have h1 : 2 * (q : ℕ) + 1 < a := by omega
  unfold subsetPairSum gapPairSum
  change 2 ≤ subsetGapNat j u hcard (2 * (q : ℕ)) +
    subsetGapNat j u hcard (2 * (q : ℕ) + 1)
  rw [subsetGapNat_of_lt hcard (by omega), subsetGapNat_of_lt hcard (by omega)]
  have hp0 := subsetGap_pos hsub hcard ⟨2 * (q : ℕ), by omega⟩
  have hp1 := subsetGap_pos hsub hcard ⟨2 * (q : ℕ) + 1, by omega⟩
  omega

/-! ## Reindexing the numerator by reverse times -/

/-- The elements of `u` above its `i`-th ordered element are exactly the images of the
indices above `i`. -/
theorem filter_lt_orderEmbOfFin {u : Finset ℕ} {a : ℕ} (hu : u.card = a) (i : Fin a) :
    u.filter (fun e => u.orderEmbOfFin hu i < e) =
      (Finset.Ioi i).image (u.orderEmbOfFin hu) := by
  ext e
  constructor
  · intro he
    have heu : e ∈ u := (Finset.mem_filter.mp he).1
    obtain ⟨k, hk⟩ := Set.ext_iff.mp (u.range_orderEmbOfFin hu) e |>.mpr heu
    refine Finset.mem_image.mpr ⟨k, ?_, hk⟩
    exact Finset.mem_Ioi.mpr ((u.orderEmbOfFin hu).lt_iff_lt.mp (hk ▸ (Finset.mem_filter.mp he).2))
  · intro he
    obtain ⟨k, hki, rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_filter.mpr ⟨u.orderEmbOfFin_mem hu k,
      (u.orderEmbOfFin hu).lt_iff_lt.mpr (Finset.mem_Ioi.mp hki)⟩

/-- In ordered coordinates, the exponent of `3` in `wordNumer` is the number of remaining
elements. -/
theorem card_filter_orderEmbOfFin_lt {u : Finset ℕ} {a : ℕ} (hu : u.card = a) (i : Fin a) :
    (u.filter (fun e => u.orderEmbOfFin hu i < e)).card = a - 1 - i := by
  rw [filter_lt_orderEmbOfFin hu i, Finset.card_image_of_injective _ (u.orderEmbOfFin hu).injective,
    Fin.card_Ioi]

/-- `wordNumer` written in the increasing enumeration of its support. -/
theorem wordNumer_eq_sum_orderEmbOfFin {u : Finset ℕ} {a : ℕ} (hu : u.card = a) :
    wordNumer u = ∑ i : Fin a, 3 ^ (a - 1 - i) * 2 ^ (u.orderEmbOfFin hu i) := by
  unfold wordNumer
  calc
    ∑ d ∈ u, 3 ^ (u.filter (fun e => d < e)).card * 2 ^ d =
        ∑ d ∈ Finset.image (u.orderEmbOfFin hu) Finset.univ,
          3 ^ (u.filter (fun e => d < e)).card * 2 ^ d := by
      rw [u.image_orderEmbOfFin_univ hu]
    _ = ∑ i : Fin a, 3 ^ (a - 1 - i) * 2 ^ (u.orderEmbOfFin hu i) := by
      rw [Finset.sum_image (u.orderEmbOfFin hu).injective.injOn]
      apply Finset.sum_congr rfl
      intro i _
      rw [card_filter_orderEmbOfFin_lt hu i]

/-- The exact positive-gap form of the truncated Syracuse residue.  The exponent of `3` is now
the reverse index, and the exponent of `2⁻¹` is the corresponding reverse odd time. -/
theorem wordNumer_mul_inv_eq_sum_reverseOddTime {j a : ℕ} {u : Finset ℕ}
    (hsub : u ⊆ Finset.range j) (hu : u.card = a) :
    (wordNumer u : ZMod (3 ^ a)) * (2 : ZMod (3 ^ a))⁻¹ ^ j =
      ∑ m : Fin a, (3 : ZMod (3 ^ a)) ^ (m : ℕ) *
        (2 : ZMod (3 ^ a))⁻¹ ^ reverseOddTime j u hu m := by
  rw [wordNumer_eq_sum_orderEmbOfFin hu]
  push_cast
  rw [Finset.sum_mul]
  apply Fintype.sum_equiv (Fin.revPerm : Equiv.Perm (Fin a)) _ _
  intro m
  have hmem : u.orderEmbOfFin hu m ∈ u := u.orderEmbOfFin_mem hu _
  have hlt : u.orderEmbOfFin hu m < j := Finset.mem_range.mp (hsub hmem)
  have hrev : a - 1 - (m : ℕ) = (Fin.rev m : ℕ) := by
    simp only [Fin.rev]
    omega
  change (3 : ZMod (3 ^ a)) ^ (a - 1 - (m : ℕ)) *
      (2 : ZMod (3 ^ a)) ^ (u.orderEmbOfFin hu m) *
        (2 : ZMod (3 ^ a))⁻¹ ^ j =
    (3 : ZMod (3 ^ a)) ^ (Fin.rev m : ℕ) *
      (2 : ZMod (3 ^ a))⁻¹ ^ reverseOddTime j u hu (Fin.rev m)
  rw [hrev, mul_assoc, two_pow_mul_inv_pow hlt.le]
  simp [reverseOddTime]

/-- The slice residue in positive-gap coordinates: the exponent of `2⁻¹` in the `m`-th
summand is the prefix sum through the `m`-th gap. -/
theorem wordNumer_mul_inv_eq_sum_subsetGap {j a : ℕ} {u : Finset ℕ}
    (hsub : u ⊆ Finset.range j) (hu : u.card = a + 1) :
    (wordNumer u : ZMod (3 ^ (a + 1))) * (2 : ZMod (3 ^ (a + 1)))⁻¹ ^ j =
      ∑ m : Fin (a + 1), (3 : ZMod (3 ^ (a + 1))) ^ (m : ℕ) *
        (2 : ZMod (3 ^ (a + 1)))⁻¹ ^
          (∑ k ∈ Finset.range ((m : ℕ) + 1), subsetGapNat j u hu k) := by
  rw [wordNumer_mul_inv_eq_sum_reverseOddTime hsub hu]
  apply Finset.sum_congr rfl
  intro m _
  rw [sum_subsetGapNat_eq_reverseOddTime hsub hu m (by omega)]

/-- After passing to the negative character, the exact slice residue is a product of one
unit-modulus factor per gap prefix. -/
theorem charZ_sliceResidue_eq_prod {j a ξ : ℕ} {u : Finset ℕ}
    (hsub : u ⊆ Finset.range j) (hu : u.card = a) :
    charZ a ((ξ : ZMod (3 ^ a)) *
      ((wordNumer u : ZMod (3 ^ a)) * (2 : ZMod (3 ^ a))⁻¹ ^ j)) =
      ∏ m : Fin a, charZ a
        ((ξ : ZMod (3 ^ a)) * (3 : ZMod (3 ^ a)) ^ (m : ℕ) *
          (2 : ZMod (3 ^ a))⁻¹ ^ reverseOddTime j u hu m) := by
  rw [wordNumer_mul_inv_eq_sum_reverseOddTime hsub hu, Finset.mul_sum]
  rw [charZ_sum a Finset.univ]
  apply Finset.prod_congr rfl
  intro m _
  apply congrArg (charZ a)
  ring

/-! ## The slice character in gap coordinates -/

/-- The negative character attached to a positive-gap vector. -/
noncomputable def gapCharTerm (a ξ : ℕ) (g : Fin a → ℕ) : ℂ :=
  ∏ m : Fin a, charZ a
    ((ξ : ZMod (3 ^ a)) * (3 : ZMod (3 ^ a)) ^ (m : ℕ) *
      (2 : ZMod (3 ^ a))⁻¹ ^ gapTime g m)

/-- The negative-character version of the subset sum.  It is the complex conjugate of
`subsetChar`, hence has the same norm. -/
noncomputable def negativeSubsetChar (j a ξ : ℕ) : ℂ :=
  ∑ u ∈ (Finset.range j).powersetCard a,
    charZ a ((ξ : ZMod (3 ^ a)) *
      ((wordNumer u : ZMod (3 ^ a)) * (2 : ZMod (3 ^ a))⁻¹ ^ j))

theorem subsetChar_eq_conj_negativeSubsetChar (j a ξ : ℕ) :
    subsetChar j a ξ = conj (negativeSubsetChar j a ξ) := by
  unfold subsetChar negativeSubsetChar
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [subsetCharTerm_eq_inv_charZ, Complex.inv_eq_conj (norm_charZ _ _)]

theorem norm_subsetChar_eq_norm_negativeSubsetChar (j a ξ : ℕ) :
    ‖subsetChar j a ξ‖ = ‖negativeSubsetChar j a ξ‖ := by
  rw [subsetChar_eq_conj_negativeSubsetChar, Complex.norm_conj]

theorem charZ_sliceResidue_eq_gapCharTerm {j a ξ : ℕ} {u : Finset ℕ}
    (hsub : u ⊆ Finset.range j) (hu : u.card = a) :
    charZ a ((ξ : ZMod (3 ^ a)) *
      ((wordNumer u : ZMod (3 ^ a)) * (2 : ZMod (3 ^ a))⁻¹ ^ j)) =
      gapCharTerm a ξ (subsetGaps j u hu) := by
  rw [charZ_sliceResidue_eq_prod hsub hu]
  unfold gapCharTerm
  apply Finset.prod_congr rfl
  intro m _
  rw [gapTime_subsetGaps hsub hu]

/-- Exact finite reindexing of the slice character by its positive gaps. -/
theorem negativeSubsetChar_eq_sum_gapVector (j a ξ : ℕ) :
    negativeSubsetChar j a ξ = ∑ g ∈ gapVectorFinset j a, gapCharTerm a ξ g := by
  unfold negativeSubsetChar
  calc
    ∑ u ∈ (Finset.range j).powersetCard a,
        charZ a ((ξ : ZMod (3 ^ a)) *
          ((wordNumer u : ZMod (3 ^ a)) * (2 : ZMod (3 ^ a))⁻¹ ^ j)) =
      ∑ u : ↥((Finset.range j).powersetCard a),
        charZ a ((ξ : ZMod (3 ^ a)) *
          ((wordNumer u.1 : ZMod (3 ^ a)) * (2 : ZMod (3 ^ a))⁻¹ ^ j)) := by
        exact (Finset.sum_coe_sort ((Finset.range j).powersetCard a)
          (fun u => charZ a ((ξ : ZMod (3 ^ a)) *
            ((wordNumer u : ZMod (3 ^ a)) * (2 : ZMod (3 ^ a))⁻¹ ^ j)))).symm
    _ = ∑ g : ↥(gapVectorFinset j a), gapCharTerm a ξ g.1 := by
      apply Fintype.sum_equiv (sliceGapEquiv j a)
      intro u
      exact charZ_sliceResidue_eq_gapCharTerm
        (Finset.mem_powersetCard.mp u.2).1 (Finset.mem_powersetCard.mp u.2).2
    _ = ∑ g ∈ gapVectorFinset j a, gapCharTerm a ξ g := by
      exact Finset.sum_coe_sort (gapVectorFinset j a) (gapCharTerm a ξ)

/-! ## Pair coordinates -/

/-- Split `Fin a` into `a / 2` adjacent pairs and the `a % 2` terminal coordinates. -/
def gapBlockEquiv (a : ℕ) :
    (Fin (a / 2) × Fin 2) ⊕ Fin (a % 2) ≃ Fin a :=
  (Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans <|
    finSumFinEquiv.trans (finCongr (by
      have := Nat.div_add_mod a 2
      omega))

/-- Coordinate `s=0,1` of pair `q`. -/
def pairGapIndex (a : ℕ) (q : Fin (a / 2)) (s : Fin 2) : Fin a :=
  gapBlockEquiv a (Sum.inl (q, s))

/-- A possible unpaired terminal coordinate. -/
def tailGapIndex (a : ℕ) (t : Fin (a % 2)) : Fin a :=
  gapBlockEquiv a (Sum.inr t)

@[simp] theorem pairGapIndex_val (a : ℕ) (q : Fin (a / 2)) (s : Fin 2) :
    (pairGapIndex a q s : ℕ) = 2 * (q : ℕ) + (s : ℕ) := by
  simp [pairGapIndex, gapBlockEquiv, finProdFinEquiv, finSumFinEquiv]
  omega

@[simp] theorem tailGapIndex_val (a : ℕ) (t : Fin (a % 2)) :
    (tailGapIndex a t : ℕ) = 2 * (a / 2) + (t : ℕ) := by
  simp [tailGapIndex, gapBlockEquiv, finSumFinEquiv]
  omega

/-- Pair sums and the possible final gap are the coordinates on which the paired norm depends. -/
def gapPairVector {a : ℕ} (g : Fin a → ℕ) (q : Fin (a / 2)) : ℕ :=
  g (pairGapIndex a q 0) + g (pairGapIndex a q 1)

def gapTailVector {a : ℕ} (g : Fin a → ℕ) (t : Fin (a % 2)) : ℕ :=
  g (tailGapIndex a t)

theorem gapPairVector_two_le {a : ℕ} {g : Fin a → ℕ} (hg : ∀ i, 0 < g i)
    (q : Fin (a / 2)) : 2 ≤ gapPairVector g q := by
  unfold gapPairVector
  have h0 := hg (pairGapIndex a q 0)
  have h1 := hg (pairGapIndex a q 1)
  omega

theorem sum_gapPairVector_add_tail {a : ℕ} (g : Fin a → ℕ) :
    (∑ q, gapPairVector g q) + ∑ t, gapTailVector g t = ∑ i, g i := by
  rw [← (gapBlockEquiv a).sum_comp g, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp [gapPairVector, gapTailVector, pairGapIndex, tailGapIndex, Fin.sum_univ_two]

theorem gapPairVector_eq_gapPairSum {a : ℕ} (g : Fin a → ℕ) (q : Fin (a / 2)) :
    gapPairVector g q = gapPairSum (gapAtNat g) q := by
  unfold gapPairVector gapPairSum
  rw [gapAtNat_of_lt g (by omega), gapAtNat_of_lt g (by omega)]
  congr 1
  · apply congrArg g
    apply Fin.ext
    simp
  · apply congrArg g
    apply Fin.ext
    simp

/-- The prefix through pair `q`, in exactly the form used by `pascalDamping`. -/
def gapPairPrefix {a : ℕ} (b : Fin (a / 2) → ℕ) (q : Fin (a / 2)) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin (a / 2) => i ≤ q), b i

theorem gapPairPrefix_eq_sum_range {a : ℕ} (b : Fin (a / 2) → ℕ)
    (q : Fin (a / 2)) :
    gapPairPrefix b q = ∑ m ∈ Finset.range ((q : ℕ) + 1), gapAtNat b m := by
  let s := Finset.univ.filter (fun i : Fin (a / 2) => i ≤ q)
  have himage : Finset.image (fun i : Fin (a / 2) => (i : ℕ)) s =
      Finset.range ((q : ℕ) + 1) := by
    ext m
    simp only [s, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      omega
    · intro hm
      refine ⟨⟨m, by omega⟩, ?_, rfl⟩
      exact Fin.mk_le_mk.mpr (by omega)
  unfold gapPairPrefix
  change ∑ i ∈ s, b i = _
  calc
    ∑ i ∈ s, b i = ∑ i ∈ s, gapAtNat b (i : ℕ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [gapAtNat_of_lt b i.isLt]
    _ = ∑ m ∈ Finset.image (fun i : Fin (a / 2) => (i : ℕ)) s, gapAtNat b m := by
      rw [Finset.sum_image]
      exact fun _ _ _ _ h => Fin.ext h
    _ = ∑ m ∈ Finset.range ((q : ℕ) + 1), gapAtNat b m := by rw [himage]

theorem gapTime_pair_one {a : ℕ} (g : Fin a → ℕ) (q : Fin (a / 2)) :
    gapTime g (pairGapIndex a q 1) = gapPairPrefix (gapPairVector g) q := by
  rw [gapPairPrefix_eq_sum_range]
  unfold gapTime
  simp only [pairGapIndex_val, Fin.val_one]
  rw [show 2 * (q : ℕ) + 1 + 1 = 2 * ((q : ℕ) + 1) by omega]
  rw [← sum_gapPairSum_range (gapAtNat g) ((q : ℕ) + 1)]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < a / 2 := by
    have := Finset.mem_range.mp hi
    omega
  rw [gapAtNat_of_lt (gapPairVector g) hi']
  exact (gapPairVector_eq_gapPairSum g ⟨i, hi'⟩).symm

/-- The sum of the pair blocks strictly before `q`. -/
def gapPairBefore {a : ℕ} (b : Fin (a / 2) → ℕ) (q : Fin (a / 2)) : ℕ :=
  ∑ m ∈ Finset.range (q : ℕ), gapAtNat b m

theorem gapTime_pair_zero {a : ℕ} (g : Fin a → ℕ) (q : Fin (a / 2)) :
    gapTime g (pairGapIndex a q 0) =
      gapPairBefore (gapPairVector g) q + g (pairGapIndex a q 0) := by
  unfold gapTime gapPairBefore
  simp only [pairGapIndex_val, Fin.val_zero, Nat.add_zero, Finset.sum_range_succ]
  rw [← sum_gapPairSum_range (gapAtNat g) (q : ℕ)]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < a / 2 := by
      have := Finset.mem_range.mp hi
      omega
    rw [gapAtNat_of_lt (gapPairVector g) hi']
    exact (gapPairVector_eq_gapPairSum g ⟨i, hi'⟩).symm
  · rw [gapAtNat_of_lt g (by omega)]
    apply congrArg g
    apply Fin.ext
    simp

theorem gapPairPrefix_eq_before_add {a : ℕ} (b : Fin (a / 2) → ℕ)
    (q : Fin (a / 2)) : gapPairPrefix b q = gapPairBefore b q + b q := by
  rw [gapPairPrefix_eq_sum_range]
  unfold gapPairBefore
  rw [Finset.sum_range_succ, gapAtNat_of_lt b q.isLt]

theorem gapTime_tail {a : ℕ} (g : Fin a → ℕ) (t : Fin (a % 2)) :
    gapTime g (tailGapIndex a t) =
      (∑ q, gapPairVector g q) + gapTailVector g t := by
  have hmod : a % 2 < 2 := Nat.mod_lt _ (by omega)
  have ht0 : (t : ℕ) = 0 := by omega
  have hcard : 2 * (a / 2) + 1 = a := by
    have := Nat.div_add_mod a 2
    omega
  have htime : gapTime g (tailGapIndex a t) = ∑ i, g i := by
    rw [← sum_gapAtNat g]
    unfold gapTime
    congr 2
    simp only [tailGapIndex_val]
    omega
  rw [htime, ← sum_gapPairVector_add_tail g]
  congr 1
  exact Fintype.sum_eq_single t (fun b hne => (hne (Fin.ext (by omega))).elim)

/-- The character contribution of one gap coordinate. -/
noncomputable def gapCharFactor (a ξ : ℕ) (g : Fin a → ℕ) (i : Fin a) : ℂ :=
  charZ a ((ξ : ZMod (3 ^ a)) * (3 : ZMod (3 ^ a)) ^ (i : ℕ) *
    (2 : ZMod (3 ^ a))⁻¹ ^ gapTime g i)

/-- The two character factors in a pair collapse to the frozen `fPair` summand. -/
theorem gapCharFactor_pair {a ξ : ℕ} (g : Fin a → ℕ) (q : Fin (a / 2)) :
    gapCharFactor a ξ g (pairGapIndex a q 0) *
        gapCharFactor a ξ g (pairGapIndex a q 1) =
      charZ a (xArg a ξ q (gapPairPrefix (gapPairVector g) q) *
        ((2 : ZMod (3 ^ a)) ^ g (pairGapIndex a q 1) + 3)) := by
  let s := gapPairBefore (gapPairVector g) q
  have hzero := gapTime_pair_zero g q
  have hone := gapTime_pair_one g q
  have hprefix := gapPairPrefix_eq_before_add (gapPairVector g) q
  have hprefeq : s + g (pairGapIndex a q 0) + g (pairGapIndex a q 1) =
      gapPairPrefix (gapPairVector g) q := by
    rw [hprefix]
    unfold s gapPairVector
    omega
  have htime0 : gapTime g (pairGapIndex a q 0) =
      s + g (pairGapIndex a q 0) := hzero
  have htime1 : gapTime g (pairGapIndex a q 1) =
      s + g (pairGapIndex a q 0) + g (pairGapIndex a q 1) := by
    rw [hone, ← hprefeq]
  calc
    gapCharFactor a ξ g (pairGapIndex a q 0) *
        gapCharFactor a ξ g (pairGapIndex a q 1) =
      charZ a (xArg a ξ q
        (s + g (pairGapIndex a q 0) + g (pairGapIndex a q 1)) *
          ((2 : ZMod (3 ^ a)) ^ g (pairGapIndex a q 1) + 3)) := by
        simpa only [gapCharFactor, pairGapIndex_val, Fin.val_zero, Fin.val_one,
          Nat.add_zero, htime0, htime1] using
          charZ_two_gap_terms a ξ q s
            (g (pairGapIndex a q 0)) (g (pairGapIndex a q 1))
    _ = charZ a (xArg a ξ q (gapPairPrefix (gapPairVector g) q) *
        ((2 : ZMod (3 ^ a)) ^ g (pairGapIndex a q 1) + 3)) := by rw [hprefeq]

/-- Reconstruct a gap vector from pair sums, one positive split coordinate per pair, and the
possible terminal coordinate.  A split coordinate `c : Fin (b-1)` represents second gap `c+1`. -/
def splitGapVector {a : ℕ} (b : Fin (a / 2) → ℕ)
    (c : ∀ q, Fin (b q - 1)) (t : Fin (a % 2) → ℕ) : Fin a → ℕ :=
  fun i =>
    match (gapBlockEquiv a).symm i with
    | Sum.inl qs => Fin.cases (b qs.1 - ((c qs.1 : ℕ) + 1))
        (fun _ => (c qs.1 : ℕ) + 1) qs.2
    | Sum.inr r => t r

@[simp] theorem splitGapVector_pair_zero {a : ℕ} (b : Fin (a / 2) → ℕ)
    (c : ∀ q, Fin (b q - 1)) (t : Fin (a % 2) → ℕ) (q : Fin (a / 2)) :
    splitGapVector b c t (pairGapIndex a q 0) = b q - ((c q : ℕ) + 1) := by
  simp [splitGapVector, pairGapIndex]

@[simp] theorem splitGapVector_pair_one {a : ℕ} (b : Fin (a / 2) → ℕ)
    (c : ∀ q, Fin (b q - 1)) (t : Fin (a % 2) → ℕ) (q : Fin (a / 2)) :
    splitGapVector b c t (pairGapIndex a q 1) = (c q : ℕ) + 1 := by
  simp [splitGapVector, pairGapIndex]
  change (c q : ℕ) + 1 = (c q : ℕ) + 1
  rfl

@[simp] theorem splitGapVector_tail {a : ℕ} (b : Fin (a / 2) → ℕ)
    (c : ∀ q, Fin (b q - 1)) (t : Fin (a % 2) → ℕ) (r : Fin (a % 2)) :
    splitGapVector b c t (tailGapIndex a r) = t r := by
  simp [splitGapVector, tailGapIndex]

theorem splitGapVector_pos {a : ℕ} {b : Fin (a / 2) → ℕ}
    (hb : ∀ q, 2 ≤ b q) (c : ∀ q, Fin (b q - 1)) {t : Fin (a % 2) → ℕ}
    (ht : ∀ r, 0 < t r) (i : Fin a) : 0 < splitGapVector b c t i := by
  let x := (gapBlockEquiv a).symm i
  have hi : gapBlockEquiv a x = i := (gapBlockEquiv a).apply_symm_apply i
  rw [← hi]
  rcases x with qs | r
  · rcases qs with ⟨q, s⟩
    fin_cases s
    · change 0 < splitGapVector b c t (pairGapIndex a q 0)
      rw [splitGapVector_pair_zero]
      have hc := (c q).isLt
      have hbq := hb q
      omega
    · change 0 < splitGapVector b c t (pairGapIndex a q 1)
      rw [splitGapVector_pair_one]
      omega
  · change 0 < splitGapVector b c t (tailGapIndex a r)
    rw [splitGapVector_tail]
    exact ht r

theorem gapPairVector_splitGapVector {a : ℕ} {b : Fin (a / 2) → ℕ}
    (hb : ∀ q, 2 ≤ b q) (c : ∀ q, Fin (b q - 1)) (t : Fin (a % 2) → ℕ) :
    gapPairVector (splitGapVector b c t) = b := by
  funext q
  unfold gapPairVector
  rw [splitGapVector_pair_zero, splitGapVector_pair_one]
  have hc := (c q).isLt
  have hbq := hb q
  omega

theorem gapTailVector_splitGapVector {a : ℕ} (b : Fin (a / 2) → ℕ)
    (c : ∀ q, Fin (b q - 1)) (t : Fin (a % 2) → ℕ) :
    gapTailVector (splitGapVector b c t) = t := by
  funext r
  exact splitGapVector_tail b c t r

theorem sum_splitGapVector {a : ℕ} {b : Fin (a / 2) → ℕ}
    (hb : ∀ q, 2 ≤ b q) (c : ∀ q, Fin (b q - 1)) (t : Fin (a % 2) → ℕ) :
    ∑ i, splitGapVector b c t i = (∑ q, b q) + ∑ r, t r := by
  rw [← sum_gapPairVector_add_tail (splitGapVector b c t),
    gapPairVector_splitGapVector hb c t, gapTailVector_splitGapVector]

/-- The split coordinate canonically extracted from a positive gap vector. -/
def gapSplitChoice {a : ℕ} (g : Fin a → ℕ) (hg : ∀ i, 0 < g i)
    (q : Fin (a / 2)) : Fin (gapPairVector g q - 1) :=
  ⟨g (pairGapIndex a q 1) - 1, by
    have h0 := hg (pairGapIndex a q 0)
    have h1 := hg (pairGapIndex a q 1)
    unfold gapPairVector
    omega⟩

theorem splitGapVector_gapSplitChoice {a : ℕ} (g : Fin a → ℕ) (hg : ∀ i, 0 < g i) :
    splitGapVector (gapPairVector g) (gapSplitChoice g hg) (gapTailVector g) = g := by
  funext i
  let x := (gapBlockEquiv a).symm i
  have hi : gapBlockEquiv a x = i := (gapBlockEquiv a).apply_symm_apply i
  rw [← hi]
  rcases x with qs | r
  · rcases qs with ⟨q, s⟩
    fin_cases s
    · change splitGapVector (gapPairVector g) (gapSplitChoice g hg) (gapTailVector g)
          (pairGapIndex a q 0) = g (pairGapIndex a q 0)
      rw [splitGapVector_pair_zero]
      unfold gapSplitChoice gapPairVector
      have h1 := hg (pairGapIndex a q 1)
      change (g (pairGapIndex a q 0) + g (pairGapIndex a q 1)) -
        ((g (pairGapIndex a q 1) - 1) + 1) = g (pairGapIndex a q 0)
      omega
    · change splitGapVector (gapPairVector g) (gapSplitChoice g hg) (gapTailVector g)
          (pairGapIndex a q 1) = g (pairGapIndex a q 1)
      rw [splitGapVector_pair_one]
      unfold gapSplitChoice
      have h1 := hg (pairGapIndex a q 1)
      change (g (pairGapIndex a q 1) - 1) + 1 = g (pairGapIndex a q 1)
      omega
  · change splitGapVector (gapPairVector g) (gapSplitChoice g hg) (gapTailVector g)
        (tailGapIndex a r) = g (tailGapIndex a r)
    rw [splitGapVector_tail]
    rfl

/-- The character contribution of the possible unpaired terminal gap. -/
noncomputable def gapTailCharProduct (a ξ : ℕ) (b : Fin (a / 2) → ℕ)
    (t : Fin (a % 2) → ℕ) : ℂ :=
  ∏ r : Fin (a % 2), charZ a
    ((ξ : ZMod (3 ^ a)) * (3 : ZMod (3 ^ a)) ^ (tailGapIndex a r : ℕ) *
      (2 : ZMod (3 ^ a))⁻¹ ^ ((∑ q, b q) + t r))

theorem norm_gapTailCharProduct (a ξ : ℕ) (b : Fin (a / 2) → ℕ)
    (t : Fin (a % 2) → ℕ) : ‖gapTailCharProduct a ξ b t‖ = 1 := by
  unfold gapTailCharProduct
  rw [Complex.norm_prod]
  simp only [norm_charZ, Finset.prod_const_one]

/-- Pair every coordinate of `gapCharTerm`; the only remaining factor has unit norm. -/
theorem gapCharTerm_eq_pair_prod_mul_tail (a ξ : ℕ) (g : Fin a → ℕ) :
    gapCharTerm a ξ g =
      (∏ q : Fin (a / 2),
        charZ a (xArg a ξ q (gapPairPrefix (gapPairVector g) q) *
          ((2 : ZMod (3 ^ a)) ^ g (pairGapIndex a q 1) + 3))) *
        gapTailCharProduct a ξ (gapPairVector g) (gapTailVector g) := by
  unfold gapCharTerm
  change (∏ i : Fin a, gapCharFactor a ξ g i) = _
  rw [← (gapBlockEquiv a).prod_comp (gapCharFactor a ξ g),
    Fintype.prod_sum_type, Fintype.prod_prod_type]
  simp only [Fin.prod_univ_two]
  congr 1
  · apply Finset.prod_congr rfl
    intro q _
    exact gapCharFactor_pair g q
  · unfold gapTailCharProduct gapCharFactor
    apply Finset.prod_congr rfl
    intro r _
    change charZ a ((ξ : ZMod (3 ^ a)) *
      (3 : ZMod (3 ^ a)) ^ (tailGapIndex a r : ℕ) *
        (2 : ZMod (3 ^ a))⁻¹ ^ gapTime g (tailGapIndex a r)) = _
    rw [gapTime_tail]

theorem gapCharTerm_splitGapVector {a ξ : ℕ} {b : Fin (a / 2) → ℕ}
    (hb : ∀ q, 2 ≤ b q) (c : ∀ q, Fin (b q - 1)) (t : Fin (a % 2) → ℕ) :
    gapCharTerm a ξ (splitGapVector b c t) =
      (∏ q : Fin (a / 2),
        charZ a (xArg a ξ q (gapPairPrefix b q) *
          ((2 : ZMod (3 ^ a)) ^ ((c q : ℕ) + 1) + 3))) *
        gapTailCharProduct a ξ b t := by
  rw [gapCharTerm_eq_pair_prod_mul_tail,
    gapPairVector_splitGapVector hb c t, gapTailVector_splitGapVector]
  apply congrArg₂ (· * ·) ?_ rfl
  apply Finset.prod_congr rfl
  intro q _
  rw [splitGapVector_pair_one]

/-- Positive split values `1, ..., b-1` as the finite type `Fin (b-1)`. -/
def positiveSplitEquiv {b : ℕ} (_hb : 2 ≤ b) :
    Fin (b - 1) ≃ ↥(Finset.Icc 1 (b - 1)) where
  toFun c := ⟨(c : ℕ) + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
  invFun d := ⟨(d : ℕ) - 1, by
    have hd := Finset.mem_Icc.mp d.2
    omega⟩
  left_inv c := by
    apply Fin.ext
    simp
  right_inv d := by
    apply Subtype.ext
    change (d : ℕ) - 1 + 1 = (d : ℕ)
    have hd := Finset.mem_Icc.mp d.2
    omega

theorem sum_positiveSplits (a ξ : ℕ) (b : Fin (a / 2) → ℕ)
    (hb : ∀ q, 2 ≤ b q) (q : Fin (a / 2)) :
    (∑ c : Fin (b q - 1),
      charZ a (xArg a ξ q (gapPairPrefix b q) *
        ((2 : ZMod (3 ^ a)) ^ ((c : ℕ) + 1) + 3))) =
      ((b q : ℂ) - 1) * fPair a (xArg a ξ q (gapPairPrefix b q)) (b q) := by
  calc
    (∑ c : Fin (b q - 1),
      charZ a (xArg a ξ q (gapPairPrefix b q) *
        ((2 : ZMod (3 ^ a)) ^ ((c : ℕ) + 1) + 3))) =
      ∑ d : ↥(Finset.Icc 1 (b q - 1)),
        charZ a (xArg a ξ q (gapPairPrefix b q) *
          ((2 : ZMod (3 ^ a)) ^ (d : ℕ) + 3)) := by
        apply Fintype.sum_equiv (positiveSplitEquiv (hb q))
        intro c
        rfl
    _ = ∑ d ∈ Finset.Icc 1 (b q - 1),
        charZ a (xArg a ξ q (gapPairPrefix b q) *
          ((2 : ZMod (3 ^ a)) ^ d + 3)) := by
      exact Finset.sum_coe_sort (Finset.Icc 1 (b q - 1))
        (fun d => charZ a (xArg a ξ q (gapPairPrefix b q) *
          ((2 : ZMod (3 ^ a)) ^ d + 3)))
    _ = ((b q : ℂ) - 1) * fPair a (xArg a ξ q (gapPairPrefix b q)) (b q) :=
      sum_charZ_splits_eq_mul_fPair a _ (hb q)

/-- Exact complex sum over all positive splits of fixed pair sums. -/
theorem sum_gapCharTerm_splits {a ξ : ℕ} {b : Fin (a / 2) → ℕ}
    (hb : ∀ q, 2 ≤ b q) (t : Fin (a % 2) → ℕ) :
    (∑ c : ∀ q, Fin (b q - 1), gapCharTerm a ξ (splitGapVector b c t)) =
      (∏ q : Fin (a / 2),
        ((b q : ℂ) - 1) * fPair a (xArg a ξ q (gapPairPrefix b q)) (b q)) *
        gapTailCharProduct a ξ b t := by
  calc
    (∑ c : ∀ q, Fin (b q - 1), gapCharTerm a ξ (splitGapVector b c t)) =
      (∑ c : ∀ q, Fin (b q - 1),
        (∏ q : Fin (a / 2),
          charZ a (xArg a ξ q (gapPairPrefix b q) *
            ((2 : ZMod (3 ^ a)) ^ ((c q : ℕ) + 1) + 3))) *
          gapTailCharProduct a ξ b t) := by
      apply Finset.sum_congr rfl
      intro c _
      exact gapCharTerm_splitGapVector hb c t
    _ = (∑ c : ∀ q, Fin (b q - 1),
        ∏ q : Fin (a / 2),
          charZ a (xArg a ξ q (gapPairPrefix b q) *
            ((2 : ZMod (3 ^ a)) ^ ((c q : ℕ) + 1) + 3))) *
        gapTailCharProduct a ξ b t := by rw [Finset.sum_mul]
    _ = (∏ q : Fin (a / 2), ∑ c : Fin (b q - 1),
          charZ a (xArg a ξ q (gapPairPrefix b q) *
            ((2 : ZMod (3 ^ a)) ^ ((c : ℕ) + 1) + 3))) *
        gapTailCharProduct a ξ b t := by rw [Fintype.prod_sum]
    _ = (∏ q : Fin (a / 2),
        ((b q : ℂ) - 1) * fPair a (xArg a ξ q (gapPairPrefix b q)) (b q)) *
        gapTailCharProduct a ξ b t := by
      congr 1
      apply Finset.prod_congr rfl
      intro q _
      exact sum_positiveSplits a ξ b hb q

theorem norm_sum_gapCharTerm_splits {a ξ : ℕ} {b : Fin (a / 2) → ℕ}
    (hb : ∀ q, 2 ≤ b q) (t : Fin (a % 2) → ℕ) :
    ‖∑ c : ∀ q, Fin (b q - 1), gapCharTerm a ξ (splitGapVector b c t)‖ =
      ∏ q : Fin (a / 2),
        ((b q : ℝ) - 1) * ‖fPair a (xArg a ξ q (gapPairPrefix b q)) (b q)‖ := by
  rw [sum_gapCharTerm_splits hb t, norm_mul, norm_gapTailCharProduct, mul_one,
    Complex.norm_prod]
  apply Finset.prod_congr rfl
  intro q _
  rw [norm_mul]
  congr 1
  rw [Complex.norm_def, Complex.normSq_apply]
  simp
  have hb1 : (1 : ℝ) ≤ b q := by exact_mod_cast (hb q).trans' (by omega)
  rw [← sq, Real.sqrt_sq (sub_nonneg.mpr hb1)]

/-! The same split coordinates with natural-valued second gaps.  This presentation is used for
finite fiberwise summation because its function type is independent of the pair sums. -/

def splitGapVectorNat {a : ℕ} (b d : Fin (a / 2) → ℕ)
    (t : Fin (a % 2) → ℕ) : Fin a → ℕ :=
  fun i =>
    match (gapBlockEquiv a).symm i with
    | Sum.inl qs => Fin.cases (b qs.1 - d qs.1) (fun _ => d qs.1) qs.2
    | Sum.inr r => t r

@[simp] theorem splitGapVectorNat_pair_zero {a : ℕ} (b d : Fin (a / 2) → ℕ)
    (t : Fin (a % 2) → ℕ) (q : Fin (a / 2)) :
    splitGapVectorNat b d t (pairGapIndex a q 0) = b q - d q := by
  simp [splitGapVectorNat, pairGapIndex]

@[simp] theorem splitGapVectorNat_pair_one {a : ℕ} (b d : Fin (a / 2) → ℕ)
    (t : Fin (a % 2) → ℕ) (q : Fin (a / 2)) :
    splitGapVectorNat b d t (pairGapIndex a q 1) = d q := by
  simp [splitGapVectorNat, pairGapIndex]
  change d q = d q
  rfl

@[simp] theorem splitGapVectorNat_tail {a : ℕ} (b d : Fin (a / 2) → ℕ)
    (t : Fin (a % 2) → ℕ) (r : Fin (a % 2)) :
    splitGapVectorNat b d t (tailGapIndex a r) = t r := by
  simp [splitGapVectorNat, tailGapIndex]

theorem splitGapVectorNat_pos {a : ℕ} {b d : Fin (a / 2) → ℕ}
    (hd : ∀ q, d q ∈ Finset.Icc 1 (b q - 1)) {t : Fin (a % 2) → ℕ}
    (ht : ∀ r, 0 < t r) (i : Fin a) : 0 < splitGapVectorNat b d t i := by
  let x := (gapBlockEquiv a).symm i
  have hi : gapBlockEquiv a x = i := (gapBlockEquiv a).apply_symm_apply i
  rw [← hi]
  rcases x with qs | r
  · rcases qs with ⟨q, s⟩
    fin_cases s
    · change 0 < splitGapVectorNat b d t (pairGapIndex a q 0)
      rw [splitGapVectorNat_pair_zero]
      have hdq := Finset.mem_Icc.mp (hd q)
      omega
    · change 0 < splitGapVectorNat b d t (pairGapIndex a q 1)
      rw [splitGapVectorNat_pair_one]
      exact (Finset.mem_Icc.mp (hd q)).1
  · change 0 < splitGapVectorNat b d t (tailGapIndex a r)
    rw [splitGapVectorNat_tail]
    exact ht r

theorem gapPairVector_splitGapVectorNat {a : ℕ} {b d : Fin (a / 2) → ℕ}
    (hd : ∀ q, d q ∈ Finset.Icc 1 (b q - 1)) (t : Fin (a % 2) → ℕ) :
    gapPairVector (splitGapVectorNat b d t) = b := by
  funext q
  unfold gapPairVector
  rw [splitGapVectorNat_pair_zero, splitGapVectorNat_pair_one]
  have hdq := Finset.mem_Icc.mp (hd q)
  omega

theorem gapTailVector_splitGapVectorNat {a : ℕ} (b d : Fin (a / 2) → ℕ)
    (t : Fin (a % 2) → ℕ) : gapTailVector (splitGapVectorNat b d t) = t := by
  funext r
  exact splitGapVectorNat_tail b d t r

theorem sum_splitGapVectorNat {a : ℕ} {b d : Fin (a / 2) → ℕ}
    (hd : ∀ q, d q ∈ Finset.Icc 1 (b q - 1)) (t : Fin (a % 2) → ℕ) :
    ∑ i, splitGapVectorNat b d t i = (∑ q, b q) + ∑ r, t r := by
  rw [← sum_gapPairVector_add_tail (splitGapVectorNat b d t),
    gapPairVector_splitGapVectorNat hd t, gapTailVector_splitGapVectorNat]

theorem splitGapVectorNat_of_gap {a : ℕ} (g : Fin a → ℕ) :
    splitGapVectorNat (gapPairVector g) (fun q => g (pairGapIndex a q 1))
      (gapTailVector g) = g := by
  funext i
  let x := (gapBlockEquiv a).symm i
  have hi : gapBlockEquiv a x = i := (gapBlockEquiv a).apply_symm_apply i
  rw [← hi]
  rcases x with qs | r
  · rcases qs with ⟨q, s⟩
    fin_cases s
    · change splitGapVectorNat (gapPairVector g) (fun q => g (pairGapIndex a q 1))
          (gapTailVector g) (pairGapIndex a q 0) = g (pairGapIndex a q 0)
      rw [splitGapVectorNat_pair_zero]
      unfold gapPairVector
      omega
    · change splitGapVectorNat (gapPairVector g) (fun q => g (pairGapIndex a q 1))
          (gapTailVector g) (pairGapIndex a q 1) = g (pairGapIndex a q 1)
      rw [splitGapVectorNat_pair_one]
  · change splitGapVectorNat (gapPairVector g) (fun q => g (pairGapIndex a q 1))
        (gapTailVector g) (tailGapIndex a r) = g (tailGapIndex a r)
    rw [splitGapVectorNat_tail]
    rfl

theorem gapCharTerm_splitGapVectorNat {a ξ : ℕ} {b d : Fin (a / 2) → ℕ}
    (hd : ∀ q, d q ∈ Finset.Icc 1 (b q - 1)) (t : Fin (a % 2) → ℕ) :
    gapCharTerm a ξ (splitGapVectorNat b d t) =
      (∏ q : Fin (a / 2),
        charZ a (xArg a ξ q (gapPairPrefix b q) *
          ((2 : ZMod (3 ^ a)) ^ d q + 3))) * gapTailCharProduct a ξ b t := by
  rw [gapCharTerm_eq_pair_prod_mul_tail,
    gapPairVector_splitGapVectorNat hd t, gapTailVector_splitGapVectorNat]
  apply congrArg₂ (· * ·) ?_ rfl
  apply Finset.prod_congr rfl
  intro q _
  rw [splitGapVectorNat_pair_one]

/-- The independent finite choices of the second gap in every pair with prescribed pair sums. -/
def splitChoiceFinset {a : ℕ} (b : Fin (a / 2) → ℕ) : Finset (Fin (a / 2) → ℕ) :=
  Fintype.piFinset fun q => Finset.Icc 1 (b q - 1)

theorem mem_splitChoiceFinset {a : ℕ} {b d : Fin (a / 2) → ℕ} :
    d ∈ splitChoiceFinset b ↔ ∀ q, d q ∈ Finset.Icc 1 (b q - 1) := by
  simp [splitChoiceFinset]

/-- Gap vectors with fixed pair sums and fixed possible terminal gap. -/
def gapFiberFinset (j a : ℕ) (b : Fin (a / 2) → ℕ) (t : Fin (a % 2) → ℕ) :
    Finset (Fin a → ℕ) :=
  (gapVectorFinset j a).filter fun g => gapPairVector g = b ∧ gapTailVector g = t

theorem mem_gapFiberFinset {j a : ℕ} {b : Fin (a / 2) → ℕ}
    {t : Fin (a % 2) → ℕ} {g : Fin a → ℕ} :
    g ∈ gapFiberFinset j a b t ↔
      g ∈ gapVectorFinset j a ∧ gapPairVector g = b ∧ gapTailVector g = t := by
  simp [gapFiberFinset]

/-- For admissible pair and tail data, its gap-vector fiber is exactly the product of the
independent positive split intervals. -/
theorem sum_gapFiberFinset_eq_splits {j a ξ : ℕ} {b : Fin (a / 2) → ℕ}
    (_hb : ∀ q, 2 ≤ b q) {t : Fin (a % 2) → ℕ} (ht : ∀ r, 0 < t r)
    (htotal : (∑ q, b q) + ∑ r, t r ≤ j) :
    ∑ g ∈ gapFiberFinset j a b t, gapCharTerm a ξ g =
      ∑ d ∈ splitChoiceFinset b, gapCharTerm a ξ (splitGapVectorNat b d t) := by
  classical
  symm
  apply Finset.sum_bij (fun d _ => splitGapVectorNat b d t)
  · intro d hd
    have hd' := mem_splitChoiceFinset.mp hd
    rw [mem_gapFiberFinset]
    refine ⟨mem_gapVectorFinset.mpr ⟨splitGapVectorNat_pos hd' ht, ?_⟩, ?_, ?_⟩
    · rw [sum_splitGapVectorNat hd' t]
      exact htotal
    · exact gapPairVector_splitGapVectorNat hd' t
    · exact gapTailVector_splitGapVectorNat b d t
  · intro d₁ hd₁ d₂ hd₂ heq
    funext q
    have h := congr_fun heq (pairGapIndex a q 1)
    simpa using h
  · intro g hg
    have hgf := mem_gapFiberFinset.mp hg
    let d : Fin (a / 2) → ℕ := fun q => g (pairGapIndex a q 1)
    have hgpos := (mem_gapVectorFinset.mp hgf.1).1
    have hd : d ∈ splitChoiceFinset b := by
      rw [mem_splitChoiceFinset]
      intro q
      rw [Finset.mem_Icc]
      change 1 ≤ g (pairGapIndex a q 1) ∧ g (pairGapIndex a q 1) ≤ b q - 1
      have hpair := congr_fun hgf.2.1 q
      unfold gapPairVector at hpair
      constructor
      · exact hgpos (pairGapIndex a q 1)
      · have hzero := hgpos (pairGapIndex a q 0)
        omega
    refine ⟨d, hd, ?_⟩
    rw [← hgf.2.1, ← hgf.2.2]
    exact splitGapVectorNat_of_gap g
  · intro d hd
    rfl

/-- Exact complex sum over one fiber of fixed pair sums and fixed terminal gap. -/
theorem sum_gapFiberFinset {j a ξ : ℕ} {b : Fin (a / 2) → ℕ}
    (hb : ∀ q, 2 ≤ b q) {t : Fin (a % 2) → ℕ} (ht : ∀ r, 0 < t r)
    (htotal : (∑ q, b q) + ∑ r, t r ≤ j) :
    ∑ g ∈ gapFiberFinset j a b t, gapCharTerm a ξ g =
      (∏ q : Fin (a / 2),
        ((b q : ℂ) - 1) * fPair a (xArg a ξ q (gapPairPrefix b q)) (b q)) *
        gapTailCharProduct a ξ b t := by
  classical
  rw [sum_gapFiberFinset_eq_splits hb ht htotal]
  calc
    ∑ d ∈ splitChoiceFinset b, gapCharTerm a ξ (splitGapVectorNat b d t) =
        ∑ d ∈ splitChoiceFinset b,
          (∏ q : Fin (a / 2),
            charZ a (xArg a ξ q (gapPairPrefix b q) *
              ((2 : ZMod (3 ^ a)) ^ d q + 3))) * gapTailCharProduct a ξ b t := by
      apply Finset.sum_congr rfl
      intro d hd
      exact gapCharTerm_splitGapVectorNat (mem_splitChoiceFinset.mp hd) t
    _ = (∑ d ∈ splitChoiceFinset b,
          ∏ q : Fin (a / 2),
            charZ a (xArg a ξ q (gapPairPrefix b q) *
              ((2 : ZMod (3 ^ a)) ^ d q + 3))) * gapTailCharProduct a ξ b t := by
      rw [Finset.sum_mul]
    _ = (∏ q : Fin (a / 2), ∑ d ∈ Finset.Icc 1 (b q - 1),
          charZ a (xArg a ξ q (gapPairPrefix b q) *
            ((2 : ZMod (3 ^ a)) ^ d + 3))) * gapTailCharProduct a ξ b t := by
      rw [Finset.prod_univ_sum]
      rfl
    _ = (∏ q : Fin (a / 2),
          ((b q : ℂ) - 1) * fPair a (xArg a ξ q (gapPairPrefix b q)) (b q)) *
          gapTailCharProduct a ξ b t := by
      congr 1
      apply Finset.prod_congr rfl
      intro q _
      exact sum_charZ_splits_eq_mul_fPair a _ (hb q)

/-- After summing all splits, the norm of one fiber is the product of the frozen pair factors;
the possible terminal factor has norm one. -/
theorem norm_sum_gapFiberFinset {j a ξ : ℕ} {b : Fin (a / 2) → ℕ}
    (hb : ∀ q, 2 ≤ b q) {t : Fin (a % 2) → ℕ} (ht : ∀ r, 0 < t r)
    (htotal : (∑ q, b q) + ∑ r, t r ≤ j) :
    ‖∑ g ∈ gapFiberFinset j a b t, gapCharTerm a ξ g‖ =
      ∏ q : Fin (a / 2),
        ((b q : ℝ) - 1) * ‖fPair a (xArg a ξ q (gapPairPrefix b q)) (b q)‖ := by
  rw [sum_gapFiberFinset hb ht htotal, norm_mul, norm_gapTailCharProduct, mul_one,
    Complex.norm_prod]
  apply Finset.prod_congr rfl
  intro q _
  rw [norm_mul]
  congr 1
  rw [Complex.norm_def, Complex.normSq_apply]
  simp
  have hb1 : (1 : ℝ) ≤ b q := by exact_mod_cast (hb q).trans' (by omega)
  rw [← sq, Real.sqrt_sq (sub_nonneg.mpr hb1)]

/-- Pair sums together with the possible terminal gap form the coarse coordinates used to group
the complete finite gap sum. -/
def gapKey {a : ℕ} (g : Fin a → ℕ) :
    (Fin (a / 2) → ℕ) × (Fin (a % 2) → ℕ) :=
  (gapPairVector g, gapTailVector g)

def gapKeyFinset (j a : ℕ) :
    Finset ((Fin (a / 2) → ℕ) × (Fin (a % 2) → ℕ)) :=
  (gapVectorFinset j a).image gapKey

theorem mem_gapKeyFinset {j a : ℕ}
    {bt : (Fin (a / 2) → ℕ) × (Fin (a % 2) → ℕ)} :
    bt ∈ gapKeyFinset j a ↔ ∃ g ∈ gapVectorFinset j a, gapKey g = bt := by
  simp [gapKeyFinset]

theorem gapKeyFinset_admissible {j a : ℕ}
    {bt : (Fin (a / 2) → ℕ) × (Fin (a % 2) → ℕ)}
    (hbt : bt ∈ gapKeyFinset j a) :
    (∀ q, 2 ≤ bt.1 q) ∧ (∀ r, 0 < bt.2 r) ∧
      (∑ q, bt.1 q) + ∑ r, bt.2 r ≤ j := by
  obtain ⟨g, hg, rfl⟩ := mem_gapKeyFinset.mp hbt
  have hgap := mem_gapVectorFinset.mp hg
  refine ⟨gapPairVector_two_le hgap.1, fun r => hgap.1 (tailGapIndex a r), ?_⟩
  unfold gapKey
  rw [sum_gapPairVector_add_tail]
  exact hgap.2

/-- The complete gap sum is the sum of its disjoint pair-sum/tail fibers. -/
theorem sum_gapVectorFinset_eq_sum_gapFibers (j a ξ : ℕ) :
    ∑ g ∈ gapVectorFinset j a, gapCharTerm a ξ g =
      ∑ bt ∈ gapKeyFinset j a,
        ∑ g ∈ gapFiberFinset j a bt.1 bt.2, gapCharTerm a ξ g := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := gapVectorFinset j a) (t := gapKeyFinset j a) (g := gapKey)
    (fun g hg => Finset.mem_image.mpr ⟨g, hg, rfl⟩) (gapCharTerm a ξ)]
  apply Finset.sum_congr rfl
  intro bt hbt
  apply Finset.sum_congr
  · rcases bt with ⟨b, t⟩
    ext g
    simp [gapFiberFinset, gapKey]
  · intro g hg
    rfl

/-- Triangle inequality after all cancellation within each independent split fiber. -/
theorem norm_sum_gapVectorFinset_le_pairFibers (j a ξ : ℕ) :
    ‖∑ g ∈ gapVectorFinset j a, gapCharTerm a ξ g‖ ≤
      ∑ bt ∈ gapKeyFinset j a, ∏ q : Fin (a / 2),
        ((bt.1 q : ℝ) - 1) *
          ‖fPair a (xArg a ξ q (gapPairPrefix bt.1 q)) (bt.1 q)‖ := by
  rw [sum_gapVectorFinset_eq_sum_gapFibers]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro bt hbt
  obtain ⟨hb, ht, htotal⟩ := gapKeyFinset_admissible hbt
  exact le_of_eq (norm_sum_gapFiberFinset hb ht htotal)

/-! ## Summability of the Pascal majorant -/

theorem norm_fPair_le_one (n : ℕ) (x : ZMod (3 ^ n)) (b : ℕ) :
    ‖fPair n x b‖ ≤ 1 := by
  by_cases hb : 2 ≤ b
  · have htriangle :
        ‖∑ d ∈ Finset.Icc 1 (b - 1), charZ n (x * (2 ^ d + 3))‖ ≤ (b : ℝ) - 1 := by
      calc
        ‖∑ d ∈ Finset.Icc 1 (b - 1), charZ n (x * (2 ^ d + 3))‖ ≤
            ∑ d ∈ Finset.Icc 1 (b - 1), ‖charZ n (x * (2 ^ d + 3))‖ :=
          norm_sum_le _ _
        _ = (b : ℝ) - 1 := by
          simp only [norm_charZ, Finset.sum_const, nsmul_eq_mul, mul_one]
          have hcard : (Finset.Icc 1 (b - 1)).card = b - 1 := by
            rw [Nat.card_Icc]
            omega
          rw [hcard, Nat.cast_sub (by omega : 1 ≤ b)]
          norm_num
    rw [norm_sum_charZ_splits n x hb] at htriangle
    have hpos : 0 < (b : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast (show 1 < b by omega))
    nlinarith [norm_nonneg (fPair n x b)]
  · have hb' : b = 0 ∨ b = 1 := by omega
    rcases hb' with rfl | rfl <;> simp [fPair]

theorem summable_pascalWeight {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Summable (pascalWeight p) := by
  have hnorm : ‖1 - p‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  have hgeom := summable_choose_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm
  have htail : Summable (fun n : ℕ => pascalWeight p (n + 2)) := by
    apply (hgeom.mul_left (p ^ 2)).congr
    intro n
    rw [pascalWeight_of_two_le p (by omega)]
    simp only [Nat.add_sub_cancel, Nat.choose_one_right]
    push_cast
    ring
  exact (summable_nat_add_iff 2).mp htail

/-- A finite product of copies of a nonnegative summable series is summable on the corresponding
finite function space. -/
theorem summable_fin_product_of_nonneg {w : ℕ → ℝ} (hw0 : ∀ m, 0 ≤ w m)
    (hw : Summable w) (k : ℕ) :
    Summable (fun b : Fin k → ℕ => ∏ q, w (b q)) := by
  induction k with
  | zero => exact (hasSum_fintype _).summable
  | succ k ih =>
      have ih0 : ∀ b : Fin k → ℕ, 0 ≤ ∏ q, w (b q) :=
        fun b => Finset.prod_nonneg fun q _ => hw0 (b q)
      have hprod : Summable (fun bt : ℕ × (Fin k → ℕ) =>
          w bt.1 * ∏ q, w (bt.2 q)) :=
        Summable.mul_of_nonneg (f := w) (g := fun b : Fin k → ℕ => ∏ q, w (b q))
          hw ih hw0 ih0
      apply (Fin.consEquiv (fun _ : Fin (k + 1) => ℕ)).summable_iff.mp
      convert hprod using 1
      ext bt
      change (∏ q, w (Fin.cons (α := fun _ : Fin (k + 1) => ℕ) bt.1 bt.2 q)) = _
      rw [Fin.prod_univ_succ]
      simp

/-- One summand of the frozen `pascalDamping` series. -/
noncomputable def pascalDampingTerm (n : ℕ) (p : ℝ) (ξ : ℕ)
    (b : Fin (n / 2) → ℕ) : ℝ :=
  (∏ q, pascalWeight p (b q)) *
    ∏ q : Fin (n / 2),
      ‖fPair n (xArg n ξ q (gapPairPrefix b q)) (b q)‖

theorem pascalDamping_eq_tsum (n : ℕ) (p : ℝ) (ξ : ℕ) :
    pascalDamping n p ξ = ∑' b, pascalDampingTerm n p ξ b := by
  rfl

theorem pascalDampingTerm_nonneg {p : ℝ} (hp1 : p ≤ 1) (n ξ : ℕ)
    (b : Fin (n / 2) → ℕ) : 0 ≤ pascalDampingTerm n p ξ b := by
  unfold pascalDampingTerm
  exact mul_nonneg (Finset.prod_nonneg fun q _ => pascalWeight_nonneg hp1 (b q))
    (Finset.prod_nonneg fun _ _ => norm_nonneg _)

theorem summable_pascalDampingTerm {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (n ξ : ℕ) : Summable (pascalDampingTerm n p ξ) := by
  have hweights : Summable (fun b : Fin (n / 2) → ℕ =>
      ∏ q, pascalWeight p (b q)) :=
    summable_fin_product_of_nonneg (fun m => pascalWeight_nonneg hp1.le m)
      (summable_pascalWeight hp0 hp1) _
  refine Summable.of_nonneg_of_le
    (fun b => pascalDampingTerm_nonneg hp1.le n ξ b) ?_ hweights
  intro b
  unfold pascalDampingTerm
  refine mul_le_of_le_one_right (Finset.prod_nonneg fun q _ => pascalWeight_nonneg hp1.le (b q)) ?_
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _)
    (fun q _ => norm_fPair_le_one n _ (b q))

theorem sum_pascalDampingTerm_le {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (n ξ : ℕ) (s : Finset (Fin (n / 2) → ℕ)) :
    ∑ b ∈ s, pascalDampingTerm n p ξ b ≤ pascalDamping n p ξ := by
  rw [pascalDamping_eq_tsum]
  exact (summable_pascalDampingTerm hp0 hp1 n ξ).sum_le_tsum s
    (fun b _ => pascalDampingTerm_nonneg hp1.le n ξ b)

/-! ## Geometric reweighting -/

noncomputable def pairFiberNorm (a ξ : ℕ) (b : Fin (a / 2) → ℕ) : ℝ :=
  ∏ q : Fin (a / 2),
    ((b q : ℝ) - 1) *
      ‖fPair a (xArg a ξ q (gapPairPrefix b q)) (b q)‖

theorem pairFiberNorm_nonneg {a ξ : ℕ} {b : Fin (a / 2) → ℕ}
    (hb : ∀ q, 2 ≤ b q) : 0 ≤ pairFiberNorm a ξ b := by
  unfold pairFiberNorm
  apply Finset.prod_nonneg
  intro q _
  have hbqNat : 1 ≤ b q := Nat.le_trans (by norm_num) (hb q)
  have hbq : (1 : ℝ) ≤ b q := by exact_mod_cast hbqNat
  exact mul_nonneg (sub_nonneg.mpr hbq) (norm_nonneg _)

theorem sum_pair_sub_two {a : ℕ} {b : Fin (a / 2) → ℕ} (hb : ∀ q, 2 ≤ b q) :
    ∑ q, (b q - 2) = (∑ q, b q) - 2 * (a / 2) := by
  rw [Finset.sum_tsub_distrib Finset.univ (fun q _ => hb q)]
  simp [Nat.mul_comm]

/-- Expanding the Pascal weights leaves the fixed-fiber norm times the geometric mass assigned
to the paired gaps. -/
theorem pascalDampingTerm_eq_geom_mul_pairFiberNorm {a ξ : ℕ} (p : ℝ)
    {b : Fin (a / 2) → ℕ} (hb : ∀ q, 2 ≤ b q) :
    pascalDampingTerm a p ξ b =
      p ^ (2 * (a / 2)) * (1 - p) ^ ((∑ q, b q) - 2 * (a / 2)) *
        pairFiberNorm a ξ b := by
  have hweight : (∏ q, pascalWeight p (b q)) =
      (∏ q, ((b q : ℝ) - 1)) * p ^ (2 * (a / 2)) *
        (1 - p) ^ ((∑ q, b q) - 2 * (a / 2)) := by
    simp_rw [pascalWeight_of_two_le p (hb _)]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← pow_mul, Finset.prod_pow_eq_pow_sum, sum_pair_sub_two hb]
  unfold pascalDampingTerm pairFiberNorm
  rw [hweight, Finset.prod_mul_distrib]
  ring

/-- Every admissible finite slice key, after multiplying by the constant slice probability
weight, is dominated by its full Pascal damping summand. -/
theorem weighted_pairFiberNorm_le_pascalDampingTerm {j a ξ : ℕ} {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1)
    {bt : (Fin (a / 2) → ℕ) × (Fin (a % 2) → ℕ)}
    (hbt : bt ∈ gapKeyFinset j a) :
    p ^ a * (1 - p) ^ (j - a) * pairFiberNorm a ξ bt.1 ≤
      pascalDampingTerm a p ξ bt.1 := by
  obtain ⟨hb, ht, htotal⟩ := gapKeyFinset_admissible hbt
  let k := a / 2
  let r := a % 2
  let S := ∑ q, bt.1 q
  have hrlt : r < 2 := by
    unfold r
    exact Nat.mod_lt _ (by omega)
  have ha : a = 2 * k + r := by
    unfold k r
    have h := Nat.div_add_mod a 2
    omega
  have htwo : 2 * k ≤ S := by
    unfold k S
    calc
      2 * (a / 2) = ∑ q : Fin (a / 2), 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ q, bt.1 q := Finset.sum_le_sum fun q _ => hb q
  have hrtail : r ≤ ∑ t, bt.2 t := by
    by_cases hr0 : r = 0
    · simp [hr0]
    · have hr1 : r = 1 := by omega
      let t0 : Fin (a % 2) := ⟨0, by simp [r, hr1]⟩
      have hsingle : bt.2 t0 ≤ ∑ t, bt.2 t :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ t0)
      have ht0 := ht t0
      omega
  have hSj : S + r ≤ j := by
    change S + ∑ t, bt.2 t ≤ j at htotal
    omega
  have hpPow : p ^ a = p ^ (2 * k) * p ^ r := by rw [ha, pow_add]
  have hqPow : (1 - p) ^ (j - a) =
      (1 - p) ^ (S - 2 * k) * (1 - p) ^ (j - S - r) := by
    rw [← pow_add]
    congr 1
    omega
  have hid : p ^ a * (1 - p) ^ (j - a) * pairFiberNorm a ξ bt.1 =
      (p ^ (2 * k) * (1 - p) ^ (S - 2 * k) * pairFiberNorm a ξ bt.1) *
        (p ^ r * (1 - p) ^ (j - S - r)) := by
    rw [hpPow, hqPow]
    ring
  have hq0 : 0 ≤ 1 - p := by linarith
  have hfactor : p ^ r * (1 - p) ^ (j - S - r) ≤ 1 := by
    calc
      p ^ r * (1 - p) ^ (j - S - r) ≤ 1 * 1 :=
        mul_le_mul (pow_le_one₀ hp0.le hp1.le) (pow_le_one₀ hq0 (by linarith))
          (pow_nonneg hq0 _) zero_le_one
      _ = 1 := one_mul 1
  rw [pascalDampingTerm_eq_geom_mul_pairFiberNorm p hb]
  change _ ≤ p ^ (2 * k) * (1 - p) ^ (S - 2 * k) * pairFiberNorm a ξ bt.1
  rw [hid]
  calc
    (p ^ (2 * k) * (1 - p) ^ (S - 2 * k) * pairFiberNorm a ξ bt.1) *
          (p ^ r * (1 - p) ^ (j - S - r)) ≤
        (p ^ (2 * k) * (1 - p) ^ (S - 2 * k) * pairFiberNorm a ξ bt.1) * 1 :=
      mul_le_mul_of_nonneg_left hfactor
        (mul_nonneg (mul_nonneg (pow_nonneg hp0.le _) (pow_nonneg hq0 _))
          (pairFiberNorm_nonneg hb))
    _ = p ^ (2 * k) * (1 - p) ^ (S - 2 * k) * pairFiberNorm a ξ bt.1 := by ring

/-- All positive choices for the possible terminal gap.  Its domain has cardinality zero or one,
so this finite set has at most `j + 1` elements. -/
def tailChoiceFinset (j a : ℕ) : Finset (Fin (a % 2) → ℕ) :=
  Fintype.piFinset fun _ => Finset.Icc 1 j

theorem mem_tailChoiceFinset {j a : ℕ} {t : Fin (a % 2) → ℕ} :
    t ∈ tailChoiceFinset j a ↔ ∀ r, t r ∈ Finset.Icc 1 j := by
  simp [tailChoiceFinset]

theorem card_tailChoiceFinset_le (j a : ℕ) : (tailChoiceFinset j a).card ≤ j + 1 := by
  unfold tailChoiceFinset
  rw [Fintype.card_piFinset]
  have hr : a % 2 = 0 ∨ a % 2 = 1 := by
    have := Nat.mod_lt a (by omega : 0 < 2)
    omega
  rcases hr with hr | hr
  · simp [hr]
  · simp [hr, Nat.card_Icc]

def pairKeyFinset (j a : ℕ) : Finset (Fin (a / 2) → ℕ) :=
  (gapKeyFinset j a).image Prod.fst

theorem gapKeyFinset_subset_pair_product (j a : ℕ) :
    gapKeyFinset j a ⊆ (pairKeyFinset j a).product (tailChoiceFinset j a) := by
  intro bt hbt
  rw [Finset.product_eq_sprod, Finset.mem_product]
  refine ⟨Finset.mem_image.mpr ⟨bt, hbt, rfl⟩, mem_tailChoiceFinset.mpr ?_⟩
  intro r
  rw [Finset.mem_Icc]
  obtain ⟨_, ht, htotal⟩ := gapKeyFinset_admissible hbt
  refine ⟨ht r, ?_⟩
  have hsingle : bt.2 r ≤ ∑ t, bt.2 t :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
  omega

theorem sum_gapKey_pascalDampingTerm_le {j a ξ : ℕ} {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    ∑ bt ∈ gapKeyFinset j a, pascalDampingTerm a p ξ bt.1 ≤
      (j + 1 : ℝ) * pascalDamping a p ξ := by
  let bs := pairKeyFinset j a
  let ts := tailChoiceFinset j a
  have hsubset : gapKeyFinset j a ⊆ bs.product ts := by
    exact gapKeyFinset_subset_pair_product j a
  have hfinite := sum_pascalDampingTerm_le hp0 hp1 a ξ bs
  have hcard : (ts.card : ℝ) ≤ j + 1 := by
    exact_mod_cast card_tailChoiceFinset_le j a
  have hsum0 : 0 ≤ ∑ b ∈ bs, pascalDampingTerm a p ξ b :=
    Finset.sum_nonneg fun b _ => pascalDampingTerm_nonneg hp1.le a ξ b
  calc
    ∑ bt ∈ gapKeyFinset j a, pascalDampingTerm a p ξ bt.1 ≤
        ∑ bt ∈ bs.product ts, pascalDampingTerm a p ξ bt.1 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun bt _ _ => pascalDampingTerm_nonneg hp1.le a ξ bt.1)
    _ = (ts.card : ℝ) * ∑ b ∈ bs, pascalDampingTerm a p ξ b := by
      rw [Finset.product_eq_sprod, Finset.sum_product]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [Finset.mul_sum]
    _ ≤ (j + 1 : ℝ) * ∑ b ∈ bs, pascalDampingTerm a p ξ b :=
      mul_le_mul_of_nonneg_right hcard hsum0
    _ ≤ (j + 1 : ℝ) * pascalDamping a p ξ :=
      mul_le_mul_of_nonneg_left hfinite (by positivity)

/-- The unnormalised slice gap sum, weighted by the probability of any one slice word, is at
most a harmless `j+1` factor times the frozen Pascal damping series. -/
theorem weighted_gapCharSum_le_pascalDamping {j a ξ : ℕ} {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    p ^ a * (1 - p) ^ (j - a) *
        ‖∑ g ∈ gapVectorFinset j a, gapCharTerm a ξ g‖ ≤
      (j + 1 : ℝ) * pascalDamping a p ξ := by
  have hq0 : 0 ≤ 1 - p := by linarith
  have hweight : 0 ≤ p ^ a * (1 - p) ^ (j - a) :=
    mul_nonneg (pow_nonneg hp0.le _) (pow_nonneg hq0 _)
  have hnorm :
      ‖∑ g ∈ gapVectorFinset j a, gapCharTerm a ξ g‖ ≤
        ∑ bt ∈ gapKeyFinset j a, pairFiberNorm a ξ bt.1 := by
    simpa only [pairFiberNorm] using norm_sum_gapVectorFinset_le_pairFibers j a ξ
  calc
    p ^ a * (1 - p) ^ (j - a) *
        ‖∑ g ∈ gapVectorFinset j a, gapCharTerm a ξ g‖ ≤
      (p ^ a * (1 - p) ^ (j - a)) *
        ∑ bt ∈ gapKeyFinset j a, pairFiberNorm a ξ bt.1 :=
      mul_le_mul_of_nonneg_left hnorm hweight
    _ = ∑ bt ∈ gapKeyFinset j a,
        p ^ a * (1 - p) ^ (j - a) * pairFiberNorm a ξ bt.1 := by
      rw [Finset.mul_sum]
    _ ≤ ∑ bt ∈ gapKeyFinset j a, pascalDampingTerm a p ξ bt.1 := by
      apply Finset.sum_le_sum
      intro bt hbt
      exact weighted_pairFiberNorm_le_pascalDampingTerm hp0 hp1 hbt
    _ ≤ (j + 1 : ℝ) * pascalDamping a p ξ :=
      sum_gapKey_pascalDampingTerm_le hp0 hp1

theorem norm_sliceChar_eq_norm_gapCharSum (j a ξ : ℕ) :
    ‖sliceChar j a ξ‖ = ‖∑ g ∈ gapVectorFinset j a, gapCharTerm a ξ g‖ := by
  rw [sliceChar_eq_subsetChar, norm_subsetChar_eq_norm_negativeSubsetChar,
    negativeSubsetChar_eq_sum_gapVector]

theorem weighted_sliceChar_le_pascalDamping {j a ξ : ℕ} {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    p ^ a * (1 - p) ^ (j - a) * ‖sliceChar j a ξ‖ ≤
      (j + 1 : ℝ) * pascalDamping a p ξ := by
  rw [norm_sliceChar_eq_norm_gapCharSum]
  exact weighted_gapCharSum_le_pascalDamping hp0 hp1

/-! ## The central binomial mass at its mode -/

/-- Adjacent binomial masses satisfy the usual balance identity, stated without division. -/
theorem binomialSliceWeight_succ_balance {j k : ℕ} (p : ℝ) (hk : k < j) :
    binomialSliceWeight j (k + 1) p * ((k + 1 : ℝ) * (1 - p)) =
      binomialSliceWeight j k p * ((j - k : ℝ) * p) := by
  have hchooseNat := Nat.choose_succ_right_eq j k
  have hchoose : (j.choose (k + 1) : ℝ) * (k + 1 : ℝ) =
      (j.choose k : ℝ) * (j - k : ℝ) := by
    calc
      (j.choose (k + 1) : ℝ) * (k + 1 : ℝ) =
          (j.choose (k + 1) * (k + 1) : ℕ) := by push_cast; ring
      _ = (j.choose k * (j - k) : ℕ) := by rw [hchooseNat]
      _ = (j.choose k : ℝ) * (j - k : ℝ) := by
        rw [Nat.cast_mul, Nat.cast_sub hk.le]
  have hexp : j - (k + 1) + 1 = j - k := by omega
  have hqpow : (1 - p) ^ (j - (k + 1)) * (1 - p) = (1 - p) ^ (j - k) := by
    rw [← pow_succ, hexp]
  unfold binomialSliceWeight
  rw [pow_succ p k]
  calc
    (j.choose (k + 1) : ℝ) * (p ^ k * p) * (1 - p) ^ (j - (k + 1)) *
        ((k + 1 : ℝ) * (1 - p)) =
      ((j.choose (k + 1) : ℝ) * (k + 1 : ℝ)) * p ^ k * p *
        ((1 - p) ^ (j - (k + 1)) * (1 - p)) := by ring
    _ = ((j.choose k : ℝ) * (j - k : ℝ)) * p ^ k * p *
        (1 - p) ^ (j - k) := by rw [hchoose, hqpow]
    _ = (j.choose k : ℝ) * p ^ k * (1 - p) ^ (j - k) *
        ((j - k : ℝ) * p) := by ring

theorem binomialSliceWeight_succ_le_of_lt_mode {j a k : ℕ}
    (hj : 0 < j) (ha : a < j) (hk : k < a) :
    binomialSliceWeight j k ((a : ℝ) / j) ≤
      binomialSliceWeight j (k + 1) ((a : ℝ) / j) := by
  let p : ℝ := (a : ℝ) / j
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have haR : (a : ℝ) < j := by exact_mod_cast ha
  have hp0 : 0 ≤ p := by unfold p; positivity
  have hq0 : 0 < 1 - p := by unfold p; rw [sub_pos, div_lt_one hjR]; exact haR
  have hfactor : (k + 1 : ℝ) * (1 - p) ≤ (j - k : ℝ) * p := by
    have hkaCast : (k + 1 : ℝ) ≤ a := by exact_mod_cast hk
    have hka : (0 : ℝ) ≤ (a : ℝ) - (k + 1 : ℝ) := sub_nonneg.mpr hkaCast
    have hprod : 0 ≤ (j : ℝ) * ((a : ℝ) - (k + 1 : ℝ)) :=
      mul_nonneg hjR.le hka
    unfold p
    field_simp
    nlinarith
  change binomialSliceWeight j k p ≤ binomialSliceWeight j (k + 1) p
  have hc : 0 < (k + 1 : ℝ) * (1 - p) := mul_pos (by positivity) hq0
  apply (mul_le_mul_iff_of_pos_right hc).mp
  calc
    binomialSliceWeight j k p * ((k + 1 : ℝ) * (1 - p)) ≤
        binomialSliceWeight j k p * ((j - k : ℝ) * p) :=
      mul_le_mul_of_nonneg_left hfactor (by
        unfold binomialSliceWeight
        positivity)
    _ = binomialSliceWeight j (k + 1) p * ((k + 1 : ℝ) * (1 - p)) :=
      (binomialSliceWeight_succ_balance p (by omega)).symm

theorem binomialSliceWeight_succ_ge_of_mode_le {j a k : ℕ}
    (hj : 0 < j) (ha0 : 0 < a) (hak : a ≤ k) (hkj : k < j) :
    binomialSliceWeight j (k + 1) ((a : ℝ) / j) ≤
      binomialSliceWeight j k ((a : ℝ) / j) := by
  let p : ℝ := (a : ℝ) / j
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have ha0R : (0 : ℝ) < a := by exact_mod_cast ha0
  have hp0 : 0 < p := div_pos ha0R hjR
  have hakj : a < j := hak.trans_lt hkj
  have hq0 : 0 < 1 - p := by
    unfold p
    rw [sub_pos, div_lt_one hjR]
    exact_mod_cast hakj
  have hfactor : (j - k : ℝ) * p ≤ (k + 1 : ℝ) * (1 - p) := by
    have hkaCast : (a : ℝ) + 1 ≤ k + 1 := by exact_mod_cast (show a + 1 ≤ k + 1 by omega)
    have hka : (1 : ℝ) ≤ (k + 1 : ℝ) - (a : ℝ) := by linarith
    have haj : (a : ℝ) ≤ j := by exact_mod_cast hakj.le
    have hprod : (a : ℝ) ≤ (j : ℝ) * ((k + 1 : ℝ) - (a : ℝ)) :=
      haj.trans (by nlinarith [mul_nonneg hjR.le (sub_nonneg.mpr (by linarith : (a : ℝ) ≤ k + 1))])
    unfold p
    field_simp
    nlinarith
  change binomialSliceWeight j (k + 1) p ≤ binomialSliceWeight j k p
  have hc : 0 < (k + 1 : ℝ) * (1 - p) := mul_pos (by positivity) hq0
  apply (mul_le_mul_iff_of_pos_right hc).mp
  calc
    binomialSliceWeight j (k + 1) p * ((k + 1 : ℝ) * (1 - p)) =
        binomialSliceWeight j k p * ((j - k : ℝ) * p) :=
      binomialSliceWeight_succ_balance p hkj
    _ ≤ binomialSliceWeight j k p * ((k + 1 : ℝ) * (1 - p)) :=
      mul_le_mul_of_nonneg_left hfactor (by
        unfold binomialSliceWeight
        positivity)

theorem binomialSliceWeight_le_mode {j a m : ℕ} (hj : 0 < j) (ha0 : 0 < a)
    (ha : a < j) (hm : m ≤ j) :
    binomialSliceWeight j m ((a : ℝ) / j) ≤
      binomialSliceWeight j a ((a : ℝ) / j) := by
  let w : ℕ → ℝ := fun k => binomialSliceWeight j k ((a : ℝ) / j)
  by_cases hma : m ≤ a
  · have hstep : ∀ k, k < a → w k ≤ w (k + 1) := by
      intro k hk
      exact binomialSliceWeight_succ_le_of_lt_mode hj ha hk
    have hind := Nat.le_induction (m := m)
      (P := fun n _ => n ≤ a → w m ≤ w n)
      (fun _ => le_rfl)
      (fun n _ ih hna => (ih (by omega)).trans (hstep n (by omega))) a hma
    exact hind le_rfl
  · have ham : a ≤ m := by omega
    have hstep : ∀ k, a ≤ k → k < j → w (k + 1) ≤ w k := by
      intro k hak hkj
      exact binomialSliceWeight_succ_ge_of_mode_le hj ha0 hak hkj
    have hind := Nat.le_induction (m := a)
      (P := fun n _ => n ≤ m → w n ≤ w a)
      (fun _ => le_rfl)
      (fun n han ih hnm =>
        (hstep n han (by omega)).trans (ih (by omega))) m ham
    exact hind le_rfl

/-- At `p = a/j`, the `a`-th binomial mass is at least the average of the `j+1` masses. -/
theorem one_div_succ_le_binomialSliceWeight_mode {j a : ℕ}
    (hj : 0 < j) (ha0 : 0 < a) (ha : a < j) :
    1 / (j + 1 : ℝ) ≤ binomialSliceWeight j a ((a : ℝ) / j) := by
  let p : ℝ := (a : ℝ) / j
  have hsumle :
      ∑ m ∈ Finset.range (j + 1), binomialSliceWeight j m p ≤
        (Finset.range (j + 1)).card • binomialSliceWeight j a p := by
    apply Finset.sum_le_card_nsmul
    intro m hm
    exact binomialSliceWeight_le_mode hj ha0 ha (by
      have := Finset.mem_range.mp hm
      omega)
  rw [sum_binomialSliceWeight] at hsumle
  simp only [Finset.card_range, nsmul_eq_mul] at hsumle
  have hj1 : (0 : ℝ) < j + 1 := by positivity
  apply (div_le_iff₀ hj1).2
  calc
    1 ≤ (j + 1 : ℝ) * binomialSliceWeight j a p := by simpa using hsumle
    _ = binomialSliceWeight j a p * (j + 1 : ℝ) := by ring

/-- Combining geometric reweighting with the mode bound gives a normalized slice estimate with
only the two harmless `j+1` losses: one for the optional terminal gap and one for conditioning on
the binomial slice. -/
theorem norm_sliceChar_le_mode_damping {j a ξ : ℕ}
    (hj : 0 < j) (ha0 : 0 < a) (ha : a < j) :
    ‖sliceChar j a ξ‖ ≤
      (j + 1 : ℝ) ^ 2 * (j.choose a : ℝ) *
        pascalDamping a ((a : ℝ) / j) ξ := by
  let p : ℝ := (a : ℝ) / j
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have haR : (0 : ℝ) < a := by exact_mod_cast ha0
  have hp0 : 0 < p := by unfold p; exact div_pos haR hjR
  have hp1 : p < 1 := by unfold p; exact (div_lt_one hjR).mpr (by exact_mod_cast ha)
  have hweighted := weighted_sliceChar_le_pascalDamping (j := j) (a := a) (ξ := ξ) hp0 hp1
  have hchoose : (0 : ℝ) ≤ j.choose a := by positivity
  have hweighted' :
      binomialSliceWeight j a p * ‖sliceChar j a ξ‖ ≤
        (j.choose a : ℝ) * ((j + 1 : ℝ) * pascalDamping a p ξ) := by
    have hm := mul_le_mul_of_nonneg_left hweighted hchoose
    unfold binomialSliceWeight
    calc
      (j.choose a : ℝ) * p ^ a * (1 - p) ^ (j - a) * ‖sliceChar j a ξ‖ =
          (j.choose a : ℝ) *
            (p ^ a * (1 - p) ^ (j - a) * ‖sliceChar j a ξ‖) := by ring
      _ ≤ (j.choose a : ℝ) * ((j + 1 : ℝ) * pascalDamping a p ξ) := hm
  have hmode : 1 / (j + 1 : ℝ) ≤ binomialSliceWeight j a p :=
    one_div_succ_le_binomialSliceWeight_mode hj ha0 ha
  have hconditioned :
      (1 / (j + 1 : ℝ)) * ‖sliceChar j a ξ‖ ≤
        (j.choose a : ℝ) * ((j + 1 : ℝ) * pascalDamping a p ξ) :=
    (mul_le_mul_of_nonneg_right hmode (norm_nonneg _)).trans hweighted'
  have hj1 : (0 : ℝ) < j + 1 := by positivity
  calc
    ‖sliceChar j a ξ‖ = (j + 1 : ℝ) *
        ((1 / (j + 1 : ℝ)) * ‖sliceChar j a ξ‖) := by field_simp
    _ ≤ (j + 1 : ℝ) *
        ((j.choose a : ℝ) * ((j + 1 : ℝ) * pascalDamping a p ξ)) :=
      mul_le_mul_of_nonneg_left hconditioned hj1.le
    _ = (j + 1 : ℝ) ^ 2 * (j.choose a : ℝ) * pascalDamping a p ξ := by ring

/-- A direct real-power calculation absorbing the two polynomial conditioning losses using
`j ≤ 5a`. -/
theorem succ_sq_mul_rpow_neg_add_three {A : ℝ} (hA : 0 < A) {j a : ℕ}
    (hj : 1 ≤ j) (hja : j ≤ 5 * a) :
    (j + 1 : ℝ) ^ 2 * (a : ℝ) ^ (-(A + 3)) ≤
      (4 * (5 : ℝ) ^ (A + 3)) * (j : ℝ) ^ (-A) := by
  have hjR : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hjOne : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have haR : (0 : ℝ) < a := by
    have : 0 < a := by omega
    exact_mod_cast this
  have hbase : (j : ℝ) / 5 ≤ a := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 5)).2
    exact_mod_cast (by simpa [Nat.mul_comm] using hja)
  have hscale : (a : ℝ) ^ (-(A + 3)) ≤
      ((j : ℝ) / 5) ^ (-(A + 3)) :=
    Real.rpow_le_rpow_of_nonpos (div_pos hjR (by norm_num)) hbase (by linarith)
  have hdiv : ((j : ℝ) / 5) ^ (-(A + 3)) =
      (5 : ℝ) ^ (A + 3) * (j : ℝ) ^ (-(A + 3)) := by
    calc
      ((j : ℝ) / 5) ^ (-(A + 3)) =
          (j : ℝ) ^ (-(A + 3)) / (5 : ℝ) ^ (-(A + 3)) :=
        Real.div_rpow hjR.le (by norm_num) _
      _ = ((j : ℝ) ^ (A + 3))⁻¹ / ((5 : ℝ) ^ (A + 3))⁻¹ := by
        rw [Real.rpow_neg hjR.le, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 5)]
      _ = (5 : ℝ) ^ (A + 3) * ((j : ℝ) ^ (A + 3))⁻¹ := by
        rw [div_inv_eq_mul]
        ring
      _ = (5 : ℝ) ^ (A + 3) * (j : ℝ) ^ (-(A + 3)) := by
        rw [Real.rpow_neg hjR.le]
  have hpoly : (j + 1 : ℝ) ^ 2 ≤ 4 * (j : ℝ) ^ 2 := by
    have hfac : 0 ≤ (3 * (j : ℝ) + 1) * ((j : ℝ) - 1) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr hjOne)
    nlinarith
  have hjdecay : (j : ℝ) ^ 2 * (j : ℝ) ^ (-(A + 3)) ≤
      (j : ℝ) ^ (-A) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_add hjR]
    apply Real.rpow_le_rpow_of_exponent_le hjOne
    ring_nf
    norm_num
  calc
    (j + 1 : ℝ) ^ 2 * (a : ℝ) ^ (-(A + 3)) ≤
        (j + 1 : ℝ) ^ 2 * ((j : ℝ) / 5) ^ (-(A + 3)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = (j + 1 : ℝ) ^ 2 *
        ((5 : ℝ) ^ (A + 3) * (j : ℝ) ^ (-(A + 3))) := by rw [hdiv]
    _ ≤ (4 * (j : ℝ) ^ 2) *
        ((5 : ℝ) ^ (A + 3) * (j : ℝ) ^ (-(A + 3))) :=
      mul_le_mul_of_nonneg_right hpoly
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hjR.le _))
    _ = (4 * (5 : ℝ) ^ (A + 3)) *
        ((j : ℝ) ^ 2 * (j : ℝ) ^ (-(A + 3))) := by ring
    _ ≤ (4 * (5 : ℝ) ^ (A + 3)) * (j : ℝ) ^ (-A) :=
      mul_le_mul_of_nonneg_left hjdecay
        (mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _))

/-- **Edge: the uniform damping bound gives slice character decay.**  Sketch (personal-c5's two
facts, `SliceDecay.lean`): write the slice law at `(j, a)` as `Σ_k 3^{k−1} 2^{−T_k} mod 3^a` with
`T` the partial sums of a uniform `a`-subset of `[1, j]`; that is iid `Geom(p)` gaps conditioned
on `T_a ≤ j < T_{a+1}`, for any `p`; pair the gaps, condition on the pair sums (uniform splits,
Tao 7.4–7.5), and bound the slice expectation of `∏|f| ≥ 0` by
`pascalDamping a p ξ / P_p(T_a ≤ j < T_{a+1})`; take `p = a/j ∈ [1/5, 3/5]`, where a local limit
theorem gives `P_p(slice) ≥ c j^{−1/2}` uniformly.  So `|sliceChar| / #slice ≤ C' j^{1/2} a^{−A}`,
and `a ≥ j/5`.  Confidence 85%. -/
theorem sliceCharDecay_of_pascalDampingDecay (h : PascalDampingDecay) : SliceCharDecay := by
  intro A hA
  obtain ⟨C, hC, hD⟩ := h (A + 3) (by linarith)
  refine ⟨4 * (5 : ℝ) ^ (A + 3) * C, ?_, ?_⟩
  · exact mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _)) hC
  · intro j a ξ hj hja haj hξ
    have hj0 : 0 < j := by omega
    have ha0 : 0 < a := by omega
    have haj' : a < j := by omega
    have hjR : (0 : ℝ) < j := by exact_mod_cast hj0
    let p : ℝ := (a : ℝ) / j
    have hpLow : 1 / 5 ≤ p := by
      change (1 : ℝ) / 5 ≤ (a : ℝ) / j
      rw [div_le_div_iff₀ (by norm_num) hjR]
      exact_mod_cast (by simpa [Nat.mul_comm] using hja)
    have hpHigh : p ≤ 3 / 5 := by
      change (a : ℝ) / j ≤ (3 : ℝ) / 5
      rw [div_le_div_iff₀ hjR (by norm_num)]
      exact_mod_cast (by simpa [Nat.mul_comm] using haj)
    have hDamp : pascalDamping a p ξ ≤ C * (a : ℝ) ^ (-(A + 3)) :=
      hD p hpLow hpHigh a ξ (by omega) hξ
    have hmode := norm_sliceChar_le_mode_damping (j := j) (a := a) (ξ := ξ) hj0 ha0 haj'
    have hfactor : 0 ≤ (j + 1 : ℝ) ^ 2 * (j.choose a : ℝ) := by positivity
    have hmid : ‖sliceChar j a ξ‖ ≤
        (j + 1 : ℝ) ^ 2 * (j.choose a : ℝ) *
          (C * (a : ℝ) ^ (-(A + 3))) :=
      hmode.trans (mul_le_mul_of_nonneg_left hDamp hfactor)
    have habsorb := succ_sq_mul_rpow_neg_add_three hA hj hja
    have hCchoose : 0 ≤ C * (j.choose a : ℝ) :=
      mul_nonneg hC.le (by positivity)
    rw [card_levelSet_eq_choose]
    calc
      ‖sliceChar j a ξ‖ ≤
          (j + 1 : ℝ) ^ 2 * (j.choose a : ℝ) *
            (C * (a : ℝ) ^ (-(A + 3))) := hmid
      _ = (C * (j.choose a : ℝ)) *
          ((j + 1 : ℝ) ^ 2 * (a : ℝ) ^ (-(A + 3))) := by ring
      _ ≤ (C * (j.choose a : ℝ)) *
          ((4 * (5 : ℝ) ^ (A + 3)) * (j : ℝ) ^ (-A)) :=
        mul_le_mul_of_nonneg_left habsorb hCchoose
      _ = (4 * (5 : ℝ) ^ (A + 3) * C) * (j : ℝ) ^ (-A) * (j.choose a : ℝ) := by
        ring

end CollatzMoonshot.Conjugacy
