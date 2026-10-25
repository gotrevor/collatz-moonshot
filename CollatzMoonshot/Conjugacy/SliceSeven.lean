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

/-- **Edge: the uniform damping bound gives slice character decay.**  Sketch (personal-c5's two
facts, `SliceDecay.lean`): write the slice law at `(j, a)` as `Σ_k 3^{k−1} 2^{−T_k} mod 3^a` with
`T` the partial sums of a uniform `a`-subset of `[1, j]`; that is iid `Geom(p)` gaps conditioned
on `T_a ≤ j < T_{a+1}`, for any `p`; pair the gaps, condition on the pair sums (uniform splits,
Tao 7.4–7.5), and bound the slice expectation of `∏|f| ≥ 0` by
`pascalDamping a p ξ / P_p(T_a ≤ j < T_{a+1})`; take `p = a/j ∈ [1/5, 3/5]`, where a local limit
theorem gives `P_p(slice) ≥ c j^{−1/2}` uniformly.  So `|sliceChar| / #slice ≤ C' j^{1/2} a^{−A}`,
and `a ≥ j/5`.  Confidence 85%. -/
theorem sliceCharDecay_of_pascalDampingDecay (h : PascalDampingDecay) : SliceCharDecay := by
  sorry

end CollatzMoonshot.Conjugacy
