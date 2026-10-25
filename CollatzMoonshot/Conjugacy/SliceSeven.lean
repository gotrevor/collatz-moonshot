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

/-- Tao's pair factor (7.4): `f(x, b) = (b−1)⁻¹ Σ_{a=1}^{b−1} e(−x(2^a + 3)/3^n)`, the conditional
expectation of the pair's character given its sum `b` (uniform over the `b − 1` splits, for any
gap law `Geom(p)`). -/
noncomputable def fPair (n : ℕ) (x : ZMod (3 ^ n)) (b : ℕ) : ℂ :=
  ((b : ℂ) - 1)⁻¹ * ∑ a ∈ Finset.Icc 1 (b - 1), charZ n (x * (2 ^ a + 3))

/-- The argument `x_j = ξ · 3^{2j} · 2^{−s}` at prefix pair-sum `s` (0-indexed `j`). -/
noncomputable def xArg (n ξ j s : ℕ) : ZMod (3 ^ n) :=
  (ξ : ZMod (3 ^ n)) * 3 ^ (2 * j) * (2 : ZMod (3 ^ n))⁻¹ ^ s

/-- The pair-sum law `Pascal(p)`: the sum of two iid `Geom(p)` gaps on `{1, 2, …}`,
`P(b) = (b−1) p² (1−p)^{b−2}` for `b ≥ 2`. -/
noncomputable def pascalWeight (p : ℝ) (b : ℕ) : ℝ :=
  if 2 ≤ b then ((b : ℝ) - 1) * p ^ 2 * (1 - p) ^ (b - 2) else 0

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
