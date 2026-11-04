/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Conjugacy.BeyondWords
import CollatzMoonshot.Conjugacy.Bridge3
import CollatzMoonshot.Conjugacy.SliceFourierRate

/-!
# Beyond-Terras uniformity at growing depth: logarithmic (unconditional) and linear (one node)

`BeyondWords.lean` proves that for every fixed `K` the residues `T^j r mod 2^K`, `r < 2^j`, are
asymptotically uniform (`beyondWordsUniform`).  This file asks how far past the Terras horizon
that uniformity reaches when `K` grows with `j`, measured in total variation:

    beyondTV j K = Σ_{c < 2^K} |beyondCount j K c / 2^j − 2^{−K}|.

* **Logarithmic depth, unconditional** (`beyondWordsUniformLog`): for every `C`, the first
  `C · log₂ j` letters past the horizon are jointly uniform.  The proof is the C1 pipeline of
  `SliceFourierGeneral.lean` run with its rate kept: on a slice `levelSet j a` in the window the
  centred residue count is `≤ 4(a+1) · C_A · j^{−A} · card` plus a sub-slice tail `≤ C a 3^{−j/12}
  card`, uniformly in `K` and `c` (`layeredWeight_resInd`, `SliceCharDecay`); summing over the
  `2^K = j^{C}` residues costs `j^C`, paid by `A = C + 2`; slices outside the window are
  `outOddSet j`, of size `O(2^j / j)`, and contribute at most twice their share to the TV sum.

* **Linear depth, one node** (`beyondWordsUniformLinear_of_sliceOscDecay`): the slice analogue
  of Tao 2019 Proposition 1.14 (`SliceOscDecay`: the oscillation of the slice law above the
  3-adic scale `m` is `≤ C m^{−A} · card`, for all `1 ≤ m ≤ a` in the window) gives uniformity
  to depth `K ≤ j/8`.  Mechanism: above scale `m` the slice law is within `levelOsc j a m` of a
  law that is uniform on every fibre `{c + 3^m t : t < 3^{a−m}}`; each fibre is an arithmetic
  progression with odd step, so its residues mod `2^K` are uniform up to `2^K / 3^{a−m}` per
  fibre; with `m = ⌊a/2⌋` and `a ≥ j/4` this is `≤ 2^{K − 0.198 j}`, which vanishes for
  `K ≤ j/8`.  The node implies `TruncatedSyracMixing` (`Bridge3.lean`) at once.  Its input,
  the sliced Proposition 1.17, is the theorem `sliceCharDecay`; the edge
  `SliceCharDecay → SliceOscDecay` is Tao's §6 for the sliced law and is NOT attempted here.

Both headline theorems are ensemble statements over all `j`-bit starts.  They say nothing about
any individual orbit, hence nothing about the Collatz conjecture.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB

/-- Total-variation distance, at depth `K`, between the beyond-Terras residues `T^j r mod 2^K`
over `r < 2^j` and the uniform distribution on `ℤ/2^K`. -/
noncomputable def beyondTV (j K : ℕ) : ℝ :=
  ∑ c ∈ Finset.range (2 ^ K), |(beyondCount j K c : ℝ) / 2 ^ j - 1 / 2 ^ K|

/-- **Node (frozen): the sliced Tao Proposition 1.14.**  On every slice in the window
`j ≤ 5a ≤ 3j` and at every 3-adic scale `1 ≤ m ≤ a`, the oscillation of the slice law above
scale `m` is a `C_A m^{−A}` fraction of the slice.  Its input, the sliced Proposition 1.17, is
the theorem `sliceCharDecay`; the edge is Tao's §6 argument for the sliced law.  Confidence
75% true; the probe is the exact `levelOsc` table (`experiments/conjugacy/`). -/
def SliceOscDecay : Prop :=
  ∀ A > (0 : ℝ), ∃ C > (0 : ℝ), ∀ j a m : ℕ, 1 ≤ m → m ≤ a → j ≤ 5 * a → 5 * a ≤ 3 * j →
    levelOsc j a m ≤ C * (m : ℝ) ^ (-A) * (levelSet j a).card

/-- **Linear-depth uniformity.**  For every `ε`, eventually in `j`, every depth `K ≤ κ j` has
`beyondTV j K ≤ ε`. -/
def BeyondWordsUniformLinear (κ : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∀ᶠ j : ℕ in atTop, ∀ K : ℕ, (K : ℝ) ≤ κ * j → beyondTV j K ≤ ε

/-- **Logarithmic-depth uniformity.**  For every `C` and `ε`, eventually in `j`, every depth
`K ≤ C log₂ j` has `beyondTV j K ≤ ε`. -/
def BeyondWordsUniformLog : Prop :=
  ∀ C : ℝ, ∀ ε > (0 : ℝ), ∀ᶠ j : ℕ in atTop, ∀ K : ℕ, (K : ℝ) ≤ C * Real.logb 2 j →
    beyondTV j K ≤ ε


/-! ## Total variation from slice-wise residue sums -/

/-- One start carries centred mass at most `2` summed over all residues `c < 2^K`. -/
theorem sum_norm_resInd_le (K y : ℕ) :
    ∑ c ∈ Finset.range (2 ^ K), ‖resInd K c y‖ ≤ 2 := by
  have hpt (c : ℕ) :
      ‖resInd K c y‖ ≤ (if y % 2 ^ K = c then (1 : ℝ) else 0) + ((2 : ℝ) ^ K)⁻¹ := by
    unfold resInd
    refine (norm_sub_le _ _).trans (add_le_add ?_ (le_of_eq ?_))
    · split_ifs <;> simp
    · simp
  have h1 : (2 : ℝ) ^ K * ((2 : ℝ) ^ K)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
  calc
    ∑ c ∈ Finset.range (2 ^ K), ‖resInd K c y‖ ≤
        ∑ c ∈ Finset.range (2 ^ K),
          ((if y % 2 ^ K = c then (1 : ℝ) else 0) + ((2 : ℝ) ^ K)⁻¹) :=
      Finset.sum_le_sum fun c _ => hpt c
    _ = (if y % 2 ^ K ∈ Finset.range (2 ^ K) then (1 : ℝ) else 0) +
        (2 : ℝ) ^ K * ((2 : ℝ) ^ K)⁻¹ := by
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
      push_cast
      ring
    _ ≤ 2 := by
      rw [h1]
      split_ifs <;> norm_num

/-- **Total variation from the slices.**  If on every central slice the residue sums of the
centred indicators total at most `M · #slice` over `c < 2^K`, then `beyondTV j K` is at most
`M` plus twice the non-central share: those starts are charged once as their counts and once as
their part of the uniform mass (`sum_norm_resInd_le`). -/
theorem beyondTV_le_of_slice (j K : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hslice : ∀ a, j ≤ 4 * a → a ≤ 11 * j / 20 →
      ∑ c ∈ Finset.range (2 ^ K), ‖∑ r ∈ levelSet j a, resInd K c (tstep^[j] r)‖ ≤
        M * (levelSet j a).card) :
    beyondTV j K ≤ M + 2 * ((outOddSet j).card : ℝ) / 2 ^ j := by
  let I := Finset.range (j + 1)
  let L := I.filter (fun a => j ≤ 4 * a ∧ a ≤ 11 * j / 20)
  let H := I.filter (fun a => 4 * a < j ∨ 11 * j / 20 < a)
  let S : ℕ → ℕ → ℂ := fun c a => ∑ r ∈ levelSet j a, resInd K c (tstep^[j] r)
  have hpowpos : (0 : ℝ) < 2 ^ j := by positivity
  have hterm (c : ℕ) : |(beyondCount j K c : ℝ) / 2 ^ j - 1 / 2 ^ K| =
      ‖∑ r ∈ Finset.range (2 ^ j), resInd K c (tstep^[j] r)‖ / 2 ^ j := by
    rw [sum_resInd_eq]
    have hr := Complex.norm_real ((beyondCount j K c : ℝ) - 2 ^ j * ((2 : ℝ) ^ K)⁻¹)
    push_cast at hr
    rw [hr, Real.norm_eq_abs]
    have heq : (beyondCount j K c : ℝ) / 2 ^ j - 1 / 2 ^ K =
        ((beyondCount j K c : ℝ) - 2 ^ j * ((2 : ℝ) ^ K)⁻¹) / 2 ^ j := by
      field_simp
    rw [heq, abs_div, abs_of_pos hpowpos]
  have hpartition (c : ℕ) : ∑ r ∈ Finset.range (2 ^ j), resInd K c (tstep^[j] r) =
      (∑ a ∈ L, S c a) + ∑ a ∈ H, S c a := by
    rw [sum_range_eq_sum_levelSet j (fun r => resInd K c (tstep^[j] r))]
    have hs := Finset.sum_filter_add_sum_filter_not I
      (fun a => j ≤ 4 * a ∧ a ≤ 11 * j / 20) (S c)
    rw [show I.filter (fun a => ¬(j ≤ 4 * a ∧ a ≤ 11 * j / 20)) = H by
      ext a
      simp [H]
      omega] at hs
    exact hs.symm
  have hHnorm (c : ℕ) : ‖∑ a ∈ H, S c a‖ ≤
      ∑ a ∈ H, ∑ r ∈ levelSet j a, ‖resInd K c (tstep^[j] r)‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
  have hLcard : ∑ a ∈ L, ((levelSet j a).card : ℝ) ≤ 2 ^ j := by
    calc
      ∑ a ∈ L, ((levelSet j a).card : ℝ) ≤
          ∑ a ∈ I, ((levelSet j a).card : ℝ) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => by positivity)
      _ = 2 ^ j := by
        exact_mod_cast sum_levelSet_card j
  have hHcard : ∑ a ∈ H, ((levelSet j a).card : ℝ) = (outOddSet j).card := by
    exact_mod_cast sum_out_levelSet_card j
  have hLsum : ∑ c ∈ Finset.range (2 ^ K), ∑ a ∈ L, ‖S c a‖ ≤ M * 2 ^ j := by
    rw [Finset.sum_comm]
    calc
      ∑ a ∈ L, ∑ c ∈ Finset.range (2 ^ K), ‖S c a‖ ≤
          ∑ a ∈ L, M * ((levelSet j a).card : ℝ) :=
        Finset.sum_le_sum fun a ha =>
          hslice a (Finset.mem_filter.mp ha).2.1 (Finset.mem_filter.mp ha).2.2
      _ = M * ∑ a ∈ L, ((levelSet j a).card : ℝ) := by rw [Finset.mul_sum]
      _ ≤ M * 2 ^ j := mul_le_mul_of_nonneg_left hLcard hM
  have hHsum : ∑ c ∈ Finset.range (2 ^ K),
      ∑ a ∈ H, ∑ r ∈ levelSet j a, ‖resInd K c (tstep^[j] r)‖ ≤
        2 * (outOddSet j).card := by
    rw [Finset.sum_comm]
    calc
      ∑ a ∈ H, ∑ c ∈ Finset.range (2 ^ K), ∑ r ∈ levelSet j a, ‖resInd K c (tstep^[j] r)‖ =
          ∑ a ∈ H, ∑ r ∈ levelSet j a,
            ∑ c ∈ Finset.range (2 ^ K), ‖resInd K c (tstep^[j] r)‖ := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_comm]
      _ ≤ ∑ a ∈ H, ∑ _r ∈ levelSet j a, (2 : ℝ) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun r _ => sum_norm_resInd_le K _
      _ = 2 * ∑ a ∈ H, ((levelSet j a).card : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
      _ = 2 * (outOddSet j).card := by rw [hHcard]
  unfold beyondTV
  calc
    ∑ c ∈ Finset.range (2 ^ K), |(beyondCount j K c : ℝ) / 2 ^ j - 1 / 2 ^ K| =
        (∑ c ∈ Finset.range (2 ^ K),
          ‖∑ r ∈ Finset.range (2 ^ j), resInd K c (tstep^[j] r)‖) / 2 ^ j := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun c _ => hterm c
    _ ≤ (∑ c ∈ Finset.range (2 ^ K), ((∑ a ∈ L, ‖S c a‖) +
          ∑ a ∈ H, ∑ r ∈ levelSet j a, ‖resInd K c (tstep^[j] r)‖)) / 2 ^ j := by
      gcongr with c hc
      rw [hpartition c]
      exact (norm_add_le _ _).trans (add_le_add (norm_sum_le _ _) (hHnorm c))
    _ ≤ (M * 2 ^ j + 2 * (outOddSet j).card) / 2 ^ j := by
      gcongr
      rw [Finset.sum_add_distrib]
      exact add_le_add hLsum hHsum
    _ = M + 2 * ((outOddSet j).card : ℝ) / 2 ^ j := by
      field_simp

/-- **Edge (elementary).**  The sliced Proposition 1.14 gives the truncated mixing node of
`Bridge3.lean`: take `m = ⌊a/2⌋`. -/
theorem truncatedSyracMixing_of_sliceOscDecay (h : SliceOscDecay) : TruncatedSyracMixing := by
  intro ε hε
  obtain ⟨C, hCpos, hC⟩ := h 1 one_pos
  obtain ⟨M, hM⟩ := exists_nat_gt ((C + 1) / ε)
  have hCM : C + 1 < ε * M := by
    rw [div_lt_iff₀ hε] at hM
    linarith
  filter_upwards [eventually_ge_atTop (8 * M + 16)] with j hj
  intro a hja haj
  refine ⟨a / 2, Nat.div_le_self a 2, ?_, ?_⟩
  · have hm1 : 1 ≤ a / 2 := by omega
    have hb := hC j a (a / 2) hm1 (Nat.div_le_self a 2) (by omega) (by omega)
    rw [Real.rpow_neg_one] at hb
    have hmM : (M : ℝ) ≤ ((a / 2 : ℕ) : ℝ) := by exact_mod_cast (show M ≤ a / 2 by omega)
    have hmpos : (0 : ℝ) < ((a / 2 : ℕ) : ℝ) := by exact_mod_cast hm1
    have hCm : C * (((a / 2 : ℕ) : ℝ))⁻¹ ≤ ε := by
      rw [← div_eq_mul_inv, div_le_iff₀ hmpos]
      nlinarith
    have hcard : (0 : ℝ) ≤ (levelSet j a).card := by positivity
    calc
      levelOsc j a (a / 2) ≤ C * (((a / 2 : ℕ) : ℝ))⁻¹ * (levelSet j a).card := hb
      _ ≤ ε * (levelSet j a).card := by gcongr
  · have hd : a / 2 + (a - a / 2) = a := by omega
    have hlt : a - a / 2 < 3 ^ (a - a / 2) := Nat.lt_pow_self (by norm_num)
    have hMd : M ≤ a - a / 2 := by omega
    have h3 : (M : ℝ) < (3 : ℝ) ^ (a - a / 2) := by
      exact_mod_cast (lt_of_le_of_lt hMd hlt)
    have h1 : 1 ≤ ε * (3 : ℝ) ^ (a - a / 2) := by nlinarith
    have hpow : (3 : ℝ) ^ a = 3 ^ (a / 2) * 3 ^ (a - a / 2) := by
      rw [← pow_add, hd]
    rw [hpow]
    calc
      (3 : ℝ) ^ (a / 2) = 3 ^ (a / 2) * 1 := by ring
      _ ≤ 3 ^ (a / 2) * (ε * 3 ^ (a - a / 2)) := by gcongr
      _ = ε * (3 ^ (a / 2) * 3 ^ (a - a / 2)) := by ring

/-! ## Linear depth: the fibre-progression bound -/

/-- Reindex `[0, Q·T)` as `d + Q t` with `d < Q`, `t < T`. -/
theorem sum_range_mul_eq_sum_sum {M : Type*} [AddCommMonoid M] (F : ℕ → M) (Q T : ℕ) :
    ∑ y ∈ Finset.range (Q * T), F y =
      ∑ d ∈ Finset.range Q, ∑ t ∈ Finset.range T, F (d + Q * t) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    simp only [Finset.sum_range_succ, Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro d _
    rw [add_comm]

/-- **An odd-step progression is equidistributed mod `2^K` up to one point.**  For `q` odd,
`#{t < T : d + q t ≡ c (mod 2^K)}` is within `1` of `T / 2^K`: the condition is a single residue
class of `t` (`q` is a unit mod `2^K`), counted by `Nat.count_modEq_card`. -/
theorem abs_card_progression_sub_le {q : ℕ} (hq : Nat.Coprime q 2) (K d c T : ℕ)
    (hc : c < 2 ^ K) :
    |(((Finset.range T).filter (fun t => (d + q * t) % 2 ^ K = c)).card : ℝ) - T / 2 ^ K| ≤ 1 := by
  have : NeZero (2 ^ K) := ⟨by positivity⟩
  have hcop : Nat.Coprime q (2 ^ K) := Nat.Coprime.pow_right K hq
  let u := ZMod.unitOfCoprime q hcop
  let t0 : ℕ := ((↑u⁻¹ * ((c : ZMod (2 ^ K)) - d)) : ZMod (2 ^ K)).val
  have hiff : ∀ t, (d + q * t) % 2 ^ K = c ↔ t ≡ t0 [MOD 2 ^ K] := by
    intro t
    have e1 : (d + q * t) % 2 ^ K = c ↔
        ((d + q * t : ℕ) : ZMod (2 ^ K)) = (c : ZMod (2 ^ K)) := by
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hc]
    have e2 : t ≡ t0 [MOD 2 ^ K] ↔
        (t : ZMod (2 ^ K)) = ↑u⁻¹ * ((c : ZMod (2 ^ K)) - d) := by
      rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
    rw [e1, e2, Units.eq_inv_mul_iff_mul_eq, ZMod.coe_unitOfCoprime]
    push_cast
    constructor <;> intro h <;> linear_combination h
  have hcard : ((Finset.range T).filter (fun t => (d + q * t) % 2 ^ K = c)).card =
      T / 2 ^ K + if t0 % 2 ^ K < T % 2 ^ K then 1 else 0 := by
    rw [← Nat.count_modEq_card T (by positivity) t0, Nat.count_eq_card_filter_range]
    congr 1
    exact Finset.filter_congr fun t _ => hiff t
  rw [hcard]
  have hdm := Nat.div_add_mod T (2 ^ K)
  have hmod := Nat.mod_lt T (show 0 < 2 ^ K by positivity)
  have hTR : (T : ℝ) = 2 ^ K * ((T / 2 ^ K : ℕ) : ℝ) + ((T % 2 ^ K : ℕ) : ℝ) := by
    exact_mod_cast hdm.symm
  have hmodR : ((T % 2 ^ K : ℕ) : ℝ) < 2 ^ K := by exact_mod_cast hmod
  have hp : (0 : ℝ) < 2 ^ K := by positivity
  have hdiv : (T : ℝ) / 2 ^ K = ((T / 2 ^ K : ℕ) : ℝ) + ((T % 2 ^ K : ℕ) : ℝ) / 2 ^ K := by
    rw [hTR]
    field_simp
  have hfrac0 : 0 ≤ ((T % 2 ^ K : ℕ) : ℝ) / 2 ^ K := by positivity
  have hfrac1 : ((T % 2 ^ K : ℕ) : ℝ) / 2 ^ K < 1 := by
    rw [div_lt_one hp]
    exact hmodR
  rw [hdiv, abs_le]
  split_ifs <;> push_cast <;> constructor <;> linarith

/-- The centred indicator summed along an odd-step progression is at most `1`. -/
theorem norm_sum_resInd_progression_le {q : ℕ} (hq : Nat.Coprime q 2) (K d c T : ℕ)
    (hc : c < 2 ^ K) :
    ‖∑ t ∈ Finset.range T, resInd K c (d + q * t)‖ ≤ 1 := by
  have h := abs_card_progression_sub_le hq K d c T hc
  have heq : ∑ t ∈ Finset.range T, resInd K c (d + q * t) =
      (((((Finset.range T).filter (fun t => (d + q * t) % 2 ^ K = c)).card : ℝ) -
        T / 2 ^ K : ℝ) : ℂ) := by
    unfold resInd
    rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    push_cast
    ring
  rw [heq, Complex.norm_real, Real.norm_eq_abs]
  exact h

/-- A slice sum of an observable of the iterate is the observable against the slice masses. -/
theorem sum_levelSet_eq_sum_mass (j a : ℕ) (g : ℕ → ℂ) :
    ∑ r ∈ levelSet j a, g (tstep^[j] r) =
      ∑ y ∈ Finset.range (3 ^ a), (levelMass j a y : ℂ) * g y := by
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := levelSet j a) (t := Finset.range (3 ^ a)) (g := fun r => tstep^[j] r)
    (fun r hr => Finset.mem_range.2 (by
      have hlt := tstep_iterate_lt_three_pow
        (Finset.mem_range.1 (Finset.mem_filter.1 hr).1)
      simpa [(Finset.mem_filter.1 hr).2] using hlt))
    (fun r => g (tstep^[j] r))
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro y _
  rw [levelMass, Finset.sum_congr rfl (fun r hr => congrArg g (Finset.mem_filter.1 hr).2),
    Finset.sum_const, nsmul_eq_mul]

/-- The classes mod `3^m` partition the slice. -/
theorem sum_levelClass_eq_card (j a m : ℕ) :
    ∑ c ∈ Finset.range (3 ^ m), (levelClass j a m c : ℝ) = (levelSet j a).card := by
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := levelSet j a) (t := Finset.range (3 ^ m))
    (g := fun r => tstep^[j] r % 3 ^ m)
    (fun r _ => Finset.mem_range.2 (Nat.mod_lt _ (pow_pos (by omega) _)))
    (fun _ => (1 : ℝ))
  calc
    ∑ c ∈ Finset.range (3 ^ m), (levelClass j a m c : ℝ) =
        ∑ c ∈ Finset.range (3 ^ m),
          ∑ r ∈ (levelSet j a).filter (fun r => tstep^[j] r % 3 ^ m = c), (1 : ℝ) := by
      simp [levelClass]
    _ = ∑ _r ∈ levelSet j a, (1 : ℝ) := hfiber
    _ = (levelSet j a).card := by simp

/-- **The slice-wise residue bound.**  For every scale `m ≤ a`, the residue sums of a slice total
at most twice its oscillation above scale `m`, plus `2^K · 3^{m−a}` per start: the fibrewise
uniform law is uniform mod `2^K` up to one point per fibre and residue
(`norm_sum_resInd_progression_le`). -/
theorem sum_norm_levelSum_resInd_le (j a m K : ℕ) (hma : m ≤ a) :
    ∑ c ∈ Finset.range (2 ^ K), ‖∑ r ∈ levelSet j a, resInd K c (tstep^[j] r)‖ ≤
      2 * levelOsc j a m + 2 ^ K * ((3 : ℝ) ^ m / 3 ^ a) * (levelSet j a).card := by
  let lam : ℕ → ℝ := fun y => (3 : ℝ) ^ m / 3 ^ a * levelClass j a m (y % 3 ^ m)
  let D : ℕ → ℝ := fun y => (levelMass j a y : ℝ) - lam y
  have hodd : Nat.Coprime (3 ^ m) 2 := Nat.Coprime.pow_left m (by norm_num)
  have hsplit (c : ℕ) : ∑ r ∈ levelSet j a, resInd K c (tstep^[j] r) =
      ∑ y ∈ Finset.range (3 ^ a), ((D y : ℝ) : ℂ) * resInd K c y +
        ∑ y ∈ Finset.range (3 ^ a), ((lam y : ℝ) : ℂ) * resInd K c y := by
    rw [sum_levelSet_eq_sum_mass, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y _
    simp only [D]
    push_cast
    ring
  have hlam (c : ℕ) (hc : c < 2 ^ K) :
      ‖∑ y ∈ Finset.range (3 ^ a), ((lam y : ℝ) : ℂ) * resInd K c y‖ ≤
        (3 : ℝ) ^ m / 3 ^ a * (levelSet j a).card := by
    have hpow : 3 ^ a = 3 ^ m * 3 ^ (a - m) := by rw [← pow_add, Nat.add_sub_of_le hma]
    rw [hpow, sum_range_mul_eq_sum_sum]
    have hinner (d : ℕ) (hd : d ∈ Finset.range (3 ^ m)) :
        ∑ t ∈ Finset.range (3 ^ (a - m)),
            ((lam (d + 3 ^ m * t) : ℝ) : ℂ) * resInd K c (d + 3 ^ m * t) =
          (((3 : ℝ) ^ m / 3 ^ a * levelClass j a m d : ℝ) : ℂ) *
            ∑ t ∈ Finset.range (3 ^ (a - m)), resInd K c (d + 3 ^ m * t) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      have hmod : (d + 3 ^ m * t) % 3 ^ m = d := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Finset.mem_range.1 hd)]
      simp only [lam, hmod]
    rw [Finset.sum_congr rfl hinner]
    calc
      ‖∑ d ∈ Finset.range (3 ^ m),
          (((3 : ℝ) ^ m / 3 ^ a * levelClass j a m d : ℝ) : ℂ) *
            ∑ t ∈ Finset.range (3 ^ (a - m)), resInd K c (d + 3 ^ m * t)‖ ≤
          ∑ d ∈ Finset.range (3 ^ m),
            ‖(((3 : ℝ) ^ m / 3 ^ a * levelClass j a m d : ℝ) : ℂ) *
              ∑ t ∈ Finset.range (3 ^ (a - m)), resInd K c (d + 3 ^ m * t)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ d ∈ Finset.range (3 ^ m), (3 : ℝ) ^ m / 3 ^ a * levelClass j a m d := by
        apply Finset.sum_le_sum
        intro d _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have hb := norm_sum_resInd_progression_le hodd K d c (3 ^ (a - m)) hc
        calc
          (3 : ℝ) ^ m / 3 ^ a * levelClass j a m d *
              ‖∑ t ∈ Finset.range (3 ^ (a - m)), resInd K c (d + 3 ^ m * t)‖ ≤
              (3 : ℝ) ^ m / 3 ^ a * levelClass j a m d * 1 := by gcongr
          _ = (3 : ℝ) ^ m / 3 ^ a * levelClass j a m d := mul_one _
      _ = (3 : ℝ) ^ m / 3 ^ a * (levelSet j a).card := by
        rw [← Finset.mul_sum, sum_levelClass_eq_card]
  have hD (c : ℕ) :
      ‖∑ y ∈ Finset.range (3 ^ a), ((D y : ℝ) : ℂ) * resInd K c y‖ ≤
        ∑ y ∈ Finset.range (3 ^ a), |D y| * ‖resInd K c y‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    apply Finset.sum_congr rfl
    intro y _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hosc : levelOsc j a m = ∑ y ∈ Finset.range (3 ^ a), |D y| := rfl
  have hDsum : ∑ c ∈ Finset.range (2 ^ K),
      ∑ y ∈ Finset.range (3 ^ a), |D y| * ‖resInd K c y‖ ≤ 2 * levelOsc j a m := by
    rw [Finset.sum_comm, hosc, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro y _
    rw [← Finset.mul_sum]
    have := sum_norm_resInd_le K y
    have hDy : 0 ≤ |D y| := abs_nonneg _
    nlinarith
  calc
    ∑ c ∈ Finset.range (2 ^ K), ‖∑ r ∈ levelSet j a, resInd K c (tstep^[j] r)‖ ≤
        ∑ c ∈ Finset.range (2 ^ K),
          (∑ y ∈ Finset.range (3 ^ a), |D y| * ‖resInd K c y‖ +
            (3 : ℝ) ^ m / 3 ^ a * (levelSet j a).card) := by
      apply Finset.sum_le_sum
      intro c hc
      rw [hsplit c]
      exact (norm_add_le _ _).trans (add_le_add (hD c) (hlam c (Finset.mem_range.1 hc)))
    _ = ∑ c ∈ Finset.range (2 ^ K), ∑ y ∈ Finset.range (3 ^ a), |D y| * ‖resInd K c y‖ +
          2 ^ K * ((3 : ℝ) ^ m / 3 ^ a) * (levelSet j a).card := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring
    _ ≤ 2 * levelOsc j a m + 2 ^ K * ((3 : ℝ) ^ m / 3 ^ a) * (levelSet j a).card := by
      linarith

/-- **Edge: linear depth from the sliced Proposition 1.14** (the fibre-progression argument of
the module docstring, with `m = ⌊a/2⌋` and the `outOddSet` tail). -/
theorem beyondWordsUniformLinear_of_sliceOscDecay (h : SliceOscDecay) :
    BeyondWordsUniformLinear (1 / 8) := by
  sorry

/-- **Theorem (unconditional): logarithmic depth.**  The first `C log₂ j` letters past the
Terras horizon are jointly uniform, for every `C`. -/
theorem beyondWordsUniformLog : BeyondWordsUniformLog := by
  intro C ε hε
  have h := sliceCharDecay_of_pascalDampingDecay pascalDampingDecay
  obtain ⟨C', hC'pos, hslice⟩ := exists_norm_levelSum_le_rate h (⌈C⌉₊ + 2) (by omega)
  have hsmall := (tendsto_logMajorant C' ⌈C⌉₊).eventually (gt_mem_nhds (half_pos hε))
  have htail := (tendsto_const_div_atTop_nhds_zero_nat (200 : ℝ)).eventually
    (gt_mem_nhds (half_pos hε))
  filter_upwards [hsmall, htail, eventually_ge_atTop 4096] with j hjM hjt hj
  intro K hK
  set N := ⌈C⌉₊ with hN
  have hjR1 : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
  have hjRpos : (0 : ℝ) < j := by linarith
  have h2K : (2 : ℝ) ^ K ≤ (j : ℝ) ^ N := by
    have hlog : (K : ℝ) ≤ Real.logb 2 ((j : ℝ) ^ N) := by
      rw [Real.logb_pow]
      have h0 : 0 ≤ Real.logb 2 (j : ℝ) := Real.logb_nonneg one_lt_two hjR1
      have hCN : C ≤ (N : ℝ) := Nat.le_ceil C
      nlinarith [mul_le_mul_of_nonneg_right hCN h0]
    rw [Real.le_logb_iff_rpow_le one_lt_two (by positivity), Real.rpow_natCast] at hlog
    exact hlog
  have hM0 : 0 ≤ logMajorant C' N j := by unfold logMajorant; positivity
  have hper : ∀ a, j ≤ 4 * a → a ≤ 11 * j / 20 →
      ∑ c ∈ Finset.range (2 ^ K), ‖∑ r ∈ levelSet j a, resInd K c (tstep^[j] r)‖ ≤
        logMajorant C' N j * (levelSet j a).card := by
    intro a hja haj
    let E : ℝ := (2 ^ (N + 2) * C' / (j : ℝ) ^ (N + 2) +
        (j : ℝ) * ((7 : ℝ) / 8) ^ (j / 16 - j / 32)) * (4 * (j + 1)) +
      ((3 : ℝ) ^ (j / 4096))⁻¹ * (4 * (j + 1))
    have hE0 : 0 ≤ E := by positivity
    have hcard : (0 : ℝ) ≤ (levelSet j a).card := by positivity
    have hpt : ∀ c ∈ Finset.range (2 ^ K),
        ‖∑ r ∈ levelSet j a, resInd K c (tstep^[j] r)‖ ≤ E * (levelSet j a).card := by
      intro c hc
      have hb := hslice j a hj hja haj (resInd K c) 1
        (layeredWeight_resInd (Finset.mem_range.mp hc) a)
      have haj' : (a : ℝ) + 1 ≤ (j : ℝ) + 1 := by
        have : a ≤ j := by omega
        have : (a : ℝ) ≤ j := by exact_mod_cast this
        linarith
      calc
        ‖∑ r ∈ levelSet j a, resInd K c (tstep^[j] r)‖ ≤ _ := hb
        _ ≤ E * (levelSet j a).card := by
          rw [one_mul]
          dsimp only [E]
          gcongr
    calc
      ∑ c ∈ Finset.range (2 ^ K), ‖∑ r ∈ levelSet j a, resInd K c (tstep^[j] r)‖ ≤
          ∑ _c ∈ Finset.range (2 ^ K), E * (levelSet j a).card := Finset.sum_le_sum hpt
      _ = (2 : ℝ) ^ K * (E * (levelSet j a).card) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
      _ ≤ (j : ℝ) ^ N * (E * (levelSet j a).card) := by gcongr
      _ = logMajorant C' N j * (levelSet j a).card := by
        simp only [logMajorant, E]
        ring
  have hTV := beyondTV_le_of_slice j K hM0 hper
  have hout := outOddSet_ratio_le j (by omega)
  have h2out : 2 * ((outOddSet j).card : ℝ) / 2 ^ j ≤ 200 / j := by
    rw [mul_div_assoc]
    have : (200 : ℝ) / j = 2 * (100 / j) := by ring
    rw [this]
    linarith
  linarith

/-- Consistency: logarithmic-depth uniformity recovers the fixed-`K` statement of
`BeyondWords.lean`. -/
theorem beyondWordsUniform_of_log (h : BeyondWordsUniformLog) : BeyondWordsUniform := by
  intro K c hc
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h1 := h 1 (ε / 2) (half_pos hε)
  have hlog : ∀ᶠ j : ℕ in atTop, (K : ℝ) ≤ 1 * Real.logb 2 j := by
    have ht : Tendsto (fun j : ℕ => Real.logb 2 j) atTop atTop :=
      (Real.tendsto_logb_atTop one_lt_two).comp tendsto_natCast_atTop_atTop
    simpa using ht.eventually_ge_atTop (K : ℝ)
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (h1.and hlog)
  refine ⟨J, fun j hj => ?_⟩
  obtain ⟨hTV, hK⟩ := hJ j hj
  have hb := hTV K hK
  rw [Real.dist_eq]
  have hle : |(beyondCount j K c : ℝ) / 2 ^ j - 1 / 2 ^ K| ≤ beyondTV j K :=
    Finset.single_le_sum (f := fun c => |(beyondCount j K c : ℝ) / 2 ^ j - 1 / 2 ^ K|)
      (fun _ _ => abs_nonneg _) (Finset.mem_range.2 hc)
  linarith

end CollatzMoonshot.Conjugacy
