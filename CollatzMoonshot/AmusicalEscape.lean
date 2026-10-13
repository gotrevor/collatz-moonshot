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

/-- **Target (Lemma E).**  A non-periodic forward orbit spends at most `log₂ 3 + δ` bits per
step infinitely often. -/
theorem escape_forward (m : ℤ) (hm : ∀ k ≥ 1, amusical^[k] m ≠ m) (δ : ℝ) (hδ : 0 < δ)
    (K : ℕ) : ∃ k ≥ K, (fwdBits m k : ℝ) ≤ (Real.logb 2 3 + δ) * k := by
  sorry

/-- **Target (Lemma E′).**  A non-periodic backward orbit spends at least `log₂ 3 − δ` bits per
step infinitely often. -/
theorem escape_backward (m : ℤ) (hm : ∀ k ≥ 1, amusical^[k] m ≠ m) (δ : ℝ) (hδ : 0 < δ)
    (K : ℕ) : ∃ k ≥ K, (Real.logb 2 3 - δ) * k ≤ (bwdBits m k : ℝ) := by
  sorry

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
