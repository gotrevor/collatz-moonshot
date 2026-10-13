/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalContinuousReversor

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

/-- **Target.**  An orbit whose even steps have limiting frequency `c < 2 − log₂ 3` spends
`2 − c > log₂ 3` bits per step, so it is periodic by `escape_forward`. -/
theorem periodic_of_evenFrequency_lt (m : ℤ) (c : ℝ) (hc : c < 2 - Real.logb 2 3)
    (h : Filter.Tendsto (fun k : ℕ =>
      (((Finset.range k).filter fun j => stepSym (amusical^[j] m) = 0).card : ℝ) / k)
      Filter.atTop (nhds c)) :
    ∃ p ≥ 1, amusical^[p] m = m := by
  sorry

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
  sorry

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
  sorry

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
  sorry

end CollatzMoonshot.Amusical
