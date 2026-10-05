/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# The ceiling of Flatto's Z-number count

A **Z-number** (Mahler 1968) is `ξ > 0` with `{ξ (3/2)^n} < 1/2` for every `n`.  Mahler bounded
their count below `X` by `O(X^0.7)`; Flatto (*Z-numbers and β-transformations*, Contemp. Math. 135,
1992) improved this to `O(X^θ)`, `θ = log₂(3/2) ≈ 0.585`.  No later improvement was found
(searched 2026-10-05).

Writing `ξ (3/2)^i = g_i + r_i`, the integer parts follow Mahler's map `g ↦ ⌈3g/2⌉` and the
fractional parts follow the slope-`3/2` map `rstep` on `[0, 1/2)`; `g_i` is odd exactly when
`r_i ≥ 1/3`.  So the parity word of `⌊ξ⌋` is an itinerary of `rstep`.

This file states why the bound stops at `log₂(3/2)`.  A start `g < 2^n` determines exactly its
first `n` parities, and every residue class mod `2^n` is realized (Terras's bijection,
`parityWord_injective`).  The admissible itineraries number at least `(3/2)^n`
(`card_admissible_ge`).  Hence any argument that reads only the first `⌊log₂ X⌋` parities of
`g < X` keeps at least `X^{log₂(3/2)}` candidates.  To beat Flatto you must read parities past
the 2-adic horizon, which is the open part of Mahler's problem.  Maze row: "within-horizon
refinement of Flatto's Z-number count".
-/

namespace CollatzMoonshot.Benchmark.FlattoCeiling

/-- A Z-number: `ξ > 0` and every `ξ (3/2)^n` has fractional part below `1/2`. -/
def IsZNumber (ξ : ℝ) : Prop := 0 < ξ ∧ ∀ n : ℕ, Int.fract (ξ * (3 / 2) ^ n) < 1 / 2

/-- Mahler's integer map `g ↦ ⌈3g/2⌉`, in Terras form. -/
def mstep (g : ℕ) : ℕ := (3 * g + g % 2) / 2

/-- The first `n` parities of the `mstep` orbit of `g` (`true` = odd). -/
def parityWord (n : ℕ) (g : ℕ) : Fin n → Bool := fun i => decide ((mstep^[i.val] g) % 2 = 1)

/-- The fractional-part map on `[0, 1/2)`: slope `3/2`, a cut at `1/3`. -/
noncomputable def rstep (r : ℝ) : ℝ := if r < 1 / 3 then 3 * r / 2 else 3 * r / 2 - 1 / 2

/-- `w` is an itinerary of `rstep`: some `r ∈ [0, 1/2)` has `rstep^[i] r ≥ 1/3` exactly at the
`true` letters of `w`. -/
def Admissible {n : ℕ} (w : Fin n → Bool) : Prop :=
  ∃ r ∈ Set.Ico (0 : ℝ) (1 / 2), ∀ i : Fin n, w i = true ↔ 1 / 3 ≤ rstep^[i.val] r

/-- The parity word depends only on `g mod 2^n`.
Confidence 98%.  Proof: induct on `n` with `mstep (g + 2^(k+1) t) = mstep g + 3·2^k t`
(adding an even number keeps the parity of `g`). -/
theorem parityWord_add_pow (n g t : ℕ) : parityWord n (g + 2 ^ n * t) = parityWord n g := by
  sorry

/-- Terras's bijection for Mahler's map: distinct residues below `2^n` have distinct parity words,
so (by counting) every word of length `n` occurs exactly once.
Confidence 97%.  Proof: the least index where `g ≠ g'` differ mod `2^(i+1)` is read off by the
`i`-th parity, via the same identity as `parityWord_add_pow`. -/
theorem parityWord_injective (n : ℕ) :
    Function.Injective (fun g : Fin (2 ^ n) => parityWord n (g : ℕ)) := by
  sorry

/-- The parity word of a Z-number's integer part is admissible: `r = {ξ}` realizes it.
Confidence 95%.  Proof: with `ξ (3/2)^i = g_i + r_i`, `0 ≤ r_i < 1/2`, Mahler's eq. (2) gives
`g_{i+1} = mstep g_i` and `r_{i+1} = rstep r_i`, and `g_i` odd iff `r_i ≥ 1/3` (an even `g_i`
needs `3r_i/2 < 1/2`; an odd one needs `1/2 + 3r_i/2 ≥ 1`). -/
theorem zNumber_parityWord_admissible {ξ : ℝ} (h : IsZNumber ξ) (n : ℕ) :
    Admissible (parityWord n ⌊ξ⌋₊) := by
  sorry

open Classical in
/-- **The ceiling.**  At least `(3/2)^n` words of length `n` are admissible.
Confidence 95%.  Proof: the cylinders `{r ∈ [0,1/2) : itinerary w}` partition `[0, 1/2)`; on each,
`rstep^[n]` is affine with slope `(3/2)^n` into `[0, 1/2)`, so each has length at most
`(1/2)(2/3)^n`, and their lengths sum to `1/2`. -/
theorem card_admissible_ge (n : ℕ) :
    ((3 : ℝ) / 2) ^ n ≤ ((Finset.univ : Finset (Fin n → Bool)).filter Admissible).card := by
  sorry

open Classical in
/-- The ceiling in counting form: at least `(3/2)^n` starts `g < 2^n` pass every within-horizon
test.  With `X = 2^n` that is `X^{log₂(3/2)}`, Flatto's exponent.
Confidence 95%.  Proof: `parityWord_injective` is a bijection onto all words (equal finite
cardinalities), then `card_admissible_ge`. -/
theorem card_admissible_starts_ge (n : ℕ) :
    ((3 : ℝ) / 2) ^ n ≤
      ((Finset.range (2 ^ n)).filter fun g => Admissible (parityWord n g)).card := by
  sorry

end CollatzMoonshot.Benchmark.FlattoCeiling
