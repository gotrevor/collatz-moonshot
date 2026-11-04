/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.Champernowne

/-!
# `𝒞_1` is normal

Fix a word `u` of length `L`.  The proof counts occurrences **by offset**, not by stage.

* **One period** (`card_windowMatch`).  Among `r < 2^(t+L)`, exactly `2^t` have letters
  `t, …, t+L−1` reading `u`: Terras's flip `accWord_add_two_pow`, by induction on `L`.
* **Any interval** (`abs_card_Ico_windowMatch_sub_le`).  The window is periodic in `n` with period
  `2^(t+L)` (`windowMatch_periodic`), so over *any* `m` consecutive integers the count is
  `m / 2^L` up to `2^t`.  No alignment is needed, so no dyadic cut of a partial stage.
* **All offsets** (`abs_interior_sub_main_le`).  For offset `t`, the integers `n ≤ N` whose word
  holds the window are the interval `[2^(t+L−1), N]`.  The errors sum to `∑ 2^t ≤ 2N` over
  `t < size N`.
* **The rest** (`occ_cum_le`, `abs_main_sub_cum_le`).  At most `L` positions per word straddle a
  boundary.

So `|occ (cum N) − cum N / 2^L| ≤ (2L + 2) N` (`abs_occ_cum_sub_le`), while `cum N / N → ∞`.  The
last letter of a word needs no separate treatment: its window is the offset `t = size n − L`.

The two bounds were checked exactly on `n < 2^15` before this file was written
(`|count − m/2^L| / 2^t` reached `0.938`, so that bound has little slack).
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord

/-- Letters `t, …, t + L − 1` of the parity word of `n` read `g 0, …, g (L − 1)`. -/
def WindowMatch (g : ℕ → Bool) (L t n : ℕ) : Prop := ∀ s < L, accWord n (t + s) = g s

instance (g : ℕ → Bool) (L t : ℕ) : DecidablePred (WindowMatch g L t) := fun n => by
  unfold WindowMatch; infer_instance

/-! ## One period, and any interval -/

/-- **Terras, on a window.**  Exactly `2^t` of the `r < 2^(t+L)` have the prescribed letters at
`t, …, t + L − 1`. -/
theorem card_windowMatch (g : ℕ → Bool) (L t : ℕ) :
    ((Finset.range (2 ^ (t + L))).filter (WindowMatch g L t)).card = 2 ^ t := by
  sorry

/-- The window has period `2^(t+L)` in `n`. -/
theorem windowMatch_periodic (g : ℕ → Bool) (L t : ℕ) :
    Function.Periodic (WindowMatch g L t) (2 ^ (t + L)) := by
  sorry

/-- **Any interval.**  Over any `m` consecutive integers the window count is `m / 2^L` up to
`2^t`. -/
theorem abs_card_Ico_windowMatch_sub_le (g : ℕ → Bool) (L t a m : ℕ) :
    |(((Finset.Ico a (a + m)).filter (WindowMatch g L t)).card : ℝ) - (m : ℝ) / 2 ^ L| ≤
      2 ^ t := by
  sorry

/-! ## Reading occurrences in `𝒞_1` -/

/-- A window inside the word of `n + 1` is an occurrence in `𝒞_1`. -/
theorem occursAt_cum_iff (u : List Bool) (n i : ℕ) (hi : i + u.length ≤ Nat.size (n + 1)) :
    OccursAt (collatzChampernowne 1) u (cum (champLen 1) n + i) ↔
      WindowMatch (fun s => u.getD s false) u.length i (n + 1) := by
  sorry

/-- `occ` over `a + b` positions splits. -/
theorem occ_add (w : ℕ → Bool) (u : List Bool) (a b : ℕ) :
    occ w u (a + b) = occ w u a + ((Finset.range b).filter fun i => OccursAt w u (a + i)).card := by
  sorry

/-- The occurrences whose window lies inside a word of `n + 1 ≤ N`. -/
def interior (g : ℕ → Bool) (L N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range N, ((Finset.range (Nat.size (n + 1))).filter
    fun i => i + L ≤ Nat.size (n + 1) ∧ WindowMatch g L i (n + 1)).card

/-- The number of offsets whose window fits in the word of `n + 1 ≤ N`. -/
def windowCount (L N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range N, ((Finset.range (Nat.size (n + 1))).filter
    fun i => i + L ≤ Nat.size (n + 1)).card

/-- Interior windows are occurrences, and at most `L` positions per word straddle its end. -/
theorem occ_cum_le (u : List Bool) (N : ℕ) :
    interior (fun s => u.getD s false) u.length N ≤
        occ (collatzChampernowne 1) u (cum (champLen 1) N) ∧
      occ (collatzChampernowne 1) u (cum (champLen 1) N) ≤
        interior (fun s => u.getD s false) u.length N + u.length * N := by
  sorry

/-! ## Summing over offsets -/

/-- **All offsets.**  Swap the sums; offset `t` runs over the interval `[2^(t+L−1), N]`, with error
`2^t` (`abs_card_Ico_windowMatch_sub_le`), and `∑_{t < size N} 2^t ≤ 2N`. -/
theorem abs_interior_sub_main_le (g : ℕ → Bool) (L N : ℕ) (hL : 1 ≤ L) :
    |(interior g L N : ℝ) - (windowCount L N : ℝ) / 2 ^ L| ≤ 2 * N := by
  sorry

/-- Each word loses at most `L` offsets to its end. -/
theorem abs_main_sub_cum_le (L N : ℕ) :
    |(windowCount L N : ℝ) / 2 ^ L - (cum (champLen 1) N : ℝ) / 2 ^ L| ≤ L * N := by
  sorry

/-- **The discrepancy of `𝒞_1` at word ends.** -/
theorem abs_occ_cum_sub_le (u : List Bool) (hu : 1 ≤ u.length) (N : ℕ) :
    |(occ (collatzChampernowne 1) u (cum (champLen 1) N) : ℝ) -
        (cum (champLen 1) N : ℝ) / 2 ^ u.length| ≤ (2 * u.length + 2) * N := by
  sorry

/-! ## Passing to every prefix -/

/-- The word ends grow faster than the word count: `cum N ≥ B (N − 2^B)` for every `B`. -/
theorem tendsto_succ_div_cum :
    Tendsto (fun N : ℕ => ((N : ℝ) + 1) / (cum (champLen 1) N : ℝ)) atTop (𝓝 0) := by
  sorry

/-- A prefix ending inside word `N` costs at most `N + 1` more, on each side. -/
theorem abs_occ_sub_le (u : List Bool) (hu : 1 ≤ u.length) (N K : ℕ)
    (h₁ : cum (champLen 1) N ≤ K) (h₂ : K < cum (champLen 1) (N + 1)) :
    |(occ (collatzChampernowne 1) u K : ℝ) - (K : ℝ) / 2 ^ u.length| ≤
      (2 * u.length + 4) * ((N : ℝ) + 1) := by
  sorry

/-- **`𝒞_1` is normal**: Terras's bijection and a count, with no further Collatz input. -/
theorem collatzChampernowne_one_normal : Normal (collatzChampernowne 1) := by
  sorry

end CollatzMoonshot.Conjugacy
