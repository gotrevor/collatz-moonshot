/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.OrbitWordLawOrbit

/-!
# The orbit word law: the probabilistic side

`winLaw x` is Tao's log-uniform law on the odd numbers in `[x^α, x^(α²)]`.

* **Terras, with constraints** (`card_match_set`): among `r < 2^m`, prescribing the letters at any
  set `S` of positions below `m` leaves `2^(m − |S|)` of them.
* **Chebyshev on a block** (`sum_sq_wdev_le`, `card_bad_block_le`): occurrences of `u` at positions
  at least `|u|` apart are uncorrelated, so the second moment of the count over a block of `b`
  start positions is at most `2 |u| b` per residue.
* **Blocks give windows** (`winGood_of_blocks`): a deviation is `1`-Lipschitz in the end point, so
  good blocks of length `b ≤ δ H / 8` make every window of length `≥ H` good.  Boundedly many
  blocks cover the first `2 Λ` letters, so `¬ WinGood` has probability `O(1 / (δ² η log x))`
  over residues (`card_not_winGood_le`).
* **Transfer** (`prob_periodic_le`): an event that only sees `N mod 2^(3 n₀)` has nearly the same
  probability under `winLaw x` as over odd residues, by Tao's integral test.
* **The chain** (`dTV_chain`): by Tao's Proposition 1.11 at each scale, data processing, and
  `passLoc_passLoc`, the law of the passage location below `x_j` of a start drawn from `winLaw x`
  is close to that of a start drawn from `winLaw x_j`.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord
open TaoCollatz

/-- Tao's window law at scale `x`: log-uniform on the odd numbers in `[x^α, x^(α²)]`. -/
noncomputable def winLaw (x : ℝ) : PMF ℕ := logUnifOdd (x ^ alpha) (x ^ alpha ^ 2)

/-! ## Terras with constraints, and Chebyshev on a block -/

/-- **Terras, with constraints.**  Prescribing the letters at the positions of `S ⊆ [0, m)` leaves
exactly `2^(m − |S|)` of the residues `r < 2^m`. -/
theorem card_match_set (g : ℕ → Bool) (S : Finset ℕ) (m : ℕ) (hS : ∀ s ∈ S, s < m) :
    ((Finset.range (2 ^ m)).filter fun r => ∀ s ∈ S, accWord r s = g s).card = 2 ^ (m - S.card) := by
  sorry

/-- One window: `2^(m − |u|)` residues match `u` at `i`, when `i + |u| ≤ m`. -/
theorem card_match_one (u : List Bool) {m i : ℕ} (h : i + u.length ≤ m) :
    ((Finset.range (2 ^ m)).filter
      fun r => WindowMatch (fun s => u.getD s false) u.length i r).card = 2 ^ (m - u.length) := by
  sorry

/-- Two disjoint windows: `2^(m − 2|u|)` residues match `u` at both `i` and `i'`, when
`i + |u| ≤ i'` and `i' + |u| ≤ m`. -/
theorem card_match_two (u : List Bool) {m i i' : ℕ} (h : i + u.length ≤ i')
    (h' : i' + u.length ≤ m) :
    ((Finset.range (2 ^ m)).filter fun r =>
      WindowMatch (fun s => u.getD s false) u.length i r ∧
        WindowMatch (fun s => u.getD s false) u.length i' r).card = 2 ^ (m - 2 * u.length) := by
  sorry

/-- **The second moment over a block.**  For `a + b + |u| ≤ m`,
`∑_{r < 2^m} wdev(r)² ≤ 2 |u| b 2^m`. -/
theorem sum_sq_wdev_le (u : List Bool) {m a b : ℕ} (h : a + b + u.length ≤ m) :
    ∑ r ∈ Finset.range (2 ^ m), (wdev u r a b) ^ 2 ≤ 2 * u.length * b * 2 ^ m := by
  sorry

/-- **Chebyshev on a block.** -/
theorem card_bad_block_le (u : List Bool) {m a b : ℕ} (h : a + b + u.length ≤ m) {ε : ℝ}
    (hε : 0 < ε) (hb : 0 < b) :
    (((Finset.range (2 ^ m)).filter fun r => ε * b < |wdev u r a b|).card : ℝ) ≤
      2 * u.length * 2 ^ m / (ε ^ 2 * b) := by
  sorry

/-- **Blocks give windows.**  If the `K` blocks `[k b, (k + 1) b)` are good within `δ / 4`, with
`K b ≥ 2 Λ` and `8 b ≤ δ H`, then every window at offset `≤ Λ` with length in `[H, Λ]` is good
within `δ`. -/
theorem winGood_of_blocks {u : List Bool} {δ : ℝ} (hδ : 0 < δ) {H Λ K b n : ℕ} (hb : 0 < b)
    (hK : 2 * Λ ≤ K * b) (hbH : 8 * (b : ℝ) ≤ δ * H)
    (hblk : ∀ k < K, |wdev u n (k * b) b| ≤ δ / 4 * b) : WinGood u δ H Λ n := by
  sorry

/-- A window event sees only `N mod 2^m`, when `2 Λ + |u| ≤ m`. -/
theorem winGood_mod_iff {u : List Bool} {δ : ℝ} {H Λ m : ℕ} (hm : 2 * Λ + u.length ≤ m)
    (n : ℕ) : WinGood u δ H Λ (n % 2 ^ m) ↔ WinGood u δ H Λ n := by
  sorry

open Classical in
/-- **Transfer by the integral test.**  For large `x`, an event that sees only `N mod 2^m`,
`m = 3 n₀(x)`, has `winLaw x`-probability at most twice its proportion among residues, plus
`K 2^(−m)`. -/
theorem prob_periodic_le :
    ∃ X₀ : ℝ, ∀ x : ℝ, X₀ ≤ x → ∀ S : Set ℕ, (∀ n, n % 2 ^ (3 * nZero x) ∈ S ↔ n ∈ S) →
      (winLaw x).expect (Set.indicator S 1) ≤
        2 * (((Finset.range (2 ^ (3 * nZero x))).filter (· ∈ S)).card : ℝ) / 2 ^ (3 * nZero x) +
          K_intTest * (2 : ℝ) ^ (-(3 * (nZero x : ℝ))) := by
  sorry

/-- **Terras at one scale.**  Under `winLaw x`, all windows of the first `2 lam x` letters are good,
with probability tending to `1`. -/
theorem winGood_whp (u : List Bool) {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    Tendsto (fun x => (winLaw x).expect
      (Set.indicator {N | ¬ WinGood u δ (hgt η x) (lam x) N} 1)) atTop (𝓝 0) := by
  sorry

/-- Both words at one scale. -/
theorem scaleGood_whp (u : List Bool) {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    Tendsto (fun x => (winLaw x).expect
      (Set.indicator {N | ¬ ScaleGood u δ η x N} 1)) atTop (𝓝 0) := by
  sorry

/-- **The location event.**  Under `ν_x`, the law of the passage location below `x` of a start
drawn from `winLaw x`, the location is good at scale `x` with probability tending to `1`. -/
theorem locGood_whp (u : List Bool) {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) (hη1 : η ≤ 1 / 1000) :
    Tendsto (fun x => ((winLaw x).map (passLoc ⌊x⌋₊)).expect
      (Set.indicator {M | ¬ LocGood u δ η x M} 1)) atTop (𝓝 0) := by
  sorry

/-! ## The chain of scales -/

/-- **The chain.**  The law of the passage location below `x_j` of a start drawn from `winLaw x` is
within `o(1)` of `ν_(x_j)`, by induction on `j`: Proposition 1.11 at `x_(j+1)`, data processing,
and `passLoc_passLoc`. -/
theorem dTV_chain (j : ℕ) :
    Tendsto (fun x => PMF.dTV ((winLaw x).map (passLoc ⌊scale x j⌋₊))
      ((winLaw (scale x j)).map (passLoc ⌊scale x j⌋₊))) atTop (𝓝 0) := by
  sorry

/-- Each stage event holds with probability tending to `1`. -/
theorem stage_whp (u : List Bool) {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) (hη1 : η ≤ 1 / 1000)
    (j : ℕ) :
    Tendsto (fun x => (winLaw x).expect (Set.indicator
      {n | ¬ LocGood u δ η (scale x j) (passLoc ⌊scale x j⌋₊ n)} 1)) atTop (𝓝 0) := by
  sorry

/-- **All scales at once.**  Under `winLaw x`, the start is good over its first `4.2 size n`
letters with probability tending to `1`. -/
theorem goodOdd_whp (u : List Bool) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun x => (winLaw x).expect (Set.indicator {n | ¬ GoodOdd u δ n} 1))
      atTop (𝓝 0) := by
  sorry

end CollatzMoonshot.Conjugacy
