/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalSurvivorCeiling

/-!
# The quantized ladder and the near-cycle reduction

The 2026-10-14 "fsfloor" agent (research §35).  A *rung* is a forward survivor `n` that is not its
orbit's minimum; its *depth* `g` is its first backward drop, `p = Vᵍ n` is the next lower forward
survivor (§31's P′), and `ρ = n/p ∈ (1, 3/2]`.

**`rung_log_ratio` (Theorem SQ, part 1).**  Along `p → n` each step is `x ↦ (3x + e)/2^d` with
`e ∈ {0, ±1}`, and `e ≠ 0` only at odd points, which are intermediate points `> n` (a ladder
excursion never dips below its endpoint).  So `log ρ = g log 3 − a log 2` up to a carry
`≤ g/(3n − 1)`, not the `O(log g)` of a general return.

**`rung_depth_spectrum` (Theorem SQ, part 2).**  Hence, once the carry is small, `{gθ} ≤ θ − 1`
(`θ = log₂ 3`): forward-survivor depths lie in the Sturmian set `{1, 2, 4, 6, 7, 9, 11, 12, …}`.
Backward-survivor depths lie in the complementary set `{1, 3, 5, 8, 10, 13, …}`.  Checked on all
of `[1, 2²³)`: 0 off-spectrum.  The rewired `τ` and `τ_odd` break it on 35–43% of their rungs.

**`bwdSurvivor_odd_separation`.**  The mirror of Sep3: two backward survivors `n < n'` on one orbit
with `n'` odd satisfy `4n ≤ 3n' + 1`.

**`infinitelyManyOrbits_of_fwdSurvivor_pos_of_nearCycle_null` (Theorem NC′).**  A `D`-near-cycle
start is a `p` whose forward orbit first re-enters `[0, p + D]` inside `(p, p + D]`.  If
near-cycle starts have density `0` for every `D`, then forward survivors of positive upper
density already imply Klamkin (a): the threshold of §31's C2′ drops from `c` to `0`.  Proof: under
`r` orbits, rungs of one orbit in a block `(Y, 2Y]` telescope to `∏ ρ ≤ 3`, so at most `3.3Y/D`
have gap `> D`; every other rung's predecessor is a `D`-near-cycle start, injectively.
-/

namespace CollatzMoonshot.Amusical

/-- **Target (Sep3 mirror).**  Odd backward survivors separate orbits. -/
theorem bwdSurvivor_odd_separation {n n' : ℤ} (hn : BwdSurvivor n) (hn' : BwdSurvivor n')
    (h0 : 0 ≤ n) (hlt : n < n') (hodd : Odd n') (horb : n ∈ amusicalOrbit n') :
    4 * n ≤ 3 * n' + 1 := by
  sorry

/-- **Target (Theorem SQ, part 1).**  The log-ratio of a rung is `g log 3 − a log 2` up to the
carry `g/(3n − 1)`. -/
theorem rung_log_ratio {n : ℤ} {g : ℕ} (hg : 1 ≤ g) (hn : FwdSurvivor n) (hpos : 2 ≤ n)
    (hdrop : amusicalInv^[g] n < n)
    (hmin : ∀ t, 1 ≤ t → t < g → n ≤ amusicalInv^[t] n) :
    ∃ a : ℕ, |Real.log ((n : ℝ) / (amusicalInv^[g] n : ℝ)) - (g * Real.log 3 - a * Real.log 2)|
      ≤ g / (3 * (n : ℝ) - 1) := by
  sorry

/-- **Target (Theorem SQ, part 2).**  Once the carry is below both margins, the depth of a rung is
a forward-survivor depth: `{gθ} ≤ θ − 1`. -/
theorem rung_depth_spectrum {n : ℤ} {g : ℕ} (hg : 1 ≤ g) (hn : FwdSurvivor n) (hpos : 2 ≤ n)
    (hdrop : amusicalInv^[g] n < n)
    (hmin : ∀ t, 1 ≤ t → t < g → n ≤ amusicalInv^[t] n)
    (hbig : (g : ℝ) / ((3 * n - 1) * Real.log 2) <
      min (1 - Int.fract (g * Real.logb 2 3))
        |Int.fract (g * Real.logb 2 3) - (Real.logb 2 3 - 1)|) :
    Int.fract (g * Real.logb 2 3) ≤ Real.logb 2 3 - 1 := by
  sorry

/-- A `D`-near-cycle start: the forward orbit of `p` first re-enters `[0, p + D]` inside
`(p, p + D]`. -/
def NearCycleStart (D p : ℕ) : Prop :=
  ∃ g ≥ 1, (p : ℤ) < amusical^[g] p ∧ amusical^[g] p ≤ p + D ∧
    ∀ k, 1 ≤ k → k < g → (p : ℤ) + D < amusical^[k] p

open Classical in
/-- **Target (Theorem NC′).**  If near-cycle starts have density `0` for every `D`, forward
survivors of positive upper density imply Klamkin (a). -/
theorem infinitelyManyOrbits_of_fwdSurvivor_pos_of_nearCycle_null
    (hNC : ∀ D : ℕ, Filter.Tendsto (fun X : ℕ =>
        (((Finset.range X).filter (NearCycleStart D)).card : ℝ) / X) Filter.atTop (nhds 0))
    {δ : ℝ} (hδ : 0 < δ)
    (hFS : ∃ᶠ X : ℕ in Filter.atTop,
        δ * X ≤ ((Finset.range X).filter fun n : ℕ => FwdSurvivor n).card) :
    AmusicalInfinitelyManyOrbits := by
  sorry

end CollatzMoonshot.Amusical
