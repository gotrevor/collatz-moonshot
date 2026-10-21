/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.Ladder
import CollatzMoonshot.FrontA.OrbitPacking
import CollatzMoonshot.Obstructions.Q1Coalescence

/-!
# Orbit coalescence: why the beyond-Terras letter is correlated across starts

**The correlation of the beyond-Terras letter across starts is orbit coalescence.**  Merged
orbits carry identical letters forever; the measured autocorrelation `R_j(d)` is the
coalescence density `coal_j(d)` up to a `−0.03` remainder from non-merged pairs (2026-10-21,
`experiments/conjugacy/coalesce.py`, `j = 20`, every `d ≤ 256`).  Classical seed:
`r ≡ 4 (mod 8)` merges with `r + 1` in three steps (cf. Garner 1985 on consecutive integers of
equal height).  Consequence for the walk `s ↦ Σ_{r<s} g_j(r)`: its block variance is the
integrated coalescence density, not Brownian.

The sign `g_j(r) = (−1)^{tstep^[j] r}` of the first beyond-Terras letter (`letterSign`) is
strongly correlated across nearby starts: over `r < 2^20`, `g_20(r) = g_20(r+1)` for 69% of `r`.
The mechanism is **orbit coalescence** (`Coalesces`): if `tstep^[k] r = tstep^[k] (r + d)` for
some `k ≤ j`, then `tstep^[j] r = tstep^[j] (r + d)` (`tstep_iterate_eq_of_coalesces`) and the
two signs agree.  Numerically (`j = 20`) the window autocorrelation
`R_j(d) = 2^(−j) · letterCorr j d` equals the coalescence density `coal_j(d) = 2^(−j) · coalCount j d`
up to a remainder from non-merged pairs that is `−0.03 .. −0.01` for every `d ≤ 256`:

| `d` | `coal_20(d)` | `R_20(d)` |
|---|---|---|
| 1 | 0.402 | 0.384 |
| 2 | 0.280 | 0.254 |
| 4 | 0.198 | 0.168 |
| 64 | 0.039 | 0.026 |

* **The exact decomposition** (`letterCorr_eq`): `letterCorr j d = coalCount j d + nonCoalCorr j d`,
  a theorem, because every coalesced pair contributes `+1`.
* **The classical seed** (`coalesces_four_mod_eight`): `8t+4 → 4t+2 → 2t+1 → 3t+2` and
  `8t+5 → 12t+8 → 6t+4 → 3t+2`, so `r ≡ 4 (mod 8)` coalesces with `r + 1` by step `3`; hence
  `coal_j(1) ≥ 1/8` for `j ≥ 3` (`coalCount_one_ge`, `coalescenceDensityPositive_one`).
* **Pairs about to merge are anticorrelated** (`letterSign_mul_eq_neg_one_of_merge_next`,
  `letterCorr_eq_refined`): two distinct starts with the same image have opposite parities
  (`mod_two_ne_of_tstep_eq`), so a pair that merges exactly one step past the window contributes
  `−1`.  The small negative remainder among non-merged pairs (`−0.03` at `j = 20`) has an exact
  negative component from the pairs that merge next.
* **The parity recursion at even distance** (`coalCount_succ_two_mul`): an even start halves
  the pair and an odd start triples it, so `coalCount (j+1) (2d) = coalCount j d +
  oddImageCoalCount j (3d)` exactly.  Numerically the odd-image starts coalesce at the uniform
  rate (`experiments/conjugacy/coalrec.py`, `j = 20`: `coal_20(2) = 0.2796`, `coal_19(1) = 0.3984`,
  odd-image `coal_19(3) = 0.1609` against uniform `0.1609`), so the even-distance profile is the
  parity mixture `coal_j(2d) ≈ (coal_{j−1}(d) + coal_{j−1}(3d))/2` to four decimals; odd
  distances, `d = 1` first, are the irreducible base case.
* **Equal-odd-count merging is a residue-class property**
  (`genericCoalesces_add_pow_two_mul_iff`): by the cylinder offset
  `tstep^[k] (x + 2^k d) = tstep^[k] x + 3^a d` a merge at a step with equal odd-step counts
  depends only on `s mod 2^j` (`genericCoalesces_iff_mod`), so its density is the same over every
  complete residue system mod `2^j`; in particular the odd-image starts `3r + 2` of the parity
  recursion see exactly the uniform count (`oddImage_genericCoalCount`).  Numerically
  (`experiments/conjugacy/mergeodd.py`, `j = 20`) all but `2-3·10^{−5}` of starts
  (`0.0001-0.0003` of merges) merge this way, which is why the odd-image starts of the parity
  recursion coalesce at the uniform rate to four decimals.
* **The generic density is monotone in the window, hence convergent**
  (`two_mul_genericCoalCount_le`, `genericCoalDensity_tendsto`): a merging residue class mod `2^j`
  lifts to two classes mod `2^(j+1)`, so `coal^gen_j(D)` is nondecreasing in `j`, bounded by `1`,
  and converges; the limit is the Haar measure of the 2-adic open set of starts that merge
  generically with `s + D`.  Numerically `coal_j(1)` climbs `0.344, 0.361, …, 0.409` over
  `j = 10, 12, …, 22` (`experiments/conjugacy/coalfinal.py`).
* **Eventual merging** (`EventuallyMerges`): the parity recursion lifts verbatim
  (`eventuallyMerges_two_mul_iff`, `eventuallyMerges_odd_iff`) and the window count is bounded by
  the eventual count (`coalCount_le_eventualMergeCount`); the fates of consecutive pairs at
  `j = 22` (`experiments/conjugacy/mergetime.py`): pre-cycle merge `0.49`, in-phase cycle arrival
  `0.25`, antiphase forever `0.26`, with the window limit strictly below the eventual density
  (frozen `WindowLimitLtEventual`, `EventualMergeDensityConverges`,
  `ConsecutiveAntiphasePositive`).
* **Frozen conjectures**: `NonCoalescedDecorrelated` (the remainder vanishes in the limit),
  `LetterCorrIsCoalescence` (equivalent to it, `letterCorrIsCoalescence_iff`),
  `CoalescenceDensityPositive` (a positive fraction of starts merge with `r + d` within the
  window), a theorem for `d = 1`, and the three eventual-merging conjectures
  `EventualMergeDensityConverges`, `WindowLimitLtEventual`, `ConsecutiveAntiphasePositive`.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord

/-! ## Coalescence -/

/-- `Coalesces r d j`: the shortcut orbits of `r` and `r + d` meet within `j` steps.  Once met,
they agree forever, so in particular the `j`-th letters agree (`tstep_iterate_eq_of_coalesces`). -/
def Coalesces (r d j : ℕ) : Prop := ∃ k ≤ j, tstep^[k] r = tstep^[k] (r + d)

theorem coalesces_iff_exists_mem_range (r d j : ℕ) :
    Coalesces r d j ↔ ∃ k ∈ Finset.range (j + 1), tstep^[k] r = tstep^[k] (r + d) := by
  simp [Coalesces]

/-- Coalescence within a window is a bounded search, hence decidable. -/
instance decidableCoalesces (r d j : ℕ) : Decidable (Coalesces r d j) :=
  decidable_of_iff _ (coalesces_iff_exists_mem_range r d j).symm

/-- A longer window sees every merge the shorter one saw. -/
theorem coalesces_mono {r d j j' : ℕ} (hjj' : j ≤ j') (h : Coalesces r d j) :
    Coalesces r d j' :=
  let ⟨k, hk, hm⟩ := h
  ⟨k, hk.trans hjj', hm⟩

/-- **Merged orbits stay merged.**  If the orbits of `r` and `r + d` meet by step `j`, the `j`-th
iterates agree. -/
theorem tstep_iterate_eq_of_coalesces {r d j : ℕ} (h : Coalesces r d j) :
    tstep^[j] r = tstep^[j] (r + d) := by
  obtain ⟨k, hk, hm⟩ := h
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [Function.iterate_add_apply, Function.iterate_add_apply, hm]

/-- `k = j` is allowed in `Coalesces`, so a non-coalesced pair has distinct `j`-th iterates. -/
theorem tstep_iterate_ne_of_not_coalesces {r d j : ℕ} (h : ¬ Coalesces r d j) :
    tstep^[j] r ≠ tstep^[j] (r + d) :=
  fun he => h ⟨j, le_rfl, he⟩

/-- Doubling both the start and the gap delays a merge by exactly one step: `tstep (2r) = r`. -/
theorem coalesces_two_mul {r d j : ℕ} (h : Coalesces r d j) :
    Coalesces (2 * r) (2 * d) (j + 1) := by
  obtain ⟨k, hk, hm⟩ := h
  refine ⟨k + 1, by omega, ?_⟩
  have h1 : tstep (2 * r) = r := by unfold tstep; split_ifs <;> omega
  have h2 : tstep (2 * r + 2 * d) = r + d := by unfold tstep; split_ifs <;> omega
  rw [Function.iterate_succ_apply, Function.iterate_succ_apply, h1, h2, hm]

/-! ## The letter sign and its autocorrelation -/

/-- The sign `(−1)^{tstep^[j] r}` of the `j`-th parity letter of `r`. -/
def letterSign (j r : ℕ) : ℤ := if tstep^[j] r % 2 = 0 then 1 else -1

theorem letterSign_mul_self (j r : ℕ) : letterSign j r * letterSign j r = 1 := by
  unfold letterSign; split_ifs <;> norm_num

theorem letterSign_eq_of_coalesces {r d j : ℕ} (h : Coalesces r d j) :
    letterSign j (r + d) = letterSign j r := by
  simp only [letterSign, tstep_iterate_eq_of_coalesces h]

/-- The window autocorrelation of the `j`-th letter sign at lag `d`:
`letterCorr j d = Σ_{r < 2^j} g_j(r) g_j(r + d)`, so `R_j(d) = letterCorr j d / 2^j`. -/
def letterCorr (j d : ℕ) : ℤ :=
  ∑ r ∈ Finset.range (2 ^ j), letterSign j r * letterSign j (r + d)

/-- The number of starts `r < 2^j` whose orbit meets that of `r + d` within `j` steps:
`coal_j(d) = coalCount j d / 2^j`. -/
def coalCount (j d : ℕ) : ℕ := ((Finset.range (2 ^ j)).filter (fun r => Coalesces r d j)).card

/-- The autocorrelation restricted to the non-coalesced pairs: the remainder in `letterCorr_eq`. -/
def nonCoalCorr (j d : ℕ) : ℤ :=
  ∑ r ∈ (Finset.range (2 ^ j)).filter (fun r => ¬ Coalesces r d j),
    letterSign j r * letterSign j (r + d)

/-- **The exact decomposition.**  Every coalesced pair contributes `+1` to the autocorrelation, so
`letterCorr j d = coalCount j d + nonCoalCorr j d`. -/
theorem letterCorr_eq (j d : ℕ) : letterCorr j d = coalCount j d + nonCoalCorr j d := by
  unfold letterCorr coalCount nonCoalCorr
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (2 ^ j)) (fun r => Coalesces r d j)]
  congr 1
  have h1 : ∀ r ∈ (Finset.range (2 ^ j)).filter (fun r => Coalesces r d j),
      letterSign j r * letterSign j (r + d) = 1 := by
    intro r hr
    rw [Finset.mem_filter] at hr
    rw [letterSign_eq_of_coalesces hr.2, letterSign_mul_self]
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]

/-! ## The classical seed: `r ≡ 4 (mod 8)` merges with `r + 1` -/

/-- **The classical seed.**  `8t+4 → 4t+2 → 2t+1 → 3t+2` and `8t+5 → 12t+8 → 6t+4 → 3t+2`: a
start `≡ 4 (mod 8)` coalesces with its successor by step `3` (Garner 1985 on consecutive
integers of equal height). -/
theorem coalesces_four_mod_eight (t : ℕ) : Coalesces (8 * t + 4) 1 3 := by
  refine ⟨3, le_rfl, ?_⟩
  have h1 : tstep (8 * t + 4) = 4 * t + 2 := by unfold tstep; split_ifs <;> omega
  have h2 : tstep (4 * t + 2) = 2 * t + 1 := by unfold tstep; split_ifs <;> omega
  have h3 : tstep (2 * t + 1) = 3 * t + 2 := by unfold tstep; split_ifs <;> omega
  have h4 : tstep (8 * t + 4 + 1) = 12 * t + 8 := by unfold tstep; split_ifs <;> omega
  have h5 : tstep (12 * t + 8) = 6 * t + 4 := by unfold tstep; split_ifs <;> omega
  have h6 : tstep (6 * t + 4) = 3 * t + 2 := by unfold tstep; split_ifs <;> omega
  show tstep (tstep (tstep (8 * t + 4))) = tstep (tstep (tstep (8 * t + 4 + 1)))
  rw [h1, h2, h3, h4, h5, h6]

/-- At least one start in eight coalesces with its successor inside any window of length `≥ 3`:
the residues `≡ 4 (mod 8)` below `2^j` number `2^j / 8` and all coalesce. -/
theorem coalCount_one_ge (j : ℕ) (hj : 3 ≤ j) : 2 ^ j / 8 ≤ coalCount j 1 := by
  unfold coalCount
  rw [← Finset.card_range (2 ^ j / 8)]
  refine Finset.card_le_card_of_injOn (fun t => 8 * t + 4) ?_ ?_
  · intro t ht
    simp only [Finset.coe_range, Set.mem_Iio, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_range] at ht ⊢
    exact ⟨by omega, coalesces_mono hj (coalesces_four_mod_eight t)⟩
  · intro a _ b _ hab
    simp only at hab
    omega

/-! ## Teeth: kernel-checked values -/

theorem letterCorr_three_one : letterCorr 3 1 = 2 := by decide
theorem coalCount_three_one : coalCount 3 1 = 1 := by decide
theorem nonCoalCorr_three_one : nonCoalCorr 3 1 = 1 := by decide
theorem letterCorr_four_one : letterCorr 4 1 = -2 := by decide
theorem coalCount_four_one : coalCount 4 1 = 3 := by decide
theorem nonCoalCorr_four_one : nonCoalCorr 4 1 = -5 := by decide
theorem letterCorr_five_one : letterCorr 5 1 = 6 := by decide
theorem coalCount_five_one : coalCount 5 1 = 8 := by decide
theorem nonCoalCorr_five_one : nonCoalCorr 5 1 = -2 := by decide
theorem coalCount_five_two : coalCount 5 2 = 3 := by decide

/-! ## Pairs about to merge are anticorrelated -/

/-- Two distinct starts with the same image under `tstep` have opposite parities: on each parity
class `tstep` is injective (`n ↦ n/2` on evens, `n ↦ (3n+1)/2` on odds). -/
theorem mod_two_ne_of_tstep_eq {y y' : ℕ} (h : tstep y = tstep y') (hne : y ≠ y') :
    y % 2 ≠ y' % 2 := by
  unfold tstep at h
  split_ifs at h <;> omega

/-- **Pairs about to merge are anticorrelated.**  A pair whose orbits are distinct at step `j` and
merge at step `j + 1` has opposite `j`-th letters, so it contributes `−1` to `letterCorr j d`. -/
theorem letterSign_mul_eq_neg_one_of_merge_next {j r d : ℕ}
    (hnot : tstep^[j] r ≠ tstep^[j] (r + d))
    (hnext : tstep^[j + 1] r = tstep^[j + 1] (r + d)) :
    letterSign j r * letterSign j (r + d) = -1 := by
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at hnext
  have hpar := mod_two_ne_of_tstep_eq hnext hnot
  unfold letterSign
  split_ifs <;> omega

/-- The number of starts `r < 2^j` not coalesced with `r + d` inside the window whose orbit merges
with that of `r + d` exactly at step `j + 1`. -/
def mergeNextCount (j d : ℕ) : ℕ :=
  ((Finset.range (2 ^ j)).filter
    (fun r => ¬ Coalesces r d j ∧ tstep^[j + 1] r = tstep^[j + 1] (r + d))).card

/-- **The refined decomposition.**  The non-coalesced remainder splits into the pairs that merge
next, each contributing exactly `−1`, and the pairs still apart at step `j + 1`:
`letterCorr j d = coalCount j d − mergeNextCount j d + (the rest)`.  So the small negative
remainder among non-merged pairs (`−0.03` at `j = 20`) has an exact negative component. -/
theorem letterCorr_eq_refined (j d : ℕ) :
    letterCorr j d = coalCount j d - mergeNextCount j d +
      ∑ r ∈ (Finset.range (2 ^ j)).filter
          (fun r => ¬ Coalesces r d j ∧ tstep^[j + 1] r ≠ tstep^[j + 1] (r + d)),
        letterSign j r * letterSign j (r + d) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not
    ((Finset.range (2 ^ j)).filter (fun r => ¬ Coalesces r d j))
    (fun r => tstep^[j + 1] r = tstep^[j + 1] (r + d))
    (fun r => letterSign j r * letterSign j (r + d))
  simp only [Finset.filter_filter] at hsplit
  have hneg : ∀ r ∈ (Finset.range (2 ^ j)).filter
      (fun r => ¬ Coalesces r d j ∧ tstep^[j + 1] r = tstep^[j + 1] (r + d)),
      letterSign j r * letterSign j (r + d) = -1 := by
    intro r hr
    rw [Finset.mem_filter] at hr
    exact letterSign_mul_eq_neg_one_of_merge_next
      (tstep_iterate_ne_of_not_coalesces hr.2.1) hr.2.2
  rw [Finset.sum_congr rfl hneg, Finset.sum_const, nsmul_eq_mul, mul_neg_one] at hsplit
  simp only [ne_eq]
  rw [letterCorr_eq, nonCoalCorr, ← hsplit, mergeNextCount]
  ring

theorem mergeNextCount_three_one : mergeNextCount 3 1 = 1 := by decide
theorem mergeNextCount_four_one : mergeNextCount 4 1 = 1 := by decide
theorem mergeNextCount_five_one : mergeNextCount 5 1 = 1 := by decide

/-! ## The parity recursion at even distance -/

/-- Doubling both the start and the gap delays a merge by exactly one step, and conversely: with
`d ≥ 1` the pair `(2r, 2r + 2d)` is not merged at step `0`, and one step sends it to `(r, r + d)`. -/
theorem coalesces_two_mul_iff {r d j : ℕ} (hd : 1 ≤ d) :
    Coalesces (2 * r) (2 * d) (j + 1) ↔ Coalesces r d j := by
  refine ⟨fun h => ?_, coalesces_two_mul⟩
  obtain ⟨k, hk, hm⟩ := h
  cases k with
  | zero =>
    simp only [Function.iterate_zero, id_eq] at hm
    omega
  | succ k =>
    refine ⟨k, by omega, ?_⟩
    have h1 : tstep (2 * r) = r := by unfold tstep; split_ifs <;> omega
    have h2 : tstep (2 * r + 2 * d) = r + d := by unfold tstep; split_ifs <;> omega
    rwa [Function.iterate_succ_apply, Function.iterate_succ_apply, h1, h2] at hm

/-- Doubling injects the starts coalesced at gap `d` within `j` steps into those coalesced at gap
`2d` within `j + 1` steps, so `coalCount j d ≤ coalCount (j + 1) (2d)`. -/
theorem coalCount_le_coalCount_succ_two_mul (j d : ℕ) :
    coalCount j d ≤ coalCount (j + 1) (2 * d) := by
  unfold coalCount
  refine Finset.card_le_card_of_injOn (fun r => 2 * r) ?_ ?_
  · intro r hr
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq, pow_succ] at hr ⊢
    exact ⟨by omega, coalesces_two_mul hr.2⟩
  · intro a _ b _ hab
    simp only at hab
    omega

/-- An odd start triples the pair: `tstep (2r + 1) = 3r + 2` and
`tstep (2r + 1 + 2d) = 3r + 2 + 3d`, so with `d ≥ 1` the pair `(2r + 1, 2r + 1 + 2d)` merges within
`j + 1` steps iff `(3r + 2, 3r + 2 + 3d)` merges within `j`. -/
theorem coalesces_odd_iff {r d j : ℕ} (hd : 1 ≤ d) :
    Coalesces (2 * r + 1) (2 * d) (j + 1) ↔ Coalesces (3 * r + 2) (3 * d) j := by
  have h1 : tstep (2 * r + 1) = 3 * r + 2 := by unfold tstep; split_ifs <;> omega
  have h2 : tstep (2 * r + 1 + 2 * d) = 3 * r + 2 + 3 * d := by
    unfold tstep; split_ifs <;> omega
  constructor
  · rintro ⟨k, hk, hm⟩
    cases k with
    | zero =>
      simp only [Function.iterate_zero, id_eq] at hm
      omega
    | succ k =>
      refine ⟨k, by omega, ?_⟩
      rwa [Function.iterate_succ_apply, Function.iterate_succ_apply, h1, h2] at hm
  · rintro ⟨k, hk, hm⟩
    refine ⟨k + 1, by omega, ?_⟩
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, h1, h2, hm]

/-- The number of odd starts `2r + 1 < 2^(j+1)` whose image `3r + 2` merges with `3r + 2 + d`
within `j` steps: the odd half of the parity recursion `coalCount_succ_two_mul`. -/
def oddImageCoalCount (j d : ℕ) : ℕ :=
  ((Finset.range (2 ^ j)).filter (fun r => Coalesces (3 * r + 2) d j)).card

/-- **The parity recursion at even distance.**  Splitting the starts `s < 2^(j+1)` by parity, an
even start `2r` halves the pair to `(r, r + d)` and an odd start `2r + 1` triples it to
`(3r + 2, 3r + 2 + 3d)`, so `coalCount (j+1) (2d) = coalCount j d + oddImageCoalCount j (3d)`
exactly. -/
theorem coalCount_succ_two_mul (j d : ℕ) (hd : 1 ≤ d) :
    coalCount (j + 1) (2 * d) = coalCount j d + oddImageCoalCount j (3 * d) := by
  unfold coalCount oddImageCoalCount
  have hset : (Finset.range (2 ^ (j + 1))).filter (fun s => Coalesces s (2 * d) (j + 1)) =
      ((Finset.range (2 ^ j)).filter (fun r => Coalesces r d j)).image (fun r => 2 * r) ∪
      ((Finset.range (2 ^ j)).filter (fun r => Coalesces (3 * r + 2) (3 * d) j)).image
        (fun r => 2 * r + 1) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_image, pow_succ]
    constructor
    · rintro ⟨hs, hc⟩
      obtain ⟨r, rfl | rfl⟩ := Nat.even_or_odd' s
      · exact Or.inl ⟨r, ⟨by omega, (coalesces_two_mul_iff hd).1 hc⟩, rfl⟩
      · exact Or.inr ⟨r, ⟨by omega, (coalesces_odd_iff hd).1 hc⟩, rfl⟩
    · rintro (⟨r, ⟨hr, hc⟩, rfl⟩ | ⟨r, ⟨hr, hc⟩, rfl⟩)
      · exact ⟨by omega, (coalesces_two_mul_iff hd).2 hc⟩
      · exact ⟨by omega, (coalesces_odd_iff hd).2 hc⟩
  have hdisj : Disjoint
      (((Finset.range (2 ^ j)).filter (fun r => Coalesces r d j)).image (fun r => 2 * r))
      (((Finset.range (2 ^ j)).filter (fun r => Coalesces (3 * r + 2) (3 * d) j)).image
        (fun r => 2 * r + 1)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_image] at hx hx'
    obtain ⟨a, _, rfl⟩ := hx
    obtain ⟨b, _, hb⟩ := hx'
    omega
  have hinj1 : Function.Injective (fun r : ℕ => 2 * r) := fun a b h => by
    simp only at h
    omega
  have hinj2 : Function.Injective (fun r : ℕ => 2 * r + 1) := fun a b h => by
    simp only at h
    omega
  rw [hset, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinj1,
    Finset.card_image_of_injective _ hinj2]

theorem oddImageCoalCount_four_three : oddImageCoalCount 4 3 = 0 := by decide
theorem oddImageCoalCount_five_three : oddImageCoalCount 5 3 = 0 := by decide

/-- The parity recursion at `j = 4`, `d = 1`, checked against the kernel values
`coalCount 5 2 = 3`, `coalCount 4 1 = 3`, `oddImageCoalCount 4 3 = 0`. -/
theorem coalCount_five_two_eq_recursion :
    coalCount 5 2 = coalCount 4 1 + oddImageCoalCount 4 3 := by decide

/-! ## Equal-odd-count merging is a residue-class property -/

/-- Adding a multiple of `2^k` leaves the length-`k` parity trace unchanged
(`FrontA.OrbitPacking.traceWord_add_mul`, restated with the power on the left). -/
theorem traceWord_add_pow_two_mul (k x d : ℕ) :
    traceWord (x + 2 ^ k * d) k = traceWord x k := by
  rw [mul_comm]
  exact CollatzMoonshot.FrontA.OrbitPacking.traceWord_add_mul k x d

/-- `GenericCoalesces s D j`: the orbits of `s` and `s + D` meet within `j` steps at a step where
their odd-step counts agree.  Unlike a bare merge, this is a property of `s mod 2^j`
(`genericCoalesces_add_pow_two_mul_iff`). -/
def GenericCoalesces (s D j : ℕ) : Prop :=
  ∃ k ≤ j, ones (traceWord s k) = ones (traceWord (s + D) k) ∧ tstep^[k] s = tstep^[k] (s + D)

/-- An equal-odd-count merge is a merge. -/
theorem coalesces_of_genericCoalesces {s D j : ℕ} (h : GenericCoalesces s D j) :
    Coalesces s D j :=
  let ⟨k, hk, _, hm⟩ := h
  ⟨k, hk, hm⟩

/-- **The cylinder offset at one step `k ≤ j`.**  Shifting the start by `2^j t = 2^k (2^(j−k) t)`
leaves both length-`k` traces unchanged (`traceWord_add_pow_two_mul`) and shifts both `k`-th
iterates by `3^a · 2^(j−k) t` (`tstep_iterate_pow_two_offset`), where `a` is the common odd-step
count; so the equal-odd-count merge condition at step `k` is invariant under the shift. -/
theorem genericCoalesces_step_add_pow_two_mul_iff {s D k j t : ℕ} (hk : k ≤ j) :
    (ones (traceWord (s + 2 ^ j * t) k) = ones (traceWord (s + 2 ^ j * t + D) k) ∧
        tstep^[k] (s + 2 ^ j * t) = tstep^[k] (s + 2 ^ j * t + D)) ↔
      (ones (traceWord s k) = ones (traceWord (s + D) k) ∧
        tstep^[k] s = tstep^[k] (s + D)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  have e1 : s + 2 ^ (k + m) * t = s + 2 ^ k * (2 ^ m * t) := by rw [pow_add]; ring
  have e2 : s + 2 ^ k * (2 ^ m * t) + D = s + D + 2 ^ k * (2 ^ m * t) := by ring
  rw [e1, e2, traceWord_add_pow_two_mul, traceWord_add_pow_two_mul,
    CollatzMoonshot.Obstructions.ArithmeticLifts.RestrictedRepair.tstep_iterate_pow_two_offset,
    CollatzMoonshot.Obstructions.ArithmeticLifts.RestrictedRepair.tstep_iterate_pow_two_offset]
  constructor
  · rintro ⟨ha, hm⟩
    refine ⟨ha, ?_⟩
    rw [ha] at hm
    exact Nat.add_right_cancel hm
  · rintro ⟨ha, hm⟩
    refine ⟨ha, ?_⟩
    rw [ha, hm]

/-- **Equal-odd-count merging is a residue-class property.**  Shifting the start by a multiple of
`2^j` neither creates nor destroys a merge with equal odd-step counts inside the window. -/
theorem genericCoalesces_add_pow_two_mul_iff (s D j t : ℕ) :
    GenericCoalesces (s + 2 ^ j * t) D j ↔ GenericCoalesces s D j := by
  unfold GenericCoalesces
  exact exists_congr fun k => and_congr_right fun hk => genericCoalesces_step_add_pow_two_mul_iff hk

/-- The forward half of `genericCoalesces_add_pow_two_mul_iff`. -/
theorem genericCoalesces_add_pow_two_mul {s D j t : ℕ} (h : GenericCoalesces s D j) :
    GenericCoalesces (s + 2 ^ j * t) D j :=
  (genericCoalesces_add_pow_two_mul_iff s D j t).2 h

/-- The converse half of `genericCoalesces_add_pow_two_mul_iff`. -/
theorem genericCoalesces_of_add_pow_two_mul {s D j t : ℕ}
    (h : GenericCoalesces (s + 2 ^ j * t) D j) : GenericCoalesces s D j :=
  (genericCoalesces_add_pow_two_mul_iff s D j t).1 h

/-- An equal-odd-count merge depends only on the residue `s mod 2^j`. -/
theorem genericCoalesces_iff_mod (s D j : ℕ) :
    GenericCoalesces s D j ↔ GenericCoalesces (s % 2 ^ j) D j := by
  have h := genericCoalesces_add_pow_two_mul_iff (s % 2 ^ j) D j (s / 2 ^ j)
  rwa [Nat.mod_add_div] at h

theorem genericCoalesces_iff_exists_mem_range (s D j : ℕ) :
    GenericCoalesces s D j ↔ ∃ k ∈ Finset.range (j + 1),
      ones (traceWord s k) = ones (traceWord (s + D) k) ∧ tstep^[k] s = tstep^[k] (s + D) := by
  simp [GenericCoalesces]

/-- Equal-odd-count coalescence within a window is a bounded search, hence decidable. -/
instance decidableGenericCoalesces (s D j : ℕ) : Decidable (GenericCoalesces s D j) :=
  decidable_of_iff _ (genericCoalesces_iff_exists_mem_range s D j).symm

/-- The number of starts `s < 2^j` whose orbit meets that of `s + D` within `j` steps at a step
with equal odd-step counts.  By `genericCoalesces_iff_mod` this count is the same over every
complete residue system mod `2^j`. -/
def genericCoalCount (j D : ℕ) : ℕ :=
  ((Finset.range (2 ^ j)).filter (fun s => GenericCoalesces s D j)).card

/-- The map `r ↦ (3r + 2) mod 2^j` is injective on `r < 2^j`, since `3` is a unit mod `2^j`. -/
theorem three_mul_add_two_mod_pow_two_injOn {j a b : ℕ} (ha : a < 2 ^ j) (hb : b < 2 ^ j)
    (hab : (3 * a + 2) % 2 ^ j = (3 * b + 2) % 2 ^ j) : a = b := by
  have hcop : Nat.Coprime (2 ^ j) 3 := Nat.Coprime.pow_left j (by norm_num)
  have h1 : 3 * a + 2 ≡ 3 * b + 2 [MOD 2 ^ j] := hab
  have h2 : 3 * a ≡ 3 * b [MOD 2 ^ j] := Nat.ModEq.add_right_cancel' 2 h1
  have h3 : a ≡ b [MOD 2 ^ j] := Nat.ModEq.cancel_left_of_coprime hcop h2
  exact Nat.ModEq.eq_of_lt_of_lt h3 ha hb

/-- **The odd-image starts see the uniform count.**  The starts `3r + 2`, `r < 2^j`, of the odd
half of the parity recursion run through a complete residue system mod `2^j`, so the number of
them that merge with equal odd-step counts equals `genericCoalCount j D`. -/
theorem oddImage_genericCoalCount (j D : ℕ) :
    ((Finset.range (2 ^ j)).filter (fun r => GenericCoalesces (3 * r + 2) D j)).card =
      genericCoalCount j D := by
  unfold genericCoalCount
  have hmaps : ∀ a ∈ Finset.range (2 ^ j), (3 * a + 2) % 2 ^ j ∈ Finset.range (2 ^ j) := by
    intro a _
    exact Finset.mem_range.2 (Nat.mod_lt _ (by positivity))
  have hinj : ∀ a₁ a₂, a₁ ∈ Finset.range (2 ^ j) → a₂ ∈ Finset.range (2 ^ j) →
      (3 * a₁ + 2) % 2 ^ j = (3 * a₂ + 2) % 2 ^ j → a₁ = a₂ := by
    intro a₁ a₂ h₁ h₂ h
    exact three_mul_add_two_mod_pow_two_injOn (Finset.mem_range.1 h₁) (Finset.mem_range.1 h₂) h
  have hsurj := Finset.surj_on_of_inj_on_of_card_le (s := Finset.range (2 ^ j))
    (t := Finset.range (2 ^ j)) (fun a _ => (3 * a + 2) % 2 ^ j) hmaps hinj le_rfl
  refine Finset.card_bij (fun r _ => (3 * r + 2) % 2 ^ j) ?_ ?_ ?_
  · intro r hr
    rw [Finset.mem_filter] at hr ⊢
    exact ⟨hmaps r hr.1, (genericCoalesces_iff_mod _ _ _).1 hr.2⟩
  · intro a₁ h₁ a₂ h₂ h
    rw [Finset.mem_filter] at h₁ h₂
    exact hinj a₁ a₂ h₁.1 h₂.1 h
  · intro b hb
    rw [Finset.mem_filter] at hb
    obtain ⟨a, ha, hab⟩ := hsurj b hb.1
    refine ⟨a, ?_, hab.symm⟩
    rw [Finset.mem_filter]
    refine ⟨ha, ?_⟩
    rw [genericCoalesces_iff_mod, ← hab]
    exact hb.2

/-- At `j ≤ 5`, `D ∈ {1, 2}` every in-window merge has equal odd-step counts: the kernel values
agree with `coalCount_three_one`, `coalCount_four_one`, `coalCount_five_one`, `coalCount_five_two`. -/
theorem genericCoalCount_three_one : genericCoalCount 3 1 = 1 := by decide
theorem genericCoalCount_four_one : genericCoalCount 4 1 = 3 := by decide
theorem genericCoalCount_five_one : genericCoalCount 5 1 = 8 := by decide
theorem genericCoalCount_five_two : genericCoalCount 5 2 = 3 := by decide

/-! ### The generic density is monotone in the window, hence convergent -/

/-- A longer window sees every equal-odd-count merge the shorter one saw. -/
theorem genericCoalesces_mono {s D j j' : ℕ} (hjj' : j ≤ j') (h : GenericCoalesces s D j) :
    GenericCoalesces s D j' :=
  let ⟨k, hk, ha, hm⟩ := h
  ⟨k, hk.trans hjj', ha, hm⟩

/-- **A merging residue class lifts to two.**  Each `s < 2^j` merging generically within `j` steps
yields the two starts `s` and `s + 2^j` below `2^(j+1)`, both merging generically within `j + 1`
steps (`genericCoalesces_add_pow_two_mul` with `t = 1`, then `genericCoalesces_mono`), so
`2 · genericCoalCount j D ≤ genericCoalCount (j + 1) D`. -/
theorem two_mul_genericCoalCount_le (j D : ℕ) :
    2 * genericCoalCount j D ≤ genericCoalCount (j + 1) D := by
  unfold genericCoalCount
  have hsub : (Finset.range (2 ^ j)).filter (fun s => GenericCoalesces s D j) ∪
      ((Finset.range (2 ^ j)).filter (fun s => GenericCoalesces s D j)).image
        (fun s => s + 2 ^ j) ⊆
      (Finset.range (2 ^ (j + 1))).filter (fun s => GenericCoalesces s D (j + 1)) := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_range,
      pow_succ] at hx ⊢
    rcases hx with ⟨hx, hc⟩ | ⟨s, ⟨hs, hc⟩, rfl⟩
    · exact ⟨by omega, genericCoalesces_mono (Nat.le_succ j) hc⟩
    · refine ⟨by omega, genericCoalesces_mono (Nat.le_succ j) ?_⟩
      have h1 := genericCoalesces_add_pow_two_mul (t := 1) hc
      rwa [mul_one] at h1
  have hdisj : Disjoint ((Finset.range (2 ^ j)).filter (fun s => GenericCoalesces s D j))
      (((Finset.range (2 ^ j)).filter (fun s => GenericCoalesces s D j)).image
        (fun s => s + 2 ^ j)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hx hx'
    obtain ⟨s, _, rfl⟩ := hx'
    omega
  have hinj : Function.Injective (fun s : ℕ => s + 2 ^ j) := add_left_injective _
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinj] at hcard
  omega

/-- The generic coalescence density `coal^gen_j(D) = genericCoalCount j D / 2^j`: the fraction of
starts `s < 2^j` that merge with `s + D` within the window at a step with equal odd-step counts. -/
noncomputable def genericCoalDensity (j D : ℕ) : ℝ := (genericCoalCount j D : ℝ) / 2 ^ j

/-- **The generic density is nondecreasing in the window**: `a / 2^j ≤ b / 2^(j+1)` whenever
`2a ≤ b` (`two_mul_genericCoalCount_le`). -/
theorem genericCoalDensity_mono (D : ℕ) : Monotone (fun j => genericCoalDensity j D) := by
  refine monotone_nat_of_le_succ fun j => ?_
  simp only [genericCoalDensity]
  have h : (2 * genericCoalCount j D : ℝ) ≤ genericCoalCount (j + 1) D := by
    exact_mod_cast two_mul_genericCoalCount_le j D
  rw [div_le_div_iff₀ (by positivity) (by positivity), pow_succ]
  nlinarith [h, pow_pos (two_pos : (0 : ℝ) < 2) j]

/-- The generic density is at most `1`: the window holds only `2^j` starts. -/
theorem genericCoalDensity_le_one (j D : ℕ) : genericCoalDensity j D ≤ 1 := by
  unfold genericCoalDensity
  rw [div_le_one (by positivity)]
  have h : genericCoalCount j D ≤ 2 ^ j := by
    unfold genericCoalCount
    exact (Finset.card_filter_le _ _).trans (Finset.card_range _).le
  exact_mod_cast h

/-- **The generic density converges.**  Nondecreasing in `j` and bounded by `1`, `coal^gen_j(D)`
tends to its supremum `L ≤ 1`, the Haar measure of the 2-adic open set of starts that merge
generically with `s + D`. -/
theorem genericCoalDensity_tendsto (D : ℕ) :
    ∃ L : ℝ, L ≤ 1 ∧ Tendsto (fun j => genericCoalDensity j D) atTop (𝓝 L) := by
  have hbdd : BddAbove (Set.range fun j => genericCoalDensity j D) :=
    ⟨1, Set.forall_mem_range.2 fun j => genericCoalDensity_le_one j D⟩
  exact ⟨⨆ j, genericCoalDensity j D, ciSup_le fun j => genericCoalDensity_le_one j D,
    tendsto_atTop_ciSup (genericCoalDensity_mono D) hbdd⟩

/-- The lift at `j = 4`, `D = 1`, against the kernel values: `2 · 3 ≤ 8`. -/
theorem two_mul_genericCoalCount_four_one_le :
    2 * genericCoalCount 4 1 ≤ genericCoalCount 5 1 := by
  rw [genericCoalCount_four_one, genericCoalCount_five_one]
  norm_num

/-! ## Eventual merging, and the fates of consecutive pairs -/

/-- `EventuallyMerges s D`: the shortcut orbits of `s` and `s + D` meet at some step - a merge
before the cycle, or arrival at the cycle `{1, 2}` in phase.  Its negation is "antiphase forever":
both orbits reach the cycle, but never at the same point at the same time. -/
def EventuallyMerges (s D : ℕ) : Prop := ∃ k, tstep^[k] s = tstep^[k] (s + D)

/-- A merge inside a window is an eventual merge. -/
theorem eventuallyMerges_of_coalesces {s D j : ℕ} (h : Coalesces s D j) :
    EventuallyMerges s D :=
  let ⟨k, _, hm⟩ := h
  ⟨k, hm⟩

/-- Eventual merging is coalescence within some window. -/
theorem eventuallyMerges_iff_exists_coalesces (s D : ℕ) :
    EventuallyMerges s D ↔ ∃ j, Coalesces s D j :=
  ⟨fun ⟨k, hk⟩ => ⟨k, k, le_rfl, hk⟩, fun ⟨_, h⟩ => eventuallyMerges_of_coalesces h⟩

/-- The classical seed: `r ≡ 4 (mod 8)` eventually merges with `r + 1`. -/
theorem eventuallyMerges_four_mod_eight (t : ℕ) : EventuallyMerges (8 * t + 4) 1 :=
  eventuallyMerges_of_coalesces (coalesces_four_mod_eight t)

/-- **The parity recursion lifts to eventual merging, even case**: with `d ≥ 1`, the pair
`(2r, 2r + 2d)` eventually merges iff `(r, r + d)` does (`coalesces_two_mul_iff`, over all
windows). -/
theorem eventuallyMerges_two_mul_iff {r d : ℕ} (hd : 1 ≤ d) :
    EventuallyMerges (2 * r) (2 * d) ↔ EventuallyMerges r d := by
  simp only [eventuallyMerges_iff_exists_coalesces]
  constructor
  · rintro ⟨j, h⟩
    exact ⟨j, (coalesces_two_mul_iff hd).1 (coalesces_mono (Nat.le_succ j) h)⟩
  · rintro ⟨j, h⟩
    exact ⟨j + 1, (coalesces_two_mul_iff hd).2 h⟩

/-- **The parity recursion lifts to eventual merging, odd case**: with `d ≥ 1`, the pair
`(2r + 1, 2r + 1 + 2d)` eventually merges iff `(3r + 2, 3r + 2 + 3d)` does (`coalesces_odd_iff`,
over all windows). -/
theorem eventuallyMerges_odd_iff {r d : ℕ} (hd : 1 ≤ d) :
    EventuallyMerges (2 * r + 1) (2 * d) ↔ EventuallyMerges (3 * r + 2) (3 * d) := by
  simp only [eventuallyMerges_iff_exists_coalesces]
  constructor
  · rintro ⟨j, h⟩
    exact ⟨j, (coalesces_odd_iff hd).1 (coalesces_mono (Nat.le_succ j) h)⟩
  · rintro ⟨j, h⟩
    exact ⟨j + 1, (coalesces_odd_iff hd).2 h⟩

open Classical in
/-- The number of starts `s < N` whose orbit eventually meets that of `s + D`.  Eventual merging
is an unbounded search, so the filter uses classical decidability. -/
noncomputable def eventualMergeCount (N D : ℕ) : ℕ :=
  ((Finset.range N).filter (fun s => EventuallyMerges s D)).card

/-- **The window count is bounded by the eventual count**: every start that merges inside the
window `j` eventually merges. -/
theorem coalCount_le_eventualMergeCount (j D : ℕ) :
    coalCount j D ≤ eventualMergeCount (2 ^ j) D := by
  classical
  unfold coalCount eventualMergeCount
  refine Finset.card_le_card ?_
  intro s hs
  simp only [Finset.mem_filter] at hs ⊢
  exact ⟨hs.1, eventuallyMerges_of_coalesces hs.2⟩

/-- The eventual merge density `eventualMergeCount N D / N`: the fraction of starts `s < N` whose
orbit eventually meets that of `s + D`. -/
noncomputable def eventualMergeDensity (N D : ℕ) : ℝ := (eventualMergeCount N D : ℝ) / N

/-! ## Frozen conjectures -/

/-- **Conjecture (non-merged pairs decorrelate).**  The autocorrelation among pairs that have not
coalesced inside the window vanishes in the limit: `nonCoalCorr j d / 2^j → 0`.  Numerics
(2026-10-21, `experiments/conjugacy/coalesce.py`, `j = 20`): the remainder is `−0.03 .. −0.01`
for every `d ≤ 256` (`d = 1`: `coal = 0.402`, `R = 0.384`; `d = 2`: `0.280 / 0.254`; `d = 4`:
`0.198 / 0.168`; `d = 64`: `0.039 / 0.026`).  Confidence 65%: the remainder is small but
consistently negative, which may be a finite-`j` effect or a genuine small anticorrelation;
`letterCorr_eq_refined` exhibits one exact negative component, the pairs that merge at step
`j + 1`. -/
def NonCoalescedDecorrelated : Prop :=
  ∀ d : ℕ, 1 ≤ d → Tendsto (fun j => (nonCoalCorr j d : ℝ) / 2 ^ j) atTop (𝓝 0)

/-- **Conjecture (the letter correlation is coalescence).**  `R_j(d) − coal_j(d) → 0`: the window
autocorrelation of the beyond-Terras letter is asymptotically the coalescence density.
Equivalent to `NonCoalescedDecorrelated` by the exact decomposition
(`letterCorrIsCoalescence_iff`).  Same numerics and confidence. -/
def LetterCorrIsCoalescence : Prop :=
  ∀ d : ℕ, 1 ≤ d →
    Tendsto (fun j => ((letterCorr j d : ℝ) - coalCount j d) / 2 ^ j) atTop (𝓝 0)

/-- The two conjectures are the same statement, by `letterCorr_eq`. -/
theorem letterCorrIsCoalescence_iff : LetterCorrIsCoalescence ↔ NonCoalescedDecorrelated := by
  have e : ∀ j d : ℕ,
      ((letterCorr j d : ℝ) - coalCount j d) / 2 ^ j = (nonCoalCorr j d : ℝ) / 2 ^ j := by
    intro j d
    rw [letterCorr_eq]
    push_cast
    ring
  simp only [LetterCorrIsCoalescence, NonCoalescedDecorrelated, e]

/-- **Conjecture (positive coalescence density).**  For every lag `d ≥ 1` a positive fraction of
the starts `r < 2^j` merge with `r + d` inside the window, eventually in `j`.  For `d = 1` this is
a theorem with `ρ = 1/8` by the classical seed (`coalescenceDensityPositive_one`); doubling
(`coalesces_two_mul`) carries the seed to `d = 2^m` at density `2^(−m) / 8`.  Numerics
(`j = 20`): `coal_20(1) = 0.402`, `coal_20(2) = 0.280`, `coal_20(4) = 0.198`,
`coal_20(64) = 0.039`.  Confidence 90% for general `d`. -/
def CoalescenceDensityPositive : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∃ ρ : ℝ, 0 < ρ ∧ ∀ᶠ j in atTop, ρ * 2 ^ j ≤ (coalCount j d : ℝ)

/-- The `d = 1` case of `CoalescenceDensityPositive`, with `ρ = 1/8`, from the classical seed. -/
theorem coalescenceDensityPositive_one :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ᶠ j in atTop, ρ * 2 ^ j ≤ (coalCount j 1 : ℝ) := by
  refine ⟨1 / 8, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop 3] with j hj
  have h := coalCount_one_ge j hj
  have hdvd : 8 ∣ 2 ^ j := by
    have h8 : (8 : ℕ) = 2 ^ 3 := by norm_num
    rw [h8]
    exact pow_dvd_pow 2 hj
  have hcast : ((2 ^ j / 8 : ℕ) : ℝ) = (2 : ℝ) ^ j / 8 := by
    rw [Nat.cast_div hdvd (by norm_num)]
    push_cast
    ring
  calc (1 / 8 : ℝ) * 2 ^ j = ((2 ^ j / 8 : ℕ) : ℝ) := by rw [hcast]; ring
    _ ≤ (coalCount j 1 : ℝ) := by exact_mod_cast h

/-- **Conjecture (the eventual merge density converges).**  For every `D ≥ 1` the fraction of
starts `s < N` whose orbit eventually meets that of `s + D` has a limit.  Numerics (2026-10-21,
`experiments/conjugacy/mergetime.py`, `D = 1`, `N = 2^j`): the density of eventual merging
(pre-cycle merge plus in-phase cycle arrival) is `0.702, 0.713, 0.723, 0.729, 0.735, 0.742` at
`j = 12, 14, …, 22`, rising with shrinking increments.  Confidence 80%. -/
def EventualMergeDensityConverges : Prop :=
  ∀ D : ℕ, 1 ≤ D → ∃ E : ℝ, Tendsto (fun N => eventualMergeDensity N D) atTop (𝓝 E)

/-- **Conjecture (the window limit is strictly below the eventual density).**  The limit `L` of
`genericCoalDensity_tendsto` at `D = 1` lies strictly below the eventual merge density `E`:
in-phase cycle arrival happens at `k ≈ 5.4 j`, outside every window, and the pre-cycle merges
beyond the window carry a mass that grows with `j` (`0.035 → 0.081` over `j = 12..22`).  Numerics
(2026-10-21, `experiments/conjugacy/mergetime.py`): window `0.409` against eventual `0.742` at
`j = 22`.  Confidence 90%. -/
def WindowLimitLtEventual : Prop :=
  ∀ L E : ℝ, Tendsto (fun j => genericCoalDensity j 1) atTop (𝓝 L) →
    Tendsto (fun N => eventualMergeDensity N 1) atTop (𝓝 E) → L < E

/-- **Conjecture (a positive fraction of consecutive pairs stay antiphase forever).**  For a
positive fraction of starts both orbits of `s` and `s + 1` reach the cycle `{1, 2}`, never in
phase.  Numerics (2026-10-21, `experiments/conjugacy/mergetime.py`, `N = 2^j`): the antiphase
fraction falls slowly, `0.298, 0.287, 0.278, 0.271, 0.265, 0.258` at `j = 12, 14, …, 22`, with
shrinking decrements; whether it tends to `0` (almost all consecutive integers share their orbit)
or to a positive limit is open on this evidence.  Confidence 55% for a positive limit. -/
def ConsecutiveAntiphasePositive : Prop :=
  ∃ ρ : ℝ, 0 < ρ ∧ ∀ᶠ N in atTop, eventualMergeDensity N 1 ≤ 1 - ρ


end CollatzMoonshot.Conjugacy
