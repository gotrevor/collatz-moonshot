/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MSP2.Defs

/-!
# MSP²: the results the article proves

One declaration per result the article establishes, stated over `ℕ`/`ℤ` as literally as
the text allows.  A `sorry` here means *not yet formalized*, never *doubted*: each of these
is arithmetic the article proves, and the numeric instances are already checked in
`MSP2.Checks`.  Parts of the article that need the inverse trees (§4-§7) or the Generator
Table itself (§11-§15) are not stated yet; `MSP2/README.md` lists them.
-/

namespace MSP2

open CollatzMoonshot

/-! ## §2: the odd run -/

/-- **§2.** If `M + 1 = 2^r·u` with `u` odd and `r ≥ 1`, then `r` MSP² odd steps take `M`
to `3^r·u − 1`, which is even; every intermediate value is odd. -/
theorem msp2_odd_run {M r u : ℕ} (hr : 1 ≤ r) (hu : u % 2 = 1) (hM : M + 1 = 2 ^ r * u) :
    msp2Step^[r] M = 3 ^ r * u - 1 ∧ (3 ^ r * u - 1) % 2 = 0 ∧
      ∀ i < r, msp2Step^[i] M % 2 = 1 := by
  sorry

/-- **§2.5 / §4.4.** The next odd value after a run is not a multiple of `3`, so it has the
form `6q ± 1`. -/
theorem not_three_dvd_after_run {r u s : ℕ} (hr : 1 ≤ r) (hu : 1 ≤ u)
    (hs : 2 ^ s ∣ 3 ^ r * u - 1) : ¬ 3 ∣ (3 ^ r * u - 1) / 2 ^ s := by
  sorry

/-! ## §3: the run-length families partition the odd numbers -/

/-- **§3.** Every odd `n` lies in exactly one family `2^(r+1)·k + 2^r − 1` with `r ≥ 1`. -/
theorem odd_family_unique {n : ℕ} (hn : n % 2 = 1) :
    ∃! p : ℕ × ℕ, 1 ≤ p.1 ∧ n = 2 ^ (p.1 + 1) * p.2 + 2 ^ p.1 - 1 := by
  sorry

/-! ## §9.8-9.9: uniform reproduction of the families, and the blocking points -/

/-- **§9.8.** Writing `u = 4v + s`, the surviving family `(3/4)·A_j·u + 1` is again of the
rank-`j+1` form with `A_{j+1} = 3·A_j`. -/
theorem fam_reproduce (j s v : ℕ) :
    3 * famA j / 4 * (4 * v + s) + 1 = fam (j + 1) s v := by
  sorry

/-- **§9.8** (the Collatz step behind "surviving family"): three steps take `A_j·u + 1`
to `(3/4)·A_j·u + 1`. -/
theorem step_three_fam_zero (j u : ℕ) : step^[3] (fam j 0 u) = 3 * famA j / 4 * u + 1 := by
  sorry

/-- Consequently every member `A_j·u + 1` with `u ≥ 1` is covered. -/
theorem covered_fam_zero (j u : ℕ) (hu : 1 ≤ u) : Covered (fam j 0 u) := by
  sorry

/-- **§9.9.** Closed form of the blocking points: `B_j = 24·16^j + 1`. -/
theorem blockB_eq (j : ℕ) : blockB j = 24 * 16 ^ j + 1 := by
  sorry

/-- **§9.9.** The blocking points grow strictly: `B_{j+1} − B_j = 360·16^j`. -/
theorem blockB_succ_sub (j : ℕ) : blockB (j + 1) - blockB j = 360 * 16 ^ j := by
  sorry

/-! ## §16.2: from coverage to reaching 1 -/

/-- **§16.2** ("De la couverture à l'arrivée à 1"): if every `2 ≤ N ≤ K` is covered, every
`1 ≤ N ≤ K` reaches `1` (strong induction). -/
theorem reachesOne_of_covered_upto {K : ℕ} (h : ∀ N, 2 ≤ N → N ≤ K → Covered N) :
    ∀ N, 1 ≤ N → N ≤ K → ReachesOne N := by
  sorry

/-- The article's `T` is the grouped step `msp2Step`; covered under it and under the
un-accelerated `step` coincide (the skipped value `3M+1` is never the first dip). -/
theorem covered_iff_msp2 {N : ℕ} (hN : 2 ≤ N) : Covered N ↔ ∃ j, msp2Step^[j] N < N := by
  sorry

/-! ## §16.3-16.5: the B constants and the useful distances -/

/-- **§16.3-16.4.** Closed form `B_n = (A_n − 1)/2` with `A_n = 3^(n+2)`. -/
theorem bConst_closed (n : ℕ) : 2 * bConst n + 1 = 3 ^ (n + 2) := by
  sorry

/-- **§16.4.** The parity of `B_n` alternates, starting even. -/
theorem bConst_parity (n : ℕ) : bConst n % 2 = n % 2 := by
  sorry

/-- **§16.3.** Under the vertical rule at `A = 3^(n+2)`, the useful distance from `1` to
`B_n` is `3^(n+1) + 1` (4, 10, 28, 82, …): reached at that step and not before. -/
theorem tA_distance (n : ℕ) :
    (tA (3 ^ (n + 2)))^[3 ^ (n + 1) + 1] 1 = bConst n ∧
      ∀ i < 3 ^ (n + 1) + 1, (tA (3 ^ (n + 2)))^[i] 1 ≠ bConst n := by
  sorry

/-- **§16.5.** The left route revisits the right side on alternate levels:
`C_{2m+2} = B_{2m+1}` (13, 121, 1093, …). -/
theorem cLeft_even_eq_bConst (m : ℕ) : cLeft (2 * m + 2) = bConst (2 * m + 1) := by
  sorry

/-- **§16.5.** The useful distance between the two sides at `A = 3^(m+3)` is `2·3^(m+1)`
(6, 18, 54, …), in the direction that alternates with the level. -/
theorem tA_distance_opt2 (m : ℕ) :
    if m % 2 = 0 then (tA (3 ^ (m + 3)))^[2 * 3 ^ (m + 1)] (cLeft (m + 1)) = bConst (m + 1)
    else (tA (3 ^ (m + 3)))^[2 * 3 ^ (m + 1)] (bConst (m + 1)) = cLeft (m + 1) := by
  sorry

/-! ## §16.7: the vertical rule is multiplication by `2⁻¹` -/

/-- **§16.7.1.** For odd `A`, `T_A(b) ≡ b·2⁻¹ (mod A)`, i.e. `2·T_A(b) ≡ b`. -/
theorem tA_two_mul {A : ℕ} (hA : A % 2 = 1) (b : ℕ) : 2 * tA A b ≡ b [MOD A] := by
  sorry

/-- **§16.7.2.** At `A = 3ⁿ` the vertical loop through any `b` prime to `3` has length
`2·3^(n−1)` (2 is a primitive root mod `3ⁿ`). -/
theorem tA_period {n b : ℕ} (hn : 1 ≤ n) (hb : b < 3 ^ n) (h3 : ¬ 3 ∣ b) :
    Function.minimalPeriod (tA (3 ^ n)) b = 2 * 3 ^ (n - 1) := by
  sorry

/-- **§16.7.4**, the closed form the article gives for its recurrence:
`Δ_n = (9·(−3)ⁿ − 5)/2`.  (This is algebra; the open question is whether the Generator
Table's cousin jumps obey `delta` at every level.) -/
theorem delta_closed (n : ℕ) : 2 * delta n = 9 * (-3) ^ n - 5 := by
  sorry

/-- **§16.7.4**, the conditional algebra: with the §16.4 passage (`k ↦ 2k+1` when `B_n` is
even, `k ↦ 2k` when odd, shift `+1`, cousin jump `+Δ_{n+1}`, halve), the jump `delta`
carries `B_n` to `B_{n+1}`. -/
theorem bConst_succ_via_delta (n : ℕ) :
    2 * (bConst (n + 1) : ℤ) =
      (if n % 2 = 0 then 3 * ((3 : ℤ) ^ (n + 2) + bConst n + 1) else 3 * ((bConst n : ℤ) + 1))
        + delta (n + 1) := by
  sorry

/-! ## §16.8: the residue bound -/

/-- **§16.8** (Proposition): for `m ≥ 2`, `B_{m−2} = (3^m − 1)/2 > K_m = 2^m − 1`. -/
theorem residue_bound {m : ℕ} (hm : 2 ≤ m) : 2 ^ m - 1 < (3 ^ m - 1) / 2 := by
  sorry

end MSP2
