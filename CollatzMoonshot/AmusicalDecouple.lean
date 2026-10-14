/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalFormalMin
import CollatzMoonshot.AmusicalLateDrops
import CollatzMoonshot.AmusicalSpitzer

/-!
# The two primes decouple: Lemma D, and the formal-minimum route to Klamkin (a)

The 2026-10-14 "lfprobe" agent asked what ringunit's Conjecture LF (research §28) really is.
Answer (research §32): it has no joint 2-adic/3-adic content.

**`tendsto_density_inter_of_two_three` (Lemma D).**  Let `A_L` be eventually periodic with
power-of-`2` periods and `B_L` with power-of-`3` periods.  If `⋂ A_L` has density `α = lim d(A_L)`
and `⋂ B_L` has density `β = lim d(B_L)`, then `⋂ A_L ∩ ⋂ B_L` has density `αβ`.  Only CRT is
used.  (i) `B := ⋂ B_L` is equidistributed mod `2ⁿ`: a class `r + 2ⁿℕ` meets `B_L` in density
`d(B_L)/2ⁿ`, so `B` has upper density `≤ β/2ⁿ` there, and the complement of the other `2ⁿ − 1`
classes gives the matching lower bound.  (ii) `A_L` is, up to a finite set, a union of classes
mod `2^a`, so `d(A_L ∩ B) = d(A_L) β`, and `d(A_L \ A) = d(A_L) − α → 0`.

**`orbitMin_density_of_survivor_densities` (Corollary MD).**  The conjectured orbit-minimum
density `c = p_f p_b` is not a joint statement: it follows from forward survivors having density
`p_f` and backward survivors density `p_b`.  The forward `L`-window is eventually `2^(2L)`-periodic
(the first `L` steps read at most `2L` bits, and above `4^L`-scale heights Lemma K fixes the sign of
`Uᵗ n − n` by the slope), the backward one eventually `3^L`-periodic, and
`IsOrbitMin n ↔ FwdSurvivor n ∧ BwdSurvivor n`.

**`not_formalMin_of_three_dvd`.**  `V(3m) = 2m` is even, so `kBwd y 1 = 1` and `3 < 2` fails:
formal minima avoid `3ℤ`, and the formal-minimum route never meets the Sep3 / staircase witnesses
(§26, §30).

**`infinitelyManyOrbits_of_ray`.**  Infinitely many formal minima on a ray `uᵏ x` give Klamkin (a)
(`formalMin_unique`).  One hit already settles Conway's question (`not_formalMin_of_periodic`), so
no positive lower bound on the ray is in reach.
-/

namespace CollatzMoonshot.Amusical

open Classical in
/-- The number of elements of `S` below `X`. -/
noncomputable def countBelow (S : Set ℕ) (X : ℕ) : ℕ :=
  ((Finset.range X).filter fun n => n ∈ S).card

/-- **Target (Lemma D).**  Eventually `2`-power-periodic and eventually `3`-power-periodic window
families decouple in the infinite-horizon limit. -/
theorem tendsto_density_inter_of_two_three {A B : ℕ → Set ℕ}
    (pA : ∀ L, ∃ a N : ℕ, ∀ n, N ≤ n → (n ∈ A L ↔ n + 2 ^ a ∈ A L))
    (pB : ∀ L, ∃ b N : ℕ, ∀ n, N ≤ n → (n ∈ B L ↔ n + 3 ^ b ∈ B L))
    {a b : ℕ → ℝ} {α β : ℝ}
    (hAL : ∀ L, Filter.Tendsto (fun X : ℕ => (countBelow (A L) X : ℝ) / X) Filter.atTop
      (nhds (a L)))
    (hBL : ∀ L, Filter.Tendsto (fun X : ℕ => (countBelow (B L) X : ℝ) / X) Filter.atTop
      (nhds (b L)))
    (ha : Filter.Tendsto a Filter.atTop (nhds α)) (hb : Filter.Tendsto b Filter.atTop (nhds β))
    (hA : Filter.Tendsto (fun X : ℕ => (countBelow (⋂ L, A L) X : ℝ) / X) Filter.atTop
      (nhds α))
    (hB : Filter.Tendsto (fun X : ℕ => (countBelow (⋂ L, B L) X : ℝ) / X) Filter.atTop
      (nhds β)) :
    Filter.Tendsto (fun X : ℕ => (countBelow ((⋂ L, A L) ∩ ⋂ L, B L) X : ℝ) / X)
      Filter.atTop (nhds (α * β)) := by
  sorry

/-- **Target (Corollary MD).**  If forward and backward survivors have the densities the windows
predict, orbit minima have density `minimaConstant`. -/
theorem orbitMin_density_of_survivor_densities {pf pb : ℝ}
    (hpf : Filter.Tendsto (fun L : ℕ => (fwdSurv L : ℝ)) Filter.atTop (nhds pf))
    (hpb : Filter.Tendsto (fun L : ℕ => (bwdSurv L : ℝ)) Filter.atTop (nhds pb))
    (hF : Filter.Tendsto
      (fun X : ℕ => (countBelow {n : ℕ | FwdSurvivor n} X : ℝ) / X) Filter.atTop (nhds pf))
    (hB : Filter.Tendsto
      (fun X : ℕ => (countBelow {n : ℕ | BwdSurvivor n} X : ℝ) / X) Filter.atTop (nhds pb)) :
    Filter.Tendsto (fun X : ℕ => (countBelow {n : ℕ | IsOrbitMin n} X : ℝ) / X) Filter.atTop
      (nhds minimaConstant) := by
  sorry

/-- **Target.**  Formal minima avoid `3ℤ`. -/
theorem not_formalMin_of_three_dvd {y : ℤ} (h : 3 ∣ y) : ¬ FormalMin y := by
  intro hy
  have h1 := (hy 1 le_rfl).2
  obtain ⟨m, rfl⟩ := h
  have hinv : amusicalInv (3 * m) = 2 * m := by
    unfold amusicalInv; split_ifs <;> omega
  have hk : kBwd (3 * m) 1 = 1 := by
    simp [kBwd, hinv, stepBits]
  rw [hk] at h1
  norm_num at h1

/-- **Target.**  Infinitely many formal minima on a ray `uᵏ x` imply Klamkin (a). -/
theorem infinitelyManyOrbits_of_ray {u x : ℤ} (hu : 1 < u) (hx : 0 < x)
    (h : {k : ℕ | FormalMin (u ^ k * x)}.Infinite) : AmusicalInfinitelyManyOrbits := by
  apply infinitelyManyOrbits_of_formalMin_infinite
  have hpos : ∀ k : ℕ, 0 < u ^ k * x := fun k => mul_pos (pow_pos (by omega) k) hx
  have hmono : StrictMono fun k : ℕ => u ^ k * x := fun i j hij =>
    mul_lt_mul_of_pos_right (pow_lt_pow_right₀ hu hij) hx
  refine Set.infinite_of_injOn_mapsTo (f := fun k : ℕ => (u ^ k * x).toNat) ?_ ?_ h
  · intro i _ j _ hij
    have := congrArg (fun n : ℕ => (n : ℤ)) hij
    simp only [Int.toNat_of_nonneg (hpos i).le, Int.toNat_of_nonneg (hpos j).le] at this
    exact hmono.injective this
  · intro k hk
    simp only [Set.mem_ofPred_eq, Int.toNat_of_nonneg (hpos k).le]
    exact hk

end CollatzMoonshot.Amusical
