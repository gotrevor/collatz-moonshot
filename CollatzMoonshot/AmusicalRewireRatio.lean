/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalRewireRatio.Connectivity

/-!
# Bounded-ratio rewiring of `U` (Theorem R)

`rewire_single_orbit` (`AmusicalSeventh.lean`) fuses all infinite orbits of a permutation into
one by changing it on a density-`0` set.  For `U` itself the 2026-10-13 "global" agent sharpened
this: the change touches `O(log² N)` points below `N`, and each changed value stays within a
factor `3` of `U`'s (`exists_boundedRatio_rewire`).  So any property that survives such a
modification (flux, rotation-number analogues, crossing counts, finite-depth Cartesian-tree and
record statistics, Lemma K time separation) cannot prove a seventh orbit.

**Construction.**  Pick scales `Y_{k+1} ≥ 8 Y_k` with `Y_k` above the minimum of the `k`-th
infinite orbit `O_k`.  Cut each `O_i` at its first passage above `Y_k`, forward and backward, for
every `k ≥ i`; the cut points lie in `[Y_k, 1.5 Y_k + 1]` and their `U`-images in
`[(3Y_k − 1)/4, 2.25 Y_k + 2]`.  The cuts split the orbits into finite segments from scale `k` to
scale `k ± 1`, and an Eulerian-trail recursion
`T_{k+1} = B_{1,k} · T_k · F_{1,k} · core_{k+1} · B_{2,k} F_{2,k} ⋯ B_{k,k} F_{k,k}`
strings every segment into one bi-infinite chain, gluing ends to starts at the same scale.  `τ` is
the successor in the chain: it differs from `U` at most `2k` times at scale `k`, and only by
swapping one image at scale `k` for another.

Paper proof: agent report `global.md` §2 (2026-10-13; `rewire.py` builds the chain on `U`'s
apparent orbits below `1500`: one chain, ratio in `[0.336, 2.98]`).  Kernel-checked 2026-10-13 by the rewire treadmill
(`HANDOFF-amusical-rewire.md`).
-/

namespace CollatzMoonshot.Amusical

open CollatzMoonshot.Obstructions.Amusical

/-- **Proved (Theorem R).**  There is a permutation `τ` of `ℕ` that agrees with `U` on every
finite orbit, differs from `U` at `O(log² N)` points below `N`, stays within a factor `3` of `U`,
and has a single infinite orbit containing all of `U`'s infinite orbits. -/
theorem exists_boundedRatio_rewire :
    ∃ τ : Equiv.Perm ℕ,
      (∀ n : ℕ, (amusicalOrbit n).Finite → (τ n : ℤ) = amusical n) ∧
      (∃ C : ℕ, ∀ N : ℕ,
        ((Finset.range N).filter fun n => (τ n : ℤ) ≠ amusical n).card ≤
          C * (Nat.log 2 N + 1) ^ 2) ∧
      (∀ n : ℕ, (τ n : ℤ) ≤ 3 * amusical n + 3 ∧ amusical n ≤ 3 * (τ n : ℤ) + 3) ∧
      ∀ a b : ℕ, (amusicalOrbit a).Infinite → (amusicalOrbit b).Infinite →
        ∃ j : ℤ, (τ ^ j) a = b := by
  classical
  by_cases hex : ∃ n : ℕ, (amusicalOrbit (n : ℤ)).Infinite
  · let b := Nat.find hex
    have hbOrbit : (amusicalOrbit (b : ℤ)).Infinite := Nat.find_spec hex
    have hb : IsInfiniteOrbitRep (orbitMinNat (b : ℤ)) :=
      orbitMinNat_isInfiniteOrbitRep hbOrbit
    let r := orbitMinNat (b : ℤ)
    have hrb : r = b := by
      apply le_antisymm
      · exact_mod_cast orbitMinNat_le_of_nonneg_mem (Int.natCast_nonneg b)
          (mem_amusicalOrbit_self (b : ℤ))
      · exact Nat.find_min' hex hb.2
    have hrmin : ∀ s, IsInfiniteOrbitRep s → r ≤ s := by
      intro s hs
      rw [hrb]
      exact Nat.find_min' hex hs.2
    let d := BoundedRatioSourceRewire.ofScaleCutPerm
      (ScaleCutIndex.sweepCutPerm r hb)
      (ScaleCutIndex.sweepCutPerm_level r hb)
      (sweepRewired_connected r hb hrmin)
    exact d.realize
  · apply exists_boundedRatio_rewire_of_subsingleton_infiniteOrbits
    intro A hA B hB
    obtain ⟨a, rfl, ha⟩ := hA
    exact (hex ⟨a, ha⟩).elim

end CollatzMoonshot.Amusical
