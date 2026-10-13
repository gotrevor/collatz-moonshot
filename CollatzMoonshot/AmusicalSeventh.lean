/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Obstructions.Amusical

/-!
# Toward a seventh orbit: what a cofinite orbit would need, and why statistics cannot refute it

Only six orbits of `U` on `ℕ` are known to be distinct (`amusical_six_distinct_orbits`).  A
seventh orbit is the same as "no orbit of `U` is cofinite in `ℕ`"
(`atLeastSeven_of_orbit8_not_cofinite`).  This file records what the 2026-10-13 "seventh" agent
proved toward it, and the barrier it found.

* `sparse_sweep` (unconditional): an infinite orbit visits at most `ηX` of the numbers below `X`
  within any time window of length `2cX log X`.  So a cofinite orbit would need time `≳ n log n`
  to reach almost every `n`.
* `amusical_pow_classUnion_invariant`: every `Uᵐ` is residue-transitive, so no union of residue
  classes is `Uᵐ`-invariant except `∅` and `ℤ`; under a single cofinite orbit the time function
  would have no periodic shadow mod any `m ≥ 2`.
* `rewire_single_orbit` (the barrier): a permutation of `ℕ` with steps at most doubling can be
  changed on a set of density `0` so that all its infinite orbits fuse into one.  Applied to `U`
  (if it has an infinite orbit) this gives a permutation that agrees with `U` off a density-`0` set,
  shares every density, log-density, window and crossing statistic, and has exactly the cycles plus
  one orbit.  So no argument built from such statistics can prove a seventh orbit: a proof must use
  the exact value of `U` everywhere, plus a global mechanism.

Paper proofs: agent report `seventh.md` (2026-10-13), summarized in
`RESEARCH-2026-10-13-amusical-single-chain.md` §11.  Treadmill target
(`KICKOFF-2026-10-13-amusical-seventh.md`): close every `sorry` here.
-/

namespace CollatzMoonshot.Amusical

open CollatzMoonshot.Obstructions.Amusical

/-- **Target.**  If the orbit of `8` misses infinitely many nonnegative integers, there is a seventh
orbit.  Paper proof: pick a nonnegative `n` outside `knownCycleMembers` and outside the orbit of
`8`; its orbit differs from the orbit of `8` (it does not contain `8`) and from each known cycle's
orbit (each is contained in `knownCycleMembers`); add `n` to `{0, 1, 2, 4, 44, 8}`. -/
theorem atLeastSeven_of_orbit8_not_cofinite
    (h : ({n : ℤ | 0 ≤ n} \ amusicalOrbit 8).Infinite) : AmusicalAtLeastSevenOrbits := by
  sorry

/-- **Target (sparse sweeping).**  For every `η > 0` there is `c > 0` such that, for all large `X`,
every infinite orbit spends at most `ηX` of the times `|j| ≤ cX log X` below `X`.  Paper proof: for
`n ≥ 2·324^L` the order of `U^i n` and `n`, `|i| ≤ L`, is a residue condition mod `12^L` (Lemma W);
outside a set of density `2ρ^{K+1}/(1−ρ)`, `ρ = 1/√6 + 1/√3 < 1`, the minimum of the `L`-window
of `n` sits within `K` steps (Lemma T, Chernoff over residues); that minimum is an
`(L−K)`-window minimum, and window minima on one orbit are more than `L−K` steps apart
(`IsWindowMin.iterate_eq_of_isWindowMin`); take `L ≍ log X`. -/
theorem sparse_sweep : ∀ η : ℝ, 0 < η → ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ x : ℤ,
    (amusicalOrbit x).Infinite →
    (((Finset.Icc (-⌊c * X * Real.log X⌋) ⌊c * X * Real.log X⌋).filter
        fun j => 0 ≤ (amusicalPerm ^ j) x ∧ (amusicalPerm ^ j) x < X).card : ℝ) ≤ η * X := by
  sorry

/-- **Target (residue transitivity).**  No nontrivial union of residue classes mod `M` is mapped
onto itself by `Uᵐ`, for any `m ≥ 1`.  Paper proof: the residue graph of `Uᵐ` mod `M` is strongly
connected.  Write `M = 2^i 3^j N` with `gcd(N, 6) = 1`; the affine maps mod `N` of branch words
whose length is `≡ 0 (mod m)` form a subgroup of `Aff(ℤ/N)` containing `A^m` and `A^{m−1} ∘ B`,
hence the translation `A⁻¹ ∘ B : z ↦ z − 2/3`, so it is transitive; the `2`-adic prefix and
`3`-adic suffix are absorbed by choosing the word (agent report `relative.md` §4, `seventh.md`
T4). -/
theorem amusical_pow_classUnion_invariant (m M : ℕ) (hm : 0 < m) (hM : 0 < M)
    (R : Set (ZMod M))
    (h : (amusical^[m]) '' {n : ℤ | (n : ZMod M) ∈ R} = {n : ℤ | (n : ZMod M) ∈ R}) :
    R = ∅ ∨ R = Set.univ := by
  sorry

/-- **Target (the rewiring barrier).**  A permutation of `ℕ` whose steps at most double (as `U` and
`U⁻¹` do on `ℕ`) agrees, off a set of density `0` and on every finite orbit, with a permutation in
which all the infinite orbits form a single orbit.  Paper proof: every infinite orbit tends to `∞`
in both time directions (injectivity), and a step from below `Y` lands below `2Y`, so each infinite
orbit has a point in `[Y, 2Y)` at positive and at negative times for every large `Y`.  Enumerate
the infinite orbits; for `Y_k = 4^k` cut orbit `i ≤ k` once on each side inside `[Y_k, 2Y_k)` (at
most `2k` cuts there, `O((log N)²)` below `N`).  The cuts split the infinite orbits into finite
segments; enumerate the segments by `ℤ` and send the last point of segment `z` to the first of
segment `z + 1`. -/
theorem rewire_single_orbit (σ : Equiv.Perm ℕ)
    (hstep : ∀ n, σ n ≤ 2 * n + 1 ∧ σ.symm n ≤ 2 * n + 1) :
    ∃ τ : Equiv.Perm ℕ,
      (∀ n, (Set.range fun j : ℤ => (σ ^ j) n).Finite → τ n = σ n) ∧
      Filter.Tendsto (fun N : ℕ => (((Finset.range N).filter fun n => τ n ≠ σ n).card : ℝ) / N)
        Filter.atTop (nhds 0) ∧
      ∀ a b, (Set.range fun j : ℤ => (σ ^ j) a).Infinite →
        (Set.range fun j : ℤ => (σ ^ j) b).Infinite → ∃ j : ℤ, (τ ^ j) a = b := by
  sorry

end CollatzMoonshot.Amusical
