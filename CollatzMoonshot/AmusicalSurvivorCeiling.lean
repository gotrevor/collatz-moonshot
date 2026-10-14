/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalSurvivorCeiling.Packing

/-!
# The survivor ceiling: finitely many orbits cap the survivor density at `c`

The 2026-10-14 "q1sharp" agent's Ceiling C2 and Consequence C2′ (research §26), re-derived
unconditionally by the "c1verify" agent (research §31).

**`fwdSurvivor_density_le_of_finite` (C2).**  If `U` has only finitely many orbits on `ℕ`, then for
every `L` the forward survivors have upper density at most `δ_L = fwdSurv L · bwdSurv L`.  No
statistical hypothesis on the orbits is needed: they partition `ℕ`, so their window statistics are
`ℕ`'s (`windowMinDensity`).

**`infinitelyManyOrbits_of_fwdSurvivor_density` (C2′).**  Hence forward survivors of upper density
above `c = minimaConstant` imply Klamkin (a) (`windowDensityLimit`: `δ_L → c`).  The measured
density is about `0.21` (research §20); proving any bound above `c ≈ 0.0498` is the typicality wall.
The rewired `τ` (§14) and `τ_odd` (§30) sit exactly on the ceiling: their forward survivors are
`U`'s orbit minima, so `c` cannot be lowered by an argument that also applies to them.

Paper proof (value form, no time indices):
* **P′.**  If `n' < n` are forward survivors on one orbit and `g` is `n`'s first backward drop
  (least `t ≥ 1` with `Vᵗ n < n`), then `n' ≤ Vᵍ n`.  Write `n' = Uᵏ n`: `k ≥ 0` is impossible; for
  `n' = Vᵗ n`, `t < g` gives `Vᵗ n ≥ n > n'`, and `t > g` gives `Vᵍ n = U^(t−g) n' ≥ n'`.
* **Gap.**  Lemma K backward at `n` (`abs_le_four_pow_mul_iterate_sub`): `n ≤ 4^L (n − n' + 1)` when
  `n` fails the backward `L`-window.
* **Packing.**  So on one orbit, forward survivors in `[X/M, X)` failing the backward `L`-window are
  spaced `≳ X/(M 4^L)` apart: at most `8 M 4^L + 1` of them.  The rest of the forward survivors in
  `[X/M, X)` are `L`-window minima.  Sum over the `r` orbits, let `X → ∞`, then `M → ∞`.

Agent report: `c1verify.md` (§5 has an 11-lemma decomposition).  The proofs here instantiate the
direction-generic lemmas of `AmusicalSurvivorCeiling/Packing.lean` with `(f, g) = (U, V)` and
`(V, U)`.
-/

namespace CollatzMoonshot.Amusical

open Classical in
/-- **Proved (C2).**  With finitely many orbits, forward survivors have upper density `≤ δ_L`. -/
theorem fwdSurvivor_density_le_of_finite (hfin : ¬ AmusicalInfinitelyManyOrbits) (L : ℕ)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ X : ℕ in Filter.atTop,
      (((Finset.range X).filter fun n : ℕ => FwdSurvivor n).card : ℝ) ≤
        (((fwdSurv L * bwdSurv L : ℚ) : ℝ) + ε) * X :=
  Ceiling.density_le_of_finite amusical_amusicalInv
    (fun ℓ hℓ x => (abs_le_four_pow_mul_iterate_sub ℓ hℓ x).2)
    (fun _ _ h => Ceiling.exists_iterate_of_mem_amusicalOrbit h)
    (fun _ _ hf hb t h1 h2 => ⟨hf t h1, hb t h1 h2⟩) hfin L hε

open Classical in
/-- **Proved (C2′).**  Forward survivors of upper density above `c` imply Klamkin (a). -/
theorem infinitelyManyOrbits_of_fwdSurvivor_density {η : ℝ} (hη : 0 < η)
    (h : ∃ᶠ X : ℕ in Filter.atTop,
      (minimaConstant + η) * X ≤ ((Finset.range X).filter fun n : ℕ => FwdSurvivor n).card) :
    AmusicalInfinitelyManyOrbits :=
  Ceiling.infinitelyManyOrbits_of_density amusical_amusicalInv
    (fun ℓ hℓ x => (abs_le_four_pow_mul_iterate_sub ℓ hℓ x).2)
    (fun _ _ h => Ceiling.exists_iterate_of_mem_amusicalOrbit h)
    (fun _ _ hf hb t h1 h2 => ⟨hf t h1, hb t h1 h2⟩) hη h

open Classical in
/-- **Proved (C2′, backward mirror).**  Backward survivors of upper density above `c` imply
Klamkin (a). -/
theorem infinitelyManyOrbits_of_bwdSurvivor_density {η : ℝ} (hη : 0 < η)
    (h : ∃ᶠ X : ℕ in Filter.atTop,
      (minimaConstant + η) * X ≤ ((Finset.range X).filter fun n : ℕ => BwdSurvivor n).card) :
    AmusicalInfinitelyManyOrbits :=
  Ceiling.infinitelyManyOrbits_of_density amusicalInv_amusical
    (fun ℓ hℓ x => (abs_le_four_pow_mul_iterate_sub ℓ hℓ x).1)
    (fun _ _ h => (Ceiling.exists_iterate_of_mem_amusicalOrbit h).imp fun _ => Or.symm)
    (fun _ _ hb hf t h1 h2 => ⟨hf t h1 h2, hb t h1⟩) hη h

end CollatzMoonshot.Amusical
