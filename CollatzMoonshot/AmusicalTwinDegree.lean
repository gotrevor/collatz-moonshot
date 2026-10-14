/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalFunctionField
import CollatzMoonshot.AmusicalTwinDegree.Step

/-!
# The `𝔽₂[t]` twin: cycle minima are graded by the 2-adic valuation of the period

The 2026-10-13 "twin2" agent asked whether the twin of `AmusicalFunctionField` has an infinite
orbit.  It did not find one (its credence that the twin's extras make one provable is about 2%),
but it found an exact degree law for cycles and the reason Frobenius fails as an intertwiner.

**Theorem D (`twin_cycleMin_natDegree_le`).**  A cycle of period `p = 2^v q` (`q` odd) that avoids
the four exceptional points has minimum degree at most `2^v + 2`.  The odd part `q` is invisible.
Paper proof: on the cylinder of a word `w` of length `p`, `U^p x = (Q^p x + c_w) / t^{N_w}` with
`c_{j+1} = Q c_j + t^{N_j} e_{w_j}`, depths `(1, 2, 3, 3)` and offsets
`e = (0, t + 1, t⁴ + t³ + 1, t³ + t² + 1)`.  Away from the exceptional points the degree moves by
`+1, 0, −1, −1` per step, so a cycle has `N_w = 2p` and `x (t^{2p} − Q^p) = c_w`.
* (D1, `twin_den_natDegree`)  `t^{2p} − Q^p = (t^{2q} − Q^q)^{2^v}` by Frobenius, and in `Q^q` the
  `t^{2q}` terms cancel while the `t^{2q−1}` coefficient is `q = 1`.  So the degree is `2p − 2^v`.
* (D2)  Term `j` of `c_w = Σ Q^{p−1−j} t^{N_j} e_{w_j}` has degree `2p − 2 − S_j + deg e_{w_j}`,
  where `S_j = deg Uʲx − deg x ≥ 0` at the minimum.  So `deg c_w ≤ 2p + 2`.
Dividing gives `deg x ≤ 2^v + 2`.  The bound is tight up to one: freeform's Theorem F cycles have
minimum degree `p + 1` at `p = 2^e`.

Corollaries: each valuation class holds finitely many cycles, over all odd parts together
(`twin_cycleMins_finite`); a periodic polynomial of degree `d` has period at least `(2d − 4)/3`
(`twin_period_lower_bound`).  Over `ℤ`, Theorem A★ (`amusical_cycle_min_bound`) has no such
uniformity, since `|2^N − 3^p|` grows with every `p`.

**Frobenius is half an intertwiner.**  `U² (n²) = (U n)²` on the classes `E ∪ A`
(`twinU_twinU_sq`), but not on `B` or `C`.  The class read `n mod t³` forgets `n₂`, which is
what separates `B` from `C`, and Haar balance forces depth `3` there.  No class-wise constant
repair exists (`twin_no_classwise_frobenius`).  My proof, not the agent's: feeding
`n = 0, 1, 1 + t, Q` into the identity pins all four constants to `4` candidates, since `U² x = x`
only for `x ∈ {0, 1}`, and each candidate fails at `n = t`.  Proposition M
(`twin_not_periodic_of_selfSimilar`) records the certificate shape such an intertwiner would feed.

Paper proofs: agent report `twin2.md` §1, §2, §7, summarized in
`RESEARCH-2026-10-13-amusical-single-chain.md` §23.  I re-checked Theorem D independently
(`scripts/amusical/twin/twinD_ren.py`): D1 for `p ≤ 400`, and Theorem D plus the period bound on
all `113` cycles through polynomials of degree `< 16` (periods `8, 16, 20, 32, 48, 64`).  Teeth:
the bound without its `+ 2` fails on period `8`.  The class-wise no-go is
`scripts/amusical/twin/classwise_ren.py`.  Treadmill target: close every `sorry` here.
-/

namespace CollatzMoonshot.Amusical

open Polynomial

/-- The twin's exceptional points: `0` and `1` are fixed, and `t → Q → 1 + t → t` is a 3-cycle.
They are exactly the points where the degree walk `+1, 0, −1, −1` breaks. -/
noncomputable def twinExceptional : Set (ZMod 2)[X] := {0, 1, X + 1, twinQ}

/-- The twin's residue class: `E`, `A`, `B`, `C` read off the low coefficients, as in `twinU`. -/
noncomputable def twinClass (n : (ZMod 2)[X]) : Fin 4 :=
  if n.coeff 0 = 0 then 0 else if n.coeff 1 = 0 then 1 else if n.coeff 2 = 0 then 2 else 3

/-- **Target (D1).**  The cycle denominator has degree `2p − 2^{v₂(p)}`.  Paper proof: write
`p = 2^v q` with `q` odd; Frobenius gives `(t^{2q} − Q^q)^{2^v}`, and in `Q^q` the `t^{2q}`
coefficient is `1` and the `t^{2q−1}` coefficient is `q ≡ 1`. -/
theorem twin_den_natDegree (p : ℕ) (hp : 0 < p) :
    ((X ^ 2 : (ZMod 2)[X]) ^ p - twinQ ^ p).natDegree = 2 * p - 2 ^ padicValNat 2 p :=
  TwinDeg.den_natDegree p hp

/-- **Target (Theorem D).**  A non-exceptional cycle of period `2^v q` has minimum degree at
most `2^v + 2`.  Paper proof in the module docstring: `x (t^{2p} − Q^p) = c_w` with
`deg c_w ≤ 2p + 2` at the minimum, and `twin_den_natDegree`. -/
theorem twin_cycleMin_natDegree_le (x : (ZMod 2)[X]) (hx : x ∈ Function.periodicPts twinU)
    (hmin : ∀ j, x.natDegree ≤ (twinU^[j] x).natDegree) (hexc : x ∉ twinExceptional) :
    x.natDegree ≤ 2 ^ padicValNat 2 (Function.minimalPeriod twinU x) + 2 :=
  TwinDeg.cycleMin_natDegree_le x hx hmin

/-- **Target (D-i).**  For each `v`, finitely many cycle minima have period of 2-adic valuation
`v`, over all odd parts together.  Paper proof: Theorem D bounds their degree by `2^v + 2`, and
`𝔽₂` is finite; the exceptional points are four more. -/
theorem twin_cycleMins_finite (v : ℕ) :
    {x : (ZMod 2)[X] | x ∈ Function.periodicPts twinU ∧
      padicValNat 2 (Function.minimalPeriod twinU x) = v ∧
      ∀ j, x.natDegree ≤ (twinU^[j] x).natDegree}.Finite := by
  sorry

/-- **Target (D-iii).**  A periodic polynomial of degree `d` has period `p` with
`2d ≤ 3p + 4`.  Paper proof: with `m` the cycle's minimum degree, `#E = #B + #C ≤ p/2` on a
balanced word, so `d − m ≤ p/2`; and `m ≤ 2^v + 2 ≤ p + 2` by Theorem D.  The exceptional cycles
have degree at most `2`. -/
theorem twin_period_lower_bound (x : (ZMod 2)[X]) (hx : x ∈ Function.periodicPts twinU) :
    2 * x.natDegree ≤ 3 * Function.minimalPeriod twinU x + 4 := by
  sorry

/-- **Target (Frobenius on the shallow classes).**  `U² (n²) = (U n)²` for `n ∈ E ∪ A`.  Paper
proof: `n = t m` gives `n² = t² m² ↦ Q t m² ↦ Q² m²`; `n = 1 + t² m` gives
`n² = 1 + t⁴ m² ↦ Q t² m² + 1 ↦ Q² m² + 1`. -/
theorem twinU_twinU_sq (n : (ZMod 2)[X]) (h : n.coeff 0 = 0 ∨ n.coeff 1 = 0) :
    twinU (twinU (n ^ 2)) = twinU n ^ 2 := by
  sorry

/-- **Target (no class-wise Frobenius repair).**  No constants `κ_E, κ_A, κ_B, κ_C` make
`n ↦ n² + κ_{cls n}` a semiconjugacy from `U` to `U²`.  Paper proof: `n = 0` and `n = 1` force
`U² κ_E = κ_E` and `U² (1 + κ_A) = 1 + κ_A`, so both lie in `{0, 1}` (by `twin_period_lower_bound`
such points have degree `≤ 5`, and a search finds only these).  `n = 1 + t` (with `U n = t`) and
`n = Q` (with `U n = 1 + t`) then determine `κ_B` and `κ_C`.  All four candidates fail at `n = t`
(`scripts/amusical/twin/classwise_ren.py`). -/
theorem twin_no_classwise_frobenius :
    ¬ ∃ κ : Fin 4 → (ZMod 2)[X], ∀ n, twinU (twinU (n ^ 2 + κ (twinClass n))) =
      twinU n ^ 2 + κ (twinClass (twinU n)) := by
  sorry

/-- **Target (Proposition M).**  A self-similar point certifies an infinite orbit.  If squaring
plus a constant from a finite set `C` is carried along every orbit, and `z² + c` lies on the
forward orbit of `z`, then `z` is not periodic.  Paper proof: the forward orbit of `z` then
contains `y² + c'` for every `y` on it.  Take `y` of maximal degree on a cycle: `y² + c'` has
degree `2 deg y > deg y`.  The hypothesis fails for the twin (`twin_no_classwise_frobenius`
kills the simplest form); the statement records the shape for a future intertwiner. -/
theorem twin_not_periodic_of_selfSimilar (C : Finset (ZMod 2)[X])
    (hC : ∀ z, ∀ c ∈ C, ∃ k, 1 ≤ k ∧ ∃ c' ∈ C, twinU^[k] (z ^ 2 + c) = twinU z ^ 2 + c')
    (z : (ZMod 2)[X]) (hdeg : ∀ c ∈ C, c.natDegree < z.natDegree)
    (hz : ∃ c ∈ C, ∃ a, twinU^[a] z = z ^ 2 + c) : z ∉ Function.periodicPts twinU := by
  sorry

end CollatzMoonshot.Amusical
