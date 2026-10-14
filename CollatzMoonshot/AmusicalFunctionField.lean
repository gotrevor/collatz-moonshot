/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Amusical
import CollatzMoonshot.AmusicalFunctionField.Cycle

/-!
# The `𝔽₂[t]` twin of the amusical permutation has infinitely many orbits

The 2026-10-13 "freeform" agent built the function-field analogue of `U`, replacing `(ℤ, 2, 3)`
with `(𝔽₂[t], t, Q)`, `Q = t² + t + 1`.  Haar balance forces cylinder depths `(1, 2, 3, 3)`:
* `U(t m) = Q m`;
* `U(1 + t² m) = Q m + 1`;
* `U(1 + t + t³ m) = Q m + t`;
* `U(1 + t + t² + t³ m) = Q m + 1 + t` (`twinU`).
It is residue-transitive at every modulus the agent tested.  Its full-shift conjugacy,
Böhm–Sontacchi cycle formula, and every wall of the integer problem (mass conservation, rewiring,
no residue transversal, Theorem NR) carry over.

**Theorem F (`twinCycle_minimalPeriod`).**  For `p = 2^e ≥ 8` and `m = p/2`, the polynomial
`(t⁴ + t³ + 1) t^m (t+1)^(m−3)` lies on a cycle of exact length `p`, with itinerary `E^m B^m`.  So
the twin has infinitely many orbits (`twin_infinitelyManyCycles`), and the proof never touches an
infinite orbit.  The mechanism is Frobenius: for `m` a power of `2`,
`t^{3m} + Q^m = (t³ + Q)^m = (t+1)^{3m}`, and the cycle denominator `t^{2p} − Q^p = (t+1)^p` is
tiny (`twin_den_frobenius`).

**What fails over `ℤ`.**  The same word `E^m B^m` for `U` closes at
`2^m (4^m − 3^m) / (9^m − 8^m)`, an integer only for `m = 1` (the cycle `{2, 3}`)
(`amusical_EmBm_not_integral`).  The missing identity is `(a^m − b^m)/(a − b) = (a − b)^{m−1}`, i.e.
smallness of `2^N − 3^p`, which Mihăilescu and Baker forbid.  So Klamkin (a) splits cleanly into a
Diophantine half and a dynamical half.  The twin is the world where the Diophantine half is free.
Over `ℤ`, cycles are believed finite (research §5), so any proof of Klamkin (a) must exhibit
infinitely many *infinite* orbits.  Even "one infinite orbit exists" is open for the twin.

Paper proofs: agent report `freeform.md` §1–§5, summarized in
`RESEARCH-2026-10-13-amusical-single-chain.md` §21.  I re-checked Theorem F independently with my
own carry-less arithmetic (`scripts/amusical/twin/fftwin_ren.py`): exact periods and itineraries for
`p = 8, …, 256`, bijectivity on degrees `< 14`.  Teeth: `p = 10, 12, 14` and `s_E ≠ 0` do not
close.  Every statement here is proved; the closed-form orbit is in
`CollatzMoonshot/AmusicalFunctionField/Cycle.lean`.
-/

namespace CollatzMoonshot.Amusical

open Polynomial

/-- The twin's "3": `Q = t² + t + 1`, irreducible over `𝔽₂`. -/
noncomputable def twinQ : (ZMod 2)[X] := X ^ 2 + X + 1

/-- The `𝔽₂[t]` twin of `U`, read off the low coefficients of `n`. -/
noncomputable def twinU (n : (ZMod 2)[X]) : (ZMod 2)[X] :=
  if n.coeff 0 = 0 then twinQ * (n /ₘ X)
  else if n.coeff 1 = 0 then twinQ * ((n - 1) /ₘ X ^ 2) + 1
  else if n.coeff 2 = 0 then twinQ * ((n - 1 - X) /ₘ X ^ 3) + X
  else twinQ * ((n - 1 - X - X ^ 2) /ₘ X ^ 3) + (1 + X)

/-- **Proved** (`FFTwin.fU_bijective`).  The twin is a permutation of `𝔽₂[t]`.  The domains
`t𝔽₂[t]`, `1 + t²𝔽₂[t]`, `1 + t + t³𝔽₂[t]`, `1 + t + t² + t³𝔽₂[t]` partition `𝔽₂[t]`, and the
images `Q 𝔽₂[t] + s` for `s ∈ {0, 1, t, 1 + t}` partition it too, since these are the residues
mod `Q`. -/
theorem twinU_bijective : Function.Bijective twinU := FFTwin.fU_bijective

/-- **Proved.**  The cycle denominator collapses: `(t²)^(2^e) − Q^(2^e) = (t + 1)^(2^e)`
(Frobenius in characteristic `2`). -/
theorem twin_den_frobenius (e : ℕ) :
    (X ^ 2 : (ZMod 2)[X]) ^ (2 ^ e) - twinQ ^ (2 ^ e) = (X + 1) ^ (2 ^ e) := by
  rw [← sub_pow_char_pow (p := 2)]
  congr 1
  have h2 : (2 : (ZMod 2)[X]) = 0 := CharTwo.two_eq_zero
  unfold twinQ
  linear_combination (-(1 : (ZMod 2)[X]) - X) * h2

/-- The Theorem F point of period `2^e`: `(t⁴ + t³ + 1) t^m (t+1)^(m−3)` with `m = 2^(e−1)`. -/
noncomputable def twinCycle (e : ℕ) : (ZMod 2)[X] :=
  (X ^ 4 + X ^ 3 + 1) * X ^ (2 ^ (e - 1)) * (X + 1) ^ (2 ^ (e - 1) - 3)

/-- **Proved (Theorem F**, `FFTwin.fU_minimalPeriod`**).**  For `e ≥ 3`, `twinCycle e` has exact
period `2^e`.  Paper proof (`freeform.md` §3): along `E^m B^m` the `E` steps add nothing, and the
`B` steps sum to `e_B t^m (t^{3m} + Q^m)/(t³ + Q) = e_B t^m (t+1)^{3m−3}`.  Dividing by
`t^{2p} − Q^p = (t + 1)^{2m}` gives the point.  The Lean proof runs the orbit in closed form
(`CollatzMoonshot/AmusicalFunctionField/Cycle.lean`); exactness is cheaper than primitivity of
the word: the period divides `2^e`, and `U^m x₀` has constant term `1` while `x₀` has `0`. -/
theorem twinCycle_minimalPeriod (e : ℕ) (he : 3 ≤ e) :
    Function.minimalPeriod twinU (twinCycle e) = 2 ^ e := by
  obtain ⟨n, rfl⟩ : ∃ n, e = n + 1 := ⟨e - 1, by omega⟩
  exact FFTwin.fU_minimalPeriod n (by omega)

private lemma twinCycle_mem_periodicPts (e : ℕ) (he : 3 ≤ e) :
    twinCycle e ∈ Function.periodicPts twinU := by
  apply Function.minimalPeriod_pos_iff_mem_periodicPts.mp
  rw [twinCycle_minimalPeriod e he]; positivity

/-- **Proved from Theorem F.**  The twin has infinitely many cycles, hence infinitely many orbits:
cycles of distinct exact lengths are distinct sets. -/
theorem twin_infinitelyManyCycles :
    {O : Set (ZMod 2)[X] | ∃ x ∈ Function.periodicPts twinU,
      O = Set.range fun n : ℕ => twinU^[n] x}.Infinite := by
  let orb : ℕ → Set (ZMod 2)[X] := fun k => Set.range fun n : ℕ => twinU^[n] (twinCycle (k + 3))
  refine Set.infinite_of_injective_forall_mem (f := orb) ?_ ?_
  · intro a b hab
    have hmem : twinCycle (b + 3) ∈ orb a := by
      rw [hab]; exact ⟨0, rfl⟩
    obtain ⟨k, hk⟩ := hmem
    have hper :=
      Function.minimalPeriod_apply_iterate (twinCycle_mem_periodicPts (a + 3) (by omega)) k
    simp only at hk
    rw [hk, twinCycle_minimalPeriod _ (by omega), twinCycle_minimalPeriod _ (by omega)] at hper
    have := Nat.pow_right_injective (le_refl 2) hper
    omega
  · intro k
    exact ⟨twinCycle (k + 3), twinCycle_mem_periodicPts _ (by omega), rfl⟩

private lemma two_mul_eight_pow_lt (m : ℕ) (hm : 6 ≤ m) : 2 * 8 ^ m < 9 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ n _ ih => rw [pow_succ, pow_succ]; omega

/-- **Proved (what fails over `ℤ`).**  The `ℤ` analogue of Theorem F's point, the periodic point
`2^m (4^m − 3^m) / (9^m − 8^m)` of the word `E^m B^m`, is not an integer for `m ≥ 2`.  For
`m ≥ 5` the numerator `8^m − 6^m` is positive and below the denominator; `m = 2, 3, 4` are direct
checks. -/
theorem amusical_EmBm_not_integral (m : ℕ) (hm : 2 ≤ m) :
    ¬ ((9 : ℤ) ^ m - 8 ^ m ∣ 2 ^ m * (4 ^ m - 3 ^ m)) := by
  have hnum : (2 : ℤ) ^ m * (4 ^ m - 3 ^ m) = 8 ^ m - 6 ^ m := by
    rw [mul_sub, ← mul_pow, ← mul_pow]; norm_num
  rw [hnum]
  rcases (show m = 2 ∨ m = 3 ∨ m = 4 ∨ 5 ≤ m by omega) with rfl | rfl | rfl | h5
  · decide
  · decide
  · decide
  intro hd
  have hlt : (6 : ℤ) ^ m < 8 ^ m := pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
  have hbig : (8 : ℤ) ^ m - 6 ^ m < 9 ^ m - 8 ^ m := by
    rcases (show m = 5 ∨ 6 ≤ m by omega) with rfl | h6
    · norm_num
    · have h' : (2 : ℤ) * 8 ^ m < 9 ^ m := by exact_mod_cast two_mul_eight_pow_lt m h6
      have h6pos : (0 : ℤ) < 6 ^ m := by positivity
      linarith
  have := Int.le_of_dvd (by omega) hd
  omega

end CollatzMoonshot.Amusical
