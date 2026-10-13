/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Amusical

/-!
# Statistical twins of `U`

A *twin* of `U` is a residue-class-affine bijection with exactly `U`'s branch slopes and branch
classes, hence the same cylinder laws (forward `(1/2, 1/4, 1/4)`, backward uniform), the same
window-minimum densities `δ_L`, and the same full-shift coding.  The 2026-10-13 "twin" agent asked
whether a twin can have finitely many orbits, which would be a formal barrier for statistical
arguments.  Findings:

* Twins do not share `U`'s cycles: `twinW` (`U` with `+3` on the even branch) is a bijection with
  the `3`-cycle `8 → 15 → 11 → 8`, while `U` has no `3`-cycle
  (`amusical_no_threeCycle`), so the two are not conjugate (`twinW_not_conj_amusical`).
  Statistics fix neither the cycles nor the orbit structure.
* A twin with finitely many orbits is not known; proving none exists is at least as hard as
  Klamkin's problem (a), since `U` is its own twin.  The barrier the agent wanted is supplied
  instead by rewiring (`rewire_single_orbit` in `AmusicalSeventh.lean`, and the agent's sharper
  splice: a one-orbit bijection agreeing with `U` off `O(log Y)` points of `[−Y, Y]` plus one
  point per cycle).

Paper proofs: agent report `twin.md` (2026-10-13), summarized in
`RESEARCH-2026-10-13-amusical-single-chain.md` §12.  Treadmill target
(`KICKOFF-2026-10-13-amusical-twin.md`): close every `sorry` here.
-/

namespace CollatzMoonshot.Amusical

/-- The twin `W(2m) = 3m + 3`, `W(4m+1) = 3m + 1`, `W(4m+3) = 3m + 2`: `U` followed by `+3` on
the multiples of `3`.  Same branch classes and slopes as `U`. -/
def twinW (n : ℤ) : ℤ :=
  if n % 2 = 0 then 3 * (n / 2) + 3
  else if n % 4 = 1 then 3 * (n / 4) + 1
  else 3 * (n / 4) + 2

theorem twinW_eq (n : ℤ) : twinW n = amusical n + if n % 2 = 0 then 3 else 0 := by
  unfold twinW amusical
  split_ifs <;> ring

/-- `8 → 15 → 11 → 8` is a `3`-cycle of the twin. -/
theorem twinW_threeCycle : twinW 8 = 15 ∧ twinW 15 = 11 ∧ twinW 11 = 8 := by
  decide

/-- The inverse of `twinW`, separated by the three image classes modulo `3`. -/
def twinWInv (m : ℤ) : ℤ :=
  if m % 3 = 0 then 2 * (m / 3 - 1)
  else if m % 3 = 1 then 4 * (m / 3) + 1
  else 4 * (m / 3) + 3

theorem twinWInv_twinW (n : ℤ) : twinWInv (twinW n) = n := by
  unfold twinWInv twinW
  split_ifs <;> omega

theorem twinW_twinWInv (m : ℤ) : twinW (twinWInv m) = m := by
  unfold twinWInv twinW
  split_ifs <;> omega

/-- **Target.**  The twin is a bijection: its three branches land in the classes `0, 1, 2 mod 3`
and each is a bijection onto its class. -/
theorem twinW_bijective : Function.Bijective twinW := by
  exact ⟨Function.LeftInverse.injective twinWInv_twinW,
    Function.RightInverse.surjective twinW_twinWInv⟩

/-- **Target.**  `U` has no `3`-cycle: `U³ n = n` forces `U n = n`.  Paper proof: on each class
mod `64` with a fixed branch word, `U³ n = (27 n + b)/2^w` with `w ∈ {3, …, 6}`, so a solution
is `n = b/(2^w − 27)` with `|b|` bounded; check the finitely many candidates (`|n| ≤ 200`
suffices; all are the fixed points `0, ±1`). -/
theorem amusical_no_threeCycle (n : ℤ) (h : amusical^[3] n = n) : amusical n = n := by
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply] at h
  unfold amusical at h ⊢
  split_ifs at h ⊢ <;> omega

/-- **Target.**  `U` and its twin are not conjugate by any bijection of `ℤ`: a conjugacy carries
the twin's `3`-cycle to a `3`-cycle of `U`. -/
theorem twinW_not_conj_amusical :
    ¬ ∃ φ : ℤ → ℤ, Function.Injective φ ∧ ∀ n, φ (twinW n) = amusical (φ n) := by
  rintro ⟨φ, hφ, hconj⟩
  have hcycle : amusical^[3] (φ 8) = φ 8 := by
    simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
    rw [← hconj 8, twinW_threeCycle.1, ← hconj 15, twinW_threeCycle.2.1,
      ← hconj 11, twinW_threeCycle.2.2]
  have hfixed := amusical_no_threeCycle (φ 8) hcycle
  have himage : φ (twinW 8) = φ 8 := by
    rw [hconj 8, hfixed]
  have := hφ himage
  norm_num [twinW] at this

end CollatzMoonshot.Amusical
