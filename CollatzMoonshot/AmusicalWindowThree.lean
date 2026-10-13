/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalEscape

/-!
# No bijective reversor reads a window of three symbols

`AmusicalNoContinuousReversor` asks for a bijective reversor `ι` whose step symbol
`stepSym (ι n)` is determined by a residue of `n`.  This file kills the smallest nontrivial
case exactly: `stepSym (ι n)` a function of the three symbols `stepSym (U⁻¹ n)`,
`stepSym n`, `stepSym (U n)` (`no_window3_bijective_reversor`).  Any other offset reduces to this
one by composing `ι` with a power of `U`.

The proof uses only finite information:

* **Cycles.**  A bijective reversor maps integer cycles onto integer cycles of the same length.
  The integer cycles of length at most `12` are the nine known ones (`0`, `±1`, `±{2, 3}`,
  `±{4, 6, 9, 7, 5}`, `±` the `12`-cycle through `44`), by `amusical_periodic_mem`.  Matching
  them forces `f` on `25` of its `27` blocks, in one of `24` ways.
* **Orphans.**  Each of the `24 · 9 = 216` completions has an orphan word of length at most `5`:
  a word that never occurs in the forward itinerary of any `ι n`.  Every finite word occurs in
  the forward itinerary of some integer (`exists_forward_itinerary`), so `ι` is not onto.

Paper proof: agent report `q1.md` §4 (2026-10-13), re-derived independently by
`scripts/amusical/w3check.py`; certificates in `scripts/amusical/w3certs.txt`.  Treadmill target
(`KICKOFF-2026-10-13-amusical-w3.md`): close every `sorry` here.
-/

namespace CollatzMoonshot.Amusical

private theorem stepSym_add_forwardPeriod (t : ℕ) (n q : ℤ) :
    stepSym (n + amusicalForwardPeriod (t + 1) n * q) = stepSym n := by
  unfold stepSym
  simp only [amusicalForwardPeriod]
  split_ifs <;> simp_all [Int.add_emod, Int.mul_emod]

private theorem stepSym_iterate_add_forwardPeriod (t : ℕ) (n q : ℤ) :
    ∀ i < t, stepSym (amusical^[i] (n + amusicalForwardPeriod t n * q)) =
      stepSym (amusical^[i] n) := by
  induction t generalizing n q with
  | zero => simp
  | succ t ih =>
      intro i hi
      by_cases hi0 : i = 0
      · subst i
        simpa using stepSym_add_forwardPeriod t n q
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
        have hstep : amusical (n + amusicalForwardPeriod (t + 1) n * q) =
            amusical n + amusicalForwardPeriod t (amusical n) * (3 * q) := by
          rw [show amusicalForwardPeriod (t + 1) n =
            (if n % 2 = 0 then 2 else 4) * amusicalForwardPeriod t (amusical n) by
              rfl]
          by_cases hn : n % 2 = 0
          · have hnform : n = 2 * (n / 2) := by
              have := Int.mul_ediv_add_emod n 2
              omega
            rw [if_pos hn]
            conv_lhs => rw [show n + 2 * amusicalForwardPeriod t (amusical n) * q =
              2 * (n / 2 + amusicalForwardPeriod t (amusical n) * q) by
                linear_combination hnform]
            rw [amusical_two_mul]
            have hnimage : amusical n = 3 * (n / 2) := by
              conv_lhs => rw [hnform]
              rw [amusical_two_mul]
            rw [hnimage]
            ring
          · have hnodd : n % 2 = 1 := by omega
            have hmod : n % 4 = 1 ∨ n % 4 = 3 := by omega
            rw [if_neg hn]
            rcases hmod with hn1 | hn3
            · have hnform : n = 4 * (n / 4) + 1 := by
                have := Int.mul_ediv_add_emod n 4
                omega
              conv_lhs => rw [show n + 4 * amusicalForwardPeriod t (amusical n) * q =
                4 * (n / 4 + amusicalForwardPeriod t (amusical n) * q) + 1 by
                  linear_combination hnform]
              rw [amusical_four_mul_add_one]
              have hnimage : amusical n = 3 * (n / 4) + 1 := by
                conv_lhs => rw [hnform]
                rw [amusical_four_mul_add_one]
              rw [hnimage]
              ring
            · have hnform : n = 4 * (n / 4) + 3 := by
                have := Int.mul_ediv_add_emod n 4
                omega
              conv_lhs => rw [show n + 4 * amusicalForwardPeriod t (amusical n) * q =
                4 * (n / 4 + amusicalForwardPeriod t (amusical n) * q) + 3 by
                  linear_combination hnform]
              rw [amusical_four_mul_add_three]
              have hnimage : amusical n = 3 * (n / 4) + 2 := by
                conv_lhs => rw [hnform]
                rw [amusical_four_mul_add_three]
              rw [hnimage]
              ring
        rw [hstep]
        exact ih (amusical n) (3 * q) j (by omega)

private theorem amusicalForwardPeriod_is_pow_two (t : ℕ) (m : ℤ) :
    ∃ e : ℕ, amusicalForwardPeriod t m = 2 ^ e := by
  induction t generalizing m with
  | zero => exact ⟨0, by simp [amusicalForwardPeriod]⟩
  | succ t ih =>
      simp only [amusicalForwardPeriod]
      obtain ⟨e, he⟩ := ih (amusical m)
      split
      · exact ⟨e + 1, by rw [he, pow_succ']⟩
      · exact ⟨e + 2, by rw [he, pow_add]; norm_num; ring⟩

/-- **Target.**  Every integer of period at most `12` lies on a known cycle.  Paper proof: on the
cylinder of its itinerary word `w`, a period-`p` point is `x_w = N_w / (2^e − 3^p)`, and
`|x_w| ≤ 483` for every word with `p ≤ 12` (`scripts/amusical/perbound.py`); then check
`|y| ≤ 483` by `decide +kernel`. -/
theorem amusical_periodic_mem (y : ℤ) (p : ℕ) (hp : 1 ≤ p) (hp12 : p ≤ 12)
    (h : amusical^[p] y = y) : |y| ∈ knownCycleMembers := by
  sorry

/-- **Target.**  Every finite word is the start of the forward itinerary of some integer (the
set of such integers is a class mod `2^e`, nonempty by the Chinese remainder theorem). -/
theorem exists_forward_itinerary (u : List (Fin 3)) :
    ∃ m : ℤ, ∀ j (hj : j < u.length), stepSym (amusical^[j] m) = u[j] := by
  induction u with
  | nil => exact ⟨0, by simp⟩
  | cons s u ih =>
      obtain ⟨m, hm⟩ := ih
      let P := amusicalForwardPeriod u.length m
      have hP3 : IsCoprime P (3 : ℤ) := by
        have hP2 : ∃ e : ℕ, P = 2 ^ e := by
          simpa only [P] using amusicalForwardPeriod_is_pow_two u.length m
        obtain ⟨e, he⟩ := hP2
        rw [he]
        exact (show IsCoprime (2 : ℤ) 3 from ⟨-1, 1, by norm_num⟩).pow_left
      obtain ⟨q, hq⟩ := exists_mul_modEq_of_isCoprime hP3.symm (d := (s : ℕ) - m)
      let y := m + P * q
      have hy : y % 3 = (s : ℕ) := by
        have hs : y ≡ (s : ℤ) [ZMOD 3] := by
          dsimp only [y]
          convert hq.add_right m using 1 <;> ring
        change y % 3 = (s : ℤ) % 3 at hs
        rw [hs]
        exact Int.emod_eq_of_lt (by omega) (by exact_mod_cast s.isLt)
      fin_cases s
      · refine ⟨2 * (y / 3), ?_⟩
        norm_num at hy
        intro j hj
        by_cases hj0 : j = 0
        · subst j
          apply Fin.ext
          norm_num [stepSym, Int.add_emod, Int.mul_emod]
        · obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
          have hi : i < u.length := by
            change i + 1 < u.length + 1 at hj
            omega
          rw [Function.iterate_succ_apply]
          have hyform : y = 3 * (y / 3) := by
            have := Int.mul_ediv_add_emod y 3
            omega
          rw [amusical_two_mul, ← hyform]
          rw [stepSym_iterate_add_forwardPeriod u.length m q i hi, hm i hi]
          simp
      · refine ⟨4 * (y / 3) + 1, ?_⟩
        norm_num at hy
        intro j hj
        by_cases hj0 : j = 0
        · subst j
          apply Fin.ext
          norm_num [stepSym, Int.add_emod, Int.mul_emod]
        · obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
          have hi : i < u.length := by
            change i + 1 < u.length + 1 at hj
            omega
          rw [Function.iterate_succ_apply]
          have hyform : y = 3 * (y / 3) + 1 := by
            have := Int.mul_ediv_add_emod y 3
            omega
          rw [amusical_four_mul_add_one, ← hyform]
          rw [stepSym_iterate_add_forwardPeriod u.length m q i hi, hm i hi]
          simp
      · refine ⟨4 * (y / 3) + 3, ?_⟩
        norm_num at hy
        intro j hj
        by_cases hj0 : j = 0
        · subst j
          apply Fin.ext
          norm_num [stepSym, Int.add_emod, Int.mul_emod]
        · obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
          have hi : i < u.length := by
            change i + 1 < u.length + 1 at hj
            omega
          rw [Function.iterate_succ_apply]
          have hyform : y = 3 * (y / 3) + 2 := by
            have := Int.mul_ediv_add_emod y 3
            omega
          rw [amusical_four_mul_add_three, ← hyform]
          rw [stepSym_iterate_add_forwardPeriod u.length m q i hi, hm i hi]
          simp

/-- **Target (Theorem W3).**  No bijective reversor of `U` has `stepSym (ι n)` determined by
`stepSym (U⁻¹ n)`, `stepSym n`, `stepSym (U n)`.  Paper proof: module docstring and
`KICKOFF-2026-10-13-amusical-w3.md`. -/
theorem no_window3_bijective_reversor (f : Fin 3 → Fin 3 → Fin 3 → Fin 3) {ι : ℤ → ℤ}
    (hrev : IsAmusicalReversor ι) (hbij : Function.Bijective ι)
    (hloc : ∀ n, stepSym (ι n) =
      f (stepSym (amusicalInv n)) (stepSym n) (stepSym (amusical n))) : False := by
  sorry

end CollatzMoonshot.Amusical
