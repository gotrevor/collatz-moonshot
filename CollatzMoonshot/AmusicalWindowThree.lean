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

private def symbolBits (s : Fin 3) : ℕ :=
  if s = 0 then 1 else 2

private def symbolError (s : Fin 3) : ℤ :=
  if s = 1 then 1 else if s = 2 then -1 else 0

private def wordBits : List (Fin 3) → ℕ
  | [] => 0
  | s :: w => symbolBits s + wordBits w

private def wordNumerator : List (Fin 3) → ℤ
  | [] => 0
  | s :: w => 3 ^ w.length * symbolError s + 2 ^ symbolBits s * wordNumerator w

private def orbitWord : ℕ → ℤ → List (Fin 3)
  | 0, _ => []
  | p + 1, y => stepSym y :: orbitWord p (amusical y)

private theorem orbitWord_length (p : ℕ) (y : ℤ) : (orbitWord p y).length = p := by
  induction p generalizing y with
  | zero => simp [orbitWord]
  | succ p ih => simp [orbitWord, ih]

private theorem step_affine (x : ℤ) :
    (2 : ℤ) ^ symbolBits (stepSym x) * amusical x = 3 * x + symbolError (stepSym x) := by
  unfold stepSym symbolBits symbolError amusical
  split_ifs <;> norm_num <;> omega

private theorem iterate_affine (p : ℕ) (y : ℤ) :
    (2 : ℤ) ^ wordBits (orbitWord p y) * amusical^[p] y =
      3 ^ p * y + wordNumerator (orbitWord p y) := by
  induction p generalizing y with
  | zero => simp [orbitWord, wordBits, wordNumerator]
  | succ p ih =>
      simp only [orbitWord, wordBits, wordNumerator, Function.iterate_succ_apply]
      rw [pow_add, mul_assoc, ih]
      rw [orbitWord_length, pow_succ]
      have hs := step_affine y
      linear_combination (3 : ℤ) ^ p * hs

private theorem wordBits_bounds (w : List (Fin 3)) :
    w.length ≤ wordBits w ∧ wordBits w ≤ 2 * w.length := by
  induction w with
  | nil => simp [wordBits]
  | cons s w ih =>
      simp only [List.length_cons, wordBits]
      have hs : 1 ≤ symbolBits s ∧ symbolBits s ≤ 2 := by
        fin_cases s <;> decide
      omega

private theorem wordNumerator_abs_le (w : List (Fin 3)) :
    |wordNumerator w| ≤ (4 : ℤ) ^ w.length - 3 ^ w.length := by
  induction w with
  | nil => simp [wordNumerator]
  | cons s w ih =>
      have h34 : (3 : ℤ) ^ w.length ≤ 4 ^ w.length := by
        exact (pow_le_pow_left₀ (by norm_num : (0 : ℤ) ≤ 3)
          (by norm_num : (3 : ℤ) ≤ 4)) w.length
      have h4 : 0 ≤ (4 : ℤ) ^ w.length := pow_nonneg (by norm_num) _
      fin_cases s
      · simp [wordNumerator, symbolBits, symbolError]
        calc
          2 * |wordNumerator w| ≤ 2 * (4 ^ w.length - 3 ^ w.length) := by omega
          _ ≤ 4 ^ (w.length + 1) - 3 ^ (w.length + 1) := by
            rw [pow_succ, pow_succ]
            omega
      · simp [wordNumerator, symbolBits, symbolError]
        calc
          |3 ^ w.length + 4 * wordNumerator w| ≤
              |(3 : ℤ) ^ w.length| + |4 * wordNumerator w| := abs_add_le _ _
          _ = 3 ^ w.length + 4 * |wordNumerator w| := by
            rw [abs_of_nonneg (pow_nonneg (by norm_num) _), abs_mul]
            norm_num
          _ ≤ 3 ^ w.length + 4 * (4 ^ w.length - 3 ^ w.length) := by omega
          _ = 4 ^ (w.length + 1) - 3 ^ (w.length + 1) := by
            rw [pow_succ, pow_succ]
            ring
      · simp [wordNumerator, symbolBits, symbolError]
        calc
          |-(3 : ℤ) ^ w.length + 4 * wordNumerator w| ≤
              |-((3 : ℤ) ^ w.length)| + |4 * wordNumerator w| := abs_add_le _ _
          _ = 3 ^ w.length + 4 * |wordNumerator w| := by
            rw [abs_neg, abs_of_nonneg (pow_nonneg (by norm_num) _), abs_mul]
            norm_num
          _ ≤ 3 ^ w.length + 4 * (4 ^ w.length - 3 ^ w.length) := by omega
          _ = 4 ^ (w.length + 1) - 3 ^ (w.length + 1) := by
            rw [pow_succ, pow_succ]
            ring

private theorem wordNumerator_abs_lt_four_pow (w : List (Fin 3)) :
    |wordNumerator w| < (4 : ℤ) ^ w.length := by
  have h3 : 0 < (3 : ℤ) ^ w.length := pow_pos (by norm_num) _
  exact lt_of_le_of_lt (wordNumerator_abs_le w) (by omega)

-- The kernel evaluates 4,693 integers at twelve periods; the interval recursion exceeds the
-- default elaborator depth but does not enumerate itinerary words.
set_option maxRecDepth 10000 in
private theorem periodic_bounded_check :
    ∀ y : ↥(Finset.Icc (-2346 : ℤ) 2346), ∀ p : ↥(Finset.Icc 1 12),
      amusical^[p.1] y.1 = y.1 → |y.1| ∈ knownCycleMembers := by
  decide +kernel

/-- **Target.**  Every integer of period at most `12` lies on a known cycle.  Paper proof: on the
cylinder of its itinerary word `w`, a period-`p` point is `x_w = N_w / (2^e − 3^p)`, and
`|x_w| ≤ 483` for every word with `p ≤ 12` (`scripts/amusical/perbound.py`); then check
`|y| ≤ 483` by `decide +kernel`. -/
theorem amusical_periodic_mem (y : ℤ) (p : ℕ) (hp : 1 ≤ p) (hp12 : p ≤ 12)
    (h : amusical^[p] y = y) : |y| ∈ knownCycleMembers := by
  have hbits := wordBits_bounds (orbitWord p y)
  rw [orbitWord_length] at hbits
  have hN := wordNumerator_abs_lt_four_pow (orbitWord p y)
  rw [orbitWord_length, abs_lt] at hN
  have haff := iterate_affine p y
  rw [h] at haff
  let e := wordBits (orbitWord p y)
  change p ≤ e ∧ e ≤ 2 * p at hbits
  have he_lower : 1 ≤ e := by omega
  have he_upper : e ≤ 24 := by omega
  change -(4 : ℤ) ^ p < wordNumerator (orbitWord p y) ∧
    wordNumerator (orbitWord p y) < 4 ^ p at hN
  change (2 : ℤ) ^ e * y = 3 ^ p * y + wordNumerator (orbitWord p y) at haff
  have hy : -2346 ≤ y ∧ y ≤ 2346 := by
    constructor <;>
      interval_cases p <;> interval_cases e <;> norm_num at haff hN ⊢ <;> omega
  exact periodic_bounded_check ⟨y, Finset.mem_Icc.mpr hy⟩
    ⟨p, Finset.mem_Icc.mpr ⟨hp, hp12⟩⟩ h

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

private def IsWindowThreeOrphan (f : Fin 3 → Fin 3 → Fin 3 → Fin 3) {L : ℕ}
    (u : Fin L → Fin 3) : Prop :=
  ∀ s : Fin (L + 2) → Fin 3, ∃ j : Fin L,
    f (s ⟨j.val + 2, by omega⟩) (s ⟨j.val + 1, by omega⟩) (s ⟨j.val, by omega⟩) ≠ u j

private theorem orphan_forbids_surjective_reversor
    (f : Fin 3 → Fin 3 → Fin 3 → Fin 3) {ι : ℤ → ℤ}
    (hrev : IsAmusicalReversor ι) (hsurj : Function.Surjective ι)
    (hloc : ∀ n, stepSym (ι n) =
      f (stepSym (amusicalInv n)) (stepSym n) (stepSym (amusical n)))
    {L : ℕ} {u : Fin L → Fin 3} (hu : IsWindowThreeOrphan f u) : False := by
  let word := List.ofFn u
  obtain ⟨m, hm⟩ := exists_forward_itinerary word
  obtain ⟨n, rfl⟩ := hsurj m
  have hback (z : ℤ) : ι (amusicalInv z) = amusical (ι z) := by
    calc
      ι (amusicalInv z) = amusical (amusicalInv (ι (amusicalInv z))) :=
        (amusical_amusicalInv _).symm
      _ = amusical (ι (amusical (amusicalInv z))) := by rw [hrev]
      _ = amusical (ι z) := by rw [amusical_amusicalInv]
  have hiter : ∀ k z, ι (amusicalInv^[k] z) = amusical^[k] (ι z) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        intro z
        rw [Function.iterate_succ_apply', hback, ih]
        exact (Function.iterate_succ_apply' _ k _).symm
  let s : Fin (L + 2) → Fin 3 := fun k =>
    if hk : k.val = 0 then stepSym (amusical n)
    else stepSym (amusicalInv^[k.val - 1] n)
  obtain ⟨j, hj⟩ := hu s
  have hit : stepSym (amusical^[j.val] (ι n)) = u j := by
    simpa [word] using hm j.val (by simpa [word] using j.isLt)
  rw [← hiter j.val n, hloc] at hit
  have hs0 : s ⟨j.val, by omega⟩ =
      stepSym (amusical (amusicalInv^[j.val] n)) := by
    by_cases hj0 : j.val = 0
    · simp [s, hj0]
    · simp only [s, dif_neg hj0]
      have he : j.val = (j.val - 1) + 1 := by omega
      rw [he, Function.iterate_succ_apply']
      simp only [amusical_amusicalInv]
      congr 2
  have hs1 : s ⟨j.val + 1, by omega⟩ = stepSym (amusicalInv^[j.val] n) := by
    simp [s]
  have hs2 : s ⟨j.val + 2, by omega⟩ =
      stepSym (amusicalInv (amusicalInv^[j.val] n)) := by
    simp [s, Function.iterate_succ_apply']
  rw [hs0, hs1, hs2, hit] at hj
  exact hj rfl

private theorem reversor_iterate_forward {ι : ℤ → ℤ} (hrev : IsAmusicalReversor ι) :
    ∀ k n, ι (amusical^[k] n) = amusicalInv^[k] (ι n) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      intro n
      rw [Function.iterate_succ_apply', hrev, ih]
      exact (Function.iterate_succ_apply' _ k _).symm

private theorem reversor_iterate_backward {ι : ℤ → ℤ} (hrev : IsAmusicalReversor ι) :
    ∀ k n, ι (amusicalInv^[k] n) = amusical^[k] (ι n) := by
  have hback (n : ℤ) : ι (amusicalInv n) = amusical (ι n) := by
    calc
      ι (amusicalInv n) = amusical (amusicalInv (ι (amusicalInv n))) :=
        (amusical_amusicalInv _).symm
      _ = amusical (ι (amusical (amusicalInv n))) := by rw [hrev]
      _ = amusical (ι n) := by rw [amusical_amusicalInv]
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      intro n
      rw [Function.iterate_succ_apply', hback, ih]
      exact (Function.iterate_succ_apply' _ k _).symm

private def HasExactAmusicalPeriod (p : ℕ) (n : ℤ) : Prop :=
  amusical^[p] n = n ∧ ∀ q, 1 ≤ q → q < p → amusical^[q] n ≠ n

private theorem reversor_preserves_exact_period {ι : ℤ → ℤ}
    (hrev : IsAmusicalReversor ι) (hinj : Function.Injective ι) {p : ℕ} {n : ℤ}
    (hn : HasExactAmusicalPeriod p n) : HasExactAmusicalPeriod p (ι n) := by
  constructor
  · have hv : amusicalInv^[p] (ι n) = ι n := by
      rw [← reversor_iterate_forward hrev, hn.1]
    calc
      amusical^[p] (ι n) = amusical^[p] (amusicalInv^[p] (ι n)) := by rw [hv]
      _ = ι n := Function.LeftInverse.iterate amusical_amusicalInv p (ι n)
  · intro q hq hqp hi
    apply hn.2 q hq hqp
    apply hinj
    rw [reversor_iterate_forward hrev]
    have := congrArg (amusicalInv^[q]) hi
    rw [Function.LeftInverse.iterate amusicalInv_amusical q (ι n)] at this
    exact this.symm

private theorem reversor_image_mem_exactPeriodCandidates {ι : ℤ → ℤ}
    (hrev : IsAmusicalReversor ι) (hinj : Function.Injective ι) {p : ℕ} {n : ℤ}
    (hp : 1 ≤ p) (hp12 : p ≤ 12) (hn : HasExactAmusicalPeriod p n) :
    |ι n| ∈ knownCycleMembers ∧ HasExactAmusicalPeriod p (ι n) := by
  have himage := reversor_preserves_exact_period hrev hinj hn
  exact ⟨amusical_periodic_mem (ι n) p hp hp12 himage.1, himage⟩

/-- **Target (Theorem W3).**  No bijective reversor of `U` has `stepSym (ι n)` determined by
`stepSym (U⁻¹ n)`, `stepSym n`, `stepSym (U n)`.  Paper proof: module docstring and
`KICKOFF-2026-10-13-amusical-w3.md`. -/
theorem no_window3_bijective_reversor (f : Fin 3 → Fin 3 → Fin 3 → Fin 3) {ι : ℤ → ℤ}
    (hrev : IsAmusicalReversor ι) (hbij : Function.Bijective ι)
    (hloc : ∀ n, stepSym (ι n) =
      f (stepSym (amusicalInv n)) (stepSym n) (stepSym (amusical n))) : False := by
  sorry

end CollatzMoonshot.Amusical
