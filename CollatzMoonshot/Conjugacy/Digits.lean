/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.Ladder

/-!
# Digits: the digit–letter correlation matrix and the digit form of the bias

Two exact readings of the bias `bias j` of `Ladder.lean`, the correlation between the `j`-th
parity letter and the `j`-th binary digit.

* **Only the diagonal survives** (`corr_diag`, `corr_off`).  The correlation matrix
  `corr i j = Σ_r (−1)^{ε_i(r) ⊕ w_j(r)}` between the binary digit `ε_i` and the parity letter
  `w_j`, summed over one full period `r < 2^(max i j + 1)`, is diagonal: `corr j j = 2 · bias j`
  and `corr i j = 0` for `i ≠ j`.  Both are the lift identity: `+2^k` flips digit `k` and letter
  `k`, and nothing else.
* **Terras's bijection, as a theorem** (`onesSet_injOn`, `onesSet_surjOn`): `r ↦ onesSet r j`,
  the set of positions of the ones of the `j`-letter word of `r`, is a bijection of `[0, 2^j)`
  onto the subsets of `[0, j)`.  Injectivity is the left inverse `prefixInt_accWord` read off
  `Ladder.lean`; surjectivity is a count.
* **The digit form** (`bias_eq_one_add_digitSum`).  For `u ⊆ [0, j)` nonempty, with
  `N_u = wordNumer u = Σ_{d ∈ u} 3^{#(u ∩ (d, j))} 2^d` and `a = |u|`, the first beyond-Terras
  letter of the start `r_u` with word `u` is the **complement of the `j`-th 2-adic digit of
  `N_u / 3^a`** (`tstep_iterate_even_iff_padicDigit`), and
  `bias j = 1 + Σ_{u ≠ ∅} (−1)^{1 + digit_j(N_u / 3^a)}`.
  Kernel-checked for `j ≤ 4` (`bias_eq_one_add_digitSum_check_*`).

The digit form moves the bias from the dynamics to arithmetic: the 2-adic digits of `N / 3^a`
are the parities of the halving dynamics `t ↦ t · 2^{−1} mod 3^a`, i.e. the binary digits of
the real `N / 3^a` read backwards within each period.  `BiasPositive` becomes: among the
`2^j − 1` nonempty `u ⊆ [0, j)`, the `j`-th digit of `N_u / 3^a` is `1` more often than `0`
(`bias_pos_iff_digitSum_nonneg`; the count of terms is odd, so "at least as often" is
"strictly more often").
-/

namespace CollatzMoonshot.Conjugacy

open CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord

/-! ## Halving a period -/

/-- One full period `r < 2^(k+1)` is the lower half `r < 2^k` and its translate by `2^k`. -/
theorem sum_range_two_pow_succ {M : Type*} [AddCommMonoid M] (f : ℕ → M) (k : ℕ) :
    ∑ r ∈ Finset.range (2 ^ (k + 1)), f r =
      ∑ r ∈ Finset.range (2 ^ k), (f r + f (r + 2 ^ k)) := by
  rw [pow_succ, mul_two, Finset.sum_range_add, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun r _ => by rw [add_comm (2 ^ k) r]

/-- Digit `j` of a `j`-bit number is `0`. -/
theorem natDigits_of_lt {r j : ℕ} (hr : r < 2 ^ j) : natDigits r j = false := by
  simp [natDigits, Nat.div_eq_of_lt hr]

/-- Digit `j` of `r + 2^j` is `1` for a `j`-bit `r`. -/
theorem natDigits_add_two_pow_self {r j : ℕ} (hr : r < 2 ^ j) :
    natDigits (r + 2 ^ j) j = true := by
  have hpos : 0 < 2 ^ j := by positivity
  simp [natDigits, Nat.add_div_right _ hpos, Nat.div_eq_of_lt hr]

/-- A digit below `j` does not see `+ 2^j`. -/
theorem natDigits_add_two_pow_of_lt {i j : ℕ} (h : i < j) (r : ℕ) :
    natDigits (r + 2 ^ j) i = natDigits r i := by
  have hpos : 0 < 2 ^ i := by positivity
  obtain ⟨k, hk⟩ : ∃ k, j = i + 1 + k := ⟨j - (i + 1), by omega⟩
  have e' : 2 ^ j = 2 ^ k * 2 * 2 ^ i := by rw [hk]; ring
  simp only [natDigits, e', Nat.add_mul_div_right _ _ hpos, Nat.add_mul_mod_self_right]

/-- A letter below `i` does not see `+ 2^i`. -/
theorem accWord_add_two_pow_of_lt {i j : ℕ} (h : j < i) (r : ℕ) :
    accWord (r + 2 ^ i) j = accWord r j := by
  obtain ⟨k, hk⟩ : ∃ k, i = j + 1 + k := ⟨i - (j + 1), by omega⟩
  have e : 2 ^ i = 2 ^ k * 2 ^ (j + 1) := by rw [hk]; ring
  rw [e, accWord_add_mul_two_pow_succ]

/-! ## The digit–letter correlation matrix -/

/-- The correlation `Σ_r (−1)^{ε_i(r) ⊕ w_j(r)}` between binary digit `i` (`natDigits r i`) and
parity letter `j` (`accWord r j`), over one full period `r < 2^(max i j + 1)`. -/
def corr (i j : ℕ) : ℤ :=
  ∑ r ∈ Finset.range (2 ^ (max i j + 1)), (if natDigits r i = accWord r j then (1 : ℤ) else -1)

/-- **Only the diagonal survives (diagonal).**  `corr j j = 2 · bias j`: the `j`-th parity
letter is correlated with the `j`-th binary digit, with advantage `bias j / 2^j`.  Under
`+2^j` both the digit and the letter flip (`accWord_add_two_pow`), so the two halves of the
period contribute equally. -/
theorem corr_diag (j : ℕ) : corr j j = 2 * bias j := by
  unfold corr bias
  rw [max_self, sum_range_two_pow_succ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr' : r < 2 ^ j := Finset.mem_range.mp hr
  rw [natDigits_of_lt hr', natDigits_add_two_pow_self hr', accWord_add_two_pow]
  simp only [accWord]
  rcases Nat.mod_two_eq_zero_or_one (tstep^[j] r) with h | h <;> simp [h]

/-- **Only the diagonal survives (off-diagonal).**  `corr i j = 0` for `i ≠ j`: the `j`-th
letter is uncorrelated with every other digit.  For `i < j`, `+2^j` flips the letter and leaves
digit `i` alone; for `j < i`, `+2^i` flips digit `i` and leaves the letter alone
(`accWord_add_mul_two_pow_succ`).  Either way the two halves of the period cancel.

Together with `corr_diag`: `E[(−1)^{ε_i + w_j}] = δ_{ij} · bias j / 2^j`.  In the triangular
form `Qword ε j = ε j ^^ feedback ε j` this says the feedback `f_j` has Walsh coefficient
`f̂_j(∅) = bias j` at the empty set, and the Walsh spectrum of `w_j` is that of `f_j` shifted
by `{j}`. -/
theorem corr_off (i j : ℕ) (h : i ≠ j) : corr i j = 0 := by
  unfold corr
  rcases Nat.lt_or_gt_of_ne h with hij | hij
  · rw [max_eq_right hij.le, sum_range_two_pow_succ]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [natDigits_add_two_pow_of_lt hij, accWord_add_two_pow]
    rcases Bool.eq_false_or_eq_true (natDigits r i) with h1 | h1 <;>
      rcases Bool.eq_false_or_eq_true (accWord r j) with h2 | h2 <;> simp [h1, h2]
  · rw [max_eq_left hij.le, sum_range_two_pow_succ]
    refine Finset.sum_eq_zero fun r hr => ?_
    have hr' : r < 2 ^ i := Finset.mem_range.mp hr
    rw [natDigits_of_lt hr', natDigits_add_two_pow_self hr', accWord_add_two_pow_of_lt hij]
    rcases Bool.eq_false_or_eq_true (accWord r j) with h2 | h2 <;> simp [h2]

/-! ## Words as sets of positions -/

/-- The numerator `N_u = Σ_{d ∈ u} 3^{#{e ∈ u : d < e}} · 2^d` of the parity word with ones at
the positions `u`: the one at `d` is multiplied by `3` once for every later one.  For
`u = {d_0 < ⋯ < d_{a−1}}` this is `Σ_i 3^{a−1−i} 2^{d_i}`, the `numer` of `Words.lean`
(`wordNumer_onesSet`). -/
def wordNumer (u : Finset ℕ) : ℕ := ∑ d ∈ u, 3 ^ (u.filter (fun e => d < e)).card * 2 ^ d

/-- The `j`-th 2-adic digit of the rational `N / 3^a`: bit `j` of `N · 3^{−a} mod 2^(j+1)`
(`3` is a unit mod `2^(j+1)`). -/
def padicDigit (j N a : ℕ) : Bool :=
  decide ((((N : ZMod (2 ^ (j + 1))) * ((3 : ZMod (2 ^ (j + 1))) ^ a)⁻¹).val / 2 ^ j) % 2 = 1)

/-- The positions of the ones of the `j`-letter parity word of `r`. -/
def onesSet (r j : ℕ) : Finset ℕ := (Finset.range j).filter (fun i => accWord r i = true)

theorem mem_onesSet {r j i : ℕ} : i ∈ onesSet r j ↔ i < j ∧ accWord r i = true := by
  simp [onesSet]

theorem onesSet_subset_range (r j : ℕ) : ∀ d ∈ onesSet r j, d < j :=
  fun _ hd => (mem_onesSet.mp hd).1

theorem card_onesSet (r j : ℕ) : (onesSet r j).card = oddCount r j := by
  rw [onesSet, Finset.card_filter, oddCount_eq_sum]

theorem onesSet_succ (r j : ℕ) :
    onesSet r (j + 1) = if accWord r j then insert j (onesSet r j) else onesSet r j := by
  rw [onesSet, Finset.range_add_one, Finset.filter_insert]
  rfl

/-- The parity trace grows at the back by the next letter. -/
theorem traceWord_succ' (n : ℕ) : ∀ m, traceWord n (m + 1) = traceWord n m ++ [accWord n m] := by
  suffices h : ∀ m n, traceWord n (m + 1) = traceWord n m ++ [accWord n m] from fun m => h m n
  intro m
  induction m with
  | zero =>
    intro n
    simp [traceWord, accWord]
    exact decide_eq_decide.mpr Iff.rfl
  | succ k ih =>
    intro n
    rw [traceWord, ih (tstep n), traceWord]
    simp [accWord, Function.iterate_succ_apply]
    exact decide_eq_decide.mpr Iff.rfl

/-- Adding a new top position multiplies the numerator by `3` and adds `2^j`. -/
theorem wordNumer_insert {u : Finset ℕ} {j : ℕ} (hu : ∀ d ∈ u, d < j) :
    wordNumer (insert j u) = 3 * wordNumer u + 2 ^ j := by
  have hj : j ∉ u := fun h => lt_irrefl j (hu j h)
  have h1 : (insert j u).filter (fun e => j < e) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact lt_irrefl _
    · exact fun h => absurd (hu e he) (not_lt.mpr h.le)
  have h2 : ∀ d ∈ u, (insert j u).filter (fun e => d < e) = insert j (u.filter (fun e => d < e)) :=
    fun d hd => by rw [Finset.filter_insert, if_pos (hu d hd)]
  have h3 : ∀ d ∈ u, j ∉ u.filter (fun e => d < e) :=
    fun _ _ h => hj (Finset.mem_filter.mp h).1
  have h4 : ∑ d ∈ u, 3 ^ ((insert j u).filter (fun e => d < e)).card * 2 ^ d
      = ∑ d ∈ u, 3 * (3 ^ (u.filter (fun e => d < e)).card * 2 ^ d) := by
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [h2 d hd, Finset.card_insert_of_notMem (h3 d hd), pow_succ]
    ring
  unfold wordNumer
  rw [Finset.sum_insert hj, h1, Finset.card_empty, pow_zero, one_mul, h4, Finset.mul_sum]
  exact add_comm _ _

/-- `wordNumer` of the set of ones is the `numer` of the word. -/
theorem wordNumer_onesSet (r : ℕ) : ∀ j, wordNumer (onesSet r j) = numer (traceWord r j) := by
  intro j
  induction j with
  | zero => simp [onesSet, wordNumer, traceWord]
  | succ k ih =>
    rw [traceWord_succ', onesSet_succ]
    rcases Bool.eq_false_or_eq_true (accWord r k) with h | h
    · rw [h, if_pos rfl, wordNumer_insert (onesSet_subset_range r k), ih, numer_append_true,
        traceWord_length]
    · rw [h, if_neg Bool.false_ne_true, numer_append_false, ih]

/-! ## Terras's bijection -/

theorem prefixInt_congr {w w' : ℕ → Bool} :
    ∀ j, (∀ i < j, w i = w' i) → prefixInt w j = prefixInt w' j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    rw [prefixInt_succ, prefixInt_succ, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)),
      h k (Nat.lt_succ_self k)]

/-- **Terras, the left inverse.**  A `j`-bit start is recovered from its `j`-letter word. -/
theorem prefixInt_accWord {r j : ℕ} (hr : r < 2 ^ j) : prefixInt (accWord r) j = r := by
  rw [← Qword_natDigits, prefixInt_Qword, bitsToNat_natDigits, Nat.mod_eq_of_lt hr]

theorem tstep_iterate_zero_left (i : ℕ) : tstep^[i] 0 = 0 :=
  Function.iterate_fixed (by decide) i

theorem onesSet_zero_left (j : ℕ) : onesSet 0 j = ∅ := by
  simp [onesSet, accWord, tstep_iterate_zero_left]

theorem accWord_eq_of_onesSet_eq {r s j : ℕ} (h : onesSet r j = onesSet s j) {i : ℕ}
    (hi : i < j) : accWord r i = accWord s i := by
  have := Finset.ext_iff.mp h i
  simp only [mem_onesSet, hi, true_and] at this
  exact Bool.eq_iff_iff.mpr this

/-- **Terras's bijection, injectivity**: distinct `j`-bit starts have distinct `j`-letter
words. -/
theorem onesSet_injOn (j : ℕ) : Set.InjOn (fun r => onesSet r j) (Finset.range (2 ^ j)) := by
  intro r hr s hs h
  have hr' : r < 2 ^ j := Finset.mem_range.mp (Finset.mem_coe.mp hr)
  have hs' : s < 2 ^ j := Finset.mem_range.mp (Finset.mem_coe.mp hs)
  rw [← prefixInt_accWord hr', ← prefixInt_accWord hs']
  exact prefixInt_congr j fun i hi => accWord_eq_of_onesSet_eq h hi

theorem onesSet_mem_powerset (r j : ℕ) : onesSet r j ∈ (Finset.range j).powerset :=
  Finset.mem_powerset.mpr (Finset.filter_subset _ _)

/-- **Terras's bijection, surjectivity**: every `u ⊆ [0, j)` is the word of a `j`-bit start.
A count: the injection `onesSet · j` maps `2^j` starts into `2^j` subsets. -/
theorem onesSet_surjOn (j : ℕ) :
    Set.SurjOn (fun r => onesSet r j) (Finset.range (2 ^ j)) (Finset.range j).powerset :=
  Finset.surjOn_of_injOn_of_card_le _ (fun r _ => Finset.mem_coe.mpr (onesSet_mem_powerset r j))
    (onesSet_injOn j) (by rw [Finset.card_powerset, Finset.card_range, Finset.card_range])

/-- A nonzero `j`-bit start has a one somewhere in its word. -/
theorem onesSet_ne_empty {r j : ℕ} (hr : r < 2 ^ j) (hr0 : r ≠ 0) : onesSet r j ≠ ∅ := by
  intro h
  apply hr0
  exact onesSet_injOn j (Finset.mem_coe.mpr (Finset.mem_range.mpr hr))
    (Finset.mem_coe.mpr (Finset.mem_range.mpr (by positivity)))
    (by show onesSet r j = onesSet 0 j; rw [h, onesSet_zero_left])

/-! ## The beyond-Terras letter as a 2-adic digit -/

theorem three_pow_coprime_two_pow (a m : ℕ) : Nat.Coprime (3 ^ a) (2 ^ m) :=
  Nat.Coprime.pow _ _ (by decide)

/-- `S := N · 3^{−a} mod 2^(j+1)` solves `3^a · S ≡ N (mod 2^(j+1))`. -/
theorem three_pow_mul_val_modEq (j N a : ℕ) :
    3 ^ a * ((N : ZMod (2 ^ (j + 1))) * ((3 : ZMod (2 ^ (j + 1))) ^ a)⁻¹).val
      ≡ N [MOD 2 ^ (j + 1)] := by
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, Nat.cast_pow, ZMod.natCast_zmod_val]
  have h := ZMod.coe_mul_inv_eq_one (n := 2 ^ (j + 1)) (3 ^ a) (three_pow_coprime_two_pow a (j + 1))
  push_cast at h ⊢
  calc (3 : ZMod (2 ^ (j + 1))) ^ a * ((N : ZMod (2 ^ (j + 1))) * ((3 : ZMod (2 ^ (j + 1))) ^ a)⁻¹)
      = (N : ZMod (2 ^ (j + 1))) * ((3 : ZMod (2 ^ (j + 1))) ^ a * ((3 : ZMod (2 ^ (j + 1))) ^ a)⁻¹) := by
        ring
    _ = N := by rw [h, mul_one]

/-- **The beyond-Terras letter is a digit.**  For `0 < r < 2^j`, with `N = numer v` and
`a = ones v` for the `j`-letter word `v` of `r`, the `j`-th iterate `tstep^[j] r` is even iff the
`j`-th 2-adic digit of `N / 3^a` is `1`.

Proof.  Put `S = N · 3^{−a} mod 2^(j+1)`, so `3^a S ≡ N`.  The iterate identity
`2^j · tstep^[j] r = 3^a r + N` gives `2^j · tstep^[j] r ≡ 3^a (r + S) (mod 2^(j+1))`, so
`2^j ∣ r + S` (as `3^a` is odd).  Writing `S = 2^j s₁ + s₀` with `s₀ < 2^j`, the number
`r + s₀` is a positive multiple of `2^j` below `2^(j+1)`, hence equals `2^j`, so
`(r + S) / 2^j = s₁ + 1` and `tstep^[j] r ≡ 3^a (s₁ + 1) ≡ s₁ + 1 (mod 2)`. -/
theorem tstep_iterate_even_iff_padicDigit {j r : ℕ} (hr : r < 2 ^ j) (hr0 : r ≠ 0) :
    tstep^[j] r % 2 = 0 ↔ padicDigit j (numer (traceWord r j)) (oddCount r j) = true := by
  set a := oddCount r j with ha
  set N := numer (traceWord r j) with hN
  set T := tstep^[j] r with hT
  set S := ((N : ZMod (2 ^ (j + 1))) * ((3 : ZMod (2 ^ (j + 1))) ^ a)⁻¹).val with hS
  have hid : 2 ^ j * T = 3 ^ a * r + N := tstep_iterate_identity j r
  have hSlt : S < 2 ^ (j + 1) := ZMod.val_lt _
  have hinv : 3 ^ a * S ≡ N [MOD 2 ^ (j + 1)] := three_pow_mul_val_modEq j N a
  have hP : 0 < 2 ^ j := by positivity
  -- `2^j · T ≡ 3^a (r + S) (mod 2^(j+1))`
  have h1 : 2 ^ j * T ≡ 3 ^ a * (r + S) [MOD 2 ^ (j + 1)] := by
    rw [hid, mul_add]
    exact (Nat.ModEq.refl _).add hinv.symm
  -- hence `2^j ∣ r + S`
  have h2 : 2 ^ j ∣ 3 ^ a * (r + S) := by
    have hd : 2 ^ j ∣ 2 ^ (j + 1) := pow_dvd_pow 2 (Nat.le_succ j)
    exact Nat.modEq_zero_iff_dvd.mp
      (((Nat.ModEq.of_dvd hd h1).symm).trans (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right _ _)))
  obtain ⟨q, hq⟩ : 2 ^ j ∣ r + S := (three_pow_coprime_two_pow a j).symm.dvd_of_dvd_mul_left h2
  -- `T ≡ 3^a q ≡ q (mod 2)`
  have h4 : T ≡ 3 ^ a * q [MOD 2] := by
    apply Nat.ModEq.mul_left_cancel' (c := 2 ^ j) hP.ne'
    rw [← pow_succ]
    calc 2 ^ j * T ≡ 3 ^ a * (r + S) [MOD 2 ^ (j + 1)] := h1
      _ = 2 ^ j * (3 ^ a * q) := by rw [hq]; ring
  have hTq : T % 2 = q % 2 := by
    have h4' : T % 2 = 3 ^ a * q % 2 := h4
    rw [h4', Nat.mul_mod, three_pow_mod_two, one_mul, Nat.mod_mod]
  -- `q = S / 2^j + 1`
  have hdm := Nat.div_add_mod S (2 ^ j)
  have hmod := Nat.mod_lt S hP
  set s₁ := S / 2 ^ j with hs₁
  set s₀ := S % 2 ^ j with hs₀
  have hdvd : 2 ^ j ∣ r + s₀ := by
    have : 2 ^ j ∣ 2 ^ j * s₁ + (r + s₀) := ⟨q, by omega⟩
    exact (Nat.dvd_add_right (dvd_mul_right _ _)).mp this
  obtain ⟨t, ht⟩ := hdvd
  have ht1 : t = 1 := by
    have hlt : 2 ^ j * t < 2 ^ j * 2 := by rw [← ht]; omega
    have hpos : 0 < 2 ^ j * t := by rw [← ht]; omega
    have h2' := Nat.lt_of_mul_lt_mul_left hlt
    rcases t with _ | _ | t
    · simp at hpos
    · rfl
    · omega
  have hq' : q = s₁ + 1 := by
    apply Nat.eq_of_mul_eq_mul_left hP
    calc 2 ^ j * q = r + S := hq.symm
      _ = (r + s₀) + 2 ^ j * s₁ := by omega
      _ = 2 ^ j * 1 + 2 ^ j * s₁ := by rw [ht, ht1]
      _ = 2 ^ j * (s₁ + 1) := by ring
  have hdig : padicDigit j N a = decide (s₁ % 2 = 1) := rfl
  rw [hdig, decide_eq_true_iff, hTq, hq']
  omega

/-! ## The digit form of the bias -/

/-- `Σ_{∅ ≠ u ⊆ [0, j)} (−1)^{1 + digit_j(N_u / 3^a)}`: `+1` when the `j`-th 2-adic digit of
`N_u / 3^{|u|}` is `1`, `−1` when it is `0`. -/
def digitSum (j : ℕ) : ℤ :=
  ∑ u ∈ (Finset.range j).powerset.filter (fun u => u.Nonempty),
    (if padicDigit j (wordNumer u) u.card then (1 : ℤ) else -1)

/-- **The digit form.**  `bias j = 1 + Σ_{∅ ≠ u ⊆ [0, j)} (−1)^{1 + digit_j(N_u / 3^{|u|})}`.

The first beyond-Terras letter of `r_u` is the complement of the `j`-th 2-adic digit of
`Σ_{i<a} 2^{d_i} / 3^{i+1} = N_u / 3^a` (`tstep_iterate_even_iff_padicDigit`); the `1` is the
start `r = 0`, whose word is empty and whose iterate `0` is even.  `BiasPositive` ⟺ among the
nonempty `u ⊆ [0, j)`, that digit is `1` strictly more often than `0`
(`bias_pos_iff_digitSum_nonneg`, and the number of terms `2^j − 1` is odd).

The 2-adic digits of `N / 3^a` are the parities of the halving dynamics `t ↦ t · 2^{−1} mod 3^a`,
i.e. the binary digits of the real `N / 3^a` read backwards within each period: the
beyond-Terras parity is a binary digit of a fraction with denominator `3^a`, averaged over the
structured set of numerators `N_u`.

Proof: reindex `bias j` along Terras's bijection `r ↦ onesSet r j` (`onesSet_injOn`,
`onesSet_surjOn`), translate `numer`/`oddCount` to `wordNumer`/`card` (`wordNumer_onesSet`,
`card_onesSet`), apply the digit lemma to each `r ≠ 0`, and peel off `u = ∅`. -/
theorem bias_eq_one_add_digitSum (j : ℕ) : bias j = 1 + digitSum j := by
  have hre : bias j = ∑ u ∈ (Finset.range j).powerset,
      (if u = ∅ then (1 : ℤ) else if padicDigit j (wordNumer u) u.card then 1 else -1) := by
    unfold bias
    refine Finset.sum_nbij (fun r => onesSet r j) (fun r _ => onesSet_mem_powerset r j)
      (onesSet_injOn j) (onesSet_surjOn j) fun r hr => ?_
    have hr' : r < 2 ^ j := Finset.mem_range.mp hr
    by_cases hr0 : r = 0
    · subst hr0
      rw [onesSet_zero_left, if_pos rfl, if_pos (by rw [tstep_iterate_zero_left])]
    · rw [if_neg (onesSet_ne_empty hr' hr0), wordNumer_onesSet, card_onesSet]
      rcases Nat.mod_two_eq_zero_or_one (tstep^[j] r) with h | h
      · rw [if_pos h, if_pos ((tstep_iterate_even_iff_padicDigit hr' hr0).mp h)]
      · rw [if_neg (by omega), if_neg]
        intro hd
        have := (tstep_iterate_even_iff_padicDigit hr' hr0).mpr hd
        omega
  have hempty : (Finset.range j).powerset.filter (fun u => ¬ u.Nonempty) = {∅} := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.not_nonempty_iff_eq_empty,
      Finset.mem_singleton]
    constructor
    · exact fun h => h.2
    · rintro rfl
      exact ⟨Finset.empty_subset _, rfl⟩
  rw [hre, ← Finset.sum_filter_add_sum_filter_not _ (fun u => u.Nonempty), hempty,
    Finset.sum_singleton, if_pos rfl, add_comm]
  congr 1
  unfold digitSum
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [if_neg (Finset.nonempty_iff_ne_empty.mp (Finset.mem_filter.mp hu).2)]

/-- `BiasPositive` at `j` is a majority vote among the digits. -/
theorem bias_pos_iff_digitSum_nonneg (j : ℕ) : 0 < bias j ↔ 0 ≤ digitSum j := by
  rw [bias_eq_one_add_digitSum]; omega

/-! **Teeth.**  The digit form, kernel-evaluated on both sides for `j ≤ 4` (the right side
runs `ZMod` inverses through `Nat.xgcd`, which plain `decide` cannot unfold). -/

theorem bias_eq_one_add_digitSum_check_0 : bias 0 = 1 + digitSum 0 := by decide +kernel
theorem bias_eq_one_add_digitSum_check_1 : bias 1 = 1 + digitSum 1 := by decide +kernel
theorem bias_eq_one_add_digitSum_check_2 : bias 2 = 1 + digitSum 2 := by decide +kernel
theorem bias_eq_one_add_digitSum_check_3 : bias 3 = 1 + digitSum 3 := by decide +kernel
theorem bias_eq_one_add_digitSum_check_4 : bias 4 = 1 + digitSum 4 := by decide +kernel

/-- The values themselves: `digitSum j = bias j − 1`. -/
theorem digitSum_three : digitSum 3 = 5 := by decide +kernel
theorem digitSum_four : digitSum 4 = 5 := by decide +kernel

end CollatzMoonshot.Conjugacy
