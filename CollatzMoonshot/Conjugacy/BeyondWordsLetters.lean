/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.BeyondWords

/-!
# Beyond-Terras words, letter form (2026-11-04)

`BeyondWordsUniform` is stated through residues: `T^j r mod 2^K` is asymptotically uniform.  The
letter form: for every binary word `w` of length `K`, the proportion of `j`-bit starts whose
parity letters `j, j+1, …, j+K−1` spell `w` tends to `2^{−K}`.

The bridge is Terras's bijection at finite length: `prefixInt w K` (Ladder.lean) is a `K`-bit
integer whose first `K` parity letters are `w` (`accWord_prefixInt`), and the first `K` letters
determine `m mod 2^K` (`mod_two_pow_eq_prefixInt_iff`, by counting: `c ↦ (accWord c i)_{i<K}` is a
surjection of `2^K` residues onto `2^K` words, hence injective).  So the word count is
`beyondCount j K (prefixInt w K)` (`beyondWordCount_eq`).
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord

/-- The number of `j`-bit starts whose beyond-Terras word of length `K` is `w`: the parity
letters of `T^j r, …, T^{j+K−1} r` are `w 0, …, w (K−1)`. -/
def beyondWordCount (j K : ℕ) (w : ℕ → Bool) : ℕ :=
  ((Finset.range (2 ^ j)).filter (fun r => ∀ i < K, accWord (tstep^[j] r) i = w i)).card

/-- The truncations of `prefixInt w` are the shorter `prefixInt`s. -/
theorem prefixInt_mod_two_pow (w : ℕ → Bool) {i K : ℕ} (h : i ≤ K) :
    prefixInt w K % 2 ^ i = prefixInt w i := by
  induction K, h using Nat.le_induction with
  | base => exact Nat.mod_eq_of_lt (prefixInt_lt w i)
  | succ K hiK ih =>
    rw [prefixInt_succ]
    split_ifs
    · rw [show 2 ^ K = 2 ^ i * 2 ^ (K - i) by rw [← pow_add, Nat.add_sub_of_le hiK],
        Nat.add_mul_mod_self_left, ih]
    · rw [add_zero, ih]

/-- **Terras at finite length (existence).**  `prefixInt w K` has first `K` letters `w`. -/
theorem accWord_prefixInt (w : ℕ → Bool) {i K : ℕ} (h : i < K) :
    accWord (prefixInt w K) i = w i := by
  have hc : prefixInt w K % 2 ^ (i + 1) = prefixInt w (i + 1) % 2 ^ (i + 1) := by
    rw [prefixInt_mod_two_pow w (by omega : i + 1 ≤ K),
      Nat.mod_eq_of_lt (prefixInt_lt w (i + 1))]
  rw [accWord_congr_mod i hc]
  have hq := congrFun (Qword_Qinv w) i
  simpa only [Qword, bitsToNat_Qinv] using hq

/-- The first `K` letters of `m` are those of `m mod 2^K`. -/
theorem accWord_mod_two_pow (m : ℕ) {i K : ℕ} (h : i < K) :
    accWord (m % 2 ^ K) i = accWord m i := by
  apply accWord_congr_mod i
  rw [Nat.mod_mod_of_dvd m (Nat.pow_dvd_pow 2 (by omega : i + 1 ≤ K))]

/-- The first `K` letters as a map from residues mod `2^K` to words of length `K`. -/
def letterMap (K : ℕ) (c : Fin (2 ^ K)) : Fin K → Bool := fun i => accWord c i

/-- **Terras at finite length (bijection).**  Surjective by `accWord_prefixInt`; a surjection
between two sets of size `2^K` is injective. -/
theorem letterMap_injective (K : ℕ) : Function.Injective (letterMap K) := by
  have hsurj : Function.Surjective (letterMap K) := by
    intro v
    let w : ℕ → Bool := fun i => if h : i < K then v ⟨i, h⟩ else false
    refine ⟨⟨prefixInt w K, prefixInt_lt w K⟩, ?_⟩
    funext i
    simp only [letterMap]
    rw [accWord_prefixInt w i.isLt]
    simp [w, i.isLt]
  have hcard : Fintype.card (Fin (2 ^ K)) = Fintype.card (Fin K → Bool) := by simp
  exact ((Fintype.bijective_iff_surjective_and_card _).mpr ⟨hsurj, hcard⟩).1

/-- **Terras at finite length (uniqueness).**  `m` has first `K` letters `w` iff
`m ≡ prefixInt w K (mod 2^K)`. -/
theorem mod_two_pow_eq_prefixInt_iff (w : ℕ → Bool) (K m : ℕ) :
    (∀ i < K, accWord m i = w i) ↔ m % 2 ^ K = prefixInt w K := by
  constructor
  · intro hm
    have hinj := letterMap_injective K
    have heq : letterMap K ⟨m % 2 ^ K, Nat.mod_lt _ (by positivity)⟩ =
        letterMap K ⟨prefixInt w K, prefixInt_lt w K⟩ := by
      funext i
      simp only [letterMap]
      rw [accWord_mod_two_pow m i.isLt, hm i i.isLt, accWord_prefixInt w i.isLt]
    exact congrArg Fin.val (hinj heq)
  · intro hm i hi
    rw [← accWord_mod_two_pow m hi, hm, accWord_prefixInt w hi]

/-- The word count is a residue count. -/
theorem beyondWordCount_eq (j K : ℕ) (w : ℕ → Bool) :
    beyondWordCount j K w = beyondCount j K (prefixInt w K) := by
  unfold beyondWordCount beyondCount
  congr 1
  apply Finset.filter_congr
  intro r _
  exact mod_two_pow_eq_prefixInt_iff w K (tstep^[j] r)

/-- Teeth: of the `16` four-bit starts, `6` have beyond-Terras word `00`, matching
`beyondCount 4 2 0 = 6` (`T^4 r ≡ 0 mod 4`); the word `010` is the residue `2 mod 8`. -/
example : beyondWordCount 4 2 (fun _ => false) = 6 := by decide
example : beyondCount 4 2 0 = 6 := by decide
example : prefixInt (fun i => i == 1) 3 = 2 := by decide

/-- **Beyond-Terras words are uniform, letter form.**  For every binary word `w` of length `K`,
the proportion of `j`-bit starts whose parity letters `j, …, j+K−1` spell `w` tends to `2^{−K}`.
Unconditional. -/
theorem beyondWordCount_tendsto (K : ℕ) (w : ℕ → Bool) :
    Tendsto (fun j : ℕ => (beyondWordCount j K w : ℝ) / 2 ^ j) atTop (𝓝 (1 / 2 ^ K)) := by
  simp_rw [beyondWordCount_eq]
  exact beyondWordsUniform K (prefixInt w K) (prefixInt_lt w K)

end CollatzMoonshot.Conjugacy
