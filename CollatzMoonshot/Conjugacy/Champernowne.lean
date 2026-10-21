/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.Ladder

/-!
# The Collatz–Champernowne sequence

Champernowne's constant `0.123456789101112…` is normal because the decimal expansions of
`1, 2, 3, …`, written in order, exhaust every block of each length at the right rate.  This
module writes the same object with **parity words in place of decimal expansions**: for
`C ≥ 1`, the sequence `𝒞_C = collatzChampernowne C` concatenates, for `n = 1, 2, 3, …`, the
first `C · size n` letters of the shortcut parity word `accWord n`, `size n` the bit length.
The letters of `n` at positions below `size n` are the **Terras range** (they determine
`n mod 2^(size n)`, `accWord_congr_mod`); the letters at and beyond `size n` depend on the
orbit, not on a residue.

* **Concatenation** (`cum`, `concat`, `concat_apply`): position `cum len n + i` of the
  concatenation of words of lengths `len` carries letter `i` of word `n`.  Everything is
  computable; the word index is a `Nat.find`.
* **`C = 1`** (`collatzChampernowne 1`): the word of `n` is its `size n`-letter Terras word.
  Normality is believed with no new Collatz input (`collatzChampernowne_one_normal`,
  confidence 85%): Champernowne's counting, with the within-stage order permuted by Terras's
  bijection.
* **`C ≥ 2`**: normality of `𝒞_C` is read as a **short-interval, beyond-Terras
  equidistribution** of the parity letters of `k`-bit integers, `ShortIntervalMixing C`.  The
  direction `ShortIntervalMixing C → Normal 𝒞_C` is frozen (`normal_of_shortIntervalMixing`,
  75%); the converse only returns an average over positions, so it is not stated.  The
  single-letter shadow is proved: `ShortIntervalMixing 2` implies the bias-decay conjecture
  C1 of `Ladder.lean` (`biasDecays_of_shortIntervalMixing`).
* **The threshold** `C* = 2 / (2 − log₂ 3) ≈ 4.82` (`threshold_bounds`: `4 < C* < 5`).  Under
  the stochastic model (Lagarias–Weiss 1992, Kontorovich–Lagarias 2009) the total stopping
  time of a typical `n` is `≈ C* · log₂ n`.  For `C > C*` a positive fraction of a typical word
  is the alternating tail `1010…` of the cycle `{1, 2}`, and `𝒞_C` is not normal: the
  alternating block of length `L` then has frequency bounded below independently of `L`
  (`EarlyArrival`, `not_normal_of_earlyArrival`, `ChampernowneNotNormalAboveThreshold`).  For
  `C < C*` the words are in flight and conjecturally mixing (`ChampernowneNormalBelowThreshold`).
* **The stop-at-`1` version** (`stopWordLen`, `collatzChampernowneStop`): each word runs to the
  first hit of `1`.  The definition's fallback branch is unused exactly when the Collatz
  conjecture holds, and normality (`ChampernowneStopNormal`) is the beyond-Terras mixing
  conjecture with the cycle tail cut off.

## The regimes

| `C` | word of a `k`-bit `n` | status |
|---|---|---|
| `1` | the `k` Terras letters | normal, believed (`collatzChampernowne_one_normal`, 85%) |
| `2 … 4` | `k` Terras letters, then `(C − 1) k` letters in flight | normal iff mixing; `normal_of_shortIntervalMixing` frozen (75%) |
| `≥ 5` | in flight, then the cycle tail `1010…` for a positive fraction | not normal, conditional on `EarlyArrival C` (`not_normal_of_earlyArrival`, 90%) |
| stop at `1` | `stopWordLen n` letters, no tail | `ChampernowneStopNormal` (65%) |

New (2026-10-21): the object is the Collatz analogue of Champernowne's constant.  As far as this
repo knows, neither the sequence nor the threshold phenomenon is in print.
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord

/-! ## Concatenating a sequence of words -/

/-- `cum len n = ∑ i < n, len i`: the position at which word `n` starts in the concatenation
of words of lengths `len 0, len 1, …`. -/
def cum (len : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => cum len n + len n

@[simp] theorem cum_zero (len : ℕ → ℕ) : cum len 0 = 0 := rfl

theorem cum_succ (len : ℕ → ℕ) (n : ℕ) : cum len (n + 1) = cum len n + len n := rfl

theorem cum_mono (len : ℕ → ℕ) : Monotone (cum len) :=
  monotone_nat_of_le_succ fun n => by rw [cum_succ]; exact Nat.le_add_right _ _

/-- With positive lengths the word starts are strictly increasing. -/
theorem cum_lt_succ (len : ℕ → ℕ) (hlen : ∀ n, 1 ≤ len n) (n : ℕ) :
    cum len n < cum len (n + 1) := by
  rw [cum_succ]; have := hlen n; omega

/-- With positive lengths, word `n` starts at position `≥ n`. -/
theorem le_cum (len : ℕ → ℕ) (hlen : ∀ n, 1 ≤ len n) : ∀ n, n ≤ cum len n
  | 0 => le_rfl
  | n + 1 => by rw [cum_succ]; have := hlen n; have := le_cum len hlen n; omega

/-- Every position falls before the end of some word (word `i` ends at `cum len (i+1) ≥ i+1`). -/
theorem exists_lt_cum_succ (len : ℕ → ℕ) (hlen : ∀ n, 1 ≤ len n) (i : ℕ) :
    ∃ n, i < cum len (n + 1) :=
  ⟨i, lt_of_lt_of_le (Nat.lt_succ_self i) (le_cum len hlen (i + 1))⟩

/-- The index of the word containing position `i`: the least `n` with `i < cum len (n+1)`. -/
def wordIndex (len : ℕ → ℕ) (hlen : ∀ n, 1 ≤ len n) (i : ℕ) : ℕ :=
  Nat.find (exists_lt_cum_succ len hlen i)

/-- **Concatenation.**  `concat len hlen word` is the infinite word `word 0 ∣ word 1 ∣ …` where
word `n` contributes its first `len n` letters: position `i` lies in word `wordIndex len hlen i`
at offset `i − cum len (wordIndex len hlen i)`. -/
def concat (len : ℕ → ℕ) (hlen : ∀ n, 1 ≤ len n) (word : ℕ → ℕ → Bool) : ℕ → Bool :=
  fun i => word (wordIndex len hlen i) (i - cum len (wordIndex len hlen i))

/-- Position `cum len n + i`, `i < len n`, lies in word `n`. -/
theorem wordIndex_eq (len : ℕ → ℕ) (hlen : ∀ n, 1 ≤ len n) (n i : ℕ) (hi : i < len n) :
    wordIndex len hlen (cum len n + i) = n := by
  rw [wordIndex, Nat.find_eq_iff]
  refine ⟨?_, fun m hm => ?_⟩
  · rw [cum_succ]; omega
  · rw [not_lt]
    exact (cum_mono len (Nat.succ_le_of_lt hm)).trans (Nat.le_add_right _ _)

/-- **The sanity theorem.**  Letter `i` of word `n` sits at position `cum len n + i`. -/
theorem concat_apply (len : ℕ → ℕ) (hlen : ∀ n, 1 ≤ len n) (word : ℕ → ℕ → Bool) (n i : ℕ)
    (hi : i < len n) : concat len hlen word (cum len n + i) = word n i := by
  simp only [concat, wordIndex_eq len hlen n i hi, Nat.add_sub_cancel_left]

/-! ## The Collatz–Champernowne sequence `𝒞_C` -/

/-- The word lengths of `collatzChampernowne C`: word `n` carries the integer `n + 1` and has
`max C 1 · size (n+1)` letters (`max C 1` keeps the lengths positive for `C = 0`; only `C ≥ 1`
is of interest). -/
def champLen (C n : ℕ) : ℕ := max C 1 * Nat.size (n + 1)

theorem one_le_champLen (C n : ℕ) : 1 ≤ champLen C n :=
  Nat.mul_pos (lt_of_lt_of_le one_pos (le_max_right C 1)) (Nat.size_pos.mpr n.succ_pos)

/-- **The Collatz–Champernowne sequence `𝒞_C`.**  For `n = 1, 2, 3, …` in order, the first
`C · size n` letters of the shortcut parity word `accWord n`.  For `C = 1` the word of `n` is
exactly its Terras word, the `size n` letters that determine `n mod 2^(size n)`. -/
def collatzChampernowne (C : ℕ) : ℕ → Bool :=
  concat (champLen C) (one_le_champLen C) fun n => accWord (n + 1)

/-- Letter `i` of the word of `n + 1` sits at position `cum (champLen C) n + i` of `𝒞_C`. -/
theorem collatzChampernowne_apply (C n i : ℕ) (hi : i < max C 1 * Nat.size (n + 1)) :
    collatzChampernowne C (cum (champLen C) n + i) = accWord (n + 1) i :=
  concat_apply _ _ _ n i hi

/-- Teeth test: `𝒞_1` starts `1 ∣ 01 ∣ 11 ∣ 001 ∣ …`; its second letter is the first letter of
the word of `2`, which is even. -/
theorem collatzChampernowne_one_one : collatzChampernowne 1 1 = false := by
  have h := collatzChampernowne_apply 1 1 0
    (Nat.mul_pos (by norm_num) (Nat.size_pos.mpr (by norm_num)))
  have hc : cum (champLen 1) 1 = 1 := by simp [cum_succ, champLen, Nat.size_one]
  rw [hc] at h
  simpa [accWord] using h

/-! ## The stop-at-`1` version -/

open Classical in
/-- The length of the word of `n` in `collatzChampernowneStop`: the first `t` with
`tstep^[t] n = 1` (at least `1`, so that `n = 1` still contributes a letter), with a fallback
of `1` when the orbit never reaches `1`.  The fallback branch is unused for every `n ≥ 1`
exactly when every positive integer reaches `1`, the Collatz conjecture
(`CollatzMoonshot.Conjecture`, read through the shortcut map). -/
noncomputable def stopWordLen (n : ℕ) : ℕ :=
  if h : ∃ t, tstep^[t] n = 1 then max 1 (Nat.find h) else 1

/-- On an orbit that reaches `1`, the word length is the first hitting time (at least `1`). -/
theorem stopWordLen_eq_of_reaches (n : ℕ) (h : ∃ t, tstep^[t] n = 1) :
    stopWordLen n = max 1 (Nat.find h) := by
  rw [stopWordLen, dif_pos h]

theorem one_le_stopWordLen (n : ℕ) : 1 ≤ stopWordLen n := by
  unfold stopWordLen; split_ifs <;> simp

/-- Teeth test: `3 → 5 → 8 → 4 → 2 → 1`, so the word of `3` has `5` letters. -/
theorem stopWordLen_three : stopWordLen 3 = 5 := by
  have h : ∃ t, tstep^[t] 3 = 1 := ⟨5, by decide⟩
  rw [stopWordLen_eq_of_reaches 3 h]
  have : Nat.find h = 5 := by rw [Nat.find_eq_iff]; decide
  rw [this]; omega

/-- **The stop-at-`1` Collatz–Champernowne sequence.**  For `n = 1, 2, 3, …` in order, the
parity word of `n` up to the first hit of `1`: the whole in-flight word, with the cycle tail
`1010…` cut off.  The sequence is well defined without the fallback of `stopWordLen` exactly
when the Collatz conjecture holds, so this is a binary sequence whose *definition* is the
Collatz conjecture and whose normality (`ChampernowneStopNormal`) is the beyond-Terras
mixing conjecture.  Each word of an `n ∉ {1, 2, 4}` ends in `000` (the orbit arrives through
`8 → 4 → 2 → 1`), which is `O(1 / log n)` of its letters. -/
noncomputable def collatzChampernowneStop : ℕ → Bool :=
  concat (fun n => stopWordLen (n + 1)) (fun n => one_le_stopWordLen (n + 1))
    fun n => accWord (n + 1)

/-! ## `C = 1`: Champernowne with the order permuted -/

/-- **Theorem (believed, confidence 85%).**  `𝒞_1` is normal.

*Stage `k`* is the `k`-bit integers `n ∈ [2^(k-1), 2^k)`; each contributes its `k`-letter
Terras word.  By `accWord_congr_mod`, letter `j` depends only on `n mod 2^(j+1)`, so the first
`k − 1` letters depend only on `n mod 2^(k-1)`, which runs over every residue once as `n` runs
over the stage; by Terras's bijection (`Qword_bijective` on `natDigits`) the `(k−1)`-letter
prefix runs bijectively over all `(k−1)`-words.  Hence every block of length `L` whose
`L` positions lie inside the first `k − 1` letters has frequency exactly `2^(−L)` over the
stage.  The last letter of each word is feedback-determined (`Qword_eq_xor` with top digit
`1`), and the `L` positions per word that touch it or straddle a word boundary are an
`L / k` fraction of the stage's letters.

A prefix ending `m ≤ 2^(k-1)` words into stage `k`: write `m` in binary and cut
`[2^(k-1), 2^(k-1) + m)` into aligned dyadic blocks, one of length `2^b` per set bit `b`.  In a
block of length `2^b`, `n mod 2^b` runs over every residue once, so the first `b` letters of
its words are exactly uniform; the remaining `k − b` letters per word, plus the `L` positions
touching them, are counted as determined.  Over all blocks the determined positions number at
most `2m (k − log₂ m + 2) + 2mL`, which is at most `(6 + 2L) · 2^(k-1)` on `m ≤ 2^(k-1)`,
while the prefix has length at least `(k − 2) · 2^(k-1)` (the stages below `k`).  So the
determined positions are `o(prefix length)` uniformly in `m`, and every block of length `L`
has frequency `2^(−L) + o(1)`: Champernowne's argument, with the within-stage order permuted
by the conjugacy.  No new Collatz input enters for `C = 1`. -/
theorem collatzChampernowne_one_normal : Normal (collatzChampernowne 1) := by
  sorry

/-! ## `C ≥ 2`: beyond-Terras short-interval mixing -/

/-- **Beyond-Terras short-interval equidistribution.**  For every block length `L`, pattern
`p`, and `δ > 0`, for all large `k`, every initial segment `[2^(k-1), 2^(k-1) + m)` of stage
`k`, and every position `t` with `k ≤ t` and `t + L ≤ C · k`, the number of `n` in the segment
whose letters at `t, …, t + L − 1` read `p` is `m / 2^L` up to `δ · 2^(k-1)`.  In words: the
letters past the bit length, over every initial segment of a dyadic stage, are jointly uniform
with error `o(2^k)`, uniformly in the segment.  For `C = 1` the condition is vacuous.

Evidence (2026-10-21, `experiments/conjugacy/profile.py 20 40`, over `[0, 2^20)`): the
single-letter bias `|2 P(letter t = 1) − 1|` is below `0.012` for positions `t ∈ [k, 2k]`,
and reaches `0.03`–`0.05` by position `3k`, where a quarter of the starts below `2^k` have already
reached the cycle `{1, 2}` and the starts still in flight show a survivorship bias toward odd
letters of the same size.  The first beyond-range letter has bias `≍ 2^(−k/2)` (`bias j` and
`BiasDecays` in `Ladder.lean`; the measured `+0.00099` at `k = 20` is `2^(−10)`).  Whether the
biases at fixed `t / k < C*` vanish as `k → ∞` is the content of the conjecture; `k = 20` is
too small to separate the `O(√k)` arrival fluctuations from a genuine bias. -/
def ShortIntervalMixing (C : ℕ) : Prop :=
  ∀ (L : ℕ) (p : Fin L → Bool) (δ : ℝ), 0 < δ → ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ m : ℕ, m ≤ 2 ^ (k - 1) →
    ∀ t : ℕ, k ≤ t → t + L ≤ C * k →
      |(((Finset.Ico (2 ^ (k - 1)) (2 ^ (k - 1) + m)).filter
          fun n => ∀ s : Fin L, accWord n (t + s) = p s).card : ℝ) - (m : ℝ) / 2 ^ L| ≤
        δ * 2 ^ (k - 1)

/-- **Theorem (believed, confidence 75%).**  Short-interval mixing makes `𝒞_C` normal.

The in-range letters (positions `t` with `t + L ≤ k − 1` in a word of stage `k`) are counted
exactly as in `collatzChampernowne_one_normal`, by the dyadic decomposition of the partial
stage.  For the beyond-range positions `k ≤ t ≤ C k − L`, apply the hypothesis to the partial
stage `[2^(k-1), 2^(k-1) + m)` as a whole, with the same `m` at which the prefix is cut: each
such `t` contributes `m / 2^L ± δ 2^(k-1)` occurrences, so over the `≤ C k` positions the
error is `≤ δ C k 2^(k-1)`, against a prefix of length `≥ C (k − 2) 2^(k-1)`; stages below the
threshold `K` of the hypothesis are finitely many.  The positions per word that straddle
`k − 1` or the word end are `2L`, a `2L / (C k)` fraction.  Then `δ → 0`.

What most needs checking: the hypothesis is used *uniformly in `m`*, since the prefix may be
cut anywhere inside a stage; without that uniformity the partial stage is uncontrolled and the
block frequencies could oscillate within a stage.  The converse (normality implies mixing)
yields only that the average over `t ∈ [k, C k)` of the discrepancies vanishes, not each `t`,
which is why only this direction is frozen. -/
theorem normal_of_shortIntervalMixing (C : ℕ) (hC : 1 ≤ C) (h : ShortIntervalMixing C) :
    Normal (collatzChampernowne C) := by
  sorry

/-! ## The edge to the bias conjecture C1 -/

/-- Mixing to a longer horizon is mixing to a shorter one: the hypothesis for `C'` covers every
position the hypothesis for `C ≤ C'` asks about. -/
theorem shortIntervalMixing_mono {C C' : ℕ} (hCC' : C ≤ C') (h : ShortIntervalMixing C') :
    ShortIntervalMixing C := by
  intro L p δ hδ
  obtain ⟨K, hK⟩ := h L p δ hδ
  exact ⟨K, fun k hk m hm t ht htL =>
    hK k hk m hm t ht (htL.trans (Nat.mul_le_mul_right k hCC'))⟩

/-- The single-letter even pattern of `ShortIntervalMixing`, read as the parity of the iterate. -/
theorem filter_even_letter (s : Finset ℕ) (t : ℕ) :
    (s.filter fun n => ∀ j : Fin 1, accWord n (t + j) = false) =
      s.filter fun n => tstep^[t] n % 2 = 0 := by
  apply Finset.filter_congr
  intro n _
  simp only [Fin.forall_fin_one, Fin.val_zero, add_zero, accWord, decide_eq_false_iff_not]
  omega

/-- The `±1` sum over an interval is twice the even count minus the length. -/
theorem sum_Ico_sgn_eq (a m K : ℕ) :
    ∑ n ∈ Finset.Ico a (a + m), (if tstep^[K] n % 2 = 0 then (1 : ℝ) else -1) =
      2 * (((Finset.Ico a (a + m)).filter fun n => tstep^[K] n % 2 = 0).card : ℝ) - m := by
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one,
    mul_neg_one]
  have hc := Finset.card_filter_add_card_filter_not (s := Finset.Ico a (a + m))
    (fun n => tstep^[K] n % 2 = 0)
  rw [Nat.card_Ico, Nat.add_sub_cancel_left] at hc
  have hc' : ((((Finset.Ico a (a + m)).filter fun n => tstep^[K] n % 2 = 0).card : ℕ) : ℝ) +
      ((((Finset.Ico a (a + m)).filter fun n => ¬ tstep^[K] n % 2 = 0).card : ℕ) : ℝ) = m := by
    exact_mod_cast hc
  linarith

/-- A stage whose even count is within `δ · 2^i` of half has `±1` sum within `δ · 2^(i+1)` of
zero. -/
theorem stage_imbalance_le {δ : ℝ} {i K : ℕ}
    (h : |(((Finset.Ico (2 ^ i) (2 ^ i + 2 ^ i)).filter fun n => tstep^[K] n % 2 = 0).card : ℝ) -
      (2 : ℝ) ^ i / 2| ≤ δ * 2 ^ i) :
    |∑ n ∈ Finset.Ico (2 ^ i) (2 ^ (i + 1)), (if tstep^[K] n % 2 = 0 then (1 : ℝ) else -1)| ≤
      δ * 2 ^ (i + 1) := by
  have e : 2 ^ (i + 1) = 2 ^ i + 2 ^ i := by rw [pow_succ, mul_two]
  rw [e, sum_Ico_sgn_eq]
  push_cast
  rw [abs_le] at h ⊢
  rw [pow_succ]
  constructor <;> linarith [h.1, h.2]

/-- `[0, 2^K) = [0, 2^J) ∪ ⋃_{J ≤ i < K} [2^i, 2^(i+1))`, as a sum identity. -/
theorem sum_range_two_pow_split (f : ℕ → ℝ) {J K : ℕ} (hJK : J ≤ K) :
    ∑ r ∈ Finset.range (2 ^ K), f r =
      ∑ r ∈ Finset.range (2 ^ J), f r +
        ∑ i ∈ Finset.Ico J K, ∑ r ∈ Finset.Ico (2 ^ i) (2 ^ (i + 1)), f r := by
  induction K, hJK using Nat.le_induction with
  | base => simp
  | succ K hJK ih =>
    rw [Finset.sum_Ico_succ_top hJK, ← add_assoc, ← ih]
    simp only [Finset.range_eq_Ico]
    rw [Finset.sum_Ico_consecutive f (Nat.zero_le _)
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ K))]

theorem sum_range_two_pow_succ_le (K : ℕ) :
    ∑ i ∈ Finset.range K, (2 : ℝ) ^ (i + 1) ≤ 2 ^ (K + 1) := by
  induction K with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, pow_succ 2 (n + 1)]; linarith [ih]

theorem sum_Ico_two_pow_succ_le (J K : ℕ) :
    ∑ i ∈ Finset.Ico J K, (2 : ℝ) ^ (i + 1) ≤ 2 ^ (K + 1) :=
  (Finset.sum_le_sum_of_subset_of_nonneg
    (by rw [Finset.range_eq_Ico]; exact Finset.Ico_subset_Ico_left (Nat.zero_le _))
    (fun _ _ _ => by positivity)).trans (sum_range_two_pow_succ_le K)

theorem bias_cast_eq_sum (K : ℕ) :
    (bias K : ℝ) = ∑ r ∈ Finset.range (2 ^ K), (if tstep^[K] r % 2 = 0 then (1 : ℝ) else -1) := by
  simp [bias]

/-- **Edge: the Champernowne mixing hypothesis implies the decay conjecture.**  The bias
`bias K` over `[0, 2^K)` is the sum over dyadic stages `[2^(i-1), 2^i)` of the letter-`K`
imbalance; for `K/2 < i ≤ K` that letter lies in the beyond-range window `[i, 2i)` of the
`i`-bit integers and `ShortIntervalMixing 2` makes each stage's imbalance `o(2^i)`; the stages
`i ≤ K/2` carry at most `2^(K/2+1)` integers.  So `C1` (`BiasDecays`) is the single-letter,
full-stage shadow of the mixing hypothesis behind the normality of `𝒞_2`.  With
`shortIntervalMixing_mono`, every `ShortIntervalMixing C`, `C ≥ 2`, implies `BiasDecays`.

Proof: with `J = K / 2` and `K ≥ 2 K₀ + 2 M + 2`, every stage `[2^i, 2^(i+1))`, `J ≤ i < K`,
has `i + 1 ≥ K₀` and `K + 1 ≤ 2 (i + 1)`, so the hypothesis (pattern `[false]`, `t = K`,
`m = 2^i`) bounds its imbalance by `δ 2^(i+1)`; the stages below `J` contribute at most `2^J`
in absolute value.  Hence `|bias K| ≤ 2^J + δ 2^(K+1)`, and `2^J ≤ 2^K / 2^J ≤ 2^K / 2^M`. -/
theorem biasDecays_of_shortIntervalMixing (h : ShortIntervalMixing 2) : BiasDecays := by
  rw [BiasDecays, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K₀, hK₀⟩ := h 1 (fun _ => false) (ε / 4) (by positivity)
  obtain ⟨M, hM⟩ := exists_nat_gt (2 / ε)
  refine ⟨2 * K₀ + 2 * M + 2, fun K hK => ?_⟩
  have hKpos : (0 : ℝ) < 2 ^ K := by positivity
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hKpos, div_lt_iff₀ hKpos]
  set J := K / 2 with hJ
  -- the stage bound from the hypothesis
  have hstage : ∀ i ∈ Finset.Ico J K,
      |∑ n ∈ Finset.Ico (2 ^ i) (2 ^ (i + 1)), (if tstep^[K] n % 2 = 0 then (1 : ℝ) else -1)| ≤
        ε / 4 * 2 ^ (i + 1) := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    have h1 : K₀ ≤ i + 1 := by omega
    have h3 : K + 1 ≤ 2 * (i + 1) := by omega
    have := hK₀ (i + 1) h1 (2 ^ i) (by simp) K (by omega) h3
    simp only [Nat.add_sub_cancel, pow_one, filter_even_letter] at this
    push_cast at this
    exact stage_imbalance_le this
  -- the two pieces
  have hA : |∑ r ∈ Finset.range (2 ^ J), (if tstep^[K] r % 2 = 0 then (1 : ℝ) else -1)| ≤
      2 ^ J := by
    calc |∑ r ∈ Finset.range (2 ^ J), (if tstep^[K] r % 2 = 0 then (1 : ℝ) else -1)|
        ≤ ∑ r ∈ Finset.range (2 ^ J), |if tstep^[K] r % 2 = 0 then (1 : ℝ) else -1| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ r ∈ Finset.range (2 ^ J), (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro r _
          split_ifs <;> simp
      _ = 2 ^ J := by simp
  have hB : |∑ i ∈ Finset.Ico J K, ∑ n ∈ Finset.Ico (2 ^ i) (2 ^ (i + 1)),
      (if tstep^[K] n % 2 = 0 then (1 : ℝ) else -1)| ≤ ε / 4 * 2 ^ (K + 1) := by
    calc |∑ i ∈ Finset.Ico J K, ∑ n ∈ Finset.Ico (2 ^ i) (2 ^ (i + 1)),
          (if tstep^[K] n % 2 = 0 then (1 : ℝ) else -1)|
        ≤ ∑ i ∈ Finset.Ico J K, |∑ n ∈ Finset.Ico (2 ^ i) (2 ^ (i + 1)),
            (if tstep^[K] n % 2 = 0 then (1 : ℝ) else -1)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.Ico J K, ε / 4 * 2 ^ (i + 1) := Finset.sum_le_sum hstage
      _ = ε / 4 * ∑ i ∈ Finset.Ico J K, (2 : ℝ) ^ (i + 1) := by rw [Finset.mul_sum]
      _ ≤ ε / 4 * 2 ^ (K + 1) := by gcongr; exact sum_Ico_two_pow_succ_le J K
  have habs : |(bias K : ℝ)| ≤ 2 ^ J + ε / 4 * 2 ^ (K + 1) := by
    rw [bias_cast_eq_sum, sum_range_two_pow_split _ (Nat.div_le_self K 2)]
    exact (abs_add_le _ _).trans (add_le_add hA hB)
  -- the arithmetic: `2^J < ε 2^K / 2`
  have h2J : (2 : ℝ) ^ J * 2 ^ J ≤ 2 ^ K := by
    rw [← pow_add]; exact pow_le_pow_right₀ one_le_two (by omega)
  have hM2 : (2 : ℝ) ^ M ≤ 2 ^ J := pow_le_pow_right₀ one_le_two (by omega)
  have hMlt : (M : ℝ) < 2 ^ M := by exact_mod_cast Nat.lt_two_pow_self
  have hpos : (0 : ℝ) < 2 ^ J := by positivity
  have h1 : 2 / ε < 2 ^ J := by linarith
  have h2 : (2 : ℝ) < ε * 2 ^ J := by rwa [div_lt_iff₀' hε] at h1
  have h3 : 2 * 2 ^ J < ε * 2 ^ J * 2 ^ J := mul_lt_mul_of_pos_right h2 hpos
  have h4 : ε * (2 ^ J * 2 ^ J) ≤ ε * 2 ^ K := mul_le_mul_of_nonneg_left h2J hε.le
  rw [pow_succ] at habs
  linarith

/-! ## The threshold `C* = 2 / (2 − log₂ 3)` -/

theorem two_rpow_three_halves_sq : ((2 : ℝ) ^ ((3 : ℝ) / 2)) ^ (2 : ℕ) = 8 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have : (3 : ℝ) / 2 * ((2 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
  rw [this, Real.rpow_natCast]; norm_num

theorem two_rpow_eight_fifths_pow_five : ((2 : ℝ) ^ ((8 : ℝ) / 5)) ^ (5 : ℕ) = 256 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have : (8 : ℝ) / 5 * ((5 : ℕ) : ℝ) = ((8 : ℕ) : ℝ) := by norm_num
  rw [this, Real.rpow_natCast]; norm_num

/-- `2^(3/2) < 3`, i.e. `8 < 9`. -/
theorem two_rpow_three_halves_lt_three : (2 : ℝ) ^ ((3 : ℝ) / 2) < 3 := by
  have h0 : (0 : ℝ) ≤ 2 ^ ((3 : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  rw [← pow_lt_pow_iff_left₀ h0 (by norm_num : (0 : ℝ) ≤ 3) (by norm_num : (2 : ℕ) ≠ 0),
    two_rpow_three_halves_sq]
  norm_num

/-- `3 < 2^(8/5)`, i.e. `243 < 256`. -/
theorem three_lt_two_rpow_eight_fifths : (3 : ℝ) < 2 ^ ((8 : ℝ) / 5) := by
  have h0 : (0 : ℝ) ≤ 2 ^ ((8 : ℝ) / 5) := Real.rpow_nonneg (by norm_num) _
  rw [← pow_lt_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 3) h0 (by norm_num : (5 : ℕ) ≠ 0),
    two_rpow_eight_fifths_pow_five]
  norm_num

/-- **The threshold is strictly between `4` and `5`.**  `C* = 2 / (2 − log₂ 3) ≈ 4.819`, from
`3/2 < log₂ 3 < 8/5`. -/
theorem threshold_bounds :
    4 < 2 / (2 - Real.logb 2 3) ∧ 2 / (2 - Real.logb 2 3) < 5 := by
  have hlo : (3 : ℝ) / 2 < Real.logb 2 3 := by
    rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by norm_num)]
    exact two_rpow_three_halves_lt_three
  have hhi : Real.logb 2 3 < 8 / 5 := by
    rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by norm_num)]
    exact three_lt_two_rpow_eight_fifths
  have hpos : 0 < 2 - Real.logb 2 3 := by linarith
  constructor
  · rw [lt_div_iff₀ hpos]; linarith
  · rw [div_lt_iff₀ hpos]; linarith

/-- **Conjecture (the threshold, below).**  `𝒞_C` is normal for `1 ≤ C ≤ 4`.  Confidence 70%.

The stochastic model (Lagarias–Weiss 1992, *The 3x+1 problem: two stochastic models*;
Kontorovich–Lagarias 2009, *Stochastic models for the 3x+1 and 5x+1 problems*) has the
shortcut orbit of `n` multiply by `1/2` or `3/2` with equal probability, so `log₂` drifts by
`(log₂ 3 − 2) / 2` per step and the total stopping time of a typical `n` is
`≈ C* · log₂ n` with `C* = 2 / (2 − log₂ 3) ≈ 4.819` (`threshold_bounds`), with `O(√log n)`
fluctuations.  For `C ≤ 4 < C*` the fraction of stage `k` that has reached `1` by position
`C k` tends to `0`, so the words are in flight throughout, and the conjecture is that in-flight
letters mix (`ShortIntervalMixing C`); then `normal_of_shortIntervalMixing` applies
(`champernowneNormalBelowThreshold_of_shortIntervalMixing`). -/
def ChampernowneNormalBelowThreshold : Prop :=
  ∀ C, 1 ≤ C → C ≤ 4 → Normal (collatzChampernowne C)

theorem champernowneNormalBelowThreshold_of_shortIntervalMixing
    (h : ∀ C, 1 ≤ C → C ≤ 4 → ShortIntervalMixing C) : ChampernowneNormalBelowThreshold :=
  fun C h1 h4 => normal_of_shortIntervalMixing C h1 (h C h1 h4)

/-- **Early arrival at positive density.**  Some rate `r < C` and some density `ρ > 0` such
that, for all large `k`, at least `ρ · 2^(k-1)` of the `k`-bit integers reach `1` within `r k`
shortcut steps.  The stochastic model predicts this for every `C > C* ≈ 4.819` with `ρ → 1`
(take `C* < r < C`); it is open, since even "almost every `n` reaches `1`" is open: Tao 2019
(*Almost all orbits of the Collatz map attain almost bounded values*) gives almost-bounded
values in logarithmic density, not total stopping times. -/
def EarlyArrival (C : ℕ) : Prop :=
  ∃ r ρ : ℝ, r < C ∧ 0 < ρ ∧ ∀ᶠ k : ℕ in atTop,
    ρ * 2 ^ (k - 1) ≤
      (Set.ncard {n : ℕ | 2 ^ (k - 1) ≤ n ∧ n < 2 ^ k ∧
        ∃ t : ℕ, (t : ℝ) ≤ r * k ∧ tstep^[t] n = 1} : ℝ)

/-- **Theorem (believed, confidence 90%).**  Early arrival at positive density makes `𝒞_C`
non-normal, with no input about the in-flight letters.

Once `tstep^[t] n = 1` the letters from `t` on are the alternating tail `1010…` of the cycle
`1 → 2 → 1`.  For `n` in stage `k` with first hitting time `≤ r k`, the tail occupies the
last `≥ (C − r) k` of the word's `C k` letters, so the alternating block `(10)^(L/2)` (`L`
even) occurs at every other tail position: at least `((C − r) k − L) / 2` times in the word.
Over stage `k` this is at least `ρ 2^(k-1) ((C − r) k − L) / 2` occurrences among
`C k 2^(k-1)` letters, a density `≥ ρ (C − r) / (2C) − o(1)`.  A prefix cut `m` words into
stage `k` contains all the stages below `k`, which are at least half of its length up to
`o(1)`, so the lower density of the block along every prefix is at least
`ρ (C − r) / (4C) > 0`, a bound independent of `L`.  Normality would force the frequency
`2^(−L)`; take `L` even with `2^(−L) < ρ (C − r) / (4C)`.

The block `11`, which the brief of 2026-10-21 named, is weaker: its tail frequency is `0`, and
an in-flight `11`-density above `1/4` could compensate, so the `11` route needs in-flight
input as well; the alternating block needs none. -/
theorem not_normal_of_earlyArrival (C : ℕ) (h : EarlyArrival C) :
    ¬ Normal (collatzChampernowne C) := by
  sorry

/-- **Conjecture (the threshold, above).**  `𝒞_C` is not normal for `C ≥ 5`.  Confidence 80%.

This is the new phenomenon: Champernowne-type sequences of parity words change character at
`C* = 2 / (2 − log₂ 3) ≈ 4.819` (`threshold_bounds`).  Under the stochastic model the total
stopping time of a typical `k`-bit `n` is `C* k + O(√k)`, so for `C > C*` a density-one set of
each stage has the cycle tail `1010…` over a `(C − C*) / C` fraction of its word, and the
alternating block of each even length `L` has frequency `≥ (C − C*) / (2C) − o(1)` instead
of `2^(−L)` (`not_normal_of_earlyArrival`; under full in-flight mixing the block `11` has
frequency `C* / (4C) < 1/4` as well).  Conditional on `EarlyArrival C` for `C ≥ 5`
(`champernowneNotNormalAboveThreshold_of_earlyArrival`), which is the stopping-time
concentration at positive density, itself open: Tao 2019 gives almost-bounded values in
logarithmic density, not total stopping times.  The `80%` is the model's `C* < 5`
(`threshold_bounds`) plus the margin `5 − C* ≈ 0.18`, which `O(√k)` fluctuations do not
erase. -/
def ChampernowneNotNormalAboveThreshold : Prop :=
  ∀ C, 5 ≤ C → ¬ Normal (collatzChampernowne C)

theorem champernowneNotNormalAboveThreshold_of_earlyArrival
    (h : ∀ C, 5 ≤ C → EarlyArrival C) : ChampernowneNotNormalAboveThreshold :=
  fun C hC => not_normal_of_earlyArrival C (h C hC)

/-- **Conjecture.**  The stop-at-`1` sequence is normal.  Confidence 65%.

Each word is the in-flight parity word of `n` up to its first hit of `1`, of length
`≈ C* log₂ n` under the stochastic model: the `size n` Terras letters, then
`≈ (C* − 1) size n` beyond-range letters, and no cycle tail.  Normality is the beyond-Terras
mixing conjecture (`ShortIntervalMixing`) with the horizon at the stopping time instead of a
fixed multiple of the bit length.  The word of each `n ∉ {1, 2, 4}` ends in the forced block
`000` (arrival through `8 → 4 → 2 → 1`), an `O(1 / log n)` fraction, so the forced ending does
not obstruct.  Well-definedness without the fallback of `stopWordLen` is `IntegerRung`-adjacent:
it is the full Collatz conjecture, `stopWordLen_eq_of_reaches` being the branch that holds
on every orbit that reaches `1`. -/
def ChampernowneStopNormal : Prop := Normal collatzChampernowneStop

end CollatzMoonshot.Conjugacy
