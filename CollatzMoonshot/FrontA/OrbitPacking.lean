/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.FrontA.ParityReconstruction

/-!
# Orbit packing: a power saving for iterate-separated sets

This module formalizes the counting half of `RESEARCH-2026-09-22-packing-shadow.md`
(the mechanism is classical: M. V. P. Garcia and F. A. Tal, *A note on the generalized
3n+1 problem*, Acta Arithmetica 90 (1999), 245-250).

The statement proved here is purely combinatorial, with no divergence hypothesis:
if every shortcut iterate `tstep^[m]` is injective on a set `S` of naturals
(`IterateSeparated`), then `S` meets every aligned dyadic block
`[q·2^m, (q+1)·2^m)` in at most `(m+1)·3^⌊3m/5⌋ + 3^m/2^(⌊3m/5⌋+1)` elements,
which is `O(λ^m)` for `λ < 2`.

## The two halves

* **Good words** (`5·r ≤ 3m`, where `r` is the number of odd steps in the first `m`
  shortcut steps): the affine block identity `tstep_iterate_block` sends the whole
  residue class into an interval of `3^r` integers, so injectivity caps the count at
  `3^r` for each `r`.
* **Bad words** (`5·r > 3m`): these are exponentially rare among *all* residues, by the
  weighted count `weightSum_le` (`∑_{s<2^m} 2^(ones (traceWord s m)) ≤ 3^m`), which is
  proved from a one-step injection, not from the exact binomial count.

The threshold `3/5` sits in `(1/2, log₃ 2)`; the weight `2` then gives
`(1+2)/(2·2^(3/5)) < 1`.  No constant here is optimized.
-/

namespace CollatzMoonshot.FrontA.OrbitPacking

open CollatzMoonshot CollatzMoonshot.FrontB

/-! ## Translation invariance of the parity trace -/

/-- Adding a multiple of `2^m` does not change the length-`m` parity trace. -/
theorem traceWord_add_mul (m : ℕ) : ∀ a q : ℕ, traceWord (a + q * 2 ^ m) m = traceWord a m := by
  induction m with
  | zero => intro a q; rfl
  | succ k ih =>
    intro a q
    have hpow : (2 : ℕ) ^ (k + 1) = 2 ^ k * 2 := by ring
    have hpar : (a + q * 2 ^ (k + 1)) % 2 = a % 2 := by
      rw [hpow, ← Nat.mul_assoc]; simp
    rcases Nat.even_or_odd a with he | ho
    · have ha : a % 2 = 0 := Nat.even_iff.mp he
      have hA : (a + q * 2 ^ (k + 1)) % 2 = 0 := by rw [hpar, ha]
      have hts : tstep (a + q * 2 ^ (k + 1)) = tstep a + q * 2 ^ k := by
        have h1 : tstep (a + q * 2 ^ (k + 1)) = (a + q * 2 ^ (k + 1)) / 2 := by
          simp [tstep, hA]
        have h2 : tstep a = a / 2 := by simp [tstep, ha]
        rw [h1, h2, hpow, ← Nat.mul_assoc, Nat.add_mul_div_right _ _ (by norm_num)]
      rw [traceWord, traceWord, hpar, hts, ih (tstep a) q]
    · have ha : a % 2 = 1 := Nat.odd_iff.mp ho
      have hA : ¬ (a + q * 2 ^ (k + 1)) % 2 = 0 := by rw [hpar, ha]; norm_num
      have hts : tstep (a + q * 2 ^ (k + 1)) = tstep a + (3 * q) * 2 ^ k := by
        have h1 : tstep (a + q * 2 ^ (k + 1)) = (3 * (a + q * 2 ^ (k + 1)) + 1) / 2 := by
          simp [tstep, hA]
        have h2 : tstep a = (3 * a + 1) / 2 := by simp [tstep, ha]
        have h3 : 3 * (a + q * 2 ^ (k + 1)) + 1 = (3 * a + 1) + (3 * q * 2 ^ k) * 2 := by
          rw [hpow]; ring
        rw [h1, h2, h3, Nat.add_mul_div_right _ _ (by norm_num)]
      rw [traceWord, traceWord, hpar, hts, ih (tstep a) (3 * q)]

/-- The length-`m` parity trace only depends on the start modulo `2^m`. -/
theorem traceWord_mod (m a : ℕ) : traceWord (a % 2 ^ m) m = traceWord a m := by
  conv_rhs => rw [← Nat.div_add_mod a (2 ^ m), Nat.add_comm, Nat.mul_comm]
  exact (traceWord_add_mul m (a % 2 ^ m) (a / 2 ^ m)).symm

/-- **The aligned-block affine identity.**  Shifting the start by `q·2^m` shifts the
`m`-th shortcut iterate by exactly `q·3^r`, where `r` is the number of odd steps. -/
theorem tstep_iterate_block (m s q : ℕ) :
    tstep^[m] (s + q * 2 ^ m) = tstep^[m] s + q * 3 ^ ones (traceWord s m) := by
  have hpos : 0 < 2 ^ m := Nat.two_pow_pos m
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  have h2 := tstep_iterate_identity m s
  rw [tstep_iterate_identity, traceWord_add_mul m s q,
    show 2 ^ m * (tstep^[m] s + q * 3 ^ ones (traceWord s m))
      = 2 ^ m * tstep^[m] s + q * 3 ^ ones (traceWord s m) * 2 ^ m from by ring, h2]
  ring


/-! ## The weighted residue count -/

/-- Splitting a range of even length into its even and odd halves. -/
theorem sum_range_two_mul (f : ℕ → ℕ) (N : ℕ) :
    ∑ s ∈ Finset.range (2 * N), f s
      = ∑ t ∈ Finset.range N, (f (2 * t) + f (2 * t + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have h : 2 * (N + 1) = 2 * N + 1 + 1 := by ring
    rw [h, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

/-- The total weight `∑_{s<2^m} 2^(#odd steps of s in m steps)`.  The exact value is
`3^m` (each word of length `m` is realized exactly once); only `≤` is needed. -/
def weightSum (m : ℕ) : ℕ := ∑ s ∈ Finset.range (2 ^ m), 2 ^ ones (traceWord s m)

/-- **The weighted residue count.**  Odd-step-heavy residues are exponentially rare:
weighting each residue by `2^(number of odd steps)` still gives only `3^m` in total. -/
theorem weightSum_le (m : ℕ) : weightSum m ≤ 3 ^ m := by
  induction m with
  | zero => simp [weightSum, traceWord]
  | succ k ih =>
    have hsplit : weightSum (k + 1)
        = ∑ t ∈ Finset.range (2 ^ k),
            (2 ^ ones (traceWord (2 * t) (k + 1)) + 2 ^ ones (traceWord (2 * t + 1) (k + 1))) := by
      unfold weightSum
      rw [show (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k from by ring, sum_range_two_mul]
    have heven : ∀ t : ℕ, ones (traceWord (2 * t) (k + 1)) = ones (traceWord t k) := by
      intro t
      have h0 : (2 * t) % 2 = 0 := by omega
      have h1 : tstep (2 * t) = t := by simp [tstep, h0]
      have h2 : traceWord (2 * t) (k + 1) = false :: traceWord t k := by
        rw [traceWord, h1]; simp [h0]
      rw [h2]
      rfl
    have hodd : ∀ t : ℕ, ones (traceWord (2 * t + 1) (k + 1))
        = ones (traceWord ((3 * t + 2) % 2 ^ k) k) + 1 := by
      intro t
      have h0 : (2 * t + 1) % 2 = 1 := by omega
      have h1 : tstep (2 * t + 1) = 3 * t + 2 := by
        have hne : ¬ (2 * t + 1) % 2 = 0 := by omega
        simp only [tstep, if_neg hne]; omega
      have h2 : traceWord (2 * t + 1) (k + 1) = true :: traceWord (3 * t + 2) k := by
        rw [traceWord, h1]; simp [h0]
      rw [h2, traceWord_mod]
      rfl
    have hinj : ∀ a ∈ Finset.range (2 ^ k), ∀ b ∈ Finset.range (2 ^ k),
        (3 * a + 2) % 2 ^ k = (3 * b + 2) % 2 ^ k → a = b := by
      intro a ha b hb hab
      rw [Finset.mem_range] at ha hb
      have hmod : (3 * a + 2) ≡ (3 * b + 2) [MOD 2 ^ k] := hab
      have h3 : 3 * a ≡ 3 * b [MOD 2 ^ k] := Nat.ModEq.add_right_cancel' 2 hmod
      have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by decide)
      have hfin := Nat.ModEq.cancel_left_of_coprime hcop h3
      have ha' : a % 2 ^ k = a := Nat.mod_eq_of_lt ha
      have hb' : b % 2 ^ k = b := Nat.mod_eq_of_lt hb
      unfold Nat.ModEq at hfin
      omega
    have hsub : ∑ t ∈ Finset.range (2 ^ k), 2 ^ ones (traceWord ((3 * t + 2) % 2 ^ k) k)
        ≤ weightSum k := by
      have himg : ∑ t ∈ Finset.range (2 ^ k), 2 ^ ones (traceWord ((3 * t + 2) % 2 ^ k) k)
          = ∑ x ∈ (Finset.range (2 ^ k)).image (fun t => (3 * t + 2) % 2 ^ k),
              2 ^ ones (traceWord x k) :=
        (Finset.sum_image (f := fun x => 2 ^ ones (traceWord x k))
          (fun a ha b hb hab => hinj a (by simpa using ha) b (by simpa using hb) hab)).symm
      rw [himg]
      refine Finset.sum_le_sum_of_subset ?_
      intro x hx
      simp only [Finset.mem_image] at hx
      obtain ⟨t, _, rfl⟩ := hx
      exact Finset.mem_range.mpr (Nat.mod_lt _ (Nat.two_pow_pos k))
    rw [hsplit]
    simp only [heven, hodd, pow_succ]
    rw [Finset.sum_add_distrib]
    have hmul : ∑ t ∈ Finset.range (2 ^ k),
        2 ^ ones (traceWord ((3 * t + 2) % 2 ^ k) k) * 2
        = 2 * ∑ t ∈ Finset.range (2 ^ k),
            2 ^ ones (traceWord ((3 * t + 2) % 2 ^ k) k) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => Nat.mul_comm _ _)
    have hfirst : ∑ t ∈ Finset.range (2 ^ k), 2 ^ ones (traceWord t k) = weightSum k := rfl
    rw [hmul, hfirst]
    have : weightSum k + 2 * weightSum k ≤ 3 * 3 ^ k := by omega
    calc weightSum k + 2 * ∑ t ∈ Finset.range (2 ^ k),
            2 ^ ones (traceWord ((3 * t + 2) % 2 ^ k) k)
        ≤ weightSum k + 2 * weightSum k := by omega
      _ ≤ 3 * 3 ^ k := this
      _ = 3 ^ (k + 1) := by ring


/-! ## The packing bound -/

/-- Every shortcut iterate is injective on `S`.  This is the only hypothesis the packing
bound needs; for the value set of a divergent orbit it follows from time-injectivity. -/
def IterateSeparated (S : Set ℕ) : Prop := ∀ m : ℕ, Set.InjOn (tstep^[m]) S

theorem ones_le_length (v : List Bool) : ones v ≤ v.length := by
  induction v with
  | nil => simp
  | cons b t ih => cases b <;> simp [ones] <;> omega

variable {S : Set ℕ}

/-- **Fixed-word packing.**  Inside one aligned block, the elements of an
iterate-separated set whose parity word has exactly `r` odd steps all have their
`m`-th iterates in a single interval of `3^r` integers, so there are at most `3^r`. -/
theorem fiber_card_le (hS : IterateSeparated S) {m q r : ℕ} (B : Finset ℕ)
    (hBS : ∀ x ∈ B, x ∈ S) (hBI : ∀ x ∈ B, q * 2 ^ m ≤ x ∧ x < (q + 1) * 2 ^ m)
    (hBr : ∀ x ∈ B, ones (traceWord x m) = r) : B.card ≤ 3 ^ r := by
  have hmap : ∀ x ∈ B, tstep^[m] x ∈ Finset.Ico (q * 3 ^ r) (q * 3 ^ r + 3 ^ r) := by
    intro x hx
    obtain ⟨h1, h2⟩ := hBI x hx
    have hxs : x = (x - q * 2 ^ m) + q * 2 ^ m := by omega
    have hslt : x - q * 2 ^ m < 2 ^ m := by
      have hq : (q + 1) * 2 ^ m = q * 2 ^ m + 2 ^ m := by ring
      omega
    have htr : traceWord x m = traceWord (x - q * 2 ^ m) m := by
      conv_lhs => rw [hxs]
      exact traceWord_add_mul m _ q
    have hr : ones (traceWord (x - q * 2 ^ m) m) = r := by rw [← htr]; exact hBr x hx
    have hit : tstep^[m] x = tstep^[m] (x - q * 2 ^ m) + q * 3 ^ r := by
      conv_lhs => rw [hxs]
      rw [tstep_iterate_block, hr]
    have hlt : tstep^[m] (x - q * 2 ^ m) < 3 ^ r := by
      have h := tstep_iterate_lt_pow_ones hslt
      rwa [hr] at h
    rw [Finset.mem_Ico, hit]
    omega
  have hinj : Set.InjOn (tstep^[m]) B := by
    intro a ha b hb hab
    exact hS m (hBS a (by simpa using ha)) (hBS b (by simpa using hb)) hab
  have hle := Finset.card_le_card_of_injOn (tstep^[m]) hmap hinj
  simpa using hle

/-- **The aligned-block packing bound.**  An iterate-separated set meets the aligned
dyadic block `[q·2^m, (q+1)·2^m)` in at most `(m+1)·3^⌊3m/5⌋ + 3^m/2^(⌊3m/5⌋+1)`
elements.  Both terms are `O(λ^m)` with `λ < 2`, a genuine power saving over the
block length `2^m`. -/
theorem block_card_le (hS : IterateSeparated S) (m q : ℕ) (B : Finset ℕ)
    (hBS : ∀ x ∈ B, x ∈ S) (hBI : ∀ x ∈ B, q * 2 ^ m ≤ x ∧ x < (q + 1) * 2 ^ m) :
    B.card ≤ (m + 1) * 3 ^ (3 * m / 5) + 3 ^ m / 2 ^ (3 * m / 5 + 1) := by
  classical
  have hmaps : ∀ x ∈ B, ones (traceWord x m) ∈ Finset.range (m + 1) := by
    intro x _
    have h := ones_le_length (traceWord x m)
    rw [traceWord_length] at h
    exact Finset.mem_range.mpr (by omega)
  have hcard := Finset.card_eq_sum_card_fiberwise hmaps
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range (m + 1))
    (fun r => 5 * r ≤ 3 * m)
    (fun r => (B.filter (fun x => ones (traceWord x m) = r)).card)
  -- the good half
  have hgood : ∑ r ∈ (Finset.range (m + 1)).filter (fun r => 5 * r ≤ 3 * m),
      (B.filter (fun x => ones (traceWord x m) = r)).card ≤ (m + 1) * 3 ^ (3 * m / 5) := by
    have hstep1 : ∑ r ∈ (Finset.range (m + 1)).filter (fun r => 5 * r ≤ 3 * m),
        (B.filter (fun x => ones (traceWord x m) = r)).card
        ≤ ∑ _r ∈ (Finset.range (m + 1)).filter (fun r => 5 * r ≤ 3 * m),
            3 ^ (3 * m / 5) := by
      refine Finset.sum_le_sum ?_
      intro r hr
      rw [Finset.mem_filter] at hr
      refine le_trans (fiber_card_le hS (m := m) (q := q) (r := r) _ ?_ ?_ ?_) ?_
      · intro x hx; exact hBS x (Finset.mem_filter.mp hx).1
      · intro x hx; exact hBI x (Finset.mem_filter.mp hx).1
      · intro x hx; exact (Finset.mem_filter.mp hx).2
      · exact Nat.pow_le_pow_right (by norm_num)
          ((Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega))
    refine hstep1.trans ?_
    calc ∑ _r ∈ (Finset.range (m + 1)).filter (fun r => 5 * r ≤ 3 * m), 3 ^ (3 * m / 5)
        = ((Finset.range (m + 1)).filter (fun r => 5 * r ≤ 3 * m)).card * 3 ^ (3 * m / 5) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (m + 1) * 3 ^ (3 * m / 5) := by
          refine Nat.mul_le_mul_right _ ?_
          simpa using Finset.card_filter_le (Finset.range (m + 1)) _
  -- the bad half
  have hbadcard : (B.filter (fun x => ¬ 5 * ones (traceWord x m) ≤ 3 * m)).card
      * 2 ^ (3 * m / 5 + 1) ≤ 3 ^ m := by
    set Bb := B.filter (fun x => ¬ 5 * ones (traceWord x m) ≤ 3 * m) with hBb
    have hmem : ∀ x ∈ Bb, x - q * 2 ^ m < 2 ^ m
        ∧ ones (traceWord (x - q * 2 ^ m) m) = ones (traceWord x m) := by
      intro x hx
      have hxB := (Finset.mem_filter.mp hx).1
      obtain ⟨h1, h2⟩ := hBI x hxB
      have hq : (q + 1) * 2 ^ m = q * 2 ^ m + 2 ^ m := by ring
      refine ⟨by omega, ?_⟩
      have hxs : x = (x - q * 2 ^ m) + q * 2 ^ m := by omega
      conv_rhs => rw [hxs]
      rw [traceWord_add_mul]
    have hinjs : ∀ a ∈ Bb, ∀ b ∈ Bb, a - q * 2 ^ m = b - q * 2 ^ m → a = b := by
      intro a ha b hb hab
      have h1 := hBI a (Finset.mem_filter.mp ha).1
      have h2 := hBI b (Finset.mem_filter.mp hb).1
      omega
    have hcardim : (Bb.image (fun x => x - q * 2 ^ m)).card = Bb.card :=
      Finset.card_image_of_injOn (fun a ha b hb hab => hinjs a (by simpa using ha) b
        (by simpa using hb) hab)
    have hstep : Bb.card * 2 ^ (3 * m / 5 + 1)
        ≤ ∑ s ∈ Bb.image (fun x => x - q * 2 ^ m), 2 ^ ones (traceWord s m) := by
      have hconst : (Bb.image (fun x => x - q * 2 ^ m)).card * 2 ^ (3 * m / 5 + 1)
          = ∑ _s ∈ Bb.image (fun x => x - q * 2 ^ m), 2 ^ (3 * m / 5 + 1) := by
        rw [Finset.sum_const, smul_eq_mul]
      rw [← hcardim, hconst]
      refine Finset.sum_le_sum ?_
      intro s hs
      simp only [Finset.mem_image] at hs
      obtain ⟨x, hxBb, rfl⟩ := hs
      have hx2 := (Finset.mem_filter.mp hxBb).2
      have hone := (hmem x hxBb).2
      refine Nat.pow_le_pow_right (by norm_num) ?_
      rw [hone]
      have : 3 * m / 5 < ones (traceWord x m) :=
        (Nat.div_lt_iff_lt_mul (by norm_num)).mpr (by omega)
      omega
    refine le_trans hstep (le_trans ?_ (weightSum_le m))
    unfold weightSum
    refine Finset.sum_le_sum_of_subset ?_
    intro s hs
    simp only [Finset.mem_image] at hs
    obtain ⟨x, hxBb, rfl⟩ := hs
    exact Finset.mem_range.mpr (hmem x hxBb).1
  have hbad : ∑ r ∈ (Finset.range (m + 1)).filter (fun r => ¬ 5 * r ≤ 3 * m),
      (B.filter (fun x => ones (traceWord x m) = r)).card
      ≤ 3 ^ m / 2 ^ (3 * m / 5 + 1) := by
    have hEq : ∑ r ∈ (Finset.range (m + 1)).filter (fun r => ¬ 5 * r ≤ 3 * m),
        (B.filter (fun x => ones (traceWord x m) = r)).card
        = (B.filter (fun x => ¬ 5 * ones (traceWord x m) ≤ 3 * m)).card := by
      rw [Finset.card_eq_sum_card_fiberwise
        (f := fun x => ones (traceWord x m))
        (t := (Finset.range (m + 1)).filter (fun r => ¬ 5 * r ≤ 3 * m))
        (fun x hx => by
          simp only [Finset.mem_coe, Finset.mem_filter] at hx ⊢
          exact ⟨hmaps x hx.1, hx.2⟩)]
      refine Finset.sum_congr rfl ?_
      intro r hr
      rw [Finset.mem_filter] at hr
      congr 1
      ext x
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hx, hone⟩; exact ⟨⟨hx, by rw [hone]; exact hr.2⟩, hone⟩
      · rintro ⟨⟨hx, _⟩, hone⟩; exact ⟨hx, hone⟩
    rw [hEq]
    exact (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr hbadcard
  omega

end CollatzMoonshot.FrontA.OrbitPacking
