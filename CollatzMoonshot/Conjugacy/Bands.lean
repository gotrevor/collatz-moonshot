/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Conjugacy.Ladder
import CollatzMoonshot.Conjugacy.Recursion

/-!
# Odd-count bands of the bias

The bias `bias j = ∑_{r < 2^j} (−1)^(tstep^[j] r)` of `Ladder.lean` splits along the number of
odd steps `a = oddCount r j` among the first `j`:

  `biasBand j a = ∑_{r < 2^j, oddCount r j = a} (−1)^(tstep^[j] r)`,  `bias j = ∑_{a ≤ j} biasBand j a`
  (`sum_biasBand`).

* **Band sizes** (`card_band`): the band `{r < 2^j : oddCount r j = a}` has exactly
  `Nat.choose j a` elements.  This is Terras's bijection read through the Hamming weight (the
  `j`-letter parity word is a bijection of `[0, 2^j)` onto `{0,1}^j`), proved here as Pascal's
  rule: `r` and `r + 2^j` share their first `j` letters and differ in the `(j+1)`-st
  (`oddCount_add_two_pow`, `oddCount_add_two_pow_succ`), so each pair feeds one element to band
  `a` and one to band `a + 1` at level `j + 1`.
* **Exact small bands.**  `biasBand j 0 = 1`: the band is `{0}` (`oddCount_eq_zero_iff`: no odd
  step among `j` means `2^j ∣ r`).  `biasBand j j = 1`: the band is `{2^j − 1}`, whose `j`-th
  iterate is `3^j − 1`, even (`tstep_iterate_all_odd`).  `biasBand j 1 = j % 2`: the band has `j`
  elements, one per position of the odd step, with signs alternating in the position; proved
  through the front recursion.
* **The front recursion** (`biasBand_succ_succ`): the even starts `2s < 2^(j+1)` reproduce
  `biasBand j (a+1)` on the nose (`tstep (2s) = s`), and the odd starts `2s + 1` contribute the
  band-`a` bias over the shifted starts `3s + 2` (`biasBandShift`).  At `a = 0` the shifted band
  is a single start, `3s + 2 ∈ {2^j, 2^(j+1)}` according to `2^j mod 3` (`biasBandShift_zero`).
* **Inheritance** (`biasBand_succ_succ_inherit`): the band-wise form of the mod-3 recursion
  `bias_succ_leakClass` of `Recursion.lean`,
  `biasBand (m+1) (a+1) = biasBand m (a+1) + biasBand m a − 2 · biasBandClass m a (leakClass m)`,
  where `biasBandClass m a c` is the slice of band `a` on the residue class `c` mod 3 of the start.
  Band `a+1` at level `m+1` descends from bands `a+1` and `a` at level `m`: a Pascal recursion
  with a leak.
* **Frozen conjectures** from the numerics of 2026-10-21: `BandCoherence` (the inner bands of a
  level share a sign and each carries a bias of order the square root of its size) and
  `BiasQuarterPowerLaw` (what summing the band law over `a` would give for `bias j`).

## The numerics (2026-10-21, `experiments/conjugacy`)

Normalize each band by the square root of its size, `E/√N = biasBand j a / √(choose j a)`.  At
`j = 26` the bands `a = 2..24` read `13, 56, 160, 358, 560, 564, 393, 574, 131, 1752, −2454,
1456, 4440, 1866, −1333, 1500, 2167, 1210, 182, 28, 84, 24, 5` (21 positive, 2 negative), with
`E/√N` from `+0.7` to `+1.7` and the two negatives at `−0.8, −0.6`.  Across `j = 16..26` the
inner bands `2 ≤ a ≤ j − 2` are positive in 156 cases and negative in 41, with mean normalized
value `+0.40 .. +0.67` (rising slowly with `j`) and spread `≈ 0.6`.  So the positive sign of
`bias j` at these levels is a per-band phenomenon of size `κ · √(choose j a)`, `κ ≈ 0.5–0.65`, in
every odd-count class, not a bulk accident and not a small-`a` or cycle effect.
-/

namespace CollatzMoonshot.Conjugacy

open CollatzMoonshot.FrontB

/-! ## The bands -/

/-- The bias restricted to the band of `j`-bit starts with exactly `a` odd steps among the first
`j`: `∑_{r < 2^j, oddCount r j = a} (−1)^(tstep^[j] r)`. -/
def biasBand (j a : ℕ) : ℤ :=
  ∑ r ∈ (Finset.range (2 ^ j)).filter (fun r => oddCount r j = a),
    (if tstep^[j] r % 2 = 0 then (1 : ℤ) else -1)

private theorem ones_le_length (v : List Bool) : ones v ≤ v.length := by
  induction v with
  | nil => simp
  | cons b t ih => cases b <;> simp [ones] <;> omega

/-- The number of odd steps among the first `j` is at most `j`. -/
theorem oddCount_le (r j : ℕ) : oddCount r j ≤ j := by
  have h := ones_le_length (traceWord r j)
  rw [traceWord_length] at h
  exact h

/-- **The bands partition the bias.**  `bias j = ∑_{a ≤ j} biasBand j a`. -/
theorem sum_biasBand (j : ℕ) : ∑ a ∈ Finset.range (j + 1), biasBand j a = bias j := by
  unfold biasBand bias
  exact Finset.sum_fiberwise_of_maps_to
    (fun r _ => Finset.mem_range.2 (Nat.lt_succ_of_le (oddCount_le r j))) _

/-! ## Band sizes: Terras via Pascal -/

/-- The first `j` letters of `r + c · 2^j` are those of `r` (`accWord_add_mul_two_pow_succ`,
letter by letter). -/
theorem oddCount_add_mul_two_pow (r c j : ℕ) : oddCount (r + c * 2 ^ j) j = oddCount r j := by
  rw [oddCount_eq_sum, oddCount_eq_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi := Finset.mem_range.1 hi
  have hj : j = (j - (i + 1)) + (i + 1) := by omega
  have e : r + c * 2 ^ j = r + (c * 2 ^ (j - (i + 1))) * 2 ^ (i + 1) := by
    rw [mul_assoc, ← pow_add, ← hj]
  rw [e, accWord_add_mul_two_pow_succ]

/-- The first `j` letters of `r + 2^j` are those of `r`. -/
theorem oddCount_add_two_pow (r j : ℕ) : oddCount (r + 2 ^ j) j = oddCount r j := by
  simpa using oddCount_add_mul_two_pow r 1 j

/-- The parity of the `j`-th iterate flips under `+ 2^j` (because `3^a` is odd), in arithmetic
form. -/
theorem tstep_iterate_add_two_pow_mod_two (r j : ℕ) :
    tstep^[j] (r + 2 ^ j) % 2 = 1 - tstep^[j] r % 2 := by
  rw [tstep_iterate_add_two_pow]
  have := three_pow_mod_two (oddCount r j)
  omega

/-- The `(j+1)`-letter count of `r + 2^j`: the first `j` letters are those of `r`, the
`(j+1)`-st is flipped.  Together with `oddCount_succ'`, the pair `r`, `r + 2^j` lands in the
bands `oddCount r j` and `oddCount r j + 1` at level `j + 1`, one each. -/
theorem oddCount_add_two_pow_succ (r j : ℕ) :
    oddCount (r + 2 ^ j) (j + 1) = oddCount r j + (if tstep^[j] r % 2 = 1 then 0 else 1) := by
  rw [oddCount_succ', oddCount_add_two_pow, tstep_iterate_add_two_pow_mod_two]
  rcases Nat.mod_two_eq_zero_or_one (tstep^[j] r) with h | h <;> simp [h]

/-- **Pascal's rule for the bands.**  The indicator count of band `a` at level `j` is
`Nat.choose j a`: at level `j + 1` the pair `r`, `r + 2^j` contributes one to band `a` when
`oddCount r j = a` and one to band `a` when `oddCount r j + 1 = a`, whichever of the two has the
odd `(j+1)`-st letter. -/
theorem sum_ite_oddCount (j : ℕ) : ∀ a : ℕ,
    (∑ r ∈ Finset.range (2 ^ j), if oddCount r j = a then 1 else 0) = Nat.choose j a := by
  induction j with
  | zero =>
    intro a
    cases a <;> simp [oddCount_zero]
  | succ k ih =>
    intro a
    rw [pow_succ, mul_two, Finset.sum_range_add, ← Finset.sum_add_distrib]
    have key : ∀ r, ((if oddCount r (k + 1) = a then 1 else 0) +
        (if oddCount (2 ^ k + r) (k + 1) = a then 1 else 0) : ℕ) =
        (if oddCount r k = a then 1 else 0) + (if oddCount r k + 1 = a then 1 else 0) := by
      intro r
      rw [oddCount_succ', add_comm (2 ^ k) r, oddCount_add_two_pow_succ]
      rcases Nat.mod_two_eq_zero_or_one (tstep^[k] r) with h | h <;> simp only [h] <;>
        split_ifs <;> omega
    rw [Finset.sum_congr rfl (fun r _ => key r), Finset.sum_add_distrib, ih a]
    cases a with
    | zero => simp
    | succ a =>
      simp only [Nat.add_right_cancel_iff]
      rw [ih a, Nat.choose_succ_succ', add_comm]

/-- **Band sizes.**  The band `{r < 2^j : oddCount r j = a}` has exactly `Nat.choose j a`
elements: Terras's bijection of `[0, 2^j)` onto the words `{0,1}^j`, read through the Hamming
weight. -/
theorem card_band (j a : ℕ) :
    ((Finset.range (2 ^ j)).filter (fun r => oddCount r j = a)).card = Nat.choose j a := by
  rw [Finset.card_filter]
  exact sum_ite_oddCount j a

/-! ## Elementary helpers -/

theorem tstep_zero : tstep 0 = 0 := by decide

theorem tstep_iterate_zero (j : ℕ) : tstep^[j] 0 = 0 := Function.iterate_fixed tstep_zero j

theorem oddCount_zero_left (j : ℕ) : oddCount 0 j = 0 := by
  induction j with
  | zero => rfl
  | succ k ih => rw [oddCount_succ', ih, tstep_iterate_zero]; simp

/-- `2^j mod 3` alternates: `1` for even `j`, `2` for odd `j`. -/
theorem two_pow_mod_three_eq (j : ℕ) : 2 ^ j % 3 = if j % 2 = 0 then 1 else 2 := by
  induction j with
  | zero => simp
  | succ k ih => rw [pow_succ]; split_ifs at ih ⊢ <;> omega

/-! ## The band `a = 0` -/

/-- **No odd step means `j` halvings.**  `oddCount y j = 0 ↔ 2^j ∣ y`.  Forward: the iterate
identity `2^j · tstep^[j] y = 3^0 · y + numer v` with `numer v = 0` for an all-even word.
Backward: `traceWord_add_mul` from the start `0`. -/
theorem oddCount_eq_zero_iff (y j : ℕ) : oddCount y j = 0 ↔ 2 ^ j ∣ y := by
  constructor
  · intro h
    have hid := tstep_iterate_identity j y
    rw [show ones (traceWord y j) = 0 from h, numer_eq_zero_of_ones_eq_zero h, pow_zero, one_mul,
      add_zero] at hid
    exact ⟨_, hid.symm⟩
  · rintro ⟨t, rfl⟩
    rw [show 2 ^ j * t = 0 + t * 2 ^ j by ring, oddCount_add_mul_two_pow]
    exact oddCount_zero_left j

/-- The `j`-th iterate of `t · 2^j` is `t`: the lift identity from the start `0`. -/
theorem tstep_iterate_mul_two_pow (t j : ℕ) : tstep^[j] (t * 2 ^ j) = t := by
  have h := tstep_iterate_add_mul_two_pow j 0 t
  rwa [zero_add, tstep_iterate_zero, oddCount_zero_left, pow_zero, mul_one, zero_add] at h

/-- The band `a = 0` is `{0}`. -/
theorem band_zero_eq (j : ℕ) :
    (Finset.range (2 ^ j)).filter (fun r => oddCount r j = 0) = {0} := by
  ext r
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, oddCount_eq_zero_iff]
  constructor
  · rintro ⟨hr, hd⟩
    exact Nat.eq_zero_of_dvd_of_lt hd hr
  · rintro rfl
    exact ⟨Nat.two_pow_pos j, dvd_zero _⟩

/-- **The band `a = 0`.**  `biasBand j 0 = 1`: the only `j`-bit start with no odd step is `0`,
and its `j`-th iterate `0` is even. -/
theorem biasBand_zero (j : ℕ) : biasBand j 0 = 1 := by
  unfold biasBand
  rw [band_zero_eq, Finset.sum_singleton, tstep_iterate_zero]
  simp

/-! ## The band `a = j` -/

/-- **The all-odd orbit.**  If `r + 1 = 2^j · (m+1)` then the first `j` steps from `r` are all
odd and `tstep^[j] r + 1 = 3^j · (m+1)`.  Induction on `j`: `r = 2N − 1` is odd with
`tstep r = 3N − 1`, and `3N = 2^(j−1) · 3(m+1)`. -/
theorem tstep_iterate_all_odd (j : ℕ) : ∀ m r : ℕ, r + 1 = 2 ^ j * (m + 1) →
    tstep^[j] r + 1 = 3 ^ j * (m + 1) ∧ oddCount r j = j := by
  induction j with
  | zero =>
    intro m r h
    simp only [pow_zero, one_mul] at h
    refine ⟨?_, oddCount_zero r⟩
    simpa using h
  | succ k ih =>
    intro m r h
    have e : 2 ^ (k + 1) * (m + 1) = 2 * (2 ^ k * (m + 1)) := by ring
    have e3 : 2 ^ k * (3 * m + 2 + 1) = 3 * (2 ^ k * (m + 1)) := by ring
    rw [e] at h
    have hodd : r % 2 = 1 := by
      generalize 2 ^ k * (m + 1) = N at h
      omega
    have ht : tstep r + 1 = 2 ^ k * (3 * m + 2 + 1) := by
      rw [e3]
      have hts : tstep r = (3 * r + 1) / 2 := by
        unfold tstep
        rw [if_neg (by omega)]
      rw [hts]
      generalize 2 ^ k * (m + 1) = N at h
      omega
    obtain ⟨h1, h2⟩ := ih (3 * m + 2) (tstep r) ht
    refine ⟨?_, ?_⟩
    · rw [Function.iterate_succ_apply, h1]
      ring
    · rw [oddCount_succ, h2, if_pos hodd]

/-- `2^j − 1` lies in the band `a = j`. -/
theorem mem_band_top (j : ℕ) :
    2 ^ j - 1 ∈ (Finset.range (2 ^ j)).filter (fun r => oddCount r j = j) := by
  have hpos := Nat.two_pow_pos j
  obtain ⟨_, h2⟩ := tstep_iterate_all_odd j 0 (2 ^ j - 1) (by simp only [zero_add, mul_one]; omega)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, h2⟩

/-- **The band `a = j`.**  `biasBand j j = 1`: the band has `choose j j = 1` element, it is
`2^j − 1` (the all-ones Terras word), and `tstep^[j] (2^j − 1) = 3^j − 1` is even. -/
theorem biasBand_top (j : ℕ) : biasBand j j = 1 := by
  have hcard : ((Finset.range (2 ^ j)).filter (fun r => oddCount r j = j)).card = 1 := by
    rw [card_band, Nat.choose_self]
  obtain ⟨x, hx⟩ := Finset.card_eq_one.1 hcard
  have hmem := mem_band_top j
  rw [hx, Finset.mem_singleton] at hmem
  unfold biasBand
  rw [hx, Finset.sum_singleton, ← hmem]
  have hpos := Nat.two_pow_pos j
  obtain ⟨h1, _⟩ := tstep_iterate_all_odd j 0 (2 ^ j - 1) (by simp only [zero_add, mul_one]; omega)
  have h3 := three_pow_mod_two j
  simp only [zero_add, mul_one] at h1
  rw [if_pos (by omega)]

/-! ## The front recursion and the band `a = 1` -/

/-- An even start `2s` reproduces the orbit of `s` one step later: its `(j+1)`-letter count is
the `j`-letter count of `s`. -/
theorem oddCount_two_mul (s j : ℕ) : oddCount (2 * s) (j + 1) = oddCount s j := by
  rw [oddCount_succ, tstep_two_mul]
  simp

/-- An odd start `2s + 1` takes one odd step to `3s + 2`. -/
theorem oddCount_two_mul_add_one (s j : ℕ) :
    oddCount (2 * s + 1) (j + 1) = oddCount (3 * s + 2) j + 1 := by
  rw [oddCount_succ, tstep_two_mul_add_one, if_pos (by omega)]

theorem tstep_iterate_two_mul (s j : ℕ) : tstep^[j + 1] (2 * s) = tstep^[j] s := by
  rw [Function.iterate_succ_apply, tstep_two_mul]

theorem tstep_iterate_two_mul_add_one (s j : ℕ) :
    tstep^[j + 1] (2 * s + 1) = tstep^[j] (3 * s + 2) := by
  rw [Function.iterate_succ_apply, tstep_two_mul_add_one]

/-- The band-`a` bias over the shifted starts `3s + 2`, `s < 2^j`: the contribution of the odd
starts `2s + 1 < 2^(j+1)` to `biasBand (j+1) (a+1)`. -/
def biasBandShift (j a : ℕ) : ℤ :=
  ∑ s ∈ (Finset.range (2 ^ j)).filter (fun s => oddCount (3 * s + 2) j = a),
    (if tstep^[j] (3 * s + 2) % 2 = 0 then (1 : ℤ) else -1)

/-- **The front recursion.**  Splitting `range (2^(j+1))` into even and odd starts: the even half
is `biasBand j (a+1)` on the nose, the odd half is the shifted band `biasBandShift j a`. -/
theorem biasBand_succ_succ (j a : ℕ) :
    biasBand (j + 1) (a + 1) = biasBand j (a + 1) + biasBandShift j a := by
  unfold biasBand biasBandShift
  simp only [Finset.sum_filter]
  rw [pow_succ', sum_range_two_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  simp only [oddCount_two_mul, oddCount_two_mul_add_one, tstep_iterate_two_mul,
    tstep_iterate_two_mul_add_one, Nat.add_right_cancel_iff]

/-- **The shifted band `a = 0` is a single start.**  `oddCount (3s + 2) j = 0` means
`2^j ∣ 3s + 2`, and with `s < 2^j` the quotient is `1` or `2`; which one is forced by
`2^j mod 3`: for even `j` (`2^j ≡ 1`) it is `3s + 2 = 2^(j+1)`, whose `j`-th iterate `2` is even;
for odd `j` (`2^j ≡ 2`) it is `3s + 2 = 2^j`, whose `j`-th iterate `1` is odd. -/
theorem biasBandShift_zero (j : ℕ) : biasBandShift j 0 = if j % 2 = 0 then 1 else -1 := by
  have hmod := two_pow_mod_three_eq j
  have hpos := Nat.two_pow_pos j
  unfold biasBandShift
  rcases Nat.mod_two_eq_zero_or_one j with hj | hj
  · rw [if_pos hj] at hmod ⊢
    obtain ⟨s₀, hs₀⟩ : ∃ s₀, 3 * s₀ + 2 = 2 * 2 ^ j := ⟨(2 * 2 ^ j - 2) / 3, by omega⟩
    have hfilt : (Finset.range (2 ^ j)).filter (fun s => oddCount (3 * s + 2) j = 0) = {s₀} := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, oddCount_eq_zero_iff]
      constructor
      · rintro ⟨hs, c, hc⟩
        have hc3 : c < 3 := by
          by_contra hge
          have : 2 ^ j * 3 ≤ 2 ^ j * c := Nat.mul_le_mul_left _ (Nat.le_of_not_lt hge)
          omega
        interval_cases c <;> omega
      · rintro rfl
        exact ⟨by omega, 2, by omega⟩
    rw [hfilt, Finset.sum_singleton, hs₀, tstep_iterate_mul_two_pow]
    simp
  · rw [if_neg (by omega)] at hmod ⊢
    obtain ⟨s₀, hs₀⟩ : ∃ s₀, 3 * s₀ + 2 = 1 * 2 ^ j := ⟨(2 ^ j - 2) / 3, by omega⟩
    have hfilt : (Finset.range (2 ^ j)).filter (fun s => oddCount (3 * s + 2) j = 0) = {s₀} := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, oddCount_eq_zero_iff]
      constructor
      · rintro ⟨hs, c, hc⟩
        have hc3 : c < 3 := by
          by_contra hge
          have : 2 ^ j * 3 ≤ 2 ^ j * c := Nat.mul_le_mul_left _ (Nat.le_of_not_lt hge)
          omega
        interval_cases c <;> omega
      · rintro rfl
        exact ⟨by omega, 1, by omega⟩
    rw [hfilt, Finset.sum_singleton, hs₀, tstep_iterate_mul_two_pow]
    simp

/-- **The band `a = 1`.**  `biasBand j 1 = j % 2`.  By the front recursion
`biasBand (j+1) 1 = biasBand j 1 + biasBandShift j 0 = biasBand j 1 + (−1)^j`, from
`biasBand 0 1 = 0`.  Directly: the band has `j` elements, one per position `d` of the odd step;
the start is `2^d · m` with `3m + 1 = 2^(j−d) · ν`, `ν = tstep^[j] r ∈ {1, 2}`, and `ν = 1`
(sign `−1`) exactly when `j − d` is even, so the sum is
`#{d < j : j − d odd} − #{d < j : j − d even} = j % 2`. -/
theorem biasBand_one (j : ℕ) : biasBand j 1 = j % 2 := by
  induction j with
  | zero => decide
  | succ k ih =>
    rw [biasBand_succ_succ, ih, biasBandShift_zero]
    split_ifs with h <;> omega

/-! ## Inheritance: the band-wise mod-3 recursion -/

/-- The band `a = 0` is `{0}` at every level. -/
theorem biasBand_succ_zero (m : ℕ) : biasBand (m + 1) 0 = biasBand m 0 := by
  rw [biasBand_zero, biasBand_zero]

/-- The slice of band `a` on the residue class `c` mod 3 of the start:
`biasBandClass k a c = ∑_{y < 2^k, oddCount y k = a, y ≡ c (3)} (−1)^(tstep^[k] y)`. -/
def biasBandClass (k a c : ℕ) : ℤ :=
  ∑ y ∈ (Finset.range (2 ^ k)).filter (fun y => oddCount y k = a ∧ y % 3 = c),
    (if tstep^[k] y % 2 = 0 then (1 : ℤ) else -1)

/-- The three classes of a band add up to the band. -/
theorem sum_biasBandClass_classes (k a : ℕ) :
    biasBandClass k a 0 + biasBandClass k a 1 + biasBandClass k a 2 = biasBand k a := by
  unfold biasBandClass biasBand
  have h := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.range (2 ^ k)).filter (fun y => oddCount y k = a)) (t := Finset.range 3)
    (g := fun y => y % 3) (fun y _ => Finset.mem_range.2 (Nat.mod_lt _ (by norm_num)))
    (fun y => (if tstep^[k] y % 2 = 0 then (1 : ℤ) else -1))
  rw [← h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Finset.filter_filter]

/-- The slice, with the class filter applied first. -/
theorem biasBandClass_eq_filter_filter (k a c : ℕ) :
    biasBandClass k a c = ∑ y ∈ ((Finset.range (2 ^ k)).filter (fun y => y % 3 = c)).filter
      (fun y => oddCount y k = a), (if tstep^[k] y % 2 = 0 then (1 : ℤ) else -1) := by
  unfold biasBandClass
  rw [Finset.filter_filter]
  exact Finset.sum_congr (Finset.filter_congr (fun y _ => and_comm)) (fun _ _ => rfl)

/-- The bands of a class add up to the class bias `biasClass` of `Recursion.lean`. -/
theorem sum_biasBandClass_bands (k c : ℕ) :
    ∑ a ∈ Finset.range (k + 1), biasBandClass k a c = biasClass k c := by
  simp only [biasBandClass_eq_filter_filter]
  unfold biasClass
  exact Finset.sum_fiberwise_of_maps_to
    (fun y _ => Finset.mem_range.2 (Nat.lt_succ_of_le (oddCount_le y k))) _

/-- The shifted band, reindexed by the odd starts `3s + 2 < 3 · 2^m` (`bias_odd_half_reindex`,
restricted to the band). -/
theorem biasBandShift_reindex (m a : ℕ) :
    biasBandShift m a = ∑ y ∈ Finset.range (3 * 2 ^ m),
      (if y % 3 = 2 then
        (if oddCount y m = a then (if tstep^[m] y % 2 = 0 then (1 : ℤ) else -1) else 0) else 0) := by
  unfold biasBandShift
  rw [Finset.sum_filter]
  conv_rhs => rw [← Finset.sum_filter]
  apply Finset.sum_nbij' (fun s => 3 * s + 2) (fun y => y / 3)
  · intro s hs; simp only [Finset.mem_filter, Finset.mem_range] at hs ⊢; omega
  · intro y hy; simp only [Finset.mem_filter, Finset.mem_range] at hy ⊢; omega
  · intro s hs; simp only [Finset.mem_range] at hs; omega
  · intro y hy; simp only [Finset.mem_filter, Finset.mem_range] at hy; omega
  · intro s _; rfl

/-- **The shifted band is the band minus twice its leaking class.**  The odd starts `3s + 2`,
`s < 2^m`, are the starts `y < 3 · 2^m` with `y ≡ 2 (mod 3)`: three blocks of length `2^m`.  The
lift identity keeps the first `m` letters (`oddCount_add_two_pow`, `oddCount_add_mul_two_pow`)
and gives the blocks the signs `+, −, +` (`sign_add_two_pow`, `sign_add_two_mul_two_pow`), so the
sum is `biasBandClass m a 2 − biasBandClass m a c + biasBandClass m a c'` with `{2, c, c'}` the
three residues and `c = leakClass m`; by `sum_biasBandClass_classes` this is
`biasBand m a − 2 · biasBandClass m a c`. -/
theorem biasBandShift_eq (m a : ℕ) :
    biasBandShift m a = biasBand m a - 2 * biasBandClass m a (leakClass m) := by
  have hthree : 3 * 2 ^ m = 2 ^ m + 2 ^ m + 2 ^ m := by ring
  have hB1 : ∑ y ∈ Finset.range (2 ^ m),
      (if y % 3 = 2 then
        (if oddCount y m = a then (if tstep^[m] y % 2 = 0 then (1 : ℤ) else -1) else 0) else 0)
        = biasBandClass m a 2 := by
    rw [biasBandClass, Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases h1 : y % 3 = 2 <;> by_cases h2 : oddCount y m = a <;> simp [h1, h2]
  have hB2 : ∑ y ∈ Finset.range (2 ^ m),
      (if (2 ^ m + y) % 3 = 2 then
        (if oddCount (2 ^ m + y) m = a then
          (if tstep^[m] (2 ^ m + y) % 2 = 0 then (1 : ℤ) else -1) else 0) else 0)
        = -biasBandClass m a (leakClass m) := by
    rw [biasBandClass, Finset.sum_filter, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hc : (y + 2 ^ m) % 3 = 2 ↔ y % 3 = leakClass m := by unfold leakClass; omega
    rw [add_comm (2 ^ m) y, sign_add_two_pow, oddCount_add_two_pow]
    simp only [hc]
    by_cases h1 : y % 3 = leakClass m <;> by_cases h2 : oddCount y m = a <;> simp [h1, h2]
  have hB3 : ∑ y ∈ Finset.range (2 ^ m),
      (if (2 ^ m + 2 ^ m + y) % 3 = 2 then
        (if oddCount (2 ^ m + 2 ^ m + y) m = a then
          (if tstep^[m] (2 ^ m + 2 ^ m + y) % 2 = 0 then (1 : ℤ) else -1) else 0) else 0)
        = biasBandClass m a ((2 + 2 ^ m % 3) % 3) := by
    rw [biasBandClass, Finset.sum_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    have e : 2 ^ m + 2 ^ m + y = y + 2 * 2 ^ m := by ring
    have hc : (y + 2 * 2 ^ m) % 3 = 2 ↔ y % 3 = (2 + 2 ^ m % 3) % 3 := by omega
    rw [e, sign_add_two_mul_two_pow, oddCount_add_mul_two_pow]
    simp only [hc]
    by_cases h1 : y % 3 = (2 + 2 ^ m % 3) % 3 <;> by_cases h2 : oddCount y m = a <;>
      simp [h1, h2]
  rw [biasBandShift_reindex, hthree, Finset.sum_range_add, Finset.sum_range_add, hB1, hB2, hB3]
  have hadd := sum_biasBandClass_classes m a
  unfold leakClass
  rcases two_pow_mod_three m with h | h <;> rw [h] <;> norm_num <;> linarith

/-- **Inheritance.**  Band `a+1` at level `m+1` is the sum of bands `a+1` and `a` at level `m`,
minus twice the class-`leakClass m` slice of band `a`: a Pascal recursion with a leak, which is
why the bands of one level share a sign (they descend from common ancestors) for every map of
the family.  Summing over `a` (`sum_biasBand`, `sum_biasBandClass_bands`) recovers the mod-3
recursion `bias_succ_leakClass` of `Recursion.lean`. -/
theorem biasBand_succ_succ_inherit (m a : ℕ) :
    biasBand (m + 1) (a + 1) =
      biasBand m (a + 1) + biasBand m a - 2 * biasBandClass m a (leakClass m) := by
  rw [biasBand_succ_succ, biasBandShift_eq]
  ring

/-! ## Kernel checks: the teeth test of the definitions -/

theorem biasBand_one_check_1 : biasBand 1 1 = 1 := by decide
theorem biasBand_one_check_2 : biasBand 2 1 = 0 := by decide
theorem biasBand_one_check_3 : biasBand 3 1 = 1 := by decide
theorem biasBand_one_check_4 : biasBand 4 1 = 0 := by decide
theorem biasBand_one_check_5 : biasBand 5 1 = 1 := by decide
theorem biasBand_one_check_6 : biasBand 6 1 = 0 := by decide +kernel
theorem biasBand_one_check_7 : biasBand 7 1 = 1 := by decide +kernel

/-- The `j = 8` bands are `1, 0, 4, 8, 14, 8, −2, 0, 1` for `a = 0..8` (sum `34 = bias 8`). -/
theorem biasBand_eight_two : biasBand 8 2 = 4 := by decide +kernel
theorem biasBand_eight_four : biasBand 8 4 = 14 := by decide +kernel
theorem biasBand_eight_six : biasBand 8 6 = -2 := by decide +kernel

/-! ## Frozen conjectures -/

/-- **Conjecture C5 (band coherence).**  The inner bands `2 ≤ a ≤ j − 2` of a level share a
sign, and each carries a bias of order the square root of its size: summing the normalized bands
`biasBand j a / √(choose j a)` over `a` gives at least `κ · j`.  Evidence: the numerics in the
module docstring (`j = 16..26`: 156 positive inner bands against 41 negative, mean normalized
value `+0.40 .. +0.67`).

The lower bound `κ · j` as written is the *persistent-sign* reading.  The within-level coherence
itself looks generic: for `3x+5`, `3x+7`, `5x+1`, `7x+1` the bands of a level also share a sign,
but that sign wanders with `j` (`3x+5`: band mean `−0.65` at `j = 18`, `+0.24` at `j = 24`), and
`3x−1` mirrors `3x+1` exactly (`bias_j(3x−1) = 2 − bias_j(3x+1)`).  The generic reading is
`|∑_a biasBand j a / √(choose j a)| ≥ κ j` with a map-dependent, level-dependent sign.  The
mechanism is inheritance: with `E_{m,a} = biasBand m a` and `G_{m−1,a−1}(c)` the class-`c`
(mod 3) slice of band `a − 1`,

  `E_{m,a} = E_{m−1,a} + E_{m−1,a−1} − 2 · G_{m−1,a−1}(c_m)`,

a Pascal recursion with a leak; this is the theorem `biasBand_succ_succ_inherit` below.
Confidence 60%. -/
def BandCoherence : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ ∃ J : ℕ, ∀ j ≥ J,
    κ * (j : ℝ) ≤ ∑ a ∈ Finset.Icc 2 (j - 2), (biasBand j a : ℝ) / Real.sqrt (Nat.choose j a)

/-- **Conjecture C2c (quarter-power law).**  Summing the band law `κ √(choose j a)` over `a` gives
`bias j ≈ κ (2π j)^(1/4) 2^(j/2)`, so `bias j` would be of exact order `j^(1/4) · 2^(j/2)`.  This
is the refinement of `BiasSqrtLaw` and `BiasPositive` (`Ladder.lean`) suggested by the bands; if
the `j^(1/4)` growth is real it contradicts `BiasSqrtLaw` as stated.  The data to `j = 31` cannot
separate the two: `bias j / 2^(j/2)` reads `1.41` at `j = 16` and `1.72–1.80` at `j = 30, 31`.

Against it: the mod-3 recursion gives the normalized bias `b̃_m = bias m / 2^(m/2)` the form
`b̃_m = (4/3)/√2 · b̃_(m−1) + η_m` with `(4/3)/√2 ≈ 0.943`; the fitted innovations over
`j = 10..31` have mean `+0.14` and standard deviation `0.33`, and under the zero-mean null the 22
consecutive positive values have probability about `0.40` (simulation).  So neither positivity nor
`j^(1/4)` growth is supported yet; the null predicts a stationary `b̃` (that is, `BiasSqrtLaw`
true) and a sign that persists over runs of about 17 levels for every map in the family.
Confidence 25%. -/
def BiasQuarterPowerLaw : Prop :=
  ∃ c C : ℝ, 0 < c ∧ ∀ j : ℕ, 1 ≤ j →
    c * (j : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt 2 ^ j ≤ (bias j : ℝ) ∧
    (bias j : ℝ) ≤ C * (j : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt 2 ^ j

/-- The quarter-power lower bound gives eventual positivity of the bias. -/
theorem biasQuarterPowerLaw_imp_biasPositive_eventually (h : BiasQuarterPowerLaw) :
    ∃ J, ∀ j ≥ J, 0 < bias j := by
  obtain ⟨c, C, hc, h⟩ := h
  refine ⟨1, fun j hj => ?_⟩
  have hjpos : (0 : ℝ) < j := Nat.cast_pos.2 (by omega)
  have hlow := (h j hj).1
  have hpos : 0 < c * (j : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt 2 ^ j :=
    mul_pos (mul_pos hc (Real.rpow_pos_of_pos hjpos _)) (pow_pos (Real.sqrt_pos.2 two_pos) _)
  exact_mod_cast hpos.trans_le hlow

end CollatzMoonshot.Conjugacy
