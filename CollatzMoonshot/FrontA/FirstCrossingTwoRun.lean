import CollatzMoonshot.FrontA.FirstCrossingOneRun

/-! # First crossing: stopping-time correctness on two-run words

A *two-run* word is `1^k₁ 0^l₁ 1^k₂ 0^l₂`.  This file proves that a start `n ≥ 2` whose
first-crossing trace has that shape descends there, given only the numerically verified
range of the coefficient stopping-time conjecture (`CSTVerified`, Rozier–Terracol).

The engine is a two-sided squeeze on the number `K = k₁ + k₂` of odd steps.  The verified
range plus the strong Rhin-lite separation `sep_strong_492276` force `K ≥ 492276` for a
surviving start; the two block identities plus the weak separation `sep_two_three` force
`K < 64`.  No stopping-time or crossing-existence assumption beyond `CSTVerified` is used.
-/

namespace CollatzMoonshot.FrontA.FirstCrossing

open CollatzMoonshot CollatzMoonshot.FrontB

/-- **The numerically verified range of the coefficient stopping-time conjecture.**
Rozier–Terracol, arXiv:2502.00948v5, Corollary 5.4: the coefficient stopping time equals
the stopping time for every `2 ≤ n ≤ 2.8 · 10^19`; in particular every such start descends
at its first coefficient crossing.  Stated as a named hypothesis (a `def`, in the style of
`SteinerOneCircuit`), never as an axiom. -/
def CSTVerified : Prop := ∀ n m, 2 ≤ n → n ≤ 28 * 10 ^ 18 → At n m → tstep^[m] n < n

/-- **A surviving start has a huge number of odd steps.**  If `n ≥ 2` fails to descend at
its first crossing, then that crossing carries at least `492276` odd letters: below that
threshold `sep_strong_492276` makes the gap `D = 2^m − 3^a` large enough that
`small_start_of_not_descending` bounds `n` inside the verified range. -/
theorem ones_ge_of_survives (hv : CSTVerified) {n m : ℕ} (hn : 2 ≤ n) (h : At n m)
    (hsurv : n ≤ tstep^[m] n) : 492276 ≤ ones (traceWord n m) := by
  by_contra hlt
  push_neg at hlt
  set a := ones (traceWord n m) with ha
  have hsub : 3 ^ a < 2 ^ m := h.2.2
  rcases Nat.eq_zero_or_pos a with h0 | hpos
  · -- no odd letters: `2^m · y = n`, and `m ≥ 1`, so `y < n`
    have hid := tstep_iterate_identity m n
    rw [← ha, h0, pow_zero, one_mul,
      numer_eq_zero_of_ones_eq_zero (by rw [← ha, h0])] at hid
    have h2m : 2 ≤ 2 ^ m := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h.1
    have : 2 * n ≤ 2 ^ m * tstep^[m] n := by
      calc 2 * n ≤ 2 * tstep^[m] n := by omega
        _ ≤ 2 ^ m * tstep^[m] n := Nat.mul_le_mul_right _ h2m
    omega
  · have hsep := sep_strong_492276 a m hpos hlt hsub
    set D := 2 ^ m - 3 ^ a with hD
    have hDpos : 0 < D := by omega
    have hsmall := small_start_of_not_descending h hsurv
    rw [← ha] at hsmall
    have hchain : 3 * D * n ≤ a * (D * 2 ^ 25) :=
      le_trans hsmall (Nat.mul_le_mul_left _ hsep)
    have h3n : 3 * n ≤ a * 2 ^ 25 := by
      have : D * (3 * n) ≤ D * (a * 2 ^ 25) := by
        calc D * (3 * n) = 3 * D * n := by ring
          _ ≤ a * (D * 2 ^ 25) := hchain
          _ = D * (a * 2 ^ 25) := by ring
      exact Nat.le_of_mul_le_mul_left this hDpos
    have hbound : n ≤ 28 * 10 ^ 18 := by
      have : a * 2 ^ 25 ≤ 492275 * 2 ^ 25 := Nat.mul_le_mul_right _ (by omega)
      norm_num at this ⊢
      omega
    exact absurd (hv n m hn hbound h) (by omega)

/-- The canonical two-run word `1^k₁ 0^l₁ 1^k₂ 0^l₂`. -/
def twoRunWord (k₁ l₁ k₂ l₂ : ℕ) : List Bool :=
  List.replicate k₁ true ++ List.replicate l₁ false ++
    List.replicate k₂ true ++ List.replicate l₂ false

@[simp] theorem ones_twoRunWord (k₁ l₁ k₂ l₂ : ℕ) :
    ones (twoRunWord k₁ l₁ k₂ l₂) = k₁ + k₂ := by
  simp [twoRunWord, ones_append, ones_replicate_false']

@[simp] theorem length_twoRunWord (k₁ l₁ k₂ l₂ : ℕ) :
    (twoRunWord k₁ l₁ k₂ l₂).length = k₁ + l₁ + k₂ + l₂ := by
  simp [twoRunWord]; omega

/-- **A supercritical prefix cannot descend.**  If `2^j ≤ 3^(ones of the length-`j` trace)`
then `tstep^[j] n ≥ n`. -/
theorem iterate_ge_of_prefix_supercritical {n j : ℕ}
    (hp : 2 ^ j ≤ 3 ^ ones (traceWord n j)) : n ≤ tstep^[j] n := by
  have hid := tstep_iterate_identity j n
  have h1 : 2 ^ j * n ≤ 2 ^ j * tstep^[j] n := by
    rw [hid]
    calc 2 ^ j * n ≤ 3 ^ ones (traceWord n j) * n := Nat.mul_le_mul_right _ hp
      _ ≤ _ := Nat.le_add_right _ _
  exact Nat.le_of_mul_le_mul_left h1 (by positivity)

/-- **Two-run stopping-time correctness.**  A start `n ≥ 2` whose first crossing is a
two-run word `1^k₁ 0^l₁ 1^k₂ 0^l₂` descends there. -/
theorem descends_of_twoRun (hv : CSTVerified) {n m k₁ l₁ k₂ l₂ : ℕ} (hn : 2 ≤ n)
    (h : At n m) (hw : traceWord n m = twoRunWord k₁ l₁ k₂ l₂) : tstep^[m] n < n := by
  sorry

end CollatzMoonshot.FrontA.FirstCrossing
