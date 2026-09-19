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

/-! ### Run helpers -/

/-- A maximal run of even steps: `b` halvings multiply the endpoint back up. -/
theorem run_false {z b : ℕ} (hz : traceWord z b = List.replicate b false) :
    z = 2 ^ b * tstep^[b] z := by
  have hid := tstep_iterate_identity b z
  rw [hz, ones_replicate_false',
    numer_eq_zero_of_ones_eq_zero (ones_replicate_false' b)] at hid
  simp only [pow_zero, one_mul, add_zero] at hid
  exact hid.symm

/-- A maximal run of odd steps: `a` odd steps send `z + 1 = 2^a s` to `3^a s`. -/
theorem run_true {z a : ℕ} (hz : traceWord z a = List.replicate a true) :
    ∃ s, 1 ≤ s ∧ z + 1 = 2 ^ a * s ∧ tstep^[a] z + 1 = 3 ^ a * s := by
  have hid := tstep_iterate_identity a z
  have hnum : numer (List.replicate a true) = 3 ^ a - 2 ^ a := by
    have := numer_oneCircuitWord a 0; simpa [oneCircuitWord] using this
  rw [hz, ones_replicate_true, hnum] at hid
  have h23 : 2 ^ a ≤ 3 ^ a := Nat.pow_le_pow_left (by norm_num) a
  have hid' : 2 ^ a * (tstep^[a] z + 1) = 3 ^ a * (z + 1) := by
    rw [mul_add, mul_add, hid]; omega
  have hdvd : 2 ^ a ∣ z + 1 := by
    have hcop : Nat.Coprime (2 ^ a) (3 ^ a) := Nat.Coprime.pow _ _ (by decide)
    exact hcop.dvd_of_dvd_mul_left ⟨_, hid'.symm⟩
  obtain ⟨s, hs⟩ := hdvd
  refine ⟨s, ?_, hs, ?_⟩
  · rcases Nat.eq_zero_or_pos s with rfl | hpos
    · simp at hs
    · exact hpos
  · have : 2 ^ a * (tstep^[a] z + 1) = 2 ^ a * (3 ^ a * s) := by rw [hid', hs]; ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) this

/-- Recover the trace of a proper prefix that drops one final letter. -/
theorem traceWord_of_append_singleton {n m : ℕ} {v : List Bool} {b : Bool}
    (hw : traceWord n m = v ++ [b]) : traceWord n v.length = v := by
  have hm : m = v.length + 1 := by
    have := congrArg List.length hw; simpa using this
  rw [← take_traceWord n m v.length (by omega), hw]
  simp

/-- **Two-run stopping-time correctness.**  A start `n ≥ 2` whose first crossing is a
two-run word `1^k₁ 0^l₁ 1^k₂ 0^l₂` descends there. -/
theorem descends_of_twoRun (hv : CSTVerified) {n m k₁ l₁ k₂ l₂ : ℕ} (hn : 2 ≤ n)
    (h : At n m) (hw : traceWord n m = twoRunWord k₁ l₁ k₂ l₂) : tstep^[m] n < n := by
  have hm : m = k₁ + l₁ + k₂ + l₂ := by
    have := congrArg List.length hw; simpa using this
  -- degenerate shapes are one-run words
  rcases Nat.eq_zero_or_pos k₂ with rfl | hk2
  · refine descends_of_oneRun (a := k₁) (b := l₁ + l₂) hn h ?_
    rw [hw]; simp [twoRunWord, oneCircuitWord, List.append_assoc, ← List.replicate_add]
  rcases Nat.eq_zero_or_pos l₁ with rfl | hl1
  · refine descends_of_oneRun (a := k₁ + k₂) (b := l₂) hn h ?_
    rw [hw]; simp [twoRunWord, oneCircuitWord, List.append_assoc, ← List.replicate_add]
  rcases Nat.eq_zero_or_pos k₁ with rfl | hk1
  · -- the word starts with `false`, but the length-one prefix must be supercritical
    exfalso
    obtain ⟨l, rfl⟩ : ∃ l, l₁ = l + 1 := ⟨l₁ - 1, by omega⟩
    have ht1 : traceWord n 1 = [false] := by
      rw [← take_traceWord n m 1 (by omega), hw]
      simp [twoRunWord, List.replicate_succ]
    have hsup := h.2.1 1 (by omega)
    rw [ht1] at hsup
    norm_num [ones] at hsup
  -- the last letter is `false`
  have hl2 : 1 ≤ l₂ := by
    rcases Nat.eq_zero_or_pos l₂ with rfl | hp
    · exfalso
      obtain ⟨k, rfl⟩ : ∃ k, k₂ = k + 1 := ⟨k₂ - 1, by omega⟩
      have hsp : twoRunWord k₁ l₁ (k + 1) 0 = twoRunWord k₁ l₁ k 0 ++ [true] := by
        simp [twoRunWord, List.replicate_succ', List.append_assoc]
      rw [hsp] at hw
      have hpre := traceWord_of_append_singleton hw
      rw [length_twoRunWord] at hpre
      have hsup := h.2.1 (k₁ + l₁ + k + 0) (by omega)
      rw [hpre, ones_twoRunWord] at hsup
      have hsub : 3 ^ (k₁ + k + 1) < 2 ^ m := by
        have := h.2.2; rw [hw] at this
        simpa [ones_twoRunWord, ones_append, ones] using this
      have hexp : 2 ^ m = 2 * 2 ^ (k₁ + l₁ + k + 0) := by
        rw [show m = (k₁ + l₁ + k + 0) + 1 from by omega, pow_succ']
        ring
      have h3 : 3 ^ (k₁ + k + 1) = 3 * 3 ^ (k₁ + k) := by
        rw [pow_succ']
      have hpos : 0 < 3 ^ (k₁ + k) := by positivity
      omega
    · exact hp
  -- main case: all four blocks nonempty
  by_contra hsurv
  push_neg at hsurv
  set K := k₁ + k₂ with hKdef
  have hones : ones (traceWord n m) = K := by rw [hw, ones_twoRunWord]
  have hK : 492276 ≤ K := by
    have := ones_ge_of_survives hv hn h hsurv; rwa [hones] at this
  have hsub : 3 ^ K < 2 ^ m := by have := h.2.2; rwa [hones] at this
  -- the near-critical window, from the proper prefix of length `m - 1`
  have hwin : 2 ^ m < 2 * 3 ^ K := by
    obtain ⟨l, hl⟩ : ∃ l, l₂ = l + 1 := ⟨l₂ - 1, by omega⟩
    have hsp : twoRunWord k₁ l₁ k₂ l₂ = twoRunWord k₁ l₁ k₂ l ++ [false] := by
      rw [hl]; simp [twoRunWord, List.replicate_succ', List.append_assoc]
    rw [hsp] at hw
    have hpre := traceWord_of_append_singleton hw
    rw [length_twoRunWord] at hpre
    have hsup := h.2.1 (k₁ + l₁ + k₂ + l) (by omega)
    rw [hpre, ones_twoRunWord, ← hKdef] at hsup
    have hexp : 2 ^ m = 2 * 2 ^ (k₁ + l₁ + k₂ + l) := by
      rw [show m = (k₁ + l₁ + k₂ + l) + 1 from by omega, pow_succ]; ring
    -- strictness: `2^(m-1)` is even, `3^K` is odd
    have hodd : 3 ^ K % 2 = 1 := by
      have := Nat.pow_mod 3 K 2; simpa using this
    have heven : 2 ^ (k₁ + l₁ + k₂ + l) % 2 = 0 := by
      obtain ⟨t, ht⟩ : ∃ t, k₁ + l₁ + k₂ + l = t + 1 := ⟨k₁ + l₁ + k₂ + l - 1, by omega⟩
      rw [ht, pow_succ]
      omega
    omega
  -- split the trace into its four runs
  have hassoc : twoRunWord k₁ l₁ k₂ l₂ =
      List.replicate k₁ true ++ (List.replicate l₁ false ++
        (List.replicate k₂ true ++ List.replicate l₂ false)) := by
    simp [twoRunWord, List.append_assoc]
  set x₀ := tstep^[k₁] n with hx₀def
  set x₁ := tstep^[l₁] x₀ with hx₁def
  set x₂ := tstep^[k₂] x₁ with hx₂def
  set y := tstep^[l₂] x₂ with hydef
  have hsplit : traceWord n k₁ ++ traceWord x₀ (l₁ + (k₂ + l₂)) =
      List.replicate k₁ true ++ (List.replicate l₁ false ++
        (List.replicate k₂ true ++ List.replicate l₂ false)) := by
    rw [hx₀def, ← traceWord_add, show k₁ + (l₁ + (k₂ + l₂)) = m from by omega, hw, hassoc]
  obtain ⟨hA, hrest⟩ := List.append_inj hsplit (by simp)
  rw [traceWord_add] at hrest
  obtain ⟨hB, hrest2⟩ := List.append_inj hrest (by simp)
  rw [← hx₁def, traceWord_add] at hrest2
  obtain ⟨hC, hD⟩ := List.append_inj hrest2 (by simp)
  rw [← hx₂def] at hD
  have hyeq : tstep^[m] n = y := by
    rw [hydef, hx₂def, hx₁def, hx₀def, ← Function.iterate_add_apply,
      ← Function.iterate_add_apply, ← Function.iterate_add_apply]
    congr 1
    omega
  rw [hyeq] at hsurv
  -- the four run identities
  obtain ⟨a0, ha0, e1, e2⟩ := run_true hA
  have e3 : x₀ = 2 ^ l₁ * x₁ := run_false hB
  obtain ⟨a1, ha1, e4, e5⟩ := run_true hC
  have e6 : x₂ = 2 ^ l₂ * y := run_false hD
  -- the middle point does not descend either
  have hnx₁ : n ≤ x₁ := by
    have hsup := h.2.1 (k₁ + l₁) (by omega)
    have := iterate_ge_of_prefix_supercritical hsup
    rwa [show k₁ + l₁ = l₁ + k₁ from Nat.add_comm _ _, Function.iterate_add_apply,
      ← hx₀def, ← hx₁def] at this
  have hx₁pos : 0 < x₁ := by omega
  -- the two block identities
  have key1 : 3 ^ k₁ * (n + 1) = 2 ^ k₁ * (2 ^ l₁ * x₁ + 1) := by
    rw [← e3, e2, e1]; ring
  have key2 : 3 ^ k₂ * (x₁ + 1) = 2 ^ k₂ * (2 ^ l₂ * y + 1) := by
    rw [← e6, e5, e4]; ring
  have hprod : 3 ^ K * ((n + 1) * (x₁ + 1))
      = 2 ^ K * ((2 ^ l₁ * x₁ + 1) * (2 ^ l₂ * y + 1)) := by
    rw [hKdef, pow_add, pow_add]
    calc 3 ^ k₁ * 3 ^ k₂ * ((n + 1) * (x₁ + 1))
        = (3 ^ k₁ * (n + 1)) * (3 ^ k₂ * (x₁ + 1)) := by ring
      _ = (2 ^ k₁ * (2 ^ l₁ * x₁ + 1)) * (2 ^ k₂ * (2 ^ l₂ * y + 1)) := by rw [key1, key2]
      _ = 2 ^ k₁ * 2 ^ k₂ * ((2 ^ l₁ * x₁ + 1) * (2 ^ l₂ * y + 1)) := by ring
  have hge : 2 ^ m * (x₁ * n) ≤ 3 ^ K * ((n + 1) * (x₁ + 1)) := by
    rw [hprod, show m = K + (l₁ + l₂) from by omega, pow_add]
    have h1 : 2 ^ l₁ * x₁ * (2 ^ l₂ * y) ≤ (2 ^ l₁ * x₁ + 1) * (2 ^ l₂ * y + 1) := by nlinarith
    calc 2 ^ K * 2 ^ (l₁ + l₂) * (x₁ * n)
        ≤ 2 ^ K * 2 ^ (l₁ + l₂) * (x₁ * y) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hsurv)
      _ = 2 ^ K * (2 ^ l₁ * x₁ * (2 ^ l₂ * y)) := by rw [pow_add]; ring
      _ ≤ 2 ^ K * ((2 ^ l₁ * x₁ + 1) * (2 ^ l₂ * y + 1)) := Nat.mul_le_mul_left _ h1
  have hsq : 2 ^ m * (n * n) ≤ 3 ^ K * ((n + 1) * (n + 1)) := by
    have hstep : n * (x₁ + 1) ≤ (n + 1) * x₁ := by nlinarith
    have hc : x₁ * (2 ^ m * (n * n)) ≤ x₁ * (3 ^ K * ((n + 1) * (n + 1))) := by
      calc x₁ * (2 ^ m * (n * n)) = (2 ^ m * (x₁ * n)) * n := by ring
        _ ≤ (3 ^ K * ((n + 1) * (x₁ + 1))) * n := Nat.mul_le_mul_right _ hge
        _ = 3 ^ K * (n + 1) * (n * (x₁ + 1)) := by ring
        _ ≤ 3 ^ K * (n + 1) * ((n + 1) * x₁) := Nat.mul_le_mul_left _ hstep
        _ = x₁ * (3 ^ K * ((n + 1) * (n + 1))) := by ring
    exact Nat.le_of_mul_le_mul_left hc hx₁pos
  -- the gap `D`
  obtain ⟨D, hD'⟩ : ∃ D, 2 ^ m = D + 3 ^ K := ⟨_, (Nat.sub_add_cancel hsub.le).symm⟩
  have hDpos : 0 < D := by omega
  have hDn : D * (n * n) ≤ 3 ^ K * (3 * n) := by
    rw [hD'] at hsq
    have hstep : D * (n * n) + 3 ^ K * (n * n) ≤ 3 ^ K * (2 * n + 1) + 3 ^ K * (n * n) := by
      calc D * (n * n) + 3 ^ K * (n * n) = (D + 3 ^ K) * (n * n) := by ring
        _ ≤ 3 ^ K * ((n + 1) * (n + 1)) := hsq
        _ = 3 ^ K * (2 * n + 1) + 3 ^ K * (n * n) := by ring
    have h1 : D * (n * n) ≤ 3 ^ K * (2 * n + 1) := Nat.add_le_add_iff_right.mp hstep
    exact h1.trans (Nat.mul_le_mul_left _ (by omega))
  have hDn2 : D * n ≤ 3 * 3 ^ K := by
    have hc : (D * n) * n ≤ (3 * 3 ^ K) * n := by
      calc (D * n) * n = D * (n * n) := by ring
        _ ≤ 3 ^ K * (3 * n) := hDn
        _ = (3 * 3 ^ K) * n := by ring
    exact Nat.le_of_mul_le_mul_right hc (by omega)
  -- the weak separation
  have hsep : 3 ^ (3 * K) ≤ D ^ 3 * 2 ^ K := by
    have := sep_two_three K m (by omega) hsub hwin
    rwa [show 2 ^ m - 3 ^ K = D from by omega] at this
  have hpow3 : (3 ^ K) ^ 3 = 3 ^ (3 * K) := by rw [← pow_mul, Nat.mul_comm]
  have hn3 : n ^ 3 ≤ 27 * 2 ^ K := by
    have hcube : D ^ 3 * n ^ 3 ≤ D ^ 3 * (27 * 2 ^ K) := by
      calc D ^ 3 * n ^ 3 = (D * n) ^ 3 := by ring
        _ ≤ (3 * 3 ^ K) ^ 3 := Nat.pow_le_pow_left hDn2 3
        _ = 27 * (3 ^ K) ^ 3 := by ring
        _ = 27 * 3 ^ (3 * K) := by rw [hpow3]
        _ ≤ 27 * (D ^ 3 * 2 ^ K) := Nat.mul_le_mul_left _ hsep
        _ = D ^ 3 * (27 * 2 ^ K) := by ring
    exact Nat.le_of_mul_le_mul_left hcube (by positivity)
  have hA1 : (n + 1) ^ 3 < 2 ^ (K + 8) := by
    have hcu := Nat.pow_le_pow_left (show 2 * (n + 1) ≤ 3 * n from by omega) 3
    have h8 : 8 * (n + 1) ^ 3 ≤ 729 * 2 ^ K := by
      calc 8 * (n + 1) ^ 3 = (2 * (n + 1)) ^ 3 := by ring
        _ ≤ (3 * n) ^ 3 := hcu
        _ = 27 * n ^ 3 := by ring
        _ ≤ 27 * (27 * 2 ^ K) := Nat.mul_le_mul_left _ hn3
        _ = 729 * 2 ^ K := by ring
    have hKe : 2 ^ (K + 8) = 256 * 2 ^ K := by rw [pow_add]; ring
    have h2K : 0 < 2 ^ K := by positivity
    rw [hKe]
    exact (fun (A B : ℕ) (hB : 0 < B) (hle : 8 * A ≤ 729 * B) => by omega)
      ((n + 1) ^ 3) (2 ^ K) h2K h8
  -- lower bounds on the two runs of odd steps
  have h2k1 : 2 ^ k₁ ≤ n + 1 := by rw [e1]; exact Nat.le_mul_of_pos_right _ ha0
  have hk1lt : 3 * k₁ < K + 8 := by
    have hc : 2 ^ (3 * k₁) < 2 ^ (K + 8) := by
      calc 2 ^ (3 * k₁) = (2 ^ k₁) ^ 3 := by rw [← pow_mul, Nat.mul_comm]
        _ ≤ (n + 1) ^ 3 := Nat.pow_le_pow_left h2k1 3
        _ < 2 ^ (K + 8) := hA1
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hc
  have h2l1 : 2 * x₁ ≤ x₀ := by
    rw [e3]
    exact Nat.mul_le_mul_right _ (by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ l₁ := Nat.pow_le_pow_right (by norm_num) hl1)
  have h2k2 : 2 ^ k₂ ≤ 3 ^ k₁ * a0 := by
    rw [← e2]
    have : 2 ^ k₂ ≤ x₁ + 1 := by rw [e4]; exact Nat.le_mul_of_pos_right _ ha1
    omega
  have hK2 : 2 ^ K ≤ 3 ^ k₁ * (n + 1) := by
    rw [hKdef, pow_add, e1]
    calc 2 ^ k₁ * 2 ^ k₂ ≤ 2 ^ k₁ * (3 ^ k₁ * a0) := Nat.mul_le_mul_left _ h2k2
      _ = 3 ^ k₁ * (2 ^ k₁ * a0) := by ring
  have hfin : 3 * K < 5 * k₁ + (K + 8) := by
    have h35 : (3 : ℕ) ^ (3 * k₁) ≤ 2 ^ (5 * k₁) := by
      rw [pow_mul, pow_mul]; exact Nat.pow_le_pow_left (by norm_num) k₁
    have hc : 2 ^ (3 * K) < 2 ^ (5 * k₁ + (K + 8)) := by
      calc 2 ^ (3 * K) = (2 ^ K) ^ 3 := by rw [← pow_mul, Nat.mul_comm]
        _ ≤ (3 ^ k₁ * (n + 1)) ^ 3 := Nat.pow_le_pow_left hK2 3
        _ = (3 ^ k₁) ^ 3 * (n + 1) ^ 3 := by ring
        _ = 3 ^ (3 * k₁) * (n + 1) ^ 3 := by
              rw [show (3 : ℕ) ^ (3 * k₁) = (3 ^ k₁) ^ 3 from by rw [← pow_mul, Nat.mul_comm]]
        _ ≤ 2 ^ (5 * k₁) * (n + 1) ^ 3 := Nat.mul_le_mul_right _ h35
        _ < 2 ^ (5 * k₁) * 2 ^ (K + 8) := Nat.mul_lt_mul_of_pos_left hA1 (by positivity)
        _ = 2 ^ (5 * k₁ + (K + 8)) := (pow_add 2 (5 * k₁) (K + 8)).symm
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hc
  omega

end CollatzMoonshot.FrontA.FirstCrossing
