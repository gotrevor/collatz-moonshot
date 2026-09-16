/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.Conjecture
import CollatzMoonshot.Assumed.Computation

/-!
# Eliahou's cycle-length bound, proved

This module discharges what used to be `Assumed.eliahou_min_cycle_length`: any
nontrivial `step`-cycle has period at least `27,869,189`.

Structure follows tangentstorm's Lean 4.28 formalization (edited by Aristotle) of
Eliahou (1993), read for lemma names and shape only; all proofs here are our own,
and the architecture is different: we never build a `Fin L`-indexed cycle
structure and we never leave `ℕ`.

## The argument

Along `m` plain steps from `n`, let `S` be the odd-step index set (`a = |S|`) and
`E` the even-step index set (`e = |E|`), so `a + e = m`.  Unconditionally

* `step_prod_identity` : `2^e · step^[m] n · ∏_{i∈S} x_i = n · ∏_{i∈S} (3x_i+1)`,

a one-line induction (odd step multiplies both sides by `3x+1`, even step eats a
`2`).  On a cycle the `n` cancels, leaving Eliahou's product identity
`∏_{i∈S} (3 + 1/x_i) = 2^e` in integer form.  From it:

* `three_pow_lt_two_pow` : `3^a < 2^e` (each factor `3x_i+1` beats `3x_i`);
* `two_pow_mul_pow_le`  : `2^e · x^a ≤ (3x+1)^a` for any lower bound `x ≤ x_i`.

With `x = 2^68` (every member of a nontrivial cycle exceeds `2^68`, by the
verification frontier) these say exactly `log₂3 < e/a < log₂(3 + 2^-68)`.  Two
consecutive convergents of `log₂3` straddle that interval,

  `c₁ = 16785921/10590737 < log₂3 < e/a < log₂(3+2^-68) < 301994/190537 = c₂`,

and they are Farey neighbours (`10590737·301994 = 16785921·190537 + 1`), so
`farey_denominator_bound` forces `a ≥ 10590737 + 190537 = 10781274`; then
`3^a < 2^e` together with `2^17087914 < 3^10781274` forces `e ≥ 17087915`, and
`m = a + e ≥ 27869189`.

## Certificates

Three big-integer inequalities are checked by `native_decide` (each mints its own
`…_native.native_decide.ax_…` axiom; they are disclosed here and in the docstring
of `Assumed.eliahou_min_cycle_length`):

* `two_pow_lt_three_pow_cert` : `2^16785921 < 3^10590737`   (`c₁ < log₂3`)
* `upper_convergent_cert`     : `(3·2^68+1)^190537 < 2^(301994 + 68·190537)`
                                                            (`log₂(3+2^-68) < c₂`)
* `two_pow_lt_three_pow_big`  : `2^17087914 < 3^10781274`    (the `e` bound)

Nothing else is assumed beyond `Assumed.collatz_verified_up_to_two_pow_68` and
the classical trio.
-/

namespace CollatzMoonshot.FrontB.Eliahou

open CollatzMoonshot Finset

/-! ### Odd and even step index sets for the plain map -/

/-- Indices `i < m` at which the plain orbit of `n` is odd. -/
def oddS (n m : ℕ) : Finset ℕ := (Finset.range m).filter (fun i => step^[i] n % 2 = 1)

/-- Indices `i < m` at which the plain orbit of `n` is even. -/
def evenS (n m : ℕ) : Finset ℕ := (Finset.range m).filter (fun i => step^[i] n % 2 = 0)

theorem oddS_succ (n m : ℕ) :
    oddS n (m + 1) = if step^[m] n % 2 = 1 then insert m (oddS n m) else oddS n m := by
  unfold oddS; rw [Finset.range_add_one, Finset.filter_insert]

theorem evenS_succ (n m : ℕ) :
    evenS n (m + 1) = if step^[m] n % 2 = 0 then insert m (evenS n m) else evenS n m := by
  unfold evenS; rw [Finset.range_add_one, Finset.filter_insert]

theorem not_mem_oddS (n m : ℕ) : m ∉ oddS n m := by simp [oddS]

theorem not_mem_evenS (n m : ℕ) : m ∉ evenS n m := by simp [evenS]

theorem two_mul_step_of_even {x : ℕ} (h : x % 2 = 0) : 2 * step x = x := by
  unfold step; rw [if_pos h]; omega

theorem step_of_odd {x : ℕ} (h : x % 2 = 1) : step x = 3 * x + 1 := by
  unfold step; rw [if_neg (by omega)]

theorem mem_oddS {n m i : ℕ} : i ∈ oddS n m ↔ i < m ∧ step^[i] n % 2 = 1 := by
  simp [oddS]

/-- Odd members are positive. -/
theorem one_le_of_mem_oddS {n m i : ℕ} (hi : i ∈ oddS n m) : 1 ≤ step^[i] n := by
  have := (mem_oddS.mp hi).2; omega

/-- The two index sets partition `range m`. -/
theorem card_oddS_add_card_evenS (n m : ℕ) :
    (oddS n m).card + (evenS n m).card = m := by
  induction m with
  | zero => simp [oddS, evenS]
  | succ k ih =>
    rw [oddS_succ, evenS_succ]
    rcases Nat.mod_two_eq_zero_or_one (step^[k] n) with h | h
    · rw [if_neg (by omega), if_pos h, Finset.card_insert_of_notMem (not_mem_evenS n k)]
      omega
    · rw [if_pos h, if_neg (by omega), Finset.card_insert_of_notMem (not_mem_oddS n k)]
      omega

/-! ### The product identity -/

/-- **Product identity for the plain map.**
`2^e · x_m · ∏_{i∈S} x_i = n · ∏_{i∈S} (3 x_i + 1)`, where `S` is the odd-step set
and `e` the number of even steps.  Unconditional; one induction along the orbit. -/
theorem step_prod_identity (n m : ℕ) :
    2 ^ (evenS n m).card * step^[m] n * ∏ i ∈ oddS n m, step^[i] n
      = n * ∏ i ∈ oddS n m, (3 * step^[i] n + 1) := by
  induction m with
  | zero => simp [oddS, evenS]
  | succ k ih =>
    rcases Nat.mod_two_eq_zero_or_one (step^[k] n) with h | h
    · rw [oddS_succ, evenS_succ, Function.iterate_succ_apply',
        if_neg (show ¬ step^[k] n % 2 = 1 by omega), if_pos h,
        Finset.card_insert_of_notMem (not_mem_evenS n k)]
      have h2 := two_mul_step_of_even h
      calc 2 ^ ((evenS n k).card + 1) * step (step^[k] n) * ∏ i ∈ oddS n k, step^[i] n
          = 2 ^ (evenS n k).card * (2 * step (step^[k] n))
              * ∏ i ∈ oddS n k, step^[i] n := by ring
        _ = 2 ^ (evenS n k).card * step^[k] n * ∏ i ∈ oddS n k, step^[i] n := by rw [h2]
        _ = _ := ih
    · rw [oddS_succ, evenS_succ, Function.iterate_succ_apply', if_pos h,
        if_neg (show ¬ step^[k] n % 2 = 0 by omega),
        Finset.prod_insert (not_mem_oddS n k), Finset.prod_insert (not_mem_oddS n k),
        step_of_odd h]
      calc 2 ^ (evenS n k).card * (3 * step^[k] n + 1)
              * (step^[k] n * ∏ i ∈ oddS n k, step^[i] n)
          = (3 * step^[k] n + 1)
              * (2 ^ (evenS n k).card * step^[k] n * ∏ i ∈ oddS n k, step^[i] n) := by ring
        _ = (3 * step^[k] n + 1) * (n * ∏ i ∈ oddS n k, (3 * step^[i] n + 1)) := by rw [ih]
        _ = n * ((3 * step^[k] n + 1) * ∏ i ∈ oddS n k, (3 * step^[i] n + 1)) := by ring

/-- On a cycle the start value cancels: `2^e · ∏ x_i = ∏ (3x_i+1)`. -/
theorem cycle_prod_identity {n m : ℕ} (hn : 1 ≤ n) (hcyc : step^[m] n = n) :
    2 ^ (evenS n m).card * ∏ i ∈ oddS n m, step^[i] n
      = ∏ i ∈ oddS n m, (3 * step^[i] n + 1) := by
  have h := step_prod_identity n m
  rw [hcyc] at h
  refine Nat.eq_of_mul_eq_mul_left (show 0 < n by omega) ?_
  rw [← h]; ring

theorem prod_oddS_pos (n m : ℕ) : 0 < ∏ i ∈ oddS n m, step^[i] n :=
  Finset.prod_pos fun i hi => by have := one_le_of_mem_oddS hi; omega

/-! ### The two inequalities -/

/-- **Strict subcriticality on a cycle.**  `3^a < 2^e`. -/
theorem three_pow_lt_two_pow {n m : ℕ} (hn : 1 ≤ n) (hcyc : step^[m] n = n)
    (hne : (oddS n m).Nonempty) :
    3 ^ (oddS n m).card < 2 ^ (evenS n m).card := by
  have hid := cycle_prod_identity hn hcyc
  have hP := prod_oddS_pos n m
  have hlt : 3 ^ (oddS n m).card * ∏ i ∈ oddS n m, step^[i] n
      < ∏ i ∈ oddS n m, (3 * step^[i] n + 1) := by
    have : 3 ^ (oddS n m).card * ∏ i ∈ oddS n m, step^[i] n
        = ∏ i ∈ oddS n m, (3 * step^[i] n) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const]
    rw [this]
    exact Finset.prod_lt_prod_of_nonempty
      (fun i hi => by have := one_le_of_mem_oddS hi; omega)
      (fun i _ => by omega) hne
  rw [← hid] at hlt
  exact Nat.lt_of_mul_lt_mul_right hlt

/-- **Min-term inequality.**  For any lower bound `x` on the odd cycle members,
`2^e · x^a ≤ (3x+1)^a`. -/
theorem two_pow_mul_pow_le {n m x : ℕ} (hn : 1 ≤ n) (hcyc : step^[m] n = n)
    (hx : ∀ i ∈ oddS n m, x ≤ step^[i] n) :
    2 ^ (evenS n m).card * x ^ (oddS n m).card ≤ (3 * x + 1) ^ (oddS n m).card := by
  have hid := cycle_prod_identity hn hcyc
  have hP := prod_oddS_pos n m
  have hr : (∏ i ∈ oddS n m, (3 * step^[i] n + 1)) * x ^ (oddS n m).card
      ≤ (3 * x + 1) ^ (oddS n m).card * ∏ i ∈ oddS n m, step^[i] n := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib, ← Finset.prod_const,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun i _ => by positivity) ?_
    intro i hi
    have := hx i hi
    nlinarith
  rw [← hid] at hr
  refine Nat.le_of_mul_le_mul_right ?_ hP
  calc 2 ^ (evenS n m).card * x ^ (oddS n m).card * ∏ i ∈ oddS n m, step^[i] n
      = 2 ^ (evenS n m).card * (∏ i ∈ oddS n m, step^[i] n) * x ^ (oddS n m).card := by ring
    _ ≤ (3 * x + 1) ^ (oddS n m).card * ∏ i ∈ oddS n m, step^[i] n := hr

/-! ### The Farey step -/

/-- **Farey-neighbour denominator bound.**  If `p₁/q₁ < e/a < p₂/q₂` strictly and
`q₁p₂ = p₁q₂ + 1` (Farey neighbours), then `a ≥ q₁ + q₂`.  Pure arithmetic:
`a = a(q₁p₂ - p₁q₂) = q₁(ap₂ - eq₂) + q₂(eq₁ - ap₁) ≥ q₁ + q₂`. -/
theorem farey_denominator_bound {p₁ q₁ p₂ q₂ e a : ℕ}
    (hdet : q₁ * p₂ = p₁ * q₂ + 1)
    (h₁ : p₁ * a < e * q₁) (h₂ : e * q₂ < p₂ * a) :
    q₁ + q₂ ≤ a := by
  have e1 : q₁ * (e * q₂ + 1) ≤ q₁ * (p₂ * a) := Nat.mul_le_mul le_rfl h₂
  have e2 : q₂ * (p₁ * a + 1) ≤ q₂ * (e * q₁) := Nat.mul_le_mul le_rfl h₁
  have hd : q₁ * p₂ * a = p₁ * q₂ * a + a := by rw [hdet]; ring
  nlinarith [e1, e2, hd]

/-! ### The certified convergent facts -/

/-- Certificate: `16785921/10590737 < log₂ 3`, as `2^16785921 < 3^10590737`.
Checked by `native_decide` (GMP big-integer comparison, milliseconds). -/
theorem two_pow_lt_three_pow_cert : (2 : ℕ) ^ 16785921 < 3 ^ 10590737 := by
  native_decide

/-- Certificate: `log₂ (3 + 2⁻⁶⁸) < 301994/190537`, as
`(3·2^68+1)^190537 < 2^(301994 + 68·190537)`.  Checked by `native_decide`. -/
theorem upper_convergent_cert :
    (3 * 2 ^ 68 + 1 : ℕ) ^ 190537 < 2 ^ (301994 + 68 * 190537) := by
  native_decide

/-- Certificate: `2^17087914 < 3^10781274`.  Checked by `native_decide`. -/
theorem two_pow_lt_three_pow_big : (2 : ℕ) ^ 17087914 < 3 ^ 10781274 := by
  native_decide

/-! ### Assembling the bound -/

/-- Every member of the plain orbit of a nontrivial cycle exceeds `2⁶⁸`. -/
theorem two_pow_68_lt_orbit {n m : ℕ} (hn : 1 ≤ n) (hm : 0 < m) (hcyc : step^[m] n = n)
    (hnt : ¬(n = 1 ∨ n = 2 ∨ n = 4)) (i : ℕ) : 2 ^ 68 < step^[i] n := by
  by_contra hle
  push_neg at hle
  have hpos : 1 ≤ step^[i] n := iterate_step_pos hn i
  obtain ⟨c, hc⟩ := Assumed.collatz_verified_up_to_two_pow_68 _ hpos hle
  exact hnt (eq_trivial_of_onCycle_of_reachesOne ⟨m, hm, hcyc⟩
    ⟨c + i, by rw [Function.iterate_add_apply]; exact hc⟩)

/-- **The arithmetic core.**  From the two cycle inequalities `3^a < 2^e` and
`2^e · (2^68)^a ≤ (3·2^68+1)^a` (with `a ≥ 1`), the Farey step gives
`a ≥ 10781274` and `e ≥ 17087915`, hence `a + e ≥ 27869189`. -/
theorem length_bound {a e : ℕ} (ha1 : 1 ≤ a)
    (hA : 3 ^ a < 2 ^ e)
    (hB : 2 ^ e * (2 ^ 68 : ℕ) ^ a ≤ (3 * 2 ^ 68 + 1) ^ a) :
    27869189 ≤ a + e := by
  -- Step 1: `16785921 · a < e · 10590737`, i.e. `16785921/10590737 < e/a`.
  have h₁ : 16785921 * a < e * 10590737 := by
    have c1 : ((2 : ℕ) ^ 16785921) ^ a < (3 ^ 10590737) ^ a :=
      Nat.pow_lt_pow_left two_pow_lt_three_pow_cert (by omega)
    have c2 : ((3 : ℕ) ^ 10590737) ^ a = (3 ^ a) ^ 10590737 := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    have c3 : ((3 : ℕ) ^ a) ^ 10590737 < (2 ^ e) ^ 10590737 :=
      Nat.pow_lt_pow_left hA (by omega)
    have hpow : (2 : ℕ) ^ (16785921 * a) < 2 ^ (e * 10590737) := by
      rw [pow_mul, pow_mul]
      calc ((2 : ℕ) ^ 16785921) ^ a < (3 ^ 10590737) ^ a := c1
        _ = (3 ^ a) ^ 10590737 := c2
        _ < (2 ^ e) ^ 10590737 := c3
    exact (Nat.pow_lt_pow_iff_right (by omega)).mp hpow
  -- Step 2: `e · 190537 < 301994 · a`, i.e. `e/a < 301994/190537`.
  have h₂ : e * 190537 < 301994 * a := by
    have e1 : (2 : ℕ) ^ (e * 190537) * 2 ^ (68 * a * 190537)
        ≤ (3 * 2 ^ 68 + 1) ^ (a * 190537) := by
      have hpl := Nat.pow_le_pow_left hB 190537
      calc (2 : ℕ) ^ (e * 190537) * 2 ^ (68 * a * 190537)
          = (2 ^ e * (2 ^ 68) ^ a) ^ 190537 := by
            rw [mul_pow, ← pow_mul (2 : ℕ) 68 a, ← pow_mul (2 : ℕ) e 190537,
              ← pow_mul (2 : ℕ) (68 * a) 190537]
        _ ≤ ((3 * 2 ^ 68 + 1 : ℕ) ^ a) ^ 190537 := hpl
        _ = (3 * 2 ^ 68 + 1 : ℕ) ^ (a * 190537) := (pow_mul _ a 190537).symm
    have e2 : (3 * 2 ^ 68 + 1 : ℕ) ^ (a * 190537)
        < 2 ^ (301994 * a) * 2 ^ (68 * a * 190537) := by
      have hup : ((3 * 2 ^ 68 + 1 : ℕ) ^ 190537) ^ a
          < ((2 : ℕ) ^ (301994 + 68 * 190537)) ^ a :=
        Nat.pow_lt_pow_left upper_convergent_cert (by omega)
      calc (3 * 2 ^ 68 + 1 : ℕ) ^ (a * 190537)
          = ((3 * 2 ^ 68 + 1 : ℕ) ^ 190537) ^ a := by
            rw [← pow_mul, Nat.mul_comm 190537 a]
        _ < ((2 : ℕ) ^ (301994 + 68 * 190537)) ^ a := hup
        _ = 2 ^ (301994 * a) * 2 ^ (68 * a * 190537) := by
            rw [← pow_mul, ← pow_add]
            congr 1
            ring
    exact (Nat.pow_lt_pow_iff_right (by omega)).mp
      (Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt e1 e2))
  -- Farey neighbours `16785921/10590737` and `301994/190537`.
  have hfar : 10590737 + 190537 ≤ a :=
    farey_denominator_bound (p₁ := 16785921) (q₁ := 10590737)
      (p₂ := 301994) (q₂ := 190537) (by norm_num) h₁ h₂
  have haBig : 10781274 ≤ a := by omega
  have heBig : 17087915 ≤ e := by
    by_contra hlt
    push_neg at hlt
    have g1 : (2 : ℕ) ^ e ≤ 2 ^ 17087914 := pow_le_pow_right₀ (by norm_num) (by omega)
    have g2 : (3 : ℕ) ^ 10781274 ≤ 3 ^ a := pow_le_pow_right₀ (by norm_num) haBig
    have g3 := two_pow_lt_three_pow_big
    exact absurd hA (not_lt.mpr (g1.trans (g3.le.trans g2)))
  omega

/-- **Eliahou (1993), in the kernel.**  Any `step`-cycle outside `{1,2,4}` has
period at least `27,869,189`.

Stands on `Assumed.collatz_verified_up_to_two_pow_68` plus three `native_decide`
big-integer certificates and the classical trio. -/
theorem min_cycle_length :
    ∀ n m : ℕ, 1 ≤ n → 0 < m → step^[m] n = n →
      (n = 1 ∨ n = 2 ∨ n = 4) ∨ 27869189 ≤ m := by
  intro n m hn hm hcyc
  by_cases hnt : n = 1 ∨ n = 2 ∨ n = 4
  · exact Or.inl hnt
  refine Or.inr ?_
  have hsum : (oddS n m).card + (evenS n m).card = m := card_oddS_add_card_evenS n m
  have hx : ∀ i ∈ oddS n m, (2 : ℕ) ^ 68 ≤ step^[i] n :=
    fun i _ => (two_pow_68_lt_orbit hn hm hcyc hnt i).le
  have hne : (oddS n m).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h0
    have hid := cycle_prod_identity hn hcyc
    rw [h0] at hid
    simp only [Finset.prod_empty, mul_one] at hid
    have hcard : (evenS n m).card = m := by
      have h1 : (oddS n m).card = 0 := by rw [h0]; simp
      omega
    rw [hcard] at hid
    have h2 : (1 : ℕ) < 2 ^ m := Nat.one_lt_pow (by omega) (by omega)
    omega
  have ha1 : 1 ≤ (oddS n m).card := Finset.card_pos.mpr hne
  have hA : 3 ^ (oddS n m).card < 2 ^ (evenS n m).card :=
    three_pow_lt_two_pow hn hcyc hne
  have hB : 2 ^ (evenS n m).card * (2 ^ 68 : ℕ) ^ (oddS n m).card
      ≤ (3 * 2 ^ 68 + 1) ^ (oddS n m).card := two_pow_mul_pow_le hn hcyc hx
  have := length_bound ha1 hA hB
  omega

end CollatzMoonshot.FrontB.Eliahou
