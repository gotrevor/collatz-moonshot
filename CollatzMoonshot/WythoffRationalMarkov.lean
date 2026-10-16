/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.WythoffRational

/-!
# Theorem M: parity itineraries of `W_{p/q±}` are exactly Markov (even `p`) or i.i.d. (odd `p`)

For `x ∈ ℤ` let `ε_i = W^i x mod 2` (`i ≥ 0`) and `β_i = W^{−i} x mod 2` (`i ≥ 1`).  For even `p`
coprime to `q`, over every window `[a, a + N)` whose length is a multiple of the period
`markovPeriod p q L L' = 2 (qR)^L (p/2)^{L'}`, the number of `x` with `ε_0 = e`, forward word
`ε_1 … ε_L = f` and backward word `β_1 … β_{L'} = b` is exactly
`N/2 · ∏ F(ε_i → ε_{i+1}) · ∏ B(β_i → β_{i+1})` (`β_0 = e`), with the chains `fwdProb`,
`bwdProb` of Lemma 1 (`cylCount_eq`).  So forward and backward itineraries are independent given
the parity of `x` (`cylCount_condIndep`), and not independent without it (`tenThirds_dependent`,
`r = 10/3`, `+`).  For odd `p` the law is i.i.d.: forward `Bernoulli(½)`, backward `(q/p, R/p)`,
over windows that are multiples of `iidPeriod p q L L' = 2^{L+1} (qR)^L p^{L'}`
(`cylCount_eq_odd`).

On `ℤ` every branch of `W` is exactly affine (`wythoff_add_even`, `wythoff_add_odd`), so the
counts are exact for every window, with no boundary terms.  Research note `wythoff-evenp` §2.
-/

namespace CollatzMoonshot.WythoffRationalMarkov

open CollatzMoonshot.WythoffRational

/-! ## Words, itineraries, cylinder counts -/

/-- The weight of a parity word `w` under a two-state chain `P` started in state `e`:
`P(e → w₀) P(w₀ → w₁) ⋯`. -/
def wordWeight (P : ZMod 2 → ZMod 2 → ℚ) : ZMod 2 → List (ZMod 2) → ℚ
  | _, [] => 1
  | e, f :: w => P e f * wordWeight P f w

/-- Forward parity itinerary `[W x, W² x, …, W^L x] mod 2`. -/
def fwdItin (s : Side) (p q : ℕ) (x : ℤ) (L : ℕ) : List (ZMod 2) :=
  (List.range L).map fun i => (((wythoff s p q)^[i + 1] x : ℤ) : ZMod 2)

/-- Backward parity itinerary `[W⁻¹ x, W⁻² x, …, W^{−L} x] mod 2`. -/
def bwdItin (s : Side) (p q : ℕ) (x : ℤ) (L : ℕ) : List (ZMod 2) :=
  (List.range L).map fun i => (((wythoffInv s p q)^[i + 1] x : ℤ) : ZMod 2)

/-- The number of `x = a + i ∈ [a, a + N)` with parity `e`, forward word `f` and backward word
`b`. -/
def cylCount (s : Side) (p q : ℕ) (a : ℤ) (N : ℕ) (e : ZMod 2) (f b : List (ZMod 2)) : ℕ :=
  ((Finset.range N).filter fun i : ℕ =>
    ((a + i : ℤ) : ZMod 2) = e ∧ fwdItin s p q (a + i) f.length = f ∧
      bwdItin s p q (a + i) b.length = b).card

/-- The even-`p` period `2 (qR)^L (p/2)^{L'}`. -/
def markovPeriod (p q L L' : ℕ) : ℕ :=
  2 * (q * (p - q)) ^ L * (p / 2) ^ L'

/-- The odd-`p` period `2^{L+1} (qR)^L p^{L'}`. -/
def iidPeriod (p q L L' : ℕ) : ℕ :=
  2 ^ (L + 1) * (q * (p - q)) ^ L * p ^ L'

/-- The i.i.d. backward law for odd `p`: `W⁻¹ m` is even with probability `q/p`. -/
def iidBwd (p q : ℕ) (b : ZMod 2) : ℚ :=
  if b = 0 then (q : ℚ) / p else ((p : ℚ) - q) / p

/-! ## Counting tools -/

section Counting

open Finset

/-- Shifting by any multiple of a period. -/
theorem periodic_add_mul {g : ℤ → ℕ} {M : ℤ} (hg : Function.Periodic g M) (x k : ℤ) :
    g (x + k * M) = g x := (hg.int_mul k) x

/-- Tool A: a one-period sum is shift-invariant. -/
theorem sum_shift {g : ℤ → ℕ} {M : ℕ} (hg : Function.Periodic g M) (c : ℤ) :
    ∑ i ∈ range M, g (c + i) = ∑ i ∈ range M, g i := by
  have step : ∀ c : ℤ, ∑ i ∈ range M, g (c + 1 + i) = ∑ i ∈ range M, g (c + i) := by
    intro c
    have h1 : ∑ i ∈ range (M + 1), g (c + i) = ∑ i ∈ range M, g (c + 1 + i) + g c := by
      rw [sum_range_succ']
      congr 1
      · apply sum_congr rfl; intro i _; congr 1; push_cast; ring
      · simp
    have h2 : ∑ i ∈ range (M + 1), g (c + i) = ∑ i ∈ range M, g (c + i) + g c := by
      rw [sum_range_succ, hg c]
    omega
  induction c using Int.induction_on with
  | zero => simp
  | succ i ih => rw [step, ih]
  | pred i ih => rw [← step, sub_add_cancel]; exact ih

/-- Tool E: a sum over `k` periods. -/
theorem sum_mul_period {g : ℤ → ℕ} {M : ℕ} (hg : Function.Periodic g M) (c : ℤ) (k : ℕ) :
    ∑ i ∈ range (k * M), g (c + i) = k * ∑ i ∈ range M, g i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [add_mul, one_mul, sum_range_add, ih, add_mul, one_mul]
    congr 1
    rw [← sum_shift hg (c + (k * M : ℕ))]
    apply sum_congr rfl; intro i _; congr 1; push_cast; ring

/-- Tool B: an arithmetic progression with step coprime to the period meets every residue once. -/
theorem sum_ap {g : ℤ → ℕ} {M : ℕ} (hM : 0 < M) (hg : Function.Periodic g M) (c u : ℤ)
    (hu : IsCoprime u (M : ℤ)) :
    ∑ i ∈ range M, g (c + u * i) = ∑ i ∈ range M, g i := by
  have hM' : (0 : ℤ) < M := by exact_mod_cast hM
  have hmod : ∀ x : ℤ, g x = g ((x % M).toNat : ℕ) := by
    intro x
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hM'.ne')]
    conv_lhs => rw [← Int.emod_add_mul_ediv x M]
    rw [show x % ↑M + ↑M * (x / ↑M) = x % M + (x / M) * M by ring]
    exact periodic_add_mul hg _ _
  let f : ℕ → ℕ := fun i => ((c + u * i) % M).toNat
  have hf : ∀ i ∈ range M, f i ∈ range M := by
    intro i _
    simp only [mem_range, f]
    have := Int.emod_lt_of_pos (c + u * i) hM'
    have := Int.emod_nonneg (c + u * i) hM'.ne'
    omega
  have hinj : Set.InjOn f (range M : Set ℕ) := by
    intro i hi j hj hij
    simp only [coe_range, Set.mem_Iio] at hi hj
    simp only [f] at hij
    have h1 : (c + u * i) % M = (c + u * j) % M := by
      have := Int.emod_nonneg (c + u * i) hM'.ne'
      have := Int.emod_nonneg (c + u * j) hM'.ne'
      omega
    have h2 : (M : ℤ) ∣ u * ((j : ℤ) - i) := by
      have := (show Int.ModEq M (c + u * i) (c + u * j) from h1).dvd
      rwa [show c + u * (j : ℤ) - (c + u * i) = u * ((j : ℤ) - i) by ring] at this
    have h3 : (M : ℤ) ∣ (j : ℤ) - i := hu.symm.dvd_of_dvd_mul_left h2
    have h4 := Int.eq_zero_of_abs_lt_dvd h3 (abs_lt.2 ⟨by omega, by omega⟩)
    omega
  exact sum_nbij f hf hinj (surjOn_of_injOn_of_card_le f (fun i hi => hf i hi) hinj le_rfl)
    (fun i _ => hmod _)

/-- Tool C: the same inside one parity class, for a period `2K`. -/
theorem sum_ap_two {g : ℤ → ℕ} {K : ℕ} (hK : 0 < K) (hg : Function.Periodic g (2 * K : ℕ))
    (c u : ℤ) (hu : IsCoprime u (K : ℤ)) :
    ∑ i ∈ range K, g (c + 2 * u * i) = ∑ i ∈ range K, g (c % 2 + 2 * i) := by
  have hh : Function.Periodic (fun y : ℤ => g (c % 2 + 2 * y)) K := fun y => by
    simp only
    rw [show c % 2 + 2 * (y + K) = c % 2 + 2 * y + ((2 * K : ℕ) : ℤ) by push_cast; ring]
    exact hg _
  have := sum_ap hK hh (c / 2) u hu
  rw [← this]
  apply sum_congr rfl
  intro i _
  congr 1
  have := Int.emod_add_mul_ediv c 2
  linarith

/-- Tool D: splitting `range (2K)` by parity. -/
theorem sum_range_two_mul_parity (G : ℤ → ℕ) (e : ZMod 2) (K : ℕ) :
    ∑ x ∈ range (2 * K), (if ((x : ℤ) : ZMod 2) = e then G x else 0) =
      ∑ i ∈ range K, G (e.val + 2 * i) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [show 2 * (K + 1) = 2 * K + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ]
    have a : (((2 * K : ℕ) : ℤ) : ZMod 2) = 0 :=
      (intCast_zmod2_eq_zero_iff _).2 (by push_cast; omega)
    have b : (((2 * K + 1 : ℕ) : ℤ) : ZMod 2) = 1 :=
      (intCast_zmod2_eq_one_iff _).2 (by push_cast; omega)
    rcases zmod2_cases e with rfl | rfl
    · rw [if_pos a, if_neg (by rw [b]; decide)]
      simp
    · rw [if_neg (by rw [a]; decide), if_pos b]
      have : (1 : ZMod 2).val = 1 := rfl
      simp only [this]
      push_cast
      ring_nf

/-- Tool F: blocks `i = t + q m`. -/
theorem sum_range_mul_block (G : ℕ → ℕ) (q N : ℕ) :
    ∑ i ∈ range (q * N), G i = ∑ t ∈ range q, ∑ m ∈ range N, G (t + q * m) := by
  rw [sum_comm]
  induction N with
  | zero => simp
  | succ N ih =>
    rw [mul_add, mul_one, sum_range_add, ih, sum_range_succ]
    congr 1
    apply sum_congr rfl
    intro t _
    congr 1
    ring

end Counting

/-! ## Itineraries step by step -/

section Steps

variable (s : Side) {p q : ℕ}

theorem fwdItin_succ (x : ℤ) (L : ℕ) :
    fwdItin s p q x (L + 1) =
      ((wythoff s p q x : ℤ) : ZMod 2) :: fwdItin s p q (wythoff s p q x) L := by
  simp only [fwdItin, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1

theorem bwdItin_succ (x : ℤ) (L : ℕ) :
    bwdItin s p q x (L + 1) =
      ((wythoffInv s p q x : ℤ) : ZMod 2) :: bwdItin s p q (wythoffInv s p q x) L := by
  simp only [bwdItin, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1

/-- `W⁻¹(m + p y) = W⁻¹ m + 2 Q y`, `Q ∈ {q, R}` the piece of `W⁻¹ m`. -/
theorem wythoffInv_add (hq : 0 < q) (hqp : q < p) (m y : ℤ) :
    wythoffInv s p q (m + p * y) = wythoffInv s p q m +
      2 * (if wythoffInv s p q m % 2 = 0 then (q : ℤ) else (p : ℤ) - q) * y := by
  have hm : wythoff s p q (wythoffInv s p q m) = m := wythoff_wythoffInv s hq hqp m
  split_ifs with h
  · rw [← wythoffInv_wythoff s hq hqp (wythoffInv s p q m + 2 * q * y),
      wythoff_add_even s hq h, hm]
  · rw [← wythoffInv_wythoff s hq hqp (wythoffInv s p q m + 2 * ((p : ℤ) - q) * y),
      wythoff_add_odd s hqp (by omega), hm]

theorem cast_add_two_mul (a b c : ℤ) : ((a + 2 * b * c : ℤ) : ZMod 2) = (a : ZMod 2) := by
  push_cast
  rw [show (2 : ZMod 2) = 0 by decide]
  ring

end Steps

/-! ## Periodicity -/

section Periodic

variable (s : Side) {p q : ℕ}

/-- **(ratified).**  For even `p` the forward word of length `L` is periodic mod `2 (qR)^L`.
Paper proof: induction on `L`; `W(x + 2qR·M) = W x + p R M` (`x` even) or `W x + p q M` (`x`
odd), and `p R M = 2 (qR)^{L−1} · ((p/2) R M')` when `M = (qR)^{L−1} M'`. -/
theorem fwdItin_periodic (hp : Even p) (hq : 0 < q) (hqp : q < p) (x m : ℤ) (L : ℕ) :
    fwdItin s p q (x + 2 * ((q : ℤ) * ((p : ℤ) - q)) ^ L * m) L = fwdItin s p q x L := by
  obtain ⟨r, hr⟩ := hp
  have hr' : (p : ℤ) = r + r := by exact_mod_cast hr
  induction L generalizing x m with
  | zero => rfl
  | succ L ih =>
    rw [fwdItin_succ, fwdItin_succ]
    rcases Int.emod_two_eq_zero_or_one x with h | h
    · have hW : wythoff s p q (x + 2 * ((q : ℤ) * ((p : ℤ) - q)) ^ (L + 1) * m) =
          wythoff s p q x + 2 * ((q : ℤ) * ((p : ℤ) - q)) ^ L * (r * ((p : ℤ) - q) * m) := by
        rw [show x + 2 * ((q : ℤ) * ((p : ℤ) - q)) ^ (L + 1) * m =
            x + 2 * q * (((p : ℤ) - q) * ((q : ℤ) * ((p : ℤ) - q)) ^ L * m) by ring,
          wythoff_add_even s hq h, hr']
        ring
      rw [hW, ih, cast_add_two_mul]
    · have hW : wythoff s p q (x + 2 * ((q : ℤ) * ((p : ℤ) - q)) ^ (L + 1) * m) =
          wythoff s p q x + 2 * ((q : ℤ) * ((p : ℤ) - q)) ^ L * (r * q * m) := by
        rw [show x + 2 * ((q : ℤ) * ((p : ℤ) - q)) ^ (L + 1) * m =
            x + 2 * ((p : ℤ) - q) * (q * ((q : ℤ) * ((p : ℤ) - q)) ^ L * m) by ring,
          wythoff_add_odd s hqp h, hr']
        ring
      rw [hW, ih, cast_add_two_mul]

/-- **(ratified).**  For even `p` coprime to `q` the backward word of length `L` is periodic
mod `2 (p/2)^L`.  Paper proof: `W⁻¹(m + pk) = W⁻¹ m + 2Q k` with `Q ∈ {q, R}` the piece of `m`
(fixed by `m mod p`), and `2Q · (p/2)^{L−1} k' ` is `2 (p/2)^{L−1}` times an integer. -/
theorem bwdItin_periodic (hp : Even p) (hcop : Nat.Coprime p q) (hq : 0 < q) (hqp : q < p)
    (x m : ℤ) (L : ℕ) :
    bwdItin s p q (x + 2 * ((p : ℤ) / 2) ^ L * m) L = bwdItin s p q x L := by
  obtain ⟨r, hr⟩ := hp
  have hr' : (p : ℤ) = r + r := by exact_mod_cast hr
  rw [show (p : ℤ) / 2 = r by omega]
  induction L generalizing x m with
  | zero => rfl
  | succ L ih =>
    rw [bwdItin_succ, bwdItin_succ,
      show x + 2 * (r : ℤ) ^ (L + 1) * m = x + p * ((r : ℤ) ^ L * m) by rw [hr']; ring,
      wythoffInv_add s hq hqp,
      show 2 * (if wythoffInv s p q x % 2 = 0 then (q : ℤ) else (p : ℤ) - q) * ((r : ℤ) ^ L * m) =
        2 * (r : ℤ) ^ L * ((if wythoffInv s p q x % 2 = 0 then (q : ℤ) else (p : ℤ) - q) * m) by
        ring, ih, cast_add_two_mul]

end Periodic

/-! ## Theorem M -/

section TheoremM

variable (s : Side) {p q : ℕ}

/-- **(ratified, Theorem M, even `p`).**  Exact joint cylinder counts.  Paper proof (note §2):
*forward*: for pieces `π_0 … π_{L−1}` with matching parities the forward cylinder is one
residue class mod `2 ∏ Q_{π_i}` (`x = a_π + 2Q m ↦ c_π + p m`; mod 2 the tail condition is the
parity match, free of `m` as `p` is even; mod the odd part it fixes `m`, `p` being a unit), so
density `½ ∏ Q_{π_i}^{−1}`, and summing over the pieces of type `e` with image parity `f` gives
`F(e → f)` by Lemma 1.  *Backward*: `W⁻¹ m ∈ D_π ⟺ m ≡ c_π (mod p)`; the next condition fixes
`y` mod `p/2` (`gcd(2Q, p) = 2`), so a depth-`L'` cylinder is one class mod `p (p/2)^{L'−1}` and
`B(e → f) = #{π of type f : c_π ≡ e}/(p/2)`.  *Joint*: the odd parts of the two moduli are
coprime (`(qR)^L` vs `(p/2)^{L'}`), so CRT. -/
theorem cylCount_eq (hp : Even p) (hcop : Nat.Coprime p q) (hq : 0 < q) (hqp : q < p)
    (a : ℤ) (N : ℕ) (e : ZMod 2) (f b : List (ZMod 2))
    (hN : markovPeriod p q f.length b.length ∣ N) :
    (cylCount s p q a N e f b : ℚ) =
      N / 2 * wordWeight (fwdProb s p q) e f * wordWeight (bwdProb s p q) e b := by
  sorry

/-- **(ratified, Theorem M, forward only).**  The `b = []` case. -/
theorem cylCount_fwd (hp : Even p) (hcop : Nat.Coprime p q) (hq : 0 < q) (hqp : q < p)
    (a : ℤ) (N : ℕ) (e : ZMod 2) (f : List (ZMod 2)) (hN : markovPeriod p q f.length 0 ∣ N) :
    (cylCount s p q a N e f [] : ℚ) = N / 2 * wordWeight (fwdProb s p q) e f := by
  sorry

/-- **(ratified, Theorem M, backward only).**  The `f = []` case. -/
theorem cylCount_bwd (hp : Even p) (hcop : Nat.Coprime p q) (hq : 0 < q) (hqp : q < p)
    (a : ℤ) (N : ℕ) (e : ZMod 2) (b : List (ZMod 2)) (hN : markovPeriod p q 0 b.length ∣ N) :
    (cylCount s p q a N e [] b : ℚ) = N / 2 * wordWeight (bwdProb s p q) e b := by
  sorry

/-- **(ratified, conditional independence).**  Given the parity of `x`, the forward and backward
words are independent: `#(e, f, b) · #(e) = #(e, f) · #(e, b)` over every window whose length is
a multiple of the joint period. -/
theorem cylCount_condIndep (hp : Even p) (hcop : Nat.Coprime p q) (hq : 0 < q) (hqp : q < p)
    (a : ℤ) (N : ℕ) (e : ZMod 2) (f b : List (ZMod 2))
    (hN : markovPeriod p q f.length b.length ∣ N) :
    cylCount s p q a N e f b * cylCount s p q a N e [] [] =
      cylCount s p q a N e f [] * cylCount s p q a N e [] b := by
  sorry

/-- **(ratified, unconditional dependence at `r = 10/3`, `+`).**  Without conditioning on the
parity of `x`, the one-step forward and backward words are dependent: over `[0, 210)` the counts
are `37 · 210 ≠ 115 · 63`.  Paper proof: `cylCount_eq` and arithmetic. -/
theorem tenThirds_dependent :
    (cylCount .plus 10 3 0 210 0 [0] [0] + cylCount .plus 10 3 0 210 1 [0] [0]) * 210 ≠
      (cylCount .plus 10 3 0 210 0 [0] [] + cylCount .plus 10 3 0 210 1 [0] []) *
        (cylCount .plus 10 3 0 210 0 [] [0] + cylCount .plus 10 3 0 210 1 [] [0]) := by
  sorry

/-- **(ratified, Theorem M, odd `p`).**  The i.i.d. law: every forward step and the parity of `x`
cost `½`; every backward step costs `q/p` (even preimage) or `R/p` (odd), independent of
everything else.  Paper proof: as for even `p`, but now the mod-2 condition fixes `m mod 2`
(forward) and `2Q` is a unit mod `p` (backward); the moduli `2^{L+1}(qR)^L` and `p^{L'}` are
coprime. -/
theorem cylCount_eq_odd (hp : Odd p) (hcop : Nat.Coprime p q) (hq : 0 < q) (hqp : q < p)
    (a : ℤ) (N : ℕ) (e : ZMod 2) (f b : List (ZMod 2))
    (hN : iidPeriod p q f.length b.length ∣ N) :
    (cylCount s p q a N e f b : ℚ) = N / 2 ^ (f.length + 1) * (b.map (iidBwd p q)).prod := by
  sorry

end TheoremM

end CollatzMoonshot.WythoffRationalMarkov
