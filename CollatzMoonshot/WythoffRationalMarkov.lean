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

/-! ## Periodicity -/

section Periodic

variable (s : Side) {p q : ℕ}

/-- **(ratified).**  For even `p` the forward word of length `L` is periodic mod `2 (qR)^L`.
Paper proof: induction on `L`; `W(x + 2qR·M) = W x + p R M` (`x` even) or `W x + p q M` (`x`
odd), and `p R M = 2 (qR)^{L−1} · ((p/2) R M')` when `M = (qR)^{L−1} M'`. -/
theorem fwdItin_periodic (hp : Even p) (hq : 0 < q) (hqp : q < p) (x m : ℤ) (L : ℕ) :
    fwdItin s p q (x + 2 * ((q : ℤ) * ((p : ℤ) - q)) ^ L * m) L = fwdItin s p q x L := by
  sorry

/-- **(ratified).**  For even `p` coprime to `q` the backward word of length `L` is periodic
mod `2 (p/2)^L`.  Paper proof: `W⁻¹(m + pk) = W⁻¹ m + 2Q k` with `Q ∈ {q, R}` the piece of `m`
(fixed by `m mod p`), and `2Q · (p/2)^{L−1} k' ` is `2 (p/2)^{L−1}` times an integer. -/
theorem bwdItin_periodic (hp : Even p) (hcop : Nat.Coprime p q) (hq : 0 < q) (hqp : q < p)
    (x m : ℤ) (L : ℕ) :
    bwdItin s p q (x + 2 * ((p : ℤ) / 2) ^ L * m) L = bwdItin s p q x L := by
  sorry

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
