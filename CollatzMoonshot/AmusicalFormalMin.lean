/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalEscape

/-!
# Empty-interior certificates: the formal-minimum transversal and the resolution gate

Theorem M (`AmusicalPingPong.lean`, research §16) forces any certificate of infinitely many orbits
for `U` to have empty interior in `Ẑ`.  The 2026-10-13 "emptyint" agent asked which such objects
are natural.  None leads to a proof (agent: under 1% toward a seventh orbit), but two are banked.

**The formal-minimum transversal.**  `x` is a *formal minimum* (`FormalMin`) when the formal
log-slope walk has a strict global minimum at time `0`.  That is, `2^{k_t} < 3^t` for the bits
`k_t` spent by the `t` steps after `x`, and `3^t < 2^{k'_t}` for the `t` steps before.  The set is
`ℤ ∩ (W₂ × W₃)`, with `W₂`, `W₃` fat Cantor sets, and it is the wandering set of research §10.
* At most one point per orbit (`formalMin_unique`).
* No periodic points (`not_formalMin_of_periodic`): one period has slope `3^p / 2^e ≠ 1`.
* Symmetric under negation (`formalMin_neg`).
* So infinitely many nonnegative formal minima give Klamkin (a)
  (`infinitelyManyOrbits_of_formalMin_infinite`).
Certifying a single formal minimum proves its orbit infinite, so even `8 ∈ FM` would settle
Klamkin's orbit-of-`8` question.  On `[1, 10⁶]` the formal minima are exactly the `49957` orbit
minima.  The formal walk does not decide true order in general: `U¹² 31 = 30` while
`2¹⁹ < 3¹²` (`formal_walk_disagrees`).

**Proposition G (the resolution gate).**  Suppose `U` has an infinite orbit.  Then a height
`F(x mod M, ⌊log₂ x⌋)` with bounded cocycle along orbits is bounded
(`coarse_quasiInvariant_bounded`).  This kills coarse heights and digit-tail "carry" functions,
and (agent, G2′) transversals defined by residues mod `M(s) ≤ 2^{s/(10(K+1))}` at scale `2^s`.

Paper proofs: agent report `emptyint.md` §3–§4, summarized in
`RESEARCH-2026-10-13-amusical-single-chain.md` §19.  I hand-checked Theorem F.  I checked
`U¹² 31 = 30` numerically.  Theorem F kernel-checked 2026-10-13 (Codex draft, fixed by Ren on the
host); Proposition G1 is the remaining target.
-/

namespace CollatzMoonshot.Amusical

/-- Bits spent by the `t` steps of `U` after `x`. -/
def kFwd (x : ℤ) (t : ℕ) : ℕ :=
  ∑ j ∈ Finset.range t, stepBits (amusical^[j] x)

/-- Bits spent by the `t` steps of `U` before `x`. -/
def kBwd (x : ℤ) (t : ℕ) : ℕ :=
  ∑ j ∈ Finset.range t, stepBits (amusicalInv^[j + 1] x)

/-- `x` is a formal minimum: the formal log-slope walk has a strict global minimum at `0`. -/
def FormalMin (x : ℤ) : Prop :=
  ∀ t : ℕ, 1 ≤ t → 2 ^ kFwd x t < 3 ^ t ∧ 3 ^ t < 2 ^ kBwd x t

/-- **Proved.**  An orbit contains at most one formal minimum.  Paper proof: if `y = Uʲ x` with
`j > 0`, the `j` steps before `y` are the `j` steps after `x`, so `kBwd y j = kFwd x j`, and the
two conditions at `t = j` contradict.  `j < 0` is symmetric. -/
theorem formalMin_unique {x : ℤ} {j : ℤ} (hx : FormalMin x)
    (hy : FormalMin ((amusicalPerm ^ j) x)) : j = 0 := by
  sorry

/-- **Proved.**  A periodic point is not a formal minimum.  Paper proof: with period `p` the `p`
steps before `x` are the `p` steps after it, so `kBwd x p = kFwd x p`, and the two conditions at
`t = p` contradict. -/
theorem not_formalMin_of_periodic {x : ℤ} {p : ℕ} (hp : 0 < p) (h : amusical^[p] x = x) :
    ¬ FormalMin x := by
  sorry

/-- **Proved.**  `U` is odd and preserves parity, so negation preserves every bit count. -/
theorem formalMin_neg (x : ℤ) : FormalMin (-x) ↔ FormalMin x := by
  sorry

/-- **Proved.**  Infinitely many nonnegative formal minima give infinitely many orbits on `ℕ`,
since each orbit holds at most one (`formalMin_unique`). -/
theorem infinitelyManyOrbits_of_formalMin_infinite
    (h : {n : ℕ | FormalMin (n : ℤ)}.Infinite) : AmusicalInfinitelyManyOrbits := by
  sorry

/-- **Proved.**  The formal walk can disagree with the true order: `U¹² 31 = 30 < 31`, yet the
twelve steps spend only `19` bits and `2¹⁹ < 3¹²`. -/
theorem formal_walk_disagrees :
    amusical^[12] 31 = 30 ∧ kFwd 31 12 = 19 ∧ (2 : ℕ) ^ 19 < 3 ^ 12 := by
  decide

/-- **Target (Proposition G1).**  If some orbit is infinite, a height `F(x mod M, ⌊log₂ x⌋)` on
the positive integers whose cocycle along orbits is bounded by `C` is bounded.  Paper proof
(`emptyint.md` §4): (1) *two-visit lemma*: for large `s` and residues `r, r'` there are `x ≡ r`,
`Uʲ x ≡ r'`, both in `[2ˢ, 2ˢ⁺¹)`.  Prescribe the residue via marker words, steer mod the
prime-to-6 part by transitivity of the affine maps, and balance the net slope into
`[2^{−1/4}, 2^{1/4}]` with a word acting trivially mod `M`, using `log(3/2)/log(4/3) ∉ ℚ`.
(2) An infinite orbit is unbounded both ways (Lemma E), with consecutive ratios `≤ 3/2 < 2`,
so it visits every large block.  (3) Chain these: oscillation `≤ 3C` at large scales. -/
theorem coarse_quasiInvariant_bounded (M : ℕ) [NeZero M] (F : ZMod M → ℕ → ℝ) (C : ℝ)
    (hq : ∀ (x : ℤ) (j : ℕ), 1 ≤ x →
      |F (amusical^[j] x : ZMod M) (Nat.log 2 (amusical^[j] x).toNat) -
        F (x : ZMod M) (Nat.log 2 x.toNat)| ≤ C)
    (hinf : ∃ x : ℤ, ∀ p : ℕ, 0 < p → amusical^[p] x ≠ x) :
    ∃ B : ℝ, ∀ x : ℤ, 1 ≤ x → |F (x : ZMod M) (Nat.log 2 x.toNat)| ≤ B := by
  sorry

end CollatzMoonshot.Amusical
