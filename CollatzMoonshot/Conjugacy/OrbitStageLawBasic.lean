/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Conjugacy.OrbitHeightLaw

/-!
# The stage word law: definitions

* `stageMap n = T^(size n) n`, one window of `size n` letters.
* `ExpSparse B`: the stages of `B` hold at most `A (2ρ)^k` integers, `ρ < 1`.  A set of this kind has
  natural density `0` at a power rate.
* `blkCnt P L o q r`: how many of `T^(o + j L) r`, `j < q`, satisfy `P`.  When `P` sees only the
  residue mod `2^L`, the `q` events see disjoint blocks of letters, so they are independent over
  `r < 2^s` (Terras).
* The good events at scale `s`: `ClassGood` (every class of `u`-windows mod `|u|` has the right count, at
  every length `≥ η s`), `OddLow` (at least `(1/2 − γ) s` odd letters), `SufGood` (no suffix of length
  `≥ ℓ₀` has more than `3/5` odd letters).
-/

namespace CollatzMoonshot.Conjugacy

open Filter Topology CollatzMoonshot.FrontB CollatzMoonshot.Obstructions.ParityWord

/-- One window of `size n` letters: `T^(size n) n`. -/
def stageMap (n : ℕ) : ℕ := tstep^[Nat.size n] n

open Classical in
/-- **Exponentially sparse.**  Stage `k` of `B` holds at most `A (2ρ)^k` integers, for some `ρ < 1`. -/
def ExpSparse (B : Set ℕ) : Prop :=
  ∃ A ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ k : ℕ,
    (((Finset.Ico (2 ^ (k - 1)) (2 ^ k)).filter (· ∈ B)).card : ℝ) ≤ A * (2 * ρ) ^ k

/-- How many of `T^(o + j L) r`, `j < q`, satisfy `P`. -/
def blkCnt (P : ℕ → Prop) [DecidablePred P] (L o q r : ℕ) : ℕ :=
  ((Finset.range q).filter fun j => P (tstep^[o + j * L] r)).card

/-- The letters of a word, as a function of the position. -/
def uLet (u : List Bool) : ℕ → Bool := fun s => u.getD s false

/-- **Good `u`-windows at scale `s`.**  For each class `c < |u|`, the windows at `c + j |u|`, `j < q`,
match `u` about `q 2^(−|u|)` times, within `η q`, at every `q ≥ η s` that fits below `s`. -/
def ClassGood (u : List Bool) (η : ℝ) (s r : ℕ) : Prop :=
  ∀ c < u.length, ∀ q : ℕ, c + q * u.length ≤ s → η * s ≤ q →
    |(blkCnt (WindowMatch (uLet u) u.length 0) u.length c q r : ℝ) - q * (1 / 2 : ℝ) ^ u.length| ≤
      η * q

/-- At least `(1/2 − γ) s` odd letters among the first `s`. -/
def OddLow (γ : ℝ) (s r : ℕ) : Prop := (1 / 2 - γ) * s ≤ oddCount r s

/-- No suffix of the first `s` letters of length `≥ ℓ₀` has more than `3/5` odd letters. -/
def SufGood (ℓ₀ s r : ℕ) : Prop :=
  ∀ i, i + ℓ₀ ≤ s → 5 * (oddCount r s - oddCount r i) ≤ 3 * (s - i)

/-- The one-window good event at the scale of `n` itself. -/
def GoodZero (u : List Bool) (η γ : ℝ) (n : ℕ) : Prop :=
  ClassGood u η (Nat.size n) n ∧ OddLow γ (Nat.size n) n ∧ SufGood (Nat.size n / 10) (Nat.size n) n

end CollatzMoonshot.Conjugacy
