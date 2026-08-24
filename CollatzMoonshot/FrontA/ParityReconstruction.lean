/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.FrontB.Dictionary

/-!
# Front A: parity reconstruction and the carry invariant

This module executes the experiment-first project of `FRONT-A-PARITY-RECONSTRUCTION.md`.
The measure-theory bridge (M2′) is complete; the remaining Front-A content is arithmetic:
why the parity itinerary of an *ordinary positive integer* cannot sustain critical upward
drift forever, when the unrestricted `2`-adic shift can (the `-1 ↔ -2` cycle).

## The reconstruction machine

For a shortcut-Collatz parity word `v` of length `m` (matching `FrontB.traceWord`), the
exact iterate identity `FrontB.tstep_iterate_identity` reads

    2^m · tstep^[m] n = 3^(ones v) · n + numer v,   v = traceWord n m.

Because `3^a` is a unit modulo `2^m`, each word `v` has a unique **reconstruction residue**
`R(v) < 2^m` with `2^m ∣ 3^(ones v)·R(v) + numer v`, and `traceWord n m = v ↔ n ≡ R(v)`.
The canonical representative's endpoint is `q = tstep^[m](R(v))`.

## The carry invariant (the new content of this lap)

The experiment (`experiments/parity_reconstruction.py`, exhaustive to depth 14) exposed a
**depth-independent** inequality: the normalized endpoint `q / 3^a` is always `< 1`, tight
at the all-ones word (`q = 3^a − 1`).  Equivalently, for every `n < 2^m`,

    tstep^[m] n < 3^(ones (traceWord n m)).

This is genuinely carry-coupled: the naive first-bit induction breaks in the odd case
(where `tstep n` can be as large as `≈ 3·2^m`, above `2^m`).  The proof strengthens the
statement to hold for **all** `n` with a floor correction that the odd step exactly absorbs:

    tstep^[m] n < 3^(ones (traceWord n m)) · (n / 2^m + 1).          (`tstep_iterate_lt`)

For a fixed positive integer this says: once `2^m > n`, the orbit value is always strictly
below `3^(#odd steps so far)` — the precise upper envelope of the critical-drift bracket
(the matching lower bound `3^a · n / 2^m ≤ tstep^[m] n` is immediate from the identity).

Strength note (per the mandatory audit in the project doc): this is an upper envelope, not
by itself a no-divergence theorem — combined with the identity's lower bound it reproduces
the standard critical-density bracket `3^a n / 2^m ≤ tstep^[m] n < 3^a`, i.e. divergence
still requires odd density `> log 2 / log 3`.  It IS a certified, depth-independent carry
inequality (the project's "GO" bar for a stable invariant), and it is the first rigorous
archimedean constraint coupling the parity word to size in this project.
-/

namespace CollatzMoonshot.FrontA

open CollatzMoonshot CollatzMoonshot.FrontB

/-- The head letter of `traceWord n (m+1)` counts one odd step iff `n` is odd. -/
theorem ones_traceWord_succ (n m : ℕ) :
    ones (traceWord n (m + 1)) =
      ones (traceWord (tstep n) m) + (if n % 2 = 1 then 1 else 0) := by
  rw [traceWord]
  rcases Nat.even_or_odd n with h | h
  · have h0 : n % 2 = 0 := Nat.even_iff.mp h
    simp [ones, h0]
  · have h1 : n % 2 = 1 := Nat.odd_iff.mp h
    simp [ones, h1]

/-- **The carry invariant.**  For every `m` and every `n`,

    `tstep^[m] n < 3 ^ (ones (traceWord n m)) * (n / 2 ^ m + 1)`.

The odd step is exactly absorbed by the floor factor `n / 2^m + 1`; specializing to
`n < 2^m` (floor `= 0`) gives `tstep^[m] n < 3 ^ (ones (traceWord n m))`. -/
theorem tstep_iterate_lt (m n : ℕ) :
    tstep^[m] n < 3 ^ ones (traceWord n m) * (n / 2 ^ m + 1) := by
  induction m generalizing n with
  | zero => simp [traceWord]
  | succ k ih =>
    rw [Function.iterate_succ_apply, ones_traceWord_succ]
    have key := ih (tstep n)
    rcases Nat.even_or_odd n with h | h
    · -- even step: `tstep n = n / 2`, no odd letter, floors line up exactly
      have h0 : n % 2 = 0 := Nat.even_iff.mp h
      have hts : tstep n = n / 2 := by simp [tstep, h0]
      have hfloor : tstep n / 2 ^ k = n / 2 ^ (k + 1) := by
        rw [hts, Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm]
      rw [hfloor] at key
      simpa [h0] using key
    · -- odd step: one odd letter (factor `3`), floor grows by at most `2 → 3·(⌊n/2^{k+1}⌋+1)`
      have h1 : n % 2 = 1 := Nat.odd_iff.mp h
      have hts : tstep n = (3 * n + 1) / 2 := by simp [tstep, h1, Nat.mul_comm]
      -- the floor inequality: `tstep n / 2^k + 1 ≤ 3 * (n / 2^{k+1} + 1)`
      have hfl : tstep n / 2 ^ k + 1 ≤ 3 * (n / 2 ^ (k + 1) + 1) := by
        have hsplit : n = 2 ^ (k + 1) * (n / 2 ^ (k + 1)) + n % 2 ^ (k + 1) :=
          (Nat.div_add_mod n (2 ^ (k + 1))).symm
        have hmod : n % 2 ^ (k + 1) < 2 ^ (k + 1) := Nat.mod_lt _ (by positivity)
        -- `tstep n / 2^k = ((3n+1)/2) / 2^k = (3n+1) / 2^{k+1}`
        have hcollapse : tstep n / 2 ^ k = (3 * n + 1) / 2 ^ (k + 1) := by
          rw [hts, Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm 2 (2 ^ k)]
        rw [hcollapse]
        -- write `q = n / 2^{k+1}`, `s = n % 2^{k+1}`; then `3n+1 = 3q·2^{k+1} + (3s+1)`
        set q := n / 2 ^ (k + 1) with hq
        set s := n % 2 ^ (k + 1) with hs
        have hlt : 3 * n + 1 < 2 ^ (k + 1) * (3 * q + 3) := by
          have h3s : 3 * s + 1 < 3 * 2 ^ (k + 1) := by omega
          calc 3 * n + 1 = 3 * q * 2 ^ (k + 1) + (3 * s + 1) := by rw [hsplit]; ring
            _ < 3 * q * 2 ^ (k + 1) + 3 * 2 ^ (k + 1) := by omega
            _ = 2 ^ (k + 1) * (3 * q + 3) := by ring
        have hle : (3 * n + 1) / 2 ^ (k + 1) < 3 * q + 3 :=
          Nat.div_lt_of_lt_mul hlt
        omega
      -- combine: `tstep^[k] (tstep n) < 3^a' * (tstep n / 2^k + 1) ≤ 3^a' * 3 * (⌊n/2^{k+1}⌋+1)`
      have hmul : 3 ^ ones (traceWord (tstep n) k) * (tstep n / 2 ^ k + 1)
          ≤ 3 ^ ones (traceWord (tstep n) k) * (3 * (n / 2 ^ (k + 1) + 1)) :=
        Nat.mul_le_mul_left _ hfl
      have hpow : 3 ^ ones (traceWord (tstep n) k) * (3 * (n / 2 ^ (k + 1) + 1))
          = 3 ^ (ones (traceWord (tstep n) k) + 1) * (n / 2 ^ (k + 1) + 1) := by
        rw [pow_succ]; ring
      calc tstep^[k] (tstep n)
          < 3 ^ ones (traceWord (tstep n) k) * (tstep n / 2 ^ k + 1) := key
        _ ≤ 3 ^ ones (traceWord (tstep n) k) * (3 * (n / 2 ^ (k + 1) + 1)) := hmul
        _ = 3 ^ (ones (traceWord (tstep n) k) + 1) * (n / 2 ^ (k + 1) + 1) := hpow
        _ = 3 ^ (ones (traceWord (tstep n) k) + (if n % 2 = 1 then 1 else 0))
              * (n / 2 ^ (k + 1) + 1) := by rw [h1]; norm_num

/-- **The endpoint bound.**  For `n < 2^m`, the accelerated orbit value after `m` steps is
strictly below `3` to the power of the number of odd steps taken.  This is the depth-
independent normalized-endpoint bound `q / 3^a < 1` discovered exhaustively in the
experiment (tight at the all-ones word). -/
theorem tstep_iterate_lt_pow_ones {m n : ℕ} (hn : n < 2 ^ m) :
    tstep^[m] n < 3 ^ ones (traceWord n m) := by
  have h := tstep_iterate_lt m n
  have h0 : n / 2 ^ m = 0 := Nat.div_eq_of_lt hn
  simpa [h0] using h

/-- The matching lower bound, immediate from the exact identity (`numer ≥ 0`):
`3^a · n ≤ 2^m · tstep^[m] n`.  Together with `tstep_iterate_lt_pow_ones` this is the
standard critical-drift bracket. -/
theorem pow_ones_mul_le (m n : ℕ) :
    3 ^ ones (traceWord n m) * n ≤ 2 ^ m * tstep^[m] n := by
  rw [tstep_iterate_identity]; exact Nat.le_add_right _ _

/-- **The exact carry-gap identity.**  Rearranging the iterate identity gives the exact size
of the gap below the `3^a` cap: for `n ≤ 2^m` (so both subtractions are honest),

    `2^m · (3^a − tstep^[m] n) = 3^a · (2^m − n) − numer (traceWord n m)`.

The experiment confirms this holds on all words and that the gap `3^a − tstep^[m] n` bottoms
out at exactly `1` (the all-ones word), so `tstep_iterate_lt_pow_ones` is the sharpest
uniform bound — no depth-independent inequality strictly tighter than `q < 3^a` exists. -/
theorem two_pow_mul_gap (m n : ℕ) (hn : n ≤ 2 ^ m) :
    2 ^ m * (3 ^ ones (traceWord n m) - tstep^[m] n)
      = 3 ^ ones (traceWord n m) * (2 ^ m - n) - numer (traceWord n m) := by
  have hid := tstep_iterate_identity m n
  rw [Nat.mul_sub, hid, Nat.mul_sub, Nat.mul_comm (2 ^ m) (3 ^ ones (traceWord n m)),
    Nat.sub_sub]

/-!
## The reconstruction dictionary (residue determinacy)

The parity trace of length `m` determines the starting value modulo `2^m`, and conversely
(so the finite parity words biject with residues mod `2^m` — every word is realized, the
strength-audit guardrail).  Only the forward direction is needed downstream; it follows
directly from the exact identity and the fact that `3^a` is a unit mod `2^m`.
-/

/-- **Residue determinacy (forward dictionary).**  Equal length-`m` parity traces force the
starting values equal modulo `2^m`.  Proof: both sides satisfy `3^a · · + numer ≡ 0`
(mod `2^m`) with the *same* word data, and `3^a` is invertible mod `2^m`. -/
theorem traceWord_eq_imp_modEq {a b m : ℕ} (h : traceWord a m = traceWord b m) :
    a ≡ b [MOD 2 ^ m] := by
  have hA : 3 ^ ones (traceWord a m) * a + numer (traceWord a m) ≡ 0 [MOD 2 ^ m] := by
    rw [← tstep_iterate_identity m a]; exact (Nat.modEq_zero_iff_dvd).2 (dvd_mul_right _ _)
  have hB : 3 ^ ones (traceWord a m) * b + numer (traceWord a m) ≡ 0 [MOD 2 ^ m] := by
    rw [h, ← tstep_iterate_identity m b]; exact (Nat.modEq_zero_iff_dvd).2 (dvd_mul_right _ _)
  have hcancel : 3 ^ ones (traceWord a m) * a ≡ 3 ^ ones (traceWord a m) * b [MOD 2 ^ m] :=
    Nat.ModEq.add_right_cancel' _ (hA.trans hB.symm)
  have hcop : Nat.Coprime (3 ^ ones (traceWord a m)) (2 ^ m) :=
    Nat.Coprime.pow _ _ (by decide)
  exact Nat.ModEq.cancel_left_of_coprime hcop.symm hcancel

/-- **Equality from all finite traces.**  If two naturals have the same parity trace at
every length, they are equal.  This is the positivity-side statement: a natural number's
full parity itinerary determines it.  (Project item: "equality of naturals whose finite
parity traces agree at every length.") -/
theorem eq_of_forall_traceWord_eq {a b : ℕ}
    (h : ∀ m, traceWord a m = traceWord b m) : a = b := by
  have hmod : a ≡ b [MOD 2 ^ (a + b + 1)] := traceWord_eq_imp_modEq (h (a + b + 1))
  have ha : a < 2 ^ (a + b + 1) :=
    lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hb : b < 2 ^ (a + b + 1) :=
    lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by norm_num) (by omega))
  unfold Nat.ModEq at hmod
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hmod

/-!
## No-divergence baseline: eventually periodic parity trace forces an orbit repeat

If the parity itinerary of the accelerated orbit is eventually periodic, two orbit states
share their entire future trace, hence (by `eq_of_forall_traceWord_eq`) are equal, so the
orbit cycles and cannot diverge.  This is the promised restricted rigidity baseline.
-/

/-- Two starting values with identical parity itineraries have identical traces of every
length.  (Engine of the periodic baseline.) -/
theorem traceWord_eq_of_parity_itinerary_eq {u w : ℕ}
    (h : ∀ j, tstep^[j] u % 2 = tstep^[j] w % 2) (ℓ : ℕ) :
    traceWord u ℓ = traceWord w ℓ := by
  induction ℓ generalizing u w with
  | zero => rfl
  | succ ℓ ih =>
    have h0 : u % 2 = w % 2 := by simpa using h 0
    have htail : ∀ j, tstep^[j] (tstep u) % 2 = tstep^[j] (tstep w) % 2 := by
      intro j
      have := h (j + 1)
      rwa [Function.iterate_succ_apply, Function.iterate_succ_apply] at this
    rw [traceWord, traceWord, h0, ih htail]

/-- **The periodic baseline.**  If the accelerated-orbit parity is eventually periodic with
period `p` from index `M` (`p ≥ 1`), then `tstep^[M] n = tstep^[M + p] n`: the orbit
repeats.  Consequently it is bounded and does not diverge. -/
theorem tstep_repeat_of_eventually_periodic_parity {n M p : ℕ}
    (hper : ∀ k, M ≤ k → tstep^[k] n % 2 = tstep^[k + p] n % 2) :
    tstep^[M] n = tstep^[M + p] n := by
  apply eq_of_forall_traceWord_eq
  intro ℓ
  apply traceWord_eq_of_parity_itinerary_eq
  intro j
  have e := hper (M + j) (Nat.le_add_right M j)
  have lhs : tstep^[j] (tstep^[M] n) = tstep^[M + j] n := by
    rw [← Function.iterate_add_apply, Nat.add_comm]
  have rhs : tstep^[j] (tstep^[M + p] n) = tstep^[M + j + p] n := by
    rw [← Function.iterate_add_apply]; congr 1; omega
  rw [lhs, rhs, e]

/-- The accelerated orbit of `n` visits only finitely many values once its parity is
eventually periodic: every later state equals one within the first `M + p` steps.  (A
bounded orbit cannot diverge; recorded as the restricted no-divergence result.) -/
theorem tstep_periodic_of_eventually_periodic_parity {n M p : ℕ} (_hp : 1 ≤ p)
    (hper : ∀ k, M ≤ k → tstep^[k] n % 2 = tstep^[k + p] n % 2) :
    ∀ k, M ≤ k → tstep^[k] n = tstep^[k + p] n := by
  intro k hk
  obtain ⟨d, rfl⟩ : ∃ d, k = M + d := ⟨k - M, by omega⟩
  have base := tstep_repeat_of_eventually_periodic_parity hper
  have : tstep^[d] (tstep^[M] n) = tstep^[d] (tstep^[M + p] n) := by rw [base]
  rw [← Function.iterate_add_apply, ← Function.iterate_add_apply] at this
  have e1 : d + M = M + d := by omega
  have e2 : d + (M + p) = M + d + p := by omega
  rw [e1, e2] at this
  exact this

end CollatzMoonshot.FrontA
