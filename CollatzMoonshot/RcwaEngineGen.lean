/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# The `{2,3}`-slope counter-machine engine for any number of states (Lemma P, `r = 5^j`)

`RcwaEngine.lean` runs a 2-counter machine with at most 20 states inside `ℤ` (`r = 25`).  This
file does the same for `r = 5^j` and any `j ≥ 1`, so a machine with any number of states fits.

Put `N = 4·5^(j−1)` (Euler's `φ(5^j)`), so `2^N ≡ 3^N ≡ 1 (mod 5^j)`.  The **phase** of `n` is the
least `k < N` with `3^k ≡ n (mod 5^j)`.  On the **engine zone** (`n ≠ 0`, `5 ∤ n`, `n mod 5^j` a
power of `3`, and `v₃(n) ≥ phase`) the counters are `C₁ = ⌊v₂/N⌋`, `C₂ = ⌊(v₃ − phase)/N⌋`, and the
junk is `(v₂ mod N, (v₃ − phase) mod N, the part of n prime to 6)`.  States are the phases
`s < orderOf (3 : ZMod (5^j))`, and that order is at least `j` (`le_orderOf_three`), so it is
unbounded in `j`.  No primitive-root theory is needed.

The statements mirror `RcwaEngine.lean` with `20` replaced by `N j`.
-/

namespace CollatzMoonshot.RcwaEngineGen

/-- `N j = 4·5^(j−1) = φ(5^j)`. -/
def N (j : ℕ) : ℕ :=
  4 * 5 ^ (j - 1)

/-- Discrete log to base `3` in `ZMod (5^j)`: the least `k < N j` with `3^k = x` (`0` if none). -/
def dlog3 (j : ℕ) (x : ZMod (5 ^ j)) : ℕ :=
  ((List.range (N j)).find? fun k => (3 : ZMod (5 ^ j)) ^ k = x).getD 0

/-- The phase (machine state) of `n`. -/
def phase (j : ℕ) (n : ℤ) : ℕ :=
  dlog3 j (n : ZMod (5 ^ j))

/-- `v₂(n)`. -/
def v2 (n : ℤ) : ℕ :=
  padicValInt 2 n

/-- `v₃(n)`. -/
def v3 (n : ℤ) : ℕ :=
  padicValInt 3 n

/-- The engine zone: `n ≠ 0`, `5 ∤ n`, `n ≡ 3^phase (mod 5^j)`, and `v₃(n) ≥ phase`. -/
def InEngine (j : ℕ) (n : ℤ) : Prop :=
  n ≠ 0 ∧ ¬ (5 : ℤ) ∣ n ∧ (3 : ZMod (5 ^ j)) ^ phase j n = (n : ZMod (5 ^ j)) ∧
    phase j n ≤ v3 n

/-- The first counter `⌊v₂(n)/N⌋`. -/
def C1 (j : ℕ) (n : ℤ) : ℕ :=
  v2 n / N j

/-- The second counter `⌊(v₃(n) − phase)/N⌋`. -/
def C2 (j : ℕ) (n : ℤ) : ℕ :=
  (v3 n - phase j n) / N j

/-- The junk `(v₂ mod N, (v₃ − phase) mod N, the part of n prime to 6)`. -/
def junk (j : ℕ) (n : ℤ) : ℕ × ℕ × ℤ :=
  (v2 n % N j, (v3 n - phase j n) % N j, n / (2 ^ v2 n * 3 ^ v3 n))

/-- Multiply by `2^A 3^B` for integer exponents `A, B` (exact when the denominators divide). -/
def scale (n A B : ℤ) : ℤ :=
  n * 2 ^ A.toNat * 3 ^ B.toNat / (2 ^ (-A).toNat * 3 ^ (-B).toNat)

/-- **Open.**  The order of `3` mod `5^j` is at least `j`, so any number of states fits. -/
theorem le_orderOf_three {j : ℕ} (hj : 1 ≤ j) : j ≤ orderOf (3 : ZMod (5 ^ j)) := by
  sorry

/-- **Open.**  The engine phase is below `N j`. -/
theorem phase_lt {j : ℕ} (hj : 1 ≤ j) {n : ℤ} (hn : InEngine j n) : phase j n < N j := by
  sorry

/-- **Open.**  The first zero test is `2^N ∣ n`. -/
theorem one_le_C1_iff {j : ℕ} (hj : 1 ≤ j) {n : ℤ} (hn : InEngine j n) :
    1 ≤ C1 j n ↔ (2 : ℤ) ^ N j ∣ n := by
  sorry

/-- **Open.**  The second zero test is `3^(N + phase n) ∣ n`. -/
theorem one_le_C2_iff {j : ℕ} (hj : 1 ≤ j) {n : ℤ} (hn : InEngine j n) :
    1 ≤ C2 j n ↔ (3 : ℤ) ^ (N j + phase j n) ∣ n := by
  sorry

section Step

variable {j : ℕ} (hj : 1 ≤ j) {n : ℤ} (hn : InEngine j n) {s' : ℕ}
  (hs' : s' < orderOf (3 : ZMod (5 ^ j))) {δ₁ δ₂ : ℤ}
  (h₁ : 0 ≤ (C1 j n : ℤ) + δ₁) (h₂ : 0 ≤ (C2 j n : ℤ) + δ₂)
include hj hn hs' h₁ h₂

/-- **Open.**  The piece is exact: `scale` really multiplies by `2^{Nδ₁} 3^{Nδ₂ + s' − s}`. -/
theorem scale_spec :
    scale n (N j * δ₁) (N j * δ₂ + s' - phase j n) * 2 ^ (-(N j * δ₁ : ℤ)).toNat *
        3 ^ (-(N j * δ₂ + s' - phase j n : ℤ)).toNat =
      n * 2 ^ (N j * δ₁ : ℤ).toNat * 3 ^ (N j * δ₂ + s' - phase j n : ℤ).toNat := by
  sorry

/-- **Open.**  The piece maps the engine into the engine. -/
theorem inEngine_scale : InEngine j (scale n (N j * δ₁) (N j * δ₂ + s' - phase j n)) := by
  sorry

/-- **Open.**  The piece moves the state to `s'`. -/
theorem phase_scale : phase j (scale n (N j * δ₁) (N j * δ₂ + s' - phase j n)) = s' := by
  sorry

/-- **Open.**  The piece adds `δ₁` to the first counter. -/
theorem C1_scale :
    (C1 j (scale n (N j * δ₁) (N j * δ₂ + s' - phase j n)) : ℤ) = C1 j n + δ₁ := by
  sorry

/-- **Open.**  The piece adds `δ₂` to the second counter. -/
theorem C2_scale :
    (C2 j (scale n (N j * δ₁) (N j * δ₂ + s' - phase j n)) : ℤ) = C2 j n + δ₂ := by
  sorry

/-- **Open.**  The piece leaves the junk unchanged. -/
theorem junk_scale : junk j (scale n (N j * δ₁) (N j * δ₂ + s' - phase j n)) = junk j n := by
  sorry

end Step

/-- **Open.**  An engine point is determined by its state, counters and junk. -/
theorem eq_of_decode_eq {j : ℕ} (hj : 1 ≤ j) {n n' : ℤ} (hn : InEngine j n)
    (hn' : InEngine j n') (hp : phase j n = phase j n') (h1 : C1 j n = C1 j n')
    (h2 : C2 j n = C2 j n') (hjk : junk j n = junk j n') : n = n' := by
  sorry

/-- **Open.**  The junk is independent of the configuration: every state below the order of `3`
and every counter pair occur with the junk of any engine point. -/
theorem exists_decode {j : ℕ} (hj : 1 ≤ j) {n₀ : ℤ} (h₀ : InEngine j n₀) {s : ℕ}
    (hs : s < orderOf (3 : ZMod (5 ^ j))) (c₁ c₂ : ℕ) :
    ∃ n, InEngine j n ∧ phase j n = s ∧ C1 j n = c₁ ∧ C2 j n = c₂ ∧ junk j n = junk j n₀ := by
  sorry

end CollatzMoonshot.RcwaEngineGen
