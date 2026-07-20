/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.Basic

/-!
# The funnel: 2-adic proximity to `1` is an archimedean crash

The concrete mechanism behind the rigidity lane's bet.  A value `v ≡ 1 (mod 4^s)`
tracks the trivial cycle for `s` rounds of `1 → 4 → 2 → 1`, and each round of
tracking multiplies its size by exactly `3/4`: from `v = 4^s·m + 1`, after `3s`
steps the orbit sits at `3^s·m + 1 ≈ (3/4)^s · v`.

This is why the pinned working conjecture W1 (`Rigidity/Invariant.lean`) has
teeth: an invariant limit measure charging the embedded trivial cycle means the
orbit returns 2-adically close to `1` at every scale with positive frequency, and
each such return is a multiplicative crash.  Divergence and cycle-charging are
enemies.  (Upgrading this pointwise lemma to the frequency/all-scales argument is
lane milestone M2 - real work, not done here.)
-/

namespace CollatzMoonshot

/-- One tracking round: values `≡ 1 (mod 4)` follow the trivial cycle's shape for
three steps (`odd, even, even`) and come back `≡ 1 (mod 4·(3/4))`, shrunk:
`4m + 1 ↦ 3m + 1`. -/
theorem step_round (m : ℕ) : step^[3] (4 * m + 1) = 3 * m + 1 := by
  have h1 : step (4 * m + 1) = 12 * m + 4 := by unfold step; split <;> omega
  have h2 : step (12 * m + 4) = 6 * m + 2 := by unfold step; split <;> omega
  have h3 : step (6 * m + 2) = 3 * m + 1 := by unfold step; split <;> omega
  have hshow : step^[3] (4 * m + 1) = step (step (step (4 * m + 1))) := rfl
  rw [hshow, h1, h2, h3]

/-- **The funnel**: from `4^s·m + 1`, each of the first `s` tracking rounds
multiplies the displacement from `1` by exactly `3/4`. -/
theorem funnel (m s r : ℕ) (hrs : r ≤ s) :
    step^[3 * r] (4 ^ s * m + 1) = 3 ^ r * 4 ^ (s - r) * m + 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hr : r ≤ s := by omega
    have hmul : 3 * (r + 1) = 3 + 3 * r := by ring
    rw [hmul, Function.iterate_add_apply, ih hr]
    have h4 : 3 ^ r * 4 ^ (s - r) * m + 1 = 4 * (3 ^ r * 4 ^ (s - (r + 1)) * m) + 1 := by
      have hsr : s - r = (s - (r + 1)) + 1 := by omega
      rw [hsr, pow_succ]
      ring
    rw [h4, step_round]
    ring

/-- Endpoint crash: `v = 4^s·m + 1` reaches `3^s·m + 1` in `3s` steps - a
multiplicative collapse by `(3/4)^s`.  2-adic distance to `1` converts directly
into archimedean descent. -/
theorem funnel_crash (m s : ℕ) : step^[3 * s] (4 ^ s * m + 1) = 3 ^ s * m + 1 := by
  simpa using funnel m s s le_rfl

end CollatzMoonshot
