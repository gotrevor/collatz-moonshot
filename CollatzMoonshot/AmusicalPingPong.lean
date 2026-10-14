/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalAntiKohl
import CollatzMoonshot.AmusicalPingPong.Phase

/-!
# A ping-pong engine: infinitely many orbits without a periodic cone

`U` is residue-transitive: no union of residue classes is forward-invariant
(`amusical_no_periodic_cone`), so the cone mechanism of `AmusicalAntiKohl.lean` cannot apply.  The
2026-10-13 "transitive" agent asked whether *any* residue-transitive member of the anti-Kohl class
has provably infinitely many orbits, and built one.  `PP(0)` has modulus `13300`, `9711` affine
pieces, and slopes `3/4, 3/2, 3, 21/5, 15, 75/7`, all of `3`-adic valuation `1`.

**The engine.**  Four linear pieces run a two-counter machine on `(v₅ x, v₇ x)`, with a phase
`x mod 19`.  Write `K = ⟨8⟩ = {1, 7, 8, 11, 12, 18}` and `B = 15 K`.
* `x ↦ 21x/5` on `5 ∣ x`, phase in `K`;
* `x ↦ 15x` on `5 ∤ x`, `7 ∣ x`, phase `1`;
* `x ↦ 75x/7` on `7 ∣ x`, phase in `B`;
* `x ↦ 3x` on `7 ∤ x`, `5 ∣ x`, phase in `B`.

A seed has `v₅ x = A` odd, `7 ∤ x` and `x · 8^A ≡ 1 (mod 19)`.  It runs `A` steps one way,
hands off, and runs `A` steps back, returning to a seed with `A' = 2A + 1`.  So it never leaves the
engine (`pingPong_seed_inEngine`).  Every engine image is a multiple of `3`, so a seed prime to `3`
is the first engine-forever point of its orbit.  Distinct such seeds lie in distinct orbits,
hence infinitely many orbits (`infinitelyManyOrbits_of_pingPong`), for every permutation that
runs the engine.

`PP(0)` fills the rest of `ℤ` with slopes `3/2^d` so that the whole map is a bijection and
residue-transitive at every modulus.  This is checked by computer, not in Lean.
* Agent report: `transitive.md` §2.3.
* Independent checks: `scripts/amusical/pp57/` (`pp_check.py`: domains and images partition `ℤ`,
  strongly connected at 8 further moduli up to `359100`, teeth on `κ` and `U`; `pp_lemmaE.py`).

**Why it cannot transfer to `U`** (agent Theorems L and M, paper proofs).  `U` is weakly
sign-uniform: for each prime, its slopes never change valuation sign.  For such maps no orbit
stays in the linear pieces forever.  For `U` this is `amusical_not_eventually_linear`: its one
linear piece `2n ↦ 3n` lowers `v₂`.  Moreover, an invariant measure of full support rules out
every open cone and every open transversal.  So a certificate for `U` must be a set with no
residue class inside it.

Summary: `RESEARCH-2026-10-13-amusical-single-chain.md` §16.  Treadmill target
(`KICKOFF-2026-10-13-amusical-pingpong.md`): close every `sorry` here.
-/

namespace CollatzMoonshot.Amusical

/-- The phase subgroup `K = ⟨8⟩ ≤ (ℤ/19)ˣ`, as residues. -/
def phaseK : Finset ℤ := {1, 7, 8, 11, 12, 18}

/-- The coset `B = 15 K`. -/
def phaseB : Finset ℤ := {4, 6, 9, 10, 13, 15}

/-- `σ` runs the ping-pong engine on the engine domain. -/
structure RunsPingPong (σ : ℤ → ℤ) : Prop where
  stepA : ∀ x, x % 5 = 0 → x % 19 ∈ phaseK → 5 * σ x = 21 * x
  stepAB : ∀ x, x % 5 ≠ 0 → x % 7 = 0 → x % 19 = 1 → σ x = 15 * x
  stepB : ∀ x, x % 7 = 0 → x % 19 ∈ phaseB → 7 * σ x = 75 * x
  stepBA : ∀ x, x % 7 ≠ 0 → x % 5 = 0 → x % 19 ∈ phaseB → σ x = 3 * x

/-- `x` lies in the domain of one of the four engine pieces. -/
def InEngine (x : ℤ) : Prop :=
  (x % 5 = 0 ∧ x % 19 ∈ phaseK) ∨ (x % 5 ≠ 0 ∧ x % 7 = 0 ∧ x % 19 = 1) ∨
    (x % 7 = 0 ∧ x % 19 ∈ phaseB) ∨ (x % 7 ≠ 0 ∧ x % 5 = 0 ∧ x % 19 ∈ phaseB)

/-- A seed: `v₅ x` odd, `7 ∤ x`, `x · 8^(v₅ x) ≡ 1 (mod 19)`. -/
def PingPongSeed (x : ℤ) : Prop :=
  x ≠ 0 ∧ Odd (padicValInt 5 x) ∧ x % 7 ≠ 0 ∧ x * 8 ^ padicValInt 5 x % 19 = 1

/-- **Target (Lemma E).**  A seed never leaves the engine.  Paper proof: with `A = v₅ x`,
`A` steps of `21/5` take `(v₅, v₇)` from `(A, 0)` to `(0, A)` with the phase multiplied by
`8^A`, ending at phase `1`.  Then `15` gives `(1, A)` at phase `15`, and `A` steps of `75/7`
give `(2A + 1, 0)`
with phase in `B`.  Finally `3` lands on a seed with `A' = 2A + 1`, since
`7 · 8^(3A+1) ≡ 7 · 8⁴ ≡ 1 (mod 19)` for odd `A`. -/
theorem pingPong_seed_inEngine {σ : ℤ → ℤ} (h : RunsPingPong σ) {x : ℤ}
    (hx : PingPongSeed x) (n : ℕ) : InEngine (σ^[n] x) := by
  sorry

/-- **Target.**  Every permutation running the engine has infinitely many orbits.  Paper proof:
for a seed `x` with `3 ∤ x`, `σ⁻¹ x` is not engine-forever (engine images are multiples of
`3`), so `x` is the first engine-forever point of its orbit.  Two such seeds on one orbit would
both be first, so they lie on distinct orbits.  There are infinitely many: every
`x ≡ 4705 (mod 9975)` is a seed prime to `3` (`9975 = 3 · 25 · 7 · 19`, `v₅ x = 1`). -/
theorem infinitelyManyOrbits_of_pingPong (σ : Equiv.Perm ℤ) (h : RunsPingPong σ) :
    {O : Set ℤ | ∃ x, O = permOrbit σ x}.Infinite := by
  sorry

/-- **Target (Theorem L for `U`).**  No nonzero orbit of `U` stays in its linear piece
`2n ↦ 3n` forever: each such step lowers `v₂`. -/
theorem amusical_not_eventually_linear {x : ℤ} (hx : x ≠ 0) (N : ℕ) :
    ¬ ∀ k ≥ N, amusical^[k] x % 2 = 0 := by
  intro hlinear
  have hnonzero (k : ℕ) : amusical^[k] x ≠ 0 := by
    intro hk
    apply hx
    apply (amusical_injective.iterate k)
    rw [hk]
    exact (Function.iterate_fixed (by simp [amusical]) k).symm
  have hvaluation_step {y : ℤ} (hy : y ≠ 0) (heven : y % 2 = 0) :
      padicValInt 2 y = padicValInt 2 (amusical y) + 1 := by
    have hnext : amusical y ≠ 0 := by
      intro hzero
      apply hy
      apply amusical_injective
      simpa [amusical] using hzero
    have heq : 2 * amusical y = 3 * y := by
      rw [amusical]
      simp only [heven, if_pos]
      have hdiv : y / 2 * 2 = y := Int.ediv_mul_cancel (Int.dvd_iff_emod_eq_zero.mpr heven)
      linear_combination 3 * hdiv
    have htwo : (2 : ℤ) ≠ 0 := by norm_num
    have hthree : (3 : ℤ) ≠ 0 := by norm_num
    have hv := congrArg (padicValInt 2) heq
    rw [padicValInt.mul htwo hnext, padicValInt.mul hthree hy] at hv
    have hvaltwo : padicValInt 2 (2 : ℤ) = 1 := padicValInt.self (by norm_num)
    have hvalthree : padicValInt 2 (3 : ℤ) = 0 :=
      padicValInt.eq_zero_of_not_dvd (by norm_num)
    simp only [hvaltwo, hvalthree, zero_add] at hv
    omega
  let y := amusical^[N] x
  have hy : y ≠ 0 := hnonzero N
  have heven (k : ℕ) : amusical^[k] y % 2 = 0 := by
    rw [show amusical^[k] y = amusical^[N + k] x by
      change amusical^[k] (amusical^[N] x) = amusical^[N + k] x
      rw [← Function.iterate_add_apply, Nat.add_comm]]
    exact hlinear (N + k) (by omega)
  have hdrop (k : ℕ) : padicValInt 2 y = k + padicValInt 2 (amusical^[k] y) := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        have hkzero : amusical^[k] y ≠ 0 := by
          intro hzero
          apply hnonzero (N + k)
          simpa [y, ← Function.iterate_add_apply, Nat.add_comm] using hzero
        calc
          padicValInt 2 y = k + padicValInt 2 (amusical^[k] y) := ih
          _ = k + (padicValInt 2 (amusical (amusical^[k] y)) + 1) := by
            rw [hvaluation_step hkzero (heven k)]
          _ = k + 1 + padicValInt 2 (amusical (amusical^[k] y)) := by omega
  have := hdrop (padicValInt 2 y + 1)
  omega

end CollatzMoonshot.Amusical
