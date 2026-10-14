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

Summary: `RESEARCH-2026-10-13-amusical-single-chain.md` §16.  Kernel-checked 2026-10-13 by the
pingpong treadmill (`HANDOFF-amusical-pingpong.md`).
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

/-- **Proved (Lemma E).**  A seed never leaves the engine.  Paper proof: with `A = v₅ x`,
`A` steps of `21/5` take `(v₅, v₇)` from `(A, 0)` to `(0, A)` with the phase multiplied by
`8^A`, ending at phase `1`.  Then `15` gives `(1, A)` at phase `15`, and `A` steps of `75/7`
give `(2A + 1, 0)`
with phase in `B`.  Finally `3` lands on a seed with `A' = 2A + 1`, since
`7 · 8^(3A+1) ≡ 7 · 8⁴ ≡ 1 (mod 19)` for odd `A`. -/
theorem pingPong_seed_inEngine {σ : ℤ → ℤ} (h : RunsPingPong σ) {x : ℤ}
    (hx : PingPongSeed x) (n : ℕ) : InEngine (σ^[n] x) := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have seed_cycle {x : ℤ} (hx : PingPongSeed x) :
      PingPongSeed (σ^[2 * padicValInt 5 x + 2] x) ∧
        ∀ j < 2 * padicValInt 5 x + 2, InEngine (σ^[j] x) := by
    let A := padicValInt 5 x
    have hAodd : Odd A := hx.2.1
    have hApos : 0 < A := by
      obtain ⟨q, hq⟩ := hAodd
      omega
    have hv7x : padicValInt 7 x = 0 := by
      by_contra hne
      have hpos : 0 < padicValInt 7 x := by omega
      exact hx.2.2.1 ((emod_eq_zero_iff_padicValInt_pos hx.1).2 hpos)
    have runA (j : ℕ) (hj : j ≤ A) :
        σ^[j] x ≠ 0 ∧ padicValInt 5 (σ^[j] x) = A - j ∧
          padicValInt 7 (σ^[j] x) = j ∧
            (σ^[j] x * 8 ^ (A - j)) % 19 = 1 := by
      induction j with
      | zero =>
          simp only [Function.iterate_zero_apply, id_eq, Nat.sub_zero]
          exact ⟨hx.1, by simp [A], hv7x, hx.2.2.2⟩
      | succ j ih =>
          have hjA : j ≤ A := by omega
          have hjlt : j < A := by omega
          obtain ⟨hy0, hy5, hy7, hyphase⟩ := ih hjA
          have hy5pos : 0 < padicValInt 5 (σ^[j] x) := by
            rw [hy5]
            omega
          have hy5zero : σ^[j] x % 5 = 0 :=
            (emod_eq_zero_iff_padicValInt_pos hy0).2 hy5pos
          have hyK : σ^[j] x % 19 ∈ phaseK := by
            simpa [phaseK] using phaseK_of_mul_pow_eight_emod_eq_one hyphase
          have hstep := h.stepA (σ^[j] x) hy5zero hyK
          obtain ⟨hnext0, hnext5, hnext7⟩ := valuation_stepA hy0 hstep
          have hcount :
              (σ^[j] x * 8 ^ ((A - (j + 1)) + 1)) % 19 = (1 : ℤ) % 19 := by
            rw [← show A - j = (A - (j + 1)) + 1 by omega]
            simpa using hyphase
          have hnextphase := phase_countdown_step (Or.inl hstep) hcount
          rw [Function.iterate_succ_apply']
          refine ⟨hnext0, ?_, ?_, ?_⟩
          · omega
          · omega
          · simpa using hnextphase
    obtain ⟨hy0, hy5, hy7, hyphase⟩ := runA A le_rfl
    have hy5' : padicValInt 5 (σ^[A] x) = 0 := by simpa using hy5
    have hy5ne : σ^[A] x % 5 ≠ 0 := by
      intro hzero
      have hpos := (emod_eq_zero_iff_padicValInt_pos hy0).1 hzero
      rw [hy5'] at hpos
      omega
    have hy7zero : σ^[A] x % 7 = 0 := by
      apply (emod_eq_zero_iff_padicValInt_pos hy0).2
      rw [hy7]
      exact hApos
    have hyphase_one : σ^[A] x % 19 = 1 := by
      simpa using hyphase
    have hAB : σ^[A + 1] x = 15 * σ^[A] x := by
      rw [Function.iterate_succ_apply']
      exact h.stepAB (σ^[A] x) hy5ne hy7zero hyphase_one
    have h15v5 : padicValInt 5 (15 : ℤ) = 1 := by
      rw [show (15 : ℤ) = 3 * 5 by norm_num,
        padicValInt.mul (by norm_num) (by norm_num)]
      have h5 : padicValInt 5 (5 : ℤ) = 1 := padicValInt.self (p := 5) (by norm_num)
      rw [padicValInt.eq_zero_of_not_dvd (by norm_num), h5]
    have h15v7 : padicValInt 7 (15 : ℤ) = 0 :=
      padicValInt.eq_zero_of_not_dvd (by norm_num)
    have hz0 : σ^[A + 1] x ≠ 0 := by
      rw [hAB]
      exact mul_ne_zero (by norm_num) hy0
    have hz5 : padicValInt 5 (σ^[A + 1] x) = 1 := by
      rw [hAB, padicValInt.mul (by norm_num) hy0, h15v5, hy5]
      omega
    have hz7 : padicValInt 7 (σ^[A + 1] x) = A := by
      rw [hAB, padicValInt.mul (by norm_num) hy0, h15v7, hy7]
      omega
    have hzphase : σ^[A + 1] x % 19 ∈ phaseB := by
      rw [hAB]
      simpa [phaseB] using phaseAB_step hyphase_one
    have hzmod : σ^[A + 1] x ≡ 15 [ZMOD 19] := by
      rw [hAB]
      have hymod : σ^[A] x ≡ 1 [ZMOD 19] := by
        change σ^[A] x % 19 = (1 : ℤ) % 19
        simpa using hyphase_one
      simpa using hymod.mul_left 15
    have hzcount :
        (σ^[A + 1] x * 8 ^ A) % 19 = (15 * 8 ^ A) % 19 :=
      (hzmod.mul_right _).eq
    have runB (j : ℕ) (hj : j ≤ A) :
        σ^[A + 1 + j] x ≠ 0 ∧ padicValInt 7 (σ^[A + 1 + j] x) = A - j ∧
          padicValInt 5 (σ^[A + 1 + j] x) = 1 + 2 * j ∧
            σ^[A + 1 + j] x % 19 ∈ phaseB ∧
              (σ^[A + 1 + j] x * 8 ^ (A - j)) % 19 =
                (15 * 8 ^ A) % 19 := by
      induction j with
      | zero => simpa using ⟨hz0, hz7, hz5, hzphase, hzcount⟩
      | succ j ih =>
          have hjA : j ≤ A := by omega
          have hjlt : j < A := by omega
          obtain ⟨hy0, hy7, hy5, hyphase, hycount⟩ := ih hjA
          have hy7pos : 0 < padicValInt 7 (σ^[A + 1 + j] x) := by
            rw [hy7]
            omega
          have hy7zero : σ^[A + 1 + j] x % 7 = 0 :=
            (emod_eq_zero_iff_padicValInt_pos hy0).2 hy7pos
          have hstep := h.stepB (σ^[A + 1 + j] x) hy7zero hyphase
          obtain ⟨hnext0, hnext7, hnext5⟩ := valuation_stepB hy0 hstep
          have hyphase' :
              σ (σ^[A + 1 + j] x) % 19 ∈ phaseB := by
            apply phaseB_step (by simpa [phaseB] using hyphase) hstep
          have hcount :
              (σ^[A + 1 + j] x * 8 ^ ((A - (j + 1)) + 1)) % 19 =
                (15 * 8 ^ A) % 19 := by
            rw [← show A - j = (A - (j + 1)) + 1 by omega]
            exact hycount
          have hnextcount := phase_countdown_step (Or.inr hstep) hcount
          rw [show A + 1 + (j + 1) = (A + 1 + j) + 1 by omega,
            Function.iterate_succ_apply']
          refine ⟨hnext0, ?_, ?_, hyphase', hnextcount⟩ <;> omega
    obtain ⟨hw0, hw7, hw5, hwphase, hwcount⟩ := runB A le_rfl
    have hw7' : padicValInt 7 (σ^[A + 1 + A] x) = 0 := by simpa using hw7
    have hw7ne : σ^[A + 1 + A] x % 7 ≠ 0 := by
      intro hzero
      have hpos := (emod_eq_zero_iff_padicValInt_pos hw0).1 hzero
      rw [hw7'] at hpos
      omega
    have hw5zero : σ^[A + 1 + A] x % 5 = 0 := by
      apply (emod_eq_zero_iff_padicValInt_pos hw0).2
      rw [hw5]
      omega
    have hBAstep : σ (σ^[A + 1 + A] x) = 3 * σ^[A + 1 + A] x :=
      h.stepBA (σ^[A + 1 + A] x) hw7ne hw5zero hwphase
    have hreturn : σ^[2 * A + 2] x = 3 * σ^[A + 1 + A] x := by
      rw [show 2 * A + 2 = (A + 1 + A) + 1 by omega,
        Function.iterate_succ_apply']
      exact hBAstep
    have hreturn0 : σ^[2 * A + 2] x ≠ 0 := by
      rw [hreturn]
      exact mul_ne_zero (by norm_num) hw0
    have h3v5 : padicValInt 5 (3 : ℤ) = 0 :=
      padicValInt.eq_zero_of_not_dvd (by norm_num)
    have h3v7 : padicValInt 7 (3 : ℤ) = 0 :=
      padicValInt.eq_zero_of_not_dvd (by norm_num)
    have hreturn5 : padicValInt 5 (σ^[2 * A + 2] x) = 2 * A + 1 := by
      rw [hreturn, padicValInt.mul (by norm_num) hw0, h3v5, hw5]
      omega
    have hreturn7 : padicValInt 7 (σ^[2 * A + 2] x) = 0 := by
      rw [hreturn, padicValInt.mul (by norm_num) hw0, h3v7, hw7]
      omega
    have hreturn7ne : σ^[2 * A + 2] x % 7 ≠ 0 := by
      intro hzero
      have hpos := (emod_eq_zero_iff_padicValInt_pos hreturn0).1 hzero
      omega
    have hwmod : σ^[A + 1 + A] x ≡ 15 * 8 ^ A [ZMOD 19] := by
      change σ^[A + 1 + A] x % 19 = (15 * 8 ^ A) % 19
      simpa using hwcount
    have hreturnmod : σ^[2 * A + 2] x ≡ 45 * 8 ^ A [ZMOD 19] := by
      rw [hreturn]
      convert hwmod.mul_left 3 using 1 <;> ring
    have hfinal_numeric : (45 : ℤ) * 8 ^ (3 * A + 1) ≡ 1 [ZMOD 19] := by
      obtain ⟨q, hq⟩ := hAodd
      rw [hq, show 3 * (2 * q + 1) + 1 = 6 * q + 4 by omega, pow_add]
      have hperiod : (8 : ℤ) ^ (6 * q) ≡ 1 [ZMOD 19] := by
        rw [pow_mul]
        simpa using (show (8 : ℤ) ^ 6 ≡ 1 [ZMOD 19] by norm_num).pow q
      exact (hperiod.mul_right ((8 : ℤ) ^ 4)).mul_left 45 |>.trans (by norm_num)
    have hreturnphase :
        (σ^[2 * A + 2] x * 8 ^ padicValInt 5 (σ^[2 * A + 2] x)) % 19 = 1 := by
      rw [hreturn5]
      calc
        (σ^[2 * A + 2] x * 8 ^ (2 * A + 1)) % 19 =
            ((45 * 8 ^ A) * 8 ^ (2 * A + 1)) % 19 :=
          (hreturnmod.mul_right _).eq
        _ = (45 * 8 ^ (3 * A + 1)) % 19 := by
          congr 1
          rw [mul_assoc, ← pow_add]
          congr 2
          omega
        _ = 1 := hfinal_numeric.eq
    have hnextseed : PingPongSeed (σ^[2 * A + 2] x) := by
      refine ⟨hreturn0, ?_, hreturn7ne, hreturnphase⟩
      rw [hreturn5]
      exact ⟨A, rfl⟩
    refine ⟨by simpa [A] using hnextseed, ?_⟩
    intro j hj
    by_cases hjA : j ≤ A
    · obtain ⟨hy0, hy5, hy7, hyphase⟩ := runA j hjA
      by_cases hjlt : j < A
      · apply Or.inl
        have hy5zero : σ^[j] x % 5 = 0 := by
          apply (emod_eq_zero_iff_padicValInt_pos hy0).2
          rw [hy5]
          omega
        exact ⟨hy5zero, by
          simpa [phaseK] using phaseK_of_mul_pow_eight_emod_eq_one hyphase⟩
      · have hjeq : j = A := by omega
        subst j
        exact Or.inr (Or.inl ⟨hy5ne, hy7zero, hyphase_one⟩)
    · let k := j - (A + 1)
      have hjlo : A + 1 ≤ j := by omega
      have hjk : A + 1 + k = j := by simp [k, Nat.add_sub_of_le hjlo]
      have hkA : k ≤ A := by
        dsimp [k]
        omega
      obtain ⟨hy0, hy7, hy5, hyphase, _⟩ := runB k hkA
      rw [← hjk]
      by_cases hklt : k < A
      · apply Or.inr
        apply Or.inr
        apply Or.inl
        refine ⟨(emod_eq_zero_iff_padicValInt_pos hy0).2 ?_, hyphase⟩
        rw [hy7]
        omega
      · apply Or.inr
        apply Or.inr
        apply Or.inr
        refine ⟨?_, (emod_eq_zero_iff_padicValInt_pos hy0).2 ?_, hyphase⟩
        intro hzero
        have hpos := (emod_eq_zero_iff_padicValInt_pos hy0).1 hzero
        rw [hy7] at hpos
        omega
        rw [hy5]
        omega
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
      let A := padicValInt 5 x
      obtain ⟨hnextseed, hinside⟩ := seed_cycle hx
      by_cases hn : n < 2 * A + 2
      · exact hinside n (by simpa [A] using hn)
      · have hlen : 0 < 2 * A + 2 := by omega
        have hsub : n - (2 * A + 2) < n := Nat.sub_lt (by omega) hlen
        have hrec := ih (n - (2 * A + 2)) hsub hnextseed
        have hnadd : n - (2 * A + 2) + (2 * A + 2) = n := by omega
        rw [← hnadd, Function.iterate_add_apply]
        simpa [A] using hrec

/-- **Proved.**  Every permutation running the engine has infinitely many orbits.  Paper proof:
for a seed `x` with `3 ∤ x`, `σ⁻¹ x` is not engine-forever (engine images are multiples of
`3`), so `x` is the first engine-forever point of its orbit.  Two such seeds on one orbit would
both be first, so they lie on distinct orbits.  There are infinitely many: every
`x ≡ 4705 (mod 9975)` is a seed prime to `3` (`9975 = 3 · 25 · 7 · 19`, `v₅ x = 1`). -/
theorem infinitelyManyOrbits_of_pingPong (σ : Equiv.Perm ℤ) (h : RunsPingPong σ) :
    {O : Set ℤ | ∃ x, O = permOrbit σ x}.Infinite := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have engine_image_three {y : ℤ} (hy : InEngine y) : σ y % 3 = 0 := by
    apply three_dvd_of_engine_equation
    rcases hy with hy | hy | hy | hy
    · exact Or.inl (h.stepA y hy.1 hy.2)
    · exact Or.inr (Or.inl (h.stepAB y hy.1 hy.2.1 hy.2.2))
    · exact Or.inr (Or.inr (Or.inl (h.stepB y hy.1 hy.2)))
    · exact Or.inr (Or.inr (Or.inr (h.stepBA y hy.1 hy.2.1 hy.2.2)))
  have iterate_eq_zpow (j : ℕ) (y : ℤ) : σ^[j] y = (σ ^ (j : ℤ)) y := by
    rw [zpow_natCast]
    induction j generalizing y with
    | zero => rfl
    | succ j ih =>
        rw [Function.iterate_succ_apply', ih, pow_succ', Equiv.Perm.mul_apply]
  have positive_zpow_three {y : ℤ} (hy : PingPongSeed y) (j : ℕ) (hj : 0 < j) :
      (σ ^ (j : ℤ)) y % 3 = 0 := by
    rw [← iterate_eq_zpow]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    rw [Function.iterate_succ_apply']
    exact engine_image_three (pingPong_seed_inEngine h hy k)
  have seed_eq_of_same_orbit {a b : ℤ} (ha : PingPongSeed a) (hb : PingPongSeed b)
      (ha3 : a % 3 ≠ 0) (hb3 : b % 3 ≠ 0)
      (horbit : permOrbit σ a = permOrbit σ b) : a = b := by
    have hbmem : b ∈ permOrbit σ a := by
      rw [horbit]
      exact ⟨0, by simp [permOrbit]⟩
    change ∃ r : ℤ, (σ ^ r) a = b at hbmem
    obtain ⟨r, hr⟩ := hbmem
    by_cases hr0 : r = 0
    · subst r
      simpa using hr
    · rcases lt_or_gt_of_ne (Ne.symm hr0) with hrpos | hrneg
      · have hrnat : ((r.toNat : ℕ) : ℤ) = r := Int.toNat_of_nonneg hrpos.le
        have hthree := positive_zpow_three ha r.toNat (by omega)
        rw [hrnat, hr] at hthree
        exact (hb3 hthree).elim
      · have hrnat : (((-r).toNat : ℕ) : ℤ) = -r :=
          Int.toNat_of_nonneg (neg_nonneg.mpr hrneg.le)
        have hback : (σ ^ (-r)) b = a := by
          rw [← hr, ← Equiv.Perm.mul_apply, ← zpow_add]
          simp
        have hthree := positive_zpow_three hb (-r).toNat (by omega)
        rw [hrnat, hback] at hthree
        exact (ha3 hthree).elim
  let seed : ℕ → ℤ := fun t => 4705 + 9975 * t
  have seed_spec (t : ℕ) : PingPongSeed (seed t) ∧ seed t % 3 ≠ 0 := by
    have hpos : 0 < seed t := by
      dsimp [seed]
      omega
    have hfactor : seed t = 5 * (941 + 1995 * t) := by
      dsimp [seed]
      push_cast
      ring
    have hinner0 : (941 + 1995 * (t : ℤ) : ℤ) ≠ 0 := by omega
    have hinnerv : padicValInt 5 (941 + 1995 * (t : ℤ)) = 0 := by
      apply padicValInt.eq_zero_of_not_dvd
      rw [Int.dvd_iff_emod_eq_zero]
      omega
    have hseedv : padicValInt 5 (seed t) = 1 := by
      rw [hfactor, padicValInt.mul (by norm_num) hinner0]
      have h5 : padicValInt 5 (5 : ℤ) = 1 := padicValInt.self (p := 5) (by norm_num)
      rw [h5, hinnerv]
    refine ⟨⟨ne_of_gt hpos, ?_, ?_, ?_⟩, ?_⟩
    · rw [hseedv]
      exact odd_one
    · dsimp [seed]
      omega
    · rw [hseedv]
      dsimp [seed]
      norm_num [Int.add_emod, Int.mul_emod]
    · dsimp [seed]
      omega
  have seed_injective : Function.Injective seed := by
    intro s t hst
    dsimp [seed] at hst
    omega
  have orbit_injective : Set.InjOn (permOrbit σ) (Set.range seed) := by
    intro a ha b hb hab
    obtain ⟨s, rfl⟩ := ha
    obtain ⟨t, rfl⟩ := hb
    exact seed_eq_of_same_orbit (seed_spec s).1 (seed_spec t).1
      (seed_spec s).2 (seed_spec t).2 hab
  have hseed : (Set.range seed).Infinite := Set.infinite_range_of_injective seed_injective
  refine (hseed.image orbit_injective).mono ?_
  rintro O ⟨a, _, rfl⟩
  exact ⟨a, rfl⟩

/-- **Proved (Theorem L for `U`).**  No nonzero orbit of `U` stays in its linear piece
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
