/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalFormalMin.Bookkeeping
import CollatzMoonshot.AmusicalFormalMin.TwoVisit

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
host); Proposition G1 kernel-checked 2026-10-14 (`AmusicalFormalMin/TwoVisit.lean`).
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

theorem kBwd_forward_iterate (x : ℤ) (j : ℕ) :
    kBwd (amusical^[j] x) j = kFwd x j := by
  unfold kBwd kFwd
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  rw [amusicalInv_iterate_forward_iterate x j (j - 1 - i + 1) (by omega)]
  congr 2
  omega

/-- **Proved.**  An orbit contains at most one formal minimum.  Paper proof: if `y = Uʲ x` with
`j > 0`, the `j` steps before `y` are the `j` steps after `x`, so `kBwd y j = kFwd x j`, and the
two conditions at `t = j` contradict.  `j < 0` is symmetric. -/
theorem formalMin_unique {x : ℤ} {j : ℤ} (hx : FormalMin x)
    (hy : FormalMin ((amusicalPerm ^ j) x)) : j = 0 := by
  cases j with
  | ofNat n =>
      by_cases hn : n = 0
      · simp [hn]
      · have hnpos : 1 ≤ n := by omega
        have hxy := hx n hnpos
        have hyy := hy n hnpos
        have hpow : (amusicalPerm ^ Int.ofNat n) x = amusical^[n] x := by
          rw [Int.ofNat_eq_coe, amusical_iterate_eq_perm_pow]
        rw [hpow, kBwd_forward_iterate] at hyy
        exact absurd (hxy.1.trans hyy.2) (lt_irrefl _)
  | negSucc n =>
      set y := (amusicalPerm ^ Int.negSucc n) x with hy_def
      have hforward : amusical^[n + 1] y = x := by
        rw [amusical_iterate_eq_perm_pow, hy_def, ← Equiv.Perm.mul_apply, ← zpow_add]
        have h0 : ((n + 1 : ℕ) : ℤ) + Int.negSucc n = 0 := by
          rw [Int.negSucc_eq]; push_cast; ring
        rw [h0, zpow_zero, Equiv.Perm.one_apply]
      have hxx := hx (n + 1) (by omega)
      have hyy := hy (n + 1) (by omega)
      rw [← hforward, kBwd_forward_iterate] at hxx
      exact absurd (hyy.1.trans hxx.2) (lt_irrefl _)

/-- **Proved.**  A periodic point is not a formal minimum.  Paper proof: with period `p` the `p`
steps before `x` are the `p` steps after it, so `kBwd x p = kFwd x p`, and the two conditions at
`t = p` contradict. -/
theorem not_formalMin_of_periodic {x : ℤ} {p : ℕ} (hp : 0 < p) (h : amusical^[p] x = x) :
    ¬ FormalMin x := by
  intro hx
  have hf := hx p hp
  have hk := kBwd_forward_iterate x p
  rw [h] at hk
  rw [hk] at hf
  exact absurd (hf.1.trans hf.2) (lt_irrefl _)

/-- **Proved.**  `U` is odd and preserves parity, so negation preserves every bit count. -/
theorem formalMin_neg (x : ℤ) : FormalMin (-x) ↔ FormalMin x := by
  have hkFwd (y : ℤ) (t : ℕ) : kFwd (-y) t = kFwd y t := by
    unfold kFwd
    apply Finset.sum_congr rfl
    intro i _
    rw [amusical_iterate_neg, stepBits_neg]
  have hkBwd (y : ℤ) (t : ℕ) : kBwd (-y) t = kBwd y t := by
    unfold kBwd
    apply Finset.sum_congr rfl
    intro i _
    rw [amusicalInv_iterate_neg, stepBits_neg]
  simp only [FormalMin, hkFwd, hkBwd]

/-- **Proved.**  Infinitely many nonnegative formal minima give infinitely many orbits on `ℕ`,
since each orbit holds at most one (`formalMin_unique`). -/
theorem infinitelyManyOrbits_of_formalMin_infinite
    (h : {n : ℕ | FormalMin (n : ℤ)}.Infinite) : AmusicalInfinitelyManyOrbits := by
  have horbit : Set.InjOn (fun n : ℕ => amusicalOrbit (n : ℤ))
      {n : ℕ | FormalMin (n : ℤ)} := by
    intro a ha b hb hab
    have hbmem : (b : ℤ) ∈ amusicalOrbit (a : ℤ) := by
      have horb : amusicalOrbit (a : ℤ) = amusicalOrbit (b : ℤ) := hab
      rw [horb]
      exact mem_amusicalOrbit_self b
    obtain ⟨j, hj⟩ := hbmem
    have hj' : (amusicalPerm ^ j) (a : ℤ) = b := hj
    have hb' : FormalMin ((amusicalPerm ^ j) (a : ℤ)) := by
      rw [hj']
      exact hb
    have hj0 := formalMin_unique ha hb'
    subst hj0
    simpa using hj'
  refine (h.image horbit).mono ?_
  rintro O ⟨n, hn, rfl⟩
  exact ⟨n, by positivity, rfl⟩

/-- **Proved.**  The formal walk can disagree with the true order: `U¹² 31 = 30 < 31`, yet the
twelve steps spend only `19` bits and `2¹⁹ < 3¹²`. -/
theorem formal_walk_disagrees :
    amusical^[12] 31 = 30 ∧ kFwd 31 12 = 19 ∧ (2 : ℕ) ^ 19 < 3 ^ 12 := by
  decide

/-- **Proved (Proposition G1).**  If some orbit is infinite, a height `F(x mod M, ⌊log₂ x⌋)` on
the positive integers whose cocycle along orbits is bounded by `C` is bounded.  Proof:
(1) *two-visit lemma* (`TwoVisit.exists_two_visit`): for large `s` and residues `r, r'` there
are `x ≡ r`, `Uʲ x ≡ r'`, both in `[2ˢ, 2ˢ⁺¹)`.  Marker words fix the residue mod `2^a 3^b`, a
fixed-shape connector steers the prime-to-`6` part, and a minimal run of even steps puts the
slope in `[1, 3/2)`, so no irrationality input is needed.
(2) A positive aperiodic orbit visits every block above its start
(`TwoVisit.orbit_visits_block`), since a step from below `2ˢ` stays below `2ˢ⁺¹`.
(3) Chain these: `|F| ≤ |F(x₀)| + 2C` at large scales, and finitely many values below. -/
theorem coarse_quasiInvariant_bounded (M : ℕ) [NeZero M] (F : ZMod M → ℕ → ℝ) (C : ℝ)
    (hq : ∀ (x : ℤ) (j : ℕ), 1 ≤ x →
      |F (amusical^[j] x : ZMod M) (Nat.log 2 (amusical^[j] x).toNat) -
        F (x : ZMod M) (Nat.log 2 x.toNat)| ≤ C)
    (hinf : ∃ x : ℤ, ∀ p : ℕ, 0 < p → amusical^[p] x ≠ x) :
    ∃ B : ℝ, ∀ x : ℤ, 1 ≤ x → |F (x : ZMod M) (Nat.log 2 x.toNat)| ≤ B := by
  obtain ⟨x₀, hx₀, hap⟩ := TwoVisit.exists_pos_aperiodic hinf
  obtain ⟨S, hS⟩ := TwoVisit.two_visit_uniform M
  have hlog : ∀ (y : ℤ) (s : ℕ), 2 ^ s ≤ y → y < 2 ^ (s + 1) → Nat.log 2 y.toNat = s := by
    intro y s h1 h2
    have hy : ((y.toNat : ℕ) : ℤ) = y :=
      Int.toNat_of_nonneg (le_trans (by positivity) h1)
    apply Nat.log_eq_of_pow_le_of_lt_pow
    · exact_mod_cast (hy ▸ h1 : (2 : ℤ) ^ s ≤ (y.toNat : ℤ))
    · exact_mod_cast (hy ▸ h2 : (y.toNat : ℤ) < 2 ^ (s + 1))
  have hblock : ∀ y : ℤ, 1 ≤ y →
      2 ^ Nat.log 2 y.toNat ≤ y ∧ y < 2 ^ (Nat.log 2 y.toNat + 1) := by
    intro y hy
    have hy' : ((y.toNat : ℕ) : ℤ) = y := Int.toNat_of_nonneg (by omega)
    have hne : y.toNat ≠ 0 := by omega
    constructor
    · have := Nat.pow_log_le_self 2 hne
      rw [← hy']
      exact_mod_cast this
    · have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) y.toNat
      rw [← hy']
      exact_mod_cast this
  set S' := max S (Nat.log 2 x₀.toNat + 1) with hS'
  set A := |F (x₀ : ZMod M) (Nat.log 2 x₀.toNat)| with hA
  set T := ∑ ρ : ZMod M, ∑ s ∈ Finset.range S', |F ρ s| with hT
  refine ⟨max (A + 2 * C) T, fun x hx => ?_⟩
  set s := Nat.log 2 x.toNat with hs_def
  by_cases hs : S' ≤ s
  · obtain ⟨hxlo, hxhi⟩ := hblock x hx
    have hx₀s : x₀ < 2 ^ s := by
      have h1 := (hblock x₀ (by omega)).2
      have h2 : (2 : ℤ) ^ (Nat.log 2 x₀.toNat + 1) ≤ 2 ^ s :=
        pow_le_pow_right₀ (by norm_num) (le_trans (le_max_right _ _) hs)
      linarith
    obtain ⟨j₀, hj₀lo, hj₀hi⟩ := TwoVisit.orbit_visits_block hx₀ hap s hx₀s
    obtain ⟨y, j, h1, h2, h3, h4, h5, h6⟩ :=
      hS s (le_trans (le_max_left _ _) hs) (x : ZMod M) (amusical^[j₀] x₀ : ZMod M)
    have hy1 : 1 ≤ y := le_trans (one_le_pow₀ (by norm_num)) h1
    have e1 := hq x₀ j₀ (by omega)
    have e2 := hq y j hy1
    rw [hlog _ _ hj₀lo hj₀hi] at e1
    rw [hlog _ _ h3 h4, hlog _ _ h1 h2, h5, h6] at e2
    apply le_max_of_le_left
    have hA' := abs_le.mp (le_refl A)
    rw [hA] at hA'
    rw [abs_le] at e1 e2 ⊢
    constructor <;> linarith [hA'.1, hA'.2, e1.1, e1.2, e2.1, e2.2]
  · apply le_max_of_le_right
    have hsm : s ∈ Finset.range S' := Finset.mem_range.mpr (by omega)
    calc
      |F (x : ZMod M) s| ≤ ∑ s' ∈ Finset.range S', |F (x : ZMod M) s'| :=
        Finset.single_le_sum (fun i _ => abs_nonneg (F (x : ZMod M) i)) hsm
      _ ≤ T :=
        Finset.single_le_sum (f := fun ρ => ∑ s' ∈ Finset.range S', |F ρ s'|)
          (fun i _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ _)

end CollatzMoonshot.Amusical
