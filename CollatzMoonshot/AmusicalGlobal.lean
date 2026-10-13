/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalWindow
import CollatzMoonshot.AmusicalWindowThree

/-!
# Global mechanisms for a seventh orbit, and why the cheap ones fail

A proof of Klamkin's problem (a), or even of a seventh orbit, needs an infinite set that meets
each orbit boundedly often.  The 2026-10-13 "global" agent tested every mechanism class it could
name against the rewired `U` of `AmusicalRewireRatio.lean` (same values except at `O(log² N)`
points below `N`, with bounded ratio, and one infinite orbit).  This file holds the pieces that
are theorems.

* **Kohl's mirror (Lemma K).**  `|x| ≤ 4^ℓ (|Uˡ x − x| + 1)`, because the slope of `Uˡ` on each
  cylinder is `3ˡ/2^B ≠ 1` (`abs_le_four_pow_mul_iterate_sub`).  So `Uˡ x = x + d` has finitely
  many solutions (`amusical_iterate_eq_add_finite`): `U` has no translation piece, which is the
  ingredient of Kohl's one-orbit permutation `ω`.  The absence does not bite: the rewired `U`
  satisfies the same time separation.
* **No residue-definable transversal (Proposition P).**  Every residue class contains arbitrarily
  large `x` whose forward orbit visits the class at least `K + 1` times (`exists_many_returns`).
* **Survival (Proposition S).**  If forward and backward survivors (points never undercut later in
  that direction) have lower densities `a`, `b` with `a + b > f_L + b_L − f_L b_L`, Klamkin (a)
  holds (`infinitelyManyOrbits_of_survival`).  Survival is an infinite-horizon statistic, the one
  kind sparse rewiring changes; proving it is the late-drop (typicality) wall.
* **Commuting maps.**  A strictly increasing `g` commuting with `U` and moving every positive
  integer up would separate orbits (`infinitelyManyOrbits_of_commuting`).  The continuous
  candidates at window `2` are only `0, ±1, ±id, ±U` (`commuting_window_two`, exact).

Paper proofs: agent report `global.md` (2026-10-13), summarized in
`RESEARCH-2026-10-13-amusical-single-chain.md` §14; `commuting_window_two` re-derived by
`scripts/amusical/central_w2.py`.  Treadmill target (`KICKOFF-2026-10-13-amusical-global.md`):
close every `sorry` here.
-/

namespace CollatzMoonshot.Amusical

/-- The affine error in one forward branch is at most one. -/
private theorem amusical_step_affine (x : ℤ) :
    ∃ e : ℤ, |e| ≤ 1 ∧ 2 ^ stepBits x * amusical x = 3 * x + e := by
  unfold stepBits amusical
  split_ifs <;>
    first
    | exact ⟨0, by norm_num, by omega⟩
    | exact ⟨1, by norm_num, by omega⟩
    | exact ⟨-1, by norm_num, by omega⟩

/-- Iterating the branch formula produces a uniformly bounded affine error. -/
private theorem amusical_iterate_affine (l : ℕ) (x : ℤ) :
    ∃ B : ℕ, ∃ c : ℤ, l ≤ B ∧ B ≤ 2 * l ∧ |c| < 4 ^ l ∧
      2 ^ B * amusical^[l] x = 3 ^ l * x + c := by
  induction l with
  | zero =>
      exact ⟨0, 0, by norm_num⟩
  | succ l ih =>
      obtain ⟨B, c, hBl, hB, hc, heq⟩ := ih
      obtain ⟨e, he, hstep⟩ := amusical_step_affine (amusical^[l] x)
      refine ⟨B + stepBits (amusical^[l] x), 3 * c + 2 ^ B * e, ?_, ?_, ?_, ?_⟩
      · unfold stepBits
        split_ifs <;> omega
      · unfold stepBits
        split_ifs <;> omega
      · have hpowNat : 2 ^ B ≤ (4 : ℕ) ^ l := by
          calc
            2 ^ B ≤ 2 ^ (2 * l) := Nat.pow_le_pow_right (by norm_num) hB
            _ = 4 ^ l := by
              rw [show 2 * l = l * 2 by omega, pow_mul]
              simp [pow_two, ← mul_pow]
        have hpow : (2 : ℤ) ^ B ≤ 4 ^ l := by exact_mod_cast hpowNat
        calc
          |3 * c + 2 ^ B * e| ≤ |3 * c| + |2 ^ B * e| := abs_add_le _ _
          _ = 3 * |c| + 2 ^ B * |e| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ 3),
              abs_of_nonneg (by positivity : (0 : ℤ) ≤ 2 ^ B)]
          _ ≤ 3 * |c| + 4 ^ l := by
            have he' : 2 ^ B * |e| ≤ (2 : ℤ) ^ B := by
              exact mul_le_of_le_one_right (by positivity) he
            omega
          _ < 4 ^ (l + 1) := by
            rw [pow_succ]
            have hfour : (0 : ℤ) < 4 ^ l := by positivity
            omega
      · rw [Function.iterate_succ_apply', pow_succ, pow_add]
        calc
          2 ^ B * 2 ^ stepBits (amusical^[l] x) * amusical (amusical^[l] x) =
              2 ^ B * (3 * amusical^[l] x + e) := by rw [mul_assoc, hstep]
          _ = 3 * (2 ^ B * amusical^[l] x) + 2 ^ B * e := by ring
          _ = 3 * (3 ^ l * x + c) + 2 ^ B * e := by rw [heq]
          _ = 3 ^ (l + 1) * x + (3 * c + 2 ^ B * e) := by ring

/-- The analogous affine ledger for backward iteration. -/
private theorem amusicalInv_iterate_affine (l : ℕ) (x : ℤ) :
    ∃ B : ℕ, ∃ c : ℤ, l ≤ B ∧ B ≤ 2 * l ∧ |c| < 4 ^ l ∧
      3 ^ l * amusicalInv^[l] x = 2 ^ B * x + c := by
  obtain ⟨B, c, hBl, hB, hc, heq⟩ := amusical_iterate_affine l (amusicalInv^[l] x)
  have hcancel : amusical^[l] (amusicalInv^[l] x) = x := by
    rw [amusical_iterate_eq_perm_pow, amusicalInv_iterate_eq_perm_pow]
    simp
  refine ⟨B, -c, hBl, hB, by simpa, ?_⟩
  rw [hcancel] at heq
  omega

private theorem one_le_abs_three_pow_sub_two_pow (l B : ℕ) (hB : 1 ≤ B) :
    1 ≤ |(3 : ℤ) ^ l - 2 ^ B| := by
  have h3 : Odd ((3 : ℤ) ^ l) := Odd.pow (by decide)
  have h2 : Even ((2 : ℤ) ^ B) := (even_two).pow_of_ne_zero (by omega)
  obtain ⟨k, hk⟩ := h3.sub_even h2
  exact Int.one_le_abs (by omega)

/-- **Target (Lemma K).**  A point is at most `4^ℓ` times its `ℓ`-step displacement, forward and
backward.  Paper proof: on the cylinder of its word, `2^B Uˡ x = 3ˡ x + c` with `B ≤ 2ℓ` and
`|c| ≤ ∑_{j<ℓ} 3^(ℓ−1−j) 4^j < 4^ℓ`, and `|3ˡ − 2^B| ≥ 1`; backward,
`3ˡ U⁻ˡ y = 2^B y − c'` likewise. -/
theorem abs_le_four_pow_mul_iterate_sub (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (x : ℤ) :
    |x| ≤ 4 ^ ℓ * (|amusical^[ℓ] x - x| + 1) ∧
      |x| ≤ 4 ^ ℓ * (|amusicalInv^[ℓ] x - x| + 1) := by
  obtain ⟨B, c, hBℓ, hB, hc, heq⟩ := amusical_iterate_affine ℓ x
  obtain ⟨B', c', hBℓ', hB', hc', heq'⟩ := amusicalInv_iterate_affine ℓ x
  have hpowNat : 2 ^ B ≤ (4 : ℕ) ^ ℓ := by
    calc
      2 ^ B ≤ 2 ^ (2 * ℓ) := Nat.pow_le_pow_right (by norm_num) hB
      _ = 4 ^ ℓ := by
        rw [show 2 * ℓ = ℓ * 2 by omega, pow_mul]
        simp [pow_two, ← mul_pow]
  have hpow : (2 : ℤ) ^ B ≤ 4 ^ ℓ := by exact_mod_cast hpowNat
  have hpow' : (3 : ℤ) ^ ℓ ≤ 4 ^ ℓ :=
    pow_le_pow_left₀ (a := (3 : ℤ)) (b := 4) (by norm_num) (by norm_num) ℓ
  constructor
  · have hslope := one_le_abs_three_pow_sub_two_pow ℓ B (hℓ.trans hBℓ)
    have hid : ((3 : ℤ) ^ ℓ - 2 ^ B) * x =
        2 ^ B * (amusical^[ℓ] x - x) - c := by
      linear_combination -heq
    calc
      |x| ≤ |(3 ^ ℓ - 2 ^ B) * x| := by
        rw [abs_mul]
        nlinarith [abs_nonneg x]
      _ = |2 ^ B * (amusical^[ℓ] x - x) - c| := by rw [hid]
      _ = |2 ^ B * (amusical^[ℓ] x - x) + -c| := by ring
      _ ≤ |2 ^ B * (amusical^[ℓ] x - x)| + |-c| := abs_add_le _ _
      _ = |2 ^ B * (amusical^[ℓ] x - x)| + |c| := by rw [abs_neg]
      _ = 2 ^ B * |amusical^[ℓ] x - x| + |c| := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ 2 ^ B)]
      _ ≤ 4 ^ ℓ * (|amusical^[ℓ] x - x| + 1) := by
        nlinarith [abs_nonneg (amusical^[ℓ] x - x)]
  · have hslope := one_le_abs_three_pow_sub_two_pow ℓ B' (hℓ.trans hBℓ')
    have hid : ((2 : ℤ) ^ B' - 3 ^ ℓ) * x =
        3 ^ ℓ * (amusicalInv^[ℓ] x - x) - c' := by
      linear_combination -heq'
    calc
      |x| ≤ |(2 ^ B' - 3 ^ ℓ) * x| := by
        rw [abs_mul, abs_sub_comm]
        nlinarith [abs_nonneg x]
      _ = |3 ^ ℓ * (amusicalInv^[ℓ] x - x) - c'| := by rw [hid]
      _ = |3 ^ ℓ * (amusicalInv^[ℓ] x - x) + -c'| := by ring
      _ ≤ |3 ^ ℓ * (amusicalInv^[ℓ] x - x)| + |-c'| := abs_add_le _ _
      _ = |3 ^ ℓ * (amusicalInv^[ℓ] x - x)| + |c'| := by rw [abs_neg]
      _ = 3 ^ ℓ * |amusicalInv^[ℓ] x - x| + |c'| := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ 3 ^ ℓ)]
      _ ≤ 4 ^ ℓ * (|amusicalInv^[ℓ] x - x| + 1) := by
        nlinarith [abs_nonneg (amusicalInv^[ℓ] x - x)]

/-- **Target.**  No power of `U` has a translation piece: `Uˡ x = x + d` has finitely many
solutions (all with `|x| ≤ 4^ℓ (|d| + 1)`, by Lemma K). -/
theorem amusical_iterate_eq_add_finite (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (d : ℤ) :
    {x : ℤ | amusical^[ℓ] x = x + d}.Finite := by
  let C : ℤ := 4 ^ ℓ * (|d| + 1)
  refine (Set.finite_Icc (-C) C).subset ?_
  intro x hx
  have hbound := (abs_le_four_pow_mul_iterate_sub ℓ hℓ x).1
  change amusical^[ℓ] x = x + d at hx
  rw [hx] at hbound
  have hbound' : |x| ≤ C := by simpa [C] using hbound
  exact (abs_le.mp hbound')

/-- **Target (Proposition P).**  Every residue class contains points `x ≥ N` whose first `T`
forward iterates visit the class at least `K + 1` times, so no eventually periodic infinite set
meets every orbit boundedly often.  Paper proof: write `M = 2^a 3^b M₀` with `gcd(M₀, 6) = 1`;
`Uⁱ x mod 2^a` is fixed by the next `a` symbols, `Uⁱ x mod 3^b` by the previous `b`, and the
branch maps act transitively on `ℤ/M₀` (`g_A⁻¹ g_B` is translation by `−2/3`).  Build a word
`p v₁ p ⋯ v_K p` with a marker `p` coding `r` and connectors `vⱼ` fixing the `M₀` part, then
prescribe its cylinder and `x mod 3^b M₀` by CRT. -/
theorem exists_many_returns (M : ℕ) (hM : 0 < M) (r : ℤ) (K N : ℕ) :
    ∃ x : ℤ, ∃ T : ℕ, (N : ℤ) ≤ x ∧
      K + 1 ≤ ((Finset.range T).filter fun i => amusical^[i] x ≡ r [ZMOD M]).card := by
  sorry

/-- `n` is never undercut going forward. -/
def FwdSurvivor (n : ℤ) : Prop :=
  ∀ t : ℕ, 1 ≤ t → n ≤ amusical^[t] n

/-- `n` is never undercut going backward. -/
def BwdSurvivor (n : ℤ) : Prop :=
  ∀ t : ℕ, 1 ≤ t → n ≤ amusicalInv^[t] n

open Classical in
/-- **Target (Proposition S).**  Survivor densities above `f_L + b_L − f_L b_L` give Klamkin (a).
Paper proof: orbit minima are `FS ∩ BS`, which contains `(FS_L ∩ BS_L) ∖ ((FS_L ∖ FS) ∪
(BS_L ∖ BS))`.  The window minima `FS_L ∩ BS_L` have density `f_L b_L` (`windowMinDensity`),
and `FS_L` has density `f_L` (the forward half of the same proof), so `FS_L ∖ FS` has upper
density `f_L − a`; the minima get lower density `a + b − f_L − b_L + f_L b_L > 0`. -/
theorem infinitelyManyOrbits_of_survival (L : ℕ) (a b : ℝ)
    (ha : ∀ᶠ X : ℕ in Filter.atTop,
      a * X ≤ ((Finset.range X).filter fun n : ℕ => FwdSurvivor n).card)
    (hb : ∀ᶠ X : ℕ in Filter.atTop,
      b * X ≤ ((Finset.range X).filter fun n : ℕ => BwdSurvivor n).card)
    (h : ((fwdSurv L + bwdSurv L - fwdSurv L * bwdSurv L : ℚ) : ℝ) < a + b) :
    AmusicalInfinitelyManyOrbits := by
  sorry

/-- **Target.**  A strictly increasing map commuting with `U` and raising every positive integer
separates orbits.  Paper proof: `g` also commutes with `U⁻¹`, so it maps the orbit of `m` onto the
orbit of `g m`, with minimum `g m > m`; the orbits of `m, g m, g² m, …` are distinct. -/
theorem infinitelyManyOrbits_of_commuting {g : ℤ → ℤ} (hg : ∀ n, g (amusical n) = amusical (g n))
    (hmono : StrictMono g) (hgt : ∀ n, 0 < n → n < g n) (hpos : ∀ n, 0 ≤ n → 0 ≤ g n)
    (hinf : ∃ n, 0 < n ∧ IsOrbitMin n ∧ (amusicalOrbit n).Infinite) :
    AmusicalInfinitelyManyOrbits := by
  sorry

/-- **Target (window-2 centralizer).**  A map commuting with `U` whose step symbol reads
`stepSym n` and `stepSym (U n)` is one of `0, 1, −1, id, −id, U, −U`.  Paper proof: the forward
itinerary of `g x` is the block code of that of `x`, so `g` maps each cycle point to an integer
periodic point of period dividing its period; by `amusical_periodic_mem` the image lies on the
nine known cycles.  Of the `3⁹` tables exactly these seven pass (`scripts/amusical/central_w2.py`),
and the table determines `g` since an integer is determined by its forward itinerary
(`reversor_eq_of_stepSym_eq` argument). -/
theorem commuting_window_two (f : Fin 3 → Fin 3 → Fin 3) {g : ℤ → ℤ}
    (hg : ∀ n, g (amusical n) = amusical (g n))
    (hloc : ∀ n, stepSym (g n) = f (stepSym n) (stepSym (amusical n))) :
    g = (fun _ => 0) ∨ g = (fun _ => 1) ∨ g = (fun _ => -1) ∨ g = id ∨ g = Neg.neg ∨
      g = amusical ∨ g = fun n => -amusical n := by
  sorry

end CollatzMoonshot.Amusical
