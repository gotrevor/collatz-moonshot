/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalWindow
import CollatzMoonshot.AmusicalWindowThree
import CollatzMoonshot.AmusicalGlobal.WindowTwo

/-!
# Global mechanisms for a seventh orbit, and why the cheap ones fail

A proof of Klamkin's problem (a), or even of a seventh orbit, needs an infinite set that meets
each orbit boundedly often.  The 2026-10-13 "global" agent tested every mechanism class it could
name against the rewired `U` of `AmusicalRewireRatio.lean` (same values except at `O(log² N)`
points below `N`, with bounded ratio, and one infinite orbit).  This file holds the pieces that
are theorems.

* **Kohl's mirror (Lemma K).**  `|x| ≤ 4^ℓ (|Uˡ x − x| + 1)`, because the slope of `Uˡ` on
  each cylinder is `3ˡ/2^B ≠ 1` (`abs_le_four_pow_mul_iterate_sub`).
  So `Uˡ x = x + d` has finitely
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
`scripts/amusical/central_w2.py`.  Kernel-checked 2026-10-13 by the global treadmill
(`HANDOFF-amusical-global.md`).
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

/-- **Proved (Lemma K).**  A point is at most `4^ℓ` times its `ℓ`-step displacement, forward and
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

/-- **Proved.**  No power of `U` has a translation piece: `Uˡ x = x + d` has finitely many
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

/-! ## Modular connectors for Proposition P -/

private def B (m : ℕ) (z : ZMod m) : ZMod m :=
  (3 * z + 1) * (4 : ZMod m)⁻¹

private def C (m : ℕ) (z : ZMod m) : ZMod m :=
  (3 * z - 1) * (4 : ZMod m)⁻¹

private def BI (m : ℕ) (z : ZMod m) : ZMod m :=
  (4 * z - 1) * (3 : ZMod m)⁻¹

private theorem left (m : ℕ) (h3 : IsUnit (3 : ZMod m))
    (h4 : IsUnit (4 : ZMod m)) : Function.LeftInverse (BI m) (B m) := by
  intro z
  dsimp [BI, B]
  calc
    (4 * ((3 * z + 1) * (4 : ZMod m)⁻¹) - 1) * (3 : ZMod m)⁻¹ =
        (((4 : ZMod m) * 4⁻¹) * (3 * z + 1) - 1) * 3⁻¹ := by ring
    _ = (3 * z) * 3⁻¹ := by rw [ZMod.mul_inv_of_unit 4 h4]; ring
    _ = z * ((3 : ZMod m) * 3⁻¹) := by ring
    _ = z := by rw [ZMod.mul_inv_of_unit 3 h3, mul_one]

private theorem right (m : ℕ) (h3 : IsUnit (3 : ZMod m))
    (h4 : IsUnit (4 : ZMod m)) : Function.RightInverse (BI m) (B m) := by
  intro z
  dsimp [BI, B]
  calc
    (3 * ((4 * z - 1) * (3 : ZMod m)⁻¹) + 1) * (4 : ZMod m)⁻¹ =
        (((3 : ZMod m) * 3⁻¹) * (4 * z - 1) + 1) * 4⁻¹ := by ring
    _ = (4 * z) * 4⁻¹ := by rw [ZMod.mul_inv_of_unit 3 h3]; ring
    _ = z * ((4 : ZMod m) * 4⁻¹) := by ring
    _ = z := by rw [ZMod.mul_inv_of_unit 4 h4, mul_one]

private theorem bic (m : ℕ) (h3 : IsUnit (3 : ZMod m))
    (h4 : IsUnit (4 : ZMod m)) (z : ZMod m) :
    BI m (C m z) = z - 2 * (3 : ZMod m)⁻¹ := by
  dsimp [BI, C]
  calc
    (4 * ((3 * z - 1) * (4 : ZMod m)⁻¹) - 1) * (3 : ZMod m)⁻¹ =
        (((4 : ZMod m) * 4⁻¹) * (3 * z - 1) - 1) * 3⁻¹ := by ring
    _ = (3 * z - 2) * 3⁻¹ := by rw [ZMod.mul_inv_of_unit 4 h4]; ring
    _ = z * ((3 : ZMod m) * 3⁻¹) - 2 * 3⁻¹ := by ring
    _ = z - 2 * 3⁻¹ := by rw [ZMod.mul_inv_of_unit 3 h3, mul_one]

private theorem bcycle (m : ℕ) [NeZero m] (h3 : IsUnit (3 : ZMod m))
    (h4 : IsUnit (4 : ZMod m)) : (B m)^[(m.factorial)] = id := by
  have hinj : Function.Injective (B m) := (left m h3 h4).injective
  simpa [ZMod.card] using
    (Function.injective_iff_iterate_factorial_card_eq_id.mp hinj)

private theorem connector_step (m : ℕ) [NeZero m] (h3 : IsUnit (3 : ZMod m))
    (h4 : IsUnit (4 : ZMod m)) (z : ZMod m) :
    (B m)^[(m.factorial - 1)] (C m z) = z - 2 * (3 : ZMod m)⁻¹ := by
  rw [← right m h3 h4 (C m z)]
  rw [← Function.iterate_succ_apply]
  have hfac : 0 < m.factorial := Nat.factorial_pos m
  have hs : (m.factorial - 1).succ = m.factorial := by omega
  rw [hs, bcycle m h3 h4]
  exact bic m h3 h4 z

private def branch (m : ℕ) (s : Fin 3) (z : ZMod m) : ZMod m :=
  ![fun z => 3 * z * (2 : ZMod m)⁻¹, B m, C m] s z

@[simp] private theorem branch_one (m : ℕ) (z : ZMod m) : branch m 1 z = B m z := by
  rfl

@[simp] private theorem branch_two (m : ℕ) (z : ZMod m) : branch m 2 z = C m z := by
  rfl

private def act (m : ℕ) : List (Fin 3) → ZMod m → ZMod m
  | [], z => z
  | s :: w, z => act m w (branch m s z)

private theorem act_append (m : ℕ) (u v : List (Fin 3)) (z : ZMod m) :
    act m (u ++ v) z = act m v (act m u z) := by
  induction u generalizing z with
  | nil => rfl
  | cons s u ih => simpa [act] using ih (branch m s z)

private theorem act_replicate_one (m n : ℕ) (z : ZMod m) :
    act m (List.replicate n (1 : Fin 3)) z = (B m)^[n] z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
      simp only [List.replicate_succ, act, branch_one, ih]
      rw [Function.iterate_succ_apply]

private def connectorUnit (m : ℕ) : List (Fin 3) :=
  (2 : Fin 3) :: List.replicate (m.factorial - 1) (1 : Fin 3)

private theorem act_connectorUnit (m : ℕ) [NeZero m]
    (h3 : IsUnit (3 : ZMod m)) (h4 : IsUnit (4 : ZMod m)) (z : ZMod m) :
    act m (connectorUnit m) z = z - 2 * (3 : ZMod m)⁻¹ := by
  simp only [connectorUnit, act, branch_two, act_replicate_one]
  exact connector_step m h3 h4 z

private def connectorCore (m q : ℕ) : List (Fin 3) :=
  (List.replicate q (connectorUnit m)).flatten

private theorem act_connectorCore (m q : ℕ) [NeZero m]
    (h3 : IsUnit (3 : ZMod m)) (h4 : IsUnit (4 : ZMod m)) (z : ZMod m) :
    act m (connectorCore m q) z =
      z + (q : ZMod m) * (-2 * (3 : ZMod m)⁻¹) := by
  induction q generalizing z with
  | zero => simp [connectorCore, act]
  | succ q ih =>
      rw [show connectorCore m (q + 1) = connectorUnit m ++ connectorCore m q by
        dsimp only [connectorCore]
        rw [List.replicate_succ, List.flatten_cons]]
      rw [act_append, act_connectorUnit m h3 h4, ih]
      push_cast
      ring

private theorem exists_connector (m : ℕ) (hm : 0 < m) (hcop : m.Coprime 6)
    (s t : ZMod m) : ∃ w : List (Fin 3), 0 < w.length ∧ act m w s = t := by
  haveI : NeZero m := ⟨hm.ne'⟩
  have h2nat : m.Coprime 2 :=
    Nat.Coprime.of_dvd_right (show 2 ∣ 6 by norm_num) hcop
  have h3nat : m.Coprime 3 :=
    Nat.Coprime.of_dvd_right (show 3 ∣ 6 by norm_num) hcop
  have h2 : IsUnit (2 : ZMod m) :=
    (ZMod.isUnit_iff_coprime 2 m).mpr h2nat.symm
  have h3 : IsUnit (3 : ZMod m) :=
    (ZMod.isUnit_iff_coprime 3 m).mpr h3nat.symm
  have h4 : IsUnit (4 : ZMod m) := by
    convert h2.mul h2 using 1 <;> norm_num
  let d : ZMod m := -2 * (3 : ZMod m)⁻¹
  have hneg2 : IsUnit (- (2 : ZMod m)) := h2.neg
  have hinv3 : IsUnit ((3 : ZMod m)⁻¹) :=
    isUnit_iff_exists_inv.mpr ⟨3, ZMod.inv_mul_of_unit 3 h3⟩
  have hd : IsUnit d := by
    dsimp [d]
    exact hneg2.mul hinv3
  let q : ℕ := ((t - s) * d⁻¹).val
  let w := connectorCore m q ++ List.replicate m.factorial (1 : Fin 3)
  refine ⟨w, ?_, ?_⟩
  · dsimp [w]
    simp only [List.length_append, List.length_replicate]
    exact Nat.lt_add_left _ (Nat.factorial_pos m)
  · rw [act_append, act_connectorCore m q h3 h4, act_replicate_one]
    rw [bcycle m h3 h4]
    change s + (q : ZMod m) * d = t
    have hq : (q : ZMod m) = (t - s) * d⁻¹ := by
      simpa [q] using ZMod.natCast_zmod_val ((t - s) * d⁻¹)
    rw [hq]
    calc
      s + ((t - s) * d⁻¹) * d = s + (t - s) * (d⁻¹ * d) := by ring
      _ = s + (t - s) := by rw [ZMod.inv_mul_of_unit d hd, mul_one]
      _ = t := by ring

private theorem affine_injective {R : Type*} [CommRing R] {a c : R}
    (ha : IsUnit a) : Function.Injective (fun z : R => z * a + c) := by
  intro x y hxy
  apply ha.mul_left_inj.mp
  exact add_right_cancel hxy

private theorem branch_injective (m : ℕ) (hcop : m.Coprime 6) (s : Fin 3) :
    Function.Injective (branch m s) := by
  have h2nat : m.Coprime 2 :=
    Nat.Coprime.of_dvd_right (show 2 ∣ 6 by norm_num) hcop
  have h3nat : m.Coprime 3 :=
    Nat.Coprime.of_dvd_right (show 3 ∣ 6 by norm_num) hcop
  have h2 : IsUnit (2 : ZMod m) :=
    (ZMod.isUnit_iff_coprime 2 m).mpr h2nat.symm
  have h3 : IsUnit (3 : ZMod m) :=
    (ZMod.isUnit_iff_coprime 3 m).mpr h3nat.symm
  have h4 : IsUnit (4 : ZMod m) := by
    convert h2.mul h2 using 1 <;> norm_num
  have hinv2 : IsUnit ((2 : ZMod m)⁻¹) :=
    isUnit_iff_exists_inv.mpr ⟨2, ZMod.inv_mul_of_unit 2 h2⟩
  have hinv4 : IsUnit ((4 : ZMod m)⁻¹) :=
    isUnit_iff_exists_inv.mpr ⟨4, ZMod.inv_mul_of_unit 4 h4⟩
  fin_cases s
  · convert affine_injective (c := (0 : ZMod m)) (h3.mul hinv2) using 1
    funext z
    simp [branch]
    ring
  · exact (left m h3 h4).injective
  · convert affine_injective (c := -(4 : ZMod m)⁻¹) (h3.mul hinv4) using 1
    funext z
    simp [branch, C]
    ring

private theorem act_injective (m : ℕ) (hcop : m.Coprime 6) (w : List (Fin 3)) :
    Function.Injective (act m w) := by
  induction w with
  | nil => exact Function.injective_id
  | cons s w ih =>
      exact ih.comp (branch_injective m hcop s)

private theorem act_surjective (m : ℕ) [NeZero m] (hcop : m.Coprime 6)
    (w : List (Fin 3)) : Function.Surjective (act m w) :=
  (Finite.injective_iff_surjective.mp (act_injective m hcop w))

private theorem cast_amusical_eq_branch (m : ℕ) (hcop : m.Coprime 6) (x : ℤ) :
    (amusical x : ZMod m) = branch m (stepSym x) x := by
  have h2nat : m.Coprime 2 :=
    Nat.Coprime.of_dvd_right (show 2 ∣ 6 by norm_num) hcop
  have h2 : IsUnit (2 : ZMod m) :=
    (ZMod.isUnit_iff_coprime 2 m).mpr h2nat.symm
  have h4 : IsUnit (4 : ZMod m) := by
    convert h2.mul h2 using 1 <;> norm_num
  unfold stepSym
  split_ifs with hx2 hx4
  · have hxform : x = 2 * (x / 2) := by
      have hx := Int.mul_ediv_add_emod x 2
      omega
    rw [hxform, amusical_two_mul]
    push_cast
    simp only [branch, Matrix.cons_val_zero]
    calc
      3 * ((x / 2 : ℤ) : ZMod m) =
          3 * ((x / 2 : ℤ) : ZMod m) * 1 := by ring
      _ = 3 * ((x / 2 : ℤ) : ZMod m) * ((2 : ZMod m) * 2⁻¹) := by
        rw [ZMod.mul_inv_of_unit 2 h2]
      _ = 3 * (2 * ((x / 2 : ℤ) : ZMod m)) * 2⁻¹ := by ring
  · have hxform : x = 4 * (x / 4) + 1 := by
      have hx := Int.mul_ediv_add_emod x 4
      omega
    rw [hxform, amusical_four_mul_add_one]
    push_cast
    simp only [branch_one, B]
    calc
      3 * ((x / 4 : ℤ) : ZMod m) + 1 =
          (3 * ((x / 4 : ℤ) : ZMod m) + 1) * 1 := by ring
      _ = (3 * ((x / 4 : ℤ) : ZMod m) + 1) * ((4 : ZMod m) * 4⁻¹) := by
        rw [ZMod.mul_inv_of_unit 4 h4]
      _ = (3 * (4 * ((x / 4 : ℤ) : ZMod m) + 1) + 1) * 4⁻¹ := by ring
  · have hxform : x = 4 * (x / 4) + 3 := by
      have hx := Int.mul_ediv_add_emod x 4
      omega
    rw [hxform, amusical_four_mul_add_three]
    push_cast
    simp only [branch_two, C]
    calc
      3 * ((x / 4 : ℤ) : ZMod m) + 2 =
          (3 * ((x / 4 : ℤ) : ZMod m) + 2) * 1 := by ring
      _ = (3 * ((x / 4 : ℤ) : ZMod m) + 2) * ((4 : ZMod m) * 4⁻¹) := by
        rw [ZMod.mul_inv_of_unit 4 h4]
      _ = (3 * (4 * ((x / 4 : ℤ) : ZMod m) + 3) - 1) * 4⁻¹ := by ring

private theorem cast_iterate_eq_act (m : ℕ) (hcop : m.Coprime 6)
    (w : List (Fin 3)) (x : ℤ)
    (hw : ∀ i (hi : i < w.length), stepSym (amusical^[i] x) = w[i]) :
    (amusical^[w.length] x : ZMod m) = act m w x := by
  induction w generalizing x with
  | nil => rfl
  | cons s w ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      have htail : ∀ i (hi : i < w.length),
          stepSym (amusical^[i] (amusical x)) = w[i] := by
        intro i hi
        rw [show amusical^[i] (amusical x) = amusical^[i + 1] x by
          rw [Function.iterate_succ_apply]]
        have h := hw (i + 1) (by simp; omega)
        rw [List.getElem_cons_succ] at h
        exact h
      rw [ih (amusical x) htail, cast_amusical_eq_branch m hcop]
      have hhead := hw 0 (by simp)
      rw [List.getElem_cons_zero] at hhead
      simp only [Function.iterate_zero_apply] at hhead
      rw [hhead]
      rfl

private theorem pow_three_dvd_iterate_sub_of_symbols (b : ℕ) (x y : ℤ)
    (h : ∀ i < b, stepSym (amusical^[i] x) = stepSym (amusical^[i] y)) :
    (3 : ℤ) ^ b ∣ amusical^[b] x - amusical^[b] y := by
  apply continuous_pow_three_dvd_sub_of_word_eq b
  funext i
  unfold continuousBackwardStepWord continuousRawStepSym
  have cancel (z : ℤ) :
      amusicalInv^[i.val + 1] (amusical^[b] z) =
        amusical^[b - (i.val + 1)] z := by
    have hsplit : amusical^[b] z =
        amusical^[i.val + 1] (amusical^[b - (i.val + 1)] z) := by
      rw [← Function.iterate_add_apply]
      congr 2
      omega
    rw [hsplit, amusicalInv_iterate_amusical_iterate]
  rw [cancel x, cancel y]
  exact h (b - (i.val + 1)) (by omega)

private theorem stepSym_add_four_mul (n q : ℤ) :
    stepSym (n + 4 * q) = stepSym n := by
  unfold stepSym
  split_ifs <;> omega

private theorem stepSym_iterate_add_pow_four_mul (L i : ℕ) (hi : i < L)
    (n q : ℤ) :
    stepSym (amusical^[i] (n + (4 : ℤ) ^ L * q)) = stepSym (amusical^[i] n) := by
  rw [amusical_iterate_add_pow_four_mul_exact L i hi.le]
  obtain ⟨d, hd⟩ : ∃ d, L - i = d + 1 := by
    exact ⟨L - i - 1, by omega⟩
  rw [hd, pow_succ]
  convert stepSym_add_four_mul (amusical^[i] n)
    ((4 : ℤ) ^ d * amusicalForwardMultiplier i n * q) using 1 <;> ring

/-- Realize a finite forward itinerary by reading it backwards through the exact ternary
backward-word equivalence. -/
private theorem exists_forward_itinerary_local (u : List (Fin 3)) :
    ∃ m : ℤ, ∀ j (hj : j < u.length), stepSym (amusical^[j] m) = u[j] := by
  let L := u.length
  let f : Fin L → Fin 3 := fun i =>
    u[L - 1 - i.val]'(by dsimp only [L]; omega)
  let yy : Fin (3 ^ L) := (continuousBackwardStepWordEquiv L).symm f
  let y : ℤ := yy.val
  have hy : continuousBackwardStepWord L y = f := by
    change (continuousBackwardStepWordEquiv L) yy = f
    exact (continuousBackwardStepWordEquiv L).apply_symm_apply f
  let m := amusicalInv^[L] y
  refine ⟨m, ?_⟩
  intro j hj
  have hjL : j < L := by simpa [L] using hj
  let i : Fin L := ⟨L - 1 - j, by omega⟩
  have hi := congrFun hy i
  have hexp : L - 1 - j + 1 = L - j := by omega
  have hidx : L - 1 - (L - 1 - j) = j := by omega
  have hstate : amusical^[j] m = amusicalInv^[L - j] y := by
    dsimp only [m]
    have hsplit : amusicalInv^[L] y =
        amusicalInv^[j] (amusicalInv^[L - j] y) := by
      rw [← Function.iterate_add_apply]
      congr 2
      omega
    rw [hsplit, amusical_iterate_amusicalInv_iterate]
  rw [hstate]
  change stepSym (amusicalInv^[i.val + 1] y) = f i at hi
  dsimp only [i, f] at hi
  rw [hexp] at hi
  have hget : u[L - 1 - (L - 1 - j)] = u[j] :=
    getElem_congr rfl hidx (by dsimp only [L]; omega)
  exact hi.trans hget

/-- **Proved (Proposition P).**  Every residue class contains points `x ≥ N` whose first `T`
forward iterates visit the class at least `K + 1` times, so no eventually periodic infinite set
meets every orbit boundedly often.  Paper proof: write `M = 2^a 3^b M₀` with `gcd(M₀, 6) = 1`;
`Uⁱ x mod 2^a` is fixed by the next `a` symbols, `Uⁱ x mod 3^b` by the previous `b`, and the
branch maps act transitively on `ℤ/M₀` (`g_A⁻¹ g_B` is translation by `−2/3`).
Build a word
`p v₁ p ⋯ v_K p` with a marker `p` coding `r` and connectors `vⱼ` fixing the `M₀` part, then
prescribe its cylinder and `x mod 3^b M₀` by CRT. -/
theorem exists_many_returns (M : ℕ) (hM : 0 < M) (r : ℤ) (K N : ℕ) :
    ∃ x : ℤ, ∃ T : ℕ, (N : ℤ) ≤ x ∧
      K + 1 ≤ ((Finset.range T).filter fun i => amusical^[i] x ≡ r [ZMOD M]).card := by
  obtain ⟨a, m₁, hm₁two, hMfac⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hM.ne' 2 (by norm_num)
  have hm₁ : 0 < m₁ := by
    by_contra h
    have : m₁ = 0 := Nat.eq_zero_of_not_pos h
    rw [this] at hMfac
    simp at hMfac
    omega
  obtain ⟨b, m₀, hm₀three, hm₁fac⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hm₁.ne' 3 (by norm_num)
  have hm₀ : 0 < m₀ := by
    by_contra h
    have : m₀ = 0 := Nat.eq_zero_of_not_pos h
    rw [this] at hm₁fac
    simp at hm₁fac
    omega
  have hm₀two : ¬2 ∣ m₀ := by
    intro h
    obtain ⟨q, hq⟩ := h
    apply hm₁two
    refine ⟨3 ^ b * q, ?_⟩
    rw [hm₁fac, hq]
    ring
  have hc2 : m₀.Coprime 2 :=
    ((Nat.prime_two.coprime_iff_not_dvd).mpr hm₀two).symm
  have hc3 : m₀.Coprime 3 :=
    ((Nat.prime_three.coprime_iff_not_dvd).mpr hm₀three).symm
  have hc6 : m₀.Coprime 6 := by
    convert hc2.mul_right hc3 using 1 <;> norm_num
  have hMfull : M = 2 ^ a * (3 ^ b * m₀) := by
    rw [hMfac, hm₁fac]
  let pre : List (Fin 3) :=
    List.ofFn fun i : Fin a => stepSym (amusical^[i.val] r)
  let suf : List (Fin 3) :=
    List.ofFn fun i : Fin b => stepSym (amusical^[i.val] (amusicalInv^[b] r))
  haveI : NeZero m₀ := ⟨hm₀.ne'⟩
  obtain ⟨z, hz⟩ := act_surjective m₀ hc6 suf (r : ZMod m₀)
  obtain ⟨connector, hconnectorPos, hconnector⟩ :=
    exists_connector m₀ hm₀ hc6 (act m₀ pre (r : ZMod m₀)) z
  let block := (pre ++ connector) ++ suf
  let L := block.length
  have hpreLen : pre.length = a := by simp [pre]
  have hsufLen : suf.length = b := by simp [suf]
  have hLval : L = a + connector.length + b := by
    simp [L, block, hpreLen, hsufLen, Nat.add_assoc]
  have hL : 0 < L := by omega
  have hbL : b ≤ L := by omega
  have hblock : act m₀ block (r : ZMod m₀) = r := by
    simp only [block, act_append]
    rw [hconnector, hz]
  have hprefix : ∀ i (hi : i < a), block[i] = stepSym (amusical^[i] r) := by
    intro i hi
    dsimp only [block]
    rw [List.getElem_append_left (by simp [hpreLen]; omega)]
    rw [List.getElem_append_left (by simpa [hpreLen])]
    simp [pre, List.getElem_ofFn]
  have hsuffix : ∀ i (hi : i < b),
      block[L - b + i] = stepSym (amusical^[i] (amusicalInv^[b] r)) := by
    intro i hi
    have hindex : L - b + i = (pre ++ connector).length + i := by
      simp [hLval, hpreLen]
    calc
      block[L - b + i] = block[(pre ++ connector).length + i] :=
        getElem_congr rfl hindex (by omega)
      _ = stepSym (amusical^[i] (amusicalInv^[b] r)) := by
        dsimp only [block]
        rw [List.getElem_append_right (Nat.le_add_right _ _)]
        simp only [List.length_append, Nat.add_sub_cancel_left]
        simp [suf, List.getElem_ofFn]
  let D := K * L + a
  let word : List (Fin 3) := List.ofFn fun i : Fin D =>
    block[i.val % L]'(Nat.mod_lt _ hL)
  have hwordLen : word.length = D := by simp [word]
  obtain ⟨m, hm⟩ := exists_forward_itinerary_local word
  let O := 3 ^ b * m₀
  have hO : 0 < O := by positivity
  have hO2 : O.Coprime 2 := by
    dsimp only [O]
    exact (by norm_num : (3 : ℕ).Coprime 2).pow_left b |>.mul_left hc2
  have hO4 : O.Coprime 4 := by
    convert hO2.pow_right 2 using 1 <;> norm_num
  have hOA : O.Coprime (4 ^ D) := hO4.pow_right D
  have hcopInt : IsCoprime (O : ℤ) ((4 : ℤ) ^ D) := by
    exact Nat.Coprime.isCoprime hOA
  obtain ⟨q₀, hq₀⟩ : ∃ q : ℤ, (4 : ℤ) ^ D * q ≡ r - m [ZMOD O] :=
    exists_mul_modEq_of_isCoprime hcopInt
  let t : ℤ := (N : ℤ) + |m| + |q₀| + 1
  let q : ℤ := q₀ + O * t
  let x : ℤ := m + 4 ^ D * q
  have ht : 0 ≤ t := by
    dsimp [t]
    positivity
  have hOcast : (1 : ℤ) ≤ O := by exact_mod_cast hO
  have hOt : t ≤ (O : ℤ) * t := by nlinarith
  have hq : (N : ℤ) + |m| + 1 ≤ q := by
    have hqabs : -|q₀| ≤ q₀ := neg_abs_le q₀
    calc
      (N : ℤ) + |m| + 1 ≤ -|q₀| + t := by dsimp [t]; omega
      _ ≤ q₀ + (O : ℤ) * t := by omega
      _ = q := by rfl
  have hA : (1 : ℤ) ≤ 4 ^ D := by
    have hp : (0 : ℤ) < 4 ^ D := pow_pos (by norm_num) D
    omega
  have hAq : q ≤ (4 : ℤ) ^ D * q := by
    have hqpos : 0 ≤ q := by
      have := abs_nonneg m
      omega
    nlinarith
  have hxlarge : (N : ℤ) ≤ x := by
    dsimp only [x]
    have hmabs : -|m| ≤ m := neg_abs_le m
    omega
  have hxOdd : x ≡ r [ZMOD O] := by
    rw [Int.modEq_iff_dvd] at hq₀ ⊢
    obtain ⟨c, hc⟩ := hq₀
    refine ⟨c - (4 : ℤ) ^ D * t, ?_⟩
    dsimp only [x, q]
    push_cast
    linear_combination hc
  have hxword : ∀ i (hi : i < D),
      stepSym (amusical^[i] x) =
        block[i % L]'(by simpa [L] using Nat.mod_lt i hL) := by
    intro i hi
    calc
      stepSym (amusical^[i] x) = stepSym (amusical^[i] m) := by
        dsimp only [x]
        exact stepSym_iterate_add_pow_four_mul D i hi m q
      _ = word[i] := hm i (by simpa [hwordLen])
      _ = block[i % L]'(by simpa [L] using Nat.mod_lt i hL) := by
        simp [word, List.getElem_ofFn]
  have hxmod₀ : (x : ZMod m₀) = r := by
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    apply (show (m₀ : ℤ) ∣ O by
      refine ⟨3 ^ b, ?_⟩
      dsimp only [O]
      push_cast
      ring).trans
    exact hxOdd.dvd
  have hm₀marker : ∀ j, j ≤ K → (amusical^[j * L] x : ZMod m₀) = r := by
    intro j hj
    induction j with
    | zero => simpa using hxmod₀
    | succ j ih =>
        have hjlt : j < K := by omega
        have hmul : (j + 1) * L ≤ K * L :=
          Nat.mul_le_mul_right L (by omega)
        have hseg : ∀ i (hi : i < block.length),
            stepSym (amusical^[i] (amusical^[j * L] x)) = block[i] := by
          intro i hi
          have hiL : i < L := by simpa [L] using hi
          have htime : i + j * L < D := by
            have hstep : i + j * L < (j + 1) * L := by
              rw [Nat.add_mul]
              omega
            exact lt_of_lt_of_le (lt_of_lt_of_le hstep hmul) (by simp [D])
          rw [← Function.iterate_add_apply]
          have hw := hxword (i + j * L) htime
          have hmod : (i + j * L) % L = i := by
            simp [Nat.add_mod, Nat.mod_eq_of_lt hiL]
          simpa only [hmod] using hw
        have hact := cast_iterate_eq_act m₀ hc6 block (amusical^[j * L] x) hseg
        calc
          (amusical^[(j + 1) * L] x : ZMod m₀) =
              (amusical^[L] (amusical^[j * L] x) : ZMod m₀) := by
            rw [show (j + 1) * L = L + j * L by ring]
            rw [Function.iterate_add_apply]
          _ = act m₀ block (amusical^[j * L] x : ZMod m₀) := hact
          _ = act m₀ block (r : ZMod m₀) := by rw [ih (by omega)]
          _ = r := hblock
  have htwoMarker : ∀ j, j ≤ K →
      (2 : ℤ) ^ a ∣ amusical^[j * L] x - r := by
    intro j hj
    apply pow_two_dvd_sub_of_stepSym_iterate_eq
    intro i hi
    have hjmul : j * L ≤ K * L := Nat.mul_le_mul_right L hj
    have htime : i + j * L < D := by
      dsimp only [D]
      omega
    rw [← Function.iterate_add_apply]
    have hw := hxword (i + j * L) htime
    have hmod : (i + j * L) % L = i := by
      have hiL : i < L := lt_of_lt_of_le hi (by omega)
      simp [Nat.add_mod, Nat.mod_eq_of_lt hiL]
    have hget : block[(i + j * L) % L] = block[i] :=
      getElem_congr rfl hmod (by simpa [L] using Nat.mod_lt (i + j * L) hL)
    exact hw.trans (hget.trans (hprefix i hi))
  have hthreeMarker : ∀ k, k < K →
      (3 : ℤ) ^ b ∣ amusical^[(k + 1) * L] x - r := by
    intro k hk
    let y := amusical^[k * L + (L - b)] x
    have hsymbols : ∀ i < b,
        stepSym (amusical^[i] y) =
          stepSym (amusical^[i] (amusicalInv^[b] r)) := by
      intro i hi
      have hoff : L - b + i < L := by omega
      have hmul : (k + 1) * L ≤ K * L :=
        Nat.mul_le_mul_right L (by omega)
      have hstep : i + (k * L + (L - b)) < (k + 1) * L := by
        rw [Nat.add_mul]
        omega
      have htime : i + (k * L + (L - b)) < D :=
        lt_of_lt_of_le (lt_of_lt_of_le hstep hmul) (by simp [D])
      dsimp only [y]
      rw [← Function.iterate_add_apply]
      have hw := hxword (i + (k * L + (L - b))) htime
      have hmod : (i + (k * L + (L - b))) % L = L - b + i := by
        rw [show i + (k * L + (L - b)) = k * L + (L - b + i) by omega]
        simp [Nat.add_mod, Nat.mod_eq_of_lt hoff]
      have hget : block[(i + (k * L + (L - b))) % L] = block[L - b + i] :=
        getElem_congr rfl hmod
          (by simpa [L] using Nat.mod_lt (i + (k * L + (L - b))) hL)
      exact hw.trans (hget.trans (hsuffix i hi))
    have hdiv :=
      pow_three_dvd_iterate_sub_of_symbols b y (amusicalInv^[b] r) hsymbols
    have hxend : amusical^[b] y = amusical^[(k + 1) * L] x := by
      dsimp only [y]
      rw [← Function.iterate_add_apply]
      congr 2
      rw [Nat.add_mul]
      omega
    rw [hxend, amusical_iterate_amusicalInv_iterate] at hdiv
    exact hdiv
  have hc3m₀ : (3 ^ b).Coprime m₀ := hc3.symm.pow_left b
  have hc2three : (2 ^ a).Coprime (3 ^ b) :=
    ((by norm_num : (2 : ℕ).Coprime 3).pow_left a).pow_right b
  have hc2m₀ : (2 ^ a).Coprime m₀ := hc2.symm.pow_left a
  have hc2O : (2 ^ a).Coprime (3 ^ b * m₀) := hc2three.mul_right hc2m₀
  have hmarker : ∀ j, j ≤ K → amusical^[j * L] x ≡ r [ZMOD M] := by
    intro j hj
    have htwo : amusical^[j * L] x ≡ r [ZMOD (2 : ℤ) ^ a] := by
      rw [Int.modEq_iff_dvd]
      have h := dvd_neg.mpr (htwoMarker j hj)
      simpa only [neg_sub] using h
    have hthree : amusical^[j * L] x ≡ r [ZMOD (3 : ℤ) ^ b] := by
      cases j with
      | zero =>
          simpa only [zero_mul, Function.iterate_zero_apply] using hxOdd.of_dvd (by
            refine ⟨m₀, ?_⟩
            dsimp only [O]
            push_cast
            ring)
      | succ k =>
          rw [Int.modEq_iff_dvd]
          have h := dvd_neg.mpr (hthreeMarker k (by omega))
          simpa only [neg_sub] using h
    have hm₀mod : amusical^[j * L] x ≡ r [ZMOD (m₀ : ℤ)] := by
      rw [Int.modEq_iff_dvd, ← ZMod.intCast_eq_intCast_iff_dvd_sub]
      exact hm₀marker j hj
    have hodd : amusical^[j * L] x ≡ r [ZMOD (3 : ℤ) ^ b * m₀] :=
      (Int.modEq_and_modEq_iff_modEq_mul (by simpa using hc3m₀)).mp ⟨hthree, hm₀mod⟩
    have hall : amusical^[j * L] x ≡ r
        [ZMOD (2 : ℤ) ^ a * ((3 : ℤ) ^ b * m₀)] :=
      (Int.modEq_and_modEq_iff_modEq_mul
        (by simpa [Int.natAbs_mul, Int.natAbs_pow] using hc2O)).mp ⟨htwo, hodd⟩
    simpa [hMfull] using hall
  let markers := (Finset.range (K + 1)).image fun j => j * L
  have hmarkersCard : markers.card = K + 1 := by
    have hinj : Set.InjOn (fun j : ℕ => j * L) (Finset.range (K + 1)) := by
      intro i _ j _ hij
      exact Nat.eq_of_mul_eq_mul_right hL hij
    dsimp only [markers]
    rw [Finset.card_image_iff.mpr hinj, Finset.card_range]
  have hmarkersSubset : markers ⊆
      (Finset.range (K * L + 1)).filter fun i => amusical^[i] x ≡ r [ZMOD M] := by
    intro n hn
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hn
    rw [Finset.mem_range] at hj
    rw [Finset.mem_filter, Finset.mem_range]
    have hjle : j ≤ K := by omega
    have hjmul : j * L ≤ K * L := Nat.mul_le_mul_right L hjle
    exact ⟨by omega, hmarker j hjle⟩
  refine ⟨x, K * L + 1, hxlarge, ?_⟩
  calc
    K + 1 = markers.card := hmarkersCard.symm
    _ ≤ ((Finset.range (K * L + 1)).filter fun i =>
        amusical^[i] x ≡ r [ZMOD M]).card := Finset.card_le_card hmarkersSubset

/-- `n` is never undercut going forward. -/
def FwdSurvivor (n : ℤ) : Prop :=
  ∀ t : ℕ, 1 ≤ t → n ≤ amusical^[t] n

/-- `n` is never undercut going backward. -/
def BwdSurvivor (n : ℤ) : Prop :=
  ∀ t : ℕ, 1 ≤ t → n ≤ amusicalInv^[t] n

/-- The finite forward half of `IsWindowMin`. -/
private def FwdWindowSurvivor (L : ℕ) (n : ℤ) : Prop :=
  ∀ t : ℕ, 1 ≤ t → t ≤ L → n ≤ amusical^[t] n

/-- The finite backward half of `IsWindowMin`. -/
private def BwdWindowSurvivor (L : ℕ) (n : ℤ) : Prop :=
  ∀ t : ℕ, 1 ≤ t → t ≤ L → n ≤ amusicalInv^[t] n

private theorem isWindowMin_iff_windowSurvivors (L : ℕ) (n : ℤ) :
    IsWindowMin L n ↔ FwdWindowSurvivor L n ∧ BwdWindowSurvivor L n := by
  constructor
  · intro hn
    exact ⟨fun t ht hL => (hn t ht hL).1, fun t ht hL => (hn t ht hL).2⟩
  · rintro ⟨hf, hb⟩ t ht hL
    exact ⟨hf t ht hL, hb t ht hL⟩

private theorem fwdSurvivor_window (L : ℕ) {n : ℤ} (hn : FwdSurvivor n) :
    FwdWindowSurvivor L n := by
  intro t ht _
  exact hn t ht

private theorem bwdSurvivor_window (L : ℕ) {n : ℤ} (hn : BwdSurvivor n) :
    BwdWindowSurvivor L n := by
  intro t ht _
  exact hn t ht

/-- Above the joint window threshold, each one-sided semantic condition is independently
equivalent to its branch-word condition. -/
private theorem windowSurvivors_iff_good_of_large (L n : ℕ)
    (hn : 4 ^ L * 3 ^ L * (windowBound L + 1) ≤ n) :
    (FwdWindowSurvivor L n ↔ FwdGood L (amusicalForwardWord L n)) ∧
      (BwdWindowSurvivor L n ↔ BwdGood L (amusicalBackwardWord L n)) := by
  set M := 4 ^ L * 3 ^ L with hM
  have hMpos : 0 < M := by positivity
  set c := n % M with hc
  set q := n / M with hq
  have hcM : c < M := Nat.mod_lt _ hMpos
  have hqge : windowBound L + 1 ≤ q :=
    (Nat.le_div_iff_mul_le hMpos).mpr (by linarith)
  have hnq : (n : ℤ) = c + M * q := by
    have h := Nat.mod_add_div n M
    exact_mod_cast h.symm
  have hnF : (n : ℤ) = c + 4 ^ L * (3 ^ L * q) := by
    rw [hnq, hM]
    push_cast
    ring
  have hnB : (n : ℤ) = c + 3 ^ L * (4 ^ L * q) := by
    rw [hnq, hM]
    push_cast
    ring
  have hpatF : amusicalForwardWord L n = amusicalForwardWord L c := by
    rw [hnF, amusicalForwardWord_add_pow_four_mul]
  have hpatB : amusicalBackwardWord L n = amusicalBackwardWord L c := by
    rw [hnB, amusicalBackwardWord_add_pow_three_mul]
  rw [hpatF, hpatB]
  have hbound : ∀ t, t ≤ L → |amusical^[t] (c : ℤ) - c| < q ∧
      |amusicalInv^[t] (c : ℤ) - c| < q := by
    intro t ht
    have h1 : (amusical^[t] (c : ℤ) - c).natAbs +
        (amusicalInv^[t] (c : ℤ) - c).natAbs ≤ windowBound L := by
      unfold windowBound
      refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.mpr hcM))
      exact Finset.single_le_sum
        (f := fun t => (amusical^[t] (c : ℤ) - c).natAbs +
          (amusicalInv^[t] (c : ℤ) - c).natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
    have h2 : ((amusical^[t] (c : ℤ) - c).natAbs : ℤ) +
        ((amusicalInv^[t] (c : ℤ) - c).natAbs : ℤ) ≤ windowBound L := by
      exact_mod_cast h1
    have h3 : (windowBound L : ℤ) + 1 ≤ q := by exact_mod_cast hqge
    rw [Int.natCast_natAbs, Int.natCast_natAbs] at h2
    have hf := abs_nonneg (amusical^[t] (c : ℤ) - c)
    have hb := abs_nonneg (amusicalInv^[t] (c : ℤ) - c)
    constructor <;> linarith
  have hq3 : (q : ℤ) ≤ 3 ^ L * q :=
    le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
  have hq4 : (q : ℤ) ≤ 4 ^ L * q :=
    le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
  have hF : ∀ t, 1 ≤ t → t ≤ L → ((n : ℤ) ≤ amusical^[t] n ↔
      2 ^ (t + ((Finset.univ.filter fun i : Fin L =>
        i.val < t ∧ amusicalForwardWord L c i = true).card)) < 3 ^ t) := by
    intro t ht1 ht
    rw [hnF, amusical_iterate_add_pow_four_mul_slope L t ht]
    rw [show (4 : ℤ) ^ (L - t) * 3 ^ t * 2 ^ amusicalForwardEvenCount t c *
        (3 ^ L * q) =
      (4 ^ (L - t) * 3 ^ t * 2 ^ amusicalForwardEvenCount t c) *
        (3 ^ L * q) by ring]
    rw [add_mul_le_add_mul_iff
      (amusical_forward_slope_ne L t (amusicalForwardEvenCount t c) ht1)
      (lt_of_lt_of_le (hbound t ht).1 hq3)]
    exact amusical_forward_slope_lt_iff L t _ _ ht
      (amusicalForwardWord_true_card_add_evenCount L t ht c)
  have hB : ∀ t, 1 ≤ t → t ≤ L → ((n : ℤ) ≤ amusicalInv^[t] n ↔
      3 ^ t < 2 ^ (t + ((Finset.univ.filter fun i : Fin L =>
        i.val < t ∧ amusicalBackwardWord L c i = true).card))) := by
    intro t ht1 ht
    rw [hnB, amusicalInv_iterate_add_pow_three_mul_slope L t ht]
    rw [add_mul_le_add_mul_iff
      (amusical_backward_slope_ne L t (amusicalBackwardFourCount t c) ht1 ht)
      (lt_of_lt_of_le (hbound t ht).2 hq4)]
    rw [amusicalBackwardWord_true_card_eq_fourCount L t ht c]
    exact amusical_backward_slope_lt_iff L t _ ht
  constructor
  · constructor
    · intro hf t ht1 ht
      exact (hF t ht1 ht).mp (hf t ht1 ht)
    · intro hf t ht1 ht
      exact (hF t ht1 ht).mpr (hf t ht1 ht)
  · constructor
    · intro hb t ht1 ht
      exact (hB t ht1 ht).mp (hb t ht1 ht)
    · intro hb t ht1 ht
      exact (hB t ht1 ht).mpr (hb t ht1 ht)

private theorem tendsto_fwdGood_density (L : ℕ) :
    Filter.Tendsto
      (fun X : ℕ =>
        (Nat.count (fun n : ℕ => FwdGood L (amusicalForwardWord L n)) X : ℝ) / X)
      Filter.atTop (nhds (fwdSurv L : ℝ)) := by
  let P : ℕ → Prop := fun n => FwdGood L (amusicalForwardWord L n)
  set M := 4 ^ L with hM
  set G := Nat.count P M with hG
  have hMpos : 0 < M := by positivity
  have hPper : ∀ n, P n ↔ P (n % M) := fun n => by
    simp only [P]
    rw [← amusicalForwardWord_natCast_mod]
  have hPadd : ∀ n : ℕ, P (n + M) ↔ P n := by
    intro n
    rw [hPper (n + M), hPper n]
    simp
  have hblock : ∀ a : ℕ, Nat.count (fun k => P (a + k)) M = G := by
    intro a
    rw [count_block_eq_of_add_periodic P hPadd a, hG]
  have hratio : (fwdSurv L : ℝ) = (G : ℝ) / M := by
    have heq := fwdSurv_mul L
    simp only [P, hM] at hG
    rw [← hG] at heq
    apply (eq_div_iff (by positivity : (M : ℝ) ≠ 0)).2
    have heq' := congrArg (fun q : ℚ => (q : ℝ)) heq
    rw [hM]
    push_cast
    norm_num at heq'
    nlinarith
  rw [hratio]
  exact tendsto_count_div_of_periodic_blocks P hMpos hblock

private theorem tendsto_bwdGood_density (L : ℕ) :
    Filter.Tendsto
      (fun X : ℕ =>
        (Nat.count (fun n : ℕ => BwdGood L (amusicalBackwardWord L n)) X : ℝ) / X)
      Filter.atTop (nhds (bwdSurv L : ℝ)) := by
  let P : ℕ → Prop := fun n => BwdGood L (amusicalBackwardWord L n)
  set M := 3 ^ L with hM
  set G := Nat.count P M with hG
  have hMpos : 0 < M := by positivity
  have hPper : ∀ n, P n ↔ P (n % M) := fun n => by
    simp only [P]
    rw [← amusicalBackwardWord_natCast_mod]
  have hPadd : ∀ n : ℕ, P (n + M) ↔ P n := by
    intro n
    rw [hPper (n + M), hPper n]
    simp
  have hblock : ∀ a : ℕ, Nat.count (fun k => P (a + k)) M = G := by
    intro a
    rw [count_block_eq_of_add_periodic P hPadd a, hG]
  have hratio : (bwdSurv L : ℝ) = (G : ℝ) / M := by
    have heq := bwdSurv_mul L
    simp only [P, hM] at hG
    rw [← hG] at heq
    apply (eq_div_iff (by positivity : (M : ℝ) ≠ 0)).2
    have heq' := congrArg (fun q : ℚ => (q : ℝ)) heq
    rw [hM]
    push_cast
    norm_num at heq'
    nlinarith
  rw [hratio]
  exact tendsto_count_div_of_periodic_blocks P hMpos hblock

open Classical in
private theorem tendsto_fwdWindowSurvivor_density (L : ℕ) :
    Filter.Tendsto
      (fun X : ℕ =>
        (((Finset.range X).filter fun n : ℕ => FwdWindowSurvivor L n).card : ℝ) / X)
      Filter.atTop (nhds (fwdSurv L : ℝ)) := by
  classical
  have h := tendsto_count_div_of_eventually_congr
    (fun n : ℕ => FwdWindowSurvivor L n)
    (fun n : ℕ => FwdGood L (amusicalForwardWord L n))
    (A := 4 ^ L * 3 ^ L * (windowBound L + 1))
    (fun n hn => (windowSurvivors_iff_good_of_large L n hn).1)
    (tendsto_fwdGood_density L)
  simpa only [Nat.count_eq_card_filter_range] using h

open Classical in
private theorem tendsto_bwdWindowSurvivor_density (L : ℕ) :
    Filter.Tendsto
      (fun X : ℕ =>
        (((Finset.range X).filter fun n : ℕ => BwdWindowSurvivor L n).card : ℝ) / X)
      Filter.atTop (nhds (bwdSurv L : ℝ)) := by
  classical
  have h := tendsto_count_div_of_eventually_congr
    (fun n : ℕ => BwdWindowSurvivor L n)
    (fun n : ℕ => BwdGood L (amusicalBackwardWord L n))
    (A := 4 ^ L * 3 ^ L * (windowBound L + 1))
    (fun n hn => (windowSurvivors_iff_good_of_large L n hn).2)
    (tendsto_bwdGood_density L)
  simpa only [Nat.count_eq_card_filter_range] using h

/-- Inclusion-exclusion after enlarging each of two finite sets independently. -/
private theorem card_add_card_add_inter_le {α : Type*} [DecidableEq α]
    {A B C D : Finset α} (hAC : A ⊆ C) (hBD : B ⊆ D) :
    A.card + B.card + (C ∩ D).card ≤ (A ∩ B).card + C.card + D.card := by
  have hcard := Finset.card_le_card (Finset.union_subset_union hAC hBD)
  have hAB := Finset.card_union_add_card_inter A B
  have hCD := Finset.card_union_add_card_inter C D
  omega

/-- A point surviving forever in both directions is precisely an orbit minimum. -/
private theorem isOrbitMin_iff_survivors (n : ℤ) :
    IsOrbitMin n ↔ FwdSurvivor n ∧ BwdSurvivor n := by
  constructor
  · intro hn
    constructor
    · intro t ht
      exact hn _ ⟨t, (amusical_iterate_eq_perm_pow t n).symm⟩
    · intro t ht
      exact hn _ ⟨-(t : ℤ), (amusicalInv_iterate_eq_perm_pow t n).symm⟩
  · rintro ⟨hf, hb⟩ y ⟨j, rfl⟩
    by_cases hj0 : j = 0
    · subst j; simp
    · rcases lt_or_gt_of_ne hj0 with hj | hj
      · obtain ⟨t, rfl⟩ := Int.eq_negSucc_of_lt_zero hj
        change n ≤ (amusicalPerm ^ (-((t + 1 : ℕ) : ℤ))) n
        rw [← amusicalInv_iterate_eq_perm_pow]
        exact hb (t + 1) (by omega)
      · obtain ⟨t, rfl⟩ := Int.eq_ofNat_of_zero_le hj.le
        change n ≤ (amusicalPerm ^ (t : ℤ)) n
        rw [← amusical_iterate_eq_perm_pow]
        exact hf t (by omega)

open Classical in
/-- **Proved (Proposition S).**  Survivor densities above `f_L + b_L − f_L b_L` give Klamkin (a).
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
  have hgap : 0 < a + b - (fwdSurv L : ℝ) - (bwdSurv L : ℝ) +
      ((fwdSurv L * bwdSurv L : ℚ) : ℝ) := by
    norm_num at h ⊢
    linarith
  let ε : ℝ := (a + b - (fwdSurv L : ℝ) - (bwdSurv L : ℝ) +
    ((fwdSurv L * bwdSurv L : ℚ) : ℝ)) / 4
  have hε : 0 < ε := by
    dsimp only [ε]
    linarith
  have hFW : ∀ᶠ X : ℕ in Filter.atTop,
      (((Finset.range X).filter fun n : ℕ => FwdWindowSurvivor L n).card : ℝ) / X <
        (fwdSurv L : ℝ) + ε :=
    (tendsto_fwdWindowSurvivor_density L).eventually
      (gt_mem_nhds (lt_add_of_pos_right _ hε))
  have hBW : ∀ᶠ X : ℕ in Filter.atTop,
      (((Finset.range X).filter fun n : ℕ => BwdWindowSurvivor L n).card : ℝ) / X <
        (bwdSurv L : ℝ) + ε :=
    (tendsto_bwdWindowSurvivor_density L).eventually
      (gt_mem_nhds (lt_add_of_pos_right _ hε))
  have hWM : ∀ᶠ X : ℕ in Filter.atTop,
      ((fwdSurv L * bwdSurv L : ℚ) : ℝ) - ε <
        (((Finset.range X).filter fun n : ℕ => IsWindowMin L n).card : ℝ) / X :=
    (windowMinDensity L).eventually (lt_mem_nhds (sub_lt_self _ hε))
  have hminLower : ∀ᶠ X : ℕ in Filter.atTop,
      ε * X < ((Finset.range X).filter fun n : ℕ => IsOrbitMin n).card := by
    filter_upwards [ha, hb, hFW, hBW, hWM, Filter.eventually_gt_atTop 0] with
      X hFS hBS hFW' hBW' hWM' hX
    let R := Finset.range X
    let FS := R.filter fun n : ℕ => FwdSurvivor n
    let BS := R.filter fun n : ℕ => BwdSurvivor n
    let FW := R.filter fun n : ℕ => FwdWindowSurvivor L n
    let BW := R.filter fun n : ℕ => BwdWindowSurvivor L n
    let WM := R.filter fun n : ℕ => IsWindowMin L n
    let OM := R.filter fun n : ℕ => IsOrbitMin n
    have hFSsub : FS ⊆ FW := by
      intro n hn
      simp only [FS, FW, Finset.mem_filter] at hn ⊢
      exact ⟨hn.1, fwdSurvivor_window L hn.2⟩
    have hBSsub : BS ⊆ BW := by
      intro n hn
      simp only [BS, BW, Finset.mem_filter] at hn ⊢
      exact ⟨hn.1, bwdSurvivor_window L hn.2⟩
    have hOMeq : OM = FS ∩ BS := by
      ext n
      simp [OM, FS, BS, R, isOrbitMin_iff_survivors]
      tauto
    have hWMeq : WM = FW ∩ BW := by
      ext n
      simp [WM, FW, BW, R, isWindowMin_iff_windowSurvivors]
      tauto
    have hcard := card_add_card_add_inter_le hFSsub hBSsub
    rw [← hOMeq, ← hWMeq] at hcard
    have hcard' : (FS.card : ℝ) + BS.card + WM.card ≤
        OM.card + FW.card + BW.card := by
      exact_mod_cast hcard
    have hFS' : a * (X : ℝ) ≤ (FS.card : ℝ) := by
      simpa only [FS, R] using hFS
    have hBS' : b * (X : ℝ) ≤ (BS.card : ℝ) := by
      simpa only [BS, R] using hBS
    have hFWratio : (FW.card : ℝ) / X < (fwdSurv L : ℝ) + ε := by
      simpa only [FW, R] using hFW'
    have hBWratio : (BW.card : ℝ) / X < (bwdSurv L : ℝ) + ε := by
      simpa only [BW, R] using hBW'
    have hWMratio : ((fwdSurv L * bwdSurv L : ℚ) : ℝ) - ε <
        (WM.card : ℝ) / X := by
      simpa only [WM, R] using hWM'
    have hXreal : (0 : ℝ) < X := by exact_mod_cast hX
    rw [div_lt_iff₀ hXreal] at hFWratio hBWratio
    rw [lt_div_iff₀ hXreal] at hWMratio
    have hεeq : a + b - (fwdSurv L : ℝ) - (bwdSurv L : ℝ) +
        ((fwdSurv L * bwdSurv L : ℚ) : ℝ) = 4 * ε := by
      dsimp only [ε]
      ring
    change ε * (X : ℝ) < (OM.card : ℝ)
    nlinarith [hεeq]
  have hNatMin : {n : ℕ | IsOrbitMin n}.Infinite := by
    intro hfin
    have hbound : ∀ X : ℕ,
        ((Finset.range X).filter fun n : ℕ => IsOrbitMin n).card ≤
          hfin.toFinset.card := by
      intro X
      apply Finset.card_le_card
      intro n hn
      rw [hfin.mem_toFinset]
      exact (Finset.mem_filter.mp hn).2
    have hlarge := hminLower.and
      (Filter.eventually_gt_atTop
        (Nat.ceil ((hfin.toFinset.card : ℝ) / ε)))
    obtain ⟨X, hXmin, hXlarge⟩ := hlarge.exists
    have hceil := Nat.le_ceil ((hfin.toFinset.card : ℝ) / ε)
    have hXlarge' : (Nat.ceil ((hfin.toFinset.card : ℝ) / ε) : ℝ) < X := by
      exact_mod_cast hXlarge
    have hratio : (hfin.toFinset.card : ℝ) / ε < X :=
      lt_of_le_of_lt hceil hXlarge'
    have hcardlt : (hfin.toFinset.card : ℝ) < ε * X := by
      rw [div_lt_iff₀ hε] at hratio
      nlinarith
    have hbound' :
        (((Finset.range X).filter fun n : ℕ => IsOrbitMin n).card : ℝ) ≤
          hfin.toFinset.card := by
      exact_mod_cast hbound X
    linarith
  apply amusicalInfinitelyManyOrbits_of_minima
  have himage : ((fun n : ℕ => (n : ℤ)) '' {n : ℕ | IsOrbitMin n}).Infinite := by
    apply hNatMin.image
    intro x _ y _ hxy
    exact Int.ofNat_injective hxy
  exact himage.mono (by
    rintro _ ⟨n, hn, rfl⟩
    exact ⟨by positivity, hn⟩)

/-- **Proved.**  A strictly increasing map commuting with `U` and raising every positive integer
separates orbits.  Paper proof: `g` also commutes with `U⁻¹`, so it maps the orbit of `m` onto
the orbit of `g m`, with minimum `g m > m`; the orbits of `m, g m, g² m, …` are distinct. -/
theorem infinitelyManyOrbits_of_commuting {g : ℤ → ℤ}
    (hg : ∀ n, g (amusical n) = amusical (g n))
    (hmono : StrictMono g) (hgt : ∀ n, 0 < n → n < g n) (hpos : ∀ n, 0 ≤ n → 0 ≤ g n)
    (hinf : ∃ n, 0 < n ∧ IsOrbitMin n ∧ (amusicalOrbit n).Infinite) :
    AmusicalInfinitelyManyOrbits := by
  have hgInv : ∀ n, g (amusicalInv n) = amusicalInv (g n) := by
    intro n
    apply amusical_injective
    rw [amusical_amusicalInv, ← hg, amusical_amusicalInv]
  have hcomm : ∀ (j : ℤ) (n : ℤ),
      g ((amusicalPerm ^ j) n) = (amusicalPerm ^ j) (g n) := by
    intro j
    induction j using Int.induction_on with
    | zero => intro n; simp
    | succ j ih =>
        intro n
        rw [zpow_add_one, Equiv.Perm.mul_apply, ih, Equiv.Perm.mul_apply]
        exact congrArg (fun z => (amusicalPerm ^ (j : ℤ)) z) (hg n)
    | pred j ih =>
        intro n
        rw [zpow_sub_one, Equiv.Perm.mul_apply, ih, Equiv.Perm.mul_apply]
        exact congrArg (fun z => (amusicalPerm ^ (-(j : ℤ))) z) (hgInv n)
  have hmin_map : ∀ {n : ℤ}, IsOrbitMin n → IsOrbitMin (g n) := by
    intro n hn y hy
    obtain ⟨j, rfl⟩ := hy
    change g n ≤ (amusicalPerm ^ j) (g n)
    rw [← hcomm]
    exact hmono.monotone (hn _ ⟨j, rfl⟩)
  obtain ⟨m, hmpos, hmmin, _⟩ := hinf
  have hseq : StrictMono (fun k : ℕ => g^[k] m) :=
    hmono.strictMono_iterate_of_lt_map (hgt m hmpos)
  have hmins : ∀ k : ℕ, IsOrbitMin (g^[k] m) := by
    intro k
    induction k with
    | zero => simpa using hmmin
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact hmin_map ih
  have hnonneg : ∀ k : ℕ, 0 ≤ g^[k] m := by
    intro k
    induction k with
    | zero => simpa using hmpos.le
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact hpos _ ih
  apply amusicalInfinitelyManyOrbits_of_minima
  refine (Set.infinite_range_of_injective hseq.injective).mono ?_
  rintro _ ⟨k, rfl⟩
  exact ⟨hnonneg k, hmins k⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem windowTwo_nonnegative_periodic_classify :
    ∀ z : Fin 2346, amusical^[12] (z : ℤ) = (z : ℤ) →
      ∃ j : Fin 31, (z : ℤ) = windowTwoPeriodicPoint j := by
  decide +kernel

private theorem windowTwoPeriodicPoint_neg (j : Fin 31) :
    ∃ k : Fin 31, -windowTwoPeriodicPoint j = windowTwoPeriodicPoint k := by
  fin_cases j <;> decide +kernel

set_option maxHeartbeats 1000000 in
private theorem windowTwo_periodic_point_exists (y : ℤ) (h : amusical^[12] y = y) :
    ∃ j : Fin 31, y = windowTwoPeriodicPoint j := by
  obtain ⟨B, c, hB12, hB24, hc, heq⟩ := amusical_iterate_affine 12 y
  rw [h] at heq
  have hslope : (7153 : ℤ) ≤ |(3 : ℤ) ^ 12 - 2 ^ B| := by
    interval_cases B <;> norm_num
  have hid : ((3 : ℤ) ^ 12 - 2 ^ B) * y = -c := by
    linear_combination -heq
  have habsprod : |(3 : ℤ) ^ 12 - 2 ^ B| * |y| = |c| := by
    calc
      |(3 : ℤ) ^ 12 - 2 ^ B| * |y| = |((3 : ℤ) ^ 12 - 2 ^ B) * y| := by
        rw [abs_mul]
      _ = |-c| := by rw [hid]
      _ = |c| := abs_neg c
  have hmul := mul_le_mul_of_nonneg_right hslope (abs_nonneg y)
  rw [habsprod] at hmul
  norm_num at hc
  have hyabs : |y| ≤ 2345 := by omega
  have hneg_iterate : ∀ k x, amusical^[k] (-x) = -amusical^[k] x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        intro x
        rw [Function.iterate_succ_apply', ih, amusical_neg,
          Function.iterate_succ_apply']
  have habsperiod : amusical^[12] |y| = |y| := by
    by_cases hy : 0 ≤ y
    · simpa [abs_of_nonneg hy] using h
    · have hylt : y < 0 := lt_of_not_ge hy
      rw [abs_of_neg hylt, hneg_iterate, h]
  have hnat : y.natAbs ≤ 2345 := by
    rw [← Int.natCast_natAbs] at hyabs
    exact_mod_cast hyabs
  let z : Fin 2346 := ⟨y.natAbs, by omega⟩
  have hzcast : (z : ℤ) = |y| := by
    simp [z]
  have hzperiod : amusical^[12] (z : ℤ) = (z : ℤ) := by
    simpa only [hzcast] using habsperiod
  obtain ⟨j, hj⟩ := windowTwo_nonnegative_periodic_classify z hzperiod
  have habsj : |y| = windowTwoPeriodicPoint j := hzcast.symm.trans hj
  rcases eq_or_eq_neg_of_abs_eq habsj with hy | hy
  · exact ⟨j, hy⟩
  · obtain ⟨k, hk⟩ := windowTwoPeriodicPoint_neg j
    exact ⟨k, hy.trans hk⟩

private theorem commuting_eq_of_stepSym_eq {g q : ℤ → ℤ}
    (hg : ∀ n, g (amusical n) = amusical (g n))
    (hq : ∀ n, q (amusical n) = amusical (q n))
    (hs : ∀ n, stepSym (g n) = stepSym (q n)) : g = q := by
  funext n
  apply eq_of_stepSym_iterate_eq
  intro i
  change stepSym (amusical^[i] (g n)) = stepSym (amusical^[i] (q n))
  have iter_g : ∀ k x, g (amusical^[k] x) = amusical^[k] (g x) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        intro x
        rw [Function.iterate_succ_apply', hg, ih, Function.iterate_succ_apply']
  have iter_q : ∀ k x, q (amusical^[k] x) = amusical^[k] (q x) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        intro x
        rw [Function.iterate_succ_apply', hq, ih, Function.iterate_succ_apply']
  rw [← iter_g, ← iter_q]
  exact hs _

private theorem stepSym_neg (n : ℤ) : stepSym (-n) = -stepSym n := by
  unfold stepSym
  split_ifs <;> apply Fin.ext <;> simp_all <;> first | rfl | omega

/-- **Proved (window-2 centralizer).**  A map commuting with `U` whose step symbol reads
`stepSym n` and `stepSym (U n)` is one of `0, 1, −1, id, −id, U, −U`.
Paper proof: the forward
itinerary of `g x` is the block code of that of `x`, so `g` maps each cycle point to an integer
periodic point of period dividing its period; an affine bound and finite certificate put the
image on the nine known cycles.  Of the `3⁹` tables exactly these seven pass
(`scripts/amusical/central_w2.py`),
and the table determines `g` since an integer is determined by its forward itinerary
(`reversor_eq_of_stepSym_eq` argument). -/
theorem commuting_window_two (f : Fin 3 → Fin 3 → Fin 3) {g : ℤ → ℤ}
    (hg : ∀ n, g (amusical n) = amusical (g n))
    (hloc : ∀ n, stepSym (g n) = f (stepSym n) (stepSym (amusical n))) :
    g = (fun _ => 0) ∨ g = (fun _ => 1) ∨ g = (fun _ => -1) ∨ g = id ∨ g = Neg.neg ∨
      g = amusical ∨ g = fun n => -amusical n := by
  rcases windowTwo_table_classify windowTwo_periodic_point_exists f hg hloc with
    hf | hf | hf | hf | hf | hf | hf
  · left
    apply commuting_eq_of_stepSym_eq hg
    · intro n
      norm_num [amusical]
    · intro n
      rw [hloc, hf]
      norm_num [stepSym]
  · right; right; right; left
    apply commuting_eq_of_stepSym_eq hg
    · intro n
      rfl
    · intro n
      rw [hloc, hf]
      rfl
  · right; right; right; right; left
    apply commuting_eq_of_stepSym_eq hg
    · intro n
      exact (amusical_neg n).symm
    · intro n
      rw [hloc, hf]
      exact (stepSym_neg n).symm
  · right; right; right; right; right; left
    apply commuting_eq_of_stepSym_eq hg
    · intro n
      rfl
    · intro n
      rw [hloc, hf]
  · right; right; right; right; right; right
    apply commuting_eq_of_stepSym_eq hg
    · intro n
      exact (amusical_neg (amusical n)).symm
    · intro n
      rw [hloc, hf]
      exact (stepSym_neg (amusical n)).symm
  · right; left
    apply commuting_eq_of_stepSym_eq hg
    · intro n
      norm_num [amusical]
    · intro n
      rw [hloc, hf]
      norm_num [stepSym]
  · right; right; left
    apply commuting_eq_of_stepSym_eq hg
    · intro n
      norm_num [amusical]
    · intro n
      rw [hloc, hf]
      norm_num [stepSym]

end CollatzMoonshot.Amusical
