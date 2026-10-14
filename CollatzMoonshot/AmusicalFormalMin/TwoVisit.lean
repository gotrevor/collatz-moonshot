/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalWindow
import CollatzMoonshot.AmusicalFormalMin.Bookkeeping

/-!
# The two-visit lemma for Proposition G1

For every modulus `M`, residues `r, r'` and every large `s`, some `x ∈ [2ˢ, 2ˢ⁺¹)` with
`x ≡ r` has an iterate `Uʲ x ∈ [2ˢ, 2ˢ⁺¹)` with `Uʲ x ≡ r' (mod M)` (`exists_two_visit`).

The construction is the Proposition P word of `AmusicalGlobal.lean` (prefix marker for the
`2`-part, suffix marker for the `3`-part, connector for the prime-to-`6` part), with two changes
that replace the paper's irrationality-of-`log(3/2)/log(4/3)` balancing:
* the connector has a fixed shape (`q` translation units padded by identity blocks to a fixed
  length, all odd steps), so its length and bit count do not depend on the residues;
* a run of `L'` even steps, inserted before the connector, is chosen *minimal* with
  `3^L ≥ 2^B`; then the slope `3^L / 2^B` lies in `[1, 3/2)`, enough to return to the block.

The modular connector machinery below is copied from the `private` section of
`AmusicalGlobal.lean` (that file is owned by another treadmill).
-/

namespace CollatzMoonshot.Amusical.TwoVisit

open CollatzMoonshot.Amusical

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
/-! ## Itineraries as a predicate on lists -/

/-- `x` follows the branch word `w` for `|w|` steps. -/
def Follows (x : ℤ) : List (Fin 3) → Prop
  | [] => True
  | s :: w => stepSym x = s ∧ Follows (amusical x) w

theorem follows_iff : ∀ (w : List (Fin 3)) (x : ℤ),
    Follows x w ↔ ∀ i (hi : i < w.length), stepSym (amusical^[i] x) = w[i]
  | [], x => by simp [Follows]
  | s :: w, x => by
      rw [Follows, follows_iff w (amusical x)]
      constructor
      · rintro ⟨h0, h⟩ i hi
        cases i with
        | zero => simpa using h0
        | succ i =>
            rw [Function.iterate_succ_apply]
            simpa using h i (by simpa using hi)
      · intro h
        refine ⟨h 0 (by simp), fun i hi => ?_⟩
        have := h (i + 1) (by simpa using hi)
        rw [Function.iterate_succ_apply] at this
        simpa using this

theorem follows_append : ∀ (u v : List (Fin 3)) (x : ℤ),
    Follows x (u ++ v) ↔ Follows x u ∧ Follows (amusical^[u.length] x) v
  | [], v, x => by simp [Follows]
  | s :: u, v, x => by
      rw [List.cons_append, Follows, Follows, follows_append u v (amusical x),
        List.length_cons, Function.iterate_succ_apply, and_assoc]

/-- The word read off the first `n` steps of `x`. -/
def orbitWord (x : ℤ) (n : ℕ) : List (Fin 3) :=
  List.ofFn fun i : Fin n => stepSym (amusical^[i.val] x)

theorem orbitWord_length (x : ℤ) (n : ℕ) : (orbitWord x n).length = n := by
  simp [orbitWord]

theorem follows_orbitWord (x : ℤ) (n : ℕ) : Follows x (orbitWord x n) := by
  rw [follows_iff]
  intro i hi
  simp [orbitWord, List.getElem_ofFn]

theorem follows_exists (w : List (Fin 3)) : ∃ m : ℤ, Follows m w := by
  obtain ⟨m, hm⟩ := exists_forward_itinerary_local w
  exact ⟨m, (follows_iff w m).mpr hm⟩

theorem follows_add_pow_four_mul {w : List (Fin 3)} {m : ℤ} (h : Follows m w) (q : ℤ) :
    Follows (m + (4 : ℤ) ^ w.length * q) w := by
  rw [follows_iff] at h ⊢
  intro i hi
  rw [stepSym_iterate_add_pow_four_mul w.length i hi m q]
  exact h i hi

theorem two_pow_dvd_of_follows {w : List (Fin 3)} {x y : ℤ} (hx : Follows x w)
    (hy : Follows y w) : (2 : ℤ) ^ w.length ∣ x - y := by
  rw [follows_iff] at hx hy
  apply pow_two_dvd_sub_of_stepSym_iterate_eq
  intro i hi
  have h := (hx i hi).trans (hy i hi).symm
  exact h

theorem three_pow_dvd_of_follows {w : List (Fin 3)} {x y : ℤ} (hx : Follows x w)
    (hy : Follows y w) :
    (3 : ℤ) ^ w.length ∣ amusical^[w.length] x - amusical^[w.length] y := by
  rw [follows_iff] at hx hy
  apply pow_three_dvd_iterate_sub_of_symbols
  intro i hi
  exact (hx i hi).trans (hy i hi).symm

theorem cast_iterate_of_follows (m : ℕ) (hcop : m.Coprime 6) {w : List (Fin 3)} {x : ℤ}
    (hx : Follows x w) : (amusical^[w.length] x : ZMod m) = act m w x :=
  cast_iterate_eq_act m hcop w x ((follows_iff w x).mp hx)

/-! ## Bit counts -/

def symBits (s : Fin 3) : ℕ := if s = 0 then 1 else 2

def wordBits (w : List (Fin 3)) : ℕ := (w.map symBits).sum

theorem wordBits_append (u v : List (Fin 3)) :
    wordBits (u ++ v) = wordBits u + wordBits v := by
  simp [wordBits]

theorem length_le_wordBits (w : List (Fin 3)) : w.length ≤ wordBits w := by
  induction w with
  | nil => simp [wordBits]
  | cons s w ih =>
      simp only [wordBits, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
      have : 1 ≤ symBits s := by unfold symBits; split_ifs <;> omega
      omega

theorem wordBits_replicate_zero (e : ℕ) : wordBits (List.replicate e (0 : Fin 3)) = e := by
  simp [wordBits, symBits]

theorem wordBits_of_ne_zero (w : List (Fin 3)) (h : ∀ s ∈ w, s ≠ 0) :
    wordBits w = 2 * w.length := by
  induction w with
  | nil => simp [wordBits]
  | cons s w ih =>
      have hs := h s (by simp)
      have ih' := ih (fun t ht => h t (by simp [ht]))
      simp only [wordBits, List.map_cons, List.sum_cons, List.length_cons] at ih' ⊢
      rw [ih']
      simp [symBits, hs]
      ring

theorem stepBits_eq_symBits (x : ℤ) : stepBits x = symBits (stepSym x) := by
  unfold stepBits stepSym symBits
  split_ifs <;> simp_all

theorem fwdBits_succ' (x : ℤ) (n : ℕ) :
    fwdBits x (n + 1) = stepBits x + fwdBits (amusical x) n := by
  unfold fwdBits
  rw [Finset.sum_range_succ', add_comm]
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]

theorem fwdBits_of_follows : ∀ (w : List (Fin 3)) (x : ℤ), Follows x w →
    fwdBits x w.length = wordBits w
  | [], x, _ => by simp [fwdBits, wordBits]
  | s :: w, x, ⟨h0, h⟩ => by
      rw [List.length_cons, fwdBits_succ', fwdBits_of_follows w (amusical x) h,
        stepBits_eq_symBits, h0]
      simp [wordBits]

theorem fwdBits_le (x : ℤ) (L : ℕ) : fwdBits x L ≤ 2 * L := by
  induction L with
  | zero => simp [fwdBits]
  | succ L ih =>
      rw [fwdBits_succ]
      unfold stepBits
      split_ifs <;> omega

theorem amusical_step_affine' (x : ℤ) :
    ∃ e : ℤ, |e| ≤ 1 ∧ 2 ^ stepBits x * amusical x = 3 * x + e := by
  unfold stepBits amusical
  split_ifs <;>
    first
    | exact ⟨0, by norm_num, by omega⟩
    | exact ⟨1, by norm_num, by omega⟩
    | exact ⟨-1, by norm_num, by omega⟩

/-- The affine ledger `2^B Uᴸ x = 3ᴸ x + c`, `|c| < 4ᴸ`, with `B` the actual bit count. -/
theorem amusical_iterate_affine_bits (L : ℕ) (x : ℤ) :
    ∃ c : ℤ, |c| < 4 ^ L ∧ 2 ^ fwdBits x L * amusical^[L] x = 3 ^ L * x + c := by
  induction L with
  | zero => exact ⟨0, by simp, by simp [fwdBits]⟩
  | succ L ih =>
      obtain ⟨c, hc, heq⟩ := ih
      obtain ⟨e, he, hstep⟩ := amusical_step_affine' (amusical^[L] x)
      refine ⟨3 * c + 2 ^ fwdBits x L * e, ?_, ?_⟩
      · have hpowNat : 2 ^ fwdBits x L ≤ (4 : ℕ) ^ L := by
          calc
            2 ^ fwdBits x L ≤ 2 ^ (2 * L) := Nat.pow_le_pow_right (by norm_num) (fwdBits_le x L)
            _ = 4 ^ L := by rw [pow_mul]; norm_num
        have hpow : (2 : ℤ) ^ fwdBits x L ≤ 4 ^ L := by exact_mod_cast hpowNat
        have h2pos : (0 : ℤ) < 2 ^ fwdBits x L := by positivity
        calc
          |3 * c + 2 ^ fwdBits x L * e| ≤ |3 * c| + |2 ^ fwdBits x L * e| := abs_add_le _ _
          _ = 3 * |c| + 2 ^ fwdBits x L * |e| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ 3),
              abs_of_pos h2pos]
          _ ≤ 3 * |c| + 4 ^ L := by
            have he' : 2 ^ fwdBits x L * |e| ≤ (2 : ℤ) ^ fwdBits x L :=
              mul_le_of_le_one_right h2pos.le he
            omega
          _ < 4 ^ (L + 1) := by
            rw [pow_succ]
            have hfour : (0 : ℤ) < 4 ^ L := by positivity
            omega
      · rw [Function.iterate_succ_apply', fwdBits_succ, pow_add]
        calc
          2 ^ fwdBits x L * 2 ^ stepBits (amusical^[L] x) * amusical (amusical^[L] x) =
              2 ^ fwdBits x L * (3 * amusical^[L] x + e) := by rw [mul_assoc, hstep]
          _ = 3 * (2 ^ fwdBits x L * amusical^[L] x) + 2 ^ fwdBits x L * e := by ring
          _ = 3 * (3 ^ L * x + c) + 2 ^ fwdBits x L * e := by rw [heq]
          _ = 3 ^ (L + 1) * x + (3 * c + 2 ^ fwdBits x L * e) := by ring

/-! ## Fixed-shape connectors -/

/-- `q` translation units, padded by identity blocks `B^{m!}` to `Q` units. -/
def connectorFixed (m Q q : ℕ) : List (Fin 3) :=
  connectorCore m q ++ List.replicate (m.factorial * (Q - q)) (1 : Fin 3)

theorem act_connectorFixed (m Q q : ℕ) [NeZero m]
    (h3 : IsUnit (3 : ZMod m)) (h4 : IsUnit (4 : ZMod m)) (z : ZMod m) :
    act m (connectorFixed m Q q) z = z + (q : ZMod m) * (-2 * (3 : ZMod m)⁻¹) := by
  rw [connectorFixed, act_append, act_connectorCore m q h3 h4, act_replicate_one,
    Function.iterate_mul, bcycle m h3 h4, Function.iterate_id]
  rfl

theorem length_connectorFixed (m Q q : ℕ) (hq : q ≤ Q) :
    (connectorFixed m Q q).length = m.factorial * Q := by
  have hf : 0 < m.factorial := Nat.factorial_pos m
  simp only [connectorFixed, connectorCore, connectorUnit, List.length_append,
    List.length_flatten, List.length_replicate, List.map_replicate, List.sum_replicate,
    smul_eq_mul, List.length_cons]
  rw [Nat.sub_add_cancel hf, mul_comm q, ← Nat.mul_add, Nat.add_sub_cancel' hq]

theorem ne_zero_of_mem_connectorFixed {m Q q : ℕ} {s : Fin 3}
    (hs : s ∈ connectorFixed m Q q) : s ≠ 0 := by
  simp only [connectorFixed, connectorCore, connectorUnit, List.mem_append, List.mem_flatten,
    List.mem_replicate, List.mem_cons] at hs
  rcases hs with ⟨l, ⟨_, rfl⟩, h⟩ | ⟨_, rfl⟩
  · simp only [List.mem_cons, List.mem_replicate] at h
    rcases h with rfl | ⟨_, rfl⟩ <;> decide
  · decide

/-! ## Realization and return to the block -/

/-- A word's cylinder, intersected with a residue class mod `O` prime to `2`, contains a full
residue class mod some `P`. -/
theorem realize (w : List (Fin 3)) (O : ℕ) (hO : O.Coprime 2) (r : ℤ) :
    ∃ xs : ℤ, ∃ P : ℕ, 0 < P ∧
      ∀ x : ℤ, x ≡ xs [ZMOD P] → x ≡ r [ZMOD O] ∧ Follows x w := by
  obtain ⟨m, hmw⟩ := follows_exists w
  set D := w.length with hD
  have hO4 : O.Coprime (4 ^ D) := by
    have : O.Coprime 4 := by convert hO.pow_right 2 using 1
    exact this.pow_right D
  have hcop : IsCoprime (O : ℤ) ((4 : ℤ) ^ D) := by
    have := Nat.Coprime.isCoprime hO4
    exact_mod_cast this
  obtain ⟨q₀, hq₀⟩ : ∃ q : ℤ, (4 : ℤ) ^ D * q ≡ r - m [ZMOD O] :=
    exists_mul_modEq_of_isCoprime hcop
  refine ⟨m + 4 ^ D * q₀, 4 ^ D * O, ?_, fun x hx => ?_⟩
  · have : 0 < O := by
      rcases Nat.eq_zero_or_pos O with h | h
      · rw [h] at hO; norm_num at hO
      · exact h
    positivity
  obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.mp hx.symm
  push_cast at ht
  constructor
  · rw [Int.modEq_iff_dvd] at hq₀ ⊢
    obtain ⟨c, hc⟩ := hq₀
    exact ⟨c - 4 ^ D * t, by linear_combination hc - ht⟩
  · have hx' : x = m + (4 : ℤ) ^ w.length * (q₀ + O * t) := by
      rw [← hD]; linear_combination ht
    rw [hx']
    exact follows_add_pow_four_mul hmw _

/-- With slope `3ᴸ / 2ᴮ ∈ [1, 3/2)`, a point placed low enough in the block `[2ˢ, 2ˢ⁺¹)`
returns to it after `L` steps. -/
theorem level_return {L B s : ℕ} {x y c : ℤ} (h1 : (2 : ℤ) ^ B ≤ 3 ^ L)
    (h2 : 2 * (3 : ℤ) ^ L < 3 * 2 ^ B) (hc : |c| < 4 ^ L)
    (heq : 2 ^ B * y = 3 ^ L * x + c) (hlo : (2 : ℤ) ^ s + 4 ^ L ≤ x)
    (hhi : 3 * x + 2 * 4 ^ L ≤ 4 * 2 ^ s) : (2 : ℤ) ^ s ≤ y ∧ y < 2 ^ (s + 1) := by
  have hP : (1 : ℤ) ≤ 2 ^ B := one_le_pow₀ (by norm_num)
  have h4 : (0 : ℤ) < 4 ^ L := by positivity
  have hs : (0 : ℤ) < 2 ^ s := by positivity
  have hx0 : 0 ≤ x := by linarith
  have hcl := neg_abs_le c
  have hcu := le_abs_self c
  constructor
  · by_contra hy
    push Not at hy
    have hy' : y + 4 ^ L ≤ x := by linarith
    have : 2 ^ B * (y + 4 ^ L) ≤ 2 ^ B * x := mul_le_mul_of_nonneg_left hy' (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right h1 hx0]
  · rw [pow_succ]
    by_contra hy
    push Not at hy
    have hmul : 2 ^ B * (2 * (2 ^ s * 2)) ≤ 2 ^ B * (2 * y) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right h2.le hx0]

theorem three_pow_lt_two_pow (n k : ℕ) : 3 ^ (3 * n + 1 + k) < 2 ^ (5 * n + 2 + 2 * k) := by
  have e1 : 3 ^ (3 * n + 1 + k) = 27 ^ n * 3 * 3 ^ k := by
    rw [pow_add, pow_add, pow_mul]; norm_num
  have e2 : 2 ^ (5 * n + 2 + 2 * k) = 32 ^ n * 4 * 4 ^ k := by
    rw [pow_add, pow_add, pow_mul, pow_mul]; norm_num
  rw [e1, e2]
  have a1 : 27 ^ n ≤ 32 ^ n := Nat.pow_le_pow_left (by norm_num) n
  have a2 : 3 ^ k ≤ 4 ^ k := Nat.pow_le_pow_left (by norm_num) k
  calc
    27 ^ n * 3 * 3 ^ k < 27 ^ n * 4 * 3 ^ k := by gcongr; norm_num
    _ ≤ 32 ^ n * 4 * 4 ^ k := by gcongr

theorem modEq_of_dvd_parts {a b m₀ : ℕ} (hc2 : m₀.Coprime 2) (hc3 : m₀.Coprime 3) {u v : ℤ}
    (h2 : (2 : ℤ) ^ a ∣ u - v) (h3 : (3 : ℤ) ^ b ∣ u - v) (hm : (m₀ : ℤ) ∣ u - v) :
    u ≡ v [ZMOD ((2 ^ a * (3 ^ b * m₀) : ℕ) : ℤ)] := by
  have c1 : IsCoprime ((3 : ℤ) ^ b) (m₀ : ℤ) := by
    have := Nat.Coprime.isCoprime (hc3.symm.pow_left b)
    exact_mod_cast this
  have c2 : IsCoprime ((2 : ℤ) ^ a) ((3 : ℤ) ^ b * m₀) := by
    have h23 : (2 ^ a).Coprime (3 ^ b * m₀) :=
      (((by norm_num : (2 : ℕ).Coprime 3).pow_left a).pow_right b).mul_right
        (hc2.symm.pow_left a)
    have := Nat.Coprime.isCoprime h23
    exact_mod_cast this
  rw [Int.modEq_iff_dvd]
  push_cast
  exact dvd_sub_comm.mp (c2.mul_dvd h2 (c1.mul_dvd h3 hm))

/-- Connectors of one fixed length `Lc ≥ K`, all odd steps, realize every translation. -/
theorem exists_fixed_connector (m₀ : ℕ) [NeZero m₀] (hc2 : m₀.Coprime 2) (hc3 : m₀.Coprime 3)
    (K : ℕ) : ∃ Lc : ℕ, K ≤ Lc ∧ ∀ s t : ZMod m₀, ∃ conn : List (Fin 3),
      act m₀ conn s = t ∧ conn.length = Lc ∧ wordBits conn = 2 * Lc := by
  have h2 : IsUnit (2 : ZMod m₀) := (ZMod.isUnit_iff_coprime 2 m₀).mpr hc2.symm
  have h3 : IsUnit (3 : ZMod m₀) := (ZMod.isUnit_iff_coprime 3 m₀).mpr hc3.symm
  have h4 : IsUnit (4 : ZMod m₀) := by
    convert h2.mul h2 using 1
    norm_num
  have hd : IsUnit (-2 * (3 : ZMod m₀)⁻¹) := by
    have hinv3 : IsUnit ((3 : ZMod m₀)⁻¹) :=
      isUnit_iff_exists_inv.mpr ⟨3, ZMod.inv_mul_of_unit 3 h3⟩
    exact h2.neg.mul hinv3
  refine ⟨m₀.factorial * (m₀ + K), ?_, fun s t => ?_⟩
  · exact le_trans (by omega) (Nat.le_mul_of_pos_left _ (Nat.factorial_pos m₀))
  set d : ZMod m₀ := -2 * (3 : ZMod m₀)⁻¹ with hd_def
  have hqlt := ZMod.val_lt ((t - s) * d⁻¹)
  refine ⟨connectorFixed m₀ (m₀ + K) ((t - s) * d⁻¹).val, ?_, ?_, ?_⟩
  · rw [act_connectorFixed _ _ _ h3 h4, ← hd_def, ZMod.natCast_zmod_val, mul_assoc,
      ZMod.inv_mul_of_unit d hd, mul_one]
    ring
  · exact length_connectorFixed _ _ _ (by omega)
  · rw [wordBits_of_ne_zero _ (fun s hs => ne_zero_of_mem_connectorFixed hs),
      length_connectorFixed _ _ _ (by omega)]

/-- The balanced word: it fixes the start mod `2^a`, the end mod `3^b`, carries `r` to `r'` mod
`m₀`, and has slope `3ᴸ / 2ᴮ ∈ [1, 3/2)`. -/
theorem exists_balanced_word (a b m₀ : ℕ) [NeZero m₀] (hc2 : m₀.Coprime 2)
    (hc3 : m₀.Coprime 3) (r r' : ℤ) :
    ∃ block : List (Fin 3),
      (∀ x, Follows x block →
        (2 : ℤ) ^ a ∣ x - r ∧ (3 : ℤ) ^ b ∣ amusical^[block.length] x - r') ∧
      act m₀ block (r : ZMod m₀) = r' ∧
      (2 : ℤ) ^ wordBits block ≤ 3 ^ block.length ∧
      2 * (3 : ℤ) ^ block.length < 3 * 2 ^ wordBits block := by
  have hc6 : m₀.Coprime 6 := by
    convert hc2.mul_right hc3 using 1
  obtain ⟨pre, hpreF, hpreLen⟩ : ∃ w, Follows r w ∧ w.length = a :=
    ⟨_, follows_orbitWord r a, orbitWord_length r a⟩
  obtain ⟨suf, hsufF, hsufLen⟩ : ∃ w, Follows (amusicalInv^[b] r') w ∧ w.length = b :=
    ⟨_, follows_orbitWord _ b, orbitWord_length _ b⟩
  have hrb : amusical^[b] (amusicalInv^[b] r') = r' := amusical_iterate_amusicalInv_iterate b r'
  obtain ⟨Lc, hLc, hconnex⟩ := exists_fixed_connector m₀ hc2 hc3 (2 * (a + b) + 1)
  obtain ⟨L0, hL0⟩ : ∃ L0, L0 = a + Lc + b := ⟨_, rfl⟩
  obtain ⟨B0, hB0⟩ : ∃ B0, B0 = wordBits pre + 2 * Lc + wordBits suf := ⟨_, rfl⟩
  have hpreB : a ≤ wordBits pre := hpreLen ▸ length_le_wordBits pre
  have hsufB : b ≤ wordBits suf := hsufLen ▸ length_le_wordBits suf
  have h0 : 3 ^ L0 < 2 ^ B0 := by
    have hle : 2 ^ (a + b + 2 * Lc) ≤ 2 ^ B0 := Nat.pow_le_pow_right (by norm_num) (by omega)
    refine lt_of_lt_of_le ?_ hle
    obtain ⟨k, hk⟩ : ∃ k, Lc = 2 * (a + b) + 1 + k := ⟨Lc - (2 * (a + b) + 1), by omega⟩
    have e1 : L0 = 3 * (a + b) + 1 + k := by omega
    have e2 : a + b + 2 * Lc = 5 * (a + b) + 2 + 2 * k := by omega
    rw [e1, e2]
    exact three_pow_lt_two_pow (a + b) k
  have hex : ∃ e : ℕ, 2 ^ B0 * 2 ^ e ≤ 3 ^ L0 * 3 ^ e := by
    refine ⟨2 * B0, ?_⟩
    have : 2 ^ B0 * 2 ^ (2 * B0) ≤ 3 ^ (2 * B0) := by
      rw [← pow_add, show B0 + 2 * B0 = 3 * B0 by ring, pow_mul, pow_mul]
      exact Nat.pow_le_pow_left (by norm_num) B0
    calc
      _ ≤ 3 ^ (2 * B0) := this
      _ ≤ 3 ^ L0 * 3 ^ (2 * B0) := Nat.le_mul_of_pos_left _ (by positivity)
  classical
  obtain ⟨e, he, he1⟩ : ∃ e, 2 ^ B0 * 2 ^ e ≤ 3 ^ L0 * 3 ^ e ∧
      ∀ e' < e, ¬ 2 ^ B0 * 2 ^ e' ≤ 3 ^ L0 * 3 ^ e' :=
    ⟨Nat.find hex, Nat.find_spec hex, fun e' he' => Nat.find_min hex he'⟩
  have he0 : e ≠ 0 := by
    intro h
    rw [h] at he
    simp only [pow_zero, mul_one] at he
    omega
  have he1' : 3 ^ L0 * 3 ^ (e - 1) < 2 ^ B0 * 2 ^ (e - 1) := by
    have := he1 (e - 1) (by omega)
    push Not at this
    exact this
  obtain ⟨z, hz⟩ := act_surjective m₀ hc6 suf (r' : ZMod m₀)
  obtain ⟨conn, hconn, hconnLen, hconnBits⟩ :=
    hconnex (act m₀ (List.replicate e (0 : Fin 3)) (act m₀ pre (r : ZMod m₀))) z
  refine ⟨pre ++ (List.replicate e 0 ++ (conn ++ suf)), fun x hx => ?_, ?_, ?_, ?_⟩
  · rw [follows_append, follows_append, follows_append] at hx
    obtain ⟨hx1, -, -, hx4⟩ := hx
    refine ⟨hpreLen ▸ two_pow_dvd_of_follows hx1 hpreF, ?_⟩
    have := three_pow_dvd_of_follows hx4 hsufF
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply,
      ← Function.iterate_add_apply, hsufLen, hrb] at this
    convert this using 4
    simp only [List.length_append, List.length_replicate, hconnLen, hpreLen, hsufLen]
    omega
  · rw [act_append, act_append, act_append, hconn, hz]
  · rw [wordBits_append, wordBits_append, wordBits_append, wordBits_replicate_zero, hconnBits]
    simp only [List.length_append, List.length_replicate, hconnLen, hpreLen, hsufLen]
    have : wordBits pre + (e + (2 * Lc + wordBits suf)) = B0 + e := by omega
    rw [this, show a + (e + (Lc + b)) = L0 + e by omega, pow_add, pow_add]
    exact_mod_cast he
  · rw [wordBits_append, wordBits_append, wordBits_append, wordBits_replicate_zero, hconnBits]
    simp only [List.length_append, List.length_replicate, hconnLen, hpreLen, hsufLen]
    have : wordBits pre + (e + (2 * Lc + wordBits suf)) = B0 + (e - 1) + 1 := by omega
    rw [this, show a + (e + (Lc + b)) = L0 + (e - 1) + 1 by omega]
    have hnat : 2 * 3 ^ (L0 + (e - 1) + 1) < 3 * 2 ^ (B0 + (e - 1) + 1) := by
      rw [pow_succ, pow_succ, pow_add, pow_add]
      calc
        2 * (3 ^ L0 * 3 ^ (e - 1) * 3) = 6 * (3 ^ L0 * 3 ^ (e - 1)) := by ring
        _ < 6 * (2 ^ B0 * 2 ^ (e - 1)) := by omega
        _ = 3 * (2 ^ B0 * 2 ^ (e - 1) * 2) := by ring
    exact_mod_cast hnat

/-- **Proved (two-visit lemma).**  For every modulus `M`, residues `r, r'`, and every large `s`,
some `x ∈ [2ˢ, 2ˢ⁺¹)` with `x ≡ r` has an iterate `Uʲ x ∈ [2ˢ, 2ˢ⁺¹)` with `Uʲ x ≡ r'`.
Proof: write `M = 2^a 3^b m₀`.  Follow the word `pre · Eᵉ · conn · suf · pre'`:
* `pre`, `pre'` are `a` steps of `r`, `r'`; they fix both visits mod `2^a`;
* `suf` is the `b` steps into `r'`; it fixes the second visit mod `3^b`;
* `conn` is a fixed-shape connector fixing the prime-to-`6` part;
* `e` is minimal with `3ᴸ ≥ 2ᴮ`, so the slope lies in `[1, 3/2)`.
Take `x` in the word's cylinder, `≡ r mod 3^b m₀`, just above `2ˢ`. -/
theorem exists_two_visit (M : ℕ) (hM : 0 < M) (r r' : ℤ) :
    ∃ S : ℕ, ∀ s ≥ S, ∃ x : ℤ, ∃ j : ℕ,
      (2 : ℤ) ^ s ≤ x ∧ x < 2 ^ (s + 1) ∧ (2 : ℤ) ^ s ≤ amusical^[j] x ∧
        amusical^[j] x < 2 ^ (s + 1) ∧ x ≡ r [ZMOD M] ∧ amusical^[j] x ≡ r' [ZMOD M] := by
  obtain ⟨a, m₁, hm₁two, hMfac⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hM.ne' 2 (by norm_num)
  have hm₁ : 0 < m₁ := by
    rcases Nat.eq_zero_or_pos m₁ with h | h
    · rw [h] at hMfac; omega
    · exact h
  obtain ⟨b, m₀, hm₀three, hm₁fac⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hm₁.ne' 3 (by norm_num)
  have hm₀ : 0 < m₀ := by
    rcases Nat.eq_zero_or_pos m₀ with h | h
    · rw [h] at hm₁fac; omega
    · exact h
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
    convert hc2.mul_right hc3 using 1
  have hMfull : M = 2 ^ a * (3 ^ b * m₀) := by
    rw [hMfac, hm₁fac]
  haveI : NeZero m₀ := ⟨hm₀.ne'⟩
  obtain ⟨block, hmark, hact, hslope1, hslope2⟩ := exists_balanced_word a b m₀ hc2 hc3 r r'
  obtain ⟨pre', hpre'F, hpre'Len⟩ : ∃ w, Follows r' w ∧ w.length = a :=
    ⟨_, follows_orbitWord r' a, orbitWord_length r' a⟩
  obtain ⟨L, hL⟩ : ∃ L, L = block.length := ⟨_, rfl⟩
  have hO2 : (3 ^ b * m₀).Coprime 2 :=
    Nat.Coprime.mul ((by norm_num : (3 : ℕ).Coprime 2).pow_left b) hc2
  obtain ⟨xs, P, hP, hreal⟩ := realize (block ++ pre') (3 ^ b * m₀) hO2 r
  refine ⟨5 * 4 ^ L + 3 * P, fun s hs => ?_⟩
  have h2s : ((5 * 4 ^ L + 3 * P : ℕ) : ℤ) ≤ 2 ^ s := by
    have : 5 * 4 ^ L + 3 * P < 2 ^ s := lt_of_le_of_lt hs Nat.lt_two_pow_self
    exact_mod_cast this.le
  push_cast at h2s
  obtain ⟨base, hbase⟩ : ∃ base : ℤ, base = 2 ^ s + 4 ^ L := ⟨_, rfl⟩
  obtain ⟨x, hx_def⟩ : ∃ x : ℤ, x = base + (xs - base) % P := ⟨_, rfl⟩
  have hPz : (0 : ℤ) < P := by exact_mod_cast hP
  have hxmod : x ≡ xs [ZMOD P] := by
    rw [Int.modEq_iff_dvd]
    refine ⟨(xs - base) / P, ?_⟩
    have := Int.mul_ediv_add_emod (xs - base) P
    rw [hx_def]
    linarith
  have hxlo : base ≤ x := by
    have := Int.emod_nonneg (xs - base) hPz.ne'
    rw [hx_def]
    linarith
  have hxhi : x < base + P := by
    have := Int.emod_lt_of_pos (xs - base) hPz
    rw [hx_def]
    linarith
  obtain ⟨hxO, hxw⟩ := hreal x hxmod
  rw [follows_append] at hxw
  obtain ⟨hxblock, hy⟩ := hxw
  rw [← hL] at hy
  obtain ⟨h2x, h3y⟩ := hmark x hxblock
  rw [← hL] at h3y
  have hO : ((3 ^ b * m₀ : ℕ) : ℤ) ∣ x - r := hxO.symm.dvd
  push_cast at hO
  have hstart : x ≡ r [ZMOD M] := by
    rw [hMfull]
    exact modEq_of_dvd_parts hc2 hc3 h2x ((Dvd.intro _ rfl).trans hO)
      ((Dvd.intro_left _ rfl).trans hO)
  have hend : amusical^[L] x ≡ r' [ZMOD M] := by
    rw [hMfull]
    have h2' : (2 : ℤ) ^ a ∣ amusical^[L] x - r' :=
      hpre'Len ▸ two_pow_dvd_of_follows hy hpre'F
    have hm' : (m₀ : ℤ) ∣ amusical^[L] x - r' := by
      have hcast := cast_iterate_of_follows m₀ hc6 hxblock
      have hx₀ : (x : ZMod m₀) = (r : ZMod m₀) := by
        rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
        exact dvd_sub_comm.mp ((Dvd.intro_left _ rfl).trans hO)
      rw [hx₀, hact, ← hL] at hcast
      exact dvd_sub_comm.mp ((ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hcast)
    exact modEq_of_dvd_parts hc2 hc3 h2' h3y hm'
  obtain ⟨c, hc, heq⟩ := amusical_iterate_affine_bits L x
  rw [hL, fwdBits_of_follows block x hxblock, ← hL] at heq
  rw [← hL] at hslope1 hslope2
  have h4 : (0 : ℤ) < 4 ^ L := by positivity
  have hlev := level_return hslope1 hslope2 hc heq (by rw [← hbase]; exact hxlo)
    (by rw [hbase] at hxhi; linarith)
  refine ⟨x, L, by linarith, ?_, hlev.1, hlev.2, hstart, hend⟩
  rw [pow_succ]
  linarith

/-! ## Inputs for Proposition G1 -/

/-- The two-visit lemma, uniform over residue pairs mod `M`. -/
theorem two_visit_uniform (M : ℕ) [NeZero M] :
    ∃ S : ℕ, ∀ s ≥ S, ∀ ρ ρ' : ZMod M, ∃ x : ℤ, ∃ j : ℕ,
      (2 : ℤ) ^ s ≤ x ∧ x < 2 ^ (s + 1) ∧ (2 : ℤ) ^ s ≤ amusical^[j] x ∧
        amusical^[j] x < 2 ^ (s + 1) ∧ (x : ZMod M) = ρ ∧ (amusical^[j] x : ZMod M) = ρ' := by
  have hcast : ∀ (y : ℤ) (ρ : ZMod M), y ≡ (ρ.val : ℤ) [ZMOD M] → (y : ZMod M) = ρ := by
    intro y ρ h
    rw [(ZMod.intCast_eq_intCast_iff _ _ _).mpr h, Int.cast_natCast, ZMod.natCast_zmod_val]
  have h : ∀ p : ZMod M × ZMod M, ∀ᶠ s in Filter.atTop, ∃ x : ℤ, ∃ j : ℕ,
      (2 : ℤ) ^ s ≤ x ∧ x < 2 ^ (s + 1) ∧ (2 : ℤ) ^ s ≤ amusical^[j] x ∧
        amusical^[j] x < 2 ^ (s + 1) ∧ (x : ZMod M) = p.1 ∧
          (amusical^[j] x : ZMod M) = p.2 := by
    intro p
    obtain ⟨S, hS⟩ := exists_two_visit M (NeZero.pos M) (p.1.val : ℤ) (p.2.val : ℤ)
    filter_upwards [Filter.eventually_ge_atTop S] with s hs
    obtain ⟨x, j, h1, h2, h3, h4, h5, h6⟩ := hS s hs
    exact ⟨x, j, h1, h2, h3, h4, hcast _ _ h5, hcast _ _ h6⟩
  obtain ⟨S, hS⟩ := Filter.eventually_atTop.mp (Filter.eventually_all.mpr h)
  exact ⟨S, fun s hs ρ ρ' => hS s hs (ρ, ρ')⟩

theorem amusical_pos' {x : ℤ} (hx : 0 < x) : 0 < amusical x := by
  unfold amusical
  split_ifs <;> omega

theorem amusical_iterate_pos' {x : ℤ} (hx : 0 < x) (j : ℕ) : 0 < amusical^[j] x := by
  induction j with
  | zero => exact hx
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact amusical_pos' ih

/-- An aperiodic point gives a positive aperiodic point (`U` is odd and fixes `0`). -/
theorem exists_pos_aperiodic (hinf : ∃ x : ℤ, ∀ p : ℕ, 0 < p → amusical^[p] x ≠ x) :
    ∃ x : ℤ, 0 < x ∧ ∀ p : ℕ, 0 < p → amusical^[p] x ≠ x := by
  obtain ⟨x, hx⟩ := hinf
  rcases lt_trichotomy x 0 with h | h | h
  · refine ⟨-x, by omega, fun p hp heq => hx p hp ?_⟩
    rw [amusical_iterate_neg] at heq
    omega
  · exact absurd (by rw [h]; rfl) (hx 1 one_pos)
  · exact ⟨x, h, hx⟩

/-- A positive aperiodic forward orbit visits every dyadic block above its start: it is
unbounded (injective) and a step from below `2ˢ` stays below `2ˢ⁺¹`. -/
theorem orbit_visits_block {x : ℤ} (hx : 0 < x) (hap : ∀ p : ℕ, 0 < p → amusical^[p] x ≠ x)
    (s : ℕ) (hs : x < 2 ^ s) : ∃ j : ℕ, (2 : ℤ) ^ s ≤ amusical^[j] x ∧
      amusical^[j] x < 2 ^ (s + 1) := by
  have hinj := iterate_orbit_injective_of_aperiodic amusical amusical_injective x
    (fun k hk => hap k hk)
  obtain ⟨k, hk⟩ := (eventually_abs_ge_of_injective _ hinj (2 ^ s)).exists
  have hex : ∃ k, (2 : ℤ) ^ s ≤ amusical^[k] x := by
    refine ⟨k, ?_⟩
    rw [abs_of_pos (amusical_iterate_pos' hx k)] at hk
    exact_mod_cast hk
  classical
  obtain ⟨j, hj, hjmin⟩ : ∃ j, (2 : ℤ) ^ s ≤ amusical^[j] x ∧
      ∀ i < j, ¬ (2 : ℤ) ^ s ≤ amusical^[i] x :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩
  have hj0 : j ≠ 0 := by
    intro h
    rw [h, Function.iterate_zero_apply] at hj
    linarith
  have hprev : amusical^[j - 1] x < 2 ^ s := by
    have := hjmin (j - 1) (by omega)
    push Not at this
    exact this
  refine ⟨j, hj, ?_⟩
  have hstep : amusical^[j] x = amusical (amusical^[j - 1] x) := by
    rw [← Function.iterate_succ_apply' amusical (j - 1) x]
    congr 1
    omega
  rw [hstep]
  have hy := amusical_iterate_pos' hx (j - 1)
  have hb := abs_amusical_le (amusical^[j - 1] x)
  rw [abs_of_pos (amusical_pos' hy), abs_of_pos hy] at hb
  have h2b : (2 : ℤ) ≤ 2 ^ stepBits (amusical^[j - 1] x) := by
    unfold stepBits
    split_ifs <;> norm_num
  have hUy := amusical_pos' hy
  rw [pow_succ]
  nlinarith

end CollatzMoonshot.Amusical.TwoVisit
