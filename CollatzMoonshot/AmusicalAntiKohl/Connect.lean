/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalWindow
import CollatzMoonshot.AmusicalContinuousReversor

/-!
# Residue connectivity of `U`

Every residue class modulo `M` reaches every other one under forward iteration of `U`
(`amusical_reach`).  Write `M = 2^a 3^b M₀` with `gcd(M₀, 6) = 1`.  The first `a` step symbols of
`x` fix `x mod 2^a`, the `b` symbols before time `L` fix `Uᴸ x mod 3^b`, and the branch maps act
transitively on `ℤ/M₀` (`g_A⁻¹ g_B` is translation by `−2/3`).  The modular connectors are those
of the global treadmill's proof of `exists_many_returns` (`AmusicalGlobal.lean`), duplicated here
because that module is owned by another treadmill.
-/

namespace CollatzMoonshot.Amusical.AntiKohlConnect

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

/-- Every residue class modulo `M` reaches every other one: for all `r s`, some `x ≡ r` has an
iterate `Uᴸ x ≡ s (mod M)`.  The itinerary is `pre · connector · suf · post`, where `pre` and
`post` are the first `a` symbols of `r` and `s`, `suf` the `b` symbols leading into `s`, and the
connector fixes the `M₀` part; `x mod 3^b M₀` is then prescribed by CRT. -/
theorem amusical_reach (M : ℕ) (hM : 0 < M) (r s : ℤ) :
    ∃ x : ℤ, ∃ L : ℕ, x ≡ r [ZMOD M] ∧ amusical^[L] x ≡ s [ZMOD M] := by
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
  let post : List (Fin 3) :=
    List.ofFn fun i : Fin a => stepSym (amusical^[i.val] s)
  let suf : List (Fin 3) :=
    List.ofFn fun i : Fin b => stepSym (amusical^[i.val] (amusicalInv^[b] s))
  haveI : NeZero m₀ := ⟨hm₀.ne'⟩
  obtain ⟨z, hz⟩ := act_surjective m₀ hc6 suf (s : ZMod m₀)
  obtain ⟨connector, -, hconnector⟩ :=
    exists_connector m₀ hm₀ hc6 (act m₀ pre (r : ZMod m₀)) z
  let block := (pre ++ connector) ++ suf
  let L := block.length
  let word := block ++ post
  let D := word.length
  have hpreLen : pre.length = a := by simp [pre]
  have hpostLen : post.length = a := by simp [post]
  have hsufLen : suf.length = b := by simp [suf]
  have hLval : L = a + connector.length + b := by
    simp [L, block, hpreLen, hsufLen, Nat.add_assoc]
  have hDval : D = L + a := by simp [D, word, L, hpostLen]
  have hblock : act m₀ block (r : ZMod m₀) = s := by
    simp only [block, act_append]
    rw [hconnector, hz]
  have hwordBlock : ∀ i (hi : i < L), word[i]'(by omega) = block[i] := by
    intro i hi
    exact List.getElem_append_left hi
  have hprefix : ∀ i (hi : i < a), word[i]'(by omega) = stepSym (amusical^[i] r) := by
    intro i hi
    rw [hwordBlock i (by omega)]
    dsimp only [block]
    rw [List.getElem_append_left (by simp [hpreLen]; omega)]
    rw [List.getElem_append_left (by simpa [hpreLen])]
    simp [pre, List.getElem_ofFn]
  have hpost : ∀ i (hi : i < a), word[L + i]'(by omega) = stepSym (amusical^[i] s) := by
    intro i hi
    dsimp only [word]
    rw [List.getElem_append_right (Nat.le_add_right _ _)]
    simp [post, List.getElem_ofFn]
  have hsuffix : ∀ i (hi : i < b),
      word[L - b + i]'(by omega) = stepSym (amusical^[i] (amusicalInv^[b] s)) := by
    intro i hi
    rw [hwordBlock (L - b + i) (by omega)]
    have hindex : L - b + i = (pre ++ connector).length + i := by
      simp [hLval, hpreLen]
    calc
      block[L - b + i] = block[(pre ++ connector).length + i] :=
        getElem_congr rfl hindex (by omega)
      _ = stepSym (amusical^[i] (amusicalInv^[b] s)) := by
        dsimp only [block]
        rw [List.getElem_append_right (Nat.le_add_right _ _)]
        simp only [List.length_append, Nat.add_sub_cancel_left]
        simp [suf, List.getElem_ofFn]
  obtain ⟨m, hm⟩ := exists_forward_itinerary_local word
  let O := 3 ^ b * m₀
  have hO2 : O.Coprime 2 := by
    dsimp only [O]
    exact (by norm_num : (3 : ℕ).Coprime 2).pow_left b |>.mul_left hc2
  have hO4 : O.Coprime 4 := by
    convert hO2.pow_right 2 using 1 <;> norm_num
  have hOA : O.Coprime (4 ^ D) := hO4.pow_right D
  have hcopInt : IsCoprime (O : ℤ) ((4 : ℤ) ^ D) := by
    exact Nat.Coprime.isCoprime hOA
  obtain ⟨q, hq⟩ : ∃ q : ℤ, (4 : ℤ) ^ D * q ≡ r - m [ZMOD O] :=
    exists_mul_modEq_of_isCoprime hcopInt
  let x : ℤ := m + 4 ^ D * q
  have hxOdd : x ≡ r [ZMOD O] := by
    rw [Int.modEq_iff_dvd] at hq ⊢
    obtain ⟨c, hc⟩ := hq
    refine ⟨c, ?_⟩
    dsimp only [x]
    push_cast
    linear_combination hc
  have hxword : ∀ i (hi : i < D), stepSym (amusical^[i] x) = word[i] := by
    intro i hi
    calc
      stepSym (amusical^[i] x) = stepSym (amusical^[i] m) := by
        dsimp only [x]
        exact stepSym_iterate_add_pow_four_mul D i hi m q
      _ = word[i] := hm i hi
  have hxmod₀ : (x : ZMod m₀) = r := by
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    apply (show (m₀ : ℤ) ∣ O by
      refine ⟨3 ^ b, ?_⟩
      dsimp only [O]
      push_cast
      ring).trans
    exact hxOdd.dvd
  have hseg : ∀ i (hi : i < block.length), stepSym (amusical^[i] x) = block[i] := by
    intro i hi
    rw [hxword i (by omega)]
    exact hwordBlock i hi
  have hend₀ : (amusical^[L] x : ZMod m₀) = s := by
    rw [cast_iterate_eq_act m₀ hc6 block x hseg, hxmod₀, hblock]
  have hx2 : (2 : ℤ) ^ a ∣ x - r := by
    apply pow_two_dvd_sub_of_stepSym_iterate_eq
    intro i hi
    exact (hxword i (by omega)).trans (hprefix i hi)
  have hend2 : (2 : ℤ) ^ a ∣ amusical^[L] x - s := by
    apply pow_two_dvd_sub_of_stepSym_iterate_eq
    intro i hi
    rw [← Function.iterate_add_apply, add_comm i L]
    exact (hxword (L + i) (by omega)).trans (hpost i hi)
  have hend3 : (3 : ℤ) ^ b ∣ amusical^[L] x - s := by
    let y := amusical^[L - b] x
    have hsymbols : ∀ i < b,
        stepSym (amusical^[i] y) =
          stepSym (amusical^[i] (amusicalInv^[b] s)) := by
      intro i hi
      dsimp only [y]
      rw [← Function.iterate_add_apply, add_comm i (L - b)]
      exact (hxword (L - b + i) (by omega)).trans (hsuffix i hi)
    have hdiv :=
      pow_three_dvd_iterate_sub_of_symbols b y (amusicalInv^[b] s) hsymbols
    have hxend : amusical^[b] y = amusical^[L] x := by
      dsimp only [y]
      rw [← Function.iterate_add_apply]
      congr 2
      omega
    rw [hxend, amusical_iterate_amusicalInv_iterate] at hdiv
    exact hdiv
  have hc3m₀ : (3 ^ b).Coprime m₀ := hc3.symm.pow_left b
  have hc2three : (2 ^ a).Coprime (3 ^ b) :=
    ((by norm_num : (2 : ℕ).Coprime 3).pow_left a).pow_right b
  have hc2m₀ : (2 ^ a).Coprime m₀ := hc2.symm.pow_left a
  have hc2O : (2 ^ a).Coprime (3 ^ b * m₀) := hc2three.mul_right hc2m₀
  refine ⟨x, L, ?_, ?_⟩
  · have htwo : x ≡ r [ZMOD (2 : ℤ) ^ a] := by
      rw [Int.modEq_iff_dvd]
      have h := dvd_neg.mpr hx2
      simpa only [neg_sub] using h
    have hodd : x ≡ r [ZMOD (3 : ℤ) ^ b * m₀] := by
      simpa [O] using hxOdd
    have hall : x ≡ r [ZMOD (2 : ℤ) ^ a * ((3 : ℤ) ^ b * m₀)] :=
      (Int.modEq_and_modEq_iff_modEq_mul
        (by simpa [Int.natAbs_mul, Int.natAbs_pow] using hc2O)).mp ⟨htwo, hodd⟩
    simpa [hMfull] using hall
  · have htwo : amusical^[L] x ≡ s [ZMOD (2 : ℤ) ^ a] := by
      rw [Int.modEq_iff_dvd]
      have h := dvd_neg.mpr hend2
      simpa only [neg_sub] using h
    have hthree : amusical^[L] x ≡ s [ZMOD (3 : ℤ) ^ b] := by
      rw [Int.modEq_iff_dvd]
      have h := dvd_neg.mpr hend3
      simpa only [neg_sub] using h
    have hm₀mod : amusical^[L] x ≡ s [ZMOD (m₀ : ℤ)] := by
      rw [Int.modEq_iff_dvd, ← ZMod.intCast_eq_intCast_iff_dvd_sub]
      exact hend₀
    have hodd : amusical^[L] x ≡ s [ZMOD (3 : ℤ) ^ b * m₀] :=
      (Int.modEq_and_modEq_iff_modEq_mul (by simpa using hc3m₀)).mp ⟨hthree, hm₀mod⟩
    have hall : amusical^[L] x ≡ s
        [ZMOD (2 : ℤ) ^ a * ((3 : ℤ) ^ b * m₀)] :=
      (Int.modEq_and_modEq_iff_modEq_mul
        (by simpa [Int.natAbs_mul, Int.natAbs_pow] using hc2O)).mp ⟨htwo, hodd⟩
    simpa [hMfull] using hall

end CollatzMoonshot.Amusical.AntiKohlConnect
