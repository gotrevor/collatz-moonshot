/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.FrontA.BackwardTree

/-!
# A uniform pruned subtree inside the floor-preserving backward tree

This is the first unconditional chip at the new mathematics exposed by the
barrier-tree census.  Every `x ≥ 2` that is a unit modulo `3` has two distinct,
larger unit predecessors.  Each uses one odd inverse followed by at most seven
doublings, so its complete forward block back to `x` stays in `[x, 128x]`.

The arithmetic branching kernel and its finite `2^r`-node iteration are proved
below.  The iteration composes band witnesses and uses uniqueness of the
2-adic factorization to prevent children of distinct odd parents from
colliding.  No new Collatz hypothesis is involved.
-/

namespace CollatzMoonshot.FrontA

/-- One reverse macro-step: an odd `y` maps to `2^j x`, then `j` halvings reach
`x`.  We retain unit children, force strict growth, and cap the exponent at 7. -/
def UnitOddBlockChild (x y : ℕ) : Prop :=
  ∃ j, 1 ≤ j ∧ j ≤ 7 ∧ y % 2 = 1 ∧ ¬3 ∣ y ∧ x < y ∧
    3 * y + 1 = 2 ^ j * x

theorem iterate_two_pow_mul_of_le {i j x : ℕ} (hij : i ≤ j) :
    step^[i] (2 ^ j * x) = 2 ^ (j - i) * x := by
  have hpow : 2 ^ j * x = 2 ^ i * (2 ^ (j - i) * x) := by
    have hji : j = i + (j - i) := (Nat.add_sub_of_le hij).symm
    calc
      2 ^ j * x = 2 ^ (i + (j - i)) * x := congrArg (fun n => 2 ^ n * x) hji
      _ = 2 ^ i * (2 ^ (j - i) * x) := by rw [pow_add]; ring
  rw [hpow, iterate_pow_two_mul]

theorem reachesInBand_of_odd_block {x y j : ℕ} (hyodd : y % 2 = 1)
    (hy : x ≤ y) (hblock : 3 * y + 1 = 2 ^ j * x) :
    ReachesInBand x (2 ^ j * x) y := by
  have hstep : step y = 2 ^ j * x := by
    rw [show step y = 3 * y + 1 by unfold step; simp [hyodd]]
    exact hblock
  refine ⟨j + 1, ?_, ?_⟩
  · rw [Function.iterate_succ_apply, hstep]
    exact iterate_pow_two_mul j x
  · intro t ht
    rcases t with _ | t
    · simp only [Function.iterate_zero_apply]
      exact ⟨hy, by omega⟩
    · have htj : t ≤ j := by omega
      rw [Function.iterate_succ_apply, hstep]
      rw [iterate_two_pow_mul_of_le htj]
      constructor
      · have hp : 0 < 2 ^ (j - t) := pow_pos (by omega) _
        exact Nat.le_mul_of_pos_left x hp
      · have he : j - t ≤ j := Nat.sub_le _ _
        have hp : 2 ^ (j - t) ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) he
        exact Nat.mul_le_mul_right x hp

theorem reachesInBand_mono_ceiling {d X Y m : ℕ} (hXY : X ≤ Y)
    (h : ReachesInBand d X m) : ReachesInBand d Y m := by
  obtain ⟨k, hk, hband⟩ := h
  refine ⟨k, hk, ?_⟩
  intro t ht
  obtain ⟨hlo, hhi⟩ := hband t ht
  exact ⟨hlo, hhi.trans hXY⟩

theorem UnitOddBlockChild.reachesInBand {x y : ℕ} (h : UnitOddBlockChild x y) :
    ReachesInBand x (128 * x) y := by
  obtain ⟨j, _, hj7, hyodd, _, hxy, hblock⟩ := h
  apply reachesInBand_mono_ceiling (X := 2 ^ j * x)
  · have hp : 2 ^ j ≤ 2 ^ 7 := Nat.pow_le_pow_right (by omega) hj7
    norm_num at hp ⊢
    exact Nat.mul_le_mul_right x hp
  · exact reachesInBand_of_odd_block hyodd hxy.le hblock

private theorem children_mod9_one (q : ℕ) (hx : 2 ≤ 9 * q + 1) :
    ∃ y₁ y₂, y₁ ≠ y₂ ∧
      UnitOddBlockChild (9 * q + 1) y₁ ∧ UnitOddBlockChild (9 * q + 1) y₂ := by
  refine ⟨12 * q + 1, 48 * q + 5, by omega, ?_, ?_⟩
  · exact ⟨2, by norm_num, by norm_num, by omega, by omega, by omega, by ring⟩
  · exact ⟨4, by norm_num, by norm_num, by omega, by omega, by omega, by ring⟩

private theorem children_mod9_two (q : ℕ) :
    ∃ y₁ y₂, y₁ ≠ y₂ ∧
      UnitOddBlockChild (9 * q + 2) y₁ ∧ UnitOddBlockChild (9 * q + 2) y₂ := by
  refine ⟨24 * q + 5, 384 * q + 85, by omega, ?_, ?_⟩
  · exact ⟨3, by norm_num, by norm_num, by omega, by omega, by omega, by ring⟩
  · exact ⟨7, by norm_num, by norm_num, by omega, by omega, by omega, by ring⟩

private theorem children_mod9_four (q : ℕ) :
    ∃ y₁ y₂, y₁ ≠ y₂ ∧
      UnitOddBlockChild (9 * q + 4) y₁ ∧ UnitOddBlockChild (9 * q + 4) y₂ := by
  refine ⟨12 * q + 5, 192 * q + 85, by omega, ?_, ?_⟩
  · exact ⟨2, by norm_num, by norm_num, by omega, by omega, by omega, by ring⟩
  · exact ⟨6, by norm_num, by norm_num, by omega, by omega, by omega, by ring⟩

private theorem children_mod9_five (q : ℕ) :
    ∃ y₁ y₂, y₁ ≠ y₂ ∧
      UnitOddBlockChild (9 * q + 5) y₁ ∧ UnitOddBlockChild (9 * q + 5) y₂ := by
  refine ⟨24 * q + 13, 96 * q + 53, by omega, ?_, ?_⟩
  · exact ⟨3, by norm_num, by norm_num, by omega, by omega, by omega, by ring⟩
  · exact ⟨5, by norm_num, by norm_num, by omega, by omega, by omega, by ring⟩

private theorem children_mod9_seven (q : ℕ) :
    ∃ y₁ y₂, y₁ ≠ y₂ ∧
      UnitOddBlockChild (9 * q + 7) y₁ ∧ UnitOddBlockChild (9 * q + 7) y₂ := by
  refine ⟨48 * q + 37, 192 * q + 149, by omega, ?_, ?_⟩
  · exact ⟨4, by norm_num, by norm_num, by omega, by omega, by omega, by ring⟩
  · exact ⟨6, by norm_num, by norm_num, by omega, by omega, by omega, by ring⟩

private theorem children_mod9_eight (q : ℕ) :
    ∃ y₁ y₂, y₁ ≠ y₂ ∧
      UnitOddBlockChild (9 * q + 8) y₁ ∧ UnitOddBlockChild (9 * q + 8) y₂ := by
  refine ⟨96 * q + 85, 384 * q + 341, by omega, ?_, ?_⟩
  · exact ⟨5, by norm_num, by norm_num, by omega, by omega, by omega, by ring⟩
  · exact ⟨7, by norm_num, by norm_num, by omega, by omega, by omega, by ring⟩

/-- Every unit modulo `3` above `1` has two distinct, larger unit children, each
reaching the parent through a floor-preserving reverse block contained in
`[x, 128x]`. -/
theorem exists_two_unitOddBlockChildren {x : ℕ} (hx : 2 ≤ x) (h3 : ¬3 ∣ x) :
    ∃ y₁ y₂, y₁ ≠ y₂ ∧ UnitOddBlockChild x y₁ ∧ UnitOddBlockChild x y₂ := by
  have hlt : x % 9 < 9 := Nat.mod_lt x (by norm_num)
  have hrepr : x % 9 + 9 * (x / 9) = x := Nat.mod_add_div x 9
  interval_cases hrem : x % 9
  · exfalso
    apply h3
    use 3 * (x / 9)
    omega
  · rw [← hrepr]
    simpa [Nat.add_comm] using children_mod9_one (x / 9) (by omega)
  · rw [← hrepr]
    simpa [Nat.add_comm] using children_mod9_two (x / 9)
  · exfalso
    apply h3
    use 3 * (x / 9) + 1
    omega
  · rw [← hrepr]
    simpa [Nat.add_comm] using children_mod9_four (x / 9)
  · rw [← hrepr]
    simpa [Nat.add_comm] using children_mod9_five (x / 9)
  · exfalso
    apply h3
    use 3 * (x / 9) + 2
    omega
  · rw [← hrepr]
    simpa [Nat.add_comm] using children_mod9_seven (x / 9)
  · rw [← hrepr]
    simpa [Nat.add_comm] using children_mod9_eight (x / 9)

/-- A band path pins its endpoint between floor and ceiling. -/
theorem ReachesInBand.self_mem_band {d X m : ℕ} (h : ReachesInBand d X m) :
    d ≤ m ∧ m ≤ X := by
  obtain ⟨k, _, hband⟩ := h
  simpa using hband 0 (Nat.zero_le _)

/-- Band witnesses compose: a path from `y` down to `m` inside `[m, Y]`
followed by a path from `m` down to `d` inside `[d, X]` stays inside `[d, Z]`
for any common ceiling `Z`. -/
theorem reachesInBand_trans {d X m Y y Z : ℕ}
    (h1 : ReachesInBand m Y y) (h2 : ReachesInBand d X m)
    (hYZ : Y ≤ Z) (hXZ : X ≤ Z) : ReachesInBand d Z y := by
  have hdm : d ≤ m := h2.self_mem_band.1
  obtain ⟨k1, hk1, hb1⟩ := h1
  obtain ⟨k2, hk2, hb2⟩ := h2
  refine ⟨k2 + k1, ?_, ?_⟩
  · rw [Function.iterate_add_apply, hk1, hk2]
  · intro t ht
    rcases Nat.lt_or_ge k1 t with hgt | hle
    · have hsplit : step^[t] y = step^[t - k1] m := by
        rw [← hk1, ← Function.iterate_add_apply]
        congr 1
        omega
      obtain ⟨hlo, hhi⟩ := hb2 (t - k1) (by omega)
      rw [hsplit]
      exact ⟨hlo, hhi.trans hXZ⟩
    · obtain ⟨hlo, hhi⟩ := hb1 t hle
      exact ⟨hdm.trans hlo, hhi.trans hYZ⟩

theorem parent_eq_of_exp_le {x x' : ℕ} {j j' : ℕ} (hx : x % 2 = 1)
    (hle : j ≤ j') (heq : 2 ^ j * x = 2 ^ j' * x') : x = x' := by
  have hsplit : 2 ^ j' = 2 ^ j * 2 ^ (j' - j) := by
    rw [← pow_add]
    congr 1
    omega
  have hx' : x = 2 ^ (j' - j) * x' := by
    have h2 : 2 ^ j * x = 2 ^ j * (2 ^ (j' - j) * x') := by
      rw [heq, hsplit, mul_assoc]
    exact Nat.eq_of_mul_eq_mul_left (pow_pos (by omega) _) h2
  rcases Nat.eq_or_lt_of_le hle with rfl | hlt
  · simpa using hx'
  · exfalso
    have h2x : 2 ∣ x := by
      rw [hx']
      exact dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega : j' - j ≠ 0)) _
    omega

/-- Children of distinct **odd** parents cannot collide: `3y + 1` has a unique
factorization `2^j · (odd)`, so the parent is recoverable from the child. -/
theorem unitOddBlockChild_parent_eq {x x' y : ℕ} (hx : x % 2 = 1)
    (hx' : x' % 2 = 1) (h : UnitOddBlockChild x y)
    (h' : UnitOddBlockChild x' y) : x = x' := by
  obtain ⟨j, _, _, _, _, _, hb⟩ := h
  obtain ⟨j', _, _, _, _, _, hb'⟩ := h'
  have heq : 2 ^ j * x = 2 ^ j' * x' := by omega
  rcases le_total j j' with hle | hle
  · exact parent_eq_of_exp_le hx hle heq
  · exact (parent_eq_of_exp_le hx' hle heq.symm).symm

/-- The odd levels of the pruned binary subtree: for every `r ≥ 1` there are
`2^r` distinct odd unit values reaching `d` inside `[d, 128^r d]`. -/
theorem exists_binary_level {d : ℕ} (hd : 2 ≤ d) (h3 : ¬3 ∣ d) :
    ∀ r : ℕ, 1 ≤ r → ∃ S : Finset ℕ, S.card = 2 ^ r ∧
      ∀ m ∈ S, ¬3 ∣ m ∧ m % 2 = 1 ∧ ReachesInBand d (128 ^ r * d) m := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base =>
      obtain ⟨y₁, y₂, hne, hc1, hc2⟩ := exists_two_unitOddBlockChildren hd h3
      refine ⟨{y₁, y₂}, by rw [Finset.card_pair hne]; norm_num, ?_⟩
      intro m hm
      have hcm : UnitOddBlockChild d m := by
        rcases Finset.mem_insert.mp hm with rfl | hm'
        · exact hc1
        · rw [Finset.mem_singleton.mp hm']
          exact hc2
      have hband := hcm.reachesInBand
      obtain ⟨_, _, _, hmodd, hm3, _, _⟩ := hcm
      refine ⟨hm3, hmodd, ?_⟩
      rwa [show (128 : ℕ) ^ 1 * d = 128 * d by ring]
  | succ r hr ih =>
      obtain ⟨S, hcard, hS⟩ := ih
      have hch : ∀ m : {x // x ∈ S}, ∃ y₁ y₂, y₁ ≠ y₂ ∧
          UnitOddBlockChild m.1 y₁ ∧ UnitOddBlockChild m.1 y₂ := by
        rintro ⟨m, hm⟩
        obtain ⟨hm3, _, hmb⟩ := hS m hm
        have hdm : d ≤ m := hmb.self_mem_band.1
        have h2m : 2 ≤ m := by omega
        exact exists_two_unitOddBlockChildren h2m hm3
      choose f g hfg hf hg using hch
      have hchild : ∀ (a : {x // x ∈ S}) {y}, y ∈ ({f a, g a} : Finset ℕ) →
          UnitOddBlockChild a.1 y := by
        intro a y hy
        rcases Finset.mem_insert.mp hy with rfl | hy'
        · exact hf a
        · rw [Finset.mem_singleton.mp hy']
          exact hg a
      have hdisj : ∀ a ∈ S.attach, ∀ b ∈ S.attach, a ≠ b →
          Disjoint ({f a, g a} : Finset ℕ) {f b, g b} := by
        intro a _ b _ hab
        rw [Finset.disjoint_left]
        intro y hya hyb
        exact hab (Subtype.ext (unitOddBlockChild_parent_eq
          (hS a.1 a.2).2.1 (hS b.1 b.2).2.1 (hchild a hya) (hchild b hyb)))
      refine ⟨S.attach.biUnion fun m => {f m, g m}, ?_, ?_⟩
      · rw [Finset.card_biUnion hdisj]
        rw [Finset.sum_congr rfl fun m _ => Finset.card_pair (hfg m)]
        rw [Finset.sum_const, Finset.card_attach, hcard, smul_eq_mul,
          ← pow_succ]
      · intro y hy
        obtain ⟨a, _, hya⟩ := Finset.mem_biUnion.mp hy
        have hcy := hchild a hya
        have hyband := hcy.reachesInBand
        obtain ⟨_, _, _, hyodd, hy3, _, _⟩ := hcy
        obtain ⟨hm3, _, hmb⟩ := hS a.1 a.2
        have hmceil : a.1 ≤ 128 ^ r * d := hmb.self_mem_band.2
        refine ⟨hy3, hyodd, ?_⟩
        refine reachesInBand_trans hyband hmb ?_ ?_
        · calc 128 * a.1 ≤ 128 * (128 ^ r * d) :=
                Nat.mul_le_mul_left _ hmceil
            _ = 128 ^ (r + 1) * d := by rw [pow_succ]; ring
        · calc 128 ^ r * d ≤ 128 * (128 ^ r * d) :=
                Nat.le_mul_of_pos_left _ (by omega)
            _ = 128 ^ (r + 1) * d := by rw [pow_succ]; ring

/-- A finite-certificate form of the recursively available binary safe subtree.
The theorem below is Lean plumbing from `exists_two_unitOddBlockChildren`; it is
the scoped treadmill target, not an additional mathematical conjecture. -/
def BinaryBarrierSubtreeGrowth : Prop :=
  ∀ d : ℕ, 2 ≤ d → ¬3 ∣ d → ∀ r : ℕ,
    ∃ S : Finset ℕ, S.card = 2 ^ r ∧
      ∀ m ∈ S, ¬3 ∣ m ∧ ReachesInBand d (128 ^ r * d) m

theorem binaryBarrierSubtreeGrowth : BinaryBarrierSubtreeGrowth := by
  intro d hd h3 r
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · refine ⟨{d}, by simp, ?_⟩
    intro m hm
    rw [Finset.mem_singleton.mp hm]
    refine ⟨h3, 0, rfl, ?_⟩
    intro j hj
    have hj0 : j = 0 := Nat.le_zero.mp hj
    subst hj0
    simp only [Function.iterate_zero_apply, pow_zero, one_mul]
    exact ⟨le_refl d, le_refl d⟩
  · obtain ⟨S, hcard, hS⟩ := exists_binary_level hd h3 r hr
    exact ⟨S, hcard, fun m hm => ⟨(hS m hm).1, (hS m hm).2.2⟩⟩

end CollatzMoonshot.FrontA
