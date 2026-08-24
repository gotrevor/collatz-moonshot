/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.FrontA.BackwardThreeQuarters
import CollatzMoonshot.FrontA.BackwardRenewal

/-!
# Exact real telescoping weights for the exponent-`3/4` backward renewal

The correlated 810-state certificate in `BackwardThreeQuarters` proves local
expansion with the *rational* edge underweight `(2279/1000)·(2973/5000)^j`.
Those rational weights do not telescope along a path.  The correct
exponent-`3/4` renewal weight is the exact real

`((x : ℝ) / (y : ℝ)) ^ (3/4 : ℝ)`.

It telescopes exactly through positive endpoints, and the Collatz odd-block
identity `3y + 1 = 2^j x` proves that every rational certificate weight is
strictly smaller on an actual edge, because

`(2279/1000)^4 < 27`  and  `8·(2973/5000)^4 < 1`.

This file upgrades the actual-child local expansion `exists_threeQuartersExpansion`
to the exact real weight over a finite value-injective child set of
`Fin 5 × ℕ`, records that the frozen potential is positive on unit residues and
uniformly at most `19334101`, and defines the `3/4`-exponent stopping frontier
together with its cardinality bound.  The recursive repeat-or-stopping theorem
is completed in `BackwardThreeQuartersStopping.lean`.
-/

namespace CollatzMoonshot.FrontA

open scoped Real

set_option maxRecDepth 10000

/-! ## The exact real edge weight and its rational underweight -/

/-- The real version of the rational edge underweight of the `3/4`-certificate. -/
noncomputable def threeQuartersRationalWeight (j : ℕ) : ℝ :=
  (2279 / 1000 : ℝ) * (2973 / 5000 : ℝ) ^ j

/-- The exact exponent-`3/4` edge weight between two positive odd endpoints. -/
noncomputable def threeQuartersEdgeWeight (x y : ℕ) : ℝ :=
  ((x : ℝ) / (y : ℝ)) ^ (3 / 4 : ℝ)

theorem threeQuartersRationalWeight_pos (j : ℕ) :
    0 < threeQuartersRationalWeight j := by
  unfold threeQuartersRationalWeight; positivity

theorem threeQuartersEdgeWeight_nonneg (x y : ℕ) :
    0 ≤ threeQuartersEdgeWeight x y := by
  unfold threeQuartersEdgeWeight
  exact Real.rpow_nonneg (by positivity) _

/-- The fourth power of the rational weight is dominated by the cube of the ideal
edge factor `3 / 2^j`, from the two elementary rational comparisons. -/
theorem threeQuartersRationalWeight_fourth_lt (j : ℕ) (hj : 1 ≤ j) :
    (threeQuartersRationalWeight j) ^ 4 < (3 / (2 : ℝ) ^ j) ^ 3 := by
  have hbase : ((2973 / 5000 : ℝ) ^ 4) ^ j < ((1 / 8 : ℝ)) ^ j :=
    pow_lt_pow_left₀ (by norm_num) (by positivity) (by omega)
  have h8 : ((8 : ℝ)) ^ j = ((2 : ℝ) ^ j) ^ 3 := by
    rw [← pow_mul, show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_mul, Nat.mul_comm]
  calc
    (threeQuartersRationalWeight j) ^ 4
        = (2279 / 1000 : ℝ) ^ 4 * ((2973 / 5000 : ℝ) ^ 4) ^ j := by
          rw [threeQuartersRationalWeight, mul_pow, ← pow_mul, ← pow_mul,
            Nat.mul_comm j 4]
    _ < 27 * ((2973 / 5000 : ℝ) ^ 4) ^ j := by
          apply mul_lt_mul_of_pos_right (by norm_num) (by positivity)
    _ < 27 * ((1 / 8 : ℝ)) ^ j := mul_lt_mul_of_pos_left hbase (by norm_num)
    _ = (3 / (2 : ℝ) ^ j) ^ 3 := by
          rw [one_div_pow, mul_one_div, h8, div_pow]; norm_num

/-- On every actual positive odd block, the rational certificate weight is
strictly below the exact telescoping endpoint weight. -/
theorem threeQuartersRationalWeight_lt_edgeWeight {x y j : ℕ}
    (hy : 1 ≤ y) (hj : 1 ≤ j) (h : 3 * y + 1 = 2 ^ j * x) :
    threeQuartersRationalWeight j < threeQuartersEdgeWeight x y := by
  have hb : (3 : ℝ) * y + 1 = (2 : ℝ) ^ j * x := by exact_mod_cast h
  have hratio : (3 : ℝ) / (2 : ℝ) ^ j < (x : ℝ) / (y : ℝ) := by
    rw [div_lt_div_iff₀ (pow_pos (by norm_num) _) (by exact_mod_cast hy)]
    nlinarith
  have hbpos : (0 : ℝ) < 3 / (2 : ℝ) ^ j := by positivity
  have hBnn : 0 ≤ (3 / (2 : ℝ) ^ j) ^ (3 / 4 : ℝ) :=
    Real.rpow_nonneg (le_of_lt hbpos) _
  have hBfourth : ((3 / (2 : ℝ) ^ j) ^ (3 / 4 : ℝ)) ^ (4 : ℕ) =
      (3 / (2 : ℝ) ^ j) ^ 3 := by
    rw [← Real.rpow_natCast ((3 / (2 : ℝ) ^ j) ^ (3 / 4 : ℝ)) 4,
      ← Real.rpow_mul (le_of_lt hbpos), ← Real.rpow_natCast (3 / (2 : ℝ) ^ j) 3]
    norm_num
  have hwlt : threeQuartersRationalWeight j <
      (3 / (2 : ℝ) ^ j) ^ (3 / 4 : ℝ) := by
    apply lt_of_pow_lt_pow_left₀ 4 hBnn
    rw [hBfourth]
    exact threeQuartersRationalWeight_fourth_lt j hj
  have hmono : (3 / (2 : ℝ) ^ j) ^ (3 / 4 : ℝ) <
      threeQuartersEdgeWeight x y := by
    unfold threeQuartersEdgeWeight
    exact Real.rpow_lt_rpow (le_of_lt hbpos) hratio (by norm_num)
  exact hwlt.trans hmono

/-- Exact telescoping of the `3/4`-edge weight through a positive intermediate
endpoint. -/
theorem threeQuartersEdgeWeight_mul {x y z : ℕ} (hy : 1 ≤ y) (hz : 1 ≤ z) :
    threeQuartersEdgeWeight x y * threeQuartersEdgeWeight y z =
      threeQuartersEdgeWeight x z := by
  have hy0 : (y : ℝ) ≠ 0 := by positivity
  have hz0 : (z : ℝ) ≠ 0 := by positivity
  unfold threeQuartersEdgeWeight
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  congr 1
  field_simp

/-! ## Positivity and a uniform ceiling for the frozen potential -/

/-- Every reusable residue has strictly positive potential at every floor. -/
theorem threeQuartersPotential_pos {x : ℕ} (h3 : ¬3 ∣ x) (i : Fin 5) :
    0 < threeQuartersPotential i x := by
  rw [← threeQuartersPotential_mod]
  have hr243 : x % 243 < 243 := Nat.mod_lt x (by norm_num)
  have hru : (x % 243) % 3 ≠ 0 := by
    rw [Nat.mod_mod_of_dvd x (by norm_num : 3 ∣ 243)]
    exact fun h0 => h3 (Nat.dvd_of_mod_eq_zero h0)
  exact threeQuartersPotential_pos_of_unit i ⟨x % 243, hr243⟩ hru

/-- Every entry of the frozen `3/4`-potential is at most `19334101`. -/
theorem threeQuartersPotential_le_max_fin :
    ∀ i : Fin 5, ∀ r : Fin 243, threeQuartersPotential i r.1 ≤ 19334101 := by
  native_decide

/-- The frozen `3/4`-potential is uniformly at most `19334101`. -/
theorem threeQuartersPotential_le_max (i : Fin 5) (x : ℕ) :
    threeQuartersPotential i x ≤ 19334101 := by
  rw [← threeQuartersPotential_mod]
  have hr243 : x % 243 < 243 := Nat.mod_lt x (by norm_num)
  exact threeQuartersPotential_le_max_fin i ⟨x % 243, hr243⟩

/-! ## The finite value-injective child set with exact real weights -/

/-- A five-height state paired with its odd endpoint. -/
abbrev ThreeQuartersNode := Fin 5 × ℕ

/-- The local reusable child relation used by the stopping construction. -/
def ThreeQuartersChildAt (d : ℕ) (parent child : ThreeQuartersNode) : Prop :=
  ReusableOddBlockChild parent.2 child.2 ∧
    InThreeQuartersHeightState d child.1 child.2

/-- A finite state frontier does not count one natural endpoint twice under
different state labels. -/
def ThreeQuartersValuesInjective (C : Finset ThreeQuartersNode) : Prop :=
  ∀ a ∈ C, ∀ b ∈ C, a.2 = b.2 → a = b

/-- **Exact real exponent-`3/4` local expansion.**  Every reusable source
`x ≥ 2`, `3 ∤ x` in one of the five height states over a floor `d ≥ 2` has a
nonempty, value-injective finite child set of actual reusable Collatz children,
all in their floor-safe five-height states, each with `3 c < 2^23 x`, whose
frozen potential strictly expands the source potential under the exact
telescoping weight `((x)/(c))^(3/4)`. -/
theorem exists_threeQuartersChildFinset {d x : ℕ} (i : Fin 5) (hd : 2 ≤ d)
    (hx : 2 ≤ x) (h3 : ¬3 ∣ x) (hstate : InThreeQuartersHeightState d i x) :
    ∃ C : Finset ThreeQuartersNode, C.Nonempty ∧ ThreeQuartersValuesInjective C ∧
      (∀ c ∈ C, ThreeQuartersChildAt d (i, x) c) ∧
      (∀ c ∈ C, 3 * c.2 < 2 ^ 23 * x) ∧
      (threeQuartersPotential i x : ℝ) <
        ∑ c ∈ C, threeQuartersEdgeWeight x c.2 *
          (threeQuartersPotential c.1 c.2 : ℝ) := by
  obtain ⟨ys, z, hys, hgrow, hshrink, hrat⟩ :=
    exists_threeQuartersExpansion i hd hx h3 hstate
  -- The seven growing nodes, packaged as an injective image.
  let g : Fin 7 → ThreeQuartersNode := fun k =>
    (nextThreeQuartersState i (sevenCostsAt x k), ys k)
  have hg : Function.Injective g := fun k k' hkk' => hys (congrArg Prod.snd hkk')
  -- The edge upgrade for a single growing child.
  have hgrowEdge : ∀ k : Fin 7,
      threeQuartersRationalWeight (sevenCostsAt x k) *
          (threeQuartersPotential (nextThreeQuartersState i (sevenCostsAt x k))
            (ys k) : ℝ) <
        threeQuartersEdgeWeight x (ys k) *
          (threeQuartersPotential (nextThreeQuartersState i (sevenCostsAt x k))
            (ys k) : ℝ) := by
    intro k
    apply mul_lt_mul_of_pos_right
    · obtain ⟨hj, hyodd, hy3, _, hblock⟩ := (hgrow k).1
      exact threeQuartersRationalWeight_lt_edgeWeight (by omega) (by omega) hblock
    · exact_mod_cast threeQuartersPotential_pos
        (by obtain ⟨_, _, hy3, _, _⟩ := (hgrow k).1; exact hy3) _
  by_cases hs : threeQuartersHasShrink i x = true
  · -- Shrinking child is enabled: eight children.
    obtain ⟨hzchild, hzstate, hzne⟩ := hshrink hs
    have hznot : (shrinkThreeQuartersState i, z) ∉ Finset.univ.image g := by
      intro hmem
      obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hmem
      exact hzne k (congrArg Prod.snd hk).symm
    refine ⟨insert (shrinkThreeQuartersState i, z) (Finset.univ.image g),
      ?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨_, Finset.mem_insert_self _ _⟩
    · -- value injectivity
      intro a ha b hb hab
      rcases Finset.mem_insert.mp ha with rfl | ha
      · rcases Finset.mem_insert.mp hb with rfl | hb
        · rfl
        · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hb
          exact (hzne k hab).elim
      · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp ha
        rcases Finset.mem_insert.mp hb with rfl | hb
        · exact (hzne k hab.symm).elim
        · obtain ⟨k', _, rfl⟩ := Finset.mem_image.mp hb
          have : k = k' := hys hab
          subst this; rfl
    · -- reusable + state
      intro c hc
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact ⟨hzchild.toReusable, hzstate⟩
      · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hc
        exact ⟨(hgrow k).1.toReusable, (hgrow k).2.1⟩
    · -- ceiling bound
      intro c hc
      rcases Finset.mem_insert.mp hc with rfl | hc
      · show 3 * z < 2 ^ 23 * x
        obtain ⟨_, _, _, hblock⟩ := hzchild
        have hmul : 2 * x ≤ 2 ^ 23 * x := Nat.mul_le_mul_right x (by norm_num)
        omega
      · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hc
        exact (hgrow k).2.2
    · -- expansion
      rw [Finset.sum_insert hznot, Finset.sum_image
        (fun a _ b _ hab => hg hab)]
      have hmass :
          (threeQuartersPotential i x : ℝ) <
            (threeQuartersEdgeWeight x z *
              (threeQuartersPotential (shrinkThreeQuartersState i) z : ℝ)) +
            ∑ k : Fin 7, threeQuartersEdgeWeight x (ys k) *
              (threeQuartersPotential (nextThreeQuartersState i (sevenCostsAt x k))
                (ys k) : ℝ) := by
        have hzedge :
            threeQuartersRationalWeight 1 *
                (threeQuartersPotential (shrinkThreeQuartersState i) z : ℝ) <
              threeQuartersEdgeWeight x z *
                (threeQuartersPotential (shrinkThreeQuartersState i) z : ℝ) := by
          obtain ⟨hzodd, hz3, _, hblock⟩ := hzchild
          apply mul_lt_mul_of_pos_right
          · exact threeQuartersRationalWeight_lt_edgeWeight
              (by omega) (by norm_num) (by simpa using hblock)
          · exact_mod_cast threeQuartersPotential_pos hz3 _
        -- cast the rational certificate to ℝ, then upgrade each term
        have hcast : (threeQuartersPotential i x : ℝ) <
            (2279 / 1000 : ℝ) *
              ((∑ k : Fin 7, (2973 / 5000 : ℝ) ^ sevenCostsAt x k *
                  (threeQuartersPotential
                    (nextThreeQuartersState i (sevenCostsAt x k)) (ys k) : ℝ)) +
                (2973 / 5000 : ℝ) *
                  (threeQuartersPotential (shrinkThreeQuartersState i) z : ℝ)) := by
          have := (Rat.cast_lt (K := ℝ)).mpr hrat
          simp only [hs, if_true] at this
          push_cast at this
          convert this using 2
        rw [mul_add, Finset.mul_sum] at hcast
        have hgrowSum :
            (∑ k : Fin 7, (2279 / 1000 : ℝ) *
                ((2973 / 5000 : ℝ) ^ sevenCostsAt x k *
                  (threeQuartersPotential
                    (nextThreeQuartersState i (sevenCostsAt x k)) (ys k) : ℝ))) <
              ∑ k : Fin 7, threeQuartersEdgeWeight x (ys k) *
                (threeQuartersPotential
                  (nextThreeQuartersState i (sevenCostsAt x k)) (ys k) : ℝ) := by
          apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
          intro k _
          rw [← mul_assoc]
          exact hgrowEdge k
        have hshrinkTerm :
            (2279 / 1000 : ℝ) *
                ((2973 / 5000 : ℝ) *
                  (threeQuartersPotential (shrinkThreeQuartersState i) z : ℝ)) <
              threeQuartersEdgeWeight x z *
                (threeQuartersPotential (shrinkThreeQuartersState i) z : ℝ) := by
          have heq : (2279 / 1000 : ℝ) *
              ((2973 / 5000 : ℝ) *
                (threeQuartersPotential (shrinkThreeQuartersState i) z : ℝ)) =
              threeQuartersRationalWeight 1 *
                (threeQuartersPotential (shrinkThreeQuartersState i) z : ℝ) := by
            simp [threeQuartersRationalWeight]; ring
          rw [heq]; exact hzedge
        linarith [hcast, add_lt_add hgrowSum hshrinkTerm]
      linarith [hmass]
  · -- Shrinking child disabled: seven children.
    have hsf : threeQuartersHasShrink i x = false := by
      rw [Bool.not_eq_true] at hs; exact hs
    refine ⟨Finset.univ.image g, ?_, ?_, ?_, ?_, ?_⟩
    · exact Finset.Nonempty.image Finset.univ_nonempty g
    · intro a ha b hb hab
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨k', _, rfl⟩ := Finset.mem_image.mp hb
      have : k = k' := hys hab
      subst this; rfl
    · intro c hc
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hc
      exact ⟨(hgrow k).1.toReusable, (hgrow k).2.1⟩
    · intro c hc
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hc
      exact (hgrow k).2.2
    · rw [Finset.sum_image (fun a _ b _ hab => hg hab)]
      have hcast : (threeQuartersPotential i x : ℝ) <
          (2279 / 1000 : ℝ) *
            (∑ k : Fin 7, (2973 / 5000 : ℝ) ^ sevenCostsAt x k *
                (threeQuartersPotential
                  (nextThreeQuartersState i (sevenCostsAt x k)) (ys k) : ℝ)) := by
        have := (Rat.cast_lt (K := ℝ)).mpr hrat
        simp only [hsf, Bool.false_eq_true, if_false, add_zero] at this
        push_cast at this
        convert this using 2
      rw [Finset.mul_sum] at hcast
      have hgrowSum :
          (∑ k : Fin 7, (2279 / 1000 : ℝ) *
              ((2973 / 5000 : ℝ) ^ sevenCostsAt x k *
                (threeQuartersPotential
                  (nextThreeQuartersState i (sevenCostsAt x k)) (ys k) : ℝ))) <
            ∑ k : Fin 7, threeQuartersEdgeWeight x (ys k) *
              (threeQuartersPotential
                (nextThreeQuartersState i (sevenCostsAt x k)) (ys k) : ℝ) := by
        apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
        intro k _
        rw [← mul_assoc]
        exact hgrowEdge k
      linarith [hcast, hgrowSum]

/-! ## The exponent-`3/4` stopping frontier and its cardinal bound -/

/-- A finite first-exit frontier with enough exponent-`3/4` telescoping mass,
exactly analogous to `NetHalfStoppingFrontier`.  The value-injectivity clause
makes its cardinality count distinct natural endpoints. -/
def ThreeQuartersStoppingFrontier (d H : ℕ) (S : Finset ThreeQuartersNode) : Prop :=
  (∀ a ∈ S, ∀ b ∈ S, a.2 = b.2 → a = b) ∧
  (threeQuartersPotential 0 d : ℝ) <
    ∑ s ∈ S, threeQuartersEdgeWeight d s.2 * (threeQuartersPotential s.1 s.2 : ℝ) ∧
  ∀ s ∈ S, H < s.2 ∧ s.2 < 2 ^ 23 * H ∧
    ReachesInBand d (2 ^ 25 * H) s.2

/-- The remaining scoped theorem, exactly analogous to
`NetHalfRepeatOrStoppingGrowth`: every odd reusable root either exposes a
positive cycle above its floor or has a finite first-exit frontier carrying the
certified exponent-`3/4` mass.  Proved in `BackwardThreeQuartersStopping.lean`. -/
def ThreeQuartersRepeatOrStoppingGrowth : Prop :=
  ∀ d H : ℕ, 2 ≤ d → d % 2 = 1 → ¬3 ∣ d → d ≤ H →
    (∃ n, d ≤ n ∧ OnCycle n) ∨
      ∃ S : Finset ThreeQuartersNode, ThreeQuartersStoppingFrontier d H S

/-- The mass clause of an exponent-`3/4` stopping frontier forces
`≳ (H/d)^(3/4)`-many distinct endpoints.  The bound is left in multiplication
form so the exponent is displayed exactly. -/
theorem ThreeQuartersStoppingFrontier.card_bound {d H : ℕ}
    {S : Finset ThreeQuartersNode}
    (hd : 1 ≤ d) (hH : 1 ≤ H) (h : ThreeQuartersStoppingFrontier d H S) :
    (threeQuartersPotential 0 d : ℝ) <
      (S.card : ℝ) * (19334101 * ((d : ℝ) / (H : ℝ)) ^ (3 / 4 : ℝ)) := by
  obtain ⟨_, hmass, hleaves⟩ := h
  have hterm (s : ThreeQuartersNode) (hs : s ∈ S) :
      threeQuartersEdgeWeight d s.2 * (threeQuartersPotential s.1 s.2 : ℝ) ≤
        19334101 * ((d : ℝ) / (H : ℝ)) ^ (3 / 4 : ℝ) := by
    have hHy : H ≤ s.2 := (hleaves s hs).1.le
    have hratio : (d : ℝ) / (s.2 : ℝ) ≤ (d : ℝ) / (H : ℝ) := by
      rw [div_le_div_iff_of_pos_left (by exact_mod_cast hd)
        (by exact_mod_cast (hH.trans hHy)) (by exact_mod_cast hH)]
      exact_mod_cast hHy
    have hedge : threeQuartersEdgeWeight d s.2 ≤
        ((d : ℝ) / (H : ℝ)) ^ (3 / 4 : ℝ) := by
      unfold threeQuartersEdgeWeight
      exact Real.rpow_le_rpow (by positivity) hratio (by norm_num)
    have hpotential : (threeQuartersPotential s.1 s.2 : ℝ) ≤ 19334101 := by
      exact_mod_cast threeQuartersPotential_le_max s.1 s.2
    calc
      threeQuartersEdgeWeight d s.2 * (threeQuartersPotential s.1 s.2 : ℝ) ≤
          ((d : ℝ) / (H : ℝ)) ^ (3 / 4 : ℝ) *
            (threeQuartersPotential s.1 s.2 : ℝ) :=
        mul_le_mul_of_nonneg_right hedge (by positivity)
      _ ≤ ((d : ℝ) / (H : ℝ)) ^ (3 / 4 : ℝ) * 19334101 :=
        mul_le_mul_of_nonneg_left hpotential (Real.rpow_nonneg (by positivity) _)
      _ = 19334101 * ((d : ℝ) / (H : ℝ)) ^ (3 / 4 : ℝ) := by ring
  calc
    (threeQuartersPotential 0 d : ℝ) <
        ∑ s ∈ S, threeQuartersEdgeWeight d s.2 *
          (threeQuartersPotential s.1 s.2 : ℝ) := hmass
    _ ≤ S.card • (19334101 * ((d : ℝ) / (H : ℝ)) ^ (3 / 4 : ℝ)) :=
      Finset.sum_le_card_nsmul S _ _ hterm
    _ = (S.card : ℝ) * (19334101 * ((d : ℝ) / (H : ℝ)) ^ (3 / 4 : ℝ)) := by
      simp [nsmul_eq_mul]

end CollatzMoonshot.FrontA
