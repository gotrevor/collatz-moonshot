/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.FrontA.BackwardFourFifths
import CollatzMoonshot.FrontA.BackwardRenewal

/-!
# Exact real telescoping weights for the exponent-`4/5` backward renewal

The correlated 21870-state certificate in `BackwardFourFifths` proves local
expansion with the *rational* edge underweight `(75257/31250)·(574349/1000000)^j`.
Those rational weights do not telescope along a path.  The correct
exponent-`4/5` renewal weight is the exact real

`((x : ℝ) / (y : ℝ)) ^ (4/5 : ℝ)`.

It telescopes exactly through positive endpoints, and the Collatz odd-block
identity `3y + 1 = 2^j x` proves that every rational certificate weight is
strictly smaller on an actual edge, because

`(75257/31250)^5 < 81`  and  `16·(574349/1000000)^5 < 1`.

This file upgrades the actual-child local expansion `exists_fourFifthsExpansion`
to the exact real weight over a finite value-injective child set of
`Fin 5 × ℕ`, records that the frozen potential is positive on unit residues and
uniformly at most `41080952`, and defines the `4/5`-exponent stopping frontier
together with its cardinality bound.  The recursive repeat-or-stopping theorem
is completed in `BackwardFourFifthsStopping.lean`.
-/

namespace CollatzMoonshot.FrontA

open scoped Real

set_option maxRecDepth 400000

/-! ## The exact real edge weight and its rational underweight -/

/-- The real version of the rational edge underweight of the `4/5`-certificate. -/
noncomputable def fourFifthsRationalWeight (j : ℕ) : ℝ :=
  (75257 / 31250 : ℝ) * (574349 / 1000000 : ℝ) ^ j

/-- The exact exponent-`4/5` edge weight between two positive odd endpoints. -/
noncomputable def fourFifthsEdgeWeight (x y : ℕ) : ℝ :=
  ((x : ℝ) / (y : ℝ)) ^ (4 / 5 : ℝ)

theorem fourFifthsRationalWeight_pos (j : ℕ) :
    0 < fourFifthsRationalWeight j := by
  unfold fourFifthsRationalWeight; positivity

theorem fourFifthsEdgeWeight_nonneg (x y : ℕ) :
    0 ≤ fourFifthsEdgeWeight x y := by
  unfold fourFifthsEdgeWeight
  exact Real.rpow_nonneg (by positivity) _

/-- The fifth power of the rational weight is dominated by the fourth power of the
ideal edge factor `3 / 2^j`, from the two elementary rational comparisons
`(75257/31250)^5 < 81` and `16·(574349/1000000)^5 < 1`. -/
theorem fourFifthsRationalWeight_fifth_lt (j : ℕ) (hj : 1 ≤ j) :
    (fourFifthsRationalWeight j) ^ 5 < (3 / (2 : ℝ) ^ j) ^ 4 := by
  have hbase : ((574349 / 1000000 : ℝ) ^ 5) ^ j < ((1 / 16 : ℝ)) ^ j :=
    pow_lt_pow_left₀ (by norm_num) (by positivity) (by omega)
  have h16 : ((16 : ℝ)) ^ j = ((2 : ℝ) ^ j) ^ 4 := by
    rw [← pow_mul, show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul, Nat.mul_comm]
  calc
    (fourFifthsRationalWeight j) ^ 5
        = (75257 / 31250 : ℝ) ^ 5 * ((574349 / 1000000 : ℝ) ^ 5) ^ j := by
          rw [fourFifthsRationalWeight, mul_pow, ← pow_mul, ← pow_mul,
            Nat.mul_comm j 5]
    _ < 81 * ((574349 / 1000000 : ℝ) ^ 5) ^ j := by
          apply mul_lt_mul_of_pos_right (by norm_num) (by positivity)
    _ < 81 * ((1 / 16 : ℝ)) ^ j := mul_lt_mul_of_pos_left hbase (by norm_num)
    _ = (3 / (2 : ℝ) ^ j) ^ 4 := by
          rw [one_div_pow, mul_one_div, h16, div_pow]; norm_num

/-- On every actual positive odd block, the rational certificate weight is
strictly below the exact telescoping endpoint weight. -/
theorem fourFifthsRationalWeight_lt_edgeWeight {x y j : ℕ}
    (hy : 1 ≤ y) (hj : 1 ≤ j) (h : 3 * y + 1 = 2 ^ j * x) :
    fourFifthsRationalWeight j < fourFifthsEdgeWeight x y := by
  have hb : (3 : ℝ) * y + 1 = (2 : ℝ) ^ j * x := by exact_mod_cast h
  have hratio : (3 : ℝ) / (2 : ℝ) ^ j < (x : ℝ) / (y : ℝ) := by
    rw [div_lt_div_iff₀ (pow_pos (by norm_num) _) (by exact_mod_cast hy)]
    nlinarith
  have hbpos : (0 : ℝ) < 3 / (2 : ℝ) ^ j := by positivity
  have hBnn : 0 ≤ (3 / (2 : ℝ) ^ j) ^ (4 / 5 : ℝ) :=
    Real.rpow_nonneg (le_of_lt hbpos) _
  have hBfifth : ((3 / (2 : ℝ) ^ j) ^ (4 / 5 : ℝ)) ^ (5 : ℕ) =
      (3 / (2 : ℝ) ^ j) ^ 4 := by
    rw [← Real.rpow_natCast ((3 / (2 : ℝ) ^ j) ^ (4 / 5 : ℝ)) 5,
      ← Real.rpow_mul (le_of_lt hbpos), ← Real.rpow_natCast (3 / (2 : ℝ) ^ j) 4]
    norm_num
  have hwlt : fourFifthsRationalWeight j <
      (3 / (2 : ℝ) ^ j) ^ (4 / 5 : ℝ) := by
    apply lt_of_pow_lt_pow_left₀ 5 hBnn
    rw [hBfifth]
    exact fourFifthsRationalWeight_fifth_lt j hj
  have hmono : (3 / (2 : ℝ) ^ j) ^ (4 / 5 : ℝ) <
      fourFifthsEdgeWeight x y := by
    unfold fourFifthsEdgeWeight
    exact Real.rpow_lt_rpow (le_of_lt hbpos) hratio (by norm_num)
  exact hwlt.trans hmono

/-- Exact telescoping of the `4/5`-edge weight through a positive intermediate
endpoint. -/
theorem fourFifthsEdgeWeight_mul {x y z : ℕ} (hy : 1 ≤ y) (hz : 1 ≤ z) :
    fourFifthsEdgeWeight x y * fourFifthsEdgeWeight y z =
      fourFifthsEdgeWeight x z := by
  have hy0 : (y : ℝ) ≠ 0 := by positivity
  have hz0 : (z : ℝ) ≠ 0 := by positivity
  unfold fourFifthsEdgeWeight
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  congr 1
  field_simp

/-! ## Positivity and a uniform ceiling for the frozen potential -/

/-- Every reusable residue has strictly positive potential at every floor. -/
theorem fourFifthsPotential_pos {x : ℕ} (h3 : ¬3 ∣ x) (i : Fin 5) :
    0 < fourFifthsPotential i x := by
  rw [← fourFifthsPotential_mod]
  have hr6561 : x % 6561 < 6561 := Nat.mod_lt x (by norm_num)
  have hru : (x % 6561) % 3 ≠ 0 := by
    rw [Nat.mod_mod_of_dvd x (by norm_num : 3 ∣ 6561)]
    exact fun h0 => h3 (Nat.dvd_of_mod_eq_zero h0)
  exact fourFifthsPotential_pos_of_unit i ⟨x % 6561, hr6561⟩ hru

/-- Every entry of the frozen `4/5`-potential is at most `41080952`. -/
theorem fourFifthsPotential_le_max_fin :
    ∀ i : Fin 5, ∀ r : Fin 6561, fourFifthsPotential i r.1 ≤ 41080952 := by
  native_decide

/-- The frozen `4/5`-potential is uniformly at most `41080952`. -/
theorem fourFifthsPotential_le_max (i : Fin 5) (x : ℕ) :
    fourFifthsPotential i x ≤ 41080952 := by
  rw [← fourFifthsPotential_mod]
  have hr6561 : x % 6561 < 6561 := Nat.mod_lt x (by norm_num)
  exact fourFifthsPotential_le_max_fin i ⟨x % 6561, hr6561⟩

/-! ## The finite value-injective child set with exact real weights -/

/-- A five-height state paired with its odd endpoint. -/
abbrev FourFifthsNode := Fin 5 × ℕ

/-- The local reusable child relation used by the stopping construction. -/
def FourFifthsChildAt (d : ℕ) (parent child : FourFifthsNode) : Prop :=
  ReusableOddBlockChild parent.2 child.2 ∧
    InThreeQuartersHeightState d child.1 child.2

/-- A finite state frontier does not count one natural endpoint twice under
different state labels. -/
def FourFifthsValuesInjective (C : Finset FourFifthsNode) : Prop :=
  ∀ a ∈ C, ∀ b ∈ C, a.2 = b.2 → a = b

/-- **Exact real exponent-`4/5` local expansion.**  Every reusable source
`x ≥ 2`, `3 ∤ x` in one of the five height states over a floor `d ≥ 2` has a
nonempty, value-injective finite child set of actual reusable Collatz children,
all in their floor-safe five-height states, each with `3 c < 2^23 x`, whose
frozen potential strictly expands the source potential under the exact
telescoping weight `((x)/(c))^(4/5)`. -/
theorem exists_fourFifthsChildFinset {d x : ℕ} (i : Fin 5) (hd : 2 ≤ d)
    (hx : 2 ≤ x) (h3 : ¬3 ∣ x) (hstate : InThreeQuartersHeightState d i x) :
    ∃ C : Finset FourFifthsNode, C.Nonempty ∧ FourFifthsValuesInjective C ∧
      (∀ c ∈ C, FourFifthsChildAt d (i, x) c) ∧
      (∀ c ∈ C, 3 * c.2 < 2 ^ 23 * x) ∧
      (fourFifthsPotential i x : ℝ) <
        ∑ c ∈ C, fourFifthsEdgeWeight x c.2 *
          (fourFifthsPotential c.1 c.2 : ℝ) := by
  obtain ⟨ys, z, hys, hgrow, hshrink, hrat⟩ :=
    exists_fourFifthsExpansion i hd hx h3 hstate
  -- The seven growing nodes, packaged as an injective image.
  let g : Fin 7 → FourFifthsNode := fun k =>
    (nextThreeQuartersState i (sevenCostsAt x k), ys k)
  have hg : Function.Injective g := fun k k' hkk' => hys (congrArg Prod.snd hkk')
  -- The edge upgrade for a single growing child.
  have hgrowEdge : ∀ k : Fin 7,
      fourFifthsRationalWeight (sevenCostsAt x k) *
          (fourFifthsPotential (nextThreeQuartersState i (sevenCostsAt x k))
            (ys k) : ℝ) <
        fourFifthsEdgeWeight x (ys k) *
          (fourFifthsPotential (nextThreeQuartersState i (sevenCostsAt x k))
            (ys k) : ℝ) := by
    intro k
    apply mul_lt_mul_of_pos_right
    · obtain ⟨hj, hyodd, hy3, _, hblock⟩ := (hgrow k).1
      exact fourFifthsRationalWeight_lt_edgeWeight (by omega) (by omega) hblock
    · exact_mod_cast fourFifthsPotential_pos
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
          (fourFifthsPotential i x : ℝ) <
            (fourFifthsEdgeWeight x z *
              (fourFifthsPotential (shrinkThreeQuartersState i) z : ℝ)) +
            ∑ k : Fin 7, fourFifthsEdgeWeight x (ys k) *
              (fourFifthsPotential (nextThreeQuartersState i (sevenCostsAt x k))
                (ys k) : ℝ) := by
        have hzedge :
            fourFifthsRationalWeight 1 *
                (fourFifthsPotential (shrinkThreeQuartersState i) z : ℝ) <
              fourFifthsEdgeWeight x z *
                (fourFifthsPotential (shrinkThreeQuartersState i) z : ℝ) := by
          obtain ⟨hzodd, hz3, _, hblock⟩ := hzchild
          apply mul_lt_mul_of_pos_right
          · exact fourFifthsRationalWeight_lt_edgeWeight
              (by omega) (by norm_num) (by simpa using hblock)
          · exact_mod_cast fourFifthsPotential_pos hz3 _
        -- cast the rational certificate to ℝ, then upgrade each term
        have hcast : (fourFifthsPotential i x : ℝ) <
            (75257 / 31250 : ℝ) *
              ((∑ k : Fin 7, (574349 / 1000000 : ℝ) ^ sevenCostsAt x k *
                  (fourFifthsPotential
                    (nextThreeQuartersState i (sevenCostsAt x k)) (ys k) : ℝ)) +
                (574349 / 1000000 : ℝ) *
                  (fourFifthsPotential (shrinkThreeQuartersState i) z : ℝ)) := by
          have := (Rat.cast_lt (K := ℝ)).mpr hrat
          simp only [hs, if_true] at this
          push_cast at this
          convert this using 2
        rw [mul_add, Finset.mul_sum] at hcast
        have hgrowSum :
            (∑ k : Fin 7, (75257 / 31250 : ℝ) *
                ((574349 / 1000000 : ℝ) ^ sevenCostsAt x k *
                  (fourFifthsPotential
                    (nextThreeQuartersState i (sevenCostsAt x k)) (ys k) : ℝ))) <
              ∑ k : Fin 7, fourFifthsEdgeWeight x (ys k) *
                (fourFifthsPotential
                  (nextThreeQuartersState i (sevenCostsAt x k)) (ys k) : ℝ) := by
          apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
          intro k _
          rw [← mul_assoc]
          exact hgrowEdge k
        have hshrinkTerm :
            (75257 / 31250 : ℝ) *
                ((574349 / 1000000 : ℝ) *
                  (fourFifthsPotential (shrinkThreeQuartersState i) z : ℝ)) <
              fourFifthsEdgeWeight x z *
                (fourFifthsPotential (shrinkThreeQuartersState i) z : ℝ) := by
          have heq : (75257 / 31250 : ℝ) *
              ((574349 / 1000000 : ℝ) *
                (fourFifthsPotential (shrinkThreeQuartersState i) z : ℝ)) =
              fourFifthsRationalWeight 1 *
                (fourFifthsPotential (shrinkThreeQuartersState i) z : ℝ) := by
            simp [fourFifthsRationalWeight]; ring
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
      have hcast : (fourFifthsPotential i x : ℝ) <
          (75257 / 31250 : ℝ) *
            (∑ k : Fin 7, (574349 / 1000000 : ℝ) ^ sevenCostsAt x k *
                (fourFifthsPotential
                  (nextThreeQuartersState i (sevenCostsAt x k)) (ys k) : ℝ)) := by
        have := (Rat.cast_lt (K := ℝ)).mpr hrat
        simp only [hsf, Bool.false_eq_true, if_false, add_zero] at this
        push_cast at this
        convert this using 2
      rw [Finset.mul_sum] at hcast
      have hgrowSum :
          (∑ k : Fin 7, (75257 / 31250 : ℝ) *
              ((574349 / 1000000 : ℝ) ^ sevenCostsAt x k *
                (fourFifthsPotential
                  (nextThreeQuartersState i (sevenCostsAt x k)) (ys k) : ℝ))) <
            ∑ k : Fin 7, fourFifthsEdgeWeight x (ys k) *
              (fourFifthsPotential
                (nextThreeQuartersState i (sevenCostsAt x k)) (ys k) : ℝ) := by
        apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
        intro k _
        rw [← mul_assoc]
        exact hgrowEdge k
      linarith [hcast, hgrowSum]

/-! ## The exponent-`4/5` stopping frontier and its cardinal bound -/

/-- A finite first-exit frontier with enough exponent-`4/5` telescoping mass,
exactly analogous to `NetHalfStoppingFrontier`.  The value-injectivity clause
makes its cardinality count distinct natural endpoints. -/
def FourFifthsStoppingFrontier (d H : ℕ) (S : Finset FourFifthsNode) : Prop :=
  (∀ a ∈ S, ∀ b ∈ S, a.2 = b.2 → a = b) ∧
  (fourFifthsPotential 0 d : ℝ) <
    ∑ s ∈ S, fourFifthsEdgeWeight d s.2 * (fourFifthsPotential s.1 s.2 : ℝ) ∧
  ∀ s ∈ S, H < s.2 ∧ s.2 < 2 ^ 23 * H ∧
    ReachesInBand d (2 ^ 25 * H) s.2

/-- The remaining scoped theorem, exactly analogous to
`NetHalfRepeatOrStoppingGrowth`: every odd reusable root either exposes a
positive cycle above its floor or has a finite first-exit frontier carrying the
certified exponent-`4/5` mass.  Proved in `BackwardFourFifthsStopping.lean`. -/
def FourFifthsRepeatOrStoppingGrowth : Prop :=
  ∀ d H : ℕ, 2 ≤ d → d % 2 = 1 → ¬3 ∣ d → d ≤ H →
    (∃ n, d ≤ n ∧ OnCycle n) ∨
      ∃ S : Finset FourFifthsNode, FourFifthsStoppingFrontier d H S

/-- The mass clause of an exponent-`4/5` stopping frontier forces
`≳ (H/d)^(4/5)`-many distinct endpoints.  The bound is left in multiplication
form so the exponent is displayed exactly. -/
theorem FourFifthsStoppingFrontier.card_bound {d H : ℕ}
    {S : Finset FourFifthsNode}
    (hd : 1 ≤ d) (hH : 1 ≤ H) (h : FourFifthsStoppingFrontier d H S) :
    (fourFifthsPotential 0 d : ℝ) <
      (S.card : ℝ) * (41080952 * ((d : ℝ) / (H : ℝ)) ^ (4 / 5 : ℝ)) := by
  obtain ⟨_, hmass, hleaves⟩ := h
  have hterm (s : FourFifthsNode) (hs : s ∈ S) :
      fourFifthsEdgeWeight d s.2 * (fourFifthsPotential s.1 s.2 : ℝ) ≤
        41080952 * ((d : ℝ) / (H : ℝ)) ^ (4 / 5 : ℝ) := by
    have hHy : H ≤ s.2 := (hleaves s hs).1.le
    have hratio : (d : ℝ) / (s.2 : ℝ) ≤ (d : ℝ) / (H : ℝ) := by
      rw [div_le_div_iff_of_pos_left (by exact_mod_cast hd)
        (by exact_mod_cast (hH.trans hHy)) (by exact_mod_cast hH)]
      exact_mod_cast hHy
    have hedge : fourFifthsEdgeWeight d s.2 ≤
        ((d : ℝ) / (H : ℝ)) ^ (4 / 5 : ℝ) := by
      unfold fourFifthsEdgeWeight
      exact Real.rpow_le_rpow (by positivity) hratio (by norm_num)
    have hpotential : (fourFifthsPotential s.1 s.2 : ℝ) ≤ 41080952 := by
      exact_mod_cast fourFifthsPotential_le_max s.1 s.2
    calc
      fourFifthsEdgeWeight d s.2 * (fourFifthsPotential s.1 s.2 : ℝ) ≤
          ((d : ℝ) / (H : ℝ)) ^ (4 / 5 : ℝ) *
            (fourFifthsPotential s.1 s.2 : ℝ) :=
        mul_le_mul_of_nonneg_right hedge (by positivity)
      _ ≤ ((d : ℝ) / (H : ℝ)) ^ (4 / 5 : ℝ) * 41080952 :=
        mul_le_mul_of_nonneg_left hpotential (Real.rpow_nonneg (by positivity) _)
      _ = 41080952 * ((d : ℝ) / (H : ℝ)) ^ (4 / 5 : ℝ) := by ring
  calc
    (fourFifthsPotential 0 d : ℝ) <
        ∑ s ∈ S, fourFifthsEdgeWeight d s.2 *
          (fourFifthsPotential s.1 s.2 : ℝ) := hmass
    _ ≤ S.card • (41080952 * ((d : ℝ) / (H : ℝ)) ^ (4 / 5 : ℝ)) :=
      Finset.sum_le_card_nsmul S _ _ hterm
    _ = (S.card : ℝ) * (41080952 * ((d : ℝ) / (H : ℝ)) ^ (4 / 5 : ℝ)) := by
      simp [nsmul_eq_mul]

end CollatzMoonshot.FrontA
