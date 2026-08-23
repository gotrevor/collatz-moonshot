/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.FrontA.BackwardTwoThirds
import CollatzMoonshot.FrontA.BackwardRenewal

/-!
# Exact real telescoping weights for the exponent-`2/3` backward renewal

The correlated 270-state certificate in `BackwardTwoThirds` proves local
expansion with the *rational* edge underweight `(52/25)·(629/1000)^j`.  Those
rational weights do not telescope along a path.  The correct exponent-`2/3`
renewal weight is the exact real

`((x : ℝ) / (y : ℝ)) ^ (2/3 : ℝ)`.

It telescopes exactly through positive endpoints, and the Collatz odd-block
identity `3y + 1 = 2^j x` proves that every rational certificate weight is
strictly smaller on an actual edge, because

`(52/25)^3 < 9`  and  `4·(629/1000)^3 < 1`.

This file upgrades the actual-child local expansion `exists_twoThirdsExpansion`
to the exact real weight over a finite value-injective child set of
`Fin 5 × ℕ`, records that the frozen potential is positive on unit residues and
uniformly at most `1051827`, and defines the `2/3`-exponent stopping frontier
together with its cardinality bound.  The recursive repeat-or-stopping theorem
is deliberately left for a later lap.
-/

namespace CollatzMoonshot.FrontA

open scoped Real

/-! ## The exact real edge weight and its rational underweight -/

/-- The real version of the rational edge underweight of the `2/3`-certificate. -/
noncomputable def twoThirdsRationalWeight (j : ℕ) : ℝ :=
  (52 / 25 : ℝ) * (629 / 1000 : ℝ) ^ j

/-- The exact exponent-`2/3` edge weight between two positive odd endpoints. -/
noncomputable def twoThirdsEdgeWeight (x y : ℕ) : ℝ :=
  ((x : ℝ) / (y : ℝ)) ^ (2 / 3 : ℝ)

theorem twoThirdsRationalWeight_pos (j : ℕ) : 0 < twoThirdsRationalWeight j := by
  unfold twoThirdsRationalWeight; positivity

theorem twoThirdsEdgeWeight_nonneg (x y : ℕ) : 0 ≤ twoThirdsEdgeWeight x y := by
  unfold twoThirdsEdgeWeight
  exact Real.rpow_nonneg (by positivity) _

/-- The cube of the rational weight is dominated by the square of the ideal
edge factor `3 / 2^j`, from the two elementary rational comparisons. -/
theorem twoThirdsRationalWeight_cube_lt (j : ℕ) (hj : 1 ≤ j) :
    (twoThirdsRationalWeight j) ^ 3 < (3 / (2 : ℝ) ^ j) ^ 2 := by
  have hbase : ((629 / 1000 : ℝ) ^ 3) ^ j < ((1 / 4 : ℝ)) ^ j :=
    pow_lt_pow_left₀ (by norm_num) (by positivity) (by omega)
  have h4 : ((4 : ℝ)) ^ j = ((2 : ℝ) ^ j) ^ 2 := by
    rw [← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, Nat.mul_comm]
  calc
    (twoThirdsRationalWeight j) ^ 3
        = (52 / 25 : ℝ) ^ 3 * ((629 / 1000 : ℝ) ^ 3) ^ j := by
          rw [twoThirdsRationalWeight, mul_pow, ← pow_mul, ← pow_mul,
            Nat.mul_comm j 3]
    _ < 9 * ((629 / 1000 : ℝ) ^ 3) ^ j := by
          apply mul_lt_mul_of_pos_right (by norm_num) (by positivity)
    _ < 9 * ((1 / 4 : ℝ)) ^ j := mul_lt_mul_of_pos_left hbase (by norm_num)
    _ = (3 / (2 : ℝ) ^ j) ^ 2 := by
          rw [one_div_pow, mul_one_div, h4, div_pow]; norm_num

/-- On every actual positive odd block, the rational certificate weight is
strictly below the exact telescoping endpoint weight. -/
theorem twoThirdsRationalWeight_lt_edgeWeight {x y j : ℕ}
    (hy : 1 ≤ y) (hj : 1 ≤ j) (h : 3 * y + 1 = 2 ^ j * x) :
    twoThirdsRationalWeight j < twoThirdsEdgeWeight x y := by
  have hb : (3 : ℝ) * y + 1 = (2 : ℝ) ^ j * x := by exact_mod_cast h
  have hratio : (3 : ℝ) / (2 : ℝ) ^ j < (x : ℝ) / (y : ℝ) := by
    rw [div_lt_div_iff₀ (pow_pos (by norm_num) _) (by exact_mod_cast hy)]
    nlinarith
  have hbpos : (0 : ℝ) < 3 / (2 : ℝ) ^ j := by positivity
  have hBnn : 0 ≤ (3 / (2 : ℝ) ^ j) ^ (2 / 3 : ℝ) :=
    Real.rpow_nonneg (le_of_lt hbpos) _
  have hBcube : ((3 / (2 : ℝ) ^ j) ^ (2 / 3 : ℝ)) ^ (3 : ℕ) =
      (3 / (2 : ℝ) ^ j) ^ 2 := by
    rw [← Real.rpow_natCast ((3 / (2 : ℝ) ^ j) ^ (2 / 3 : ℝ)) 3,
      ← Real.rpow_mul (le_of_lt hbpos), ← Real.rpow_natCast (3 / (2 : ℝ) ^ j) 2]
    norm_num
  have hwlt : twoThirdsRationalWeight j < (3 / (2 : ℝ) ^ j) ^ (2 / 3 : ℝ) := by
    apply lt_of_pow_lt_pow_left₀ 3 hBnn
    rw [hBcube]
    exact twoThirdsRationalWeight_cube_lt j hj
  have hmono : (3 / (2 : ℝ) ^ j) ^ (2 / 3 : ℝ) < twoThirdsEdgeWeight x y := by
    unfold twoThirdsEdgeWeight
    exact Real.rpow_lt_rpow (le_of_lt hbpos) hratio (by norm_num)
  exact hwlt.trans hmono

/-- Exact telescoping of the `2/3`-edge weight through a positive intermediate
endpoint. -/
theorem twoThirdsEdgeWeight_mul {x y z : ℕ} (hy : 1 ≤ y) (hz : 1 ≤ z) :
    twoThirdsEdgeWeight x y * twoThirdsEdgeWeight y z =
      twoThirdsEdgeWeight x z := by
  have hy0 : (y : ℝ) ≠ 0 := by positivity
  have hz0 : (z : ℝ) ≠ 0 := by positivity
  unfold twoThirdsEdgeWeight
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  congr 1
  field_simp

/-! ## Positivity and a uniform ceiling for the frozen potential -/

/-- Every reusable residue has strictly positive potential at every floor. -/
theorem twoThirdsPotential_pos {x : ℕ} (h3 : ¬3 ∣ x) (i : Fin 5) :
    0 < twoThirdsPotential i x := by
  rw [← twoThirdsPotential_mod]
  have hr81 : x % 81 < 81 := Nat.mod_lt x (by norm_num)
  have hru : (x % 81) % 3 ≠ 0 := by
    rw [Nat.mod_mod_of_dvd x (by norm_num : 3 ∣ 81)]
    exact fun h0 => h3 (Nat.dvd_of_mod_eq_zero h0)
  exact twoThirdsPotential_pos_of_unit i ⟨x % 81, hr81⟩ hru

/-- Every entry of the frozen `2/3`-potential is at most `1051827`. -/
theorem twoThirdsPotential_le_max_fin :
    ∀ i : Fin 5, ∀ r : Fin 81, twoThirdsPotential i r.1 ≤ 1051827 := by
  decide +kernel

/-- The frozen `2/3`-potential is uniformly at most `1051827`. -/
theorem twoThirdsPotential_le_max (i : Fin 5) (x : ℕ) :
    twoThirdsPotential i x ≤ 1051827 := by
  rw [← twoThirdsPotential_mod]
  have hr81 : x % 81 < 81 := Nat.mod_lt x (by norm_num)
  exact twoThirdsPotential_le_max_fin i ⟨x % 81, hr81⟩

/-! ## The finite value-injective child set with exact real weights -/

/-- A five-height state paired with its odd endpoint. -/
abbrev TwoThirdsNode := Fin 5 × ℕ

/-- The local reusable child relation used by the stopping construction. -/
def TwoThirdsChildAt (d : ℕ) (parent child : TwoThirdsNode) : Prop :=
  ReusableOddBlockChild parent.2 child.2 ∧
    InFiveHeightState d child.1 child.2

/-- A finite state frontier does not count one natural endpoint twice under
different state labels. -/
def TwoThirdsValuesInjective (C : Finset TwoThirdsNode) : Prop :=
  ∀ a ∈ C, ∀ b ∈ C, a.2 = b.2 → a = b

/-- **Exact real exponent-`2/3` local expansion.**  Every reusable source
`x ≥ 2`, `3 ∤ x` in one of the five height states over a floor `d ≥ 2` has a
nonempty, value-injective finite child set of actual reusable Collatz children,
all in their floor-safe five-height states, each with `3 c < 2^23 x`, whose
frozen potential strictly expands the source potential under the exact
telescoping weight `((x)/(c))^(2/3)`. -/
theorem exists_twoThirdsChildFinset {d x : ℕ} (i : Fin 5) (hd : 2 ≤ d)
    (hx : 2 ≤ x) (h3 : ¬3 ∣ x) (hstate : InFiveHeightState d i x) :
    ∃ C : Finset TwoThirdsNode, C.Nonempty ∧ TwoThirdsValuesInjective C ∧
      (∀ c ∈ C, TwoThirdsChildAt d (i, x) c) ∧
      (∀ c ∈ C, 3 * c.2 < 2 ^ 23 * x) ∧
      (twoThirdsPotential i x : ℝ) <
        ∑ c ∈ C, twoThirdsEdgeWeight x c.2 *
          (twoThirdsPotential c.1 c.2 : ℝ) := by
  obtain ⟨ys, z, hys, hgrow, hshrink, hrat⟩ :=
    exists_twoThirdsExpansion i hd hx h3 hstate
  -- The seven growing nodes, packaged as an injective image.
  let g : Fin 7 → TwoThirdsNode := fun k =>
    (nextGrowingFiveState i (sevenCostsAt x k), ys k)
  have hg : Function.Injective g := fun k k' hkk' => hys (congrArg Prod.snd hkk')
  -- The rational potential of each growing child equals the potential at `g k`.
  -- The edge upgrade for a single growing child.
  have hgrowEdge : ∀ k : Fin 7,
      twoThirdsRationalWeight (sevenCostsAt x k) *
          (twoThirdsPotential (nextGrowingFiveState i (sevenCostsAt x k))
            (ys k) : ℝ) <
        twoThirdsEdgeWeight x (ys k) *
          (twoThirdsPotential (nextGrowingFiveState i (sevenCostsAt x k))
            (ys k) : ℝ) := by
    intro k
    apply mul_lt_mul_of_pos_right
    · obtain ⟨hj, hyodd, hy3, _, hblock⟩ := (hgrow k).1
      exact twoThirdsRationalWeight_lt_edgeWeight (by omega) (by omega) hblock
    · exact_mod_cast twoThirdsPotential_pos
        (by obtain ⟨_, _, hy3, _, _⟩ := (hgrow k).1; exact hy3) _
  by_cases hs : fiveHasShrink i x = true
  · -- Shrinking child is enabled: eight children.
    obtain ⟨hzchild, hzstate, hzne⟩ := hshrink hs
    have hznot : (shrinkFiveState i, z) ∉ Finset.univ.image g := by
      intro hmem
      obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hmem
      exact hzne k (congrArg Prod.snd hk).symm
    refine ⟨insert (shrinkFiveState i, z) (Finset.univ.image g), ?_, ?_, ?_, ?_, ?_⟩
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
          (twoThirdsPotential i x : ℝ) <
            (twoThirdsEdgeWeight x z *
              (twoThirdsPotential (shrinkFiveState i) z : ℝ)) +
            ∑ k : Fin 7, twoThirdsEdgeWeight x (ys k) *
              (twoThirdsPotential (nextGrowingFiveState i (sevenCostsAt x k))
                (ys k) : ℝ) := by
        have hzedge :
            twoThirdsRationalWeight 1 *
                (twoThirdsPotential (shrinkFiveState i) z : ℝ) <
              twoThirdsEdgeWeight x z *
                (twoThirdsPotential (shrinkFiveState i) z : ℝ) := by
          obtain ⟨hzodd, hz3, _, hblock⟩ := hzchild
          apply mul_lt_mul_of_pos_right
          · exact twoThirdsRationalWeight_lt_edgeWeight
              (by omega) (by norm_num) (by simpa using hblock)
          · exact_mod_cast twoThirdsPotential_pos hz3 _
        -- cast the rational certificate to ℝ, then upgrade each term
        have hcast : (twoThirdsPotential i x : ℝ) <
            (52 / 25 : ℝ) *
              ((∑ k : Fin 7, (629 / 1000 : ℝ) ^ sevenCostsAt x k *
                  (twoThirdsPotential
                    (nextGrowingFiveState i (sevenCostsAt x k)) (ys k) : ℝ)) +
                (629 / 1000 : ℝ) *
                  (twoThirdsPotential (shrinkFiveState i) z : ℝ)) := by
          have := (Rat.cast_lt (K := ℝ)).mpr hrat
          simp only [hs, if_true] at this
          push_cast at this
          convert this using 2
        rw [mul_add, Finset.mul_sum] at hcast
        have hgrowSum :
            (∑ k : Fin 7, (52 / 25 : ℝ) *
                ((629 / 1000 : ℝ) ^ sevenCostsAt x k *
                  (twoThirdsPotential
                    (nextGrowingFiveState i (sevenCostsAt x k)) (ys k) : ℝ))) <
              ∑ k : Fin 7, twoThirdsEdgeWeight x (ys k) *
                (twoThirdsPotential
                  (nextGrowingFiveState i (sevenCostsAt x k)) (ys k) : ℝ) := by
          apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
          intro k _
          rw [← mul_assoc]
          exact hgrowEdge k
        have hshrinkTerm :
            (52 / 25 : ℝ) *
                ((629 / 1000 : ℝ) *
                  (twoThirdsPotential (shrinkFiveState i) z : ℝ)) <
              twoThirdsEdgeWeight x z *
                (twoThirdsPotential (shrinkFiveState i) z : ℝ) := by
          have heq : (52 / 25 : ℝ) *
              ((629 / 1000 : ℝ) *
                (twoThirdsPotential (shrinkFiveState i) z : ℝ)) =
              twoThirdsRationalWeight 1 *
                (twoThirdsPotential (shrinkFiveState i) z : ℝ) := by
            simp [twoThirdsRationalWeight]; ring
          rw [heq]; exact hzedge
        linarith [hcast, add_lt_add hgrowSum hshrinkTerm]
      linarith [hmass]
  · -- Shrinking child disabled: seven children.
    have hsf : fiveHasShrink i x = false := by
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
      have hcast : (twoThirdsPotential i x : ℝ) <
          (52 / 25 : ℝ) *
            (∑ k : Fin 7, (629 / 1000 : ℝ) ^ sevenCostsAt x k *
                (twoThirdsPotential
                  (nextGrowingFiveState i (sevenCostsAt x k)) (ys k) : ℝ)) := by
        have := (Rat.cast_lt (K := ℝ)).mpr hrat
        simp only [hsf, Bool.false_eq_true, if_false, add_zero] at this
        push_cast at this
        convert this using 2
      rw [Finset.mul_sum] at hcast
      have hgrowSum :
          (∑ k : Fin 7, (52 / 25 : ℝ) *
              ((629 / 1000 : ℝ) ^ sevenCostsAt x k *
                (twoThirdsPotential
                  (nextGrowingFiveState i (sevenCostsAt x k)) (ys k) : ℝ))) <
            ∑ k : Fin 7, twoThirdsEdgeWeight x (ys k) *
              (twoThirdsPotential
                (nextGrowingFiveState i (sevenCostsAt x k)) (ys k) : ℝ) := by
        apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
        intro k _
        rw [← mul_assoc]
        exact hgrowEdge k
      linarith [hcast, hgrowSum]

/-! ## The exponent-`2/3` stopping frontier and its cardinal bound -/

/-- A finite first-exit frontier with enough exponent-`2/3` telescoping mass,
exactly analogous to `NetHalfStoppingFrontier`.  The value-injectivity clause
makes its cardinality count distinct natural endpoints. -/
def TwoThirdsStoppingFrontier (d H : ℕ) (S : Finset TwoThirdsNode) : Prop :=
  (∀ a ∈ S, ∀ b ∈ S, a.2 = b.2 → a = b) ∧
  (twoThirdsPotential 0 d : ℝ) <
    ∑ s ∈ S, twoThirdsEdgeWeight d s.2 * (twoThirdsPotential s.1 s.2 : ℝ) ∧
  ∀ s ∈ S, H < s.2 ∧ s.2 < 2 ^ 23 * H ∧
    ReachesInBand d (2 ^ 25 * H) s.2

/-- The remaining scoped theorem, exactly analogous to
`NetHalfRepeatOrStoppingGrowth`: every odd reusable root either exposes a
positive cycle above its floor or has a finite first-exit frontier carrying the
certified exponent-`2/3` mass.  Left as a definition until the recursive
stopping-line bookkeeping is completed in a later lap. -/
def TwoThirdsRepeatOrStoppingGrowth : Prop :=
  ∀ d H : ℕ, 2 ≤ d → d % 2 = 1 → ¬3 ∣ d → d ≤ H →
    (∃ n, d ≤ n ∧ OnCycle n) ∨
      ∃ S : Finset TwoThirdsNode, TwoThirdsStoppingFrontier d H S

/-- The mass clause of an exponent-`2/3` stopping frontier forces
`≳ (H/d)^(2/3)`-many distinct endpoints.  The bound is left in multiplication
form so the exponent is displayed exactly. -/
theorem TwoThirdsStoppingFrontier.card_bound {d H : ℕ} {S : Finset TwoThirdsNode}
    (hd : 1 ≤ d) (hH : 1 ≤ H) (h : TwoThirdsStoppingFrontier d H S) :
    (twoThirdsPotential 0 d : ℝ) <
      (S.card : ℝ) * (1051827 * ((d : ℝ) / (H : ℝ)) ^ (2 / 3 : ℝ)) := by
  obtain ⟨_, hmass, hleaves⟩ := h
  have hterm (s : TwoThirdsNode) (hs : s ∈ S) :
      twoThirdsEdgeWeight d s.2 * (twoThirdsPotential s.1 s.2 : ℝ) ≤
        1051827 * ((d : ℝ) / (H : ℝ)) ^ (2 / 3 : ℝ) := by
    have hHy : H ≤ s.2 := (hleaves s hs).1.le
    have hratio : (d : ℝ) / (s.2 : ℝ) ≤ (d : ℝ) / (H : ℝ) := by
      rw [div_le_div_iff_of_pos_left (by exact_mod_cast hd)
        (by exact_mod_cast (hH.trans hHy)) (by exact_mod_cast hH)]
      exact_mod_cast hHy
    have hedge : twoThirdsEdgeWeight d s.2 ≤
        ((d : ℝ) / (H : ℝ)) ^ (2 / 3 : ℝ) := by
      unfold twoThirdsEdgeWeight
      exact Real.rpow_le_rpow (by positivity) hratio (by norm_num)
    have hpotential : (twoThirdsPotential s.1 s.2 : ℝ) ≤ 1051827 := by
      exact_mod_cast twoThirdsPotential_le_max s.1 s.2
    calc
      twoThirdsEdgeWeight d s.2 * (twoThirdsPotential s.1 s.2 : ℝ) ≤
          ((d : ℝ) / (H : ℝ)) ^ (2 / 3 : ℝ) *
            (twoThirdsPotential s.1 s.2 : ℝ) :=
        mul_le_mul_of_nonneg_right hedge (by positivity)
      _ ≤ ((d : ℝ) / (H : ℝ)) ^ (2 / 3 : ℝ) * 1051827 :=
        mul_le_mul_of_nonneg_left hpotential (Real.rpow_nonneg (by positivity) _)
      _ = 1051827 * ((d : ℝ) / (H : ℝ)) ^ (2 / 3 : ℝ) := by ring
  calc
    (twoThirdsPotential 0 d : ℝ) <
        ∑ s ∈ S, twoThirdsEdgeWeight d s.2 *
          (twoThirdsPotential s.1 s.2 : ℝ) := hmass
    _ ≤ S.card • (1051827 * ((d : ℝ) / (H : ℝ)) ^ (2 / 3 : ℝ)) :=
      Finset.sum_le_card_nsmul S _ _ hterm
    _ = (S.card : ℝ) * (1051827 * ((d : ℝ) / (H : ℝ)) ^ (2 / 3 : ℝ)) := by
      simp [nsmul_eq_mul]

end CollatzMoonshot.FrontA
