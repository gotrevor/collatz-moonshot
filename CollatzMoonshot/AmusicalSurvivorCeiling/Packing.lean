/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalSurvivorSeparation
import CollatzMoonshot.AmusicalLateDrops
import CollatzMoonshot.AmusicalSpitzer

/-!
# The survivor ceiling: packing lemmas

Direction-generic helpers for `AmusicalSurvivorCeiling`.  Throughout, `f` is the direction in which
the points survive forever and `g` (with `f ∘ g = id`) is the direction of the finite window that
they fail.  The forward case is `f = U`, `g = V`; the backward case is `f = V`, `g = U`.

* `le_iterate_of_firstDrop` (P′): `n' < n` survivors on one orbit, `k` before `n`'s first
  `g`-drop: `n' ≤ gᵏ n`.
* `le_four_pow_mul_sub` (gap): if `n` fails the `g`-window of length `L`, then
  `n ≤ 4^L (n − n' + 1)`.
* `card_le_of_sep`, `card_orbit_le` (packing on one orbit), `card_le_of_finite` (all orbits),
  `card_survivor_le_split`, and the two density statements `density_le_of_finite` (C2) and
  `infinitelyManyOrbits_of_density` (C2′).
-/

namespace CollatzMoonshot.Amusical.Ceiling

variable {f g : ℤ → ℤ}

/-- **P′.**  Let `n' < n` be `f`-survivors on one orbit, and `k` such that `g` does not undercut
`n` at times `1, …, k − 1`.  Then `n' ≤ gᵏ n`. -/
theorem le_iterate_of_firstDrop (hfg : ∀ x, f (g x) = x) {n n' : ℤ}
    (hn : ∀ t : ℕ, 1 ≤ t → n ≤ f^[t] n) (hn' : ∀ t : ℕ, 1 ≤ t → n' ≤ f^[t] n')
    (hlt : n' < n) (horb : ∃ t : ℕ, n' = f^[t] n ∨ n' = g^[t] n) {k : ℕ}
    (hmin : ∀ t : ℕ, 1 ≤ t → t < k → n ≤ g^[t] n) : n' ≤ g^[k] n := by
  obtain ⟨t, ht | ht⟩ := horb
  · rcases Nat.eq_zero_or_pos t with rfl | ht0
    · simp at ht; omega
    · have := hn t ht0; omega
  · rcases lt_trichotomy t k with h | rfl | h
    · rcases Nat.eq_zero_or_pos t with rfl | ht0
      · simp at ht; omega
      · have := hmin t ht0 h; omega
    · exact ht.le
    · obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_lt h
      have hback : f^[s + 1] n' = g^[k] n := by
        rw [ht, show k + s + 1 = (s + 1) + k by omega, Function.iterate_add_apply g (s + 1) k n]
        exact (Function.LeftInverse.iterate hfg (s + 1)) _
      have := hn' (s + 1) (by omega)
      omega

/-- **Gap.**  If `n' < n` are `f`-survivors on one orbit and `n` fails the `g`-window of length
`L`, then `n ≤ 4^L (n − n' + 1)` (Lemma K at `n`'s first `g`-drop). -/
theorem le_four_pow_mul_sub (hfg : ∀ x, f (g x) = x)
    (hK : ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ x : ℤ, |x| ≤ 4 ^ ℓ * (|g^[ℓ] x - x| + 1)) {L : ℕ} {n n' : ℤ}
    (hn : ∀ t : ℕ, 1 ≤ t → n ≤ f^[t] n) (hn' : ∀ t : ℕ, 1 ≤ t → n' ≤ f^[t] n')
    (hlt : n' < n) (horb : ∃ t : ℕ, n' = f^[t] n ∨ n' = g^[t] n)
    (hwin : ¬ ∀ t : ℕ, 1 ≤ t → t ≤ L → n ≤ g^[t] n) : n ≤ 4 ^ L * (n - n' + 1) := by
  classical
  push Not at hwin
  have hex : ∃ t : ℕ, 1 ≤ t ∧ t ≤ L ∧ g^[t] n < n := by
    obtain ⟨t, h1, h2, h3⟩ := hwin; exact ⟨t, h1, h2, h3⟩
  obtain ⟨hk1, hkL, hkdrop⟩ := Nat.find_spec hex
  have hmin : ∀ t : ℕ, 1 ≤ t → t < Nat.find hex → n ≤ g^[t] n := by
    intro t ht1 htk
    by_contra hc
    exact absurd (Nat.find_min' hex ⟨ht1, by omega, lt_of_not_ge hc⟩) (by omega)
  have hP := le_iterate_of_firstDrop hfg hn hn' hlt horb hmin
  have hKn := hK _ hk1 n
  rw [abs_of_neg (by linarith : g^[Nat.find hex] n - n < 0)] at hKn
  have hpow : (4 : ℤ) ^ Nat.find hex ≤ 4 ^ L := pow_le_pow_right₀ (by norm_num) hkL
  have hpos : (0 : ℤ) ≤ 4 ^ Nat.find hex := by positivity
  calc n ≤ |n| := le_abs_self n
    _ ≤ 4 ^ Nat.find hex * (-(g^[Nat.find hex] n - n) + 1) := hKn
    _ ≤ 4 ^ Nat.find hex * (n - n' + 1) := by gcongr; linarith
    _ ≤ 4 ^ L * (n - n' + 1) := by gcongr

/-- **Packing.**  A set of naturals below `X` with pairwise gaps `≥ D ≥ 1` has at most
`X / D + 1` elements. -/
theorem card_le_of_sep {S : Finset ℕ} {X D : ℕ} (hD : 1 ≤ D) (hS : ∀ n ∈ S, n < X)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, a < b → a + D ≤ b) : S.card ≤ X / D + 1 := by
  have h := Finset.card_le_card_of_injOn (fun n => n / D) (t := Finset.range (X / D + 1))
    (fun n hn => by
      simp only [Finset.coe_range, Set.mem_Iio]
      exact Nat.lt_succ_of_le (Nat.div_le_div_right (hS n hn).le)) ?_
  · simpa using h
  · intro a ha b hb hab
    simp only at hab
    have key : ∀ a ∈ S, ∀ b ∈ S, a / D = b / D → ¬ a < b := by
      intro a ha b hb hab hlt
      have h1 := Nat.div_add_mod a D
      have h2 := Nat.div_add_mod b D
      have h3 := Nat.mod_lt a (by omega : D > 0)
      have h3' := Nat.mod_lt b (by omega : D > 0)
      have h4 := hsep a ha b hb hlt
      rw [hab] at h1
      generalize D * (b / D) = c at h1 h2
      omega
    rcases lt_trichotomy a b with h | h | h
    · exact absurd h (key a ha b hb hab)
    · exact h
    · exact absurd h (key b hb a ha hab.symm)

/-- **One orbit.**  `f`-survivors in `[X/M, X)` failing the `g`-window of length `L`, all on one
orbit, number at most `8 M 4^L + 1`. -/
theorem card_orbit_le (hfg : ∀ x, f (g x) = x)
    (hK : ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ x : ℤ, |x| ≤ 4 ^ ℓ * (|g^[ℓ] x - x| + 1)) {L M X : ℕ}
    (hM : 1 ≤ M) (hX : 4 * 4 ^ L ≤ X / M) (S : Finset ℕ)
    (hS : ∀ n ∈ S, X / M ≤ n ∧ n < X ∧ (∀ t : ℕ, 1 ≤ t → (n : ℤ) ≤ f^[t] n) ∧
      ¬ ∀ t : ℕ, 1 ≤ t → t ≤ L → (n : ℤ) ≤ g^[t] n)
    (horb : ∀ a ∈ S, ∀ b ∈ S, ∃ t : ℕ, (a : ℤ) = f^[t] b ∨ (a : ℤ) = g^[t] b) :
    S.card ≤ 8 * M * 4 ^ L + 1 := by
  set P := 4 ^ L with hP
  have hP1 : 1 ≤ P := Nat.one_le_pow _ _ (by norm_num)
  set A := X / M with hA
  set D := A / (2 * P) with hDdef
  have hD : 1 ≤ D := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have h2PD : 2 * P * D ≤ A := by rw [mul_comm]; exact Nat.div_mul_le_self A (2 * P)
  have hsep : ∀ a ∈ S, ∀ b ∈ S, a < b → a + D ≤ b := by
    intro a ha b hb hab
    have hgap := le_four_pow_mul_sub hfg hK (hS b hb).2.2.1 (hS a ha).2.2.1
      (by exact_mod_cast hab) (horb a ha b hb) (hS b hb).2.2.2
    have hbA := (hS b hb).1
    have h1 : ((P : ℕ) : ℤ) * (2 * D) ≤ (P : ℤ) * ((b : ℤ) - a + 1) := by
      have : ((2 * P * D : ℕ) : ℤ) ≤ b := by exact_mod_cast h2PD.trans hbA
      have hPc : ((P : ℕ) : ℤ) = 4 ^ L := by rw [hP]; push_cast; rfl
      push_cast at this
      rw [hPc] at this ⊢
      linarith
    have h2 := le_of_mul_le_mul_left h1 (by positivity)
    omega
  have hcard := card_le_of_sep hD (fun n hn => (hS n hn).2.1) hsep
  have hAD : A < 4 * (P * D) := by
    have := Nat.lt_mul_div_succ A (show 0 < 2 * P by omega)
    rw [← hDdef] at this
    nlinarith
  have hXA : X < M * (A + 1) := Nat.lt_mul_div_succ X (by omega)
  have hXle : X ≤ 8 * M * P * D := by
    have : M * (A + 1) ≤ M * (4 * (P * D)) := Nat.mul_le_mul_left _ hAD
    nlinarith
  have : X / D ≤ 8 * M * P := Nat.div_le_of_le_mul (by rw [mul_comm]; exact hXle)
  omega

/-- Orbit membership in iterate form. -/
theorem exists_iterate_of_mem_amusicalOrbit {x y : ℤ} (h : y ∈ amusicalOrbit x) :
    ∃ t : ℕ, y = amusical^[t] x ∨ y = amusicalInv^[t] x := by
  obtain ⟨j, rfl⟩ := h
  rcases Int.eq_nat_or_neg j with ⟨t, rfl | rfl⟩
  · exact ⟨t, Or.inl (amusicalPerm_pow_nat_apply t x)⟩
  · exact ⟨t, Or.inr (amusicalPerm_pow_neg_nat_apply t x)⟩

open Classical in
/-- **All orbits.**  With finitely many orbits (`r` of them), `f`-survivors in `[X/M, X)` failing
the `g`-window of length `L` number at most `r (8 M 4^L + 1)`. -/
theorem card_le_of_finite (hfg : ∀ x, f (g x) = x)
    (hK : ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ x : ℤ, |x| ≤ 4 ^ ℓ * (|g^[ℓ] x - x| + 1))
    (hbridge : ∀ x y : ℤ, y ∈ amusicalOrbit x → ∃ t : ℕ, y = f^[t] x ∨ y = g^[t] x)
    (hfin : ¬ AmusicalInfinitelyManyOrbits) :
    ∃ r : ℕ, ∀ L M X : ℕ, 1 ≤ M → 4 * 4 ^ L ≤ X / M →
      ((Finset.Ico (X / M) X).filter fun n : ℕ => (∀ t : ℕ, 1 ≤ t → (n : ℤ) ≤ f^[t] n) ∧
        ¬ ∀ t : ℕ, 1 ≤ t → t ≤ L → (n : ℤ) ≤ g^[t] n).card ≤ r * (8 * M * 4 ^ L + 1) := by
  have hfin' := Set.not_infinite.mp hfin
  refine ⟨hfin'.toFinset.card, fun L M X hM hX => ?_⟩
  set S := (Finset.Ico (X / M) X).filter fun n : ℕ => (∀ t : ℕ, 1 ≤ t → (n : ℤ) ≤ f^[t] n) ∧
    ¬ ∀ t : ℕ, 1 ≤ t → t ≤ L → (n : ℤ) ≤ g^[t] n
  have h := Finset.card_le_mul_card_image (f := fun n : ℕ => amusicalOrbit (n : ℤ)) S
    (8 * M * 4 ^ L + 1) (by
      intro O _
      refine card_orbit_le hfg hK hM hX _ (fun n hn => ?_) (fun a ha b hb => ?_)
      · simp only [S, Finset.mem_filter, Finset.mem_Ico] at hn
        exact ⟨hn.1.1.1, hn.1.1.2, hn.1.2.1, hn.1.2.2⟩
      · simp only [Finset.mem_filter] at ha hb
        apply hbridge
        rw [hb.2, ← ha.2]
        exact mem_amusicalOrbit_self _)
  have himg : (S.image fun n : ℕ => amusicalOrbit (n : ℤ)) ⊆ hfin'.toFinset := by
    intro O hO
    simp only [Finset.mem_image] at hO
    obtain ⟨n, _, rfl⟩ := hO
    rw [Set.Finite.mem_toFinset]
    exact ⟨n, by positivity, rfl⟩
  calc S.card ≤ (8 * M * 4 ^ L + 1) * (S.image fun n : ℕ => amusicalOrbit (n : ℤ)).card := h
    _ ≤ (8 * M * 4 ^ L + 1) * hfin'.toFinset.card :=
        Nat.mul_le_mul_left _ (Finset.card_le_card himg)
    _ = hfin'.toFinset.card * (8 * M * 4 ^ L + 1) := mul_comm _ _

open Classical in
/-- **Split.**  Survivors below `X` are `L`-window minima, points below `X/M`, or survivors in
`[X/M, X)` failing the `g`-window. -/
theorem card_survivor_le_split
    (hwin : ∀ (L : ℕ) (n : ℤ), (∀ t : ℕ, 1 ≤ t → n ≤ f^[t] n) →
      (∀ t : ℕ, 1 ≤ t → t ≤ L → n ≤ g^[t] n) → IsWindowMin L n) (L M X : ℕ) :
    ((Finset.range X).filter fun n : ℕ => ∀ t : ℕ, 1 ≤ t → (n : ℤ) ≤ f^[t] n).card ≤
      ((Finset.range X).filter fun n : ℕ => IsWindowMin L n).card + X / M +
      ((Finset.Ico (X / M) X).filter fun n : ℕ => (∀ t : ℕ, 1 ≤ t → (n : ℤ) ≤ f^[t] n) ∧
        ¬ ∀ t : ℕ, 1 ≤ t → t ≤ L → (n : ℤ) ≤ g^[t] n).card := by
  calc _ ≤ (((Finset.range X).filter fun n : ℕ => IsWindowMin L n) ∪ Finset.range (X / M) ∪
        ((Finset.Ico (X / M) X).filter fun n : ℕ => (∀ t : ℕ, 1 ≤ t → (n : ℤ) ≤ f^[t] n) ∧
          ¬ ∀ t : ℕ, 1 ≤ t → t ≤ L → (n : ℤ) ≤ g^[t] n)).card := by
        apply Finset.card_le_card
        intro n hn
        simp only [Finset.mem_filter, Finset.mem_range] at hn
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        by_cases h1 : n < X / M
        · exact Or.inl (Or.inr h1)
        · by_cases h2 : ∀ t : ℕ, 1 ≤ t → t ≤ L → (n : ℤ) ≤ g^[t] n
          · exact Or.inl (Or.inl ⟨hn.1, hwin L n hn.2 h2⟩)
          · exact Or.inr ⟨⟨by omega, hn.1⟩, hn.2, h2⟩
    _ ≤ _ := by
        refine (Finset.card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
        refine (Finset.card_union_le _ _).trans ?_
        simp

open Classical in
/-- **C2, direction-generic.**  With finitely many orbits, `f`-survivors have upper density at
most `δ_L`. -/
theorem density_le_of_finite (hfg : ∀ x, f (g x) = x)
    (hK : ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ x : ℤ, |x| ≤ 4 ^ ℓ * (|g^[ℓ] x - x| + 1))
    (hbridge : ∀ x y : ℤ, y ∈ amusicalOrbit x → ∃ t : ℕ, y = f^[t] x ∨ y = g^[t] x)
    (hwin : ∀ (L : ℕ) (n : ℤ), (∀ t : ℕ, 1 ≤ t → n ≤ f^[t] n) →
      (∀ t : ℕ, 1 ≤ t → t ≤ L → n ≤ g^[t] n) → IsWindowMin L n)
    (hfin : ¬ AmusicalInfinitelyManyOrbits) (L : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in Filter.atTop,
      (((Finset.range X).filter fun n : ℕ => ∀ t : ℕ, 1 ≤ t → (n : ℤ) ≤ f^[t] n).card : ℝ) ≤
        (((fwdSurv L * bwdSurv L : ℚ) : ℝ) + ε) * X := by
  obtain ⟨r, hr⟩ := card_le_of_finite hfg hK hbridge hfin
  set δ : ℝ := ((fwdSurv L * bwdSurv L : ℚ) : ℝ)
  set M : ℕ := ⌈3 / ε⌉₊ + 1 with hMdef
  have hM1 : 1 ≤ M := by omega
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM1
  have hεM : 3 ≤ (M : ℝ) * ε := by
    have h1 : 3 / ε ≤ (M : ℝ) := by
      rw [hMdef]; push_cast; linarith [Nat.le_ceil (3 / ε)]
    exact (div_le_iff₀ hε).mp h1
  set C : ℕ := r * (8 * M * 4 ^ L + 1)
  have hW := (windowMinDensity L).eventually (gt_mem_nhds (show δ < δ + ε / 3 by linarith))
  filter_upwards [hW, Filter.eventually_ge_atTop (4 * 4 ^ L * M),
    Filter.eventually_ge_atTop (⌈3 * (C : ℝ) / ε⌉₊ + 1)] with X hWX hX1 hX2
  have hXpos' : 0 < X := by omega
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hXpos'
  have hsplit := card_survivor_le_split hwin L M X
  have hT := hr L M X hM1 ((Nat.le_div_iff_mul_le (by omega)).mpr hX1)
  have hWle := (div_lt_iff₀ hXpos).mp hWX
  have hXM : ((X / M : ℕ) : ℝ) ≤ ε / 3 * X := by
    refine (Nat.cast_div_le).trans ?_
    rw [div_le_iff₀ hMpos]
    nlinarith
  have hC : 3 * (C : ℝ) < ε * X := by
    have h1 : 3 * (C : ℝ) / ε < X := by
      have := Nat.le_ceil (3 * (C : ℝ) / ε)
      have h2 : ((⌈3 * (C : ℝ) / ε⌉₊ + 1 : ℕ) : ℝ) ≤ X := by exact_mod_cast hX2
      push_cast at h2
      linarith
    have := (div_lt_iff₀ hε).mp h1
    linarith
  have hsplitR : (((Finset.range X).filter fun n : ℕ => ∀ t : ℕ, 1 ≤ t →
      (n : ℤ) ≤ f^[t] n).card : ℝ) ≤
      (((Finset.range X).filter fun n : ℕ => IsWindowMin L n).card : ℝ) + ((X / M : ℕ) : ℝ) +
        (C : ℝ) := by
    have := hsplit.trans (Nat.add_le_add_left hT _)
    exact_mod_cast this
  nlinarith

open Classical in
/-- **C2′, direction-generic.**  `f`-survivors of upper density above `c` imply Klamkin (a). -/
theorem infinitelyManyOrbits_of_density (hfg : ∀ x, f (g x) = x)
    (hK : ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ x : ℤ, |x| ≤ 4 ^ ℓ * (|g^[ℓ] x - x| + 1))
    (hbridge : ∀ x y : ℤ, y ∈ amusicalOrbit x → ∃ t : ℕ, y = f^[t] x ∨ y = g^[t] x)
    (hwin : ∀ (L : ℕ) (n : ℤ), (∀ t : ℕ, 1 ≤ t → n ≤ f^[t] n) →
      (∀ t : ℕ, 1 ≤ t → t ≤ L → n ≤ g^[t] n) → IsWindowMin L n)
    {η : ℝ} (hη : 0 < η)
    (h : ∃ᶠ X : ℕ in Filter.atTop, (minimaConstant + η) * X ≤
      ((Finset.range X).filter fun n : ℕ => ∀ t : ℕ, 1 ≤ t → (n : ℤ) ≤ f^[t] n).card) :
    AmusicalInfinitelyManyOrbits := by
  by_contra hfin
  have hlim : Filter.Tendsto (fun L : ℕ => ((fwdSurv L * bwdSurv L : ℚ) : ℝ)) Filter.atTop
      (nhds minimaConstant) := windowDensityLimit
  have hlt : minimaConstant < minimaConstant + η / 2 := by linarith
  obtain ⟨L, hL⟩ := (hlim.eventually (gt_mem_nhds hlt)).exists
  have hC2 := density_le_of_finite hfg hK hbridge hwin hfin L (show 0 < η / 4 by linarith)
  obtain ⟨X, hX1, hX2, hX3⟩ :=
    (h.and_eventually (hC2.and (Filter.eventually_gt_atTop 0))).exists
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX3
  have : (((fwdSurv L * bwdSurv L : ℚ) : ℝ) + η / 4) * X < (minimaConstant + η) * X :=
    mul_lt_mul_of_pos_right (by linarith) hXpos
  linarith

end CollatzMoonshot.Amusical.Ceiling
