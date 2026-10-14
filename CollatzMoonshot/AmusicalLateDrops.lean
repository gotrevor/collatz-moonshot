/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.AmusicalGlobal
import CollatzMoonshot.AmusicalSpitzer

/-!
# Late drops: the typicality wall, pinned to one count

Proposition S (`infinitelyManyOrbits_of_survival`) reduces Klamkin (a) to survivor lower
densities.  The 2026-10-13 "survival" agent sharpened this.  The wall is now a single count: the
*late droppers*, points that survive an `L`-window in one direction but are undercut later.

* **Counting form (Proposition S′, `card_windowMin_le`).**
  `#WindowMin_L(X) ≤ #Min(X) + #Late_L(X)`.
  A window minimum that is not an orbit minimum is undercut beyond depth `L` forward or backward.
* **Theorem LD (`infinitelyManyOrbits_of_lateDrops`).**  If, for some depth `L` and infinitely many
  `X`, the late droppers below `X` number at most `(f_L b_L − η) X`, Klamkin (a) holds.  At the
  random walk's late-drop rates this fires from `L = 23`, and late drops at any constant multiple
  `K` of the walk's rate still fire at a larger depth.  A one-sided estimate does not suffice:
  perfect forward typicality still needs backward survivors at `≥ 79%` of their heuristic density.
* **Corollary LD′ (`lateDrops_dense`).**  With finitely many orbits, late drops have density
  `≥ f_L b_L` at every depth.
* **Constants.**  The survivor limits are `p_f = 0.210136239317` and `p_b = 0.236891833789`
  (`tendsto_fwdSurv`, `tendsto_bwdSurv`).  Their product is `c`, and both equal
  `1 / E[first strict ascent]`.  The two directions share the Chernoff rate `ρ = 0.985597`
  through the tilt identity (`walk_mgf_tilt`).  Integer counts on `[16, 2³¹)` match them to
  `5 · 10⁻⁷`.
* **Calibration (`amusicalOrbit_infinite_of_strictFwd`).**  A strict forward survivor has an
  infinite orbit.  So a positive lower density of strict survivors would already exhibit an
  aperiodic orbit, which is open.

What separates `U` from the rewired `τ` (§14): `τ` has `U`'s exact window statistics but maximal
late drops.  Two properties of `U` matter.  Window independence of the two directions is proved;
typicality beyond the residue horizon `≈ log₃ X` is open.

Paper proofs: agent report `survival.md` §1–§2, summarized in
`RESEARCH-2026-10-13-amusical-single-chain.md` §20.  Constants re-derived independently
(`scripts/amusical/survival/consts_ren.py`, 12 digits, product `= c`).  Treadmill target: close
every `sorry` here.
-/

namespace CollatzMoonshot.Amusical

/-- `n` survives the forward `L`-window. -/
def IsFwdWin (L : ℕ) (n : ℤ) : Prop :=
  ∀ t : ℕ, 1 ≤ t → t ≤ L → n ≤ amusical^[t] n

/-- `n` survives the backward `L`-window. -/
def IsBwdWin (L : ℕ) (n : ℤ) : Prop :=
  ∀ t : ℕ, 1 ≤ t → t ≤ L → n ≤ amusicalInv^[t] n

open Classical in
/-- Points below `X` that survive an `L`-window in one direction but are undercut later. -/
noncomputable def lateDropCount (L X : ℕ) : ℕ :=
  ((Finset.range X).filter fun n : ℕ => IsFwdWin L n ∧ ¬ FwdSurvivor n).card +
    ((Finset.range X).filter fun n : ℕ => IsBwdWin L n ∧ ¬ BwdSurvivor n).card

open Classical in
/-- **Proved (Proposition S′).**  Window minima are orbit-survivors or late droppers. -/
theorem card_windowMin_le (L X : ℕ) :
    ((Finset.range X).filter fun n : ℕ => IsWindowMin L n).card ≤
      ((Finset.range X).filter fun n : ℕ => FwdSurvivor n ∧ BwdSurvivor n).card +
        lateDropCount L X := by
  unfold lateDropCount
  refine (Finset.card_le_card ?_).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_left (Finset.card_union_le _ _) _))
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_union] at hn ⊢
  obtain ⟨hX, hw⟩ := hn
  have hf : IsFwdWin L n := fun t h1 h2 => (hw t h1 h2).1
  have hb : IsBwdWin L n := fun t h1 h2 => (hw t h1 h2).2
  by_cases hF : FwdSurvivor (n : ℤ)
  · by_cases hB : BwdSurvivor (n : ℤ)
    · exact Or.inl ⟨hX, hF, hB⟩
    · exact Or.inr (Or.inr ⟨hX, hb, hB⟩)
  · exact Or.inr (Or.inl ⟨hX, hf, hF⟩)

/-- **Target (Theorem LD, fixed depth).**  Few late drops along a sequence give Klamkin (a).
Paper proof: by `card_windowMin_le` and `windowMinDensity L`, along the given sequence the
survivors-both-ways below `X` number at least `(η/2) X` for large `X`.  These are orbit minima
(`IsOrbitMin`, via `amusical_iterate_eq_perm_pow`).  A set with infinitely many `X` where it
has `≥ (η/2) X` members below `X` is infinite; conclude by
`amusicalInfinitelyManyOrbits_of_minima`. -/
theorem infinitelyManyOrbits_of_lateDrops (L : ℕ) {η : ℝ} (hη : 0 < η)
    (h : ∃ᶠ X : ℕ in Filter.atTop,
      (lateDropCount L X : ℝ) ≤ (((fwdSurv L * bwdSurv L : ℚ) : ℝ) - η) * X) :
    AmusicalInfinitelyManyOrbits := by
  classical
  let δ : ℝ := ((fwdSurv L * bwdSurv L : ℚ) : ℝ)
  let W : ℕ → ℕ := fun X =>
    ((Finset.range X).filter fun n : ℕ => IsWindowMin L n).card
  let S : ℕ → ℕ := fun X =>
    ((Finset.range X).filter fun n : ℕ => FwdSurvivor n ∧ BwdSurvivor n).card
  have hW : ∀ᶠ X : ℕ in Filter.atTop, (δ - η / 2) * X < (W X : ℝ) := by
    have hevent := (windowMinDensity L).eventually
      (lt_mem_nhds (sub_lt_self δ (half_pos hη)))
    filter_upwards [hevent, Filter.eventually_ge_atTop 1] with X hX hX1
    have hXpos : (0 : ℝ) < X := by exact_mod_cast hX1
    rw [show W X = ((Finset.range X).filter fun n : ℕ => IsWindowMin L n).card by rfl]
    rwa [lt_div_iff₀ hXpos] at hX
  have hfreq : ∃ᶠ X : ℕ in Filter.atTop, (η / 2) * X < (S X : ℝ) := by
    refine (h.and_eventually hW).mono ?_
    intro X hX
    have hcard := card_windowMin_le L X
    change W X ≤ S X + lateDropCount L X at hcard
    have hcard' : (W X : ℝ) ≤ S X + lateDropCount L X := by exact_mod_cast hcard
    dsimp only [δ] at hX
    nlinarith
  apply amusicalInfinitelyManyOrbits_of_minima
  intro hfinite
  let N := hfinite.toFinset.card
  have hbound : ∀ X, S X ≤ N := by
    intro X
    refine Finset.card_le_card_of_injOn (fun n : ℕ => (n : ℤ)) ?_ ?_
    · intro n hn
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hn
      refine hfinite.mem_toFinset.mpr ⟨Int.natCast_nonneg n, ?_⟩
      intro y hy
      obtain ⟨j, rfl⟩ := hy
      cases j with
      | ofNat t =>
          change (n : ℤ) ≤ (amusicalPerm ^ (t : ℤ)) n
          rw [← amusical_iterate_eq_perm_pow]
          cases t with
          | zero => simp
          | succ t => exact hn.2.1 (t + 1) (by omega)
      | negSucc t =>
          change (n : ℤ) ≤ (amusicalPerm ^ (Int.negSucc t)) n
          rw [Int.negSucc_eq, show -((t : ℤ) + 1) = -((t + 1 : ℕ) : ℤ) by norm_num, ←
            amusicalInv_iterate_eq_perm_pow]
          exact hn.2.2 (t + 1) (by omega)
    · intro a _ b _ hab
      exact Int.ofNat_inj.mp hab
  have hlarge := hfreq.and_eventually
    (Filter.eventually_ge_atTop (Nat.ceil (2 * (N : ℝ) / η) + 1))
  obtain ⟨X, hSX, hX⟩ := hlarge.exists
  have hNX : (N : ℝ) < η / 2 * X := by
    have hceil := Nat.le_ceil (2 * (N : ℝ) / η)
    have hXR : 2 * (N : ℝ) / η < X := by
      have : ((Nat.ceil (2 * (N : ℝ) / η) + 1 : ℕ) : ℝ) ≤ X := by
        exact_mod_cast hX
      push_cast at this
      linarith
    rw [div_lt_iff₀ hη] at hXR
    nlinarith
  have hSN : (S X : ℝ) ≤ N := by exact_mod_cast hbound X
  linarith

/-- **Open (the reopen condition for the late-drop wall).**  At some depth `L`, infinitely often,
late drops fall short of the window-minimum density `f_L b_L` by a fixed margin. -/
def AmusicalLateDropsSparse : Prop :=
  ∃ (L : ℕ) (η : ℝ), 0 < η ∧ ∃ᶠ X : ℕ in Filter.atTop,
    (lateDropCount L X : ℝ) ≤ (((fwdSurv L * bwdSurv L : ℚ) : ℝ) - η) * X

/-- **Proved (modulo Theorem LD).**  Sparse late drops give Klamkin (a). -/
theorem infinitelyManyOrbits_of_lateDropsSparse (h : AmusicalLateDropsSparse) :
    AmusicalInfinitelyManyOrbits := by
  obtain ⟨L, η, hη, hX⟩ := h
  exact infinitelyManyOrbits_of_lateDrops L hη hX

/-- **Target (Corollary LD′).**  With finitely many orbits, late drops are dense at every depth.
Paper proof: the contrapositive of `infinitelyManyOrbits_of_lateDrops`. -/
theorem lateDrops_dense (hfin : ¬ AmusicalInfinitelyManyOrbits) (L : ℕ) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ X : ℕ in Filter.atTop,
      (((fwdSurv L * bwdSurv L : ℚ) : ℝ) - ε) * X ≤ (lateDropCount L X : ℝ) := by
  by_contra hnot
  apply hfin
  apply infinitelyManyOrbits_of_lateDrops L hε
  have hfreq : ∃ᶠ X : ℕ in Filter.atTop,
      (lateDropCount L X : ℝ) < (((fwdSurv L * bwdSurv L : ℚ) : ℝ) - ε) * X := by
    simpa only [Filter.not_eventually, not_le] using hnot
  exact hfreq.mono fun _ hX => hX.le

/-- **Target (calibration).**  A strict forward survivor has an infinite orbit: a periodic
point returns to itself, so it is not strictly undercut-free. -/
theorem amusicalOrbit_infinite_of_strictFwd {n : ℤ}
    (h : ∀ t : ℕ, 1 ≤ t → n < amusical^[t] n) : (amusicalOrbit n).Infinite := by
  have hinj : Function.Injective (fun t : ℕ => amusical^[t] n) := by
    intro i j hij
    wlog hijle : i ≤ j generalizing i j
    · exact (this hij.symm (Nat.le_of_not_ge hijle)).symm
    obtain rfl | hijlt := hijle.eq_or_lt
    · rfl
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hijlt
      change amusical^[i] n = amusical^[i + k + 1] n at hij
      rw [show i + k + 1 = i + (k + 1) by omega, Function.iterate_add_apply] at hij
      have heq := (amusical_injective.iterate i) hij
      exact absurd heq (h (k + 1) (by omega)).ne
  refine (Set.infinite_range_of_injective hinj).mono ?_
  rintro _ ⟨t, rfl⟩
  exact ⟨(t : ℤ), (amusical_iterate_eq_perm_pow t n).symm⟩

/-- **Target (tilt duality).**  The backward Chernoff transform at `θ` equals the forward one at
`1 − θ`, so both directions share the rate `ρ = 0.985597`.  Paper proof:
`(1/2)(2/3)^{1−θ} = (1/3)(3/2)^θ` and `(1/2)(4/3)^{1−θ} = (2/3)(3/4)^θ`. -/
theorem walk_mgf_tilt (θ : ℝ) :
    (1 / 3) * (3 / 2 : ℝ) ^ θ + (2 / 3) * (3 / 4 : ℝ) ^ θ =
      (1 / 2) * (2 / 3 : ℝ) ^ (1 - θ) + (1 / 2) * (4 / 3 : ℝ) ^ (1 - θ) := by
  rw [Real.rpow_sub (by positivity), Real.rpow_sub (by positivity), Real.rpow_one,
    Real.rpow_one]
  have h₁ : (2 / 3 : ℝ) ^ θ * (3 / 2 : ℝ) ^ θ = 1 := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    norm_num
  have h₂ : (4 / 3 : ℝ) ^ θ * (3 / 4 : ℝ) ^ θ = 1 := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    norm_num
  have hp₁ : 0 < (2 / 3 : ℝ) ^ θ := Real.rpow_pos_of_pos (by positivity) _
  have hp₂ : 0 < (4 / 3 : ℝ) ^ θ := Real.rpow_pos_of_pos (by positivity) _
  have heq₁ : (1 / 2 : ℝ) * ((2 / 3) / (2 / 3) ^ θ) =
      (1 / 3) * (3 / 2) ^ θ := by
    field_simp [ne_of_gt hp₁]
    nlinarith
  have heq₂ : (1 / 2 : ℝ) * ((4 / 3) / (4 / 3) ^ θ) =
      (2 / 3) * (3 / 4) ^ θ := by
    field_simp [ne_of_gt hp₂]
    nlinarith
  rw [heq₁, heq₂]

end CollatzMoonshot.Amusical
