/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Benchmark.ArcTrap
import CollatzMoonshot.Benchmark.ArcFattening

/-!
# Rounded-operator inclusion for the relaxed arc game (physical coordinates)

The lattice solver `experiments/arc_trap_k.py solve_vw` keeps, at each step, only the grid cells
(mesh `1/N`) lying wholly inside the set of starts that have a nondegenerate interval of legal
moves.  This file states that operator in physical coordinates (as in `ArcFattening`, where the
grid commutes with integer translation) and proves the inclusion: a strategy that is robust (every
start within `ρ` of a core `C` has a whole interval of moves landing within `σ` of `C`, with
`σ + 1/N ≤ ρ`) survives rounding, so the solver's greatest fixed point contains its rounded
thickening.  Together with `ArcFattening`'s robust fattening (Astra) and the residue/physical
bridges, lattice emptiness on a width net would exclude every winner, thin or fat.

What is NOT in Lean: that `solve_vw`'s computed step contains `stepOpen` (a fact about the Python
interval code, which drops degenerate intervals: hence the nondegenerate move interval here).
-/

namespace CollatzMoonshot.Benchmark.ArcSolverInclusion

/-- The `1/N` grid cells wholly inside `S` (a point belongs to its half-open cell, so a cell ending at an
integer never leaks its endpoint into the next residue). -/
def roundIn (N : ℕ) (S : Set ℝ) : Set ℝ :=
  {x | ∃ i : ℤ, (i : ℝ) / N ≤ x ∧ x < ((i : ℝ) + 1) / N ∧ Set.Icc ((i : ℝ) / N) (((i : ℝ) + 1) / N) ⊆ S}

/-- Legal move `v` from start `x` (window width `l`, arc `[s, s + t]` mod 1). -/
def Legal (s t l x v : ℝ) : Prop :=
  x ≤ v ∧ v + 2 * l / 3 ≤ x + l ∧ ∃ j : ℤ, (j : ℝ) + s ≤ v ∧ v + 2 * l / 3 ≤ j + s + t

/-- Starts with a NONDEGENERATE interval of legal moves whose two successors (`h = 2^(k-1)` for
memory `k`) lie in `P`: the solver's interval arithmetic sees exactly such starts. -/
def stepOpen (s t l h : ℝ) (P : Set ℝ) : Set ℝ :=
  {x | ∃ v μ : ℝ, 0 < μ ∧ ∀ q : ℝ, |q| ≤ μ →
    Legal s t l x (v + q) ∧ ∀ b : ℕ, b < 2 → 3 * (v + q) / 2 + b * h ∈ P}

/-- Closed `ρ`-thickening. -/
def thick (ρ : ℝ) (C : Set ℝ) : Set ℝ := {y | ∃ x ∈ C, |y - x| ≤ ρ}

theorem roundIn_mono {N : ℕ} {S S' : Set ℝ} (h : S ⊆ S') : roundIn N S ⊆ roundIn N S' := by
  rintro x ⟨i, h1, h2, h3⟩
  exact ⟨i, h1, h2, h3.trans h⟩

theorem stepOpen_mono {s t l h : ℝ} {P P' : Set ℝ} (hP : P ⊆ P') :
    stepOpen s t l h P ⊆ stepOpen s t l h P' := by
  rintro x ⟨v, μ, hμ, hv⟩
  exact ⟨v, μ, hμ, fun q hq => ⟨(hv q hq).1, fun b hb => hP ((hv q hq).2 b hb)⟩⟩

/-- Every point within `σ` of `C` lies in a grid cell inside the `ρ`-thickening, once
`σ + 1/N ≤ ρ`. -/
theorem thick_subset_roundIn {N : ℕ} (hN : 0 < N) {σ ρ : ℝ} (hσ : σ + 1 / N ≤ ρ) (C : Set ℝ) :
    thick σ C ⊆ roundIn N (thick ρ C) := by
  rintro y ⟨x, hx, hxy⟩
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨⌊y * N⌋, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ hN']; exact Int.floor_le _
  · rw [lt_div_iff₀ hN']; exact Int.lt_floor_add_one _
  · intro z ⟨hz1, hz2⟩
    refine ⟨x, hx, ?_⟩
    have hy1 : (⌊y * N⌋ : ℝ) / N ≤ y := by rw [div_le_iff₀ hN']; exact Int.floor_le _
    have hy2 : y ≤ ((⌊y * N⌋ : ℝ) + 1) / N := by
      rw [le_div_iff₀ hN']; exact (Int.lt_floor_add_one _).le
    have hw : ((⌊y * N⌋ : ℝ) + 1) / N - (⌊y * N⌋ : ℝ) / N = 1 / N := by ring
    have hzy : |z - y| ≤ 1 / N := by rw [abs_le]; constructor <;> linarith
    calc |z - x| = |(z - y) + (y - x)| := by ring_nf
      _ ≤ |z - y| + |y - x| := abs_add_le _ _
      _ ≤ ρ := by linarith

/-- **Rounded-operator inclusion.**  If every start within `ρ` of the core `C` has a nondegenerate
interval of legal moves whose successors land within `σ` of `C`, and `σ + 1/N ≤ ρ`, then the rounded
thickening `T = roundIn N (thick ρ C)` is a post-fixed point of the rounded step:
`T ⊆ roundIn N (stepOpen T)`.  So the greatest fixed point of `P ↦ P ∩ roundIn N (stepOpen P)`
(what `solve_vw` iterates down to, from the full set) contains `T`. -/
theorem roundIn_post_fixed {N : ℕ} (hN : 0 < N) {s t l h σ ρ : ℝ} {C : Set ℝ}
    (hσ : σ + 1 / N ≤ ρ) (hR : thick ρ C ⊆ stepOpen s t l h (thick σ C)) :
    roundIn N (thick ρ C) ⊆ roundIn N (stepOpen s t l h (roundIn N (thick ρ C))) :=
  roundIn_mono (hR.trans (stepOpen_mono (thick_subset_roundIn hN hσ C)))

/-- **Fattened strategies survive the rounded solver** (composition with Astra's
`ArcFattening.LiftedStrategy.robust_fatten`).  Shift the old starts by `-e/2` to get the core `C`;
its `e/12`-thickening is `fattenCore e P`.  With grid `1/N ≤ e/48`, the rounded fattened strategy is a
post-fixed point of the rounded step on the widened arc and width `l + e`, so the solver's greatest
fixed point there contains it; it is nonempty whenever `P` is. -/
theorem rounded_fattened_post_fixed {s t l h e : ℝ} {N : ℕ} {P : Set ℝ}
    (hP : ArcFattening.LiftedStrategy s t l h P) (he : 0 < e) (hN : 0 < N) (hNe : 1 / N ≤ e / 48) :
    let C := (fun x => x - e / 2) '' P
    roundIn N (thick (e / 12) C) ⊆
        roundIn N (stepOpen (s - e / 2) (t + e) (l + e) h (roundIn N (thick (e / 12) C))) ∧
      (P.Nonempty → (roundIn N (thick (e / 12) C)).Nonempty) := by
  intro C
  refine ⟨roundIn_post_fixed hN (σ := e / 16) (by linarith) ?_, ?_⟩
  · rintro y ⟨c, ⟨x, hx, rfl⟩, hy⟩
    have hyF : y ∈ ArcFattening.fattenCore e P :=
      ⟨x, hx, y - (x - e / 2), hy, by ring⟩
    obtain ⟨v, hv⟩ := hP.robust_fatten he.le y hyF
    refine ⟨v, e / 24, by positivity, fun q hq => ?_⟩
    obtain ⟨h1, h2, hj, hb⟩ := hv q hq
    refine ⟨⟨h1, h2, hj⟩, fun b hb' => ?_⟩
    obtain ⟨x', hx', hd⟩ := hb b hb'
    exact ⟨x' - e / 2, ⟨x', hx', rfl⟩, hd⟩
  · rintro ⟨x, hx⟩
    exact ⟨x - e / 2, thick_subset_roundIn hN (σ := 0) (by linarith) C
      ⟨x - e / 2, ⟨x, hx, rfl⟩, by simp⟩⟩

/-! ### From the physical rounded post-fixed point to the solver's residue form

Chain (Astra's simplification, 2026-10-10: only the forward bridge `KToLiftedBridge` is needed):
`T ⊆ roundIn N (stepOpen T)` (physical, proved above for fattened strategies) gives
`residualize T ⊆ roundInRes N (residualize (stepOpen T))` (A, grid commutes with integers)
`⊆ roundInRes N (resStepOpen (residualize T))` (B, the carry permutation of the two lifts), and the
code computes a superset of `roundInRes ∘ resStepOpen` (C, trusted; enumeration ranges proved below),
so monotone descent from the full sets keeps `residualize T`, and an empty solver contradicts it. -/

/-- Residue-form open step, with `KRelaxedStrategy`'s own successor formula. -/
def resStepOpen (s t l : ℝ) (k : ℕ) (P : ℕ → Set ℝ) (r : ℕ) : Set ℝ :=
  {a | ∃ u μ : ℝ, 0 < μ ∧ ∀ q : ℝ, |q| ≤ μ →
    a ≤ u + q ∧ u + q + 2 * l / 3 ≤ a + l ∧
    (∃ j : ℤ, (j : ℝ) + s ≤ u + q ∧ u + q + 2 * l / 3 ≤ j + s + t) ∧
    ∀ b < 2, Int.fract (3 * (u + q) / 2 + ((r % 2 : ℕ) : ℝ) / 2) ∈
      P (((3 * r - r % 2) / 2 + (⌊3 * (u + q) / 2 + ((r % 2 : ℕ) : ℝ) / 2⌋).toNat) % 2 ^ (k - 1) +
        b * 2 ^ (k - 1))}

/-- Half-open grid cells of `[0, 1)` wholly inside `A` (residue coordinates).  The solver's closed
intervals contain these, so it over-includes, the safe direction for emptiness. -/
def roundInRes (N : ℕ) (A : Set ℝ) : Set ℝ :=
  {a | ∃ i : ℕ, i < N ∧ (i : ℝ) / N ≤ a ∧ a < ((i : ℝ) + 1) / N ∧
    Set.Ico ((i : ℝ) / N) (((i : ℝ) + 1) / N) ⊆ A}

/-- (A) Projection commutes with rounding, as an inclusion.  With half-open cells a physical cell lies in
one unit interval `[m, m + 1)` and projects onto one residue cell.  (The closed-cell version was false:
a cell ending at `m + 1` projects its endpoint to fraction `0` of the next residue.) -/
theorem residualize_roundIn_subset (k N : ℕ) (hN : 0 < N) (S : Set ℝ) (r : ℕ) :
    ArcFattening.residualize k (roundIn N S) r ⊆ roundInRes N (ArcFattening.residualize k S r) := by
  rintro a ⟨x, ⟨i, hi1, hi2, hiS⟩, hres, rfl⟩
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set m := ⌊x⌋ with hm
  have hm1 : (m : ℝ) ≤ x := Int.floor_le x
  have hm2 : x < m + 1 := Int.lt_floor_add_one x
  -- the cell index relative to the unit interval [m, m + 1)
  have hA : (i : ℝ) < (m + 1) * N := by
    have := (div_le_iff₀ hN').1 hi1; nlinarith
  have hB : (m : ℝ) * N < i + 1 := by
    have := (lt_div_iff₀ hN').1 hi2; nlinarith
  have hA' : i < (m + 1) * N := by exact_mod_cast hA
  have hB' : m * N < i + 1 := by exact_mod_cast hB
  have hA2 : i < m * N + N := by rw [add_mul, one_mul] at hA'; exact hA'
  refine ⟨(i - m * N).toNat, ?_, ?_, ?_, ?_⟩
  · omega
  · have hc : (((i - m * N).toNat : ℕ) : ℝ) = (i : ℝ) - m * N := by
      have : ((i - m * N).toNat : ℤ) = i - m * N := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    rw [hc, Int.fract, div_le_iff₀ hN']
    have := (div_le_iff₀ hN').1 hi1; nlinarith
  · have hc : (((i - m * N).toNat : ℕ) : ℝ) = (i : ℝ) - m * N := by
      have : ((i - m * N).toNat : ℤ) = i - m * N := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    rw [hc, Int.fract, lt_div_iff₀ hN']
    have := (lt_div_iff₀ hN').1 hi2; nlinarith
  · have hc : (((i - m * N).toNat : ℕ) : ℝ) = (i : ℝ) - m * N := by
      have : ((i - m * N).toNat : ℤ) = i - m * N := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    intro a' ⟨ha1, ha2⟩
    rw [hc] at ha1 ha2
    have hlt1 : a' < 1 := by
      have h' : (i : ℝ) - m * N + 1 ≤ N := by
        have : i - m * N + 1 ≤ (N : ℤ) := by omega
        exact_mod_cast this
      have : ((i : ℝ) - m * N + 1) / N ≤ 1 := by rw [div_le_one hN']; exact h'
      linarith
    have hge0 : 0 ≤ a' := by
      have : (0 : ℝ) ≤ (i - m * N) / N := by
        apply div_nonneg _ hN'.le
        have : (0 : ℤ) ≤ i - m * N := by omega
        exact_mod_cast this
      linarith
    refine ⟨m + a', hiS ⟨?_, ?_⟩, ?_, ?_⟩
    · have := (div_le_iff₀ hN').1 ha1; rw [div_le_iff₀ hN']; nlinarith
    · have := (lt_div_iff₀ hN').1 ha2; rw [le_div_iff₀ hN']; nlinarith
    · have hfl : ⌊(m : ℝ) + a'⌋ = m := by
        rw [Int.floor_eq_iff]; constructor <;> linarith
      simp only [ArcFattening.residue] at hres ⊢
      rw [hfl]; exact hres
    · rw [Int.fract, show ⌊(m : ℝ) + a'⌋ = m by rw [Int.floor_eq_iff]; constructor <;> linarith]
      ring

/-- (B) The projected physical open step lies inside the residue-form open step.  Confidence 92%: the
same carry arithmetic as `ArcFattening.integer_carry_shift_mod` (the two physical children are the two
lifts of the base, in some order). -/
theorem residualize_stepOpen_subset {s t l : ℝ} {k : ℕ} (hk : 1 ≤ k) (T : Set ℝ) (r : ℕ) :
    ArcFattening.residualize k (stepOpen s t l (2 ^ (k - 1)) T) r ⊆
      resStepOpen s t l k (ArcFattening.residualize k T) r := by
  rintro a ⟨x, ⟨v, μ, hμ, hv⟩, hres, rfl⟩
  set m := ⌊x⌋ with hm
  have hxm : Int.fract x = x - m := rfl
  refine ⟨v - m, μ, hμ, fun q hq => ?_⟩
  obtain ⟨⟨h1, h2, j, hj1, hj2⟩, hb⟩ := hv q hq
  set w := v - m + q with hw
  refine ⟨by rw [hxm]; linarith, by rw [hxm]; linarith, ⟨j - m, by push_cast; linarith,
    by push_cast; linarith⟩, fun b' hb' => ?_⟩
  -- integer bookkeeping
  set hI : ℤ := 2 ^ (k - 1) with hhI
  have hIpos : 0 < hI := by positivity
  have h2k : (2 : ℤ) ^ k = 2 * hI := by
    rw [hhI, ← pow_succ']; congr 1; omega
  have hr : (r : ℤ) = m % (2 * hI) := by
    have : r = (⌊x⌋ % (2 ^ k : ℤ)).toNat := hres.symm
    rw [this, Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity)), ← h2k]
  have hpar : (r : ℤ) % 2 = m % 2 := by
    rw [hr]; exact Int.emod_emod_of_dvd m ⟨hI, by ring⟩
  have hparR : (((r % 2 : ℕ) : ℝ)) = (((m % 2 : ℤ)) : ℝ) := by
    have h' : ((r % 2 : ℕ) : ℤ) = m % 2 := by push_cast; exact hpar
    rw [show ((r % 2 : ℕ) : ℝ) = (((r % 2 : ℕ) : ℤ) : ℝ) from (Int.cast_natCast _).symm, h']
  set c := 3 * w / 2 + ((r % 2 : ℕ) : ℝ) / 2 with hc
  have hc0 : 0 ≤ c := by
    have : (0 : ℝ) ≤ ((r % 2 : ℕ) : ℝ) := by positivity
    have : 0 ≤ w := by rw [hw]; linarith [Int.floor_le x]
    rw [hc]; positivity
  have hJ0 : 0 ≤ ⌊c⌋ := Int.floor_nonneg.mpr hc0
  set A := (3 * m - m % 2) / 2 + ⌊c⌋ with hA
  -- the target index, as an integer
  have hidx : ((((3 * r - r % 2) / 2 + (⌊c⌋).toNat) % 2 ^ (k - 1) + b' * 2 ^ (k - 1) : ℕ) : ℤ) =
      ((3 * (r : ℤ) - (r : ℤ) % 2) / 2 + ⌊c⌋) % hI + b' * hI := by
    have hsub : r % 2 ≤ 3 * r := by omega
    push_cast [Nat.cast_sub hsub, Int.toNat_of_nonneg hJ0]
    rfl
  -- pick the physical child that carries this lift
  have hlifts := ArcFattening.children_are_lifts m ⌊c⌋ hI hIpos
  simp only at hlifts
  have hmem : ((3 * (r : ℤ) - (r : ℤ) % 2) / 2 + ⌊c⌋) % hI + b' * hI ∈
      ({A % (2 * hI), (A + hI) % (2 * hI)} : Set ℤ) := by
    rw [hA, hlifts, ← hr]
    interval_cases b' <;> simp
  obtain ⟨b, hb2, hbeq⟩ : ∃ b : ℕ, b < 2 ∧ (A + b * hI) % (2 * hI) =
      ((3 * (r : ℤ) - (r : ℤ) % 2) / 2 + ⌊c⌋) % hI + b' * hI := by
    rcases hmem with h | h
    · exact ⟨0, by norm_num, by simpa using h.symm⟩
    · exact ⟨1, by norm_num, by simpa using h.symm⟩
  have hyT := hb b hb2
  refine ⟨3 * (v + q) / 2 + b * 2 ^ (k - 1), hyT, ?_, ?_⟩
  · -- residue of the chosen child
    have hvq : v + q = (m : ℝ) + w := by rw [hw]; ring
    have hfl : ⌊3 * (v + q) / 2 + (b : ℝ) * 2 ^ (k - 1)⌋ = A + b * hI := by
      have : (b : ℝ) * 2 ^ (k - 1) = ((b * hI : ℤ) : ℝ) := by rw [hhI]; push_cast; ring
      rw [this, Int.floor_add_intCast, hvq, ArcFattening.physical_child_floor, hA, hc, hparR]
      ring
    simp only [ArcFattening.residue]
    rw [hfl, h2k, hbeq]
    have := hidx
    omega
  · have hvq : v + q = (m : ℝ) + w := by rw [hw]; ring
    have : (b : ℝ) * 2 ^ (k - 1) = ((b * hI : ℤ) : ℝ) := by rw [hhI]; push_cast; ring
    rw [this, Int.fract_add_intCast, hvq, ArcFattening.physical_child_fract, hc, hparR]

theorem roundInRes_mono {N : ℕ} {A A' : Set ℝ} (h : A ⊆ A') : roundInRes N A ⊆ roundInRes N A' := by
  rintro a ⟨i, hi, h1, h2, h3⟩
  exact ⟨i, hi, h1, h2, h3.trans h⟩

theorem resStepOpen_mono {s t l : ℝ} {k : ℕ} {P P' : ℕ → Set ℝ} (h : ∀ r, P r ⊆ P' r) (r : ℕ) :
    resStepOpen s t l k P r ⊆ resStepOpen s t l k P' r := by
  rintro a ⟨u, μ, hμ, hu⟩
  exact ⟨u, μ, hμ, fun q hq => ⟨(hu q hq).1, (hu q hq).2.1, (hu q hq).2.2.1,
    fun b hb => h _ ((hu q hq).2.2.2 b hb)⟩⟩

theorem residualize_mono {k : ℕ} {S S' : Set ℝ} (h : S ⊆ S') (r : ℕ) :
    ArcFattening.residualize k S r ⊆ ArcFattening.residualize k S' r := by
  rintro a ⟨x, hx, h1, h2⟩
  exact ⟨x, h hx, h1, h2⟩

/-- A physical rounded post-fixed point projects to a residue-form rounded post-fixed point
(from (A) and (B)). -/
theorem residualize_post_fixed {s t l : ℝ} {k N : ℕ} (hk : 1 ≤ k) (hN : 0 < N) {T : Set ℝ}
    (hT : T ⊆ roundIn N (stepOpen s t l (2 ^ (k - 1)) T)) (r : ℕ) :
    ArcFattening.residualize k T r ⊆
      roundInRes N (resStepOpen s t l k (ArcFattening.residualize k T) r) :=
  (residualize_mono hT r).trans ((residualize_roundIn_subset k N hN _ r).trans
    (roundInRes_mono (residualize_stepOpen_subset hk T r)))

/-- The solver as an abstract operator: start from `[0, 1]` at every residue and intersect with `C`. -/
def descend (C : (ℕ → Set ℝ) → ℕ → Set ℝ) : ℕ → ℕ → Set ℝ
  | 0 => fun _ => Set.Icc 0 1
  | n + 1 => fun r => descend C n r ∩ C (descend C n) r

/-- **Descent keeps every residue-form rounded post-fixed point**, for any code operator `C` that contains
the rounded open step.  So the only trusted claim left about `solve_vw` / `arc_sweep` is that their step is
such a `C` (hypothesis (c)); then a nonempty `Q` forces a nonempty solver output, and an empty solver
contradicts it. -/
theorem descend_keeps {s t l : ℝ} {k N : ℕ} {C : (ℕ → Set ℝ) → ℕ → Set ℝ}
    (hC : ∀ P r, roundInRes N (resStepOpen s t l k P r) ⊆ C P r) {Q : ℕ → Set ℝ}
    (hQ0 : ∀ r, Q r ⊆ Set.Icc 0 1) (hQ : ∀ r, Q r ⊆ roundInRes N (resStepOpen s t l k Q r)) :
    ∀ n r, Q r ⊆ descend C n r := by
  intro n
  induction n with
  | zero => exact hQ0
  | succ n ih =>
    intro r a ha
    exact ⟨ih r ha, hC _ r (roundInRes_mono (resStepOpen_mono ih r) (hQ r ha))⟩

/-- **Enumeration ranges** behind (C): on a sub-arc of `[0, 1]` with `l ≤ 3/2`, every legal move from a start
in `[0, 1]` uses arc lift `j ∈ {-1, 0, 1}` and floor `⌊c⌋ ∈ {0, 1, 2}`.  The Python enumerates `j = -1 … 4`
and `J = 0 … 4`, the Rust `j = -2 … 5` and `J = 0 … 5`, so neither misses a move. -/
theorem enum_ranges {s t l a u d : ℝ} {j : ℤ} (hs : 0 ≤ s) (hst : s + t ≤ 1) (hl0 : 0 ≤ l)
    (hl : l ≤ 3 / 2) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hu : a ≤ u) (hu' : u ≤ a + l / 3) (hd0 : 0 ≤ d)
    (hd : d ≤ 1 / 2) (hj1 : (j : ℝ) + s ≤ u) (hj2 : u + 2 * l / 3 ≤ j + s + t) :
    -1 ≤ j ∧ j ≤ 1 ∧ 0 ≤ ⌊3 * u / 2 + d⌋ ∧ ⌊3 * u / 2 + d⌋ ≤ 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : (-1 : ℝ) ≤ j := by linarith
    exact_mod_cast this
  · have : (j : ℝ) < 2 := by linarith
    have : j < 2 := by exact_mod_cast this
    omega
  · exact Int.floor_nonneg.mpr (by linarith)
  · exact Int.floor_le_iff.mpr (by push_cast; linarith)

/-- **Width net.**  A winner of width `l` fattened by any `e ∈ [e0/2, e0]` has width in
`[l + e0/2, l + e0]`, and a mesh of step `δ ≤ e0/2` hits that interval. -/
theorem width_net {l e0 δ : ℝ} (hl : 0 ≤ l) (he0 : 0 < e0) (hδ : 0 < δ) (hδe : δ ≤ e0 / 2) :
    ∃ i : ℕ, l + e0 / 2 ≤ i * δ ∧ (i : ℝ) * δ ≤ l + e0 := by
  refine ⟨⌈(l + e0 / 2) / δ⌉₊, ?_, ?_⟩
  · have := Nat.le_ceil ((l + e0 / 2) / δ)
    rwa [div_le_iff₀ hδ] at this
  · have := Nat.ceil_lt_add_one (show 0 ≤ (l + e0 / 2) / δ by positivity)
    have h2 : (⌈(l + e0 / 2) / δ⌉₊ : ℝ) * δ < ((l + e0 / 2) / δ + 1) * δ :=
      mul_lt_mul_of_pos_right this hδ
    rw [add_mul, div_mul_cancel₀ _ hδ.ne'] at h2
    linarith

/-- **No `k`-memory relaxed strategy, `k = 1, …, 6`, holds `[β, 1 - β]` at `β = 7/57 + 1/1000`, at any width.**
Confidence 85%.  Proved pieces: robust fattening (`ArcFattening.LiftedStrategy.robust_fatten`, Astra),
its composition with rounding (`rounded_fattened_post_fixed`), and the width net (`width_net`).  Open:
(b) the residue/physical bridges (`ArcFattening`, Astra) and (c) `solve_vw`'s computed step containing
`stepOpen` (a fact about the Python: audited line by line against `vw_targets` / `vw_good_u` / `vw_aset` /
`round_in`, and cross-checked by an independent brute-force open-move search, `brute_open_move`: 140 open
starts on random lattice strategies at `k = 2, 3`, all in the solver's step; a version demanding only ONE
child finds 100 the solver rightly rejects, so the check has teeth.  Test
`test_solver_step_contains_open_moves`).  Given those, it reduces to a finite computation, which came out
empty (2026-10-10, `arc_trap_k.py width-sweep 3 7057/57000 1/1000 1/2500 17`): widened arc
`β' = β - e0/2 = 7/57 + 1/2000`, `e0 = 1/1000`, all 2825 widths `i/2500 ≤ 3t'/2`, grid `N = 2^17`
(`e0 N / 96 ≈ 1.4`), `k = 1, …, 6`, empty in BOTH the Python solver and the independent Rust one
(`experiments/arc_sweep_rs`, written from `stepOpen` / `roundIn`, not from the Python); Rust alone is also
empty at `k = 7, 8`.  Positive control: at `N = 2^15` the solver finds winners at
`7/57 - 1/10000` for `k = 0, 1, 2`.  Unlike `finiteMemoryRelaxedValue_ge_013`, no liveness hypothesis. -/
theorem no_kRelaxedStrategy_7_57_plus {k : ℕ} (hk : 1 ≤ k) (hk3 : k ≤ 6) (l : ℝ) (P : ℕ → Set ℝ)
    (hne : ∃ r < 2 ^ k, (P r).Nonempty) :
    ¬ ArcTrap.KRelaxedStrategy (7 / 57 + 1 / 1000) (1 - 2 * (7 / 57 + 1 / 1000)) l k P := by
  sorry

/-- **Ten times closer: no 1-, 2- or 3-memory relaxed strategy at `β = 7/57 + 1/10000`, any width.**
Confidence 80% (one instrument at this `β`).  Same hypotheses as `no_kRelaxedStrategy_7_57_plus`.
Computation (2026-10-10, Rust only: `arc_sweep sweep 1 3 70057/570000 1/10000 1/20001 20`): widened arc
`β' = 7/57 + 1/20000`, all 22629 widths `i/20001 ≤ 3t'/2` (mesh below `e0/2`), grid `N = 2^20`
(`e0 N ≈ 105 ≥ 96`), empty for `k = 1, 2, 3`.  Positive control on the same grid: winners at
`7/57 - 1/100000` (`k = 1` at widths `0.1231, 0.1234`; `k = 3` at all of `0.1225 … 0.1234`). -/
theorem no_kRelaxedStrategy_7_57_plus_tenth {k : ℕ} (hk : 1 ≤ k) (hk3 : k ≤ 3) (l : ℝ)
    (P : ℕ → Set ℝ) (hne : ∃ r < 2 ^ k, (P r).Nonempty) :
    ¬ ArcTrap.KRelaxedStrategy (7 / 57 + 1 / 10000) (1 - 2 * (7 / 57 + 1 / 10000)) l k P := by
  sorry

end CollatzMoonshot.Benchmark.ArcSolverInclusion
