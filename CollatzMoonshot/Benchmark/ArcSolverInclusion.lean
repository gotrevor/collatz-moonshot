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

/-- The `1/N` grid cells wholly inside `S`. -/
def roundIn (N : ℕ) (S : Set ℝ) : Set ℝ :=
  {x | ∃ i : ℤ, (i : ℝ) / N ≤ x ∧ x ≤ ((i : ℝ) + 1) / N ∧ Set.Icc ((i : ℝ) / N) (((i : ℝ) + 1) / N) ⊆ S}

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
  · rw [le_div_iff₀ hN']; exact (Int.lt_floor_add_one _).le
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

/-- **No 1-, 2- or 3-memory relaxed strategy holds `[β, 1 - β]` at `β = 7/57 + 1/1000`, at any width.**
Confidence 85%.  Proved pieces: robust fattening (`ArcFattening.LiftedStrategy.robust_fatten`, Astra),
its composition with rounding (`rounded_fattened_post_fixed`), and the width net (`width_net`).  Open:
(b) the residue/physical bridges (`ArcFattening`, Astra) and (c) `solve_vw`'s computed step containing
`stepOpen` (a fact about the Python).  Given those, it reduces to a finite computation, which came out
empty (2026-10-10, `arc_trap_k.py width-sweep 3 7057/57000 1/1000 1/2500 17`): widened arc
`β' = β - e0/2 = 7/57 + 1/2000`, `e0 = 1/1000`, all 2825 widths `i/2500 ≤ 3t'/2`, grid `N = 2^17`
(`e0 N / 48 ≈ 2.7`), `k = 1, 2, 3`.  Positive control: at `N = 2^15` the solver finds winners at
`7/57 - 1/10000` for `k = 0, 1, 2`.  Unlike `finiteMemoryRelaxedValue_ge_013`, no liveness hypothesis. -/
theorem no_kRelaxedStrategy_7_57_plus {k : ℕ} (hk : 1 ≤ k) (hk3 : k ≤ 3) (l : ℝ) (P : ℕ → Set ℝ)
    (hne : ∃ r < 2 ^ k, (P r).Nonempty) :
    ¬ ArcTrap.KRelaxedStrategy (7 / 57 + 1 / 1000) (1 - 2 * (7 / 57 + 1 / 1000)) l k P := by
  sorry

end CollatzMoonshot.Benchmark.ArcSolverInclusion
