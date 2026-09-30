/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Obstructions.Q1Reentry

/-! A local positive pair on the fixed-offset coefficient ray.  The admitted
edge records six actual `tstep` iterates and the affine branch identities.
It makes no claim that this pair occurs in the original hard-family orbit. -/

namespace CollatzMoonshot.Obstructions.ArithmeticLifts.RestrictedRepair

open CollatzMoonshot.FrontB

def rayA (j w : ℕ) : ℕ := 72 * 3 ^ j * (64 * w) - 5
def rayB (w : ℕ) : ℕ := 64 * w + 1

/-- The inherited relation is `(A + 1) = m * (B - 1) + d`, with `d = -4`. -/
def raySignature (j : ℕ) : ℕ × ℤ := (72 * 3 ^ j, -4)

def carriesSignature (σ : ℕ × ℤ) (a b : ℕ) : Prop :=
  (a : ℤ) + 1 = (σ.1 : ℤ) * ((b : ℤ) - 1) + σ.2

/-- An admitted edge has an actual positive six-step pair, its prescribed
parity-branch affine identities, and both inherited endpoint signatures. -/
def rayEdge (σ τ : ℕ × ℤ) : Prop :=
  ∃ a b : ℕ,
    0 < a ∧ 0 < b ∧ a > b ∧
    64 * tstep^[6] a = 81 * a + 85 ∧
    64 * tstep^[6] b = 27 * b + 37 ∧
    a < tstep^[6] a ∧ tstep^[6] b < b ∧
    σ.2 = -4 ∧ τ.2 = -4 ∧ τ.1 = 3 * σ.1 ∧
    carriesSignature σ a b ∧
    carriesSignature τ (tstep^[6] a) (tstep^[6] b)

/-! ### Local one-step parity helpers -/

private theorem tstep_even_val' {u v : ℕ} (hu : u % 2 = 0) (h : u = 2 * v) :
    tstep u = v := by
  simp only [tstep, hu, if_true]; omega

private theorem tstep_odd_val'' {u v : ℕ} (hu : u % 2 = 1) (h : 3 * u + 1 = 2 * v) :
    tstep u = v := by
  have h2 := two_tstep_odd hu; omega

/-- The six actual steps along the `110110` word, with `K` opaque. -/
private theorem rayA_core {K : ℕ} (hK : 0 < K) :
    tstep^[6] (64 * K - 5) = 81 * K - 5 := by
  have s1 : tstep (64 * K - 5) = 96 * K - 7 := tstep_odd_val'' (by omega) (by omega)
  have s2 : tstep (96 * K - 7) = 144 * K - 10 := tstep_odd_val'' (by omega) (by omega)
  have s3 : tstep (144 * K - 10) = 72 * K - 5 := tstep_even_val' (by omega) (by omega)
  have s4 : tstep (72 * K - 5) = 108 * K - 7 := tstep_odd_val'' (by omega) (by omega)
  have s5 : tstep (108 * K - 7) = 162 * K - 10 := tstep_odd_val'' (by omega) (by omega)
  have s6 : tstep (162 * K - 10) = 81 * K - 5 := tstep_even_val' (by omega) (by omega)
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply,
    id_eq, s1, s2, s3, s4, s5, s6]

/-- The six actual steps along the `101010` word. -/
private theorem rayB_core (w : ℕ) :
    tstep^[6] (64 * w + 1) = 27 * w + 1 := by
  have s1 : tstep (64 * w + 1) = 96 * w + 2 := tstep_odd_val'' (by omega) (by omega)
  have s2 : tstep (96 * w + 2) = 48 * w + 1 := tstep_even_val' (by omega) (by omega)
  have s3 : tstep (48 * w + 1) = 72 * w + 2 := tstep_odd_val'' (by omega) (by omega)
  have s4 : tstep (72 * w + 2) = 36 * w + 1 := tstep_even_val' (by omega) (by omega)
  have s5 : tstep (36 * w + 1) = 54 * w + 2 := tstep_odd_val'' (by omega) (by omega)
  have s6 : tstep (54 * w + 2) = 27 * w + 1 := tstep_even_val' (by omega) (by omega)
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply,
    id_eq, s1, s2, s3, s4, s5, s6]

private theorem rayK_pos (j w : ℕ) (hw : 0 < w) : 0 < 72 * 3 ^ j * w := by
  have := pow_pos (show (0:ℕ) < 3 by norm_num) j
  positivity

private theorem rayA_eq (j w : ℕ) : rayA j w = 64 * (72 * 3 ^ j * w) - 5 := by
  unfold rayA; congr 1; ring

/-! ### Frozen targets -/

/-- The six actual steps of the two positive local vertices. -/
theorem ray_six_steps (j w : ℕ) (hw : 0 < w) :
    tstep^[6] (rayA j w) = 216 * 3 ^ j * (27 * w) - 5 ∧
    tstep^[6] (rayB w) = 27 * w + 1 := by
  refine ⟨?_, rayB_core w⟩
  rw [rayA_eq, rayA_core (rayK_pos j w hw)]
  congr 1; ring

/-- One actual local pair realizes the entire edge, including both affine
branch formulas, strict target growth, and strict auxiliary decrease. -/
theorem ray_edge_witness (j w : ℕ) (hw : 0 < w) :
    0 < rayA j w ∧ 0 < rayB w ∧ rayA j w > rayB w ∧
    64 * tstep^[6] (rayA j w) = 81 * rayA j w + 85 ∧
    64 * tstep^[6] (rayB w) = 27 * rayB w + 37 ∧
    rayA j w < tstep^[6] (rayA j w) ∧
    tstep^[6] (rayB w) < rayB w ∧
    carriesSignature (raySignature j) (rayA j w) (rayB w) ∧
    carriesSignature (raySignature (j + 1))
      (tstep^[6] (rayA j w)) (tstep^[6] (rayB w)) := by
  set K := 72 * 3 ^ j * w with hKdef
  have hK : 0 < K := rayK_pos j w hw
  have hK72 : 72 * w ≤ K := by
    have h1 : (1:ℕ) ≤ 3 ^ j := Nat.one_le_pow _ _ (by norm_num)
    calc 72 * w = 72 * 1 * w := by ring
    _ ≤ 72 * 3 ^ j * w := by
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)
  have hA : rayA j w = 64 * K - 5 := rayA_eq j w
  have hB : rayB w = 64 * w + 1 := rfl
  have hA' : tstep^[6] (rayA j w) = 81 * K - 5 := by
    rw [hA]; exact rayA_core hK
  have hB' : tstep^[6] (rayB w) = 27 * w + 1 := by rw [hB]; exact rayB_core w
  have hAZ : ((rayA j w : ℤ)) = 64 * (K : ℤ) - 5 := by
    rw [hA]; push_cast [Nat.cast_sub (by omega : 5 ≤ 64 * K)]; ring
  have hAZ' : ((tstep^[6] (rayA j w) : ℤ)) = 81 * (K : ℤ) - 5 := by
    rw [hA']; push_cast [Nat.cast_sub (by omega : 5 ≤ 81 * K)]; ring
  have hKZ : (K : ℤ) = 72 * 3 ^ j * (w : ℤ) := by rw [hKdef]; push_cast; ring
  refine ⟨by omega, by omega, by omega, ?_, ?_, by omega, by omega, ?_, ?_⟩
  · rw [hA', hA]; omega
  · rw [hB', hB]; omega
  · simp only [carriesSignature, raySignature, hAZ, hB]
    push_cast
    rw [hKZ]; ring
  · simp only [carriesSignature, raySignature, hAZ', hB']
    push_cast
    rw [hKZ]; ring

/-- Every edge of the coefficient ray is witnessed by an actual positive
local pair.  The witness may differ from one edge to the next. -/
theorem ray_edge_exists (j : ℕ) :
    rayEdge (raySignature j) (raySignature (j + 1)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := ray_edge_witness j 1 (by norm_num)
  refine ⟨rayA j 1, rayB 1, h1, h2, h3, h4, h5, h6, h7, rfl, rfl, ?_, h8, h9⟩
  simp [raySignature, pow_succ]; ring

/-- No rank on the projected signature alone can decrease on every admitted
edge into a well-founded relation. -/
theorem no_uniform_ray_rank {α : Type*} (r : α → α → Prop)
    (hr : WellFounded r) :
    ¬ ∃ rank : (ℕ × ℤ) → α,
      ∀ σ τ : ℕ × ℤ, rayEdge σ τ → r (rank τ) (rank σ) := by
  rintro ⟨rank, hrank⟩
  have hstep : ∀ j : ℕ, r (rank (raySignature (j + 1))) (rank (raySignature j)) :=
    fun j => hrank _ _ (ray_edge_exists j)
  have key : ∀ x : α, ∀ j : ℕ, rank (raySignature j) = x → False := by
    intro x
    induction x using hr.induction with
    | _ x ih =>
      intro j hj
      exact ih (rank (raySignature (j + 1))) (hj ▸ hstep j) (j + 1) rfl
  exact key _ 0 rfl

end CollatzMoonshot.Obstructions.ArithmeticLifts.RestrictedRepair
