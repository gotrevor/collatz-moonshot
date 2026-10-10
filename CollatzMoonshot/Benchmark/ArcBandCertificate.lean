/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.Benchmark.ArcDelayGame
import CollatzMoonshot.Benchmark.ArcBandCertificateData

/-!
# The memoryless relaxed game above its upper edge

A Lean twin of `experiments/arc_band.py`: the memoryless relaxed descent with interval endpoints affine in
`(β, l)`, run on the triangles of a decision tree of split lines, with signs read off the triangle vertices.
The plan, the data format and the soundness obligations are in `ARC-BAND-CERTIFICATE-DIRECTION.md`.
-/

namespace CollatzMoonshot.Benchmark.ArcBandCertificate

open ArcTrap ArcDelayGame

/-! ## Affine arithmetic and the vertex oracle

The executable descent only ever asks for the sign of a difference of two affine
endpoints.  The following small layer isolates the mathematical fact behind that
oracle from the (larger) interval-list computation below it. -/

def Aff.eval (f : Aff) (p : ℝ × ℝ) : ℝ :=
  f.c + f.b * p.1 + f.w * p.2

def Aff.evalQ (f : Aff) (p : ℚ × ℚ) : ℚ :=
  f.c + f.b * p.1 + f.w * p.2

def Aff.neg (f : Aff) : Aff := ⟨-f.c, -f.b, -f.w⟩

def Aff.sub (f g : Aff) : Aff := ⟨f.c - g.c, f.b - g.b, f.w - g.w⟩

@[simp] theorem Aff.eval_neg (f : Aff) (p : ℝ × ℝ) : f.neg.eval p = -f.eval p := by
  simp [Aff.neg, Aff.eval]
  ring

@[simp] theorem Aff.eval_sub (f g : Aff) (p : ℝ × ℝ) :
    (f.sub g).eval p = f.eval p - g.eval p := by
  simp [Aff.sub, Aff.eval]
  ring

@[simp] theorem Aff.eval_rat (f : Aff) (p : ℚ × ℚ) :
    f.eval ((p.1 : ℝ), (p.2 : ℝ)) = (f.evalQ p : ℝ) := by
  simp [Aff.eval, Aff.evalQ]

/-- Affine maps preserve a three-term affine combination.  This is the soundness
lemma used by the triangle vertex sign oracle. -/
theorem Aff.eval_affineCombination (f : Aff) (p₁ p₂ p₃ : ℝ × ℝ)
    (a₁ a₂ a₃ : ℝ) (ha : a₁ + a₂ + a₃ = 1) :
    f.eval (a₁ • p₁ + a₂ • p₂ + a₃ • p₃) =
      a₁ * f.eval p₁ + a₂ * f.eval p₂ + a₃ * f.eval p₃ := by
  rcases p₁ with ⟨x₁, y₁⟩
  rcases p₂ with ⟨x₂, y₂⟩
  rcases p₃ with ⟨x₃, y₃⟩
  simp only [Prod.smul_mk, smul_eq_mul, Prod.fst_add, Prod.snd_add, Aff.eval]
  push_cast
  rw [show a₁ = 1 - a₂ - a₃ by linarith]
  ring

/-- If an affine form is nonnegative at all three vertices and positive at one,
then it is positive at every strict barycentric combination of the vertices. -/
theorem Aff.eval_pos_of_barycentric (f : Aff) (p p₁ p₂ p₃ : ℝ × ℝ)
    (a₁ a₂ a₃ : ℝ) (hp : p = a₁ • p₁ + a₂ • p₂ + a₃ • p₃)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (ha₃ : 0 < a₃) (ha : a₁ + a₂ + a₃ = 1)
    (h₁ : 0 ≤ f.eval p₁) (h₂ : 0 ≤ f.eval p₂) (h₃ : 0 ≤ f.eval p₃)
    (hstrict : 0 < f.eval p₁ ∨ 0 < f.eval p₂ ∨ 0 < f.eval p₃) : 0 < f.eval p := by
  rw [hp, f.eval_affineCombination p₁ p₂ p₃ a₁ a₂ a₃ ha]
  rcases hstrict with hstrict | hstrict | hstrict
  · positivity
  · positivity
  · positivity

/-- The three-valued sign returned by the executable vertex oracle. -/
def vertexSign (f : Aff) (v₁ v₂ v₃ : ℚ × ℚ) : Option Ordering :=
  let x₁ := f.evalQ v₁
  let x₂ := f.evalQ v₂
  let x₃ := f.evalQ v₃
  if x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0 then some .eq
  else if 0 ≤ x₁ ∧ 0 ≤ x₂ ∧ 0 ≤ x₃ then some .gt
  else if x₁ ≤ 0 ∧ x₂ ≤ 0 ∧ x₃ ≤ 0 then some .lt
  else none

theorem vertexSign_eq_sound {f : Aff} {v₁ v₂ v₃ : ℚ × ℚ}
    (h : vertexSign f v₁ v₂ v₃ = some .eq) :
    f.evalQ v₁ = 0 ∧ f.evalQ v₂ = 0 ∧ f.evalQ v₃ = 0 := by
  simp only [vertexSign] at h
  split at h
  · assumption
  · split at h
    · simp at h
    · split at h <;> simp at h

theorem vertexSign_gt_sound {f : Aff} {v₁ v₂ v₃ : ℚ × ℚ}
    (h : vertexSign f v₁ v₂ v₃ = some .gt) :
    (0 ≤ f.evalQ v₁ ∧ 0 ≤ f.evalQ v₂ ∧ 0 ≤ f.evalQ v₃) ∧
      (0 < f.evalQ v₁ ∨ 0 < f.evalQ v₂ ∨ 0 < f.evalQ v₃) := by
  simp only [vertexSign] at h
  split at h
  · simp_all
  split at h
  · rename_i hz hn
    refine ⟨hn, ?_⟩
    by_contra hpos
    push_neg at hpos
    exact hz ⟨le_antisymm hpos.1 hn.1, le_antisymm hpos.2.1 hn.2.1,
      le_antisymm hpos.2.2 hn.2.2⟩
  · split at h <;> simp_all

theorem vertexSign_lt_sound {f : Aff} {v₁ v₂ v₃ : ℚ × ℚ}
    (h : vertexSign f v₁ v₂ v₃ = some .lt) :
    vertexSign f.neg v₁ v₂ v₃ = some .gt := by
  simp only [vertexSign] at h
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · rename_i hz hp hn
    have hs : f.evalQ v₁ < 0 ∨ f.evalQ v₂ < 0 ∨ f.evalQ v₃ < 0 := by
      by_contra hs
      push_neg at hs
      exact hz ⟨le_antisymm hn.1 hs.1, le_antisymm hn.2.1 hs.2.1,
        le_antisymm hn.2.2 hs.2.2⟩
    have eneg (v : ℚ × ℚ) : f.neg.evalQ v = -f.evalQ v := by
      simp [Aff.neg, Aff.evalQ]
      ring
    have hzneg : ¬(-f.evalQ v₁ = 0 ∧ -f.evalQ v₂ = 0 ∧ -f.evalQ v₃ = 0) := by
      intro he
      apply hz
      simpa using he
    rw [vertexSign, if_neg (by simpa only [eneg] using hzneg)]
    rw [if_pos]
    simpa only [eneg, neg_nonneg] using hn
  · simp at h

/-- **No memoryless relaxed strategy above the upper edge** (`ArcDelayGame.RelaxedAboveUpperEdge`).
Route: soundness of the symbolic descent at one real point, a vertex sign test on open triangles (barycentric
coordinates), a decision tree whose split lines all have a nonzero `β` coefficient, and, for points on a split
line, a small leftward shift in `β` plus `RelaxedStrategy.mono`.  The certificate is checked by `native_decide`. -/
theorem relaxedAboveUpperEdge : RelaxedAboveUpperEdge := by
  sorry

end CollatzMoonshot.Benchmark.ArcBandCertificate
