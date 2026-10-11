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

/-! ## The symbolic interval descent

The certificate computation below is a direct Lean transcription of
`experiments/arc_band.py`.  Comparisons are deliberately partial: a triangle
oracle must certify one sign on all three vertices, or the whole computation
fails.  This makes the soundness theorem independent of any unverified choice
made by the executable checker. -/

def Aff.add (f g : Aff) : Aff := ⟨f.c + g.c, f.b + g.b, f.w + g.w⟩

def Aff.scale (q : ℚ) (f : Aff) : Aff := ⟨q * f.c, q * f.b, q * f.w⟩

def Aff.const (q : ℚ) : Aff := ⟨q, 0, 0⟩

def betaAff : Aff := ⟨0, 1, 0⟩

def widthAff : Aff := ⟨0, 0, 1⟩

@[simp] theorem Aff.eval_add (f g : Aff) (p : ℝ × ℝ) :
    (f.add g).eval p = f.eval p + g.eval p := by
  simp [Aff.add, Aff.eval]
  ring

@[simp] theorem Aff.eval_scale (q : ℚ) (f : Aff) (p : ℝ × ℝ) :
    (f.scale q).eval p = q * f.eval p := by
  simp [Aff.scale, Aff.eval]
  ring

@[simp] theorem Aff.eval_const (q : ℚ) (p : ℝ × ℝ) :
    (Aff.const q).eval p = q := by
  simp [Aff.const, Aff.eval]

@[simp] theorem eval_betaAff (p : ℝ × ℝ) : betaAff.eval p = p.1 := by
  simp [betaAff, Aff.eval]

@[simp] theorem eval_widthAff (p : ℝ × ℝ) : widthAff.eval p = p.2 := by
  simp [widthAff, Aff.eval]

abbrev SInterval := Aff × Aff

/-- Ask the sign oracle whether `x ≤ y`. -/
def affineLE (sign : Aff → Option Ordering) (x y : Aff) : Option Bool :=
  match sign (y.sub x) with
  | some .eq | some .gt => some true
  | some .lt => some false
  | none => none

/-- Drop symbolically empty intervals. -/
def keepNonempty (sign : Aff → Option Ordering) : List SInterval → Option (List SInterval)
  | [] => some []
  | x :: xs => do
      let keep ← affineLE sign x.1 x.2
      let ys ← keepNonempty sign xs
      pure (if keep then x :: ys else ys)

/-- Insert an interval into a list ordered by its left endpoint. -/
def insertByLeft (sign : Aff → Option Ordering) (x : SInterval) :
    List SInterval → Option (List SInterval)
  | [] => some [x]
  | y :: ys => do
      let before ← affineLE sign x.1 y.1
      if before then
        pure (x :: y :: ys)
      else
        pure (y :: (← insertByLeft sign x ys))

/-- Insertion sort with all comparisons routed through the triangle oracle. -/
def sortByLeft (sign : Aff → Option Ordering) : List SInterval → Option (List SInterval)
  | [] => some []
  | x :: xs => do
      let ys ← sortByLeft sign xs
      insertByLeft sign x ys

/-- Merge a sorted list of closed intervals. -/
def mergeFrom (sign : Aff → Option Ordering) (cur : SInterval) :
    List SInterval → Option (List SInterval)
  | [] => some [cur]
  | x :: xs => do
      let overlaps ← affineLE sign x.1 cur.2
      if overlaps then
        let startsAfter ← affineLE sign cur.1 x.1
        let grows ← affineLE sign cur.2 x.2
        mergeFrom sign (if startsAfter then cur.1 else x.1,
          if grows then x.2 else cur.2) xs
      else
        pure (cur :: (← mergeFrom sign x xs))

def mergeSorted (sign : Aff → Option Ordering) :
    List SInterval → Option (List SInterval)
  | [] => some []
  | x :: xs => mergeFrom sign x xs

/-- Sort and merge a list of closed affine intervals, dropping empty ones. -/
def normalize (sign : Aff → Option Ordering) (xs : List SInterval) :
    Option (List SInterval) := do
  let ys ← keepNonempty sign xs
  let ys ← sortByLeft sign ys
  mergeSorted sign ys

def maxAff (sign : Aff → Option Ordering) (x y : Aff) : Option Aff := do
  let h ← affineLE sign x y
  pure (if h then y else x)

def minAff (sign : Aff → Option Ordering) (x y : Aff) : Option Aff := do
  let h ← affineLE sign x y
  pure (if h then x else y)

def intersectPair (sign : Aff → Option Ordering) (x y : SInterval) :
    Option (List SInterval) := do
  let lo ← maxAff sign x.1 y.1
  let hi ← minAff sign x.2 y.2
  let nonempty ← affineLE sign lo hi
  pure (if nonempty then [(lo, hi)] else [])

def intersectionsWith (sign : Aff → Option Ordering) (x : SInterval) :
    List SInterval → Option (List SInterval)
  | [] => some []
  | y :: ys => do
      let z ← intersectPair sign x y
      pure (z ++ (← intersectionsWith sign x ys))

def rawIntersections (sign : Aff → Option Ordering) (ys : List SInterval) :
    List SInterval → Option (List SInterval)
  | [] => some []
  | x :: xs => do
      let z ← intersectionsWith sign x ys
      pure (z ++ (← rawIntersections sign ys xs))

def intersect (sign : Aff → Option Ordering) (xs ys : List SInterval) :
    Option (List SInterval) := do
  let zs ← rawIntersections sign ys xs
  normalize sign zs

def gate : List SInterval :=
  let top := (Aff.const 1).sub (betaAff.add (widthAff.scale (2 / 3)))
  [(betaAff, top), (betaAff.add (Aff.const 1), top.add (Aff.const 1))]

def preimages (d : ℚ) (P : List SInterval) : List SInterval :=
  P.flatMap fun x =>
    [0, 1, 2].map fun j =>
      ((x.1.add (Aff.const (j - d))).scale (2 / 3),
        (x.2.add (Aff.const (j - d))).scale (2 / 3))

def minkowski (P : List SInterval) : List SInterval :=
  P.map fun x => (x.1.sub (widthAff.scale (1 / 3)), x.2)

def parityStep (sign : Aff → Option Ordering) (P res : List SInterval) (d : ℚ) :
    Option (List SInterval) := do
  let pre ← normalize sign (preimages d P)
  let inside ← intersect sign pre gate
  let starts ← normalize sign (minkowski inside)
  intersect sign res starts

/-- One complete symbolic descent step, for `d = 0` and `d = 1/2`. -/
def symbolicStep (sign : Aff → Option Ordering) (P : List SInterval) :
    Option (List SInterval) := do
  let P₀ ← parityStep sign P P 0
  parityStep sign P P₀ (1 / 2)

def descend (sign : Aff → Option Ordering) : ℕ → List SInterval → Option (List SInterval)
  | 0, P => some P
  | n + 1, P => do
      let Q ← symbolicStep sign P
      descend sign n Q

def initial : List SInterval := [(Aff.const 0, Aff.const 1)]

def leafEmpties (v₁ v₂ v₃ : ℚ × ℚ) (depth : ℕ) : Bool :=
  descend (fun f => vertexSign f v₁ v₂ v₃) depth initial = some []

def leavesEmpty : CTree → Bool
  | .leaf v₁ v₂ v₃ depth => leafEmpties v₁ v₂ v₃ depth
  | .node _ pos neg => leavesEmpty pos && leavesEmpty neg

/-! ## Pointwise soundness of the computation -/

/-- Every successful answer of a partial sign oracle has its stated meaning at
the real parameter point `p`. -/
def SignSoundAt (sign : Aff → Option Ordering) (p : ℝ × ℝ) : Prop :=
  ∀ f,
    (sign f = some .eq → f.eval p = 0) ∧
    (sign f = some .gt → 0 < f.eval p) ∧
    (sign f = some .lt → f.eval p < 0)

def InIntervals (p : ℝ × ℝ) (x : ℝ) (P : List SInterval) : Prop :=
  ∃ I ∈ P, I.1.eval p ≤ x ∧ x ≤ I.2.eval p

theorem affineLE_true {sign : Aff → Option Ordering} {p : ℝ × ℝ}
    (hsound : SignSoundAt sign p) {x y : Aff}
    (h : affineLE sign x y = some true) : x.eval p ≤ y.eval p := by
  rcases hsound (y.sub x) with ⟨heq, hgt, hlt⟩
  rcases hsign : sign (y.sub x) with _ | o
  · simp [affineLE, hsign] at h
  · cases o with
    | lt => simp [affineLE, hsign] at h
    | eq =>
        have hz := heq hsign
        rw [Aff.eval_sub] at hz
        linarith
    | gt =>
        have hz := hgt hsign
        rw [Aff.eval_sub] at hz
        linarith

theorem affineLE_false {sign : Aff → Option Ordering} {p : ℝ × ℝ}
    (hsound : SignSoundAt sign p) {x y : Aff}
    (h : affineLE sign x y = some false) : y.eval p < x.eval p := by
  rcases hsound (y.sub x) with ⟨heq, hgt, hlt⟩
  rcases hsign : sign (y.sub x) with _ | o
  · simp [affineLE, hsign] at h
  · cases o with
    | lt =>
        have hz := hlt hsign
        rw [Aff.eval_sub] at hz
        linarith
    | eq => simp [affineLE, hsign] at h
    | gt => simp [affineLE, hsign] at h

theorem keepNonempty_sound {sign : Aff → Option Ordering} {p : ℝ × ℝ}
    (hsound : SignSoundAt sign p) {P Q : List SInterval}
    (hPQ : keepNonempty sign P = some Q) {x : ℝ}
    (hx : InIntervals p x P) : InIntervals p x Q := by
  induction P generalizing Q with
  | nil => simp [InIntervals] at hx
  | cons I P ih =>
      rcases hc : affineLE sign I.1 I.2 with _ | keep
      · simp [keepNonempty, hc] at hPQ
      · rcases hr : keepNonempty sign P with _ | R
        · simp [keepNonempty, hc, hr] at hPQ
        · cases keep with
          | false =>
              simp [keepNonempty, hc, hr] at hPQ
              subst Q
              rcases hx with ⟨J, hJ, hJx⟩
              rw [List.mem_cons] at hJ
              rcases hJ with rfl | hJ
              · have hempty := affineLE_false hsound hc
                linarith
              · exact ih hr ⟨J, hJ, hJx⟩
          | true =>
              simp [keepNonempty, hc, hr] at hPQ
              subst Q
              rcases hx with ⟨J, hJ, hJx⟩
              rw [List.mem_cons] at hJ
              rcases hJ with rfl | hJ
              · exact ⟨J, by simp, hJx⟩
              · obtain ⟨K, hK, hKx⟩ := ih hr ⟨J, hJ, hJx⟩
                exact ⟨K, by simp [hK], hKx⟩

theorem insertByLeft_perm {sign : Aff → Option Ordering} {I : SInterval}
    {P Q : List SInterval} (hPQ : insertByLeft sign I P = some Q) :
    Q.Perm (I :: P) := by
  induction P generalizing Q with
  | nil =>
      simp [insertByLeft] at hPQ
      subst Q
      exact List.Perm.refl _
  | cons J P ih =>
      rcases hc : affineLE sign I.1 J.1 with _ | before
      · simp [insertByLeft, hc] at hPQ
      · cases before with
        | true =>
            simp [insertByLeft, hc] at hPQ
            subst Q
            exact List.Perm.refl _
        | false =>
            rcases hr : insertByLeft sign I P with _ | R
            · simp [insertByLeft, hc, hr] at hPQ
            · simp [insertByLeft, hc, hr] at hPQ
              subst Q
              exact (List.Perm.cons J (ih hr)).trans (List.Perm.swap I J P)

theorem sortByLeft_perm {sign : Aff → Option Ordering} {P Q : List SInterval}
    (hPQ : sortByLeft sign P = some Q) : Q.Perm P := by
  induction P generalizing Q with
  | nil =>
      simp [sortByLeft] at hPQ
      subst Q
      exact List.Perm.refl _
  | cons I P ih =>
      rcases hr : sortByLeft sign P with _ | R
      · simp [sortByLeft, hr] at hPQ
      · have hins : Q.Perm (I :: R) := insertByLeft_perm (by simpa [sortByLeft, hr] using hPQ)
        exact hins.trans (List.Perm.cons I (ih hr))

theorem sortByLeft_sound {sign : Aff → Option Ordering} {p : ℝ × ℝ}
    {P Q : List SInterval} (hPQ : sortByLeft sign P = some Q) {x : ℝ}
    (hx : InIntervals p x P) : InIntervals p x Q := by
  rcases hx with ⟨I, hI, hIx⟩
  exact ⟨I, (sortByLeft_perm hPQ).mem_iff.mpr hI, hIx⟩

theorem chooseLower_sound {sign : Aff → Option Ordering} {p : ℝ × ℝ}
    (hsound : SignSoundAt sign p) {a b : Aff} {pick : Bool}
    (h : affineLE sign a b = some pick) :
    (if pick then a else b).eval p ≤ a.eval p ∧
      (if pick then a else b).eval p ≤ b.eval p := by
  cases pick with
  | false =>
      have hba := (affineLE_false hsound h).le
      simpa using And.intro hba (le_refl (b.eval p))
  | true =>
      have hab := affineLE_true hsound h
      simpa using And.intro (le_refl (a.eval p)) hab

theorem chooseUpper_sound {sign : Aff → Option Ordering} {p : ℝ × ℝ}
    (hsound : SignSoundAt sign p) {a b : Aff} {pick : Bool}
    (h : affineLE sign a b = some pick) :
    a.eval p ≤ (if pick then b else a).eval p ∧
      b.eval p ≤ (if pick then b else a).eval p := by
  cases pick with
  | false =>
      have hba := (affineLE_false hsound h).le
      simpa using And.intro (le_refl (a.eval p)) hba
  | true =>
      have hab := affineLE_true hsound h
      simpa using And.intro hab (le_refl (b.eval p))

theorem mergeFrom_sound {sign : Aff → Option Ordering} {p : ℝ × ℝ}
    (hsound : SignSoundAt sign p) {cur : SInterval} {P Q : List SInterval}
    (hPQ : mergeFrom sign cur P = some Q) {x : ℝ}
    (hx : (cur.1.eval p ≤ x ∧ x ≤ cur.2.eval p) ∨ InIntervals p x P) :
    InIntervals p x Q := by
  induction P generalizing cur Q with
  | nil =>
      simp [mergeFrom] at hPQ
      subst Q
      rcases hx with hx | hx
      · exact ⟨cur, by simp, hx⟩
      · simp [InIntervals] at hx
  | cons I P ih =>
      rcases hover : affineLE sign I.1 cur.2 with _ | overlaps
      · simp [mergeFrom, hover] at hPQ
      · cases overlaps with
        | false =>
            rcases hr : mergeFrom sign I P with _ | R
            · simp [mergeFrom, hover, hr] at hPQ
            · simp [mergeFrom, hover, hr] at hPQ
              subst Q
              rcases hx with hcur | htail
              · exact ⟨cur, by simp, hcur⟩
              · rcases htail with ⟨J, hJ, hJx⟩
                rw [List.mem_cons] at hJ
                rcases hJ with rfl | hJ
                · obtain ⟨K, hK, hKx⟩ := ih hr (Or.inl hJx)
                  exact ⟨K, by simp [hK], hKx⟩
                · obtain ⟨K, hK, hKx⟩ := ih hr (Or.inr ⟨J, hJ, hJx⟩)
                  exact ⟨K, by simp [hK], hKx⟩
        | true =>
            rcases hstart : affineLE sign cur.1 I.1 with _ | startsAfter
            · simp [mergeFrom, hover, hstart] at hPQ
            · rcases hgrow : affineLE sign cur.2 I.2 with _ | grows
              · simp [mergeFrom, hover, hstart, hgrow] at hPQ
              · let next : SInterval :=
                  (if startsAfter then cur.1 else I.1, if grows then I.2 else cur.2)
                have hlo := chooseLower_sound hsound hstart
                have hhi := chooseUpper_sound hsound hgrow
                have hnext :
                    (next.1.eval p ≤ x ∧ x ≤ next.2.eval p) ∨ InIntervals p x P := by
                  rcases hx with hcur | htail
                  · left
                    exact ⟨hlo.1.trans hcur.1, hcur.2.trans hhi.1⟩
                  · rcases htail with ⟨J, hJ, hJx⟩
                    rw [List.mem_cons] at hJ
                    rcases hJ with rfl | hJ
                    · left
                      exact ⟨hlo.2.trans hJx.1, hJx.2.trans hhi.2⟩
                    · exact Or.inr ⟨J, hJ, hJx⟩
                exact ih (cur := next)
                  (by simpa [mergeFrom, hover, hstart, hgrow, next] using hPQ) hnext

theorem mergeSorted_sound {sign : Aff → Option Ordering} {p : ℝ × ℝ}
    (hsound : SignSoundAt sign p) {P Q : List SInterval}
    (hPQ : mergeSorted sign P = some Q) {x : ℝ}
    (hx : InIntervals p x P) : InIntervals p x Q := by
  cases P with
  | nil => simp [InIntervals] at hx
  | cons I P =>
      rcases hx with ⟨J, hJ, hJx⟩
      rw [List.mem_cons] at hJ
      apply mergeFrom_sound hsound (by simpa [mergeSorted] using hPQ)
      rcases hJ with rfl | hJ
      · exact Or.inl hJx
      · exact Or.inr ⟨J, hJ, hJx⟩

theorem normalize_sound {sign : Aff → Option Ordering} {p : ℝ × ℝ}
    (hsound : SignSoundAt sign p) {P Q : List SInterval}
    (hPQ : normalize sign P = some Q) {x : ℝ}
    (hx : InIntervals p x P) : InIntervals p x Q := by
  rcases hkeep : keepNonempty sign P with _ | P₁
  · simp [normalize, hkeep] at hPQ
  · rcases hsort : sortByLeft sign P₁ with _ | P₂
    · simp [normalize, hkeep, hsort] at hPQ
    · exact mergeSorted_sound hsound (by simpa [normalize, hkeep, hsort] using hPQ)
        (sortByLeft_sound hsort (keepNonempty_sound hsound hkeep hx))

theorem maxAff_sound {sign : Aff → Option Ordering} {p : ℝ × ℝ}
    (hsound : SignSoundAt sign p) {a b c : Aff} (h : maxAff sign a b = some c) :
    a.eval p ≤ c.eval p ∧ b.eval p ≤ c.eval p := by
  rcases hc : affineLE sign a b with _ | pick
  · simp [maxAff, hc] at h
  · have hb := chooseUpper_sound hsound hc
    simp [maxAff, hc] at h
    subst c
    exact hb

theorem minAff_sound {sign : Aff → Option Ordering} {p : ℝ × ℝ}
    (hsound : SignSoundAt sign p) {a b c : Aff} (h : minAff sign a b = some c) :
    c.eval p ≤ a.eval p ∧ c.eval p ≤ b.eval p := by
  rcases hc : affineLE sign a b with _ | pick
  · simp [minAff, hc] at h
  · have hb := chooseLower_sound hsound hc
    simp [minAff, hc] at h
    subst c
    exact hb

theorem maxAff_le {sign : Aff → Option Ordering} {p : ℝ × ℝ}
    {a b c : Aff} (h : maxAff sign a b = some c) {x : ℝ}
    (ha : a.eval p ≤ x) (hb : b.eval p ≤ x) : c.eval p ≤ x := by
  rcases hc : affineLE sign a b with _ | pick
  · simp [maxAff, hc] at h
  · simp [maxAff, hc] at h
    subst c
    cases pick <;> simp_all

theorem le_minAff {sign : Aff → Option Ordering} {p : ℝ × ℝ}
    {a b c : Aff} (h : minAff sign a b = some c) {x : ℝ}
    (ha : x ≤ a.eval p) (hb : x ≤ b.eval p) : x ≤ c.eval p := by
  rcases hc : affineLE sign a b with _ | pick
  · simp [minAff, hc] at h
  · simp [minAff, hc] at h
    subst c
    cases pick <;> simp_all

theorem intersectPair_sound {sign : Aff → Option Ordering} {p : ℝ × ℝ}
    (hsound : SignSoundAt sign p) {I J : SInterval} {R : List SInterval}
    (hR : intersectPair sign I J = some R) {x : ℝ}
    (hI : I.1.eval p ≤ x ∧ x ≤ I.2.eval p)
    (hJ : J.1.eval p ≤ x ∧ x ≤ J.2.eval p) : InIntervals p x R := by
  rcases hlo : maxAff sign I.1 J.1 with _ | lo
  · simp [intersectPair, hlo] at hR
  · rcases hhi : minAff sign I.2 J.2 with _ | hi
    · simp [intersectPair, hlo, hhi] at hR
    · rcases hne : affineLE sign lo hi with _ | nonempty
      · simp [intersectPair, hlo, hhi, hne] at hR
      · have hxlo : lo.eval p ≤ x := maxAff_le hlo hI.1 hJ.1
        have hxhi : x ≤ hi.eval p := le_minAff hhi hI.2 hJ.2
        cases nonempty with
        | false =>
            have hempty := affineLE_false hsound hne
            exfalso
            linarith
        | true =>
            simp [intersectPair, hlo, hhi, hne] at hR
            subst R
            exact ⟨(lo, hi), by simp, hxlo, hxhi⟩

theorem intersectionsWith_sound {sign : Aff → Option Ordering} {p : ℝ × ℝ}
    (hsound : SignSoundAt sign p) {I : SInterval} {P Q : List SInterval}
    (hPQ : intersectionsWith sign I P = some Q) {x : ℝ}
    (hI : I.1.eval p ≤ x ∧ x ≤ I.2.eval p)
    (hx : InIntervals p x P) : InIntervals p x Q := by
  induction P generalizing Q with
  | nil => simp [InIntervals] at hx
  | cons J P ih =>
      rcases hhead : intersectPair sign I J with _ | A
      · simp [intersectionsWith, hhead] at hPQ
      · rcases htail : intersectionsWith sign I P with _ | B
        · simp [intersectionsWith, hhead, htail] at hPQ
        · simp [intersectionsWith, hhead, htail] at hPQ
          subst Q
          rcases hx with ⟨K, hK, hKx⟩
          rw [List.mem_cons] at hK
          rcases hK with rfl | hK
          · obtain ⟨L, hL, hLx⟩ := intersectPair_sound hsound hhead hI hKx
            exact ⟨L, by simp [hL], hLx⟩
          · obtain ⟨L, hL, hLx⟩ := ih htail ⟨K, hK, hKx⟩
            exact ⟨L, by simp [hL], hLx⟩

theorem rawIntersections_sound {sign : Aff → Option Ordering} {p : ℝ × ℝ}
    (hsound : SignSoundAt sign p) {P R Q : List SInterval}
    (hQ : rawIntersections sign R P = some Q) {x : ℝ}
    (hxP : InIntervals p x P) (hxR : InIntervals p x R) : InIntervals p x Q := by
  induction P generalizing Q with
  | nil => simp [InIntervals] at hxP
  | cons I P ih =>
      rcases hhead : intersectionsWith sign I R with _ | A
      · simp [rawIntersections, hhead] at hQ
      · rcases htail : rawIntersections sign R P with _ | B
        · simp [rawIntersections, hhead, htail] at hQ
        · simp [rawIntersections, hhead, htail] at hQ
          subst Q
          rcases hxP with ⟨J, hJ, hJx⟩
          rw [List.mem_cons] at hJ
          rcases hJ with rfl | hJ
          · obtain ⟨K, hK, hKx⟩ := intersectionsWith_sound hsound hhead hJx hxR
            exact ⟨K, by simp [hK], hKx⟩
          · obtain ⟨K, hK, hKx⟩ := ih htail ⟨J, hJ, hJx⟩
            exact ⟨K, by simp [hK], hKx⟩

theorem intersect_sound {sign : Aff → Option Ordering} {p : ℝ × ℝ}
    (hsound : SignSoundAt sign p) {P R Q : List SInterval}
    (hQ : intersect sign P R = some Q) {x : ℝ}
    (hxP : InIntervals p x P) (hxR : InIntervals p x R) : InIntervals p x Q := by
  rcases hraw : rawIntersections sign R P with _ | A
  · simp [intersect, hraw] at hQ
  · exact normalize_sound hsound (by simpa [intersect, hraw] using hQ)
      (rawIntersections_sound hsound hraw hxP hxR)

theorem preimages_mem {p : ℝ × ℝ} {P : List SInterval} {I : SInterval}
    (hI : I ∈ P) {d j : ℚ} (hj : j ∈ ([0, 1, 2] : List ℚ)) {c u : ℝ}
    (hc : I.1.eval p ≤ c ∧ c ≤ I.2.eval p)
    (hu : u = 2 / 3 * (c + j - d)) : InIntervals p u (preimages d P) := by
  let J : SInterval :=
    ((I.1.add (Aff.const (j - d))).scale (2 / 3),
      (I.2.add (Aff.const (j - d))).scale (2 / 3))
  refine ⟨J, ?_, ?_, ?_⟩
  · simp only [preimages, List.mem_flatMap, List.mem_map]
    exact ⟨I, hI, j, hj, rfl⟩
  · dsimp [J]
    simp only [Aff.eval_scale, Aff.eval_add, Aff.eval_const]
    push_cast
    linarith
  · dsimp [J]
    simp only [Aff.eval_scale, Aff.eval_add, Aff.eval_const]
    push_cast
    linarith

theorem gate_mem {p : ℝ × ℝ} {u : ℝ} {k : ℤ}
    (hk0 : 0 ≤ k) (hk2 : k < 2)
    (hlo : (k : ℝ) + p.1 ≤ u)
    (hhi : u + 2 * p.2 / 3 ≤ (k : ℝ) + 1 - p.1) : InIntervals p u gate := by
  have hk : k = 0 ∨ k = 1 := by omega
  rcases hk with rfl | rfl
  · refine ⟨(betaAff, (Aff.const 1).sub (betaAff.add (widthAff.scale (2 / 3)))), ?_, ?_, ?_⟩
    · simp [gate]
    · simpa using hlo
    · simp only [Aff.eval_sub, Aff.eval_const, Aff.eval_add, eval_betaAff,
        Aff.eval_scale, eval_widthAff]
      push_cast
      linarith
  · refine ⟨(betaAff.add (Aff.const 1),
        ((Aff.const 1).sub (betaAff.add (widthAff.scale (2 / 3)))).add (Aff.const 1)), ?_, ?_, ?_⟩
    · simp [gate]
    · simp only [Aff.eval_add, eval_betaAff, Aff.eval_const]
      norm_num at hlo ⊢
      linarith
    · simp only [Aff.eval_add, Aff.eval_sub, Aff.eval_const, eval_betaAff,
        Aff.eval_scale, eval_widthAff]
      push_cast
      linarith

theorem minkowski_mem {p : ℝ × ℝ} {P : List SInterval} {a u : ℝ}
    (hu : InIntervals p u P) (hau : a ≤ u) (hual : u ≤ a + p.2 / 3) :
    InIntervals p a (minkowski P) := by
  rcases hu with ⟨I, hI, hIu⟩
  rcases I with ⟨lo, hi⟩
  refine ⟨(lo.sub (widthAff.scale (1 / 3)), hi), ?_, ?_, hau.trans hIu.2⟩
  · apply List.mem_map.mpr
    exact ⟨(lo, hi), hI, rfl⟩
  · simp only [Aff.eval_sub, Aff.eval_scale, eval_widthAff]
    push_cast
    linarith

theorem initial_mem {p : ℝ × ℝ} {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    InIntervals p x initial := by
  exact ⟨(Aff.const 0, Aff.const 1), by simp [initial], by simpa, by simpa⟩

theorem parityStep_sound {sign : Aff → Option Ordering} {p : ℝ × ℝ}
    (hsound : SignSoundAt sign p) {P res out : List SInterval} {d j : ℚ}
    (hout : parityStep sign P res d = some out) {a u c : ℝ} {k : ℤ}
    (ha : InIntervals p a res) (hc : InIntervals p c P)
    (hj : j ∈ ([0, 1, 2] : List ℚ)) (hu : u = 2 / 3 * (c + j - d))
    (hk0 : 0 ≤ k) (hk2 : k < 2)
    (hgateLo : (k : ℝ) + p.1 ≤ u)
    (hgateHi : u + 2 * p.2 / 3 ≤ (k : ℝ) + 1 - p.1)
    (hau : a ≤ u) (hual : u ≤ a + p.2 / 3) : InIntervals p a out := by
  rcases hc with ⟨I, hI, hIc⟩
  have huPre : InIntervals p u (preimages d P) := preimages_mem hI hj hIc hu
  have huGate : InIntervals p u gate := gate_mem hk0 hk2 hgateLo hgateHi
  rcases hpre : normalize sign (preimages d P) with _ | pre
  · simp [parityStep, hpre] at hout
  · have huPre' := normalize_sound hsound hpre huPre
    rcases hins : intersect sign pre gate with _ | inside
    · simp [parityStep, hpre, hins] at hout
    · have huInside := intersect_sound hsound hins huPre' huGate
      have haMink := minkowski_mem huInside hau hual
      rcases hstarts : normalize sign (minkowski inside) with _ | starts
      · simp [parityStep, hpre, hins, hstarts] at hout
      · have haStarts := normalize_sound hsound hstarts haMink
        exact intersect_sound hsound (by simpa [parityStep, hpre, hins, hstarts] using hout)
          ha haStarts

theorem relaxed_mem_parityStep {sign : Aff → Option Ordering} {β l : ℝ}
    (hsound : SignSoundAt sign (β, l)) (hβ : 0 < β) (htop : l < 3 / 2 - 3 * β)
    {S : Set ℝ} (hS : RelaxedStrategy β (1 - 2 * β) l S)
    {P res out : List SInterval} (hsub : ∀ x ∈ S, InIntervals (β, l) x P)
    {a : ℝ} (haS : a ∈ S) (ha : InIntervals (β, l) a res)
    {d : ℚ} (hd : (d : ℝ) ∈ ({0, 1 / 2} : Set ℝ))
    (hd0 : (0 : ℝ) ≤ d) (hd1 : (d : ℝ) ≤ 1 / 2)
    (hout : parityStep sign P res d = some out) : InIntervals (β, l) a out := by
  obtain ⟨u, hau, hul, ⟨k, hku, huk⟩, hcS⟩ := hS.2.2.2 a haS (d : ℝ) hd
  have ha01 := hS.2.2.1 haS
  have hual : u ≤ a + l / 3 := by linarith
  have hu0 : 0 ≤ u := ha01.1.trans hau
  have ha1 : a < 1 := ha01.2
  have hu3 : u < 3 / 2 := by linarith
  have hgateHi : u + 2 * l / 3 ≤ (k : ℝ) + 1 - β := by linarith
  have hk0 : 0 ≤ k := by
    by_contra hk
    have hk' : k ≤ -1 := by omega
    have hkR : (k : ℝ) ≤ -1 := by exact_mod_cast hk'
    linarith [hS.1]
  have hk2 : k < 2 := by
    by_contra hk
    have hk' : (2 : ℤ) ≤ k := by omega
    have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk'
    linarith
  let v : ℝ := 3 * u / 2 + (d : ℝ)
  let c : ℝ := Int.fract v
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv3 : v < 3 := by dsimp [v]; push_cast; linarith
  have hfloor0 : 0 ≤ ⌊v⌋ := Int.floor_nonneg.mpr hv0
  have hfloor3 : ⌊v⌋ < (3 : ℤ) := (Int.floor_lt).mpr (by exact_mod_cast hv3)
  have hfloor : ⌊v⌋ = 0 ∨ ⌊v⌋ = 1 ∨ ⌊v⌋ = 2 := by omega
  have hc : InIntervals (β, l) c P := hsub c hcS
  have huJ (j : ℤ) (hj : ⌊v⌋ = j) :
      u = 2 / 3 * (c + (j : ℝ) - (d : ℝ)) := by
    have hv := Int.fract_add_floor v
    rw [hj] at hv
    dsimp [c, v] at hv ⊢
    push_cast at hv ⊢
    linarith
  rcases hfloor with hj | hj | hj
  · exact parityStep_sound (d := d) (j := (0 : ℚ)) hsound hout ha hc
      (by simp) (by simpa using huJ 0 hj)
      hk0 hk2 hku hgateHi hau hual
  · exact parityStep_sound (d := d) (j := (1 : ℚ)) hsound hout ha hc
      (by simp) (by simpa using huJ 1 hj)
      hk0 hk2 hku hgateHi hau hual
  · exact parityStep_sound (d := d) (j := (2 : ℚ)) hsound hout ha hc
      (by simp) (by simpa using huJ 2 hj)
      hk0 hk2 hku hgateHi hau hual

/-- A successful symbolic step contains every point of a relaxed strategy that
was contained in the input list. -/
theorem symbolicStep_sound {sign : Aff → Option Ordering} {β l : ℝ}
    (hsound : SignSoundAt sign (β, l)) (hβ : 0 < β) (htop : l < 3 / 2 - 3 * β)
    {S : Set ℝ} (hS : RelaxedStrategy β (1 - 2 * β) l S)
    {P Q : List SInterval} (hsub : ∀ x ∈ S, InIntervals (β, l) x P)
    (hPQ : symbolicStep sign P = some Q) : ∀ x ∈ S, InIntervals (β, l) x Q := by
  rcases hzero : parityStep sign P P 0 with _ | P₀
  · simp [symbolicStep, hzero] at hPQ
  · have hhalf : parityStep sign P P₀ (1 / 2) = some Q := by
      simpa [symbolicStep, hzero] using hPQ
    intro x hx
    have hx₀ : InIntervals (β, l) x P₀ :=
      relaxed_mem_parityStep hsound hβ htop hS hsub hx (hsub x hx)
        (by simp) (by norm_num) (by norm_num) hzero
    exact relaxed_mem_parityStep hsound hβ htop hS hsub hx hx₀
      (by simp) (by norm_num) (by norm_num) hhalf

theorem descend_sound {sign : Aff → Option Ordering} {β l : ℝ}
    (hsound : SignSoundAt sign (β, l)) (hβ : 0 < β) (htop : l < 3 / 2 - 3 * β)
    {S : Set ℝ} (hS : RelaxedStrategy β (1 - 2 * β) l S)
    {n : ℕ} {P Q : List SInterval} (hsub : ∀ x ∈ S, InIntervals (β, l) x P)
    (hPQ : descend sign n P = some Q) : ∀ x ∈ S, InIntervals (β, l) x Q := by
  induction n generalizing P Q with
  | zero =>
      simp [descend] at hPQ
      subst Q
      exact hsub
  | succ n ih =>
      rcases hstep : symbolicStep sign P with _ | R
      · simp [descend, hstep] at hPQ
      · apply ih (P := R) (Q := Q)
        · exact symbolicStep_sound hsound hβ htop hS hsub hstep
        · simpa [descend, hstep] using hPQ

theorem no_relaxedStrategy_of_descend_empty {sign : Aff → Option Ordering} {β l : ℝ}
    (hsound : SignSoundAt sign (β, l)) (hβ : 0 < β) (htop : l < 3 / 2 - 3 * β)
    {n : ℕ} (hempty : descend sign n initial = some []) :
    ∀ S : Set ℝ, ¬ RelaxedStrategy β (1 - 2 * β) l S := by
  intro S hS
  have hsub : ∀ x ∈ S, InIntervals (β, l) x initial := by
    intro x hx
    have hx01 := hS.2.2.1 hx
    exact initial_mem hx01.1 hx01.2.le
  obtain ⟨x, hx⟩ := hS.2.1
  have := descend_sound hsound hβ htop hS hsub hempty x hx
  simpa [InIntervals] using this

/-! ## The checked triangle tree -/

def lineThrough (p q : ℚ × ℚ) : Aff :=
  ⟨-p.2 * (q.1 - p.1) + p.1 * (q.2 - p.2), -(q.2 - p.2), q.1 - p.1⟩

structure Barycentric where
  l₁ : Aff
  l₂ : Aff
  l₃ : Aff
  deriving DecidableEq, Repr

def barycentric (v₁ v₂ v₃ : ℚ × ℚ) : Barycentric :=
  let f₁ := lineThrough v₂ v₃
  let f₂ := lineThrough v₃ v₁
  let f₃ := lineThrough v₁ v₂
  ⟨f₁.scale (1 / f₁.evalQ v₁), f₂.scale (1 / f₂.evalQ v₂),
    f₃.scale (1 / f₃.evalQ v₃)⟩

def Aff.ratio? (f g : Aff) : Option ℚ :=
  if g.c ≠ 0 then some (f.c / g.c)
  else if g.b ≠ 0 then some (f.b / g.b)
  else if g.w ≠ 0 then some (f.w / g.w)
  else none

def positiveMultiple (f g : Aff) : Bool :=
  match f.ratio? g with
  | none => false
  | some r => decide (0 < r) && decide (f = g.scale r)

def coveredBy (constraints : List Aff) (f : Aff) : Bool :=
  constraints.any (positiveMultiple f)

/-- Besides the edge-constraint check, verify the three coefficient identities
which make the generated forms barycentric coordinates. -/
def barycentricOK (v₁ v₂ v₃ : ℚ × ℚ) : Bool :=
  let b := barycentric v₁ v₂ v₃
  decide (b.l₁.add (b.l₂.add b.l₃) = Aff.const 1) &&
    decide ((b.l₁.scale v₁.1).add ((b.l₂.scale v₂.1).add (b.l₃.scale v₃.1)) =
      betaAff) &&
    decide ((b.l₁.scale v₁.2).add ((b.l₂.scale v₂.2).add (b.l₃.scale v₃.2)) =
      widthAff)

def leafOK (constraints : List Aff) (v₁ v₂ v₃ : ℚ × ℚ) (depth : ℕ) : Bool :=
  let b := barycentric v₁ v₂ v₃
  barycentricOK v₁ v₂ v₃ && coveredBy constraints b.l₁ &&
    coveredBy constraints b.l₂ && coveredBy constraints b.l₃ &&
    constraints.all (fun f => decide (f.b ≠ 0)) && leafEmpties v₁ v₂ v₃ depth

def checkTree (constraints : List Aff) : CTree → Bool
  | .leaf v₁ v₂ v₃ depth => leafOK constraints v₁ v₂ v₃ depth
  | .node f pos neg => decide (f.b ≠ 0) && checkTree (f :: constraints) pos &&
      checkTree (f.neg :: constraints) neg

def checkRoot (constraints : List Aff) (tree : CTree) : Bool :=
  constraints.all (fun f => decide (f.b ≠ 0)) && checkTree constraints tree

theorem positiveMultiple_sound {f g : Aff} (h : positiveMultiple f g = true) :
    ∃ r : ℚ, 0 < r ∧ f = g.scale r := by
  unfold positiveMultiple at h
  split at h
  · simp at h
  · rename_i r hr
    simp at h
    exact ⟨r, h.1, h.2⟩

theorem coveredBy_sound {constraints : List Aff} {f : Aff}
    (h : coveredBy constraints f = true) :
    ∃ g ∈ constraints, ∃ r : ℚ, 0 < r ∧ f = g.scale r := by
  simp only [coveredBy, List.any_eq_true] at h
  obtain ⟨g, hg, hfg⟩ := h
  obtain ⟨r, hr, hfr⟩ := positiveMultiple_sound hfg
  exact ⟨g, hg, r, hr, hfr⟩

theorem barycentricOK_sound {v₁ v₂ v₃ : ℚ × ℚ}
    (h : barycentricOK v₁ v₂ v₃ = true) :
    let b := barycentric v₁ v₂ v₃
    b.l₁.add (b.l₂.add b.l₃) = Aff.const 1 ∧
      (b.l₁.scale v₁.1).add ((b.l₂.scale v₂.1).add (b.l₃.scale v₃.1)) = betaAff ∧
      (b.l₁.scale v₁.2).add ((b.l₂.scale v₂.2).add (b.l₃.scale v₃.2)) = widthAff := by
  simp [barycentricOK] at h
  simpa only [and_assoc] using h

theorem barycentric_relations {v₁ v₂ v₃ : ℚ × ℚ} {p : ℝ × ℝ}
    (h : barycentricOK v₁ v₂ v₃ = true) :
    let b := barycentric v₁ v₂ v₃
    b.l₁.eval p + b.l₂.eval p + b.l₃.eval p = 1 ∧
      p = b.l₁.eval p • ((v₁.1 : ℝ), (v₁.2 : ℝ)) +
        b.l₂.eval p • ((v₂.1 : ℝ), (v₂.2 : ℝ)) +
        b.l₃.eval p • ((v₃.1 : ℝ), (v₃.2 : ℝ)) := by
  let b := barycentric v₁ v₂ v₃
  obtain ⟨hs, hx, hy⟩ := barycentricOK_sound h
  have hs' := congrArg (fun f : Aff => f.eval p) hs
  have hx' := congrArg (fun f : Aff => f.eval p) hx
  have hy' := congrArg (fun f : Aff => f.eval p) hy
  simp only [Aff.eval_add, Aff.eval_const] at hs'
  simp only [Aff.eval_add, Aff.eval_scale, eval_betaAff] at hx'
  simp only [Aff.eval_add, Aff.eval_scale, eval_widthAff] at hy'
  push_cast at hs' hx' hy'
  refine ⟨by linarith [hs'], ?_⟩
  apply Prod.ext
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    linarith
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    linarith

theorem coveredBy_positive {constraints : List Aff} {f : Aff} {p : ℝ × ℝ}
    (hcover : coveredBy constraints f = true)
    (hpos : ∀ g ∈ constraints, 0 < g.eval p) : 0 < f.eval p := by
  obtain ⟨g, hg, r, hr, rfl⟩ := coveredBy_sound hcover
  rw [Aff.eval_scale]
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  exact mul_pos hr' (hpos g hg)

theorem vertexSign_soundAt_of_barycentric {v₁ v₂ v₃ : ℚ × ℚ} {p : ℝ × ℝ}
    (hb : barycentricOK v₁ v₂ v₃ = true)
    (h₁ : 0 < (barycentric v₁ v₂ v₃).l₁.eval p)
    (h₂ : 0 < (barycentric v₁ v₂ v₃).l₂.eval p)
    (h₃ : 0 < (barycentric v₁ v₂ v₃).l₃.eval p) :
    SignSoundAt (fun f => vertexSign f v₁ v₂ v₃) p := by
  let b := barycentric v₁ v₂ v₃
  let p₁ : ℝ × ℝ := ((v₁.1 : ℝ), (v₁.2 : ℝ))
  let p₂ : ℝ × ℝ := ((v₂.1 : ℝ), (v₂.2 : ℝ))
  let p₃ : ℝ × ℝ := ((v₃.1 : ℝ), (v₃.2 : ℝ))
  have hrel := barycentric_relations (p := p) hb
  have hgt (f : Aff) (hf : vertexSign f v₁ v₂ v₃ = some .gt) : 0 < f.eval p := by
    obtain ⟨hn, hs⟩ := vertexSign_gt_sound hf
    have hn₁ : 0 ≤ f.eval p₁ := by
      rw [Aff.eval_rat]
      exact_mod_cast hn.1
    have hn₂ : 0 ≤ f.eval p₂ := by
      rw [Aff.eval_rat]
      exact_mod_cast hn.2.1
    have hn₃ : 0 ≤ f.eval p₃ := by
      rw [Aff.eval_rat]
      exact_mod_cast hn.2.2
    have hs' : 0 < f.eval p₁ ∨ 0 < f.eval p₂ ∨ 0 < f.eval p₃ := by
      rcases hs with hs | hs | hs
      · left
        rw [Aff.eval_rat]
        exact_mod_cast hs
      · right; left
        rw [Aff.eval_rat]
        exact_mod_cast hs
      · right; right
        rw [Aff.eval_rat]
        exact_mod_cast hs
    exact f.eval_pos_of_barycentric p p₁ p₂ p₃ (b.l₁.eval p) (b.l₂.eval p) (b.l₃.eval p)
      hrel.2 h₁ h₂ h₃ hrel.1 hn₁ hn₂ hn₃ hs'
  intro f
  refine ⟨?_, ?_, ?_⟩
  · intro hf
    obtain ⟨hz₁, hz₂, hz₃⟩ := vertexSign_eq_sound hf
    rw [hrel.2, f.eval_affineCombination p₁ p₂ p₃ (b.l₁.eval p) (b.l₂.eval p)
      (b.l₃.eval p) hrel.1]
    dsimp [p₁, p₂, p₃]
    simp only [Aff.eval_rat]
    push_cast
    rw [hz₁, hz₂, hz₃]
    ring
  · exact hgt f
  · intro hf
    have hn := hgt f.neg (vertexSign_lt_sound hf)
    simpa using hn

theorem leafOK_no_relaxedStrategy {constraints : List Aff} {v₁ v₂ v₃ : ℚ × ℚ}
    {depth : ℕ} {p : ℝ × ℝ} (hcheck : leafOK constraints v₁ v₂ v₃ depth = true)
    (hconstraints : ∀ f ∈ constraints, 0 < f.eval p) (hβ : 0 < p.1)
    (htop : p.2 < 3 / 2 - 3 * p.1) :
    ∀ S : Set ℝ, ¬ RelaxedStrategy p.1 (1 - 2 * p.1) p.2 S := by
  simp only [leafOK, Bool.and_eq_true] at hcheck
  rcases hcheck with ⟨⟨⟨⟨⟨hb, hc₁⟩, hc₂⟩, hc₃⟩, hbeta⟩, hempty⟩
  have h₁ := coveredBy_positive hc₁ hconstraints
  have h₂ := coveredBy_positive hc₂ hconstraints
  have h₃ := coveredBy_positive hc₃ hconstraints
  have hsound := vertexSign_soundAt_of_barycentric hb h₁ h₂ h₃
  have hdesc : descend (fun f => vertexSign f v₁ v₂ v₃) depth initial = some [] := by
    simpa [leafEmpties] using hempty
  exact no_relaxedStrategy_of_descend_empty hsound hβ htop hdesc

def treeForms : CTree → List Aff
  | .leaf _ _ _ _ => []
  | .node f pos neg => f :: (treeForms pos ++ treeForms neg)

theorem checkTree_no_relaxedStrategy {β l : ℝ} (hβ : 0 < β) (htop : l < 3 / 2 - 3 * β)
    {constraints : List Aff} (hconstraints : ∀ f ∈ constraints, 0 < f.eval (β, l))
    {tree : CTree} (hcheck : checkTree constraints tree = true)
    (hforms : ∀ f ∈ treeForms tree, f.eval (β, l) ≠ 0) :
    ∀ S : Set ℝ, ¬ RelaxedStrategy β (1 - 2 * β) l S := by
  induction tree generalizing constraints with
  | leaf v₁ v₂ v₃ depth =>
      exact leafOK_no_relaxedStrategy hcheck hconstraints hβ htop
  | node f pos neg ihpos ihneg =>
      simp only [checkTree, Bool.and_eq_true] at hcheck
      rcases hcheck with ⟨⟨hfb, hpos⟩, hneg⟩
      have hfne : f.eval (β, l) ≠ 0 := hforms f (by simp [treeForms])
      rcases lt_trichotomy (f.eval (β, l)) 0 with hf | hf | hf
      · apply ihneg (constraints := f.neg :: constraints)
        · intro g hg
          rw [List.mem_cons] at hg
          rcases hg with rfl | hg
          · simpa using (neg_pos.mpr hf)
          · exact hconstraints g hg
        · exact hneg
        · intro g hg
          exact hforms g (by simp [treeForms, hg])
      · exact (hfne hf).elim
      · apply ihpos (constraints := f :: constraints)
        · intro g hg
          rw [List.mem_cons] at hg
          rcases hg with rfl | hg
          · exact hf
          · exact hconstraints g hg
        · exact hpos
        · intro g hg
          exact hforms g (by simp [treeForms, hg])

theorem checkTree_forms_beta {constraints : List Aff} {tree : CTree}
    (h : checkTree constraints tree = true) : ∀ f ∈ treeForms tree, f.b ≠ 0 := by
  induction tree generalizing constraints with
  | leaf v₁ v₂ v₃ depth => simp [treeForms]
  | node f pos neg ihpos ihneg =>
      simp only [checkTree, Bool.and_eq_true] at h
      rcases h with ⟨⟨hfb, hpos⟩, hneg⟩
      simp only [decide_eq_true_eq] at hfb
      intro g hg
      simp only [treeForms, List.mem_cons, List.mem_append] at hg
      rcases hg with rfl | hg | hg
      · exact hfb
      · exact ihpos hpos g hg
      · exact ihneg hneg g hg

def allForms (constraints : List Aff) (tree : CTree) : List Aff :=
  constraints ++ treeForms tree

theorem checkRoot_forms_beta {constraints : List Aff} {tree : CTree}
    (h : checkRoot constraints tree = true) : ∀ f ∈ allForms constraints tree, f.b ≠ 0 := by
  simp only [checkRoot, Bool.and_eq_true] at h
  rcases h with ⟨hroot, htree⟩
  simp only [List.all_eq_true, decide_eq_true_eq] at hroot
  intro f hf
  rw [allForms, List.mem_append] at hf
  rcases hf with hf | hf
  · exact hroot f hf
  · exact checkTree_forms_beta htree f hf

theorem certificate0 : checkRoot root0 tree0 = true := by native_decide

theorem certificate1 : checkRoot root1 tree1 = true := by native_decide

theorem root0_positive {β l : ℝ} (h₁ : 1 / 12 < β) (h₂ : β < 1 / 9)
    (h₃ : 3 / 4 - 39 * β / 8 < l) (h₄ : l < 3 / 2 - 3 * β) :
  ∀ f ∈ root0, 0 < f.eval (β, l) := by
  intro f hf
  simp [root0] at hf
  rcases hf with rfl | rfl | rfl | rfl
  all_goals simp only [Aff.eval]; push_cast; linarith

theorem root1_positive {β l : ℝ} (h₁ : 1 / 9 < β) (h₂ : β < 7 / 57)
    (h₃ : 15 / 16 - 105 * β / 16 < l) (h₄ : l < 3 / 2 - 3 * β) :
  ∀ f ∈ root1, 0 < f.eval (β, l) := by
  intro f hf
  simp [root1] at hf
  rcases hf with rfl | rfl | rfl | rfl
  all_goals simp only [Aff.eval]; push_cast; linarith

theorem RelaxedStrategy.width_le {s t l : ℝ} {P : Set ℝ}
    (h : RelaxedStrategy s t l P) : 2 * l / 3 ≤ t := by
  obtain ⟨a, ha⟩ := h.2.1
  obtain ⟨u, -, -, ⟨k, hk₁, hk₂⟩, -⟩ := h.2.2.2 a ha 0 (by simp)
  linarith

noncomputable def betaZero (f : Aff) (l : ℝ) : ℝ :=
  -((f.c : ℝ) + (f.w : ℝ) * l) / (f.b : ℝ)

theorem eq_betaZero_of_eval_eq_zero {f : Aff} (hfb : f.b ≠ 0) {β l : ℝ}
    (h : f.eval (β, l) = 0) : β = betaZero f l := by
  have hfb' : (f.b : ℝ) ≠ 0 := by exact_mod_cast hfb
  rw [betaZero, eq_div_iff hfb']
  simp only [Aff.eval] at h
  push_cast at h ⊢
  linarith

theorem exists_beta_avoiding (forms : List Aff) {l lo hi : ℝ} (hlo : lo < hi)
    (hforms : ∀ f ∈ forms, f.b ≠ 0) :
    ∃ β ∈ Set.Ioo lo hi, ∀ f ∈ forms, f.eval (β, l) ≠ 0 := by
  classical
  let bad : Set ℝ := (fun f : Aff => betaZero f l) '' (↑forms.toFinset : Set Aff)
  have hbad : bad.Finite := forms.toFinset.finite_toSet.image _
  obtain ⟨β, hβ, hβbad⟩ := (Set.Ioo_infinite hlo).exists_notMem_finite hbad
  refine ⟨β, hβ, ?_⟩
  intro f hf hzero
  apply hβbad
  refine ⟨f, ?_, ?_⟩
  · simpa using hf
  · exact (eq_betaZero_of_eval_eq_zero (hforms f hf) hzero).symm

theorem certificate0_tree : checkTree root0 tree0 = true := by
  have h := certificate0
  simp only [checkRoot, Bool.and_eq_true] at h
  exact h.2

theorem certificate1_tree : checkTree root1 tree1 = true := by
  have h := certificate1
  simp only [checkRoot, Bool.and_eq_true] at h
  exact h.2

/-- **No memoryless relaxed strategy above the upper edge** (`ArcDelayGame.RelaxedAboveUpperEdge`).
Route: soundness of the symbolic descent at one real point, a vertex sign test on open triangles (barycentric
coordinates), a decision tree whose split lines all have a nonzero `β` coefficient, and, for points on a split
line, a small leftward shift in `β` plus `RelaxedStrategy.mono`.  The certificate is checked by `native_decide`. -/
theorem relaxedAboveUpperEdge : RelaxedAboveUpperEdge := by
  intro β l hβlo hβhi hedge P hP
  by_cases habove : 3 / 2 - 3 * β < l
  · have hw :=
      CollatzMoonshot.Benchmark.ArcBandCertificate.RelaxedStrategy.width_le hP
    linarith
  have hltop : l ≤ 3 / 2 - 3 * β := le_of_not_gt habove
  by_cases hpiece : β ≤ 1 / 9
  · have hedge₀ : 3 / 4 - 39 * β / 8 < l := by
      rw [min_eq_left (by linarith)] at hedge
      exact hedge
    let lo : ℝ := max (1 / 12) ((8 / 39) * (3 / 4 - l))
    have hlo : lo < β := by
      dsimp [lo]
      apply max_lt
      · linarith
      · linarith
    obtain ⟨β', hβ', havoid⟩ := exists_beta_avoiding (l := l) (allForms root0 tree0) hlo
      (checkRoot_forms_beta certificate0)
    have hβ'β : β' < β := hβ'.2
    have hβ'lo : 1 / 12 < β' := (le_max_left _ _).trans_lt hβ'.1
    have hβ'pos : 0 < β' := by linarith
    have hβ'hi : β' < 1 / 9 := hβ'.2.trans_le hpiece
    have hedge' : 3 / 4 - 39 * β' / 8 < l := by
      have hcut : (8 / 39 : ℝ) * (3 / 4 - l) < β' :=
        (le_max_right _ _).trans_lt hβ'.1
      linarith
    have htop' : l < 3 / 2 - 3 * β' := by linarith
    have hroot := root0_positive hβ'lo hβ'hi hedge' htop'
    have htreeForms : ∀ f ∈ treeForms tree0, f.eval (β', l) ≠ 0 := by
      intro f hf
      exact havoid f (by simp [allForms, hf])
    have hno := checkTree_no_relaxedStrategy hβ'pos htop' hroot certificate0_tree htreeForms
    have hP' : RelaxedStrategy β' (1 - 2 * β') l P :=
      hP.mono hβ'.2.le (by linarith)
    exact hno P hP'
  · have hpiece' : 1 / 9 < β := lt_of_not_ge hpiece
    have hedge₁ : 15 / 16 - 105 * β / 16 < l := by
      rw [min_eq_right (by linarith)] at hedge
      exact hedge
    let lo : ℝ := max (1 / 9) ((16 / 105) * (15 / 16 - l))
    have hlo : lo < β := by
      dsimp [lo]
      apply max_lt
      · exact hpiece'
      · linarith
    obtain ⟨β', hβ', havoid⟩ := exists_beta_avoiding (l := l) (allForms root1 tree1) hlo
      (checkRoot_forms_beta certificate1)
    have hβ'β : β' < β := hβ'.2
    have hβ'lo : 1 / 9 < β' := (le_max_left _ _).trans_lt hβ'.1
    have hβ'pos : 0 < β' := by linarith
    have hβ'hi : β' < 7 / 57 := hβ'.2.trans_le hβhi
    have hedge' : 15 / 16 - 105 * β' / 16 < l := by
      have hcut : (16 / 105 : ℝ) * (15 / 16 - l) < β' :=
        (le_max_right _ _).trans_lt hβ'.1
      linarith
    have htop' : l < 3 / 2 - 3 * β' := by linarith
    have hroot := root1_positive hβ'lo hβ'hi hedge' htop'
    have htreeForms : ∀ f ∈ treeForms tree1, f.eval (β', l) ≠ 0 := by
      intro f hf
      exact havoid f (by simp [allForms, hf])
    have hno := checkTree_no_relaxedStrategy hβ'pos htop' hroot certificate1_tree htreeForms
    have hP' : RelaxedStrategy β' (1 - 2 * β') l P :=
      hP.mono hβ'.2.le (by linarith)
    exact hno P hP'

end CollatzMoonshot.Benchmark.ArcBandCertificate
