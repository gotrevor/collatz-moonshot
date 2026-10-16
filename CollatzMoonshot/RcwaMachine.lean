/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Theorem C, the machine-to-permutation core: completion and Lemma M (abstract)

Two abstract pieces of the undecidability route for orbit counts of RCWA permutations of `ℤ`
(research notes `undec-lemma`, `undec-r25`).  No number theory appears here: the RCWA encoding
(Lemma P) turns a reversible counter machine into a partial injection, and these lemmas say what
the orbits of the completed permutation are.

## 1. Completion (Lemma C of `undec-lemma`, abstract form)

`f : PEquiv α α` is the configuration graph of a reversible machine (out- and in-degree `≤ 1`).
Its *sources* have no predecessor, its *sinks* no successor.  A bijection `τ : sinks ≃ sources`
and a *highway* type `H` are given, with a bijection `θ : ℤ ≃ sources ⊕ H` (the line).  The
completed map `σ` on `α ⊕ H` is

* `f` where `f` is defined,
* `ν ∘ τ` on sinks, where `ν = θ ∘ (+1) ∘ θ⁻¹` is the highway shift,
* `ν` on `H`.

`σ` is a bijection with no further hypotheses (`completeFun_bijective`).  Under

* **(H1)** no bi-infinite `f`-chain (a cycle is a periodic bi-infinite chain, so this also
  excludes cycles), and
* **(H2)** `τ (end x) = x` for every source `x` whose forward chain is finite,

the orbits of `σ` are the maximal cut-free runs of the line, where a *cut* is a source with an
infinite forward chain: `#orbits = 1 + #cuts` (`card_orbits`).  So `σ` has one orbit iff there is
no cut, and infinitely many orbits iff there are infinitely many cuts.  In the concrete build
each forward-divergent configuration comes with an infinite family of junk copies, so the count
is `1` or `∞`; that multiplicity is a property of the encoding, not of this lemma.

## 2. Lemma M (abstract)

A run of any step relation on `Q × V` (`Q` finite, `V` well-quasi-ordered, e.g. `ℕ × ℕ`) that
stays off a set `B` of boundary states and returns to a state must strictly lose (forward) or
gain (backward) in the order on `V`; then every infinite run visits `B` infinitely often
(`visits_boundary_forward`, `visits_boundary_backward`), by Dickson's lemma.  For a 2-counter
guarded machine the hypothesis follows from the paper's loop condition (S1), stated as: every
closed rule walk off `B` has a lap vector with one negative and one positive entry
(`TwoCounter.visits_boundary`).  Consequently immortality (and immortality of the reverse) is
decided by the macro map on boundary configurations (`immortal_iff_macro`,
`reverse_immortal_iff_macro`).
-/

namespace CollatzMoonshot.RcwaMachine

/-! ## 1. Completion -/

section Completion

universe u

variable {α H : Type u}

/-- The `n`-fold forward iterate of a partial injection, starting from `x`. -/
def fwd (f : PEquiv α α) (n : ℕ) (x : α) : Option α :=
  (fun o : Option α => o.bind f)^[n] (some x)

/-- Sources: configurations with no predecessor. -/
def Src (f : PEquiv α α) : Type u := {x : α // f.symm x = none}

/-- Sinks: configurations with no successor. -/
def Snk (f : PEquiv α α) : Type u := {x : α // f x = none}

/-- The forward chain from `x` is infinite. -/
def Diverges (f : PEquiv α α) (x : α) : Prop := ∀ n, fwd f n x ≠ none

/-- **(H1)** No bi-infinite chain: no `g : ℤ → α` with `f (g i) = g (i + 1)` for all `i`.
A cycle is a periodic such `g`, so this also rules out cycles. -/
def NoBiInfinite (f : PEquiv α α) : Prop :=
  ∀ g : ℤ → α, ¬ ∀ i, f (g i) = some (g (i + 1))

/-- **(H2)** The pairing returns every finite chain to its own start: if the chain from the source
`s` reaches the sink `t`, then `τ t = s`. -/
def EndToStart (f : PEquiv α α) (τ : Snk f ≃ Src f) : Prop :=
  ∀ (s : Src f) (t : Snk f) (n : ℕ), fwd f n s.1 = some t.1 → τ t = s

/-- The line points `sources ⊕ H`, viewed inside `α ⊕ H`. -/
def lineEmb (f : PEquiv α α) : Src f ⊕ H → α ⊕ H :=
  Sum.map Subtype.val id

/-- The highway shift `ν = θ ∘ (+1) ∘ θ⁻¹`, landing in `α ⊕ H`. -/
def nu (f : PEquiv α α) (θ : ℤ ≃ Src f ⊕ H) (p : Src f ⊕ H) : α ⊕ H :=
  lineEmb f (θ (θ.symm p + 1))

/-- The completed map: `f` where defined, `ν ∘ τ` on sinks, `ν` on the highway. -/
def completeFun (f : PEquiv α α) (τ : Snk f ≃ Src f) (θ : ℤ ≃ Src f ⊕ H) :
    α ⊕ H → α ⊕ H
  | Sum.inl x =>
    match hx : f x with
    | some y => Sum.inl y
    | none => nu f θ (Sum.inl (τ ⟨x, hx⟩))
  | Sum.inr h => nu f θ (Sum.inr h)

/-- Part 1 of Lemma C: the completion is a bijection, for any partial injection `f`, any
bijection `τ` and any line `θ`. -/
theorem completeFun_bijective (f : PEquiv α α) (τ : Snk f ≃ Src f) (θ : ℤ ≃ Src f ⊕ H) :
    Function.Bijective (completeFun f τ θ) := by
  sorry

/-- The completed permutation `σ` of `α ⊕ H`. -/
noncomputable def complete (f : PEquiv α α) (τ : Snk f ≃ Src f) (θ : ℤ ≃ Src f ⊕ H) :
    Equiv.Perm (α ⊕ H) :=
  Equiv.ofBijective _ (completeFun_bijective f τ θ)

/-- The orbits of a permutation, as a quotient type. -/
abbrev Orbits {β : Type u} (σ : Equiv.Perm β) : Type u :=
  Quotient (Equiv.Perm.SameCycle.setoid σ)

/-- A non-divergent source at line position `p` lies on one orbit with line position `p + 1`:
`σ` runs its finite chain and, by (H2), returns to the highway at `ν` of the source. -/
theorem sameCycle_succ_of_not_diverges (f : PEquiv α α) (τ : Snk f ≃ Src f)
    (θ : ℤ ≃ Src f ⊕ H) (h2 : EndToStart f τ) (p : ℤ)
    (hp : ∀ s : Src f, θ p = Sum.inl s → ¬ Diverges f s.1) :
    (complete f τ θ).SameCycle (lineEmb f (θ p)) (lineEmb f (θ (p + 1))) := by
  sorry

/-- A divergent source at line position `p` is a cut: positions `≤ p` and `> p` lie on different
orbits.  Needs (H1) and (H2). -/
theorem not_sameCycle_of_cut (f : PEquiv α α) (τ : Snk f ≃ Src f) (θ : ℤ ≃ Src f ⊕ H)
    (h1 : NoBiInfinite f) (h2 : EndToStart f τ) (s : Src f) (hs : Diverges f s.1) {p q r : ℤ}
    (hp : θ p = Sum.inl s) (hq : q ≤ p) (hr : p < r) :
    ¬ (complete f τ θ).SameCycle (lineEmb f (θ q)) (lineEmb f (θ r)) := by
  sorry

/-- **Lemma C, orbit formula.**  Under (H1) and (H2), the number of orbits of the completion is
one more than the number of forward-divergent sources (as cardinals, so `1 + ℵ₀ = ℵ₀` covers the
infinite case). -/
theorem card_orbits (f : PEquiv α α) (τ : Snk f ≃ Src f) (θ : ℤ ≃ Src f ⊕ H)
    (h1 : NoBiInfinite f) (h2 : EndToStart f τ) :
    Cardinal.mk (Orbits (complete f τ θ)) = 1 + Cardinal.mk {s : Src f // Diverges f s.1} := by
  sorry

/-- One orbit iff no source diverges. -/
theorem sameCycle_all_iff (f : PEquiv α α) (τ : Snk f ≃ Src f) (θ : ℤ ≃ Src f ⊕ H)
    (h1 : NoBiInfinite f) (h2 : EndToStart f τ) :
    (∀ a b : α ⊕ H, (complete f τ θ).SameCycle a b) ↔ ∀ s : Src f, ¬ Diverges f s.1 := by
  sorry

/-- Infinitely many orbits iff infinitely many sources diverge. -/
theorem infinite_orbits_iff (f : PEquiv α α) (τ : Snk f ≃ Src f) (θ : ℤ ≃ Src f ⊕ H)
    (h1 : NoBiInfinite f) (h2 : EndToStart f τ) :
    Infinite (Orbits (complete f τ θ)) ↔ Infinite {s : Src f // Diverges f s.1} := by
  sorry

/-- **The `{1, ∞}` dichotomy.**  If divergent sources, when present, are infinitely many (the
junk multiplicity of the concrete encoding), the completion has one orbit or infinitely many;
it has one orbit exactly when no source diverges. -/
theorem one_or_infinite_orbits (f : PEquiv α α) (τ : Snk f ≃ Src f) (θ : ℤ ≃ Src f ⊕ H)
    (h1 : NoBiInfinite f) (h2 : EndToStart f τ)
    (hjunk : (∃ s : Src f, Diverges f s.1) → Infinite {s : Src f // Diverges f s.1}) :
    ((∀ a b : α ⊕ H, (complete f τ θ).SameCycle a b) ∧ ∀ s : Src f, ¬ Diverges f s.1) ∨
      (Infinite (Orbits (complete f τ θ)) ∧ ∃ s : Src f, Diverges f s.1) := by
  sorry

end Completion

/-! ## 2. Lemma M -/

section LemmaM

variable {Q V : Type*} [Preorder V]

/-- `x` steps from index `m` to index `n` and every state at indices `m, …, n` is off `B`. -/
def OffRun (B : Set Q) (Step : Q × V → Q × V → Prop) (x : ℕ → Q × V) (m n : ℕ) : Prop :=
  (∀ i, m ≤ i → i < n → Step (x i) (x (i + 1))) ∧ ∀ i, m ≤ i → i ≤ n → (x i).1 ∉ B

/-- Forward loop condition: a nonempty run off `B` that returns to its state never ends `≥` its
start in `V`.  For counters this says each lap decreases some counter. -/
def LapNotUp (B : Set Q) (Step : Q × V → Q × V → Prop) : Prop :=
  ∀ x m n, m < n → OffRun B Step x m n → (x m).1 = (x n).1 → ¬ (x m).2 ≤ (x n).2

/-- Backward loop condition: each such lap increases some counter. -/
def LapNotDown (B : Set Q) (Step : Q × V → Q × V → Prop) : Prop :=
  ∀ x m n, m < n → OffRun B Step x m n → (x m).1 = (x n).1 → ¬ (x n).2 ≤ (x m).2

/-- Pigeonhole on the finite state plus Dickson's lemma on the counters. -/
theorem exists_lt_fst_eq_snd_le [Finite Q] [WellQuasiOrderedLE V] (z : ℕ → Q × V) :
    ∃ i j, i < j ∧ (z i).1 = (z j).1 ∧ (z i).2 ≤ (z j).2 := by
  obtain ⟨q, hq⟩ := Finite.exists_infinite_fiber (fun n => (z n).1)
  have hinf : (Set.ofPred fun n => (z n).1 = q).Infinite := Set.infinite_coe_iff.mp hq
  set k := Nat.nth fun n => (z n).1 = q
  have hk := Nat.nth_strictMono hinf
  have hkq : ∀ n, (z (k n)).1 = q := Nat.nth_mem_of_infinite hinf
  obtain ⟨i, j, hij, hle⟩ := wellQuasiOrdered_le (fun n => (z (k n)).2)
  exact ⟨k i, k j, hk hij, by rw [hkq, hkq], hle⟩

/-- **Lemma M, forward.**  Every forward-infinite run visits `B` infinitely often. -/
theorem visits_boundary_forward [Finite Q] [WellQuasiOrderedLE V] (B : Set Q)
    (Step : Q × V → Q × V → Prop) (hlap : LapNotUp B Step) (x : ℕ → Q × V)
    (hx : ∀ n, Step (x n) (x (n + 1))) : ∀ N, ∃ n, N ≤ n ∧ (x n).1 ∈ B := by
  intro N
  by_contra! hoff
  obtain ⟨i, j, hij, hq, hle⟩ := exists_lt_fst_eq_snd_le (fun n => x (N + n))
  refine hlap x (N + i) (N + j) (by omega) ⟨fun n _ _ => hx n, fun n hn _ => ?_⟩ hq hle
  exact hoff n (by omega)

omit [Preorder V] in
/-- Reversing a run turns an off-`B` run of `Step` into one of `flip Step`. -/
theorem offRun_reverse {B : Set Q} {Step : Q × V → Q × V → Prop} {x : ℕ → Q × V} {m n : ℕ}
    (h : OffRun B Step x m n) : OffRun B (flip Step) (fun i => x (m + n - i)) m n := by
  refine ⟨fun i hm hn => ?_, fun i hm hn => h.2 _ (by omega) (by omega)⟩
  have := h.1 (m + n - i - 1) (by omega) (by omega)
  simp only [flip]
  rwa [show m + n - (i + 1) = m + n - i - 1 by omega,
    show m + n - i = m + n - i - 1 + 1 by omega]

theorem lapNotUp_flip {B : Set Q} {Step : Q × V → Q × V → Prop} (h : LapNotDown B Step) :
    LapNotUp B (flip Step) := by
  intro y m n hmn hrun hq
  have := h (fun i => y (m + n - i)) m n hmn (offRun_reverse hrun)
  simp only [show m + n - n = m by omega, show m + n - m = n by omega] at this
  exact this hq.symm

/-- **Lemma M, backward.**  Every backward-infinite run visits `B` infinitely often. -/
theorem visits_boundary_backward [Finite Q] [WellQuasiOrderedLE V] (B : Set Q)
    (Step : Q × V → Q × V → Prop) (hlap : LapNotDown B Step) (x : ℕ → Q × V)
    (hx : ∀ n, Step (x (n + 1)) (x n)) : ∀ N, ∃ n, N ≤ n ∧ (x n).1 ∈ B :=
  visits_boundary_forward B (flip Step) (lapNotUp_flip hlap) x hx

/-- One macro step: from a boundary configuration to the next one, through a nonempty run whose
intermediate states are off `B`. -/
def MacroStep (B : Set Q) (Step : Q × V → Q × V → Prop) (c d : Q × V) : Prop :=
  c.1 ∈ B ∧ d.1 ∈ B ∧ ∃ (x : ℕ → Q × V) (n : ℕ), 0 < n ∧ x 0 = c ∧ x n = d ∧
    (∀ i, i < n → Step (x i) (x (i + 1))) ∧ ∀ i, 0 < i → i < n → (x i).1 ∉ B

omit [Preorder V] in
/-- Reversing a macro step. -/
theorem macroStep_flip {B : Set Q} {Step : Q × V → Q × V → Prop} {c d : Q × V}
    (h : MacroStep B Step c d) : MacroStep B (flip Step) d c := by
  obtain ⟨hc, hd, x, n, hn, h0, hn', hstep, hoff⟩ := h
  refine ⟨hd, hc, fun i => x (n - i), n, hn, by simpa using hn', by simpa using h0,
    fun i hi => ?_, fun i hi hi' => hoff _ (by omega) (by omega)⟩
  have := hstep (n - i - 1) (by omega)
  simp only [flip]
  rwa [show n - (i + 1) = n - i - 1 by omega, show n - i = n - i - 1 + 1 by omega]

/-- **Lemma M, part 2.**  The machine is immortal iff the macro map has an infinite forward
orbit. -/
theorem immortal_iff_macro [Finite Q] [WellQuasiOrderedLE V] (B : Set Q)
    (Step : Q × V → Q × V → Prop) (hlap : LapNotUp B Step) :
    (∃ x : ℕ → Q × V, ∀ n, Step (x n) (x (n + 1))) ↔
      ∃ b : ℕ → Q × V, ∀ n, MacroStep B Step (b n) (b (n + 1)) := by
  classical
  constructor
  · rintro ⟨x, hx⟩
    have hvis := visits_boundary_forward B Step hlap x hx
    have hinf : (Set.ofPred fun n => (x n).1 ∈ B).Infinite :=
      Set.infinite_of_forall_exists_gt fun a => by
        obtain ⟨n, hn, hB⟩ := hvis (a + 1); exact ⟨n, hB, by omega⟩
    set k := Nat.nth fun n => (x n).1 ∈ B
    have hk : StrictMono k := Nat.nth_strictMono hinf
    have hkB : ∀ n, (x (k n)).1 ∈ B := Nat.nth_mem_of_infinite hinf
    refine ⟨fun n => x (k n), fun n => ⟨hkB n, hkB (n + 1), fun i => x (k n + i),
      k (n + 1) - k n, by have := hk (show n < n + 1 by omega); omega, by simp, ?_,
      fun i _ => by simpa [Nat.add_assoc] using hx (k n + i), fun i hi hi' hB => ?_⟩⟩
    · have := hk (show n < n + 1 by omega)
      show x (k n + (k (n + 1) - k n)) = x (k (n + 1))
      rw [Nat.add_sub_cancel' this.le]
    · have hc : k (Nat.count (fun n => (x n).1 ∈ B) (k n + i)) = k n + i := Nat.nth_count hB
      have h1 : k n < k (Nat.count (fun n => (x n).1 ∈ B) (k n + i)) := by rw [hc]; omega
      have h2 : k (Nat.count (fun n => (x n).1 ∈ B) (k n + i)) < k (n + 1) := by
        rw [hc]; omega
      rw [hk.lt_iff_lt] at h1 h2
      omega
  · rintro ⟨b, hb⟩
    simp only [MacroStep] at hb
    choose hb1 hb2 X L hL hX0 hXL hstep _ using hb
    let nxt : ℕ × ℕ → ℕ × ℕ := fun p => if p.2 + 1 < L p.1 then (p.1, p.2 + 1) else (p.1 + 1, 0)
    let pos : ℕ → ℕ × ℕ := fun t => nxt^[t] (0, 0)
    have hpos : ∀ t, (pos t).2 < L (pos t).1 := by
      intro t
      induction t with
      | zero => exact hL 0
      | succ t ih =>
        simp only [pos, Function.iterate_succ_apply', nxt] at ih ⊢
        split_ifs with h
        · exact h
        · exact hL _
    refine ⟨fun t => X (pos t).1 (pos t).2, fun t => ?_⟩
    have hp : pos (t + 1) = nxt (pos t) := Function.iterate_succ_apply' _ _ _
    simp only [hp, nxt]
    split_ifs with h
    · exact hstep _ _ (hpos t)
    · have := hstep _ _ (hpos t)
      rwa [show (pos t).2 + 1 = L (pos t).1 by have := hpos t; omega, hXL, ← hX0] at this

/-- **Lemma M, part 3.**  The reverse is immortal iff the macro map has an infinite backward
chain. -/
theorem reverse_immortal_iff_macro [Finite Q] [WellQuasiOrderedLE V] (B : Set Q)
    (Step : Q × V → Q × V → Prop) (hlap : LapNotDown B Step) :
    (∃ x : ℕ → Q × V, ∀ n, Step (x (n + 1)) (x n)) ↔
      ∃ b : ℕ → Q × V, ∀ n, MacroStep B Step (b (n + 1)) (b n) := by
  rw [show (∃ x : ℕ → Q × V, ∀ n, Step (x (n + 1)) (x n)) ↔
      ∃ x : ℕ → Q × V, ∀ n, flip Step (x n) (x (n + 1)) from Iff.rfl,
    immortal_iff_macro B (flip Step) (lapNotUp_flip hlap)]
  exact exists_congr fun b => forall_congr' fun n =>
    ⟨fun h => macroStep_flip h, fun h => macroStep_flip h⟩

end LemmaM

/-! ## 2'. Lemma M for guarded 2-counter machines -/

namespace TwoCounter

variable {Q : Type*}

/-- A guarded rule `(q, I, δ, q')`: from state `src` with counters in `guard`, add `move` and go
to `dst`. -/
structure Rule (Q : Type*) where
  /-- The state the rule leaves. -/
  src : Q
  /-- The guard on the counters. -/
  guard : Set (ℕ × ℕ)
  /-- The move added to the counters. -/
  move : ℤ × ℤ
  /-- The state the rule enters. -/
  dst : Q

/-- `ρ` fires from `c` to `c'`. -/
def Rule.Fires (ρ : Rule Q) (c c' : Q × ℕ × ℕ) : Prop :=
  c.1 = ρ.src ∧ c.2 ∈ ρ.guard ∧ c'.1 = ρ.dst ∧
    (c'.2.1 : ℤ) = c.2.1 + ρ.move.1 ∧ (c'.2.2 : ℤ) = c.2.2 + ρ.move.2

/-- One step of the machine with rule set `R` (determinism and reversibility are not needed for
Lemma M). -/
def Step (R : Set (Rule Q)) (c c' : Q × ℕ × ℕ) : Prop :=
  ∃ ρ ∈ R, ρ.Fires c c'

/-- **(S1), sharpened.**  Every closed walk `ρ 0, …, ρ (m-1)` (`m ≥ 1`) of rules of `R` whose
states are off `B` has a lap vector `∑ ρ i.move` with one negative and one positive entry.  The
paper's (S1) (each SCC off `B` trivial, or a simple cycle with one rule per edge and a mixed-sign
lap) implies this, since a closed walk there is a whole number of laps of one cycle. -/
def LapsMixed (B : Set Q) (R : Set (Rule Q)) : Prop :=
  ∀ (ρ : ℕ → Rule Q) (m : ℕ), 0 < m → (∀ i, i < m → ρ i ∈ R) →
    (∀ i, i < m → (ρ i).src ∉ B) → (∀ i, i + 1 < m → (ρ i).dst = (ρ (i + 1)).src) →
    (ρ (m - 1)).dst = (ρ 0).src →
    let δ := ∑ i ∈ Finset.range m, (ρ i).move
    (δ.1 < 0 ∧ 0 < δ.2) ∨ (δ.2 < 0 ∧ 0 < δ.1)

/-- Under (S1), an off-`B` run returning to its state moves one counter down and the other up. -/
theorem lap_mixed {B : Set Q} {R : Set (Rule Q)} (hS1 : LapsMixed B R) (x : ℕ → Q × ℕ × ℕ)
    {m n : ℕ} (hmn : m < n) (hstep : ∀ i, m ≤ i → i < n → Step R (x i) (x (i + 1)))
    (hoff : ∀ i, m ≤ i → i ≤ n → (x i).1 ∉ B) (hq : (x m).1 = (x n).1) :
    ((x n).2.1 < (x m).2.1 ∧ (x m).2.2 < (x n).2.2) ∨
      ((x n).2.2 < (x m).2.2 ∧ (x m).2.1 < (x n).2.1) := by
  have hex : ∀ j, ∃ ρ : Rule Q, j < n - m → ρ ∈ R ∧ ρ.Fires (x (m + j)) (x (m + j + 1)) := by
    intro j
    by_cases hj : j < n - m
    · obtain ⟨ρ, hρ, hf⟩ := hstep (m + j) (by omega) (by omega)
      exact ⟨ρ, fun _ => ⟨hρ, hf⟩⟩
    · exact ⟨⟨(x m).1, ∅, 0, (x m).1⟩, fun h => absurd h hj⟩
  choose ρ hρ using hex
  have hsum : ∀ k, k ≤ n - m → ∑ i ∈ Finset.range k, (ρ i).move =
      (((x (m + k)).2.1 : ℤ) - (x m).2.1, ((x (m + k)).2.2 : ℤ) - (x m).2.2) := by
    intro k
    induction k with
    | zero => intro; ext <;> simp
    | succ k ih =>
      intro hk
      obtain ⟨-, -, -, -, h1, h2⟩ := hρ k (by omega)
      rw [Finset.sum_range_succ, ih (by omega), show m + (k + 1) = m + k + 1 by omega]
      ext <;> simp <;> omega
  have hlap := hS1 ρ (n - m) (by omega) (fun i hi => (hρ i hi).1)
    (fun i hi => by rw [← (hρ i hi).2.1]; exact hoff _ (by omega) (by omega))
    (fun i hi => by
      rw [← (hρ i (by omega)).2.2.2.1, ← (hρ (i + 1) hi).2.1, Nat.add_assoc])
    (by
      rw [← (hρ _ (by omega)).2.2.2.1, ← (hρ 0 (by omega)).2.1,
        show m + (n - m - 1) + 1 = n by omega, Nat.add_zero, hq])
  simp only [hsum _ le_rfl, show m + (n - m) = n by omega] at hlap
  omega
/-- **Lemma M for 2-counter machines.**  Under (S1), every run that is infinite forward, or
infinite backward, visits the boundary states infinitely often. -/
theorem visits_boundary [Finite Q] (B : Set Q) (R : Set (Rule Q)) (hS1 : LapsMixed B R) :
    (∀ x : ℕ → Q × ℕ × ℕ, (∀ n, Step R (x n) (x (n + 1))) →
      ∀ N, ∃ n, N ≤ n ∧ (x n).1 ∈ B) ∧
    (∀ x : ℕ → Q × ℕ × ℕ, (∀ n, Step R (x (n + 1)) (x n)) →
      ∀ N, ∃ n, N ≤ n ∧ (x n).1 ∈ B) := by
  have hup : LapNotUp B (Step R) := fun x m n hmn hrun hq hle => by
    rcases lap_mixed hS1 x hmn hrun.1 hrun.2 hq with h | h <;>
      simp only [Prod.le_def] at hle <;> omega
  have hdown : LapNotDown B (Step R) := fun x m n hmn hrun hq hle => by
    rcases lap_mixed hS1 x hmn hrun.1 hrun.2 hq with h | h <;>
      simp only [Prod.le_def] at hle <;> omega
  exact ⟨visits_boundary_forward B (Step R) hup, visits_boundary_backward B (Step R) hdown⟩

end TwoCounter

end CollatzMoonshot.RcwaMachine
