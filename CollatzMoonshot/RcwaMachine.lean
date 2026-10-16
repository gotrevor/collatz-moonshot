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

theorem fwd_zero (f : PEquiv α α) (x : α) : fwd f 0 x = some x := rfl

theorem fwd_succ (f : PEquiv α α) (n : ℕ) (x : α) : fwd f (n + 1) x = (fwd f n x).bind f :=
  Function.iterate_succ_apply' _ _ _

theorem iterate_bind_none (f : PEquiv α α) (n : ℕ) :
    (fun o : Option α => o.bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih]; rfl

theorem fwd_succ_of_some {f : PEquiv α α} {x z : α} (h : f x = some z) (n : ℕ) :
    fwd f (n + 1) x = fwd f n z := by
  simp only [fwd, Function.iterate_succ_apply, Option.bind_some, h]

theorem fwd_succ_of_none {f : PEquiv α α} {x : α} (h : f x = none) (n : ℕ) :
    fwd f (n + 1) x = none := by
  simp only [fwd, Function.iterate_succ_apply, Option.bind_some, h, iterate_bind_none]

theorem fwd_succ_eq_some {f : PEquiv α α} {n : ℕ} {x y : α} (h : fwd f (n + 1) x = some y) :
    ∃ z, fwd f n x = some z ∧ f z = some y := by
  rw [fwd_succ] at h
  cases hz : fwd f n x with
  | none => rw [hz] at h; cases h
  | some z => rw [hz] at h; exact ⟨z, rfl, h⟩

theorem fwd_symm {f : PEquiv α α} {n : ℕ} {x y : α} (h : fwd f n x = some y) :
    fwd f.symm n y = some x := by
  induction n generalizing y with
  | zero => simp only [fwd_zero, Option.some.injEq] at h ⊢; exact h.symm
  | succ n ih =>
    obtain ⟨z, hz, hzy⟩ := fwd_succ_eq_some h
    rw [fwd_succ_of_some ((PEquiv.eq_some_iff f).mpr hzy), ih hz]

/-- A point reached in at least one step has a predecessor. -/
theorem symm_ne_none_of_fwd {f : PEquiv α α} {n : ℕ} {x y : α}
    (h : fwd f (n + 1) x = some y) : f.symm y ≠ none := by
  obtain ⟨z, -, hzy⟩ := fwd_succ_eq_some h
  rw [(PEquiv.eq_some_iff f).mpr hzy]; simp

/-- A finite chain has a last point. -/
theorem exists_last {f : PEquiv α α} {x : α} (h : ∃ n, fwd f n x = none) :
    ∃ m y, fwd f m x = some y ∧ f y = none := by
  classical
  have h0 : Nat.find h ≠ 0 := fun h0 => by
    have := Nat.find_spec h; rw [h0, fwd_zero] at this; cases this
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero h0
  have hlt : ¬ fwd f m x = none := Nat.find_min h (by omega)
  obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp hlt
  refine ⟨m, y, hy, ?_⟩
  have := Nat.find_spec h
  rwa [hm, fwd_succ, hy, Option.bind_some] at this

theorem completeFun_some {f : PEquiv α α} (τ : Snk f ≃ Src f) (θ : ℤ ≃ Src f ⊕ H) {x y : α}
    (h : f x = some y) : completeFun f τ θ (Sum.inl x) = Sum.inl y := by
  rw [completeFun]; split <;> simp_all

theorem completeFun_none {f : PEquiv α α} (τ : Snk f ≃ Src f) (θ : ℤ ≃ Src f ⊕ H) {x : α}
    (h : f x = none) : completeFun f τ θ (Sum.inl x) = nu f θ (Sum.inl (τ ⟨x, h⟩)) := by
  rw [completeFun]; split <;> simp_all

theorem completeFun_inr {f : PEquiv α α} (τ : Snk f ≃ Src f) (θ : ℤ ≃ Src f ⊕ H) (h : H) :
    completeFun f τ θ (Sum.inr h) = nu f θ (Sum.inr h) := rfl

theorem lineEmb_injective (f : PEquiv α α) : Function.Injective (lineEmb (H := H) f) :=
  Sum.map_injective.mpr ⟨Subtype.val_injective, Function.injective_id⟩

theorem nu_injective (f : PEquiv α α) (θ : ℤ ≃ Src f ⊕ H) : Function.Injective (nu f θ) :=
  fun p q h => by simpa using lineEmb_injective f h

theorem nu_eq_lineEmb (f : PEquiv α α) (θ : ℤ ≃ Src f ⊕ H) (l : Src f ⊕ H) :
    nu f θ (θ (θ.symm l - 1)) = lineEmb f l := by
  simp [nu]

/-- A line point is never a point with a predecessor. -/
theorem lineEmb_ne_inl {f : PEquiv α α} (l : Src f ⊕ H) {x y : α} (h : f x = some y) :
    lineEmb f l ≠ Sum.inl y := by
  rcases l with s | k
  · intro he
    change Sum.inl s.1 = Sum.inl y at he
    have := s.2; rw [Sum.inl.inj he, (PEquiv.eq_some_iff f).mpr h] at this; cases this
  · exact Sum.inr_ne_inl

theorem completeFun_cases (f : PEquiv α α) (τ : Snk f ≃ Src f) (θ : ℤ ≃ Src f ⊕ H)
    (a : α ⊕ H) :
    (∃ x y, a = Sum.inl x ∧ f x = some y ∧ completeFun f τ θ a = Sum.inl y) ∨
      ∃ q : Snk f ⊕ H, a = Sum.map Subtype.val id q ∧
        completeFun f τ θ a = nu f θ (Sum.map τ id q) := by
  rcases a with x | k
  · cases hx : f x with
    | some y => exact Or.inl ⟨x, y, rfl, hx, completeFun_some τ θ hx⟩
    | none => exact Or.inr ⟨Sum.inl ⟨x, hx⟩, rfl, completeFun_none τ θ hx⟩
  · exact Or.inr ⟨Sum.inr k, rfl, rfl⟩

/-- Part 1 of Lemma C: the completion is a bijection, for any partial injection `f`, any
bijection `τ` and any line `θ`. -/
theorem completeFun_bijective (f : PEquiv α α) (τ : Snk f ≃ Src f) (θ : ℤ ≃ Src f ⊕ H) :
    Function.Bijective (completeFun f τ θ) := by
  have hnu : ∀ l, ∃ a, completeFun f τ θ a = lineEmb f l := by
    intro l
    rw [← nu_eq_lineEmb]
    rcases θ (θ.symm l - 1) with s | k
    · refine ⟨Sum.inl (τ.symm s).1, ?_⟩
      rw [completeFun_none τ θ (τ.symm s).2]
      show nu f θ (Sum.inl (τ (τ.symm s))) = _
      rw [Equiv.apply_symm_apply]
    · exact ⟨Sum.inr k, rfl⟩
  refine ⟨fun a b hab => ?_, fun c => ?_⟩
  · rcases completeFun_cases f τ θ a with ⟨x, y, rfl, hxy, ha⟩ | ⟨p, rfl, ha⟩ <;>
      rcases completeFun_cases f τ θ b with ⟨x', y', rfl, hxy', hb⟩ | ⟨q, rfl, hb⟩
    · rw [ha, hb, Sum.inl.injEq] at hab
      subst hab
      exact congrArg _ (PEquiv.inj f hxy hxy')
    · rw [ha, hb, nu] at hab; exact absurd hab.symm (lineEmb_ne_inl _ hxy)
    · rw [ha, hb, nu] at hab; exact absurd hab (lineEmb_ne_inl _ hxy')
    · rw [ha, hb] at hab
      have := nu_injective f θ hab
      have := (Sum.map_injective.mpr ⟨τ.injective, Function.injective_id⟩) this
      rw [this]
  · rcases c with y | k
    · cases hy : f.symm y with
      | some x => exact ⟨Sum.inl x, completeFun_some τ θ ((PEquiv.eq_some_iff f).mp hy)⟩
      | none => exact hnu (Sum.inl ⟨y, hy⟩)
    · exact hnu (Sum.inr k)


/-- The completed permutation `σ` of `α ⊕ H`. -/
noncomputable def complete (f : PEquiv α α) (τ : Snk f ≃ Src f) (θ : ℤ ≃ Src f ⊕ H) :
    Equiv.Perm (α ⊕ H) :=
  Equiv.ofBijective _ (completeFun_bijective f τ θ)

/-- The orbits of a permutation, as a quotient type. -/
abbrev Orbits {β : Type u} (σ : Equiv.Perm β) : Type u :=
  Quotient (Equiv.Perm.SameCycle.setoid σ)

theorem complete_apply (f : PEquiv α α) (τ : Snk f ≃ Src f) (θ : ℤ ≃ Src f ⊕ H)
    (a : α ⊕ H) : complete f τ θ a = completeFun f τ θ a := rfl

/-- `σ` runs the forward `f`-chain. -/
theorem complete_pow_inl {f : PEquiv α α} (τ : Snk f ≃ Src f) (θ : ℤ ≃ Src f ⊕ H) {n : ℕ}
    {x y : α} (h : fwd f n x = some y) : (complete f τ θ ^ n) (Sum.inl x) = Sum.inl y := by
  induction n generalizing y with
  | zero => simp only [fwd_zero, Option.some.injEq] at h; simp [h]
  | succ n ih =>
    obtain ⟨z, hz, hzy⟩ := fwd_succ_eq_some h
    rw [pow_succ', Equiv.Perm.mul_apply, ih hz, complete_apply, completeFun_some τ θ hzy]

theorem nu_inl_eq {f : PEquiv α α} (θ : ℤ ≃ Src f ⊕ H) {p : ℤ} {l : Src f ⊕ H}
    (hp : θ p = l) : nu f θ l = lineEmb f (θ (p + 1)) := by
  rw [nu, ← hp, Equiv.symm_apply_apply]

/-- The point `a` is on its way from line position `j`: it is the highway point there, or on the
forward chain of the source there. -/
def OnLeg (f : PEquiv α α) (θ : ℤ ≃ Src f ⊕ H) (j : ℤ) (a : α ⊕ H) : Prop :=
  (∃ k, θ j = Sum.inr k ∧ a = Sum.inr k) ∨
    ∃ s n y, θ j = Sum.inl s ∧ fwd f n s.1 = some y ∧ a = Sum.inl y

theorem onLeg_self (f : PEquiv α α) (θ : ℤ ≃ Src f ⊕ H) (j : ℤ) :
    OnLeg f θ j (lineEmb f (θ j)) := by
  rcases h : θ j with s | k
  · exact Or.inr ⟨s, 0, s.1, h, rfl, rfl⟩
  · exact Or.inl ⟨k, h, rfl⟩

/-- The only line point on the leg from `j` is position `j` itself. -/
theorem eq_of_onLeg {f : PEquiv α α} {θ : ℤ ≃ Src f ⊕ H} {i j : ℤ}
    (h : OnLeg f θ j (lineEmb f (θ i))) : i = j := by
  rcases h with ⟨k, hj, hk⟩ | ⟨s, n, y, hj, hy, he⟩
  · have : θ i = θ j := lineEmb_injective f (by rw [hk, hj]; rfl)
    exact θ.injective this
  · rcases hi : θ i with s' | k
    · rw [hi] at he
      change Sum.inl s'.1 = Sum.inl y at he
      have hs' := Sum.inl.inj he
      cases n with
      | zero =>
        rw [fwd_zero, Option.some.injEq] at hy
        exact θ.injective (by rw [hi, hj, Subtype.ext (hs'.trans hy.symm)])
      | succ n => exact absurd (hs' ▸ s'.2) (symm_ne_none_of_fwd hy)
    · rw [hi] at he; exact absurd he Sum.inr_ne_inl

/-- One step of `σ` along a leg: stay on it, or (only past a non-divergent source) move to the
next line position. -/
theorem onLeg_step {f : PEquiv α α} (τ : Snk f ≃ Src f) (θ : ℤ ≃ Src f ⊕ H)
    (h2 : EndToStart f τ) {j : ℤ} {a : α ⊕ H} (h : OnLeg f θ j a) :
    OnLeg f θ j (complete f τ θ a) ∨
      ((∀ s : Src f, θ j = Sum.inl s → ¬ Diverges f s.1) ∧
        complete f τ θ a = lineEmb f (θ (j + 1))) := by
  rcases h with ⟨k, hj, rfl⟩ | ⟨s, n, y, hj, hy, rfl⟩
  · refine Or.inr ⟨fun s hs => (by rw [hj] at hs; cases hs), ?_⟩
    rw [complete_apply, completeFun_inr, nu_inl_eq θ hj]
  · cases hfy : f y with
    | some z =>
      refine Or.inl (Or.inr ⟨s, n + 1, z, hj, ?_, ?_⟩)
      · rw [fwd_succ, hy, Option.bind_some, hfy]
      · rw [complete_apply, completeFun_some τ θ hfy]
    | none =>
      refine Or.inr ⟨fun s' hs' hd => ?_, ?_⟩
      · rw [hj, Sum.inl.injEq] at hs'
        subst hs'
        exact hd (n + 1) (by rw [fwd_succ, hy, Option.bind_some, hfy])
      · rw [complete_apply, completeFun_none τ θ hfy, h2 s ⟨y, hfy⟩ n hy, nu_inl_eq θ hj]

/-- **Forward lemma.**  The forward orbit of line position `j` visits line positions only upward,
and never past a cut. -/
theorem reach_le {f : PEquiv α α} (τ : Snk f ≃ Src f) (θ : ℤ ≃ Src f ⊕ H)
    (h2 : EndToStart f τ) {j j' : ℤ} {n : ℕ}
    (h : (complete f τ θ ^ n) (lineEmb f (θ j)) = lineEmb f (θ j')) :
    j ≤ j' ∧ ∀ i, j ≤ i → i < j' → ∀ s : Src f, θ i = Sum.inl s → ¬ Diverges f s.1 := by
  have key : ∀ n : ℕ, ∃ i, j ≤ i ∧
      (∀ i', j ≤ i' → i' < i → ∀ s : Src f, θ i' = Sum.inl s → ¬ Diverges f s.1) ∧
      OnLeg f θ i ((complete f τ θ ^ n) (lineEmb f (θ j))) := by
    intro m
    induction m with
    | zero =>
      refine ⟨j, le_rfl, ?_, onLeg_self f θ j⟩
      intro i' h h'
      omega
    | succ m ih =>
      obtain ⟨i, hji, hcut, hleg⟩ := ih
      rw [pow_succ', Equiv.Perm.mul_apply]
      rcases onLeg_step τ θ h2 hleg with hleg' | ⟨hnc, heq⟩
      · exact ⟨i, hji, hcut, hleg'⟩
      · refine ⟨i + 1, by omega, fun i' h h' => ?_, heq ▸ onLeg_self f θ (i + 1)⟩
        rcases lt_or_eq_of_le (show i' ≤ i by omega) with hlt | rfl
        · exact hcut i' h hlt
        · exact hnc
  obtain ⟨i, hji, hcut, hleg⟩ := key n
  rw [h] at hleg
  obtain rfl := eq_of_onLeg hleg
  exact ⟨hji, hcut⟩

/-- A non-divergent source at line position `p` lies on one orbit with line position `p + 1`:
`σ` runs its finite chain and, by (H2), returns to the highway at `ν` of the source. -/
theorem sameCycle_succ_of_not_diverges (f : PEquiv α α) (τ : Snk f ≃ Src f)
    (θ : ℤ ≃ Src f ⊕ H) (h2 : EndToStart f τ) (p : ℤ)
    (hp : ∀ s : Src f, θ p = Sum.inl s → ¬ Diverges f s.1) :
    (complete f τ θ).SameCycle (lineEmb f (θ p)) (lineEmb f (θ (p + 1))) := by
  rcases hθ : θ p with s | k
  · have hfin : ∃ n, fwd f n s.1 = none := by
      by_contra! hd; exact hp s hθ hd
    obtain ⟨m, t, ht, hft⟩ := exists_last hfin
    refine ⟨((m + 1 : ℕ) : ℤ), ?_⟩
    rw [zpow_natCast, pow_succ', Equiv.Perm.mul_apply]
    change complete f τ θ ((complete f τ θ ^ m) (Sum.inl s.1)) = _
    rw [complete_pow_inl τ θ ht, complete_apply, completeFun_none τ θ hft,
      h2 s ⟨t, hft⟩ m ht, nu_inl_eq θ hθ]
  · exact ⟨1, nu_inl_eq θ hθ⟩

/-- A divergent source at line position `p` is a cut: positions `≤ p` and `> p` lie on different
orbits.  Needs (H1) and (H2). -/
theorem not_sameCycle_of_cut (f : PEquiv α α) (τ : Snk f ≃ Src f) (θ : ℤ ≃ Src f ⊕ H)
    (_h1 : NoBiInfinite f) (h2 : EndToStart f τ) (s : Src f) (hs : Diverges f s.1) {p q r : ℤ}
    (hp : θ p = Sum.inl s) (hq : q ≤ p) (hr : p < r) :
    ¬ (complete f τ θ).SameCycle (lineEmb f (θ q)) (lineEmb f (θ r)) := by
  rintro ⟨k, hk⟩
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · rw [zpow_natCast] at hk
    exact (reach_le τ θ h2 hk).2 p hq hr s hp hs
  · rw [zpow_neg, zpow_natCast, Equiv.Perm.inv_eq_iff_eq] at hk
    have := (reach_le τ θ h2 hk.symm).1
    omega

/-- **Anchors.**  Under (H1), every point lies on the orbit of some line position. -/
theorem exists_sameCycle_lineEmb {f : PEquiv α α} (τ : Snk f ≃ Src f) (θ : ℤ ≃ Src f ⊕ H)
    (h1 : NoBiInfinite f) (a : α ⊕ H) :
    ∃ j, (complete f τ θ).SameCycle (lineEmb f (θ j)) a := by
  rcases a with x | k
  · by_cases hb : ∃ n, fwd f.symm n x = none
    · obtain ⟨m, s, hs, hfs⟩ := exists_last hb
      have hx : fwd f m s = some x := fwd_symm hs
      refine ⟨θ.symm (Sum.inl ⟨s, hfs⟩), m, ?_⟩
      rw [zpow_natCast, θ.apply_symm_apply]
      exact complete_pow_inl τ θ hx
    by_cases hf : ∃ n, fwd f n x = none
    · obtain ⟨m, t, ht, hft⟩ := exists_last hf
      refine ⟨θ.symm (Sum.inl (τ ⟨t, hft⟩)) + 1, Equiv.Perm.SameCycle.symm ?_⟩
      refine ⟨((m + 1 : ℕ) : ℤ), ?_⟩
      rw [zpow_natCast, pow_succ', Equiv.Perm.mul_apply, complete_pow_inl τ θ ht, complete_apply,
        completeFun_none τ θ hft]
      rfl
    push Not at hb hf
    exfalso
    let F : ℕ → α := fun n => (fwd f n x).get (Option.isSome_iff_ne_none.mpr (hf n))
    let Bk : ℕ → α := fun n => (fwd f.symm n x).get (Option.isSome_iff_ne_none.mpr (hb n))
    have hF : ∀ n, fwd f n x = some (F n) := fun n => (Option.some_get _).symm
    have hBk : ∀ n, fwd f.symm n x = some (Bk n) := fun n => (Option.some_get _).symm
    let g : ℤ → α := fun i => if 0 ≤ i then F i.toNat else Bk (-i).toNat
    have gnat : ∀ n : ℕ, g n = F n := fun n => by simp [g]
    have g0 : g 0 = F 0 := by simpa using gnat 0
    have gneg : ∀ n : ℕ, g (-(n : ℤ)) = Bk n := by
      intro n
      cases n with
      | zero =>
        have h0 := hF 0; have h0' := hBk 0
        rw [fwd_zero, Option.some.injEq] at h0 h0'
        rw [Nat.cast_zero, neg_zero, g0, ← h0, ← h0']
      | succ n => simp only [g]; rw [if_neg (by omega)]; congr
    refine h1 g fun i => ?_
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg i
    · rw [gnat, show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; rfl, gnat, ← hF (n + 1),
        fwd_succ, hF n, Option.bind_some]
    · cases n with
      | zero =>
        rw [Nat.cast_zero, neg_zero, zero_add, g0, show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl, gnat,
          ← hF 1, fwd_succ, hF 0, Option.bind_some]
      | succ n =>
        rw [show -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) by push_cast; ring, gneg, gneg]
        have := hBk (n + 1)
        rw [fwd_succ, hBk n, Option.bind_some] at this
        exact (PEquiv.eq_some_iff f).mp this
  · refine ⟨θ.symm (Sum.inr k), ?_⟩
    rw [θ.apply_symm_apply]
    exact Equiv.Perm.SameCycle.refl _ _

/-- A cut-free stretch of the line lies on one orbit. -/
theorem sameCycle_of_noCut {f : PEquiv α α} (τ : Snk f ≃ Src f) (θ : ℤ ≃ Src f ⊕ H)
    (h2 : EndToStart f τ) {q r : ℤ} (hqr : q ≤ r)
    (h : ∀ i, q ≤ i → i < r → ∀ s : Src f, θ i = Sum.inl s → ¬ Diverges f s.1) :
    (complete f τ θ).SameCycle (lineEmb f (θ q)) (lineEmb f (θ r)) := by
  induction r, hqr using Int.leInduction with
  | base => exact Equiv.Perm.SameCycle.refl _ _
  | succ r hqr ih =>
    exact (ih fun i hi hi' => h i hi (by omega)).trans
      (sameCycle_succ_of_not_diverges f τ θ h2 r (h r hqr (by omega)))

theorem lineEmb_symm_inl (f : PEquiv α α) (θ : ℤ ≃ Src f ⊕ H) (s : Src f) :
    lineEmb f (θ (θ.symm (Sum.inl s))) = Sum.inl s.1 := by
  rw [θ.apply_symm_apply]; rfl

/-- **Lemma C, orbit formula.**  Under (H1) and (H2), the number of orbits of the completion is
one more than the number of forward-divergent sources (as cardinals, so `1 + ℵ₀ = ℵ₀` covers the
infinite case). -/
theorem card_orbits (f : PEquiv α α) (τ : Snk f ≃ Src f) (θ : ℤ ≃ Src f ⊕ H)
    (h1 : NoBiInfinite f) (h2 : EndToStart f τ) :
    Cardinal.mk (Orbits (complete f τ θ)) = 1 + Cardinal.mk {s : Src f // Diverges f s.1} := by
  set σ := complete f τ θ
  let D := {s : Src f // Diverges f s.1}
  let φ : D → Orbits σ := fun d => Quotient.mk _ (Sum.inl d.1.1)
  have hφ : Function.Injective φ := by
    intro d e hde
    have hsc : σ.SameCycle (Sum.inl d.1.1) (Sum.inl e.1.1) := Quotient.exact hde
    rw [← lineEmb_symm_inl f θ d.1, ← lineEmb_symm_inl f θ e.1] at hsc
    rcases lt_trichotomy (θ.symm (Sum.inl d.1)) (θ.symm (Sum.inl e.1)) with hlt | heq | hgt
    · exact absurd hsc (not_sameCycle_of_cut f τ θ h1 h2 d.1 d.2 (θ.apply_symm_apply _) le_rfl hlt)
    · exact Subtype.ext (Sum.inl.inj (θ.symm.injective heq))
    · exact absurd hsc.symm
        (not_sameCycle_of_cut f τ θ h1 h2 e.1 e.2 (θ.apply_symm_apply _) le_rfl hgt)
  -- An orbit with no cut swallows every line position above one of its own.
  have hup : ∀ j, Quotient.mk _ (lineEmb f (θ j)) ∉ Set.range φ →
      ∀ k, j ≤ k → σ.SameCycle (lineEmb f (θ j)) (lineEmb f (θ k)) := by
    intro j hj k hjk
    induction k, hjk using Int.leInduction with
    | base => exact Equiv.Perm.SameCycle.refl _ _
    | succ k hjk ih =>
      refine ih.trans (sameCycle_succ_of_not_diverges f τ θ h2 k fun s hs hd => hj ⟨⟨s, hd⟩, ?_⟩)
      refine Quotient.sound (Equiv.Perm.SameCycle.symm ?_)
      rw [hs] at ih
      exact ih
  have hsub : Subsingleton ((Set.range φ)ᶜ : Set (Orbits σ)) := by
    constructor
    rintro ⟨o, ho⟩ ⟨o', ho'⟩
    induction o using Quotient.inductionOn with | h a => ?_
    induction o' using Quotient.inductionOn with | h b => ?_
    obtain ⟨j, hj⟩ := exists_sameCycle_lineEmb τ θ h1 a
    obtain ⟨j', hj'⟩ := exists_sameCycle_lineEmb τ θ h1 b
    have ea : Quotient.mk _ a = Quotient.mk (Equiv.Perm.SameCycle.setoid σ) (lineEmb f (θ j)) :=
      Quotient.sound hj.symm
    have eb : Quotient.mk _ b = Quotient.mk (Equiv.Perm.SameCycle.setoid σ) (lineEmb f (θ j')) :=
      Quotient.sound hj'.symm
    have hoa : Quotient.mk _ (lineEmb f (θ j)) ∉ Set.range φ := by rw [← ea]; exact ho
    have hob : Quotient.mk _ (lineEmb f (θ j')) ∉ Set.range φ := by rw [← eb]; exact ho'
    apply Subtype.ext
    show Quotient.mk _ a = Quotient.mk _ b
    rw [ea, eb]
    rcases le_total j j' with h | h
    · exact Quotient.sound (hup j hoa j' h)
    · exact (Quotient.sound (hup j' hob j h)).symm
  have hsum := Cardinal.mk_sum_compl (Set.range φ)
  rw [Cardinal.mk_range_eq φ hφ] at hsum
  rw [← hsum]
  rcases finite_or_infinite D with hfin | hinf
  · have hne : Nonempty ((Set.range φ)ᶜ : Set (Orbits σ)) := by
      obtain ⟨M, hM⟩ := (Set.finite_range fun d : D => θ.symm (Sum.inl d.1)).bddAbove
      refine ⟨⟨Quotient.mk _ (lineEmb f (θ (M + 1))), ?_⟩⟩
      rintro ⟨d, hd⟩
      have hsc : σ.SameCycle (Sum.inl d.1.1) (lineEmb f (θ (M + 1))) := Quotient.exact hd
      rw [← lineEmb_symm_inl f θ d.1] at hsc
      have : θ.symm (Sum.inl d.1) ≤ M := hM ⟨d, rfl⟩
      exact not_sameCycle_of_cut f τ θ h1 h2 d.1 d.2 (θ.apply_symm_apply _) le_rfl (by omega) hsc
    rw [Cardinal.eq_one_iff_unique.mpr ⟨hsub, hne⟩, add_comm]
  · have h := Cardinal.infinite_iff.mp hinf
    have h' : (1 : Cardinal) ≤ Cardinal.mk D := Cardinal.one_le_aleph0.trans h
    rw [Cardinal.add_eq_left h ((Cardinal.le_one_iff_subsingleton.mpr hsub).trans h'),
      Cardinal.add_eq_right h h']

/-- One orbit iff no source diverges. -/
theorem sameCycle_all_iff (f : PEquiv α α) (τ : Snk f ≃ Src f) (θ : ℤ ≃ Src f ⊕ H)
    (h1 : NoBiInfinite f) (h2 : EndToStart f τ) :
    (∀ a b : α ⊕ H, (complete f τ θ).SameCycle a b) ↔ ∀ s : Src f, ¬ Diverges f s.1 := by
  constructor
  · intro hall s hs
    exact not_sameCycle_of_cut f τ θ h1 h2 s hs (θ.apply_symm_apply _) le_rfl
      (lt_add_one _) (hall _ _)
  · intro hno a b
    obtain ⟨j, hj⟩ := exists_sameCycle_lineEmb τ θ h1 a
    obtain ⟨j', hj'⟩ := exists_sameCycle_lineEmb τ θ h1 b
    have hline : ∀ q r, q ≤ r →
        (complete f τ θ).SameCycle (lineEmb f (θ q)) (lineEmb f (θ r)) :=
      fun q r hqr => sameCycle_of_noCut τ θ h2 hqr fun i _ _ s _ => hno s
    rcases le_total j j' with h | h
    · exact hj.symm.trans ((hline j j' h).trans hj')
    · exact hj.symm.trans ((hline j' j h).symm.trans hj')

/-- Infinitely many orbits iff infinitely many sources diverge. -/
theorem infinite_orbits_iff (f : PEquiv α α) (τ : Snk f ≃ Src f) (θ : ℤ ≃ Src f ⊕ H)
    (h1 : NoBiInfinite f) (h2 : EndToStart f τ) :
    Infinite (Orbits (complete f τ θ)) ↔ Infinite {s : Src f // Diverges f s.1} := by
  rw [Cardinal.infinite_iff, Cardinal.infinite_iff, card_orbits f τ θ h1 h2]
  constructor
  · intro h
    by_contra h'
    exact absurd h (not_le.mpr (Cardinal.add_lt_aleph0 Cardinal.one_lt_aleph0 (not_le.mp h')))
  · intro h
    exact h.trans (self_le_add_left _ _)

/-- **The `{1, ∞}` dichotomy.**  If divergent sources, when present, are infinitely many (the
junk multiplicity of the concrete encoding), the completion has one orbit or infinitely many;
it has one orbit exactly when no source diverges. -/
theorem one_or_infinite_orbits (f : PEquiv α α) (τ : Snk f ≃ Src f) (θ : ℤ ≃ Src f ⊕ H)
    (h1 : NoBiInfinite f) (h2 : EndToStart f τ)
    (hjunk : (∃ s : Src f, Diverges f s.1) → Infinite {s : Src f // Diverges f s.1}) :
    ((∀ a b : α ⊕ H, (complete f τ θ).SameCycle a b) ∧ ∀ s : Src f, ¬ Diverges f s.1) ∨
      (Infinite (Orbits (complete f τ θ)) ∧ ∃ s : Src f, Diverges f s.1) := by
  by_cases h : ∃ s : Src f, Diverges f s.1
  · exact Or.inr ⟨(infinite_orbits_iff f τ θ h1 h2).mpr (hjunk h), h⟩
  · push Not at h
    exact Or.inl ⟨(sameCycle_all_iff f τ θ h1 h2).mpr h, h⟩

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
