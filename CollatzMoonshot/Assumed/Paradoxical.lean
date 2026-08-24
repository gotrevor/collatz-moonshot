/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.FrontA.Paradoxical

/-!
# Assumed: Rozier--Terracol 2026, Theorem 3.2 (paradoxical segments from infinite stopping time)

Tier: **THEOREM-grade** — published, peer-reviewed (Olivier Rozier and Claude Terracol,
*Paradoxical behavior in Collatz sequences*, Discrete Mathematics 349 (2026), 115167;
arXiv:2502.00948v5).  Represented here by a narrow, provenance-documented axiom, per the repo's
Assumed policy: a published theorem may stand as an axiom rather than be re-formalized.

## What the axiom says (the paper's actual statement)

An integer `n ≥ 2` whose **shortcut stopping time is infinite** — `tstep^[j] n ≥ n` for every
`j` — produces **infinitely many paradoxical segments** (Theorem 3.2; the construction uses the
starts `2^k n` and infinitely many left approximations `3^a / 2^b < 1` of `1`).  The
`Paradoxical` predicate is exactly the paper's definition rendered in repository notation
(`CollatzMoonshot/FrontA/Paradoxical.lean`).  `NoDivergentOrbit` is **not** packaged into the
axiom — the Front-A consumption is derived separately below.

## The Front-A wiring

`finite_acyclicParadoxical_imp_noDivergent` is the intended derived implication
`FiniteAcyclicParadoxical → NoDivergentOrbit`.  It routes through one disclosed intermediate,
`diverges_imp_infinite_acyclicParadoxical`, which is the Front-A *specialization* the project
doc flags as owed: a divergent standard orbit is nonrepeating, has a tail value of infinite
shortcut stopping time, and its constructed segments cannot close cyclically, so they are
*acyclic* — this last step is a derived specialization of the paper, not its verbatim
statement, and is left as a scoped `sorry` (standard/shortcut bridge + acyclicity).

**Strength caveat (mandatory).** `FiniteAcyclicParadoxical` is a *sufficient* hypothesis for
Front A, and its own truth (global finiteness of paradoxical segments, Rozier--Terracol
Conjecture 6.1) is **stronger than the full Collatz conjecture**.  This wiring is therefore a
conditional reduction, not an easier route; it is BASELINE Front-A plumbing, and the novel
content of the project lives in the discovery lemmas (`headBlock_not_acyclicParadoxical`, the
`≥3` odd-blocks finding), not here.
-/

namespace CollatzMoonshot

open CollatzMoonshot.FrontB CollatzMoonshot.FrontA

/-- `n` has **infinite shortcut stopping time**: its accelerated orbit never drops below `n`
(`tstep^[j] n ≥ n` for all `j`).  This is Rozier--Terracol's hypothesis for Theorem 3.2. -/
def InfiniteStoppingTime (n : ℕ) : Prop := ∀ j, n ≤ tstep^[j] n

/-- There are only finitely many acyclic paradoxical segments (pairs `(start, length)`).  This
is the Front-A sufficient condition; its truth is Rozier--Terracol Conjecture 6.1, stronger
than Collatz. -/
def FiniteAcyclicParadoxical : Prop :=
  {p : ℕ × ℕ | AcyclicParadoxical p.1 p.2}.Finite

namespace Assumed

/-- **[ASSUMED — THEOREM-grade]** Rozier--Terracol 2026, Theorem 3.2.  An integer `n ≥ 2` of
infinite shortcut stopping time yields infinitely many paradoxical segments.

Provenance: Rozier & Terracol, *Paradoxical behavior in Collatz sequences*, Discrete
Mathematics 349 (2026), 115167 (arXiv:2502.00948v5), Theorem 3.2 and Corollary 3.3.  Stated in
repository notation; the paper's `Paradoxical` definition matches `FrontA.Paradoxical`. -/
axiom rozier_terracol_3_2 (n : ℕ) (h2 : 2 ≤ n) (hstop : InfiniteStoppingTime n) :
    {p : ℕ × ℕ | Paradoxical p.1 p.2}.Infinite

end Assumed

/-- **Running-minimum lemma (proved).**  A divergent standard orbit has a least value `m₀`,
and from `m₀` the orbit never drops below `m₀` (infinite *standard* stopping time); moreover
`m₀ ≥ 2` and `m₀` itself diverges.  This is the first half of the standard/shortcut bridge:
it produces the value Rozier--Terracol Theorem 3.2 is applied to. -/
theorem exists_standardStop_of_diverges {n : ℕ} (hn : 1 ≤ n) (hdiv : Diverges n) :
    ∃ m₀, 2 ≤ m₀ ∧ (∀ j, m₀ ≤ step^[j] m₀) ∧ Diverges m₀ := by
  -- the orbit value set and its infimum
  set S : Set ℕ := Set.range (fun k => step^[k] n) with hS
  have hne : S.Nonempty := ⟨n, 0, rfl⟩
  set m₀ := sInf S with hm₀
  have hmem : m₀ ∈ S := Nat.sInf_mem hne
  obtain ⟨k₀, hk₀⟩ := hmem
  -- infinite standard stopping time at m₀
  have hstop : ∀ j, m₀ ≤ step^[j] m₀ := by
    intro j
    have : step^[j] m₀ = step^[j + k₀] n := by
      rw [← hk₀, Function.iterate_add_apply]
    rw [this]
    exact Nat.sInf_le ⟨j + k₀, rfl⟩
  -- prefix bound
  set B : ℕ := (Finset.range k₀).sup (fun i => step^[i] n) with hB
  have hprefix : ∀ i, i < k₀ → step^[i] n ≤ B := by
    intro i hi
    exact Finset.le_sup (f := fun i => step^[i] n) (Finset.mem_range.mpr hi)
  -- m₀ diverges (its tail inherits n's unbounded values)
  have hdivm : Diverges m₀ := by
    intro M
    obtain ⟨k, hk⟩ := hdiv (max M (B + 1))
    have hkge : k₀ ≤ k := by
      by_contra hlt
      push_neg at hlt
      have := hprefix k hlt
      omega
    refine ⟨k - k₀, ?_⟩
    have : step^[k - k₀] m₀ = step^[k] n := by
      rw [← hk₀, ← Function.iterate_add_apply, Nat.sub_add_cancel hkge]
    rw [this]; omega
  -- m₀ ≥ 2: m₀ ≥ 1 (positivity) and m₀ ≠ 1 (a divergent orbit cannot sit at 1)
  have hm1 : 1 ≤ m₀ := by rw [← hk₀]; exact iterate_step_pos hn k₀
  have hne1 : m₀ ≠ 1 := by
    intro h1
    -- Diverges m₀ with m₀ = 1 is impossible: orbit of 1 is ≤ 4
    obtain ⟨k, hk⟩ := hdivm 5
    have hb : ∀ i, step^[i] (1 : ℕ) = 1 ∨ step^[i] (1 : ℕ) = 2 ∨ step^[i] (1 : ℕ) = 4 := by
      intro i
      induction i with
      | zero => left; rfl
      | succ j ih =>
        rw [Function.iterate_succ_apply']
        rcases ih with h | h | h <;> rw [h] <;> decide
    rw [h1] at hk
    rcases hb k with h | h | h <;> rw [h] at hk <;> omega
  exact ⟨m₀, by omega, hstop, hdivm⟩

/-- **Shortcut embedding.**  Each accelerated iterate is some standard iterate: one `tstep` is
either one `step` (even) or two `step`s (odd). -/
theorem tstep_iterate_eq_step_iterate (x j : ℕ) : ∃ k, tstep^[j] x = step^[k] x := by
  induction j with
  | zero => exact ⟨0, rfl⟩
  | succ i ih =>
    obtain ⟨k, hk⟩ := ih
    rw [Function.iterate_succ_apply', hk]
    rcases Nat.even_or_odd (step^[k] x) with he | ho
    · exact ⟨k + 1, by rw [tstep_eq_step (Nat.even_iff.mp he), Function.iterate_succ_apply']⟩
    · exact ⟨k + 2, by
        rw [tstep_eq_step_step (Nat.odd_iff.mp ho), Function.iterate_succ_apply',
          Function.iterate_succ_apply']⟩

/-- **Second half of the bridge (proved).**  A divergent orbit yields a value `m₀ ≥ 2` of
infinite *shortcut* stopping time that still diverges — exactly Rozier--Terracol's hypothesis.
Combines `exists_standardStop_of_diverges` with the shortcut embedding. -/
theorem infiniteStoppingTime_of_diverges {n : ℕ} (hn : 1 ≤ n) (hdiv : Diverges n) :
    ∃ m₀, 2 ≤ m₀ ∧ InfiniteStoppingTime m₀ ∧ Diverges m₀ := by
  obtain ⟨m₀, h2, hstop, hdivm⟩ := exists_standardStop_of_diverges hn hdiv
  refine ⟨m₀, h2, ?_, hdivm⟩
  intro j
  obtain ⟨k, hk⟩ := tstep_iterate_eq_step_iterate m₀ j
  rw [hk]; exact hstop k

/-- **Front-A specialization (owed).**  A divergent standard-step orbit yields infinitely many
*acyclic* paradoxical segments.  This combines `Assumed.rozier_terracol_3_2` with (i) the
standard/shortcut iterate bridge that turns divergence into a tail value of infinite shortcut
stopping time, and (ii) the observation that a divergent (hence acyclic) orbit's constructed
segments cannot close cyclically.  Disclosed `sorry`: this derived specialization is the scoped
arithmetic bridge, not the cited axiom. -/
theorem diverges_imp_infinite_acyclicParadoxical (n : ℕ) (hn : 1 ≤ n) (hdiv : Diverges n) :
    {p : ℕ × ℕ | AcyclicParadoxical p.1 p.2}.Infinite := by
  sorry

/-- **The Front-A consumption theorem**: only finitely many acyclic paradoxical segments
implies no divergent orbit.  (Conditional reduction — see the strength caveat in the module
docstring.) -/
theorem finite_acyclicParadoxical_imp_noDivergent
    (hfin : FiniteAcyclicParadoxical) : NoDivergentOrbit := by
  intro n hn hdiv
  exact (diverges_imp_infinite_acyclicParadoxical n hn hdiv).not_finite hfin

end CollatzMoonshot
