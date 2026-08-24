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

`finite_acyclicParadoxical_imp_noDivergent : FiniteAcyclicParadoxical → NoDivergentOrbit` is
the intended derived implication, now **fully proved** modulo the single cited axiom
(`#print axioms` = trust base + `rozier_terracol_3_2`, no `sorry`).  It routes through
`diverges_imp_infinite_acyclicParadoxical`, the Front-A specialization the project doc flags as
owed, assembled here from: the running-minimum lemma (`exists_standardStop_of_diverges`), the
shortcut embedding (`tstep_iterate_eq_step_iterate`, `infiniteStoppingTime_of_diverges`), and
acyclicity (`not_tstep_fixed_of_diverges` via the standard↔shortcut peak invariant
`step_le_shortcut`): a divergent orbit's blow-ups `2^k m₀` still diverge, hence cannot close a
shortcut cycle, so each paradoxical segment is strictly acyclic; unboundedly large distinct
starts give an infinite set.

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

/-- **[ASSUMED — THEOREM-grade]** Rozier--Terracol 2026, Theorem 3.2 (constructive form).  An
integer `n ≥ 2` of infinite shortcut stopping time yields, for every bound `K`, a paradoxical
segment whose start `2^k n` exceeds `K` — i.e. *unboundedly large* paradoxical starts of the
form `2^k n`.  This is the paper's actual construction (starts `2^k n`, using infinitely many
left approximations `3^a/2^b < 1` of `1`), not merely "infinitely many somewhere".

Provenance: Rozier & Terracol, *Paradoxical behavior in Collatz sequences*, Discrete
Mathematics 349 (2026), 115167 (arXiv:2502.00948v5), Theorem 3.2 and Corollary 3.3.  Stated in
repository notation; the paper's `Paradoxical` definition matches `FrontA.Paradoxical`.
`NoDivergentOrbit` is not packaged in; acyclicity is derived below from the extra `Diverges`
hypothesis (a cycle minimum also has infinite stopping time, so infinite stopping alone would
give *cyclic* segments). -/
axiom rozier_terracol_3_2 (n : ℕ) (h2 : 2 ≤ n) (hstop : InfiniteStoppingTime n) :
    ∀ K, ∃ k m, K < 2 ^ k * n ∧ Paradoxical (2 ^ k * n) m

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

/-- Halving `k` times reaches the base: `step^[k] (2^k * x) = x`. -/
theorem step_iterate_two_pow_mul (x k : ℕ) : step^[k] (2 ^ k * x) = x := by
  induction k with
  | zero => simp
  | succ i ih =>
    have hstep : step (2 ^ (i + 1) * x) = 2 ^ i * x := by
      have h2 : 2 ^ (i + 1) * x = 2 * (2 ^ i * x) := by rw [pow_succ]; ring
      rw [h2]; unfold step
      rw [if_pos (by omega), Nat.mul_div_cancel_left _ (by norm_num)]
    rw [Function.iterate_succ_apply, hstep, ih]

/-- A divergent orbit's `2^k`-fold blow-up still diverges. -/
theorem diverges_two_pow_mul {x : ℕ} (hx : Diverges x) (k : ℕ) : Diverges (2 ^ k * x) := by
  intro M
  obtain ⟨i, hi⟩ := hx M
  refine ⟨i + k, ?_⟩
  rw [Function.iterate_add_apply, step_iterate_two_pow_mul]
  exact hi

/-- **Standard ↔ shortcut invariant.**  Every standard iterate is either a shortcut iterate or
the odd peak `3·(shortcut iterate)+1` sitting just before its halving; in particular it is
`≤ 3·(some shortcut iterate) + 1`. -/
theorem step_le_shortcut (s i : ℕ) : ∃ j, step^[i] s ≤ 3 * tstep^[j] s + 1 := by
  have epeak : ∀ x : ℕ, x % 2 = 1 → step (3 * x + 1) = tstep x := by
    intro x hx
    unfold step tstep
    rw [if_pos (by omega), if_neg (by omega)]
  suffices h : ∀ i, ∃ j,
      step^[i] s = tstep^[j] s ∨ (tstep^[j] s % 2 = 1 ∧ step^[i] s = 3 * tstep^[j] s + 1) by
    obtain ⟨j, hj⟩ := h i
    exact ⟨j, by rcases hj with h | ⟨_, h⟩ <;> omega⟩
  intro i
  induction i with
  | zero => exact ⟨0, Or.inl rfl⟩
  | succ p ih =>
    obtain ⟨j, hj⟩ := ih
    rcases hj with h | ⟨hodd, h⟩
    · rcases Nat.even_or_odd (tstep^[j] s) with he | ho
      · -- x even: step x = x/2 = tstep x
        refine ⟨j + 1, Or.inl ?_⟩
        rw [Function.iterate_succ_apply', h, Function.iterate_succ_apply',
          ← tstep_eq_step (Nat.even_iff.mp he)]
      · -- x odd: step x = 3x+1 (the peak)
        refine ⟨j, Or.inr ⟨Nat.odd_iff.mp ho, ?_⟩⟩
        rw [Function.iterate_succ_apply', h]
        unfold step; rw [if_neg (by simp [Nat.odd_iff.mp ho])]
    · -- step^[p] s = 3x+1 with x odd; step(3x+1) = tstep x = tstep^[j+1] s
      refine ⟨j + 1, Or.inl ?_⟩
      rw [Function.iterate_succ_apply', h, epeak _ hodd, Function.iterate_succ_apply']

/-- A divergent orbit is not eventually shortcut-periodic: `tstep^[m] s ≠ s` for `m > 0`. -/
theorem not_tstep_fixed_of_diverges {s : ℕ} (hdiv : Diverges s) {m : ℕ} (hm : 0 < m)
    (hfix : tstep^[m] s = s) : False := by
  -- shortcut orbit is periodic with period m, hence bounded by `Mc`
  set Mc : ℕ := (Finset.range m).sup (fun l => tstep^[l] s) with hMc
  have hper : ∀ j, tstep^[j] s ≤ Mc := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      rcases lt_or_ge j m with hlt | hge
      · exact Finset.le_sup (f := fun l => tstep^[l] s) (Finset.mem_range.mpr hlt)
      · have : tstep^[j] s = tstep^[j - m] s := by
          conv_lhs => rw [← Nat.sub_add_cancel hge, Function.iterate_add_apply, hfix]
        rw [this]; exact ih _ (by omega)
  -- then the standard orbit is bounded by 3*Mc+1, contradicting divergence
  obtain ⟨i, hi⟩ := hdiv (3 * Mc + 2)
  obtain ⟨j, hj⟩ := step_le_shortcut s i
  have := hper j
  omega

/-- **Front-A specialization (proved).**  A divergent standard-step orbit yields infinitely many
*acyclic* paradoxical segments: apply `Assumed.rozier_terracol_3_2` to the infinite-stopping
value `m₀`, then upgrade each paradoxical `2^k m₀` to acyclic — its orbit still diverges, so it
cannot close a shortcut cycle. -/
theorem diverges_imp_infinite_acyclicParadoxical (n : ℕ) (hn : 1 ≤ n) (hdiv : Diverges n) :
    {p : ℕ × ℕ | AcyclicParadoxical p.1 p.2}.Infinite := by
  obtain ⟨m₀, h2, hstop, hdivm⟩ := infiniteStoppingTime_of_diverges hn hdiv
  have himg : (Prod.fst '' {p : ℕ × ℕ | AcyclicParadoxical p.1 p.2}).Infinite := by
    apply Set.infinite_of_not_bddAbove
    rintro ⟨B, hB⟩
    obtain ⟨k, m, hlt, hpar⟩ := Assumed.rozier_terracol_3_2 m₀ h2 hstop B
    obtain ⟨hs2, hm, hsub, hle⟩ := hpar
    have hdivs : Diverges (2 ^ k * m₀) := diverges_two_pow_mul hdivm k
    have hne : tstep^[m] (2 ^ k * m₀) ≠ 2 ^ k * m₀ := fun h =>
      not_tstep_fixed_of_diverges hdivs hm h
    have hacyc : AcyclicParadoxical (2 ^ k * m₀) m :=
      ⟨hs2, hm, hsub, lt_of_le_of_ne hle (fun h => hne h.symm)⟩
    have hmem : 2 ^ k * m₀ ∈ Prod.fst '' {p : ℕ × ℕ | AcyclicParadoxical p.1 p.2} :=
      ⟨(2 ^ k * m₀, m), hacyc, rfl⟩
    exact absurd (hB hmem) (by omega)
  exact himg.of_image

/-- **The Front-A consumption theorem**: only finitely many acyclic paradoxical segments
implies no divergent orbit.  (Conditional reduction — see the strength caveat in the module
docstring.) -/
theorem finite_acyclicParadoxical_imp_noDivergent
    (hfin : FiniteAcyclicParadoxical) : NoDivergentOrbit := by
  intro n hn hdiv
  exact (diverges_imp_infinite_acyclicParadoxical n hn hdiv).not_finite hfin

end CollatzMoonshot
