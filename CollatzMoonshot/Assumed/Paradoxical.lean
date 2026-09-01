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
`j` — produces **infinitely many paradoxical segments** starting at numbers `2^k n` (Theorem
3.2).  Rendered here as: the set of pairs `(k, m)` with `Paradoxical (2^k n) m` is infinite.  The
`Paradoxical` predicate is exactly the paper's definition rendered in repository notation
(`CollatzMoonshot/FrontA/Paradoxical.lean`).  `NoDivergentOrbit` is **not** packaged into the
axiom — the Front-A consumption is derived separately below.

## ⚠️ Fidelity correction, 2026-09-01 (machine-checked)

Until this date the axiom read *"for every bound `K` there are `k, m` with `K < 2^k n` and
`Paradoxical (2^k n) m"* — **unboundedly large** starts.  That is strictly stronger than the
published theorem, and provably so: from a start `2^k n` the shortcut orbit first halves down
to `n` and then follows `n`'s own orbit, so if that orbit is *bounded* no segment from `2^k n`
can return to its start once `2^k n` exceeds the bound.  A nontrivial cycle's minimum has
infinite shortcut stopping time and a bounded orbit, so the old form **implies
`NoNontrivialCycle`** — an open problem, not implied by any published theorem.  That derivation
is a theorem of this file (`noNontrivialCycle_of_unboundedParadoxicalStarts`, trust-base clean),
kept as a permanent regression guard; the discarded reading is named
`UnboundedParadoxicalStarts` so it can be refuted rather than assumed.

The repaired cardinality form is *not* vacuous in the same configuration:
`infinite_paradoxical_of_tstep_cycle` proves (again trust-base clean) that a shortcut cycle
through `n > 2` does deliver infinitely many paradoxical segments starting at `2^0 n = n`.

## The Front-A wiring

`finite_acyclicParadoxical_imp_noDivergent : FiniteAcyclicParadoxical → NoDivergentOrbit` is
the intended derived implication, now **fully proved** modulo the single cited axiom
(`#print axioms` = trust base + `rozier_terracol_3_2`, no `sorry`).  It routes through
`diverges_imp_infinite_acyclicParadoxical`, the Front-A specialization the project doc flags as
owed, assembled here from: the running-minimum lemma (`exists_standardStop_of_diverges`), the
shortcut embedding (`tstep_iterate_eq_step_iterate`, `infiniteStoppingTime_of_diverges`), and
acyclicity (`not_tstep_fixed_of_diverges` via the standard↔shortcut peak invariant
`step_le_shortcut`): a divergent orbit's blow-ups `2^k m₀` still diverge, hence cannot close a
shortcut cycle, so each paradoxical segment is strictly acyclic; the injection
`(k, m) ↦ (2^k m₀, m)` then carries the axiom's infinite pair set into the acyclic set.  Only
the **cardinality** of that set is used — never any growth of its starts.

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
infinite shortcut stopping time produces **infinitely many** paradoxical segments starting at
numbers of the form `2^k n`: the set of pairs `(k, m)` with `Paradoxical (2^k n) m` is infinite.

Provenance: Rozier & Terracol, *Paradoxical behavior in Collatz sequences*, Discrete
Mathematics 349 (2026), 115167 (arXiv:2502.00948v5), Theorem 3.2 and Corollary 3.3
(`papers/rozier-terracol-2026-paradoxical-summary.md`: "any `n ≥ 2` with infinite stopping time
(`T^j(n) ≥ n` for all `j`) produces infinitely many paradoxical segments starting at numbers
`2^k n`").  Stated in repository notation; the paper's `Paradoxical` definition matches
`FrontA.Paradoxical`.  `NoDivergentOrbit` is not packaged in; acyclicity is derived below from
the extra `Diverges` hypothesis (a cycle minimum also has infinite stopping time, so infinite
stopping alone would give *cyclic* segments).

⚠️ **FIDELITY NOTE (2026-09-01, corrected).**  An earlier rendering of this axiom read
"*for every bound `K` there is a paradoxical start `2^k n > K`*", i.e. **unboundedly large**
starts.  That reading is strictly stronger than the published theorem: it is refuted by any
nontrivial cycle, hence it *proves* `NoNontrivialCycle` — an open problem — all by itself.
The refutation is machine-checked immediately below
(`noNontrivialCycle_of_unboundedParadoxicalStarts`); do **not** restore the old form.  Cardinality
of the segment set, not growth of its starts, is what Theorem 3.2 delivers. -/
axiom rozier_terracol_3_2 (n : ℕ) (h2 : 2 ≤ n) (hstop : InfiniteStoppingTime n) :
    {p : ℕ × ℕ | Paradoxical (2 ^ p.1 * n) p.2}.Infinite

end Assumed

/-!
## Fidelity guard: why the axiom states *cardinality*, not *unbounded starts*

Everything in this section is sorry-free and axiom-free (trust base only).  It exists to pin,
in the kernel, the exact reason the axiom above may not be strengthened to "unboundedly large
paradoxical starts `2^k n`": that strengthening settles the cycle front for free, so it is not
a faithful rendering of Rozier--Terracol Theorem 3.2.
-/

/-- Halving a `2^(i+1)`-multiple under the shortcut map. -/
theorem tstep_two_pow_succ_mul (x i : ℕ) : tstep (2 ^ (i + 1) * x) = 2 ^ i * x := by
  have h2 : 2 ^ (i + 1) * x = 2 * (2 ^ i * x) := by rw [pow_succ]; ring
  rw [h2]; unfold tstep
  rw [if_pos (by omega), Nat.mul_div_cancel_left _ (by norm_num)]

/-- The first `k` shortcut steps from `2^k x` are pure halvings. -/
theorem tstep_iterate_two_pow_mul_le (x : ℕ) :
    ∀ m k, m ≤ k → tstep^[m] (2 ^ k * x) = 2 ^ (k - m) * x := by
  intro m
  induction m with
  | zero => intro k _; simp
  | succ p ih =>
    intro k h
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Function.iterate_succ_apply, tstep_two_pow_succ_mul, ih k' (by omega)]
    have hk : k' + 1 - (p + 1) = k' - p := by omega
    rw [hk]

/-- Shortcut analogue of `step_iterate_two_pow_mul`. -/
theorem tstep_iterate_two_pow_mul (x k : ℕ) : tstep^[k] (2 ^ k * x) = x := by
  have := tstep_iterate_two_pow_mul_le x k k le_rfl
  simpa using this

/-- Past the halving prefix, the orbit of `2^k x` is the orbit of `x`. -/
theorem tstep_iterate_two_pow_mul_ge (x k m : ℕ) (h : k ≤ m) :
    tstep^[m] (2 ^ k * x) = tstep^[m - k] x := by
  conv_lhs => rw [show m = (m - k) + k from by omega]
  rw [Function.iterate_add_apply, tstep_iterate_two_pow_mul]

/-- The **over-strong** reading of Rozier--Terracol Theorem 3.2 that this repository used until
2026-09-01: *unboundedly large* paradoxical starts of the form `2^k n`.  Named (not axiomatized)
so that the refutation below is a theorem about it. -/
def UnboundedParadoxicalStarts (n : ℕ) : Prop :=
  ∀ K, ∃ k m, K < 2 ^ k * n ∧ Paradoxical (2 ^ k * n) m

/-- **Refutation, step 1.**  A number whose shortcut orbit is *bounded* has no unboundedly large
paradoxical starts of the form `2^k n`.  Reason: from `2^k n` the orbit first halves down to `n`
(so every value in the first `k` steps is `≤ 2^(k-1) n < 2^k n`) and then follows the orbit of
`n` (so every later value is `≤ B < 2^k n`).  The endpoint therefore never returns to the
start, and no segment from `2^k n` can be paradoxical once `2^k n > B`. -/
theorem not_unboundedParadoxicalStarts_of_bounded {n B : ℕ} (hn : 1 ≤ n)
    (hB : ∀ j, tstep^[j] n ≤ B) : ¬ UnboundedParadoxicalStarts n := by
  intro h
  obtain ⟨k, m, hlt, hpar⟩ := h B
  obtain ⟨-, hm, -, hle⟩ := hpar
  rcases le_or_gt m k with hmk | hkm
  · have hk1 : 1 ≤ k := by omega
    rw [tstep_iterate_two_pow_mul_le n m k hmk] at hle
    have hpow : (2 : ℕ) ^ (k - m) < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have : 2 ^ (k - m) * n < 2 ^ k * n := Nat.mul_lt_mul_of_lt_of_le hpow le_rfl hn
    omega
  · rw [tstep_iterate_two_pow_mul_ge n k m hkm.le] at hle
    have := hB (m - k)
    omega

/-- On a `step`-cycle the whole forward orbit is bounded by the sup over one period. -/
theorem step_orbit_bounded_of_onCycle {n : ℕ} (hc : OnCycle n) :
    ∃ B, ∀ j, step^[j] n ≤ B := by
  obtain ⟨L, hL, hfix⟩ := hc
  refine ⟨(Finset.range L).sup (fun l => step^[l] n), ?_⟩
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases lt_or_ge j L with hlt | hge
    · exact Finset.le_sup (f := fun l => step^[l] n) (Finset.mem_range.mpr hlt)
    · have hEq : step^[j] n = step^[j - L] n := by
        conv_lhs => rw [← Nat.sub_add_cancel hge, Function.iterate_add_apply, hfix]
      rw [hEq]; exact ih _ (by omega)

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

/-- **Refutation, step 2 — the reason the old axiom shape was unfaithful.**  If *every* `n ≥ 2`
of infinite shortcut stopping time had unboundedly large paradoxical starts `2^k n`, then
`NoNontrivialCycle` would follow outright: the minimum `m₀` of a nontrivial cycle has infinite
shortcut stopping time and a bounded shortcut orbit, contradicting step 1.

`NoNontrivialCycle` is open (Front B; the frontier is Hercher 2023 + Bařina 2025, which only
bound a hypothetical cycle's length).  No published theorem — Rozier--Terracol 2026 included —
implies it, so any axiom of the above shape is strictly stronger than its cited source.

This theorem is trust-base clean: it uses no axiom of this file. -/
theorem noNontrivialCycle_of_unboundedParadoxicalStarts
    (H : ∀ n, 2 ≤ n → InfiniteStoppingTime n → UnboundedParadoxicalStarts n) :
    NoNontrivialCycle := by
  intro n hn hc
  by_contra hne
  rw [not_or, not_or] at hne
  obtain ⟨B, hB⟩ := step_orbit_bounded_of_onCycle hc
  obtain ⟨m₀, k₀, hk₀, hmin⟩ :
      ∃ m₀ k₀, step^[k₀] n = m₀ ∧ ∀ j, m₀ ≤ step^[j] n := by
    have hSne : (Set.range (fun k => step^[k] n)).Nonempty := ⟨n, 0, rfl⟩
    obtain ⟨k₀, hk₀⟩ := Nat.sInf_mem hSne
    exact ⟨_, k₀, hk₀, fun j => Nat.sInf_le ⟨j, rfl⟩⟩
  have hshift : ∀ j, step^[j] m₀ = step^[j + k₀] n := by
    intro j; rw [← hk₀, Function.iterate_add_apply]
  have hstopS : ∀ j, m₀ ≤ step^[j] m₀ := fun j => by rw [hshift j]; exact hmin _
  have hm1 : 1 ≤ m₀ := by rw [← hk₀]; exact iterate_step_pos hn k₀
  have hm2 : 2 ≤ m₀ := by
    rcases Nat.lt_or_ge m₀ 2 with h | h
    · exfalso
      have h1 : m₀ = 1 := by omega
      have hr : ReachesOne n := ⟨k₀, by rw [hk₀]; exact h1⟩
      rcases eq_trivial_of_onCycle_of_reachesOne hc hr with h' | h' | h'
      · exact hne.1 h'
      · exact hne.2.1 h'
      · exact hne.2.2 h'
    · exact h
  have hBm : ∀ j, tstep^[j] m₀ ≤ B := by
    intro j
    obtain ⟨i, hi⟩ := tstep_iterate_eq_step_iterate m₀ j
    rw [hi, hshift i]
    exact hB _
  have hinf : InfiniteStoppingTime m₀ := by
    intro j
    obtain ⟨i, hi⟩ := tstep_iterate_eq_step_iterate m₀ j
    rw [hi]; exact hstopS i
  exact not_unboundedParadoxicalStarts_of_bounded hm1 hBm (H m₀ hm2 hinf)

/-!
### The repaired statement is not vacuous

The cardinality form above is *satisfied* in exactly the configuration that refutes the
unbounded-starts form: a shortcut cycle through `n > 2` gives infinitely many paradoxical
segments starting at `2^0 n = n`, namely the whole-period multiples.  So the repair keeps
Theorem 3.2's content in the cycle case while dropping the illegitimate extra strength.
-/

/-- A shortcut cycle is subcritical: `3^(odd steps) < 2^(period)`.  Repackaging of
`FrontB.integerCycle_traceWord`'s positive denominator. -/
theorem subcritical_of_tstep_cycle {n L : ℕ} (hn : 1 ≤ n) (hL : 0 < L)
    (hfix : tstep^[L] n = n) : 3 ^ ones (traceWord n L) < 2 ^ L := by
  obtain ⟨-, -, hden, -⟩ := integerCycle_traceWord hn hL hfix
  rw [den, traceWord_length] at hden
  exact_mod_cast (by linarith : ((3 : ℤ) ^ ones (traceWord n L)) < 2 ^ L)

/-- Odd steps are additive along whole periods of a shortcut cycle. -/
theorem ones_traceWord_mul_of_cycle {n L : ℕ} (hfix : tstep^[L] n = n) :
    ∀ j, ones (traceWord n (L * j)) = j * ones (traceWord n L) := by
  intro j
  induction j with
  | zero => simp [traceWord]
  | succ i ih =>
    have hiter : tstep^[L * i] n = n := by
      rw [Function.iterate_mul]
      exact Function.iterate_fixed hfix i
    have hw : traceWord n (L * (i + 1)) = traceWord n (L * i) ++ traceWord n L := by
      rw [show L * (i + 1) = L * i + L from by ring, FrontA.traceWord_add, hiter]
    rw [hw, FrontB.ones_append, ih]
    ring

/-- **Consistency anchor.**  A shortcut cycle through `n > 2` really does produce infinitely
many paradoxical segments starting at numbers `2^k n` — the period multiples `(k, m) = (0, jL)`.
Hence `Assumed.rozier_terracol_3_2` in its repaired (cardinality) form is *not* refuted by a
nontrivial cycle, unlike the unbounded-starts form.  Trust-base clean, uses no axiom. -/
theorem infinite_paradoxical_of_tstep_cycle {n L : ℕ} (h2 : 2 < n) (hL : 0 < L)
    (hfix : tstep^[L] n = n) :
    {p : ℕ × ℕ | Paradoxical (2 ^ p.1 * n) p.2}.Infinite := by
  have hn : 1 ≤ n := by omega
  have hsub1 : 3 ^ ones (traceWord n L) < 2 ^ L := subcritical_of_tstep_cycle hn hL hfix
  refine Set.infinite_of_injective_forall_mem
    (f := fun j : ℕ => ((0 : ℕ), L * (j + 1))) ?_ ?_
  · intro a b hab
    simp only [Prod.mk.injEq] at hab
    have h1 : a + 1 = b + 1 := Nat.eq_of_mul_eq_mul_left hL hab.2
    omega
  · intro j
    have hiter : tstep^[L * (j + 1)] n = n := by
      rw [Function.iterate_mul]
      exact Function.iterate_fixed hfix (j + 1)
    refine ⟨by simpa using h2, by positivity, ?_, ?_⟩
    · simp only []
      rw [pow_zero, one_mul, ones_traceWord_mul_of_cycle hfix]
      calc (3 : ℕ) ^ ((j + 1) * ones (traceWord n L))
          = (3 ^ ones (traceWord n L)) ^ (j + 1) := by rw [← pow_mul, Nat.mul_comm]
        _ < (2 ^ L) ^ (j + 1) := Nat.pow_lt_pow_left hsub1 (by omega)
        _ = 2 ^ (L * (j + 1)) := by rw [← pow_mul]
    · simp only []
      rw [pow_zero, one_mul, hiter]

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
*acyclic* paradoxical segments.  Apply `Assumed.rozier_terracol_3_2` to the infinite-stopping
value `m₀`: it gives an infinite set of pairs `(k, m)` with `Paradoxical (2^k m₀) m`.  The map
`(k, m) ↦ (2^k m₀, m)` is injective (`m₀ ≥ 1`), and each image pair is *acyclic* — the start
`2^k m₀` still diverges, so it cannot close a shortcut cycle.  Hence the acyclic set contains an
infinite injective image and is itself infinite.

Note that this uses only the **cardinality** of the segment set, never any growth of the starts:
the discarded "unbounded starts" reading is refuted above
(`noNontrivialCycle_of_unboundedParadoxicalStarts`). -/
theorem diverges_imp_infinite_acyclicParadoxical (n : ℕ) (hn : 1 ≤ n) (hdiv : Diverges n) :
    {p : ℕ × ℕ | AcyclicParadoxical p.1 p.2}.Infinite := by
  obtain ⟨m₀, h2, hstop, hdivm⟩ := infiniteStoppingTime_of_diverges hn hdiv
  have hP := Assumed.rozier_terracol_3_2 m₀ h2 hstop
  set f : ℕ × ℕ → ℕ × ℕ := fun p => (2 ^ p.1 * m₀, p.2) with hf
  have hinj : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    rw [hf] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2'⟩ := h
    have hpow : (2 : ℕ) ^ a = 2 ^ c := Nat.eq_of_mul_eq_mul_right (by omega) h1
    have hac : a = c := Nat.pow_right_injective le_rfl hpow
    simp [hac, h2']
  have hsub : f '' {p : ℕ × ℕ | Paradoxical (2 ^ p.1 * m₀) p.2}
      ⊆ {p : ℕ × ℕ | AcyclicParadoxical p.1 p.2} := by
    rintro _ ⟨⟨k, m⟩, hmem, rfl⟩
    obtain ⟨hs2, hm, hsubc, hle⟩ := hmem
    have hdivs : Diverges (2 ^ k * m₀) := diverges_two_pow_mul hdivm k
    have hnefix : tstep^[m] (2 ^ k * m₀) ≠ 2 ^ k * m₀ := fun h =>
      not_tstep_fixed_of_diverges hdivs hm h
    exact ⟨hs2, hm, hsubc, lt_of_le_of_ne hle (fun h => hnefix h.symm)⟩
  exact Set.Infinite.mono hsub (hP.image hinj.injOn)

/-- **The Front-A consumption theorem**: only finitely many acyclic paradoxical segments
implies no divergent orbit.  (Conditional reduction — see the strength caveat in the module
docstring.) -/
theorem finite_acyclicParadoxical_imp_noDivergent
    (hfin : FiniteAcyclicParadoxical) : NoDivergentOrbit := by
  intro n hn hdiv
  exact (diverges_imp_infinite_acyclicParadoxical n hn hdiv).not_finite hfin

end CollatzMoonshot
