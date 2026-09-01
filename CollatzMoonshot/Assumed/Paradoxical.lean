/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.FrontA.Paradoxical
import CollatzMoonshot.FrontA.PowApprox

/-!
# Assumed: Rozier--Terracol 2026, Theorem 3.2 (paradoxical segments from infinite stopping time)

Tier: **DISCHARGED** (2026-09-01) — this module no longer *assumes* Rozier--Terracol 2026,
Theorem 3.2 (Olivier Rozier and Claude Terracol, *Paradoxical behavior in Collatz sequences*,
Discrete Mathematics 349 (2026), 115167; arXiv:2502.00948v5).  `Assumed.rozier_terracol_3_2` is
now a **theorem proved here**, resting on exactly one disclosed node,
`FrontA.two_pow_approx_three_pow_from_above` (`FrontA/PowApprox.lean`): powers of two approximate
powers of three from above to arbitrary relative precision, infinitely often.  That node is a
classical statement about `log₂ 3` (density of `{A·log₂3}` mod `1`), not a citation.

The file keeps its `Assumed` name and namespace so that consumers are unchanged.

## What the theorem says (the paper's actual statement)

An integer `n ≥ 2` whose **shortcut stopping time is infinite** — `tstep^[j] n ≥ n` for every
`j` — produces **infinitely many paradoxical segments** starting at numbers `2^k n` (Theorem
3.2).  Rendered here as: the set of pairs `(k, m)` with `Paradoxical (2^k n) m` is infinite.  The
`Paradoxical` predicate is exactly the paper's definition rendered in repository notation
(`CollatzMoonshot/FrontA/Paradoxical.lean`).  `NoDivergentOrbit` is **not** packaged in — the
Front-A consumption is derived separately below.

## ⚠️ Fidelity correction, 2026-09-01 (machine-checked)

Until this date the statement was **axiomatized**, and read *"for every bound `K` there are `k, m` with `K < 2^k n` and
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

/-!
### The bounded half of Theorem 3.2, PROVED

If `n`'s shortcut orbit is bounded it is eventually periodic, entering a cycle of period `L` at
some time `t`.  The cycle block is subcritical (`subcritical_of_tstep_cycle`), so the segment
coefficient `3^a / 2^m` at `m = t + jL` shrinks geometrically and eventually drops below `1`,
while the endpoint sits at the cycle entry point `c ≥ n`.  Every such `m` gives a paradoxical
segment starting at `2^0 n = n`, and there are infinitely many of them.

The only quantitative ingredient is that `x^j` is eventually beaten by `y^j` for `x < y`, however
large the constant in front — proved here in `ℕ` from a multiplicative Bernoulli bound, so no
real-analysis limit is needed.
-/

/-- Bernoulli in `ℕ`, stated multiplicatively to avoid `x^(j-1)`: `x^j·(x+j) ≤ x·(x+1)^j`. -/
theorem nat_bernoulli_mul (x : ℕ) : ∀ j, x ^ j * (x + j) ≤ x * (x + 1) ^ j := by
  intro j
  induction j with
  | zero => simp
  | succ i ih =>
    have hstep : x ^ (i + 1) * (x + (i + 1)) ≤ (x ^ i * (x + i)) * (x + 1) := by
      have hexp : (x ^ i * (x + i)) * (x + 1) = x ^ (i + 1) * (x + i) + x ^ i * (x + i) := by
        ring
      rw [hexp]
      have h1 : x ^ (i + 1) * (x + (i + 1)) = x ^ (i + 1) * (x + i) + x ^ (i + 1) := by ring
      rw [h1]
      have h2 : x ^ (i + 1) ≤ x ^ i * (x + i) := by
        calc x ^ (i + 1) = x ^ i * x := by ring
          _ ≤ x ^ i * (x + i) := Nat.mul_le_mul_left _ (by omega)
      omega
    calc x ^ (i + 1) * (x + (i + 1)) ≤ (x ^ i * (x + i)) * (x + 1) := hstep
      _ ≤ (x * (x + 1) ^ i) * (x + 1) := Nat.mul_le_mul_right _ ih
      _ = x * (x + 1) ^ (i + 1) := by ring

/-- For `1 ≤ x < y` the power `y^j` outgrows any constant multiple of `x^j`: already at
`j = c·x` one has `c · x^j < y^j`.  (Pure `ℕ`; the witness is explicit.) -/
theorem const_mul_pow_lt_pow {x y : ℕ} (hx : 1 ≤ x) (hxy : x < y) (c : ℕ) :
    c * x ^ (c * x) < y ^ (c * x) := by
  set j := c * x with hj
  have hxpos : 0 < x := hx
  have hb : x ^ j * (x + j) ≤ x * (x + 1) ^ j := nat_bernoulli_mul x j
  have hy : (x + 1) ^ j ≤ y ^ j := Nat.pow_le_pow_left (by omega) j
  have h1 : x ^ j * (x + j) ≤ x * y ^ j := le_trans hb (Nat.mul_le_mul_left x hy)
  have h2 : x * (c * x ^ j) < x ^ j * (x + j) := by
    have he : x ^ j * (x + j) = x ^ j * x * (1 + c) := by rw [hj]; ring
    have hl : x * (c * x ^ j) = x ^ j * x * c := by ring
    rw [he, hl]
    exact mul_lt_mul_of_pos_left (by omega) (by positivity)
  exact Nat.lt_of_mul_lt_mul_left (lt_of_lt_of_le h2 h1)

/-- Infinite shortcut stopping time forces `n > 2` (at `n = 2` the very first step drops to `1`).
This upgrades the axiom's `2 ≤ n` to the `2 < n` that `Paradoxical` demands. -/
theorem two_lt_of_infiniteStoppingTime {n : ℕ} (h2 : 2 ≤ n) (hstop : InfiniteStoppingTime n) :
    2 < n := by
  rcases Nat.lt_or_ge 2 n with h | h
  · exact h
  · exfalso
    have hn2 : n = 2 := by omega
    have h1 := hstop 1
    rw [hn2] at h1
    simp at h1

/-- A bounded shortcut orbit is eventually periodic (pigeonhole into `Fin (B+1)`). -/
theorem exists_eventual_period_of_bounded {n B : ℕ} (hB : ∀ j, tstep^[j] n ≤ B) :
    ∃ t L, 0 < L ∧ tstep^[L] (tstep^[t] n) = tstep^[t] n := by
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun k : ℕ => (⟨tstep^[k] n, Nat.lt_succ_of_le (hB k)⟩ : Fin (B + 1)))
  have heq' : tstep^[i] n = tstep^[j] n := by simpa [Fin.ext_iff] using heq
  have key : ∀ a b : ℕ, a < b → tstep^[a] n = tstep^[b] n →
      ∃ t L, 0 < L ∧ tstep^[L] (tstep^[t] n) = tstep^[t] n := by
    intro a b hab h
    refine ⟨a, b - a, by omega, ?_⟩
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hab.le]
    exact h.symm
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h heq'
  · exact key j i h heq'.symm

/-- **Rozier--Terracol Theorem 3.2, bounded case — PROVED, trust-base clean.**  If `n ≥ 2` has
infinite shortcut stopping time and a *bounded* shortcut orbit, then infinitely many pairs
`(k, m)` satisfy `Paradoxical (2^k n) m` — all with `k = 0`, at the lengths `m = t + jL` for
`j` past an explicit threshold `j₀ = 3^(a_t)·3^(a_L)`. -/
theorem infinite_paradoxical_of_bounded_orbit {n B : ℕ} (h2 : 2 ≤ n)
    (hstop : InfiniteStoppingTime n) (hB : ∀ j, tstep^[j] n ≤ B) :
    {p : ℕ × ℕ | Paradoxical (2 ^ p.1 * n) p.2}.Infinite := by
  have hn3 : 2 < n := two_lt_of_infiniteStoppingTime h2 hstop
  obtain ⟨t, L, hL, hcfix⟩ := exists_eventual_period_of_bounded hB
  set c := tstep^[t] n with hc
  have hcn : n ≤ c := hstop t
  have hc1 : 1 ≤ c := by omega
  set aL := ones (traceWord c L) with haL
  set aT := ones (traceWord n t) with haT
  have hsubL : 3 ^ aL < 2 ^ L := subcritical_of_tstep_cycle hc1 hL hcfix
  have hones : ∀ j, ones (traceWord n (t + L * j)) = aT + j * aL := by
    intro j
    rw [FrontA.traceWord_add, FrontB.ones_append, ← hc, ones_traceWord_mul_of_cycle hcfix]
  have hend : ∀ j, tstep^[t + L * j] n = c := by
    intro j
    rw [show t + L * j = L * j + t from by ring, Function.iterate_add_apply, ← hc,
      Function.iterate_mul]
    exact Function.iterate_fixed hcfix j
  set j₀ := 3 ^ aT * 3 ^ aL with hj₀
  have h3aL : 1 ≤ (3 : ℕ) ^ aL := Nat.one_le_pow _ _ (by norm_num)
  have hsub0 : 3 ^ aT * (3 ^ aL) ^ j₀ < (2 ^ L) ^ j₀ :=
    const_mul_pow_lt_pow h3aL hsubL (3 ^ aT)
  have hsub : ∀ i : ℕ, 3 ^ (aT + (j₀ + i) * aL) < 2 ^ (t + L * (j₀ + i)) := by
    intro i
    have hle : ((3 : ℕ) ^ aL) ^ i ≤ (2 ^ L) ^ i := Nat.pow_le_pow_left hsubL.le i
    have hpos : 0 < ((2 : ℕ) ^ L) ^ i := by positivity
    have hstep : (3 ^ aT * (3 ^ aL) ^ j₀) * ((3 : ℕ) ^ aL) ^ i
        < ((2 : ℕ) ^ L) ^ j₀ * ((2 : ℕ) ^ L) ^ i :=
      Nat.mul_lt_mul_of_lt_of_le hsub0 hle hpos
    calc (3 : ℕ) ^ (aT + (j₀ + i) * aL)
        = (3 ^ aT * (3 ^ aL) ^ j₀) * ((3 : ℕ) ^ aL) ^ i := by
          rw [pow_add, ← pow_mul, ← pow_mul, ← pow_add]; ring_nf
      _ < ((2 : ℕ) ^ L) ^ j₀ * ((2 : ℕ) ^ L) ^ i := hstep
      _ = 2 ^ (L * (j₀ + i)) := by rw [← pow_add, ← pow_mul]
      _ ≤ 2 ^ (t + L * (j₀ + i)) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3T : 1 ≤ (3 : ℕ) ^ aT := Nat.one_le_pow _ _ (by norm_num)
  have hj₀pos : 1 ≤ j₀ := by rw [hj₀]; simpa using Nat.mul_le_mul h3T h3aL
  refine Set.infinite_of_injective_forall_mem
    (f := fun i : ℕ => ((0 : ℕ), t + L * (j₀ + i))) ?_ ?_
  · intro a b hab
    simp only [Prod.mk.injEq, true_and] at hab
    have hmul : L * (j₀ + a) = L * (j₀ + b) := by omega
    have := Nat.eq_of_mul_eq_mul_left hL hmul
    omega
  · intro i
    refine ⟨by simpa using hn3, ?_, ?_, ?_⟩
    · have : 0 < L * (j₀ + i) := Nat.mul_pos hL (by omega)
      simp only []
      omega
    · simp only [pow_zero, one_mul]
      rw [hones (j₀ + i)]
      exact hsub i
    · simp only [pow_zero, one_mul]
      rw [hend (j₀ + i)]
      exact hcn

/-!
### The general case: Theorem 3.2 reduced to ONE Diophantine node

The `2^k` prefix of a blow-up start contributes only halvings, and in the iterate identity it
cancels exactly:

    Paradoxical (2^k n) (k+j)  ↔  2 < 2^k n  ∧  0 < k+j  ∧  3^(a_j) < 2^(k+j)  ∧  2^k n ≤ Y_j

with `a_j = ones (traceWord n j)`, `Y_j = tstep^[j] n`.  Writing `s = k + j` and using
`2^j Y_j = 3^(a_j) n + numer_j`, the two substantive conditions become the purely arithmetic

    3^(a_j) < 2^s      and      (2^s - 3^(a_j)) · n ≤ numer_j .

Two cases.  If `3^(a_j) < 2^j` for arbitrarily large `j` (the coefficient is subcritical
infinitely often), take `k = 0`: the endpoint condition is just `n ≤ Y_j`, which is the
infinite-stopping-time hypothesis.  Otherwise `2^j ≤ 3^(a_j)` from some point on; then `a_j → ∞`
and, because `a_j` steps by at most one, it attains *every* large value `A`.  The normalized
remainder `numer_j / 3^(a_j)` is non-decreasing (`orbit_numer_mono`), so it is bounded below by a
fixed positive rational `P/Q` once one odd step has occurred.  Choosing `A` for which some `2^s`
approximates `3^A` from above to relative precision `1/(nQ)` — the node
`FrontA.two_pow_approx_three_pow_from_above` — makes `(2^s - 3^A)·n ≤ numer_j` and hence gives a
paradoxical segment with `k = s - j`.
-/

/-- The itinerary of a `2^k`-blow-up: `k` halvings, then the itinerary of the base. -/
theorem traceWord_two_pow_mul (n : ℕ) : ∀ k j : ℕ,
    traceWord (2 ^ k * n) (k + j) = List.replicate k false ++ traceWord n j := by
  intro k
  induction k with
  | zero => intro j; simp
  | succ i ih =>
    intro j
    have hx : 2 ^ (i + 1) * n = 2 * (2 ^ i * n) := by rw [pow_succ]; ring
    have heven : (2 ^ (i + 1) * n) % 2 = 0 := by omega
    rw [show i + 1 + j = (i + j) + 1 from by ring, traceWord, tstep_two_pow_succ_mul, ih j,
      List.replicate_succ, List.cons_append]
    congr 1
    simp [heven]

/-- Sufficient conditions for a `2^k`-blow-up segment to be paradoxical, stated purely in terms
of the *base* itinerary: the `2^k` prefix contributes no odd letters and cancels out. -/
theorem paradoxical_two_pow_mul {n k j : ℕ} (hn : 2 < n) (hs : 0 < k + j)
    (hsub : 3 ^ ones (traceWord n j) < 2 ^ (k + j))
    (hend : 2 ^ k * n ≤ tstep^[j] n) :
    Paradoxical (2 ^ k * n) (k + j) := by
  refine ⟨?_, hs, ?_, ?_⟩
  · calc 2 < n := hn
      _ = 1 * n := by ring
      _ ≤ 2 ^ k * n := Nat.mul_le_mul_right _ (Nat.one_le_two_pow)
  · rw [traceWord_two_pow_mul, FrontB.ones_append]
    simpa using hsub
  · rw [tstep_iterate_two_pow_mul_ge n k (k + j) (by omega)]
    simpa using hend

/-- One step of the orbit remainder recursion, odd case. -/
theorem traceWord_succ_odd {n j : ℕ} (h : tstep^[j] n % 2 = 1) :
    traceWord n (j + 1) = traceWord n j ++ [true] := by
  rw [FrontA.traceWord_add n j 1]
  congr 1
  simp [traceWord, h]

theorem traceWord_succ_even {n j : ℕ} (h : tstep^[j] n % 2 = 0) :
    traceWord n (j + 1) = traceWord n j ++ [false] := by
  rw [FrontA.traceWord_add n j 1]
  congr 1
  simp [traceWord, h]

/-- `ones` grows by at most one per step. -/
theorem ones_traceWord_succ_le (n j : ℕ) :
    ones (traceWord n (j + 1)) ≤ ones (traceWord n j) + 1 := by
  rcases Nat.even_or_odd (tstep^[j] n) with he | ho
  · rw [traceWord_succ_even (Nat.even_iff.mp he)]; simp
  · rw [traceWord_succ_odd (Nat.odd_iff.mp ho)]; simp

/-- The normalized remainder `numer / 3^ones` is non-decreasing along the orbit. -/
theorem orbit_numer_mono (n : ℕ) : ∀ i j, i ≤ j →
    numer (traceWord n i) * 3 ^ ones (traceWord n j)
      ≤ numer (traceWord n j) * 3 ^ ones (traceWord n i) := by
  intro i j hij
  obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
  induction d with
  | zero => simp
  | succ e ih =>
    have hstep : numer (traceWord n (i + e)) * 3 ^ ones (traceWord n (i + e + 1))
        ≤ numer (traceWord n (i + e + 1)) * 3 ^ ones (traceWord n (i + e)) := by
      rcases Nat.even_or_odd (tstep^[i + e] n) with he | ho
      · rw [traceWord_succ_even (Nat.even_iff.mp he), numer_append_false, ones_append_false]
      · rw [traceWord_succ_odd (Nat.odd_iff.mp ho), numer_append_true, ones_append_true,
          pow_succ]
        calc numer (traceWord n (i + e)) * (3 ^ ones (traceWord n (i + e)) * 3)
            = 3 * numer (traceWord n (i + e)) * 3 ^ ones (traceWord n (i + e)) := by ring
          _ ≤ (3 * numer (traceWord n (i + e)) + 2 ^ (traceWord n (i + e)).length)
                * 3 ^ ones (traceWord n (i + e)) :=
              Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
    have h1 := ih (by omega)
    have hpos : 0 < (3 : ℕ) ^ ones (traceWord n (i + e)) := by positivity
    show numer (traceWord n i) * 3 ^ ones (traceWord n (i + e + 1))
        ≤ numer (traceWord n (i + e + 1)) * 3 ^ ones (traceWord n i)
    -- N_i * 3^{a_{i+e}} ≤ N_{i+e} * 3^{a_i}  and  N_{i+e} * 3^{a_{i+e+1}} ≤ N_{i+e+1} * 3^{a_{i+e}}
    have hchain : numer (traceWord n i) * 3 ^ ones (traceWord n (i + e + 1))
        * 3 ^ ones (traceWord n (i + e))
        ≤ numer (traceWord n (i + e + 1)) * 3 ^ ones (traceWord n i)
          * 3 ^ ones (traceWord n (i + e)) := by
      calc numer (traceWord n i) * 3 ^ ones (traceWord n (i + e + 1))
              * 3 ^ ones (traceWord n (i + e))
          = (numer (traceWord n i) * 3 ^ ones (traceWord n (i + e)))
              * 3 ^ ones (traceWord n (i + e + 1)) := by ring
        _ ≤ (numer (traceWord n (i + e)) * 3 ^ ones (traceWord n i))
              * 3 ^ ones (traceWord n (i + e + 1)) := Nat.mul_le_mul_right _ (by
                  simpa [show i + e = i + e from rfl] using h1)
        _ = (numer (traceWord n (i + e)) * 3 ^ ones (traceWord n (i + e + 1)))
              * 3 ^ ones (traceWord n i) := by ring
        _ ≤ (numer (traceWord n (i + e + 1)) * 3 ^ ones (traceWord n (i + e)))
              * 3 ^ ones (traceWord n i) := Nat.mul_le_mul_right _ hstep
        _ = numer (traceWord n (i + e + 1)) * 3 ^ ones (traceWord n i)
              * 3 ^ ones (traceWord n (i + e)) := by ring
    exact Nat.le_of_mul_le_mul_right hchain hpos


theorem ones_traceWord_mono (n : ℕ) {i j : ℕ} (h : i ≤ j) :
    ones (traceWord n i) ≤ ones (traceWord n j) := by
  obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
  rw [FrontA.traceWord_add, FrontB.ones_append]
  omega

theorem exists_ones_eq (n : ℕ) : ∀ (d j₀ j₁ A : ℕ), j₁ = j₀ + d →
    ones (traceWord n j₀) ≤ A → A < ones (traceWord n j₁) →
    ∃ j, j₀ ≤ j ∧ ones (traceWord n j) = A := by
  intro d
  induction d with
  | zero =>
    intro j₀ j₁ A h h1 h2
    subst h
    omega
  | succ e ih =>
    intro j₀ j₁ A h h1 h2
    by_cases hEq : ones (traceWord n j₀) = A
    · exact ⟨j₀, le_rfl, hEq⟩
    · have h1' : ones (traceWord n (j₀ + 1)) ≤ A := by
        have := ones_traceWord_succ_le n j₀; omega
      obtain ⟨j, hj, hje⟩ := ih (j₀ + 1) j₁ A (by omega) h1' h2
      exact ⟨j, by omega, hje⟩

theorem infinite_of_snd_unbounded {S : Set (ℕ × ℕ)} (h : ∀ M, ∃ p ∈ S, M < p.2) :
    S.Infinite := by
  apply Set.Infinite.of_image Prod.snd
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨p, hp, hlt⟩ := h B
  have hmem : p.2 ∈ Prod.snd '' S := ⟨p, hp, rfl⟩
  exact absurd (hB hmem) (by omega)

/-- **Rozier--Terracol Theorem 3.2 — full statement, modulo the single Diophantine node.** -/
theorem infinite_paradoxical_of_infiniteStoppingTime {n : ℕ} (h2 : 2 ≤ n)
    (hstop : InfiniteStoppingTime n) :
    {p : ℕ × ℕ | Paradoxical (2 ^ p.1 * n) p.2}.Infinite := by
  have hn3 : 2 < n := two_lt_of_infiniteStoppingTime h2 hstop
  apply infinite_of_snd_unbounded
  intro M
  by_cases hB1 : ∀ M', ∃ j, M' < j ∧ 3 ^ ones (traceWord n j) < 2 ^ j
  · -- subcritical infinitely often: `k = 0`
    obtain ⟨j, hjM, hsub⟩ := hB1 M
    refine ⟨(0, j), ?_, hjM⟩
    have := paradoxical_two_pow_mul (n := n) (k := 0) (j := j) hn3 (by omega)
      (by simpa using hsub) (by simpa using hstop j)
    simpa using this
  · -- eventually supercritical
    push_neg at hB1
    obtain ⟨J, hJ'⟩ := hB1
    have haunb : ∀ A, ∃ j, A < ones (traceWord n j) := by
      intro A
      refine ⟨max (J + 1) (2 * A + 1), ?_⟩
      have hjJ : J < max (J + 1) (2 * A + 1) := by omega
      have h1 : (3 : ℕ) ^ A < 2 ^ max (J + 1) (2 * A + 1) := by
        calc (3 : ℕ) ^ A ≤ 4 ^ A := Nat.pow_le_pow_left (by norm_num) A
          _ = 2 ^ (2 * A) := by rw [pow_mul]; norm_num
          _ < 2 ^ (2 * A + 1) := by
              rw [pow_succ]
              have hp : 0 < (2 : ℕ) ^ (2 * A) := by positivity
              omega
          _ ≤ 2 ^ max (J + 1) (2 * A + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2' := hJ' _ hjJ
      have hlt : (3 : ℕ) ^ A < 3 ^ ones (traceWord n (max (J + 1) (2 * A + 1))) := by omega
      exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt
    obtain ⟨j₁, hj₁⟩ : ∃ j₁, 1 ≤ ones (traceWord n j₁) := by
      obtain ⟨j, hj⟩ := haunb 0; exact ⟨j, by omega⟩
    have hP : 1 ≤ numer (traceWord n j₁) := numer_pos hj₁
    have hQ : 0 < (3 : ℕ) ^ ones (traceWord n j₁) := by positivity
    obtain ⟨A, s, hAM, hAs, happrox⟩ :=
      two_pow_approx_three_pow_from_above (max M (ones (traceWord n (max (J + 1) j₁))))
        (n * 3 ^ ones (traceWord n j₁))
    have hMA : M < A := lt_of_le_of_lt (le_max_left _ _) hAM
    have hbase : ones (traceWord n (max (J + 1) j₁)) ≤ A :=
      le_of_lt (lt_of_le_of_lt (le_max_right _ _) hAM)
    obtain ⟨j', hj'⟩ := haunb A
    have hj'gt : max (J + 1) j₁ < j' := by
      by_contra hcon
      have := ones_traceWord_mono n (show j' ≤ max (J + 1) j₁ by omega)
      omega
    obtain ⟨j, hjge, hjA⟩ := exists_ones_eq n (j' - max (J + 1) j₁) (max (J + 1) j₁) j' A
      (by omega) hbase hj'
    have hjJ : J < j := by omega
    have hj₁j : j₁ ≤ j := by omega
    have hmono := orbit_numer_mono n j₁ j hj₁j
    rw [hjA] at hmono
    have hkey : (2 ^ s - 3 ^ A) * n ≤ numer (traceWord n j) := by
      have h1 : (2 ^ s - 3 ^ A) * n * 3 ^ ones (traceWord n j₁) ≤ 3 ^ A := by
        calc (2 ^ s - 3 ^ A) * n * 3 ^ ones (traceWord n j₁)
            = (2 ^ s - 3 ^ A) * (n * 3 ^ ones (traceWord n j₁)) := by ring
          _ ≤ 3 ^ A := happrox
      have h2 : (3 : ℕ) ^ A ≤ numer (traceWord n j₁) * 3 ^ A :=
        Nat.le_mul_of_pos_left _ hP
      have h3 : (2 ^ s - 3 ^ A) * n * 3 ^ ones (traceWord n j₁)
          ≤ numer (traceWord n j) * 3 ^ ones (traceWord n j₁) := by omega
      exact Nat.le_of_mul_le_mul_right h3 hQ
    have hid := tstep_iterate_identity j n
    rw [hjA] at hid
    have hsplit : (2 : ℕ) ^ s = (2 ^ s - 3 ^ A) + 3 ^ A := by omega
    have hsn : 2 ^ s * n ≤ 2 ^ j * tstep^[j] n := by
      calc (2 : ℕ) ^ s * n = ((2 ^ s - 3 ^ A) + 3 ^ A) * n := by rw [← hsplit]
        _ = (2 ^ s - 3 ^ A) * n + 3 ^ A * n := by ring
        _ ≤ numer (traceWord n j) + 3 ^ A * n := by omega
        _ = 2 ^ j * tstep^[j] n := by omega
    have hsj : j < s := by
      have hjs := hJ' j hjJ
      rw [hjA] at hjs
      have hpow : (2 : ℕ) ^ j < 2 ^ s := by omega
      exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp hpow
    have hAlt : (2 : ℕ) ^ A ≤ 3 ^ A := Nat.pow_le_pow_left (by norm_num) A
    have hAs' : A < s := by
      have hpow : (2 : ℕ) ^ A < 2 ^ s := by omega
      exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp hpow
    have hks : (s - j) + j = s := by omega
    have hend : 2 ^ (s - j) * n ≤ tstep^[j] n := by
      have hfac : (2 : ℕ) ^ s = 2 ^ j * 2 ^ (s - j) := by rw [← pow_add]; congr 1; omega
      have hmul : 2 ^ j * (2 ^ (s - j) * n) ≤ 2 ^ j * tstep^[j] n := by
        calc 2 ^ j * (2 ^ (s - j) * n) = 2 ^ s * n := by rw [hfac]; ring
          _ ≤ 2 ^ j * tstep^[j] n := hsn
      exact Nat.le_of_mul_le_mul_left hmul (by positivity)
    refine ⟨(s - j, (s - j) + j), ?_, by simp only []; omega⟩
    exact paradoxical_two_pow_mul hn3 (by omega) (by rw [hjA, hks]; exact hAs) hend


namespace Assumed

/-- **Rozier--Terracol 2026, Theorem 3.2 — now a THEOREM, no longer an axiom.**  The whole
statement is derived in this file: the *bounded* case unconditionally
(`infinite_paradoxical_of_bounded_orbit`), and the general case
(`infinite_paradoxical_of_infiniteStoppingTime`) from the single disclosed Diophantine node
`FrontA.two_pow_approx_three_pow_from_above`.  The name and statement consumed by the rest of the
repository are unchanged; what changed is that the dependency is now one classical fact about
`log₂ 3` rather than a cited paper. -/
theorem rozier_terracol_3_2 (n : ℕ) (h2 : 2 ≤ n) (hstop : InfiniteStoppingTime n) :
    {p : ℕ × ℕ | Paradoxical (2 ^ p.1 * n) p.2}.Infinite :=
  infinite_paradoxical_of_infiniteStoppingTime h2 hstop

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
