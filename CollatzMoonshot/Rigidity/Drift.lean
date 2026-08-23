/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CollatzMoonshot.Basic
import CollatzMoonshot.Conjecture
import CollatzMoonshot.Descent

/-!
# Drift: exact size bookkeeping along a Collatz orbit

The archimedean half of Lane 1.  `Rigidity/Padic.lean` says what the orbit does
2-adically; this file says what it does *in size*, and the two meet at the parity
partition: an even step divides by exactly `2`, an odd step multiplies by `3` and
pays an overhead for the `+1`.

## The accounting

Write `a = oddSteps n k` and `b = evenSteps n k` for the two step counts over the
first `k` steps.  Ignoring the `+1` the orbit would satisfy `n_k = n · 3^a / 2^b`
exactly, so the orbit shrinks iff `a · log 3 < b · log 2`, i.e. iff the odd-step
frequency `a / k` sits below `log 2 / log 6 ≈ 0.3868…`.

The `+1` is not ignorable, and there is no exact affine potential that removes it:
`n ↦ n + c` transports the even branch only for `c ≤ 0` and the odd branch only
for `c ≥ 1/2`.  So it is *throttled* instead: below a floor `N` that the orbit
stays above, each odd step costs at most `3 + 1/N` rather than `3`.  That single
constant carries the whole file.

* `N = 1` (no information) gives `4` - the crude bound, threshold `1/3`.
* `N → ∞` (a diverging orbit) gives `3` - the sharp bound, threshold `log 2 / log 6`.

The gap between those two thresholds is exactly the room a divergent orbit would
have to live in: a *typical* orbit spends one odd step per two halvings, odd
frequency `1/3`, which the crude bound cannot see and the sharp bound can.

## Why this is the coupling Lane 1 wants

`isClopen_evenSet` (in `Rigidity/Padic.lean`) says the parity partition is clopen
upstairs, so `μ ↦ μ(odd)` is weak-* continuous and the empirical odd frequency
converges to it along any orbit-limit measure.  `oddFrequency < log 2 / log 6`
is therefore a statement *about invariant measures* that this file converts into
archimedean descent - no funnel-frequency upgrade required.  See
`Rigidity/Invariant.lean` (`ParityRigidityW1'`).
-/

namespace CollatzMoonshot

/-- The even branch of `step`, as a rewrite rule (`unfold step` would also unfold
the `step` inside `step^[k]`). -/
theorem step_of_even {m : ℕ} (h : m % 2 = 0) : step m = m / 2 := by
  unfold step; rw [if_pos h]

/-- The odd branch of `step`, as a rewrite rule. -/
theorem step_of_odd {m : ℕ} (h : m % 2 = 1) : step m = 3 * m + 1 := by
  unfold step; rw [if_neg (by omega)]

/-- Odd steps taken in the first `k` steps of the orbit of `n`. -/
def oddSteps (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => oddSteps n k + (if step^[k] n % 2 = 1 then 1 else 0)

/-- Even (halving) steps taken in the first `k` steps of the orbit of `n`. -/
def evenSteps (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => evenSteps n k + (if step^[k] n % 2 = 0 then 1 else 0)

@[simp] theorem oddSteps_zero (n : ℕ) : oddSteps n 0 = 0 := rfl

@[simp] theorem evenSteps_zero (n : ℕ) : evenSteps n 0 = 0 := rfl

theorem oddSteps_succ_of_odd {n k : ℕ} (h : step^[k] n % 2 = 1) :
    oddSteps n (k + 1) = oddSteps n k + 1 := by
  simp [oddSteps, h]

theorem oddSteps_succ_of_even {n k : ℕ} (h : step^[k] n % 2 = 0) :
    oddSteps n (k + 1) = oddSteps n k := by
  simp [oddSteps, h]

theorem evenSteps_succ_of_even {n k : ℕ} (h : step^[k] n % 2 = 0) :
    evenSteps n (k + 1) = evenSteps n k + 1 := by
  simp [evenSteps, h]

theorem evenSteps_succ_of_odd {n k : ℕ} (h : step^[k] n % 2 = 1) :
    evenSteps n (k + 1) = evenSteps n k := by
  simp [evenSteps, h]

/-- The two counts partition the first `k` steps. -/
theorem oddSteps_add_evenSteps (n k : ℕ) : oddSteps n k + evenSteps n k = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rcases (by omega : step^[k] n % 2 = 0 ∨ step^[k] n % 2 = 1) with h | h
    · rw [oddSteps_succ_of_even h, evenSteps_succ_of_even h]; omega
    · rw [oddSteps_succ_of_odd h, evenSteps_succ_of_odd h]; omega

/-- The per-odd-step growth constant available to an orbit that never drops below
the floor `N`: the `+1` costs at most `1/N` on top of the `3`.  `growth 1 = 4`
(no information); `growth N → 3` as the floor rises. -/
noncomputable def growth (N : ℕ) : ℝ := 3 + 1 / N

theorem growth_pos {N : ℕ} (hN : 1 ≤ N) : 0 < growth N := by
  have : (0:ℝ) < N := by exact_mod_cast hN
  unfold growth; positivity

/-- One odd step costs at most the growth constant, provided the orbit is above
the floor.  This is the only place the `+1` is touched. -/
theorem three_mul_add_one_le {m N : ℕ} (hN : 1 ≤ N) (hm : N ≤ m) :
    (3 * m + 1 : ℝ) ≤ growth N * m := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hm' : (N:ℝ) ≤ m := by exact_mod_cast hm
  have h1 : (1:ℝ) ≤ (m:ℝ) / N := (one_le_div hN0).mpr hm'
  have : growth N * m = 3 * m + m / N := by
    unfold growth; field_simp
  rw [this]
  linarith

/-- **The drift estimate.**  Over the first `k` steps of an orbit that never drops
below `N`, the halving budget `2^b` and the growth budget `growth N ^ a` bracket
the orbit's size:

`n_k · 2^b ≤ n · (growth N)^a`.

Every even step is an exact `2`, so it costs nothing to carry; every odd step
spends one unit of the growth budget. -/
theorem iterate_mul_two_pow_le {n N : ℕ} (hN : 1 ≤ N) :
    ∀ k, (∀ j < k, N ≤ step^[j] n) →
      (step^[k] n : ℝ) * 2 ^ evenSteps n k ≤ (n : ℝ) * growth N ^ oddSteps n k := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hfloor
    have ihk := ih fun j hj => hfloor j (by omega)
    have hk : N ≤ step^[k] n := hfloor k (by omega)
    rw [Function.iterate_succ_apply']
    rcases (by omega : step^[k] n % 2 = 0 ∨ step^[k] n % 2 = 1) with h | h
    · -- even step: exact halving, the budget is untouched
      have hstep : step (step^[k] n) = step^[k] n / 2 := step_of_even h
      have hdouble : (step^[k] n : ℝ) = 2 * ((step^[k] n / 2 : ℕ) : ℝ) := by
        have : step^[k] n = 2 * (step^[k] n / 2) := by omega
        exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) this
      rw [hstep, oddSteps_succ_of_even h, evenSteps_succ_of_even h, pow_succ]
      rw [hdouble] at ihk
      calc ((step^[k] n / 2 : ℕ) : ℝ) * (2 ^ evenSteps n k * 2)
          = 2 * ((step^[k] n / 2 : ℕ) : ℝ) * 2 ^ evenSteps n k := by ring
        _ ≤ (n : ℝ) * growth N ^ oddSteps n k := ihk
    · -- odd step: one unit of the growth budget
      have hstep : step (step^[k] n) = 3 * step^[k] n + 1 := step_of_odd h
      have hgrow := three_mul_add_one_le (m := step^[k] n) hN hk
      have hgpos := growth_pos hN
      have htwo : (0:ℝ) < 2 ^ evenSteps n k := by positivity
      rw [hstep, oddSteps_succ_of_odd h, evenSteps_succ_of_odd h, pow_succ]
      have hcast : ((3 * step^[k] n + 1 : ℕ) : ℝ) = 3 * (step^[k] n : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      calc (3 * (step^[k] n : ℝ) + 1) * 2 ^ evenSteps n k
          ≤ (growth N * (step^[k] n : ℝ)) * 2 ^ evenSteps n k := by
            exact mul_le_mul_of_nonneg_right hgrow (le_of_lt htwo)
        _ = growth N * ((step^[k] n : ℝ) * 2 ^ evenSteps n k) := by ring
        _ ≤ growth N * ((n : ℝ) * growth N ^ oddSteps n k) := by
            exact mul_le_mul_of_nonneg_left ihk (le_of_lt hgpos)
        _ = (n : ℝ) * (growth N ^ oddSteps n k * growth N) := by ring

/-- **The descent criterion.**  If the halving budget beats the growth budget, the
orbit has strictly descended below its starting point.  `conjecture_iff_descent`
(in `Descent.lean`) says descent for every start *is* the Collatz conjecture. -/
theorem lt_of_growth_lt {n N k : ℕ} (hn : 1 ≤ n) (hN : 1 ≤ N)
    (hfloor : ∀ j < k, N ≤ step^[j] n)
    (h : growth N ^ oddSteps n k < 2 ^ evenSteps n k) :
    step^[k] n < n := by
  have key := iterate_mul_two_pow_le hN k hfloor
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hlt : (n : ℝ) * growth N ^ oddSteps n k < (n : ℝ) * 2 ^ evenSteps n k :=
    mul_lt_mul_of_pos_left h hn0
  have htwo : (0:ℝ) < 2 ^ evenSteps n k := by positivity
  have : (step^[k] n : ℝ) * 2 ^ evenSteps n k < (n : ℝ) * 2 ^ evenSteps n k :=
    lt_of_le_of_lt key hlt
  have hfin := lt_of_mul_lt_mul_right this (le_of_lt htwo)
  exact_mod_cast hfin

/-! ## The frequency form

Descent is a statement about the *rate* at which odd steps occur.  Dividing the
budget inequality by `k` turns `growth N ^ a < 2 ^ b` into a threshold on the
odd-step frequency `a / k`. -/

@[simp] theorem growth_one : growth 1 = 4 := by unfold growth; norm_num

theorem one_lt_growth {N : ℕ} (hN : 1 ≤ N) : 1 < growth N := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have : 0 < 1 / (N:ℝ) := by positivity
  unfold growth; linarith

theorem log_two_growth_pos {N : ℕ} (hN : 1 ≤ N) : 0 < Real.log (2 * growth N) :=
  Real.log_pos (by have := one_lt_growth hN; linarith)

/-- The odd-step frequency an orbit above the floor `N` is allowed before it may
stop descending: `log 2 / log (2 · growth N)`.  At `N = 1` this is exactly `1/3`
(`freqThreshold_one`); it rises to `log 2 / log 6 ≈ 0.3868…` as the floor rises
(`tendsto_freqThreshold`). -/
noncomputable def freqThreshold (N : ℕ) : ℝ := Real.log 2 / Real.log (2 * growth N)

/-- The information-free floor gives exactly the crude threshold `1/3` - which is
also the odd-step frequency of a *typical* orbit (one odd step per two halvings),
so the crude bound is blind by exactly one degenerate case.  The whole content of
this file is moving off that number. -/
theorem freqThreshold_one : freqThreshold 1 = 1 / 3 := by
  unfold freqThreshold
  rw [growth_one]
  have h8 : (2:ℝ) * 4 = 2 ^ (3:ℕ) := by norm_num
  rw [h8, Real.log_pow]
  have hne : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  push_cast
  field_simp

/-- **The frequency form of the descent criterion.**  An orbit that stays above
the floor `N` and takes odd steps at frequency strictly below `freqThreshold N`
over its first `k` steps has strictly descended. -/
theorem lt_of_oddSteps_freq_lt {n N k : ℕ} (hn : 1 ≤ n) (hN : 1 ≤ N) (hk : 0 < k)
    (hfloor : ∀ j < k, N ≤ step^[j] n)
    (h : (oddSteps n k : ℝ) / k < freqThreshold N) :
    step^[k] n < n := by
  have hab : oddSteps n k + evenSteps n k = k := oddSteps_add_evenSteps n k
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hgpos := growth_pos hN
  have hlog2g := log_two_growth_pos hN
  have hsplit : Real.log (2 * growth N) = Real.log 2 + Real.log (growth N) :=
    Real.log_mul (by norm_num) (ne_of_gt hgpos)
  rw [freqThreshold, div_lt_div_iff₀ hk0 hlog2g] at h
  have hk' : (k:ℝ) = (oddSteps n k : ℝ) + (evenSteps n k : ℝ) := by exact_mod_cast hab.symm
  rw [hsplit, hk'] at h
  have h2 : (oddSteps n k : ℝ) * Real.log (growth N)
      < (evenSteps n k : ℝ) * Real.log 2 := by nlinarith [h]
  have h3 : growth N ^ oddSteps n k < 2 ^ evenSteps n k := by
    have hlog : Real.log (growth N ^ oddSteps n k) < Real.log ((2:ℝ) ^ evenSteps n k) := by
      rw [Real.log_pow, Real.log_pow]; exact h2
    exact (Real.log_lt_log_iff (pow_pos hgpos _) (pow_pos (by norm_num) _)).mp hlog
  exact lt_of_growth_lt hn hN hfloor h3

/-- The sharp Collatz drift threshold `log 2 / log 6 ≈ 0.3868…`: the supremum of
admissible odd-step frequencies, approached from below as the floor rises.  It is
`freqThreshold` with the `+1` overhead switched off entirely. -/
noncomputable def sharpThreshold : ℝ := Real.log 2 / Real.log 6

/-- No finite floor reaches the sharp threshold: the `+1` always costs something.
The sharp constant is a supremum, never an allowance. -/
theorem freqThreshold_lt_sharp {N : ℕ} (hN : 1 ≤ N) : freqThreshold N < sharpThreshold := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hgt : (6:ℝ) < 2 * growth N := by
    have : 0 < 1 / (N:ℝ) := by positivity
    unfold growth; linarith
  unfold freqThreshold sharpThreshold
  gcongr

/-- **The sharp constant is the limit.**  As the floor rises the admissible
odd-step frequency rises to `log 2 / log 6`: the `+1` overhead is exactly what
separates a divergent orbit's budget from the ideal `n · 3^a / 2^b`. -/
theorem tendsto_freqThreshold :
    Filter.Tendsto freqThreshold Filter.atTop (nhds sharpThreshold) := by
  unfold sharpThreshold
  have hg : Filter.Tendsto (fun N : ℕ => 2 * growth N) Filter.atTop (nhds 6) := by
    have h1 : Filter.Tendsto (fun N : ℕ => (1:ℝ) / N) Filter.atTop (nhds 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have h2 : Filter.Tendsto (fun N : ℕ => growth N) Filter.atTop (nhds 3) := by
      unfold growth
      simpa using Filter.Tendsto.const_add (3:ℝ) h1
    have h3 := h2.const_mul (2:ℝ)
    norm_num at h3
    exact h3
  have hlog : Filter.Tendsto (fun N : ℕ => Real.log (2 * growth N)) Filter.atTop
      (nhds (Real.log 6)) :=
    (Real.continuousAt_log (by norm_num)).tendsto.comp hg
  have hne : Real.log 6 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  exact Filter.Tendsto.div tendsto_const_nhds hlog hne

/-! ## The floor is free

The drift estimate is conditioned on a floor `N` the orbit stays above.  Front A
supplies it at no cost: an unbounded orbit can never repeat a value (a repeat
makes it eventually periodic, hence bounded), so the map `k ↦ n_k` is injective
and each of the finitely many values below `N` is visited at most once.  Past the
last such visit the orbit is above `N` forever.

This is why `lt_of_oddSteps_freq_lt` is usable against divergence with the *sharp*
constant rather than the crude one: a divergent orbit admits every floor, so it
must respect `freqThreshold N` for every `N`, and `tendsto_freqThreshold` pushes
that to `log 2 / log 6`. -/

/-- Shifting by the period, above the repeat point. -/
theorem iterate_add_period_eq {n i j : ℕ} (hij : i < j) (h : step^[i] n = step^[j] n)
    {a : ℕ} (ha : i ≤ a) : step^[a + (j - i)] n = step^[a] n := by
  have hj : i + (j - i) = j := by omega
  calc step^[a + (j - i)] n
      = step^[(a - i) + (i + (j - i))] n := by
        rw [show (a - i) + (i + (j - i)) = a + (j - i) by omega]
    _ = step^[a - i] (step^[i + (j - i)] n) := Function.iterate_add_apply _ _ _ _
    _ = step^[a - i] (step^[i] n) := by rw [hj, ← h]
    _ = step^[(a - i) + i] n := (Function.iterate_add_apply _ _ _ _).symm
    _ = step^[a] n := by rw [show (a - i) + i = a by omega]

/-- After a repeat, every orbit value is already among the first `j`. -/
theorem exists_lt_of_repeat {n i j : ℕ} (hij : i < j) (h : step^[i] n = step^[j] n) (k : ℕ) :
    ∃ t < j, step^[k] n = step^[t] n := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk : k < j
    · exact ⟨k, hk, rfl⟩
    · have hai : i ≤ k - (j - i) := by omega
      have hlt : k - (j - i) < k := by omega
      have hshift := iterate_add_period_eq hij h hai
      rw [show k - (j - i) + (j - i) = k by omega] at hshift
      obtain ⟨t, ht, hteq⟩ := ih _ hlt
      exact ⟨t, ht, by rw [hshift, hteq]⟩

/-- **A repeat kills divergence**: an eventually periodic orbit is bounded. -/
theorem not_diverges_of_repeat {n i j : ℕ} (hij : i < j) (h : step^[i] n = step^[j] n) :
    ¬ Diverges n := by
  intro hdiv
  obtain ⟨k, hk⟩ := hdiv ((Finset.range j).sup (fun t => step^[t] n) + 1)
  obtain ⟨t, ht, hteq⟩ := exists_lt_of_repeat hij h k
  have hle : step^[t] n ≤ (Finset.range j).sup (fun t => step^[t] n) :=
    Finset.le_sup (f := fun t => step^[t] n) (Finset.mem_range.mpr ht)
  rw [hteq] at hk
  omega

/-- A divergent orbit visits every value at most once. -/
theorem injective_of_diverges {n : ℕ} (hdiv : Diverges n) :
    Function.Injective (fun k => step^[k] n) := by
  intro a b hab
  by_contra hne
  rcases Nat.lt_or_ge a b with hlt | hge
  · exact not_diverges_of_repeat hlt hab hdiv
  · exact not_diverges_of_repeat (by omega : b < a) hab.symm hdiv

/-- **Divergence supplies its own floor**: for every `N`, a divergent orbit is
eventually above `N`. -/
theorem exists_floor_of_diverges {n : ℕ} (hdiv : Diverges n) (N : ℕ) :
    ∃ K, ∀ k, K ≤ k → N ≤ step^[k] n := by
  have hinj := injective_of_diverges hdiv
  have hpre : ((fun k => step^[k] n) ⁻¹' (Set.Iio N)).Finite :=
    Set.Finite.preimage hinj.injOn (Set.finite_Iio N)
  obtain ⟨M, hM⟩ := hpre.bddAbove
  refine ⟨M + 1, fun k hk => ?_⟩
  by_contra hlt
  have hmem : k ∈ (fun k => step^[k] n) ⁻¹' (Set.Iio N) := Nat.not_le.mp hlt
  have := hM hmem
  omega

/-- Removing a finite prefix does not change whether a Collatz orbit is
unbounded.  The reverse implication uses `exists_floor_of_diverges`: an
unbounded orbit is eventually past both the requested height and the removed
prefix. -/
theorem diverges_iterate_iff {n K : ℕ} : Diverges (step^[K] n) ↔ Diverges n := by
  constructor
  · intro hdiv M
    obtain ⟨j, hj⟩ := hdiv M
    refine ⟨j + K, ?_⟩
    rwa [Function.iterate_add_apply]
  · intro hdiv M
    obtain ⟨J, hJ⟩ := exists_floor_of_diverges hdiv M
    let j := max J K
    have hJj : J ≤ j := Nat.le_max_left _ _
    have hKj : K ≤ j := Nat.le_max_right _ _
    refine ⟨j - K, ?_⟩
    calc
      M ≤ step^[j] n := hJ j hJj
      _ = step^[j - K + K] n := by rw [Nat.sub_add_cancel hKj]
      _ = step^[j - K] (step^[K] n) := Function.iterate_add_apply step _ _ n

/-- **Front-A descent consumption.**  To rule out divergence it is enough to
make every *divergent* starting value dip below itself.  Unlike `DescentAll`,
this hypothesis says nothing about points on bounded nontrivial cycles, so it
respects the two-front architecture. -/
theorem noDivergent_of_descends_if_diverges
    (h : ∀ n, 1 ≤ n → Diverges n → ∃ k, step^[k] n < n) : NoDivergentOrbit := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro hn hdiv
      obtain ⟨k, hk⟩ := h n hn hdiv
      have hpos : 1 ≤ step^[k] n := iterate_step_pos hn k
      have htail : Diverges (step^[k] n) := (diverges_iterate_iff (n := n) (K := k)).2 hdiv
      exact ih _ hk hpos htail

/-- Frequency-specialized Front-A consumption.  This is the condition the
rigidity lane actually needs: a drift-winning window only for starts already
assumed divergent.  Cyclic starts are deliberately outside the hypothesis. -/
theorem noDivergent_of_freq_descent_if_diverges
    (h : ∀ n, 1 ≤ n → Diverges n → ∃ N k, 1 ≤ N ∧ 0 < k ∧
      (∀ j < k, N ≤ step^[j] n) ∧
      (oddSteps n k : ℝ) / k < freqThreshold N) : NoDivergentOrbit := by
  apply noDivergent_of_descends_if_diverges
  intro n hn hdiv
  obtain ⟨N, k, hN, hk, hfloor, hfreq⟩ := h n hn hdiv
  exact ⟨k, lt_of_oddSteps_freq_lt hn hN hk hfloor hfreq⟩

/-- **The full-conjecture consumption form.**  A drift-frequency bound available
at *every* starting point is already the Collatz conjecture via
`conjecture_iff_descent`.  This is intentionally stronger than the Front-A-only
form `noDivergent_of_freq_descent_if_diverges` above: it also forces descent from
points on hypothetical bounded nontrivial cycles. -/
theorem conjecture_of_freq_descent
    (h : ∀ n, 2 ≤ n → ∃ N k, 1 ≤ N ∧ 0 < k ∧ (∀ j < k, N ≤ step^[j] n) ∧
      (oddSteps n k : ℝ) / k < freqThreshold N) : Conjecture := by
  apply conjecture_of_descent
  intro n hn
  obtain ⟨N, k, hN, hk, hfloor, hfreq⟩ := h n hn
  exact ⟨k, lt_of_oddSteps_freq_lt (by omega) hN hk hfloor hfreq⟩

/-- **The mirror of the drift estimate.**  Dropping the `+1` can only *under*count,
so the ideal ratio `3^a / 2^b` is a genuine lower bound.  This direction needs no
floor, no `growth` constant and no reals - it is pure `ℕ`. -/
theorem mul_three_pow_le (n : ℕ) :
    ∀ k, n * 3 ^ oddSteps n k ≤ step^[k] n * 2 ^ evenSteps n k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    rcases (by omega : step^[k] n % 2 = 0 ∨ step^[k] n % 2 = 1) with h | h
    · rw [step_of_even h, oddSteps_succ_of_even h, evenSteps_succ_of_even h, pow_succ]
      have hdvd : 2 ∣ step^[k] n := by omega
      have hd : step^[k] n / 2 * 2 = step^[k] n := Nat.div_mul_cancel hdvd
      calc n * 3 ^ oddSteps n k
          ≤ step^[k] n * 2 ^ evenSteps n k := ih
        _ = step^[k] n / 2 * 2 * 2 ^ evenSteps n k := by rw [hd]
        _ = step^[k] n / 2 * (2 ^ evenSteps n k * 2) := by ring
    · rw [step_of_odd h, oddSteps_succ_of_odd h, evenSteps_succ_of_odd h, pow_succ]
      calc n * (3 ^ oddSteps n k * 3)
          = n * 3 ^ oddSteps n k * 3 := by ring
        _ ≤ step^[k] n * 2 ^ evenSteps n k * 3 := Nat.mul_le_mul_right 3 ih
        _ = 3 * step^[k] n * 2 ^ evenSteps n k := by ring
        _ ≤ (3 * step^[k] n + 1) * 2 ^ evenSteps n k :=
            Nat.mul_le_mul_right _ (by omega)

end CollatzMoonshot
