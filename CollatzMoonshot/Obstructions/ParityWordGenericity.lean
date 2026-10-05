/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib
import CollatzMoonshot.FrontA.ParityReconstruction

/-!
# Genericity of a divergent orbit's parity word

Read a hypothetical divergent orbit's parity sequence as a binary word, or as the real
`0.w₀w₁w₂…₂`.  Is that word normal?  Disjunctive?  Is the real irrational?  Transcendental?
(Trevor, 2026-09-20; the prose verdict is in `APPROACHES.md`, "Cross-repo: the Diophantine wall".)

**The answer depends on the encoding.**

* `rawWord` (the plain `step` map): `3n + 1` is always even, so `11` never occurs
  (`rawWord_succ_false`).  The word is neither disjunctive (`rawWord_not_disjunctive`) nor
  normal (`rawWord_not_normal`), for every start, divergent or not.
* `accWord` (the shortcut map `tstep`):
  - **Normality is false** for a divergent orbit (`accWord_not_normal_of_diverges`).  The drift
    bound forces the 1-density up to at least `log 2 / log 3 ≈ 0.631`
    (`accOnes_freq_eventually_ge`), and a normal word has 1-density `1/2`.
  - **Disjunctivity is open**, and it implies arbitrarily long runs of odd steps
    (`divergentWordDisjunctive_imp_longOddRuns`).  It is a stronger target than the run question,
    so it cannot be a route to it.
  - **Irrationality is aperiodicity restated** (`irrational_parityReal_accWord`): the repo
    already proves that an eventually periodic shortcut parity forces a cycle
    (`FrontA.not_diverges_of_eventually_periodic_parity`).
  - **Transcendence**: Adamczewski–Bugeaud (`Literature.AdamczewskiBugeaud2007`) applies only
    to words of *linear* factor complexity, the Sturmian end.  Nothing about divergence pushes
    the word there (`DivergentWordLowComplexity` is the missing input), and that end is where
    `DIRECTION.md` already retired the Christoffel / Cobham angle.

None of these is a lever on the run-count gap node.  The rows live in `Maze.lean`.
-/

namespace CollatzMoonshot.Obstructions.ParityWord

open Filter Topology CollatzMoonshot.FrontB

/-! ## Word notions -/

/-- `u` occurs in `w` at position `i`. -/
def OccursAt (w : ℕ → Bool) (u : List Bool) (i : ℕ) : Prop :=
  ∀ j : Fin u.length, w (i + j) = u.get j

instance (w : ℕ → Bool) (u : List Bool) (i : ℕ) : Decidable (OccursAt w u i) := by
  unfold OccursAt; infer_instance

/-- Every finite word occurs somewhere. -/
def Disjunctive (w : ℕ → Bool) : Prop := ∀ u : List Bool, ∃ i, OccursAt w u i

/-- Occurrences of `u` starting before position `k`. -/
def occ (w : ℕ → Bool) (u : List Bool) (k : ℕ) : ℕ :=
  ((Finset.range k).filter fun i => OccursAt w u i).card

/-- Normal to base `2` (Borel's block form): every block `u` has asymptotic frequency
`2^(-|u|)`. -/
def Normal (w : ℕ → Bool) : Prop :=
  ∀ u : List Bool, Tendsto (fun k => (occ w u k : ℝ) / k) atTop (𝓝 ((1 / 2 : ℝ) ^ u.length))

/-- Periodic from some point on. -/
def EventuallyPeriodic (w : ℕ → Bool) : Prop :=
  ∃ M p, 1 ≤ p ∧ ∀ k, M ≤ k → w k = w (k + p)

/-- The factor complexity `p_w(L)`: the number of distinct length-`L` blocks of `w`. -/
noncomputable def complexity (w : ℕ → Bool) (L : ℕ) : ℕ :=
  Set.ncard {u : Fin L → Bool | ∃ i, ∀ j : Fin L, w (i + j) = u j}

/-- The real `0.w₀w₁w₂…` in base `2`. -/
noncomputable def parityReal (w : ℕ → Bool) : ℝ :=
  ∑' k, (if w k then (1 : ℝ) else 0) / 2 ^ (k + 1)

/-! ## The two encodings -/

/-- Parity word of the plain `step` orbit (`true` = odd). -/
def rawWord (n : ℕ) : ℕ → Bool := fun k => decide (step^[k] n % 2 = 1)

/-- Parity word of the shortcut `tstep` orbit (`true` = odd). -/
def accWord (n : ℕ) : ℕ → Bool := fun k => decide (tstep^[k] n % 2 = 1)

/-! ## Raw encoding: the golden-mean subshift -/

/-- An odd plain step is always followed by an even one. -/
theorem rawWord_succ_false {n k : ℕ} (h : rawWord n k = true) : rawWord n (k + 1) = false := by
  simp only [rawWord, decide_eq_true_eq, decide_eq_false_iff_not] at h ⊢
  rw [Function.iterate_succ_apply', step_of_odd h]
  omega

theorem not_occursAt_rawWord_tt (n i : ℕ) : ¬ OccursAt (rawWord n) [true, true] i := by
  intro hi
  have h0 : rawWord n i = true := by simpa using hi ⟨0, by simp⟩
  have h1 : rawWord n (i + 1) = true := by simpa using hi ⟨1, by simp⟩
  rw [rawWord_succ_false h0] at h1
  exact Bool.false_ne_true h1

/-- **Raw encoding, not disjunctive**, for every start. -/
theorem rawWord_not_disjunctive (n : ℕ) : ¬ Disjunctive (rawWord n) := fun h =>
  let ⟨i, hi⟩ := h [true, true]
  not_occursAt_rawWord_tt n i hi

/-- **Raw encoding, not normal**, for every start: the block `11` has frequency `0`, not `1/4`. -/
theorem rawWord_not_normal (n : ℕ) : ¬ Normal (rawWord n) := by
  intro h
  have hocc : ∀ k, occ (rawWord n) [true, true] k = 0 := fun k => by
    rw [occ, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun i _ => not_occursAt_rawWord_tt n i
  have ht := h [true, true]
  simp only [hocc, Nat.cast_zero, zero_div] at ht
  have := tendsto_nhds_unique ht tendsto_const_nhds
  norm_num at this

/-! ## Shortcut encoding: normality -/

theorem three_fifths_lt_log_two_div_log_three : (3 / 5 : ℝ) < Real.log 2 / Real.log 3 := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  rw [lt_div_iff₀ h3]
  have hlt : Real.log 27 < Real.log 32 := Real.log_lt_log (by norm_num) (by norm_num)
  have e27 : Real.log 27 = 3 * Real.log 3 := by
    rw [show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]; norm_num
  have e32 : Real.log 32 = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]; norm_num
  linarith

/-- **The drift bound in shortcut form.**  A divergent orbit's shortcut parity word has
1-density eventually at least any `v < log 2 / log 3`.

Confidence 95%.  English proof: by `FrontA.exists_step_count` the shortcut orbit is a
subsequence of the plain orbit at indices tending to infinity, so it tends to infinity too
(`exists_floor_of_diverges`).  Fix a floor `N`, and `K₀` past which the shortcut orbit stays
above `N`.  Above `N` an odd shortcut step multiplies by at most `(3 + 1/N)/2` and an even one
by `1/2`, so with `a` ones in the window `[K₀, m)`,
`x_m ≤ x_{K₀} · (3 + 1/N)^a / 2^(m - K₀)`.  Since `x_m → ∞`, eventually `x_m > x_{K₀}`, giving
`a / (m - K₀) > log 2 / log (3 + 1/N)`.  Choose `N` with that threshold above `v` (it rises to
`log 2 / log 3`), then absorb the fixed prefix `K₀`, which costs `O(K₀ / m)`.  This is
`Rigidity/Drift.lean`'s `lt_of_oddSteps_freq_lt` with `growth N / 2` per shortcut odd step;
the plain-map threshold `log 2 / log 6` corresponds to `log 2 / log 3` here, because each
shortcut `1` is the plain block `10`. -/
theorem accOnes_freq_eventually_ge {n : ℕ} (_hn : 1 ≤ n) (_hdiv : Diverges n) {v : ℝ}
    (_hv : v < Real.log 2 / Real.log 3) :
    ∀ᶠ m in atTop, v ≤ (occ (accWord n) [true] m : ℝ) / m := by
  sorry

/-- **Shortcut encoding, not normal** for a divergent orbit: its 1-density is eventually above
`3/5`, and a normal word's is `1/2`. -/
theorem accWord_not_normal_of_diverges {n : ℕ} (hn : 1 ≤ n) (hdiv : Diverges n) :
    ¬ Normal (accWord n) := by
  intro h
  have h1 := accOnes_freq_eventually_ge hn hdiv three_fifths_lt_log_two_div_log_three
  have h2 := (h [true]).eventually
    (eventually_lt_nhds (show ((1 : ℝ) / 2) ^ [true].length < 3 / 5 by norm_num))
  obtain ⟨m, hm1, hm2⟩ := (h1.and h2).exists
  linarith

/-! ## Shortcut encoding: disjunctivity (open) -/

/-- **Open node.**  Every divergent orbit's shortcut parity word is disjunctive.  Nothing known
forces it: the drift bound constrains only the 1-density, and the periodic pattern `110`
(density `2/3`, factor `9/8` per period) already grows with every odd run of length at most 2. -/
def DivergentWordDisjunctive : Prop := ∀ n, 1 ≤ n → Diverges n → Disjunctive (accWord n)

/-- **Open node.**  Every divergent orbit has arbitrarily long runs of consecutive odd shortcut
steps.  Not forced by density alone (see `DivergentWordDisjunctive`). -/
def DivergentLongOddRuns : Prop :=
  ∀ n, 1 ≤ n → Diverges n → ∀ L, ∃ i, ∀ j < L, accWord n (i + j) = true

theorem Disjunctive.exists_run {w : ℕ → Bool} (h : Disjunctive w) (L : ℕ) :
    ∃ i, ∀ j < L, w (i + j) = true := by
  obtain ⟨i, hi⟩ := h (List.replicate L true)
  exact ⟨i, fun j hj => by simpa using hi ⟨j, by simpa using hj⟩⟩

/-- Disjunctivity is the stronger target, so it is no route to the run question. -/
theorem divergentWordDisjunctive_imp_longOddRuns (h : DivergentWordDisjunctive) :
    DivergentLongOddRuns := fun n hn hdiv => (h n hn hdiv).exists_run

/-! ## Irrationality: aperiodicity restated -/

/-- A divergent orbit's shortcut parity word is not eventually periodic.  This is
`FrontA.not_diverges_of_eventually_periodic_parity`, read as a statement about the word. -/
theorem accWord_not_eventuallyPeriodic {n : ℕ} (hn : 1 ≤ n) (hdiv : Diverges n) :
    ¬ EventuallyPeriodic (accWord n) := by
  rintro ⟨M, p, hp, hper⟩
  refine FrontA.not_diverges_of_eventually_periodic_parity (M := M) hn hp (fun k hk => ?_) hdiv
  have h := hper k hk
  simp only [accWord] at h
  rcases Nat.mod_two_eq_zero_or_one (tstep^[k] n) with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one (tstep^[k + p] n) with hb | hb <;> simp_all

/-- A binary expansion that is not eventually periodic is irrational.

Confidence 97%.  English proof: a rational in `[0, 1]` has an eventually periodic binary
expansion (long division by its denominator `q` has at most `q` remainders), and a dyadic
rational's two expansions are both eventually constant.  `parityReal w` has digit sequence `w`,
so if it were rational, `w` would be one of those expansions. -/
theorem irrational_parityReal_of_not_eventuallyPeriodic {w : ℕ → Bool}
    (_hw : ¬ EventuallyPeriodic w) : Irrational (parityReal w) := by
  sorry

/-- **The parity real of a divergent orbit is irrational.** -/
theorem irrational_parityReal_accWord {n : ℕ} (hn : 1 ≤ n) (hdiv : Diverges n) :
    Irrational (parityReal (accWord n)) :=
  irrational_parityReal_of_not_eventuallyPeriodic (accWord_not_eventuallyPeriodic hn hdiv)

/-! ## Transcendence: the criterion points the wrong way -/

/-- **Reopen condition (wall).**  Divergent orbits have shortcut parity words of linear factor
complexity along a subsequence.  This is what Adamczewski–Bugeaud consumes.  A divergent word is
expected to look random, which is the opposite end. -/
def DivergentWordLowComplexity : Prop :=
  ∀ n, 1 ≤ n → Diverges n → ∃ C : ℕ, ∃ᶠ L in atTop, complexity (accWord n) L ≤ C * L

end CollatzMoonshot.Obstructions.ParityWord

namespace CollatzMoonshot.Literature

open Filter CollatzMoonshot.Obstructions.ParityWord

/-- **Adamczewski & Bugeaud**, *On the complexity of algebraic numbers I. Expansions in integer
bases*, Ann. of Math. 165 (2007) 547–565: the base-`b` expansion of an irrational algebraic
number has `p(L)/L → ∞`.  Transcribed for `b = 2` and combined with the standard fact that a
non-eventually-periodic expansion is irrational: linear complexity along a subsequence forces
transcendence.  Faithful to the main theorem as recalled; the step most needing an expert check
is that the source's conclusion is `lim inf p(L)/L = ∞` (so a subsequence with `p(L) ≤ C·L`
suffices), unchecked against the paper body. -/
def AdamczewskiBugeaud2007 : Prop :=
  ∀ w : ℕ → Bool, ¬ EventuallyPeriodic w → (∃ C : ℕ, ∃ᶠ L in atTop, complexity w L ≤ C * L) →
    Transcendental ℚ (parityReal w)

end CollatzMoonshot.Literature

namespace CollatzMoonshot.Obstructions.ParityWord

/-- The wiring edge: with the reopen input, Adamczewski–Bugeaud would make every divergent
orbit's parity real transcendental.  Without it, the criterion says nothing. -/
theorem transcendental_parityReal_of_lowComplexity
    (hAB : Literature.AdamczewskiBugeaud2007) (hlow : DivergentWordLowComplexity)
    {n : ℕ} (hn : 1 ≤ n) (hdiv : Diverges n) : Transcendental ℚ (parityReal (accWord n)) :=
  hAB _ (accWord_not_eventuallyPeriodic hn hdiv) (hlow n hn hdiv)

end CollatzMoonshot.Obstructions.ParityWord
