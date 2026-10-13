/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Collatz's original permutation (Conway's "amusical permutation")

`U(2n) = 3n`, `U(4n+1) = 3n+1`, `U(4n+3) = 3n+2`, a permutation of `ℤ`.  The open question is
whether the orbit of `8` is infinite.

Sources:
* Lagarias, arXiv:2111.02635v1: one of Collatz's original problems from the 1930s; the
  question about `n = 8` was raised by Murray Klamkin in 1963 and "remains unsolved".
* Conway, *On unsettleable arithmetical problems*, Amer. Math. Monthly 120 (2013) 192-198
  (summary: `papers/2013-conway-unsettleable-summary.md`).  He writes the same map as
  `2k ↦ 3k, 4k+1 ↦ 3k+1, 4k−1 ↦ 3k−1` and offers "8 lies on an infinite cycle" as his candidate
  for the simplest unsettleable statement.

The defining equations are `amusical_two_mul`, `amusical_four_mul_add_one` and
`amusical_four_mul_add_three`; the permutation is `amusicalPerm`; the open problem is the node
`AmusicalOrbitOfEightInfinite`, with `amusicalOrbitOfEightInfinite_iff` reducing it to
"`8` is not a periodic point".
-/

namespace CollatzMoonshot.Amusical

/-- Collatz's permutation `U` on `ℤ`. -/
def amusical (n : ℤ) : ℤ :=
  if n % 2 = 0 then 3 * (n / 2)
  else if n % 4 = 1 then 3 * (n / 4) + 1
  else 3 * (n / 4) + 2

/-- The inverse of `amusical`: `3m ↦ 2m`, `3m+1 ↦ 4m+1`, `3m+2 ↦ 4m+3`. -/
def amusicalInv (m : ℤ) : ℤ :=
  if m % 3 = 0 then 2 * (m / 3)
  else if m % 3 = 1 then 4 * (m / 3) + 1
  else 4 * (m / 3) + 3

theorem amusical_two_mul (n : ℤ) : amusical (2 * n) = 3 * n := by
  unfold amusical; split_ifs <;> omega

theorem amusical_four_mul_add_one (n : ℤ) : amusical (4 * n + 1) = 3 * n + 1 := by
  unfold amusical; split_ifs <;> omega

theorem amusical_four_mul_add_three (n : ℤ) : amusical (4 * n + 3) = 3 * n + 2 := by
  unfold amusical; split_ifs <;> omega

theorem amusicalInv_amusical (n : ℤ) : amusicalInv (amusical n) = n := by
  unfold amusical amusicalInv; split_ifs <;> omega

theorem amusical_amusicalInv (m : ℤ) : amusical (amusicalInv m) = m := by
  unfold amusical amusicalInv; split_ifs <;> omega

/-- `U` is a permutation of `ℤ`. -/
def amusicalPerm : Equiv.Perm ℤ where
  toFun := amusical
  invFun := amusicalInv
  left_inv := amusicalInv_amusical
  right_inv := amusical_amusicalInv

theorem amusical_injective : Function.Injective amusical :=
  amusicalPerm.injective

/-- The first thirteen steps from `8`: `8, 12, 18, 27, 20, 30, 45, 34, 51, 38, 57, 43, 32, 48`. -/
theorem amusical_orbit_eight_prefix :
    (List.range 14).map (fun k => amusical^[k] 8) =
      [8, 12, 18, 27, 20, 30, 45, 34, 51, 38, 57, 43, 32, 48] := by
  decide

/-- **Open (Collatz 1930s, Klamkin 1963; Conway 2013 suggests it may be unsettleable).**
The forward orbit of `8` under `U` is infinite.

Believed true.  Heuristic: on a random integer `U` multiplies by `3/2` with probability `1/2` and
by `3/4` with probability `1/2`, a geometric-mean drift of `(9/8)^(1/2) ≈ 1.061` per step, so
orbits should escape to infinity.  Numerics (2026-10-12, Python): no return to `8` within
`2·10^5` steps, by which point the iterate has 5224 digits, against `2·10^5 · log₁₀ 1.061 ≈ 5100`
predicted by the drift.  Control: the same loop started at `2` finds the cycle `2 → 3 → 2`.
Unlike `3x+1`, the drift points *up*, so there is no descent mechanism to prove the statement,
and a proof would need to rule out every return at once. -/
def AmusicalOrbitOfEightInfinite : Prop :=
  (Set.range fun k : ℕ => amusical^[k] 8).Infinite

/-- Because `U` is injective, the orbit of `8` is infinite exactly when `8` never returns. -/
theorem amusicalOrbitOfEightInfinite_iff :
    AmusicalOrbitOfEightInfinite ↔ ∀ k : ℕ, 0 < k → amusical^[k] 8 ≠ 8 := by
  constructor
  · intro hinf k hk hper
    apply hinf
    apply ((Finset.range k).image fun i => amusical^[i] 8).finite_toSet.subset
    rintro _ ⟨m, rfl⟩
    have hp : Function.IsPeriodicPt amusical k 8 := hper
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
    exact ⟨m % k, Nat.mod_lt _ hk, hp.iterate_mod_apply m⟩
  · intro hnot hfin
    have hninj : ¬ Function.Injective fun k : ℕ => amusical^[k] 8 :=
      fun hinj => Set.infinite_range_of_injective hinj hfin
    simp only [Function.Injective, not_forall] at hninj
    obtain ⟨i, j, hij, hne⟩ := hninj
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · apply hnot (j - i) (by omega)
      apply (amusical_injective.iterate i)
      rw [← Function.iterate_add_apply, Nat.add_sub_cancel' h.le]
      exact hij.symm
    · apply hnot (i - j) (by omega)
      apply (amusical_injective.iterate j)
      rw [← Function.iterate_add_apply, Nat.add_sub_cancel' h.le]
      exact hij

/-! ## Drift: the even-step share along the orbit of `8`

Even steps multiply by exactly `3/2`; odd steps by `3/4 ± 1/(4x)`.  For large values the orbit
grows iff the share of even steps exceeds `log₂(4/3) ≈ 0.415`.  That threshold is only a
large-value statement: `amusical_small_cycles` exhibits the cycle `2 → 3 → 2` with even share
`1/2` and the cycle `4 → 6 → 9 → 7 → 5 → 4` with share `2/5`.  The orbit of `8` avoids every
small cycle, so its values stay `≥ 4` and the odd-step ratios stay in `[11/16, 13/16]`; that
is the content of `periodic_eight_even_bound`. -/

/-- The cycles of `U` below `10`: the fixed points `0, 1`, the 2-cycle `{2, 3}` and the 5-cycle
`{4, 6, 9, 7, 5}`.  `8` lies on none of them. -/
theorem amusical_small_cycles :
    amusical 0 = 0 ∧ amusical 1 = 1 ∧ amusical 2 = 3 ∧ amusical 3 = 2 ∧
      amusical 4 = 6 ∧ amusical 6 = 9 ∧ amusical 9 = 7 ∧ amusical 7 = 5 ∧ amusical 5 = 4 := by
  decide

/-- The 12-cycle `44 → 66 → 99 → 74 → 111 → 83 → 62 → 93 → 70 → 105 → 79 → 59 → 44`, the
largest known cycle.  Atkin (SIAM Review 8 (1966) 234-236) and Conway 2013 list it with these
twelve members; Lagarias's annotated bibliography (2003, entry Klamkin 1963) gives its smallest
element as `144`, which contradicts this computation (`144` does not return within 500 steps). -/
theorem amusical_cycle_fortyFour :
    (List.range 13).map (fun k => amusical^[k] 44) =
      [44, 66, 99, 74, 111, 83, 62, 93, 70, 105, 79, 59, 44] := by
  decide

/-- `U` is odd, so its cycles on the negatives mirror those on the positives. -/
theorem amusical_neg (n : ℤ) : amusical (-n) = -amusical n := by
  unfold amusical; split_ifs <;> omega

/-- The twenty nonnegative integers known to lie on finite cycles: `{0}`, `{1}`, `{2, 3}`,
`{4, 6, 9, 7, 5}` and the 12-cycle through `44`.  Conway 2013 (Appendix 1) lists the nineteen
positive ones as the conjectured complete list. -/
def knownCycleMembers : Finset ℤ :=
  {0, 1, 2, 3, 4, 5, 6, 7, 9, 44, 59, 62, 66, 70, 74, 79, 83, 93, 99, 105, 111}

/-- **Open (Klamkin 1963, problem (b)).**  The known cycles are all the cycles on the
nonnegative integers.  By `amusical_neg` this settles the negatives too.  Implies
`AmusicalOrbitOfEightInfinite` (`8 ∉ knownCycleMembers`) and `AmusicalFinitelyManyCycles`. -/
def AmusicalNoOtherCycles : Prop :=
  ∀ n : ℤ, 0 ≤ n → n ∈ Function.periodicPts amusical → n ∈ knownCycleMembers

/-- **Open (Atkin 1966 heuristic; Lagarias 2021 conjecture C4, after Venturini 1997, for the
whole class of permutational generalized Collatz maps).**  `U` has only finitely many periodic
points.  Not Klamkin's problem (a), which counts all orbits: see
`AmusicalInfinitelyManyOrbits`. -/
def AmusicalFinitelyManyCycles : Prop :=
  (Function.periodicPts amusical).Finite

/-- The two-sided orbit `{U^j x : j ∈ ℤ}` of `x`. -/
def amusicalOrbit (x : ℤ) : Set ℤ :=
  Set.range fun j : ℤ => (amusicalPerm ^ j) x

/-- **Open (Klamkin 1963, problem (a), asked as "does `P` consist of finitely many cycles?",
counting the infinite cycle through `8`; Tavares 2013 calls it the Klamkin Problem).**  `U` has
infinitely many orbits on the nonnegative integers.

Believed true: Venturini (Adv. Appl. Math. 19 (1997), p. 303) says his estimate (16) "may" prove
every orbit has density `0`, which forces infinitely many orbits, but gives no proof.  Tavares
(Discrete Math. 313 (2013) 2139-2145, Theorem 1) reduces zero density of an orbit `O` to zero
density of `{n ∈ A : U^N n < n}` inside one residue thread `A = {U^(jN) x}` of `O`, and leaves
the problem open.  Unlike `AmusicalOrbitOfEightInfinite`, this is a statement about all orbits
at once, so a counting or density argument could settle it. -/
def AmusicalInfinitelyManyOrbits : Prop :=
  {O : Set ℤ | ∃ x : ℤ, 0 ≤ x ∧ O = amusicalOrbit x}.Infinite

theorem mem_amusicalOrbit_self (x : ℤ) : x ∈ amusicalOrbit x := ⟨0, by simp⟩

/-- `m` is the least element of its orbit. -/
def IsOrbitMin (m : ℤ) : Prop :=
  ∀ y ∈ amusicalOrbit m, m ≤ y

theorem amusicalOrbit_eq_of_mem {x y : ℤ} (h : y ∈ amusicalOrbit x) :
    amusicalOrbit y = amusicalOrbit x := by
  obtain ⟨j, rfl⟩ := h
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i + j, by dsimp only; rw [zpow_add, Equiv.Perm.mul_apply]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i - j, by dsimp only; rw [← Equiv.Perm.mul_apply, ← zpow_add, sub_add_cancel]⟩

/-- Distinct orbit minima have distinct orbits, so infinitely many minima give infinitely many
orbits. -/
theorem amusicalInfinitelyManyOrbits_of_minima
    (h : {m : ℤ | 0 ≤ m ∧ IsOrbitMin m}.Infinite) : AmusicalInfinitelyManyOrbits := by
  have hinj : Set.InjOn amusicalOrbit {m : ℤ | 0 ≤ m ∧ IsOrbitMin m} := by
    intro m hm m' hm' heq
    have h1 : m ∈ amusicalOrbit m' := heq ▸ mem_amusicalOrbit_self m
    have h2 : m' ∈ amusicalOrbit m := heq.symm ▸ mem_amusicalOrbit_self m'
    exact le_antisymm (hm.2 m' h2) (hm'.2 m h1)
  refine (h.image hinj).mono ?_
  rintro _ ⟨m, hm, rfl⟩
  exact ⟨m, hm.1, rfl⟩

open Classical in
/-- **Open (Venturini 1997 asserts it; Lagarias 2021 conjecture C5 in this form).**  Every
orbit of a nonnegative integer has natural density `0`. -/
def AmusicalOrbitsZeroDensity : Prop :=
  ∀ x : ℤ, 0 ≤ x → Filter.Tendsto
    (fun X : ℕ => (((Finset.range X).filter fun n : ℕ => (n : ℤ) ∈ amusicalOrbit x).card : ℝ) / X)
    Filter.atTop (nhds 0)

open Classical in
/-- Zero-density orbits force infinitely many orbits (the remark in Tavares 2013, §0): finitely
many orbits would cover `ℕ`, so one of them would have upper density at least `1/k`. -/
theorem amusicalInfinitelyManyOrbits_of_zeroDensity (h : AmusicalOrbitsZeroDensity) :
    AmusicalInfinitelyManyOrbits := by
  by_contra hfin
  rw [AmusicalInfinitelyManyOrbits, Set.not_infinite] at hfin
  set T := hfin.toFinset with hT
  have hmem : ∀ O ∈ T, ∃ x : ℤ, 0 ≤ x ∧ O = amusicalOrbit x := fun O hO => by
    simpa [hT] using hO
  choose! seed hseed0 hseedO using hmem
  set k := T.card
  have hev : ∀ᶠ X : ℕ in Filter.atTop, ∀ O ∈ T,
      (((Finset.range X).filter fun n : ℕ => (n : ℤ) ∈ O).card : ℝ) / X < 1 / (k + 1) := by
    rw [Filter.eventually_all_finset]
    intro O hO
    have hpos : (0 : ℝ) < 1 / (k + 1) := by positivity
    have := (h (seed O) (hseed0 O hO)).eventually (gt_mem_nhds hpos)
    simpa [← hseedO O hO] using this
  obtain ⟨X, hX⟩ := (hev.and (Filter.eventually_ge_atTop 1)).exists
  obtain ⟨hX, hX1⟩ := hX
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX1
  have hcover : Finset.range X ⊆
      T.biUnion fun O => (Finset.range X).filter fun n : ℕ => (n : ℤ) ∈ O := by
    intro n hn
    rw [Finset.mem_biUnion]
    refine ⟨amusicalOrbit n, ?_, Finset.mem_filter.2 ⟨hn, mem_amusicalOrbit_self _⟩⟩
    simp [hT]
    exact ⟨n, by positivity, rfl⟩
  have hcard : (X : ℝ) ≤ ∑ O ∈ T,
      (((Finset.range X).filter fun n : ℕ => (n : ℤ) ∈ O).card : ℝ) := by
    have := (Finset.card_le_card hcover).trans Finset.card_biUnion_le
    rw [Finset.card_range] at this
    exact_mod_cast this
  have hsum : ∑ O ∈ T, (((Finset.range X).filter fun n : ℕ => (n : ℤ) ∈ O).card : ℝ) ≤
      ∑ _O ∈ T, (X : ℝ) / (k + 1) := by
    apply Finset.sum_le_sum
    intro O hO
    have := hX O hO
    rw [div_lt_iff₀ hXpos] at this
    rw [div_eq_mul_one_div (X : ℝ)]
    linarith
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  have hk : (k : ℝ) * ((X : ℝ) / (k + 1)) < X := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

/-- The orbit of `x` returns to linear size arbitrarily late: some `C` has
`U^j x ≤ C (|j| + 1)` for arbitrarily large `|j|`.  An aperiodic orbit growing at the
heuristic rate `≈ 1.06^|j|` never does this. -/
def AmusicalLinearlyRecurrent (x : ℤ) : Prop :=
  ∃ C : ℝ, ∀ J : ℕ, ∃ j : ℤ, (J : ℤ) ≤ |j| ∧ (((amusicalPerm ^ j) x : ℤ) : ℝ) ≤ C * (|j| + 1)

open Classical in
/-- **What finitely many orbits would force.**  If `U` had only finitely many orbits, some
infinite orbit would be linearly recurrent.  So refuting linear recurrence for every aperiodic
orbit (a statement about individual orbits, the same kind as `AmusicalOrbitOfEightInfinite`)
would settle Klamkin's problem (a).  Proof: a zero-density failure gives an orbit meeting
`[0, X)` in `≥ εX` points for arbitrarily large `X`; those points sit at `≥ εX` distinct times
`j`, so one has `|j| ≥ εX/2`, while its value is `< X ≤ (2/ε)(|j| + 1)`. -/
theorem exists_linearlyRecurrent_of_finitelyManyOrbits (h : ¬ AmusicalInfinitelyManyOrbits) :
    ∃ x : ℤ, 0 ≤ x ∧ (amusicalOrbit x).Infinite ∧ AmusicalLinearlyRecurrent x := by
  have hz : ¬ AmusicalOrbitsZeroDensity := fun hz =>
    h (amusicalInfinitelyManyOrbits_of_zeroDensity hz)
  simp only [AmusicalOrbitsZeroDensity, not_forall] at hz
  obtain ⟨x, hx0, hnt⟩ := hz
  set f : ℕ → ℝ := fun X =>
    (((Finset.range X).filter fun n : ℕ => (n : ℤ) ∈ amusicalOrbit x).card : ℝ) / X with hf
  have hf0 : ∀ X, 0 ≤ f X := fun X => by positivity
  -- not tending to `0` means frequently `≥ ε`
  obtain ⟨ε, hε, hfreq⟩ : ∃ ε : ℝ, 0 < ε ∧ ∃ᶠ X in Filter.atTop, ε ≤ f X := by
    by_contra hne
    push Not at hne
    apply hnt
    rw [tendsto_order]
    refine ⟨fun a ha => Filter.Eventually.of_forall fun X => lt_of_lt_of_le ha (hf0 X), ?_⟩
    intro a ha
    simpa [Filter.not_frequently, not_le] using hne a ha
  refine ⟨x, hx0, ?_, ?_⟩
  · -- a finite orbit has bounded counts, so `f → 0`
    intro hfin
    set N := hfin.toFinset.card
    have hbound : ∀ X,
        ((Finset.range X).filter fun n : ℕ => (n : ℤ) ∈ amusicalOrbit x).card ≤ N := by
      intro X
      refine Finset.card_le_card_of_injOn (fun n : ℕ => (n : ℤ)) ?_ ?_
      · intro n hn
        simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hn
        simpa using hn.2
      · intro a _ b _ hab; simpa using hab
    have hlim : ∀ᶠ X : ℕ in Filter.atTop, f X < ε := by
      have ht : Filter.Tendsto (fun X : ℕ => (N : ℝ) / X) Filter.atTop (nhds 0) :=
        tendsto_const_div_atTop_nhds_zero_nat _
      filter_upwards [ht.eventually (gt_mem_nhds hε), Filter.eventually_ge_atTop 1] with X hX hX1
      refine lt_of_le_of_lt ?_ hX
      have hXpos : (0 : ℝ) < X := by exact_mod_cast hX1
      exact div_le_div_of_nonneg_right (by exact_mod_cast hbound X) hXpos.le
    exact (hfreq.and_eventually hlim).exists.elim fun X hX => absurd hX.1 (not_le.2 hX.2)
  · refine ⟨2 / ε, fun J => ?_⟩
    have hlarge := hfreq.and_eventually
      (Filter.eventually_ge_atTop (Nat.ceil (2 * ((J : ℝ) + 1) / ε) + 1))
    obtain ⟨X, hXε, hXbig⟩ := hlarge.exists
    have hX1 : (1 : ℕ) ≤ X := le_trans (Nat.le_add_left 1 _) hXbig
    have hXpos : (0 : ℝ) < X := by exact_mod_cast hX1
    set S := (Finset.range X).filter fun n : ℕ => (n : ℤ) ∈ amusicalOrbit x
    have hS : ε * X ≤ S.card := by
      have := hXε; simp only [hf] at this; rwa [le_div_iff₀ hXpos] at this
    -- a time for each point of `S`
    let g : ℕ → ℤ := fun n =>
      if hn : (n : ℤ) ∈ amusicalOrbit x then Classical.choose hn else 0
    have hg : ∀ n ∈ S, (amusicalPerm ^ g n) x = n := by
      intro n hn
      have hn' : (n : ℤ) ∈ amusicalOrbit x := (Finset.mem_filter.1 hn).2
      simp only [g, dif_pos hn']
      exact Classical.choose_spec hn'
    have hginj : Set.InjOn g S := by
      intro a ha b hb hab
      have := (hg a ha).symm.trans ((congrArg (fun j => (amusicalPerm ^ j) x) hab).trans (hg b hb))
      exact_mod_cast this
    set m : ℕ := Nat.floor (ε * X / 2)
    have hm2 : (2 * m : ℝ) ≤ ε * X := by
      have := Nat.floor_le (by positivity : (0 : ℝ) ≤ ε * X / 2); linarith
    have hT : (S.image g).card = S.card := Finset.card_image_of_injOn hginj
    have hIcc : (Finset.Icc (-(m : ℤ) + 1) ((m : ℤ) - 1)).card < (S.image g).card := by
      rw [Int.card_Icc, hT]
      have h1 : ((m : ℤ) - 1 + 1 - (-(m : ℤ) + 1)).toNat ≤ 2 * m - 1 := by omega
      have h2 : (2 * m : ℝ) ≤ S.card := le_trans hm2 hS
      have h3 : 2 * m ≤ S.card := by exact_mod_cast h2
      rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · have : ((m : ℤ) - 1 + 1 - (-(m : ℤ) + 1)).toNat = 0 := by omega
        rw [this]
        have hpos : (0 : ℝ) < S.card := lt_of_lt_of_le (by positivity) hS
        exact_mod_cast hpos
      · omega
    obtain ⟨j, hjT, hjI⟩ := Finset.exists_mem_notMem_of_card_lt_card hIcc
    obtain ⟨n, hnS, rfl⟩ := Finset.mem_image.1 hjT
    have hjabs : (m : ℤ) ≤ |g n| := by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hjI
      exact le_abs.2 (by omega)
    have hnX : (n : ℝ) < X := by exact_mod_cast Finset.mem_range.1 (Finset.mem_filter.1 hnS).1
    refine ⟨g n, ?_, ?_⟩
    · -- `m ≥ J` because `X ≥ 2(J+1)/ε`
      have hceil : 2 * ((J : ℝ) + 1) / ε ≤ X := by
        have := Nat.le_ceil (2 * ((J : ℝ) + 1) / ε)
        have : ((Nat.ceil (2 * ((J : ℝ) + 1) / ε) + 1 : ℕ) : ℝ) ≤ X := by exact_mod_cast hXbig
        push_cast at this; linarith
      have hJm : (J : ℝ) + 1 ≤ ε * X / 2 := by
        rw [div_le_iff₀ hε] at hceil; linarith
      have hmJ : J ≤ m := by
        apply Nat.le_floor
        linarith
      omega
    · rw [hg n hnS]
      have habs : ((m : ℤ) : ℝ) ≤ ((|g n| : ℤ) : ℝ) := by exact_mod_cast hjabs
      have hmfl : ε * X / 2 < (m : ℝ) + 1 := Nat.lt_floor_add_one _
      have key : (X : ℝ) ≤ 2 / ε * ((|g n| : ℤ) + 1) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hε]
        push_cast at habs ⊢
        linarith
      push_cast at key ⊢
      linarith

open Classical in
/-- **Conjecture (2026-10-13), a quantitative form of `AmusicalInfinitelyManyOrbits`.**  Orbit
minima have natural density `p_f · p_b ≈ 0.0498`.

Model: from a large `n`, the forward orbit is a log-scale random walk with steps `log (3/2)` and
`log (3/4)`, each with probability `1/2` (the residue of `n` mod `4` is uniform), and the
backward orbit one with steps `log (2/3)` with probability `1/3` and `log (4/3)` with
probability `2/3` (the residue mod `3` is uniform), the two independent (CRT on `2^a 3^b`).
`n` is an orbit minimum when both walks stay above `0` for ever.  Exact lattice computation
(2026-10-13, `scripts/amusical/survival.py`, 3000 steps, absorbing at height 40):
`p_f = 0.21014`, `p_b = 0.23689`, product `0.049780`.  Measured
(`scripts/amusical/minima2.py`): `49957` of the integers `1..10^6` have both orbit directions
pass `n · 2^120` without going below `n`, a density of `0.049957`, one standard error
(`≈ 0.0002`) from the prediction; the ratio is stable from `10^3` to `10^6`.  Minima lie in the
classes `±2 (mod 6)` (the local minima), and they avoid
`2, 16, 20, 34 (mod 36)`. -/
def AmusicalMinimaDensity : Prop :=
  ∃ c : ℝ, 0 < c ∧ Filter.Tendsto
    (fun X : ℕ => (((Finset.range X).filter fun m : ℕ => IsOrbitMin m).card : ℝ) / X)
    Filter.atTop (nhds c)

/-- The number of strict local minima on the cycle through a periodic `n` of period `p`: the
indices `i < p` with `U⁻¹ x > x < U x` for `x = U^[i] n`.  Simons calls a cycle with `m` of
them an *m-cycle* (arXiv:2205.10582, §1.3). -/
def cycleLocalMinCount (n : ℤ) (p : ℕ) : ℕ :=
  ((Finset.range p).filter fun i =>
    amusical^[i] n < amusical^[i + 1] n ∧ amusical^[i] n < amusicalInv (amusical^[i] n)).card

/-- The number of even values among `U^[0] 8, …, U^[k-1] 8`. -/
def evenCount (k : ℕ) : ℕ :=
  ((Finset.range k).filter fun i => amusical^[i] 8 % 2 = 0).card

/-- The number of odd values among `U^[0] 8, …, U^[k-1] 8`. -/
def oddCount (k : ℕ) : ℕ :=
  ((Finset.range k).filter fun i => ¬ amusical^[i] 8 % 2 = 0).card

theorem evenCount_add_oddCount (k : ℕ) : evenCount k + oddCount k = k := by
  unfold evenCount oddCount
  rw [Finset.card_filter_add_card_filter_not, Finset.card_range]

theorem oddCount_eq (k : ℕ) : oddCount k = k - evenCount k := by
  have := evenCount_add_oddCount k; omega

theorem evenCount_succ (k : ℕ) :
    evenCount (k + 1) = evenCount k + if amusical^[k] 8 % 2 = 0 then 1 else 0 := by
  unfold evenCount
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

theorem oddCount_succ (k : ℕ) :
    oddCount (k + 1) = oddCount k + if amusical^[k] 8 % 2 = 0 then 0 else 1 := by
  have h1 := evenCount_add_oddCount k
  have h2 := evenCount_add_oddCount (k + 1)
  have h3 := evenCount_succ k
  split_ifs at h3 ⊢ <;> omega

/-- `[0, 4)` is invariant under `U⁻¹`: a value landing there came from there. -/
theorem lt_four_of_amusical_lt_four {x : ℤ} (h0 : 0 ≤ amusical x) (h4 : amusical x < 4) :
    0 ≤ x ∧ x < 4 := by
  unfold amusical at h0 h4; split_ifs at h0 h4 <;> omega

theorem nonneg_of_iterate_lt_four (k : ℕ) :
    ∀ x : ℤ, 0 ≤ amusical^[k] x → amusical^[k] x < 4 → 0 ≤ x ∧ x < 4 := by
  induction k with
  | zero => intro x h0 h4; exact ⟨h0, h4⟩
  | succ k ih =>
    intro x h0 h4
    rw [Function.iterate_succ_apply] at h0 h4
    obtain ⟨h0', h4'⟩ := ih _ h0 h4
    exact lt_four_of_amusical_lt_four h0' h4'

theorem amusical_nonneg {x : ℤ} (h : 0 ≤ x) : 0 ≤ amusical x := by
  unfold amusical; split_ifs <;> omega

/-- The orbit of `8` stays `≥ 4`: it is nonnegative, and avoids the invariant set `[0, 4)`. -/
theorem four_le_orbit_eight (k : ℕ) : 4 ≤ amusical^[k] 8 := by
  have hnn : ∀ j : ℕ, 0 ≤ amusical^[j] 8 := by
    intro j
    induction j with
    | zero => norm_num
    | succ j ih => rw [Function.iterate_succ_apply']; exact amusical_nonneg ih
  by_contra h
  have := nonneg_of_iterate_lt_four k 8 (hnn k) (by omega)
  omega

theorem two_mul_amusical_of_even {x : ℤ} (h : x % 2 = 0) : 2 * amusical x = 3 * x := by
  unfold amusical; split_ifs; omega

theorem eleven_mul_le_of_odd {x : ℤ} (h4 : 4 ≤ x) (h : ¬ x % 2 = 0) :
    11 * x ≤ 16 * amusical x := by
  unfold amusical; split_ifs <;> omega

/-- The running product of step ratios: `(3/2)^e (11/16)^o · 8 ≤ U^[k] 8`, cleared of
denominators. -/
theorem evenCount_bound (k : ℕ) :
    (3 : ℤ) ^ evenCount k * 11 ^ oddCount k * 8 ≤
      2 ^ evenCount k * 16 ^ oddCount k * amusical^[k] 8 := by
  induction k with
  | zero => simp [evenCount, oddCount]
  | succ k ih =>
    rw [evenCount_succ, oddCount_succ, Function.iterate_succ_apply']
    have hB : (0 : ℤ) ≤ 2 ^ evenCount k * 16 ^ oddCount k := by positivity
    split_ifs with h
    · have hs := two_mul_amusical_of_even h
      calc (3 : ℤ) ^ (evenCount k + 1) * 11 ^ (oddCount k + 0) * 8
          = 3 * (3 ^ evenCount k * 11 ^ oddCount k * 8) := by ring
        _ ≤ 3 * (2 ^ evenCount k * 16 ^ oddCount k * amusical^[k] 8) := by linarith
        _ = 2 ^ evenCount k * 16 ^ oddCount k * (3 * amusical^[k] 8) := by ring
        _ = 2 ^ evenCount k * 16 ^ oddCount k * (2 * amusical (amusical^[k] 8)) := by rw [hs]
        _ = 2 ^ (evenCount k + 1) * 16 ^ (oddCount k + 0) * amusical (amusical^[k] 8) := by
          ring
    · have hs := eleven_mul_le_of_odd (four_le_orbit_eight k) h
      calc (3 : ℤ) ^ (evenCount k + 0) * 11 ^ (oddCount k + 1) * 8
          = 11 * (3 ^ evenCount k * 11 ^ oddCount k * 8) := by ring
        _ ≤ 11 * (2 ^ evenCount k * 16 ^ oddCount k * amusical^[k] 8) := by linarith
        _ = 2 ^ evenCount k * 16 ^ oddCount k * (11 * amusical^[k] 8) := by ring
        _ ≤ 2 ^ evenCount k * 16 ^ oddCount k * (16 * amusical (amusical^[k] 8)) :=
          mul_le_mul_of_nonneg_left hs hB
        _ = 2 ^ (evenCount k + 0) * 16 ^ (oddCount k + 1) * amusical (amusical^[k] 8) := by
          ring

/-- If `8` were periodic with period `p` and `e`
even steps per period, then `(3/2)^e (11/16)^(p-e) ≤ 1`.

Proof: the orbit of `8` is positive and avoids the invariant set `{0, 1, 2, 3}` (a
bijection's cycles are disjoint, and `8` is not in them), so every value is `≥ 4`.  An odd step
from `x` multiplies by `3/4 ± 1/(4x) ≥ 11/16`.  Around a cycle the product of the step ratios
is `1`, so `1 ≥ (3/2)^e (11/16)^(p-e)`. -/
theorem periodic_eight_even_bound {p : ℕ} (_hp : 0 < p) (hper : amusical^[p] 8 = 8) :
    3 ^ evenCount p * 11 ^ (p - evenCount p) ≤ 2 ^ evenCount p * 16 ^ (p - evenCount p) := by
  have h := evenCount_bound p
  rw [hper, oddCount_eq] at h
  have h' : ((3 ^ evenCount p * 11 ^ (p - evenCount p) : ℕ) : ℤ) ≤
      ((2 ^ evenCount p * 16 ^ (p - evenCount p) : ℕ) : ℤ) := by
    push_cast; omega
  exact_mod_cast h'

/-- **Open, normality-type.**  The even values have density `1/2` along the orbit of `8`.

This is the heuristic behind `AmusicalOrbitOfEightInfinite`: if the orbit's residues mod `4`
look like independent fair digits, the evens have density `1/2`, well above the large-value
threshold `log₂(4/3) ≈ 0.415`.  It is a frequency statement about one specific orbit, the same
kind of statement as the normality of a specific real number. -/
def EightEvenDensityHalf : Prop :=
  Filter.Tendsto (fun k : ℕ => (evenCount k : ℝ) / k) Filter.atTop (nhds (1 / 2))

/-- Even density `1/2` forces the orbit of `8` to be
infinite.

Proof: if `8` had period `p` with `e` even steps per period, then
`evenCount (m * p) = m * e`, so the density would be `e / p`, forcing `2e = p`.  Then
`periodic_eight_even_bound` gives `33^e ≤ 32^e`, so `e = 0` and `p = 0`, a contradiction. -/
theorem amusicalOrbitOfEightInfinite_of_evenDensityHalf (h : EightEvenDensityHalf) :
    AmusicalOrbitOfEightInfinite := by
  rw [amusicalOrbitOfEightInfinite_iff]
  intro p hp hper
  have hpt : Function.IsPeriodicPt amusical p 8 := hper
  set e := evenCount p with he
  -- along multiples of the period the count is exactly linear
  have hlin : ∀ m : ℕ, evenCount (m * p) = m * e := by
    intro m
    induction m with
    | zero => simp [evenCount]
    | succ m ih =>
      have hsplit : evenCount (m * p + p) = evenCount (m * p) + evenCount p := by
        unfold evenCount
        simp only [Finset.card_filter]
        rw [Finset.sum_range_add]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [add_comm, Function.iterate_add_apply, mul_comm, (hpt.mul_const m).eq]
      rw [Nat.succ_mul, hsplit, ih, ← he, Nat.succ_mul]
  have hmono : Filter.Tendsto (fun m : ℕ => m * p) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.2 fun b =>
      ⟨b, fun m hm => le_trans hm (Nat.le_mul_of_pos_right m hp)⟩
  have hsub := h.comp hmono
  have hconst : Filter.Tendsto (fun m : ℕ => (evenCount (m * p) : ℝ) / ((m * p : ℕ) : ℝ))
      Filter.atTop (nhds ((e : ℝ) / p)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with m hm
    rw [hlin]
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    push_cast
    field_simp
  have hval : (e : ℝ) / p = 1 / 2 := tendsto_nhds_unique hconst hsub
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have h2e : p = 2 * e := by
    field_simp at hval
    exact_mod_cast (by linarith : (p : ℝ) = 2 * e)
  have hbound := periodic_eight_even_bound hp hper
  rw [← he, show p - e = e by omega, ← mul_pow, ← mul_pow] at hbound
  have he0 : e ≠ 0 := by omega
  have := Nat.pow_lt_pow_left (show 2 * 16 < 3 * 11 by norm_num) he0
  omega

/-! ## A two-sided window for the even share of a cycle through `8`

The orbit of `8` avoids every small cycle, so its odd values are `≥ 11`, where an odd step
multiplies by a ratio in `[8/11, 10/13]`.  Around a cycle the ratios multiply to `1`, which pins
the even share `e/p` to `[log(13/10)/log(39/20), log(11/8)/log(33/16)] ≈ [0.393, 0.440]`, a
window around the large-value threshold `log₂(4/3) ≈ 0.415`.

Reading the cycle backwards adds nothing: `U⁻¹` reads residues mod `3`, and
`even_iff_amusical_mod_three` says `x` is even exactly when `U x` is a multiple of `3`, so along
any cycle the backward share of multiples of `3` equals the forward even share. -/

/-- `x` is even exactly when `U x` is a multiple of `3`. -/
theorem even_iff_amusical_mod_three (x : ℤ) : x % 2 = 0 ↔ amusical x % 3 = 0 := by
  unfold amusical; split_ifs <;> omega

/-- The small cycles `{0}, {1}, {2,3}, {4,6,9,7,5}` together are closed under `U⁻¹`. -/
theorem small_of_amusical_small {y : ℤ} (h0 : 0 ≤ amusical y) (h10 : amusical y < 10)
    (h8 : amusical y ≠ 8) : 0 ≤ y ∧ y < 10 ∧ y ≠ 8 := by
  unfold amusical at h0 h10 h8; split_ifs at h0 h10 h8 <;> omega

theorem small_of_iterate_small (k : ℕ) : ∀ x : ℤ,
    0 ≤ amusical^[k] x → amusical^[k] x < 10 → amusical^[k] x ≠ 8 → 0 ≤ x ∧ x < 10 ∧ x ≠ 8 := by
  induction k with
  | zero => intro x h0 h10 h8; exact ⟨h0, h10, h8⟩
  | succ k ih =>
    intro x h0 h10 h8
    rw [Function.iterate_succ_apply] at h0 h10 h8
    obtain ⟨h0', h10', h8'⟩ := ih _ h0 h10 h8
    exact small_of_amusical_small h0' h10' h8'

/-- Every odd value on the orbit of `8` is at least `11`. -/
theorem eleven_le_orbit_eight_of_odd (k : ℕ) (h : ¬ amusical^[k] 8 % 2 = 0) :
    11 ≤ amusical^[k] 8 := by
  have h4 := four_le_orbit_eight k
  by_contra hlt
  have hne : amusical^[k] 8 ≠ 8 := by omega
  have := small_of_iterate_small k 8 (by omega) (by omega) hne
  omega

theorem odd_step_lower {x : ℤ} (h11 : 11 ≤ x) (h : ¬ x % 2 = 0) : 8 * x ≤ 11 * amusical x := by
  unfold amusical; split_ifs <;> omega

theorem odd_step_upper {x : ℤ} (h11 : 11 ≤ x) (h : ¬ x % 2 = 0) : 13 * amusical x ≤ 10 * x := by
  unfold amusical; split_ifs <;> omega

/-- Running product, lower side: if every odd step multiplies by at least `a/b`, then
`(3/2)^e (a/b)^o · 8 ≤ U^[k] 8`. -/
theorem orbit_product_lower {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hodd : ∀ k : ℕ, ¬ amusical^[k] 8 % 2 = 0 →
      a * amusical^[k] 8 ≤ b * amusical (amusical^[k] 8)) (k : ℕ) :
    3 ^ evenCount k * a ^ oddCount k * 8 ≤ 2 ^ evenCount k * b ^ oddCount k * amusical^[k] 8 := by
  induction k with
  | zero => simp [evenCount, oddCount]
  | succ k ih =>
    rw [evenCount_succ, oddCount_succ, Function.iterate_succ_apply']
    split_ifs with h
    · have hs := two_mul_amusical_of_even h
      calc (3 : ℤ) ^ (evenCount k + 1) * a ^ (oddCount k + 0) * 8
          = 3 * (3 ^ evenCount k * a ^ oddCount k * 8) := by ring
        _ ≤ 3 * (2 ^ evenCount k * b ^ oddCount k * amusical^[k] 8) := by linarith
        _ = 2 ^ evenCount k * b ^ oddCount k * (3 * amusical^[k] 8) := by ring
        _ = 2 ^ evenCount k * b ^ oddCount k * (2 * amusical (amusical^[k] 8)) := by rw [hs]
        _ = 2 ^ (evenCount k + 1) * b ^ (oddCount k + 0) * amusical (amusical^[k] 8) := by
          ring
    · have hs := hodd k h
      calc (3 : ℤ) ^ (evenCount k + 0) * a ^ (oddCount k + 1) * 8
          = a * (3 ^ evenCount k * a ^ oddCount k * 8) := by ring
        _ ≤ a * (2 ^ evenCount k * b ^ oddCount k * amusical^[k] 8) :=
          mul_le_mul_of_nonneg_left ih ha
        _ = 2 ^ evenCount k * b ^ oddCount k * (a * amusical^[k] 8) := by ring
        _ ≤ 2 ^ evenCount k * b ^ oddCount k * (b * amusical (amusical^[k] 8)) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
        _ = 2 ^ (evenCount k + 0) * b ^ (oddCount k + 1) * amusical (amusical^[k] 8) := by
          ring

/-- Running product, upper side: if every odd step multiplies by at most `d/c`, then
`U^[k] 8 ≤ (3/2)^e (d/c)^o · 8`. -/
theorem orbit_product_upper {c d : ℤ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hodd : ∀ k : ℕ, ¬ amusical^[k] 8 % 2 = 0 →
      c * amusical (amusical^[k] 8) ≤ d * amusical^[k] 8) (k : ℕ) :
    2 ^ evenCount k * c ^ oddCount k * amusical^[k] 8 ≤ 3 ^ evenCount k * d ^ oddCount k * 8 := by
  induction k with
  | zero => simp [evenCount, oddCount]
  | succ k ih =>
    rw [evenCount_succ, oddCount_succ, Function.iterate_succ_apply']
    have hB : (0 : ℤ) ≤ 2 ^ evenCount k * c ^ oddCount k := by positivity
    split_ifs with h
    · have hs := two_mul_amusical_of_even h
      calc (2 : ℤ) ^ (evenCount k + 1) * c ^ (oddCount k + 0) * amusical (amusical^[k] 8)
          = 2 ^ evenCount k * c ^ oddCount k * (2 * amusical (amusical^[k] 8)) := by ring
        _ = 3 * (2 ^ evenCount k * c ^ oddCount k * amusical^[k] 8) := by rw [hs]; ring
        _ ≤ 3 * (3 ^ evenCount k * d ^ oddCount k * 8) := by linarith
        _ = 3 ^ (evenCount k + 1) * d ^ (oddCount k + 0) * 8 := by ring
    · have hs := hodd k h
      calc (2 : ℤ) ^ (evenCount k + 0) * c ^ (oddCount k + 1) * amusical (amusical^[k] 8)
          = 2 ^ evenCount k * c ^ oddCount k * (c * amusical (amusical^[k] 8)) := by ring
        _ ≤ 2 ^ evenCount k * c ^ oddCount k * (d * amusical^[k] 8) :=
          mul_le_mul_of_nonneg_left hs hB
        _ = d * (2 ^ evenCount k * c ^ oddCount k * amusical^[k] 8) := by ring
        _ ≤ d * (3 ^ evenCount k * d ^ oddCount k * 8) := mul_le_mul_of_nonneg_left ih hd
        _ = 3 ^ (evenCount k + 0) * d ^ (oddCount k + 1) * 8 := by ring

/-- **The even-share window.**  If `8` has period `p` with `e` even steps, then
`(3/2)^e (8/11)^(p-e) ≤ 1 ≤ (3/2)^e (10/13)^(p-e)`, so
`0.3928 < log(13/10)/log(39/20) ≤ e/p ≤ log(11/8)/log(33/16) < 0.4400`. -/
theorem periodic_eight_even_window {p : ℕ} (hper : amusical^[p] 8 = 8) :
    3 ^ evenCount p * 8 ^ (p - evenCount p) ≤ 2 ^ evenCount p * 11 ^ (p - evenCount p) ∧
      2 ^ evenCount p * 13 ^ (p - evenCount p) ≤ 3 ^ evenCount p * 10 ^ (p - evenCount p) := by
  have hlo := orbit_product_lower (a := 8) (b := 11) (by norm_num) (by norm_num)
    (fun k h => odd_step_lower (eleven_le_orbit_eight_of_odd k h) h) p
  have hhi := orbit_product_upper (c := 13) (d := 10) (by norm_num) (by norm_num)
    (fun k h => odd_step_upper (eleven_le_orbit_eight_of_odd k h) h) p
  rw [hper, oddCount_eq] at hlo hhi
  constructor
  · have h' : ((3 ^ evenCount p * 8 ^ (p - evenCount p) : ℕ) : ℤ) ≤
        ((2 ^ evenCount p * 11 ^ (p - evenCount p) : ℕ) : ℤ) := by
      push_cast; omega
    exact_mod_cast h'
  · have h' : ((2 ^ evenCount p * 13 ^ (p - evenCount p) : ℕ) : ℤ) ≤
        ((3 ^ evenCount p * 10 ^ (p - evenCount p) : ℕ) : ℤ) := by
      push_cast; omega
    exact_mod_cast h'

end CollatzMoonshot.Amusical
