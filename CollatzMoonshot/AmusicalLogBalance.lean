/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Amusical

/-!
# Log-weighted balance of unions of orbits

Weight a positive integer `n` by `1/n`.  `U` multiplies by `3/2` on evens and by about `3/4` on
odds, so it sends the evens of a `U`-invariant set onto its multiples of `3` with weight factor
`2/3`, and the odds onto the rest with factor about `4/3`.  Comparing the two sides shows that
every union of orbits carries exactly half its log weight on evens and a third on multiples of
`3`, up to a bounded error (`logWeight_even_balance`, `logWeight_three_balance`).  And if every
orbit has log density `0`, there are infinitely many orbits
(`amusicalInfinitelyManyOrbits_of_logDensityZero`), a stronger form of
`amusicalInfinitelyManyOrbits_of_zeroDensity`.

The hoped-for upgrade, "an orbit of positive log density is equidistributed in every residue class
mod `2^a 3^b`", has no ergodic engine: Haar measure on `ℤ₂ × ℤ₃` is conformal for `Û` (Jacobian
`1/slope`), not invariant, and `Û` is totally dissipative for it, its wandering set being the formal
orbit minima, of measure exactly the constant `c ≈ 0.04978` of `AmusicalConstant.lean`.  Paper
proofs: agent report `equidist.md` (2026-10-13), summarized in
`RESEARCH-2026-10-13-amusical-single-chain.md` §10.  Treadmill target
(`KICKOFF-2026-10-13-amusical-logbal.md`): close every `sorry` here.
-/

namespace CollatzMoonshot.Amusical

open Classical in
/-- The log weight `Σ 1/n` of the positive integers `n ≤ N` in `S`. -/
noncomputable def logWeight (S : Set ℤ) (N : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc (1 : ℤ) N).filter (· ∈ S), (1 : ℝ) / n

/-- **Target.**  A union of orbits carries half its log weight on evens, up to `3`.  Paper proof:
`U` maps the evens `n ≤ N` of `S` bijectively onto the multiples of `3` up to `3N/2`, each weight
times `2/3`, and the odds onto the non-multiples up to about `3N/4`, each weight times
`4/3 + O(1/n²)` (total error below `1/2`).  Moving the cutoffs back to `N` costs at most
`log(3/2)` and `log(4/3)` plus `O(1/N)`.  With `e`, `o` the even and odd weights this gives
`e + o = (2/3) e + (4/3) o + E` with `|E| < 1`, so `|e - o| < 3` and `|e - (e + o)/2| < 3/2`. -/
theorem logWeight_even_balance {S : Set ℤ} (hS : ∀ x, amusical x ∈ S ↔ x ∈ S) (N : ℕ) :
    |logWeight (S ∩ {n | 2 ∣ n}) N - logWeight S N / 2| ≤ 3 := by
  sorry

/-- **Target.**  A union of orbits carries a third of its log weight on multiples of `3`, up to
`3`: the multiples of `3` up to `N` weigh `(2/3) e` up to `log(3/2) + O(1/N)`, and
`(2/3) e - (e + o)/3 = (e - o)/3`, bounded by the even balance. -/
theorem logWeight_three_balance {S : Set ℤ} (hS : ∀ x, amusical x ∈ S ↔ x ∈ S) (N : ℕ) :
    |logWeight (S ∩ {n | 3 ∣ n}) N - logWeight S N / 3| ≤ 3 := by
  sorry

/-- **Target.**  If every orbit of a nonnegative integer has log density `0`, Klamkin's problem
(a) holds.  Paper proof: finitely many orbits would cover `ℕ`, so their log weights up to `N`
sum to at least `Σ_{n ≤ N} 1/n ≥ log N`, and one of them has `logWeight / log N ≥ 1/k`
infinitely often. -/
theorem amusicalInfinitelyManyOrbits_of_logDensityZero
    (h : ∀ x : ℤ, 0 ≤ x → Filter.Tendsto (fun N : ℕ => logWeight (amusicalOrbit x) N / Real.log N)
      Filter.atTop (nhds 0)) :
    AmusicalInfinitelyManyOrbits := by
  classical
  by_contra hfin
  rw [AmusicalInfinitelyManyOrbits, Set.not_infinite] at hfin
  set T := hfin.toFinset with hT
  have hmem : ∀ O ∈ T, ∃ x : ℤ, 0 ≤ x ∧ O = amusicalOrbit x := fun O hO => by
    simpa [hT] using hO
  choose! seed hseed0 hseedO using hmem
  set k := T.card
  have hev : Filter.Eventually (λ N : ℕ => ∀ O ∈ T,
      logWeight O N / Real.log N < 1 / (k + 1)) Filter.atTop := by
    rw [Filter.eventually_all_finset]
    intro O hO
    have hpos : (0 : ℝ) < 1 / (k + 1) := by positivity
    have := (h (seed O) (hseed0 O hO)).eventually (gt_mem_nhds hpos)
    simpa [← hseedO O hO] using this
  obtain ⟨N, hN, hN2⟩ := (hev.and (Filter.eventually_ge_atTop 2)).exists
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN2)
  have hpoint (n : ℤ) (hn : n ∈ Finset.Icc (1 : ℤ) N) :
      (1 : ℝ) / n ≤ ∑ O ∈ T, if n ∈ O then (1 : ℝ) / n else 0 := by
    have hn0 : 0 ≤ n := le_trans (by norm_num) (Finset.mem_Icc.1 hn).1
    have hO : amusicalOrbit n ∈ T := by
      simp [hT]
      exact ⟨n, hn0, rfl⟩
    calc
      (1 : ℝ) / n = if n ∈ amusicalOrbit n then (1 : ℝ) / n else 0 := by
        simp [mem_amusicalOrbit_self]
      _ ≤ ∑ O ∈ T, if n ∈ O then (1 : ℝ) / n else 0 := by
        apply Finset.single_le_sum (f := fun O => if n ∈ O then (1 : ℝ) / n else 0)
        · intro O hOT
          split_ifs <;> positivity
        · exact hO
  have htotal : (harmonic N : ℝ) ≤ ∑ O ∈ T, logWeight O N := by
    calc
      (harmonic N : ℝ) = ∑ n ∈ Finset.Icc (1 : ℤ) N, (1 : ℝ) / n := by
        rw [harmonic, Rat.cast_sum]
        apply Finset.sum_bij (fun i _ => ((i + 1 : ℕ) : ℤ))
        · intro i hi
          simp only [Finset.mem_range] at hi
          simp only [Finset.mem_Icc]
          constructor
          · omega
          · exact_mod_cast Nat.succ_le_iff.2 hi
        · intro i hi j hj hij
          have : i + 1 = j + 1 := by exact_mod_cast hij
          omega
        · intro n hn
          have hn' := Finset.mem_Icc.1 hn
          refine ⟨Int.toNat n - 1, by simp only [Finset.mem_range]; omega, ?_⟩
          omega
        · intro i hi
          norm_num
      _ ≤ ∑ n ∈ Finset.Icc (1 : ℤ) N,
          ∑ O ∈ T, if n ∈ O then (1 : ℝ) / n else 0 := by
        exact Finset.sum_le_sum fun n hn => hpoint n hn
      _ = ∑ O ∈ T, logWeight O N := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro O hO
        simp [logWeight, Finset.sum_filter]
  have hsum : ∑ O ∈ T, logWeight O N ≤ ∑ _O ∈ T, Real.log N / (k + 1) := by
    apply Finset.sum_le_sum
    intro O hO
    have hsmall := hN O hO
    rw [div_lt_iff₀ hlog] at hsmall
    exact (by simpa [div_eq_mul_inv, mul_comm] using hsmall :
      logWeight O N < Real.log N / (k + 1)).le
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  change ∑ O ∈ T, logWeight O N ≤ (k : ℝ) * (Real.log N / (k + 1)) at hsum
  have hkp : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hk : (k : ℝ) * (Real.log N / (k + 1)) < Real.log N := by
    rw [mul_div_assoc', div_lt_iff₀ hkp]
    nlinarith
  have := log_add_one_le_harmonic N
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hN2)
  have hNspos : (0 : ℝ) < N + 1 := by positivity
  have hloglt : Real.log N < Real.log (N + 1) :=
    Real.strictMonoOn_log hNpos hNspos (by exact_mod_cast Nat.lt_succ_self N)
  norm_num [Nat.cast_add, Nat.cast_one] at this
  linarith

end CollatzMoonshot.Amusical
