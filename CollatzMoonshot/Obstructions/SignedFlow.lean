import CollatzMoonshot.FrontB.Dictionary

/-! Finite signed vertex balance detects the trivial Collatz basin.

The coefficients may be negative.  This module extracts convergence from the
boundary equation; it does not construct that equation for arbitrary starts.
-/

namespace CollatzMoonshot.Obstructions.SignedFlow

open CollatzMoonshot.FrontB

noncomputable section

/-- The accelerated orbit eventually visits `1`. -/
def reachesOne (n : ℕ) : Prop := ∃ k : ℕ, tstep^[k] n = 1

/-- Divergence of a finite signed integer edge chain on the deterministic
accelerated Collatz graph.  A coefficient at `u` weights the edge
`u → tstep u`. -/
def boundary (c : ℕ →₀ ℤ) : ℕ →₀ ℤ :=
  c.sum (fun u z => z •
    (Finsupp.single u (1 : ℤ) - Finsupp.single (tstep u) (1 : ℤ)))


/-- Pairing a finite signed vertex chain with an integer weight function is the
`ℤ`-linear combination map. -/
private lemma pair_eq (w : ℕ → ℤ) (f : ℕ →₀ ℤ) :
    f.sum (fun u z => z * w u) = Finsupp.linearCombination ℤ w f := by
  rw [Finsupp.linearCombination_apply]
  simp

private lemma boundary_add (a b : ℕ →₀ ℤ) :
    boundary (a + b) = boundary a + boundary b :=
  Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by rw [add_smul])

private lemma boundary_zero : boundary (0 : ℕ →₀ ℤ) = 0 :=
  Finsupp.sum_zero_index

private lemma boundary_single (u : ℕ) :
    boundary (Finsupp.single u (1 : ℤ)) =
      Finsupp.single u (1 : ℤ) - Finsupp.single (tstep u) (1 : ℤ) := by
  rw [boundary, Finsupp.sum_single_index (by simp), one_smul]

/-- Finite signed chain following the orbit of `n` for `k` accelerated steps. -/
private def pathChain : ℕ → ℕ → (ℕ →₀ ℤ)
  | _, 0 => 0
  | n, (k + 1) => Finsupp.single n (1 : ℤ) + pathChain (tstep n) k

private lemma boundary_pathChain (k : ℕ) : ∀ n : ℕ,
    boundary (pathChain n k) =
      Finsupp.single n (1 : ℤ) - Finsupp.single (tstep^[k] n) (1 : ℤ) := by
  induction k with
  | zero => intro n; simp [pathChain, boundary_zero]
  | succ k ih =>
      intro n
      rw [pathChain, boundary_add, boundary_single, ih (tstep n),
        Function.iterate_succ_apply]
      abel

/-- The convergent basin is saturated under one forward or backward edge. -/
theorem reachesOne_step_iff (n : ℕ) :
    reachesOne n ↔ reachesOne (tstep n) := by
  constructor
  · rintro ⟨k, hk⟩
    cases k with
    | zero =>
        simp only [Function.iterate_zero, id_eq] at hk
        subst hk
        exact ⟨1, by simp⟩
    | succ k =>
        exact ⟨k, by rw [← Function.iterate_succ_apply]; exact hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩

open scoped Classical in
/-- Indicator of the convergent basin, as an integer weight. -/
private def basinIndicator (u : ℕ) : ℤ := if reachesOne u then 1 else 0

private lemma basinIndicator_invariant (u : ℕ) :
    basinIndicator (tstep u) = basinIndicator u := by
  classical
  simp only [basinIndicator]
  by_cases h : reachesOne u
  · rw [if_pos ((reachesOne_step_iff u).mp h), if_pos h]
  · rw [if_neg (fun hc => h ((reachesOne_step_iff u).mpr hc)), if_neg h]

private lemma basinIndicator_one : basinIndicator 1 = 1 := by
  classical
  rw [basinIndicator, if_pos ⟨0, rfl⟩]

private lemma basinIndicator_of_not {u : ℕ} (h : ¬ reachesOne u) :
    basinIndicator u = 0 := by
  classical
  rw [basinIndicator, if_neg h]

/-- Every function constant along `tstep` edges annihilates every finite
signed boundary.  This is the component-charge invariant; no positivity is
assumed for `c`. -/
theorem boundary_pairing_invariant (w : ℕ → ℤ)
    (hw : ∀ u : ℕ, w (tstep u) = w u) (c : ℕ →₀ ℤ) :
    (boundary c).sum (fun u z => z * w u) = 0 := by
  rw [pair_eq, boundary, Finsupp.sum, map_sum]
  refine Finset.sum_eq_zero ?_
  intro u _
  rw [map_smul, map_sub, Finsupp.linearCombination_single,
    Finsupp.linearCombination_single, hw]
  simp

/-- A finite signed integer flow of unit boundary from `n` to `1` exists
exactly when the accelerated orbit of `n` reaches `1`. -/
theorem exists_signed_flow_iff_reachesOne (n : ℕ) :
    (∃ c : ℕ →₀ ℤ,
      boundary c = Finsupp.single n (1 : ℤ) - Finsupp.single 1 (1 : ℤ)) ↔
    reachesOne n := by
  classical
  constructor
  · rintro ⟨c, hc⟩
    by_contra hn
    have key := boundary_pairing_invariant (basinIndicator) basinIndicator_invariant c
    rw [hc, pair_eq, map_sub, Finsupp.linearCombination_single,
      Finsupp.linearCombination_single] at key
    rw [basinIndicator_one, basinIndicator_of_not hn] at key
    simp at key
  · rintro ⟨k, hk⟩
    refine ⟨pathChain n k, ?_⟩
    rw [boundary_pathChain, hk]

/-- Even a nonzero integer multiple of the desired boundary forces
convergence.  In particular rational signed flows cannot evade the basin
charge after clearing denominators. -/
theorem scaled_signed_flow_reachesOne (n : ℕ) (k : ℤ) (hk : k ≠ 0)
    (c : ℕ →₀ ℤ)
    (hc : boundary c =
      k • (Finsupp.single n (1 : ℤ) - Finsupp.single 1 (1 : ℤ))) :
    reachesOne n := by
  classical
  by_contra hn
  have key := boundary_pairing_invariant (basinIndicator) basinIndicator_invariant c
  rw [hc, pair_eq, map_smul, map_sub, Finsupp.linearCombination_single,
    Finsupp.linearCombination_single] at key
  rw [basinIndicator_one, basinIndicator_of_not hn] at key
  simp at key
  exact hk key

end

end CollatzMoonshot.Obstructions.SignedFlow
