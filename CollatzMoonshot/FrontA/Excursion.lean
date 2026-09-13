import CollatzMoonshot.FrontA.Paradoxical

/-!
# Exact trunk decomposition, with the indispensable descent remainder

Split a shortcut orbit after `k` steps; the suffix has length `l`.  The split may be
at an orbit minimum, but the algebra needs no minimum hypothesis.  In particular,
"descent" does not mean that the prefix is monotone.

The endpoint condition is a criterion on the climb AND the preimage remainder.
`trunk_depth_data_insufficient` refutes dropping that remainder even when the split
is at the genuine minimum, the starts are odd, and both total words are subcritical.
Strict endpoint growth is the repository's `AcyclicParadoxical`; the equality
criterion below also retains cyclic endpoints.
-/

namespace CollatzMoonshot.FrontA

open CollatzMoonshot.FrontB

/-- Eliminate the start from the two affine segment identities.  All differences
are in `ℤ`, so this identity also works outside the subcritical regime. -/
theorem trunk_slack_identity (n k l : ℕ) :
    let t := tstep^[k] n
    let j := ones (traceWord n k)
    let b := ones (traceWord t l)
    (3 : ℤ)^j * 2^l * ((tstep^[k + l] n : ℤ) - n) =
      3^j * numer (traceWord t l) + 2^l * numer (traceWord n k) -
        (2^(k + l) - 3^(j + b)) * t := by
  dsimp only
  have hd : (2 : ℤ)^k * (tstep^[k] n : ℤ) =
      3 ^ ones (traceWord n k) * n + numer (traceWord n k) := by
    exact_mod_cast tstep_iterate_identity k n
  have hc : (2 : ℤ)^l * (tstep^[k + l] n : ℤ) =
      3 ^ ones (traceWord (tstep^[k] n) l) * (tstep^[k] n : ℤ) +
        numer (traceWord (tstep^[k] n) l) := by
    have h := tstep_iterate_identity l (tstep^[k] n)
    rw [Nat.add_comm k l, Function.iterate_add_apply]
    exact_mod_cast h
  simp only [pow_add]
  linear_combination (3 : ℤ) ^ ones (traceWord n k) * hc + (2 : ℤ)^l * hd

/-- Exact strict criterion, retaining `N_descent`.  Add `2 < n`, `0 < k+l`
and total subcriticality to obtain precisely `AcyclicParadoxical n (k+l)`. -/
theorem trunk_acyclic_criterion (n k l : ℕ) :
    let t := tstep^[k] n
    let j := ones (traceWord n k)
    let b := ones (traceWord t l)
    n < tstep^[k + l] n ↔
      (2^(k + l) - 3^(j + b) : ℤ) * t <
        3^j * numer (traceWord t l) + 2^l * numer (traceWord n k) := by
  dsimp only
  have h := trunk_slack_identity n k l
  dsimp only at h
  have hp : (0 : ℤ) < 3 ^ ones (traceWord n k) * 2^l := by positivity
  constructor
  · intro hn
    have hnz : (0 : ℤ) < (tstep^[k+l] n : ℤ) - n := by omega
    nlinarith [mul_pos hp hnz]
  · intro hs
    have hnz : (0 : ℤ) < (tstep^[k+l] n : ℤ) - n := by nlinarith
    omega

/-- Zero slack is exactly endpoint equality; the trunk identity is not restricted
to the divergence front. -/
theorem trunk_equality_criterion (n k l : ℕ) :
    let t := tstep^[k] n
    let j := ones (traceWord n k)
    let b := ones (traceWord t l)
    tstep^[k + l] n = n ↔
      (2^(k + l) - 3^(j + b) : ℤ) * t =
        3^j * numer (traceWord t l) + 2^l * numer (traceWord n k) := by
  dsimp only
  have h := trunk_slack_identity n k l
  dsimp only at h
  have hp : (0 : ℤ) < 3 ^ ones (traceWord n k) * 2^l := by positivity
  constructor
  · intro hn
    rw [hn] at h
    nlinarith
  · intro hs
    have hnz : (tstep^[k+l] n : ℤ) = n := by nlinarith
    exact_mod_cast hnz

/-- Same minimum, same depth, same prefix odd count, same climb, opposite admission.
The discarded prefix numerators are `7207` and `1375`. -/
theorem trunk_depth_data_insufficient :
    tstep^[14] 2305 = 103 ∧ tstep^[14] 2313 = 103 ∧
    ones (traceWord 2305 14) = 6 ∧ ones (traceWord 2313 14) = 6 ∧
    (∀ i ∈ Finset.range 47, 103 ≤ tstep^[i] 2305 ∧ 103 ≤ tstep^[i] 2313) ∧
    ones (traceWord 2305 46) = 29 ∧ ones (traceWord 2313 46) = 29 ∧
    (3 : ℕ)^29 < 2^46 ∧
    tstep^[46] 2305 = 2308 ∧ tstep^[46] 2313 = 2308 ∧
    numer (traceWord 2305 14) = 7207 ∧ numer (traceWord 2313 14) = 1375 ∧
    AcyclicParadoxical 2305 46 ∧ ¬ AcyclicParadoxical 2313 46 := by
  unfold AcyclicParadoxical
  decide +kernel

/-- A long admitting segment can have a one-step climb from its true minimum.
Its trunk excursion is `92/61`, so even the normalized claim `climb ≥ sqrt(m)`
fails.  This finite witness does not refute every possible asymptotic rate. -/
theorem trunk_climb_one_step_control :
    AcyclicParadoxical 91 46 ∧ tstep^[45] 91 = 61 ∧ tstep^[46] 91 = 92 ∧
    (∀ i ∈ Finset.range 47, 61 ≤ tstep^[i] 91) ∧ 92^2 < 46 * 61^2 := by
  unfold AcyclicParadoxical
  decide +kernel

end CollatzMoonshot.FrontA
