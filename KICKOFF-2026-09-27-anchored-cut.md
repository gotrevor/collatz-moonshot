# Authorized bounded Opus/low task

Trevor explicitly requested continued progress on all three branches and delegation.  This task formalizes an audited finite-cut argument; it is not a general Collatz campaign.  Edit only CollatzMoonshot/Obstructions/AnchoredCut.lean and HANDOFF-2026-09-27-anchored-cut.md.  Other agents own disjoint experiments and notes.  Do not modify other Lean files, root imports, DIRECTION, experiments, or other notes.  The host installed the root import.  The three target propositions are frozen; equivalent predecessor representation is allowed, weakening assumptions or conclusions is not.  If a statement is false, report the counterexample.  Commit a green checkpoint; partial progress can retain explicitly named open leaves.  Complete the three headlines, run the root build, write the handoff, and stop.  No successor task.  Warm host dependencies were checked; no dependency downloads or cache fetches.

# Frozen first node: anchored finite-cut transfer inequality

Target source: `CollatzMoonshot/Obstructions/AnchoredCut.lean`.  Import `CollatzMoonshot.Obstructions.ArithmeticLifts`; reuse `FrontB.tstep`.  This is one bounded, elementary formalization node.  No infinite norm, `tsum`, spectral theory, or orbit classification is needed for its acceptance.

## Exact mathematical acceptance

For every finite positive forward-closed cut `A`, every positive `n` outside it with `tstep n∈A`, every real coefficient function `a` nonnegative on positive indices, and every positive bound `M` on `A`:

1. The sum of actual transfer defects over `A` equals the sum of coefficients on the incoming boundary `{u>0:tstep u∈A,u∉A}`.  This boundary is represented by a finite `Finset`, with all positive predecessors captured.
2. The anchored coefficient satisfies `a n ≤ M * ∑_(v∈A)|transferReal a v-a v|/v`.  In particular, if `a n=1`, then `1/M ≤ ∑_(v∈A)|transferReal a v-a v|/v`.

The target quantifies over **all** `a : ℕ → ℝ`.  The nonnegativity condition is used only for the boundary inequality; the identity must hold for signed `a` too.  There is no finite-support assumption and no premise that already says the defect has positive mass.

## Suggested Lean declarations

These are frozen mathematical statements; syntax may be adjusted during elaboration without changing the propositions.  In particular, the image-based finite predecessor set may be replaced by an equivalent `Finset.range` filter if that simplifies the proof.

```lean
namespace CollatzMoonshot.Obstructions.ArithmeticLifts

open CollatzMoonshot.FrontB

def transferReal (a : ℕ → ℝ) (v : ℕ) : ℝ :=
  a (2 * v) + if v % 3 = 2 then a ((2 * v - 1) / 3) else 0

def predecessors (A : Finset ℕ) : Finset ℕ :=
  (A.image fun v => 2 * v) ∪
    ((A.filter fun v => v % 3 = 2).image fun v => (2 * v - 1) / 3)

def incoming (A : Finset ℕ) : Finset ℕ := predecessors A \ A

theorem finiteCut_identity (A : Finset ℕ) (a : ℕ → ℝ)
    (hpos : ∀ v ∈ A, 0 < v)
    (hclosed : ∀ v ∈ A, tstep v ∈ A) :
    (∑ v ∈ A, (transferReal a v - a v)) =
      ∑ u ∈ incoming A, a u := by
  ...

theorem finiteCut_anchored_lower (A : Finset ℕ) (a : ℕ → ℝ)
    (n M : ℕ)
    (hpos : ∀ v ∈ A, 0 < v)
    (hclosed : ∀ v ∈ A, tstep v ∈ A)
    (hnpos : 0 < n) (hnout : n ∉ A) (henter : tstep n ∈ A)
    (ha : ∀ u, 0 < u → 0 ≤ a u)
    (hM : ∀ v ∈ A, v ≤ M) :
    (a n : ℝ) ≤ (M : ℝ) *
      ∑ v ∈ A, |transferReal a v - a v| / (v : ℝ) := by
  ...

theorem finiteCut_unit_lower (A : Finset ℕ) (a : ℕ → ℝ)
    (n M : ℕ)
    (hpos : ∀ v ∈ A, 0 < v)
    (hclosed : ∀ v ∈ A, tstep v ∈ A)
    (hnpos : 0 < n) (hnout : n ∉ A) (henter : tstep n ∈ A)
    (ha : ∀ u, 0 < u → 0 ≤ a u)
    (hM : ∀ v ∈ A, v ≤ M) (hanchor : a n = 1) :
    (1 : ℝ) / (M : ℝ) ≤
      ∑ v ∈ A, |transferReal a v - a v| / (v : ℝ) := by
  ...

end CollatzMoonshot.Obstructions.ArithmeticLifts
```

`M>0` follows from `tstep n∈A`, `hpos`, and `hM`.  The positivity of `n` is explicit; no condition at `a 0` is needed.  If Lean's `∑ v ∈ A` parses as a dependent sum over `v` rather than a Finset sum, normalize to `∑ v ∈ A, ...` in the file.  Keep all target names distinct from existing definitions.

## Proof route

1. Prove the fiber lemma for positive `v`: `u>0 ∧ tstep u=v` iff `u=2v` or (`v%3=2` and `u=(2v-1)/3`).  Both cases use `omega` after splitting on parity.  The odd inverse is positive and odd.  Show the two images in `predecessors A` are disjoint by parity; each map is injective on its filtered domain.
2. Reindex the two summands of `∑v∈A transferReal a v` through those images.  Obtain `∑_(u∈predecessors A)a_u` for arbitrary signed `a`.  This is the only substantial Finset bookkeeping step.  An alternative is `predecessors A=(Finset.range (2*M+1)).filter (fun u => 0<u ∧ tstep u∈A)`, prove fiber counting with `sum_comm`, then specialize using `hM`.
3. By `hclosed` and `hpos`, every `u∈A` lies in `predecessors A`.  Split `predecessors A` into `A` and `incoming A`, then cancel `∑A a_u`.  This yields `finiteCut_identity`.  Avoid inserting nonnegativity here.
4. By `henter`, `hnpos`, and `hnout`, `n∈incoming A`.  Since all incoming vertices are positive and `a` is nonnegative there, `a n≤∑incoming a`.  Combine with the identity, `x≤|x|`, and `|b_v|≤M|b_v|/v` for each `v∈A`.  Sum.  The scalar inequality follows from `0<v≤M` and nonnegativity of `|b_v|`.
5. Derive the unit corollary by division using `M>0`.  The point of the theorem is that it does not assume `a` has finite norm; when that norm exists, the global lower bound follows from the finite-sum bound by comparison with `∑_(v≥1)|b_v|/v`.

## Review checks

* The theorem calls the real version of the same predecessor formula as `ArithmeticLifts.transfer`.  Do not prove a result for an unrelated abstract `P` without a bridge to this formula.
* Check `v=1,2`, especially `tstep 2=1` and the odd predecessor `1` of `2`.  The lower-bound theorem allows cuts containing these points even though admissible global coefficients set `a₁=a₂=0`.
* Check even `n` (`n=8`, `A={4,2,1}`, `M=4`) and an odd `n` (`n=3`, `A={5,8,4,2,1}`, `M=8`).  These are statement controls, not a substitute for the quantified theorem.
* A theorem that assumes `∑A b_v≥a_n`, that restricts `a` to finite support, or that only treats the `PositiveApproximationFamily` coefficients does not meet acceptance.

Stop after this node is green and report the exact theorem names and any proposition changes.  The later orbit-cut construction, dyadic-ray extremizer, and infimum equality are separate nodes.
