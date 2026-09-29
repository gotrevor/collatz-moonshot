# Audit of the anchored transfer constant

This audits §3 of `RESEARCH-2026-09-27-catalytic-repair.md` against the actual shortcut map `FrontB.tstep` and the coefficient formula `ArithmeticLifts.transfer`.  It is a mathematical audit and a proof handoff, not a Lean verification.

## Result and domain

Let `T=tstep` on positive integers.  For `a : ℕ → ℝ`, put `a₀=0` by convention and `(Pa)_v=a_(2v)+[v≡2 (mod 3)]a_((2v-1)/3)` for `v≥1`.  The formula counts exactly the positive preimages of `v` under `T`; the two possible preimages have opposite parity.  Let `‖a‖₁=∑_(u≥1)|a_u|/u`, and minimize `‖Pa-a‖₁` over `a_u≥0`, `‖a‖₁<∞`, `a₁=a₂=0`, `a_n=1`, where `n≥3`.

The claimed values survive the edge-case audit:

* If `n` is not periodic and its strict future `A_n={T^j(n):j≥1}` is bounded, then it is finite, forward closed, and excludes `n`.  With `M_n=max A_n`, the infimum is `1/M_n`.
* If the orbit of `n` is unbounded, the infimum is `0`.  Unboundedness already rules out periodicity.
* If `n≥3` is periodic, its whole cycle is disjoint from `{1,2}`.  Its indicator is a finite, nonnegative exact fixed vector with anchor `1`, so the infimum is `0`.  The phrase “nontrivial cycle” means this case.  A start `n≥3` cannot lie on the trivial `{1,2}` cycle.

The anchor excludes `n=1,2`, since `a₁=a₂=0` would contradict `a_n=1`.  The coordinate at zero never enters a positive transfer coefficient, so the Lean theorem can avoid stipulating `a₀=0` as long as every cut point and anchor is positive.

## Finite-cut identity and lower bound

Take any finite `A⊆ℕ_{>0}` satisfying `T(A)⊆A`, `n∉A`, and `T(n)∈A`.  Define its predecessor set and incoming boundary by

```
Pred(A) = {u>0 : T(u)∈A},
In(A)   = Pred(A) ∖ A.
```

`Pred(A)` is finite: each `v∈A` has preimages `2v` and, only when `v≡2 (mod 3)`, `(2v-1)/3`.  If `v≤M` for every `v∈A`, every predecessor is at most `2M`.  Thus all following sums are finite even when `a` has infinite support.  Fiber counting and reindexing give

```
∑_(v∈A) (Pa-a)_v
  = ∑_(u∈Pred(A)) a_u - ∑_(u∈A) a_u
  = ∑_(u∈In(A)) a_u.
```

The second equality uses `A⊆Pred(A)`, exactly the forward-closure hypothesis.  Since `n∈In(A)` and `a` is nonnegative, the right side is at least `a_n=1`.  For `0<v≤M`, `|b_v| ≤ M|b_v|/v`.  Hence

```
1 ≤ ∑_(v∈A)b_v ≤ ∑_(v∈A)|b_v|
  ≤ M ∑_(v∈A)|b_v|/v ≤ M‖b‖₁,       b=Pa-a.
```

The finite-cut inequality is stronger than the global norm lower bound and requires neither summability nor `a₁=a₂=0`.  The latter conditions enter only the definition of the infimum and the extremizers.  No assumption on the support of `a` or how its mass divides between the two incoming preimages is needed.

For a bounded nonperiodic orbit, choose `A=A_n`.  It is finite by boundedness of a set of naturals, excludes `n` by nonperiodicity, and is forward closed.  This yields `‖Pa-a‖₁≥1/M_n`.  In particular the proof does not assume convergence to `{1,2}`; a start that eventually enters a hypothetical nontrivial cycle but is itself nonperiodic is covered.

## Attainment and overlap checks

For positive `n`, the dyadic ray `D_n=∑_(h≥0)z^(2^h n)` has weighted norm `2/n`, has distinct support, and satisfies `(P-I)D_n=z^T(n)`.  This also holds when `n` is even: `T(n)=n/2` is outside the ray, while every later ray point maps to its predecessor.

Let `q=M_n` and let `L≥1` be the first time `T^L(n)=q`.  Put `F=D_n+∑_(j=1)^(L-1)z^(T^j(n))`.  The finite prefix telescopes, so `(P-I)F=z^q` and `‖(P-I)F‖₁=1/q`.  Its coefficient at `n` is one.  No positive forward iterate of a nonperiodic `n` equals any `2^h n`: if it did, `h` subsequent halvings would return to `n`.  Thus the prefix misses the ray.  The prefix before the first maximum also has no repetitions: a repetition before `L` makes the subsequent path periodic, forcing the maximum to have occurred before the repeat.  Therefore `F` has only 0/1 coefficients.

The prefix avoids `1,2`.  Once a shortcut orbit reaches either state, it remains inside `{1,2}`; if the maximum were first reached after that entry, it would be at most `2`, and its first occurrence would be the entry at `2` (the case `n≥3` enters at `1` is impossible because `T(u)=1` for positive `u` only when `u=2`).  More directly, every prefix state before the first maximum lies outside `{1,2}` unless the maximum itself is first reached at `2`.  The ray begins at `n≥3`.  The support is connected under the undirected `T` edge relation: the ray flows to `n`, and the prefix follows the forward orbit.  Its counting function below `X` is at most `⌊log₂(X/n)⌋+1+(L-1)` when `X≥n`.

For an unbounded orbit, choose arbitrarily large endpoints `q=T^L(n)`.  The same telescoping vector is admissible and has defect `1/q→0`.  The argument needs only a finite prefix up to each endpoint, not a global maximum.  If a prefix repeats, the orbit becomes bounded, so unboundedness guarantees distinctness.  For periodic `n≥3`, the finite cycle indicator is an exact fixed vector because `T` permutes its support.

Sample edges: `n=3` gives `q=8`, `F=D₃+z⁵`; `n=7` gives `q=26`, `F=D₇+z¹¹+z¹⁷`; `n=8` gives `q=4`, `F=D₈`; `n=4` gives `q=2`, `F=D₄`.  These are checks of the formula, not substitutes for the general proof.

## Scope and formalization order

The first Lean node should be the general finite-cut identity and weighted inequality for the *actual* transfer formula and an arbitrary real `a`.  This is an elementary finite-sum theorem.  Then specialize it to a bounded nonperiodic orbit and separately formalize the dyadic-ray extremizer before stating the full infimum theorem.  A cut assumption is a certificate supplied by bounded nonperiodic dynamics, not a hidden version of the desired inequality.  Neither `PositiveApproximationFamily` nor the uniform coercivity failure proves this anchored result.

The finite-cut lower bound and peak extremizer are generic directed-graph transport: the arithmetic of `3u+1` enters only in the predecessor formula and the availability of the dyadic ray.  The historical operator proposal in `APPROACHES.md` and `DIRECTION.md` is not a proof route through spectral theory.  The exact anchored constant is a reformulation of peak height plus periodic-state exclusion, not a new analytic estimate.  More generally, any fixed positive weight with summable dyadic rays makes the same endpoint construction's defect equal to the endpoint weight; merely changing the power exponent cannot supply a Collatz exclusion.  This observation does not enlarge the first Lean node.  The audit does not reopen the retired uniform coercivity or finite-prefix routes.

The first node has now been completed in `CollatzMoonshot/Obstructions/AnchoredCut.lean`: `finiteCut_identity`, `finiteCut_anchored_lower`, and `finiteCut_unit_lower`.  The three mathematical statements were preserved.  The orbit specialization, extremizer and infimum equality are still separate nodes.
