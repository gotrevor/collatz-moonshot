# Sharp anchored constant: first-hit and norm audit

This is the next theorem blueprint after the proved `OrbitPrefix.lean` and `AnchoredCut.lean`.  It concerns the shortcut map `T=FrontB.tstep`, positive starts `n≥3`, nonnegative coefficient functions with finite `∑_(u≥1)a_u/u`, `a₁=a₂=0`, and `a_n=1`.  It is a formalization of orbit height, not an independent Collatz estimate.  `DIRECTION.md` still retires finite-prefix filtering as a route to the conjecture.

## Correction to the paper proof

The sentence in §3 of `RESEARCH-2026-09-27-catalytic-repair.md` that calls the extremizer's finite prefix “distinct and disjoint from the ray” needs two different arguments.  Nonperiodicity of the **base** `n` proves ray disjointness: if `T^j n=2^h n` for `j≥1`, then `h` halving steps return to `n`, so `T^(j+h)n=n`.  It does **not** make the entire future injective.  For example, the orbit of `3` eventually repeats `1,2`.

The proved `orbitPrefix_defect` counts prefix states with multiplicity and needs no injectivity.  Thus the exact infimum's upper bound does not need prefix distinctness.  For the optional assertion that the extremizer has 0/1 coefficients, add the first-hit lemma below.  This repairs a proof omission; it does not change the value of the constant.

## First-hit lemmas for the bounded case

Let `A={T^j n:j≥1}` be bounded and let `q=max A`.  Then `q≥Tn≥2`; choose the *least* `L≥1` with `T^L n=q`.  The strict future is finite and forward closed.  If `n` is nonperiodic, then `n∉A`.

1. **Prefix avoids the forbidden coefficients.**  For every `1≤j<L`, `T^j n∉{1,2}`.  Once a positive shortcut orbit enters `{1,2}`, it alternates inside it.  If `q>2`, it cannot be reached after such an entry.  If `q=2`, an earlier `2` contradicts the choice of `L`; an earlier `1` must have an earlier predecessor `2` because the only positive preimage of `1` is `2`, and `n≥3`.  This is the exact place where the first-*maximum* choice matters.  It also covers `n=4`, where `q=2,L=1` and the prefix is empty.
2. **Prefix misses the dyadic ray.**  For all `j≥1,h≥0`, `T^j n≠2^h n`, by the return-to-`n` argument above.  This includes `h=0`, so the prefix never adds a second coefficient at the anchor `n`.
3. **Optional 0/1 lemma.**  The states `T^j n`, `0≤j≤L`, are pairwise distinct.  Suppose `i<j≤L` repeat.  If `j=L`, `q` appeared at `i<L`.  Otherwise, determinism makes the tail from `i` periodic with period `d=j-i`; the value at `L` also occurs at the earlier index `i+((L-i) mod d)<j≤L`.  That contradicts the first occurrence of `q`.  If `i=0,j=L`, the contradiction uses nonperiodicity of `n` (indeed `q=n`); for all other cases the first-hit condition suffices.  This is a finite first-hit fact, not injectivity of the infinite orbit.

With `F_{n,L}(v)=orbitPrefixCoeff n L v`, items 1 and 2 give `F(1)=F(2)=0` and `F(n)=1`, plus nonnegativity.  Item 3 and ray disjointness give 0/1 coefficients if that extra claim is desired.  The ray and the finite prefix form connected support under the undirected `T` edges.  No 0/1 proof is needed to establish the numerical infimum.

## Bridge from the current Lean theorems

The proved `OrbitPrefix.orbitPrefix_defect` is over `ℚ`.  Set `a_F(v)=(orbitPrefixCoeff n L v:ℝ)`.  A direct cast-and-unfold lemma should give, for positive `v`,

```
transferReal a_F v - a_F v
  = if v = T^L n then 1 else 0.
```

There is no issue at coordinate zero because the weighted norm starts at `v=1`, and `T^L n>0`.  Thus the weighted defect of `F` is exactly `1/(T^L n)` once summability is installed.  The norm of `F` is finite: the dyadic ray contributes `∑_(h≥0)1/(2^h n)=2/n`, and the remaining prefix has `L-1` finite terms, counted with multiplicity.  One can establish this by reindexing the injective power-of-two map and adding the finite prefix.  `P` bounded by 2 on this weighted ℓ¹ space then makes the defect norm finite for every admissible `a`.  Alternatively use an extended nonnegative `tsum` for the defect and prove finiteness before converting to a real value; do not apply real `tsum` to a series whose summability has not been proved.

For the lower bound, use the finite cut `A.toFinset`, bound `M=q`, and `AnchoredCut.finiteCut_unit_lower` on the *arbitrary real* admissible `a`.  Compare its finite sum with the global nonnegative weighted defect sum.  This yields `1/q≤‖(P-I)a‖` for every admissible `a`, without assuming the orbit reaches `{1,2}`.  The `F_{n,L}` bridge above attains equality.  A bounded nonperiodic start that eventually enters a hypothetical nontrivial cycle is included.

For an unbounded orbit, every prescribed height occurs below some positive endpoint `q=T^L n`.  Unboundedness prevents all repetitions and any visit to `{1,2}`.  The same finite `F_{n,L}` is admissible, has defect `1/q`, and choosing `q→∞` proves that the infimum is zero.  No first-maximum construction or bounded cut is used in this case.  A periodic start `n≥3` is a separate case: its cycle indicator is a finite admissible exact fixed vector.

## Recommended formal theorem shape

Prove concrete lower and attainment statements before introducing `sInf`:

```
bounded_nonperiodic_lower:
  boundedStrictFuture n → ¬PeriodicPoint T n →
  ∃ q, q∈strictFuture n ∧ (∀v∈strictFuture n, v≤q) ∧
    ∀ a, Admissible n a → 1/(q:ℝ) ≤ defectNorm a

bounded_nonperiodic_attains:
  same hypotheses and q chosen as above →
  ∃ a, Admissible n a ∧ defectNorm a = 1/(q:ℝ)

unbounded_arbitrarily_small:
  unboundedStrictFuture n →
  ∀ ε:ℝ, 0<ε → ∃ a, Admissible n a ∧ defectNorm a < ε
```

The `q` in the lower theorem should be the actual maximum, not an arbitrary upper bound, when asserting sharpness.  A later corollary may package these into `c_n=1/q` or `c_n=0`.  None of these statements supplies an arithmetic bound on `q` or excludes a nontrivial cycle.
