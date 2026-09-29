# Signed edge balance and the post-cubic basin cut

Let `T=tstep`, let `e_u` denote the integer basis vector at `u`, and put `B(u)=e_u-e_(T(u))`.  A finite signed edge chain is `c:ℕ→₀ℤ`, with boundary `∂c=Σ_u c(u)B(u)`.  Write `C={u:∃k,T^[k](u)=1}` for the actual basin of the `1↔2` cycle.  Since `T(1)=2` and `T(2)=1`, the exact equivalence is

```
u ∈ C  ↔  T(u) ∈ C.                                  (1)
```

Hence the integer indicator `χ_C` pairs to zero with every edge boundary, including one with negative coefficients: `⟨χ_C,∂c⟩=0`.  If a finite chain satisfies `∂c=k(e_n-e_1)` for any nonzero integer `k`, pairing gives `0=k(χ_C(n)-1)`, so `n∈C`.  Conversely, a trajectory from `n` to `1` gives a finite nonnegative path chain with boundary `e_n-e_1`.  Thus finite *signed* vertex balance is equivalent to convergence.  [SignedFlow.lean](CollatzMoonshot/Obstructions/SignedFlow.lean) proves this equivalence and its nonzero-scale version without assuming nonnegativity.  It simplifies extraction **once a chain exists**; it does not construct a chain for a new start.

## The hard cubic family under strong induction

Use the hard `K=64` class and notation of `RESEARCH-2026-09-29-head-continuation.md`: `m<n`, `a=T(n)`, `v=T(5n)`, and `T(v)=16m`.  The first Q supply and five-head Q rows, followed by the variable cubic, leave the *projected central* residual

```
R = e_(16m) - e_(T(a))
    + B(d)+B(b)+B(e1)+B(e2)
    - B(x)-B(z)-B(q1)-B(q2).                         (2)
```

All eight listed auxiliary labels `d,b,e1,e2,x,z,q1,q2` are positive and below `m`; `c` is a ninth low auxiliary already canceled between the first two Q rows.  If strong induction gives convergence of every positive input below `n`, all nine auxiliaries and `m` lie in `C`.  The explicit virtual edges `5n→v→16m→8m→4m→2m→m` then put `16m` and `v` in `C` as well.  Equation (1) implies `T(a)∈C` exactly when `n∈C`.  Pairing (2) therefore yields

```
⟨χ_C,R⟩ = 1 - χ_C(T(a)) = 1 - χ_C(n).               (3)
```

This is an exact obstruction to closing the residual using *only* already-convergent auxiliary paths.  Every extra genuine edge boundary has zero basin pairing, so attaching the known paths for labels below `m`, extending the virtual path to `m`, or adding arbitrary unit words cannot alter (3).  If `n` were a counterexample, (3) would equal `1`, whereas a fully balanced endpoint has pairing zero.  Some step must connect the actual frontier to the known basin.  Merely reducing the number of remaining virtual edges, or borrowing and returning more low factors, does not supply that step.

There is an equivalent quotient description.  Let `F=ℤ^{(ℕ)}` and `K_C=span{e_u-e_1:u∈C}`.  Under the induction hypothesis, every low auxiliary boundary and `e_(16m)-e_1` lies in `K_C`, so the class of (2) in `F/K_C` is `e_1-e_(T(a))`.  If `n∉C`, this class is nonzero: its coefficient in the complement of `C` survives.  This quotient uses the *actual* basin and is a diagnostic, not a computable rank that proves convergence.  Replacing `C` by only the IH-known vertices gives the same bookkeeping warning but loses the universal annihilation statement unless that set is closed under both directions of `T`.

The scalar cubic identity is compatible with (3) because equality of rational products carries no vertex-boundary information.  Unrestricted supply of 3-free unit factors solves their scalar availability; it does not make the inserted word boundary zero.  The common-unit return architecture ensures a particular bookend cancellation when achieved, but signed-flow extraction itself does not require positivity or that architecture.  Its missing premise is exact finite vertex balance, which is equivalent to the desired convergence.

## Signed support does not literally contain the path

The chain `c(4)=1`, `c(1)=-1`, all other coefficients zero, is a counterexample to the claim that every signed witness contains the forward path in its support.  Since `T(4)=T(1)=2`,

```
∂c = B(4)-B(1) = e_4-e_1.
```

Yet its support has edges `4→2` and `1→2`, and omits the forward edge `2→1` needed to reach `1`.  The actual path chain `e_4+e_2` differs from `c` by the directed `1↔2` circulation `e_1+e_2`.  This is consistent with signed-flow extraction: the basin cut proves reachability, while a cycle adjustment may be needed before the witness visibly contains the complete path.  No support-cardinality path bound is asserted here.
