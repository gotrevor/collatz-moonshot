# Coefficient-ray actual-edge obstruction: bounded Lean lap

Own only `CollatzMoonshot/Obstructions/CoefficientRay.lean` and `HANDOFF-2026-09-29-coefficient-ray.md`.  The frozen skeleton is installed in the repo.  Preserve **every definition and frozen theorem statement** exactly, including both six-step affine identities in `rayEdge`, the inherited multiplier update `τ.1=3*σ.1`, and the integer offset `-4`.  Parent has installed the root import and frozen consumer section in `scripts/AxiomAudit.lean`; do not change these.  Import `Q1Reentry` as staged.  No hard-family CRT theorem, no convergence assumption, no unrelated refactor, and no stronger impossibility claim.

The mathematical claim is local but genuine: for every `j`, an actual positive pair witnesses six `FrontB.tstep` iterations from signature `(72*3^j,-4)` to `(72*3^(j+1),-4)`.  The pair changes with `j`, so this is an infinite path in the *projected edge graph*, not an infinite positive Collatz orbit.  A state-only rank into any well-founded relation cannot strictly decrease on each edge.  The paper/CLI result that arbitrary finite prefixes lift into the original hard family is **outside this Lean module**.

## Arithmetic for the six actual steps

Put `K=72*3^j*w`, positive when `w>0`.  Then `rayA j w=64*K-5`.  Its six values are

```
64K-5 → 96K-7 → 144K-10 → 72K-5
      → 108K-7 → 162K-10 → 81K-5.
```

The parity word is `110110`.  For `rayB w=64w+1`, the six values are

```
64w+1 → 96w+2 → 48w+1 → 72w+2
      → 36w+1 → 54w+2 → 27w+1.
```

Its parity word is `101010`.  Use local private one-step parity helpers or unfold `tstep` with parity facts, then compose six steps using `Function.iterate_succ` as in `Q1Reentry.lean`.  Keep `K` opaque to `omega`; prove `0<K` from `w>0` and `pow_pos`, and use `ring` to expose the linear forms.  The output `81K-5` is exactly `216*3^j*(27*w)-5` by multiplication arithmetic.  No `native_decide` is needed for the variable statements.

For the witness theorem, natural subtraction is safe because `K≥72`.  The actual outputs imply

```
64A' = 81A+85,       64B' = 27B+37,
A+5 = (72*3^j)(B-1),
A'+5 = (72*3^(j+1))(B'-1).
```

Derive strict `A<A'`, `B'<B`, `A>B`, and positivity from `w>0`.  For `carriesSignature`, cast the two natural equalities to `ℤ` after eliminating the natural subtraction.  Since `(A+1)=m(B-1)-4`, both signatures have the inherited fixed offset.  `ray_edge_exists` takes `w=1` and packages `ray_edge_witness`; no arbitrary unit insertion or abstract successor is involved.  Hand anchor: `(A,B)=(4603,65)` at `j=0,w=1` actually maps in six steps to `(5827,28)`.

For the final theorem, assume a rank and get `hstep j : r (rank (raySignature (j+1))) (rank (raySignature j))` from `ray_edge_exists j`.  Well-founded induction on `rank (raySignature 0)` yields a contradiction: the induction predicate may be `fun x => ∀ j, rank (raySignature j)=x → False`; at index `j`, use `hstep j` and the induction hypothesis on the successor.  This handles arbitrary well-founded codomains, not only `ℕ`.  Do not replace the well-founded hypothesis with a natural bound or weaken `rayEdge` to an unevidenced coefficient successor.

At most **three Opus/low laps**.  A lap advances the actual-step proof or the well-founded extraction, even if it adds named helper lemmas.  Build the module and root only after the proof is ready, run `lake env lean scripts/AxiomAudit.lean`, commit green, write the handoff, then `box done --green`.  Report only completed checks.  Do not start a successor task or use Aristotle.  Parent controls launch and integration; this kickoff does not authorize an agent to change the original hard-family files.
