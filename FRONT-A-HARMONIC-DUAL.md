# Front A: harmonic dual obstruction project

## Why this is the next pull

The local certificate ladder has reached endpoint exponent `4/5`.  Merely
porting another subharmonic exponent is now mechanical and does not address the
real question: can this finite-state, uniform local-potential architecture ever
reach harmonic exponent `1`?

At ternary depth `k`, with the five height floors `{1,7/4,3,6,12}`, let `S_k`
be the unit-residue/height states and let `A(s,t)` be the child edges for source
state `s` and shared next ternary digit `t ∈ {0,1,2}`.  At harmonic weight the
three alternative linear images are

```
(M_{k,t} V)(s) = Σ_(j,u)∈A(s,t) (3 / 2^j) V(u).
```

A positive harmonic local certificate would have to satisfy

```
V(s) < (M_{k,t} V)(s)    for every state s and every lift t.
```

Therefore one adversarial policy `τ : S_k → {0,1,2}` is enough to obstruct it.
Write `M_{k,τ}` for the matrix using alternative `τ(s)` in row `s`.  If a
positive left weight `π` satisfies

```
M_{k,τ}ᵀ π < π
```

componentwise, multiplying and summing gives the immediate contradiction
`πᵀV < πᵀM_{k,τ}V < πᵀV`.  This is the useful dual/Farkas side of the search.

## Evidence already obtained

1. The nonlinear minimizing policies at depths `2..7` have harmonic radii
   approximately

   ```
   .575889, .713279, .769656, .801982, .819871, .841114.
   ```

   Exact integer left-dual contractions can be obtained simply by numerically
   solving `π = 1 + Mᵀπ`, scaling/rounding, and checking all column inequalities
   over the common denominator `2^23`.  This certifies finite-depth
   impossibility but the minimizing policies use essentially all available
   residue digits, so freezing their tables is not the desired theorem.

2. More promisingly, no optimized policy is needed.  The constant policy
   `τ(s)=1` has measured harmonic spectral radii

   | depth | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
   |---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
   | radius | .954264 | .794776 | .893423 | .943438 | .935529 | .934178 | .932160 | .932889 | .933090 |

   The stable value near `.933` suggests a structural contraction rather than
   a lucky finite table.  For every tested depth, a sufficiently high power
   also has unweighted maximum column sum below `1`; the required power grows
   mildly with depth (about `50` at depth `9`, `55` at depth `10`), so a single
   fixed block-length/unweighted proof is not yet established.

3. `experiments/barrier_two_step.py` confirms that preserving two source digits
   through two generations gives a real but smaller gain than retaining one
   extra residue digit.  Do not formalize that control as a new exponent rung.

These numbers are diagnostics, not a proof of a depth-uniform gap and not a
claim about the full barriered tree.

## Project

### A. Make the dual experiment reproducible and exact

Add `experiments/barrier_harmonic_dual.py` using the transition builder already
in `experiments/barrier_transfer.py`.

- Support minimizing and fixed policies, especially constant digits `0,1,2`.
- Report Collatz lower/upper radius bounds, the chosen policy, and compression
  statistics by residue memory.
- Construct a positive numerical left dual (for example via
  `π = 1 + Mᵀπ`), round it to integers, and verify every contraction inequality
  by integer arithmetic at common denominator `2^23`.  The verifier, not the
  eigensolver, is authoritative.
- Cross-check small depths by an independent direct construction.  Test depths
  through at least `10` in the optimized fixed-policy mode.
- Repeat the fixed-policy experiment with more than seven reusable growing
  costs and with refined/taller height grids.  The seven-child/five-floor model
  must not be mistaken for the full tree.  Record whether the apparent `.933`
  gap survives these refinements.
- Keep default runtime modest; expose deep modes explicitly.

### B. Search for a depth-independent contraction

Start from constant lift digit `1`; it is deliberately simpler than the
pointwise minimizing policy.

- Derive the exact residue map and transpose action rather than treating the
  sparse matrices as opaque data.
- Compare left Perron/Neumann weights under projection
  `S_(k+1) → S_k`.  Look for a compatible 3-adic measure, a bounded-distortion
  weight, a finite cone, or a weighted norm whose contraction constant is
  strictly below `1` uniformly in `k`.
- Test candidate formulas exactly at increasing depths and actively search for
  counterexamples.  A pattern fitted only through depth `10` is not a theorem.
- A finite-memory policy/dual is welcome, but current minimizing policies do
  not compress: at depth `7`, remembering only six digits predicts about `63%`
  of the optimized choices.  Prefer the constant policy if it survives.

### C. Formalize only genuine Collatz-specific content

The finite-dimensional dual implication itself is elementary linear algebra;
do not spend a treadmill proving a giant generic framework unless it is needed
to state the actual result.

If a clean uniform contraction is found, add a focused
`CollatzMoonshot/FrontA/BackwardHarmonicObstruction.lean` proving the exact
Collatz-specific policy/weighted-norm theorem and its consequence: no positive
potential of the stated architecture satisfies all harmonic alternatives.
Import it from `CollatzMoonshot.lean`, run `lake build` and `#print axioms`, and
document precisely which architecture is ruled out.

If no stable contraction is found, do **not** manufacture a theorem or freeze a
huge depth-specific table.  Commit the exact experiment and a clear negative
report identifying which refinement breaks the conjectured gap.

## Guardrails

- Do not add axioms, weaken existing statements, or claim a result about
  Collatz divergence from a no-go theorem for one certificate architecture.
- Do not port the `4/5` pipeline to another exponent in this project.
- `native_decide` is allowed for finite exact checks, but prefer a compact
  symbolic proof if the discovered contraction genuinely has one.
- Preserve the distinction among: numerical spectral evidence, exact
  finite-depth dual certificates, a depth-uniform theorem, and the full
  barriered backward tree.
- Commit coherent progress, including negative results.
