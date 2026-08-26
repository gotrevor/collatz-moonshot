# Architect notes — 2026-08-26 (the second transmission, and the Furstenberg dig)

*Session record: an interactive (non-treadmill) session opened with a strategy dialogue — the
"alien transmission" framing, round two; the first, 2026-08-22, birthed the normal-numbers
programme — and closed with Furstenberg's topological ×p×q rigidity proved and the
`Assumed/Furstenberg.lean` axiom discharged (see `STATUS.md` 2026-08-26 and
`papers/arxiv-1305.1514-manners-pyjama-furstenberg-pin.md`).  These notes keep the
strategy-layer observations that don't fit either of those.*

## The transmission-2 synthesis (strategy layer)

1. **One problem, not two.**  Normal numbers (×2 vs ×10, ×2 vs ×3) and Collatz (×3 vs ÷2)
   are the same substance: two multiplicatively independent arithmetics coupled through one
   object, with the irrationality of `log 2 / log 3` as the coupling constant.  The repo's
   "2⊥3 rigidity trinity" already says this; the dig confirmed how literally it cashes out —
   the *only* input the whole Furstenberg proof consumes from the pair `(p, q)` is
   `MultIndep p q`, used exactly twice (irrationality of the log-ratio; orbit injectivity).

2. **The ambient-space diagnosis.**  Both open problems are *inheritance* questions.  Collatz
   extended to ℤ₂ is solved (conjugate to the shift); Lebesgue-a.e. real is absolutely
   normal (Borel 1909).  The mysteries live entirely on canonical measure-zero skeletons —
   ℕ inside ℤ₂, the definable constants inside ℝ — and ask whether the thin sub-object
   inherits the genericity of its ambient space.  Ensemble instruments (measure, entropy,
   Fourier) prove the almost-all statements cheaply *because* they average over the coupling;
   the object of interest hides in exactly the null set the instrument cannot see.  "Infinity
   is hard" is the wrong diagnosis; *independence* is hard — there is no pointwise bridge
   seeing the base-2 and base-3 facts of one individual at once.

3. **Scalar invariants are provably too weak; the working invariant is structural.**
   Conway undecidability forces any proof to consume 3n+1-specific structure; entropy — the
   best scalar — already fails at the zero-entropy stratum where Furstenberg's measure
   conjecture sits (Rudolph–Johnson covers the rest).  The candidate structural invariant is
   the **carry cocycle** — the only channel through which the two arithmetics speak.
   Function-field Collatz is solved because carries die (`CarryProcess.lean` thesis);
   carrying is literally a 2-cocycle in group cohomology, published once as a curiosity and
   never weaponized.  Treat carries as the message, not the noise.

4. **The Galois move, and where this session fits.**  Galois changed the object of study
   from the roots to the symmetry structure of the question, then proved a rigidity theorem:
   that structure degenerates only in visible cases.  The analogous move: attach to each `x`
   the coupling object between its two expansions and prove it degenerates only for the
   visible exceptions.  Furstenberg's topological theorem (1967) is the first sighting of
   that object — **now machine-checked in this repo, axiom-clean**.  The live human frontier
   (Hochman–Shmerkin, Wu's slicing theorem) is already trading the global scalar for local
   multi-scale structure: right direction, insufficient magnification.

5. **Shape prediction (~60% confidence, timeline unbounded):** the crack, if it comes, is a
   pointwise rigidity statement about coupled expansions, not a cleverer induction on
   trajectories.  Tao 2019 is the ensemble-level invariant already in hand; promotion from
   ensemble to pointwise is the entire remaining game.

## Dig observations (proof-engineering layer)

- **The tier-5 grade was pessimistic.**  The catalog graded the topological theorem tier 5
  ("needs minimal closed invariant sets…").  The elementary route needs **no minimal-set
  theory at all**: derived set + difference sets + the intersection induction suffice.
  ~900 lines, one session.  Lesson for grading: a tier assigned from the *classical* proof's
  toolkit overestimates when an elementary route exists — check for one before pricing.
- **Difference sets are the lever, and the intersection induction is what converts them.**
  The recurring frustration ("I can prove `cl(S−S) = 𝕋`, not `S` dense") is resolved by
  Manners' `X_k = Y′ ∩ ⋂ (Y′ − aᵢ)` device: each stage's *difference* set being everything
  hands the next stage its *membership* witness.  Worth remembering as a general pattern —
  difference-set knowledge CAN be converted to set knowledge when an invariant grid of
  translations is available.
- **The orbit-pigeonhole trick** (`exists_fixed_in_orbit`): to fix a torsion point under
  sub-semigroup powers, don't compute orders/totients — pigeonhole the finite orbit for
  `p^r • β = p^{r'} • β`, pass to `β₁ = p^r • β`, repeat with `q`, and smul-commutativity
  keeps the first fixing.  No coprimality bookkeeping, no `addOrderOf` arithmetic.
- **Zero errata in the route** — the chink hunt's headline is a *verification* result: the
  Boshernitzan/Manners presentation survives full formalization.  The one glossed detail
  (rational limit points whose denominator shares factors with `pq`) is documented in the
  pin note.  Contrast with the Vandehey Lemma 3.2 find: not every classic hides a hole.
- **Prior-art naming trap** (for the next sweep): "Furstenberg" in the Lean ecosystem means
  *multiple recurrence* (lean-eval), *evenly-spaced-topology primes* (LeanFrontier), or the
  *measure conjecture statement* (formal-conjectures).  None is this theorem.

## Cheap spin-offs now enabled

- **FHK Lemma IV.1** (non-lacunary ⟺ consecutive ratios → 1): a formalizable one-lemma
  spin-off on top of `log_lattice_tail_dense`; rounds out the vocabulary.
- **Mahler's Theorem M** (block occurrence in multiples of an irrational): catalog sibling
  `mahler-block-occurrence`, tier 3, shares this machinery.
- **Effective layer**: Gayfulin–Moshchevitin (arXiv:2301.08212) gives the quantitative
  version with explicit rates if Lane 1 ever needs density *speeds*; their engine is
  pigeonhole + digit combinatorics on `Σ(M)`, no entropy.
- **Normal-numbers outer ring**: the disjunctive board's "Furstenberg 1967" row is now
  formalized here; the `dense_orbit_of_not_isOfFinAddOrder` corollary is exactly the
  `{2^m 3^n x}`-dense statement that board cites.
