# Architect notes - 2026-07-20 🌙

*Session handoff: what exists, why it's shaped this way, and where the next session
picks up. Written by Ren during the founding session.*

## State at handoff

- **History (3 commits + follow-ups from `23fbe84`)**: approach map → Lean layer →
  Lane 1. Build green (8573 jobs, using a local shared mathlib cache for the then-current toolchain).
  `main` was force-push rewritten 2026-07-20 to expunge an
  accidentally-committed paper PDF - don't resurrect old SHAs `d079362`/`4876a12`
  from reflogs or other clones.
- **Doc spine**: `APPROACHES.md` (the 3-route map + barriers + overlooked
  combinations) → `README.md` (layout) → `CollatzMoonshot/Rigidity.lean`
  (Lane 1 roadmap, milestones M1-M4) → this file (session-to-session thread).

## What is PROVED (all axiom-clean, verified via `#print axioms`)

| Theorem | File | Content |
|---|---|---|
| `conjecture_iff_split` | `Conjecture.lean` | Collatz ⟺ NoDivergentOrbit ∧ NoNontrivialCycle (pigeonhole + mod-period) |
| `conjecture_iff_descent` | `Descent.lean` | Collatz ⟺ DescentAll (strong induction; descent needs NO cycle argument) |
| `conjecture_of_fronts` | `Descent.lean` | the lane consumption form |
| `T2_natCast` | `Rigidity/Padic.lean` | base intertwining: `T2` on `ℤ_[2]` extends `step` through the embedding |
| `funnel`, `funnel_crash` | `Rigidity/Funnel.lean` | `step^[3s] (4^s·m + 1) = 3^s·m + 1` - 2-adic proximity to 1 is a `(3/4)^s` archimedean crash |
| `two_pow_68_lt_of_onCycle_nontrivial` | `Conditional.lean` | demo: conditional on exactly one named axiom |

## What is PINNED (and the doctrine that shapes it)

- **W1** (`Rigidity/Invariant.lean`, a `def`): T2-invariant probability measures
  supported on a positive orbit's 2-adic closure charge the embedded trivial cycle.
  **A `def`, never an `axiom`**: our own working conjectures are hypotheses;
  axioms are only for community-settled results (three-tier doctrine in
  `Assumed.lean`).
- **`RudolphJohnsonStatement entropy`** (`Rigidity/Circle.lean`): parameterized by
  an entropy functional because mathlib has **no Kolmogorov-Sinai entropy** (named
  blocker).  Deliberately NOT an axiom over an opaque entropy constant - that
  would be potentially-vacuous formalization theater.
- **Assumed roster**: Bařina `2⁶⁸` computation, Eliahou cycle bound, Tao 2019
  (citation-axiom → upgrade path: `require` tao-collatz), Furstenberg ×2×3
  topological rigidity (1967, entropy-free, hence axiomatizable).

## Load-bearing design reasoning (do not re-derive; do not violate)

1. **The 2-adic-blindness trap**: `T2` on `ℤ_[2]` is conjugate to the full
   one-sided shift (Bernstein-Lagarias), so its invariant measures are a Poulsen-
   simplex zoo - **any unconditioned dichotomy over all T2-invariant measures is
   FALSE**.  And `ℤ_[2]` cannot see archimedean size, so **no pure-ℤ₂ measure
   statement can imply NoDivergentOrbit by itself**.  The arithmetic/archimedean
   coupling must enter through the conditioning (W1 uses orbit-closure support) or
   a product-space upgrade.  This is exactly the "intertwining gap" of
   APPROACHES.md Approach 1 - it's the feature, not a bug.
2. **The funnel is the coupling seed**: charging the trivial cycle at all 2-adic
   scales with positive frequency forces recurrent `(3/4)^s` size crashes.  M2's
   real content is upgrading the pointwise funnel to a frequency/all-scales
   argument.
3. **The two-proof architecture** (barrier 1, 3x−1): statistical/ergodic methods
   own Front A (divergence), arithmetic owns Front B (cycles).  Don't try to make
   one tool do both.
4. **Eliahou map bookkeeping** ⚠️: the famous `17,087,915` counts SHORTCUT-map
   steps (`(3n+1)/2`); this repo's un-shortened `step` figure is `27,869,189`
   (= 17,087,915 + 10,781,274 odd steps).  Modern frontier (Hercher 2023 +
   Bařina `2⁷¹`): ~`3.6 × 10¹¹` for our map - **unadopted pending firsthand
   verification** of those two papers.  See `papers/eliahou-1993-summary.md`.

## Next moves (M2 first)

- **M2 = `MeasureRigidityW1 → NoDivergentOrbit`.**  Ingredients:
  (a) `T2` continuity (provable now: parity is clopen; `half` is 2-Lipschitz on
  the even set) and measurability - prerequisites for any transfer;
  (b) a Krylov-Bogolyubov transfer axiom (THEOREM-grade, textbook: compact space +
  continuous map ⟹ orbit-limit invariant measures supported on the orbit
  closure) in a new `Assumed/KrylovBogolyubov.lean`;
  (c) the frequency/all-scales funnel upgrade - the genuinely new lemma.
  Suggested first Lean bite: prove `Continuous T2` + `Measurable T2`; then state
  the K-B axiom precisely (quantify over the orbit closure, per the blindness
  trap).
- **Optional vocabulary**: empirical orbit measures + `MapClusterPt` over
  mathlib's `ProbabilityMeasure` weak topology (sketch exists in the founding
  session; the `(N+1)⁻¹ • ∑ dirac` mass proof is routine ENNReal juggling).
- **M3**: transfer principles of the 2⊥3 trinity (Baker ↔ Furstenberg ↔ Cobham).
- **Lane 2 seed** (when wanted): the transducer/Cobham route - `Sturmian.lean` in
  collatz-cryptid is the existing panel.

## House rules for this repo (differs from the fleet norm)

- **Investigatory**: axioms welcome under the three-tier doctrine
  (`Assumed.lean`); dev tier (warnings visible, no `warningAsError`);
  `autoImplicit = false` set at birth.
- **Parallel sessions are active here** 🤝: a second session harvests the cycle
  literature into `papers/` (Eliahou fact-check, Knight 2026 high-cycles).
  **Use explicit `git add <paths>` - never `add -A`** (an `-A` sweep is how the
  PDF hit history).  `*.pdf` is gitignored globally AND locally; PDFs live on
  disk beside committed summaries.
- Naming: `step` (not `col` - dodges the mathlib `col`=column collision debate
  from tao-collatz issue #4).  Global pre-commit green-gate builds on commit;
  `hooks.allowDirectMain true` is set (notes repo, direct-to-main).
- Next architect notes: `architect-notes-YYYY-MM-DD.md`, one per working day;
  supersede this one by linking back.
