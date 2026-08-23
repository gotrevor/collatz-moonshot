# Sketch: `Collatz ∈ Π⁰₂`, stated and proved in Lean 🎯

*Status: SKETCH (2026-08-22).  Trevor: "sketch this out; will finish it later."  Nothing
below is built.  Estimated effort when picked up: days, not weeks (~75%).*

## What is being claimed, precisely

Collatz is a **sentence**, not a set, so "Collatz ∈ Π⁰₂" is a claim about **syntax**: there
is a Π₂ *formula* of first-order arithmetic whose standard-model truth is equivalent to the
conjecture.  This needs a formula hierarchy - which mathlib lacks entirely and
**Foundation (FFL) has in full**:

- `LO.FirstOrder.Arithmetic.Hierarchy : Polarity → ℕ → Semiformula L ξ n → Prop`
  (`Foundation/FirstOrder/Arithmetic/Basic/Hierarchy.lean`)
- `HierarchySymbol` / `𝚺-[m]` / `𝚷-[m]` / `𝚫-[m]`, `ℌ.Semisentence k`, `Defined`,
  `Definable`, the `definability` tactic, and the `𝚺₁-Function₂ f via fDef` idiom
  (`.../Arithmetic/Definability/`).

(The *computability* hierarchy - Σ⁰ₙ as "r.e. in the (n-1)-jump" - is the other object;
Post's theorem is the bridge.  Out of scope here; see the parked target
`post-theorem-ffl-bridge` in the KB catalog.)

## Deliverable

A theorem of the shape:

```
theorem collatz_pi2 :
    Hierarchy 𝚷 2 collatzSentence
    ∧ (ℕ ⊧ₘ collatzSentence ↔ Conjecture)
```

i.e. (a) the sentence is syntactically Π₂ (this half should be `by simp`/`Hierarchy`
lemmas - the definition is *engineered* to make it discharge), and (b) its standard-model
evaluation is THIS repo's `Conjecture`.  Half (b) is the real work and the honest
faithfulness surface.

## Proof-shape (4 steps)

1. **`collatzStep` is Δ₀/Σ₁-definable.**  `step(x) = if 2 ∣ x then x/2 else 3x+1` -
   division-by-2 and case-split on parity are bounded-quantifier material.
   `𝚺₀.Semisentence 2 := .mkSigma "…"` + `definability`.  Goodstein's
   `scratchpad/icmp_test.lean` is the exact template (same `.mkSigma` + `via` idiom).
2. **Iteration is Σ₁.**  `f^[i](n) = m` needs a course-of-values/β-function encoding of
   the finite run.  Foundation has Σ₁ recursion machinery (it powers Gödel coding; the
   goodstein work leaned on it).  This is the step with actual content - budget most of
   the effort here.
3. **`Reaches1 n := ∃ i, step^[i] n = 1` is Σ₁** (∃ over a Σ₁ matrix).
4. **`collatzSentence := ∀ n > 0, Reaches1 n` is Π₂.** ✅

Then half (b): evaluate with `Semiformula.Eval` against ℕ and connect to
`CollatzMoonshot.Conjecture` (via `conjecture_iff_split` or directly).

## Where it lives - decision deferred to pickup time

Two options, pick when finishing:

- **Option 1: separate mini-repo** (`collatz-pi02` or a `lean-formalizations/` corner),
  `lake-base init` with mathlib + Foundation.  Keeps this repo's lakefile a clean single
  mathlib pin.  ⚠️ Check the 4.31.0 store carries Foundation (lean-universe repointed
  store-Foundation → upstream `1527b595`, 2026-07-03, green) so the CoW link is free.
- **Option 2: add Foundation to THIS repo's lakefile.**  One artifact, no new repo, but
  drags in doc-gen4 + 5 docs-only deps and couples the moonshot build to Foundation churn
  (mitigation if ever needed: the goodstein `Compat.lean` shim pattern).

Lean toward Option 1 (~70%) - this artifact is *about* Collatz but not *of* the moonshot's
proof program, and the moonshot's clean pin is worth protecting.

## Doctrine notes for the pickup session

- **Zero sorries; pins are `def`s, cited results are named axioms** (repo doctrine).
  Expected axiom footprint of the finished theorem: `[propext, Classical.choice,
  Quot.sound]` only - nothing here needs an Assumed/.
- **Faithfulness**: the one trusted joint is that `collatzSentence`'s evaluation really is
  `Conjecture` - keep that bridge on upstream Foundation API directly, small and readable.
- Payoff framing (honest): documents the problem's logical shape (why "one halting oracle
  short of checkable"); zero progress on Collatz itself.  A nice `#eval`-adjacent artifact
  and a blog seed, not a front.
