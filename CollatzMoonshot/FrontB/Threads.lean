/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CollatzMoonshot.FrontB.Words
import CollatzMoonshot.FrontB.Negative
import CollatzMoonshot.Basic
import CollatzMoonshot.Assumed.ABC

/-!
# The Front B thread board, as Lean 🎲

`FRONT-B-ROUTES.md` is the prose map; this file is the same map as **statements**, so that
"killed" means a theorem and "open" means a `Prop` nobody has inhabited.  Odds live in the
docstrings and are the author's, not facts.

House doctrine (`Assumed.lean`) applies: **our own conjectures are `def`s, never `axiom`s.**
Only community-settled results become axioms, and each is named so `#print axioms` keeps
them distinguishable.

✅ **Bridge landed** (2026-08-23): the dictionary between `Conjecture.lean`'s
`NoNontrivialCycle` (on `ℕ`) and `FrontB` below (on words) - the Halbeisen-Hungerbühler /
Bernstein-Lagarias correspondence - is proved sorry- and axiom-free in
`FrontB/Dictionary.lean` (`noNontrivialCycle_iff_frontB`).  Every result in this file is
now a genuine statement about Collatz on `ℕ`.  (Landing it required correcting
`IsTrivial`: see its docstring.)
-/

namespace CollatzMoonshot.FrontB

/-- Maximal cyclic runs of odd steps, counted by their trailing edges.  (An all-`true` word
has zero edges and one circuit; it is excluded by `0 < den` anyway.) -/
def circuits (v : List Bool) : ℕ := (v.zip (rot v)).countP (fun p => p.1 && !p.2)

/-- The word encodes a cycle of positive **integers**. -/
def IntegerCycle (v : List Bool) : Prop :=
  v ≠ [] ∧ 1 ≤ ones v ∧ 0 < den v ∧ den v ∣ (numer v : ℤ)

/-- The word encodes the trivial cycle `{1, 2}` (or a rotation/repetition of it): its
member `numer v / den v` is `1` or `2`.  Both residues are needed: the trace of the
trivial accelerated cycle rooted at `2` is `[false, true]` with `numer = 2`, `den = 1`,
a perfectly good `IntegerCycle` whose member is `2`, not `1`.  (With the member-is-`1`
definition `FrontB` would be *refutably false* on that very word, and the dictionary
`noNontrivialCycle_iff_frontB` would be false with it.) -/
def IsTrivial (v : List Bool) : Prop :=
  (numer v : ℤ) = den v ∨ (numer v : ℤ) = 2 * den v

/-- **Front B in word form**: every integral positive cycle is the trivial one. -/
def FrontB : Prop := ∀ v, IntegerCycle v → IsTrivial v

/-! ## Cited results (THEOREM-grade axioms) -/

/-- **Baker / Tijdeman**, cited: for any bound `C` only finitely many exponent pairs have
`|2^k − 3^x| ≤ C`.  This is the *closer* in every route that manages to bound the
denominator from above. -/
axiom baker_bounded_difference (C : ℕ) :
    {p : ℕ × ℕ | 1 ≤ p.2 ∧ ((2:ℤ) ^ p.1 - 3 ^ p.2).natAbs ≤ C}.Finite

/-! ## Thread 7 - integrality lattice / gcd over rotations.  **KILLED** ☠️

The hope: harvest extra divisibility by intersecting the conditions coming from all
rotations.  The reality: every rotation's numerator is a unit multiple of every other's
modulo the denominator, so there is only ever one condition. -/

/-- The Route-1 hope, stated so it can be refuted: some rotation satisfies the divisibility
while the base word does not. -/
def Route1_GcdHarvest : Prop :=
  ∃ v : List Bool, v ≠ [] ∧ 1 ≤ ones v ∧
    den v ∣ (numer (rot v) : ℤ) ∧ ¬ den v ∣ (numer v : ℤ)

/-- **Thread 7 is dead**, and this is the proof: `dvd_numer_rot_iff`. -/
theorem route1_gcdHarvest_false : ¬ Route1_GcdHarvest := by
  rintro ⟨v, hv, hx, h1, h2⟩
  exact h2 ((dvd_numer_rot_iff hv hx).mpr h1)

/-! ## Thread 1 - compression to boundedly many circuits.  **OPEN, ~55%** -/

/-- **The compression lemma** (ours, hence a `def`): a nontrivial integral cycle cannot have
arbitrarily many circuits.  Route 2's entire missing ingredient.
⚠️ `experiments/circuits3.py` shows numerics cannot guide this: `gcd(W,D)` is not a metric
on "nearness to being a cycle", so the statement must be attacked directly. -/
def Compression : Prop := ∃ C, ∀ v, IntegerCycle v → ¬ IsTrivial v → circuits v ≤ C

/-- The Simons-de Weger ladder completing at every fixed circuit count.  Their published
theorems cover specific small counts by computation; this is the *extrapolation*, so it is a
`def` and not an axiom. -/
def LadderCompletes : Prop := ∀ C v, IntegerCycle v → circuits v ≤ C → IsTrivial v

/-- **Route 2's wiring**, provable now: compression plus the ladder gives Front B. -/
theorem frontB_of_compression (h1 : Compression) (h2 : LadderCompletes) : FrontB := by
  intro v hv
  by_contra hnt
  obtain ⟨C, hC⟩ := h1
  exact hnt (h2 C v hv (hC v hv hnt))

/-! ## Thread 2 - bound the denominator from above.  **OPEN, ~12%**

The filter of `FRONT-B-ROUTES.md`, formalized: an *upper* bound on `|den|` closes the front
via Baker, whereas every Diophantine input bounds it from below and closes nothing. -/

/-- Some uniform bound on the denominator of a nontrivial integral cycle.  Knight (2026)
proves the special case `den = 1` for high cycles. -/
def BoundedDen : Prop := ∃ C, ∀ v, IntegerCycle v → ¬ IsTrivial v → (den v).natAbs ≤ C

/-- **The filter, as a theorem.**  Bounding the denominator above leaves only finitely many
exponent shapes - this is why an upper bound closes and a lower bound never can. -/
theorem finite_shapes_of_boundedDen (h : BoundedDen) :
    {p : ℕ × ℕ | ∃ v : List Bool, v.length = p.1 ∧ ones v = p.2 ∧
      IntegerCycle v ∧ ¬ IsTrivial v}.Finite := by
  obtain ⟨C, hC⟩ := h
  refine Set.Finite.subset (baker_bounded_difference C) ?_
  rintro ⟨k, x⟩ ⟨v, hk, hx, hcyc, hnt⟩
  refine ⟨by rw [← hx]; exact hcyc.2.1, ?_⟩
  have := hC v hcyc hnt
  rwa [den, hk, hx] at this

/-! ## Thread 4 - counting / equidistribution.  **KILLED as a method, ~2%** ☠️

The heuristic is favourable: in the band that can host large cycles the word entropy is
`H(log 2 / log 3) = 0.95`, so the expected count decays like `2^(−0.05k)`, and Baker's loss
on the denominator is only quasi-polynomial, so the Diophantine input this route needs
already exists.  What it yields is the statement below - and finiteness is not emptiness.
A counting argument with main term below `1` would need its error term below `1` too, i.e.
full cancellation in a sum of `2^(0.95k)` terms. -/

/-- What a successful counting argument would give: finitely many nontrivial integral
cycles.  **Not** what Front B asserts. -/
def CountingGivesFinite : Prop := {v : List Bool | IntegerCycle v ∧ ¬ IsTrivial v}.Finite

/-- The gap that kills the counting route, stated so it cannot be glossed over: finiteness
does not imply emptiness, and no amount of sharpening the count closes it. -/
def FinitenessIsNotEmptiness : Prop := CountingGivesFinite ∧ ¬ FrontB

/-! ## Thread 13 - the falsification harness.  **PROVED** ✅ -/

/-- **Every candidate Front B argument must fail on `ℤ`.**  If a proposed lemma about
positive cycles has a proof that never uses positivity, `exists_nontrivial_cycleZ` refutes
it.  Run new lemmas against `-1`, `-5`, `-17` before believing them. -/
theorem barrier_negative_cycles_exist : ∃ n : ℤ, n < 0 ∧ OnCycleZ n :=
  exists_nontrivial_cycleZ

/-! ## Thread 6 - abc.  **Assumed, and it is the WRONG HALF** ⚖️

`Assumed/ABC.lean` takes the abc conjecture as a CONJECTURE-grade axiom and derives what it
actually gives for a cycle: `2^k ≤ C · den²`, a **lower** bound on the denominator.  The
theorem below shows abc is one half of a scissors - paired with an *upper* bound it closes
the front immediately, and alone it closes nothing.

This settles the disputed line in `APPROACHES.md` ("an effective S-unit or abc-strength
input finishes cycles entirely"): as stated, it is an overclaim. -/

/-- **abc is one blade of the scissors.**  Its lower bound on `den`, together with any upper
bound, bounds the word length - so only finitely many shapes survive.  Neither blade cuts
alone, and every Diophantine input supplies the same blade abc does. -/
theorem length_bounded_of_abc_and_boundedDen (habc : AbcConjecture) (hbd : BoundedDen) :
    ∃ L : ℕ, ∀ v : List Bool, IntegerCycle v → ¬ IsTrivial v → v.length ≤ L := by
  obtain ⟨C, hCpos, hlow⟩ := den_lower_bound_of_abc habc
  obtain ⟨B, hB⟩ := hbd
  refine ⟨⌈C * (B : ℝ) ^ 2⌉₊, fun v hcyc hnt => ?_⟩
  have hden := hB v hcyc hnt
  have h1 : (2:ℝ) ^ v.length ≤ C * ((den v).natAbs : ℝ) ^ 2 :=
    hlow v hcyc.2.1 hcyc.2.2.1
  have h2 : ((den v).natAbs : ℝ) ≤ (B : ℝ) := by exact_mod_cast hden
  have h3 : (2:ℝ) ^ v.length ≤ C * (B : ℝ) ^ 2 := by
    refine le_trans h1 ?_
    have : ((den v).natAbs : ℝ) ^ 2 ≤ (B : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h2 2
    nlinarith [sq_nonneg ((den v).natAbs : ℝ)]
  have h4 : (v.length : ℝ) < (2:ℝ) ^ v.length := by
    have := Nat.lt_two_pow_self (n := v.length)
    exact_mod_cast this
  have h5 : (v.length : ℝ) ≤ (⌈C * (B : ℝ) ^ 2⌉₊ : ℝ) :=
    le_trans (le_of_lt (lt_of_lt_of_le h4 h3)) (Nat.le_ceil _)
  exact_mod_cast h5

/-! ## Thread 21 - Conway unsettleability.  **Aimed at the other front** 🎭

Conway, *On Unsettleable Arithmetical Problems*, Amer. Math. Monthly **120** (3), March 2013,
192-198.  What he actually does, separated carefully:

* **Proved**: an explicit 24-fraction Collatzian game (reduced to 7 fractions by John
  Rickard) has a starting number whose orbit never stops, and that fact is not provable from
  any given consistent axiom system.  The engine is his own 1972 universality result plus
  Gödel.  "Unsettleable" means unprovable *and* unrefutable from set theory, not merely PA.
* **Speculated**, in his words: "There is a slight chance that this problem itself is
  unsettleable - some very similar problems certainly are."  His candidate for the simplest
  unsettleable statement is not `3n+1` at all but the **amusical permutation**
  `2k ↦ 3k, 4k+1 ↦ 3k+1, 4k−1 ↦ 3k−1`, and the assertion that `8` lies on an infinite cycle.
* **His own hedge on `3n+1`** (Appendix 1): its probabilistic drift points *down*, unlike the
  amusical permutation, so "if this were provable, the conjecture would be settled by being
  provable", and he names the Hardy-Littlewood circle method as the slight hope - while
  adding "However, I don't really believe it."
* He coins **"probvious"** for probabilistically obvious, which is exactly the epistemic
  status of the entropy-margin count in `FRONT-B-ROUTES.md`.

**Why this front is different.**  Conway's pessimism targets *non-termination*, which is
`Π⁰₂` and has no finite certificate.  "No nontrivial cycle" is `Π⁰₁`: a counterexample is a
pair `(n, m)` that can be checked.  So a false Front B would be refutable in any
`Σ₁`-complete theory, and **unsettleable-and-false is impossible here** - if Front B were
unsettleable it would be *true*.  That asymmetry is the KB's
`arithmetical-hierarchy-independence-asymmetry` note; it does not rescue provability, but it
does mean Conway's argument is not evidence against *this* front. -/

/-- The refutation of Front B is a finite, checkable certificate - the formal shadow of its
being `Π⁰₁`.  Divergence admits no such statement, which is where Conway's pessimism bites. -/
instance frontB_refutation_decidable (n m : ℕ) :
    Decidable (step^[m] n = n ∧ n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) := by infer_instance

/-! ## Threads with no formal content yet

Stated as `def`s so the board is complete; none has been attacked here.

* **Thread 3, entropy-free ×2×3 rigidity (~8%)** - a classification of finite invariant sets
  of the joint action.  Needs `Rigidity/` vocabulary plus mathlib entropy, so it lives in
  Lane 1, not here.
* **Thread 17, sum-product / additive energy of a cycle's element set (~3%)** - the most
  literal "addition versus multiplication" framing on the board, and untried.
* **Thread 18, transducer / Cobham theory for the parity word (~3%)** - Lane 2's seed.
* **Thread 20, transfer the carry-free function-field proof (~2%)** - "carries die" is why
  the function-field analogue is solved.
* **Thread 21, independence from PA (~1%)** - `¬∃` nontrivial cycle is `Π₁`, so not absurd;
  unstatable here without a metatheory.
-/

end CollatzMoonshot.FrontB
