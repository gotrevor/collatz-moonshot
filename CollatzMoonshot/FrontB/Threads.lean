/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CollatzMoonshot.FrontB.Words
import CollatzMoonshot.FrontB.Powers
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
`IsTrivial`: see its docstring in `Words.lean`.)

🧨 **Degeneracy repair** (2026-08-23): the boards' original `Compression` and `BoundedDen`
quantified over ALL nontrivial integral words - and word **powers** (`Powers.lean`) make
each of them *equivalent to `FrontB` itself*, i.e. zero reduction (`wpow v j` keeps the
member value while `circuits` telescopes and `den` explodes).  Both threads now quantify
over `Primitive` words, which is what an `m`-cycle in the literature is; the naive
statements stay below as killed threads with their degeneracy theorems.
-/

namespace CollatzMoonshot.FrontB

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

/-! ## Thread 1 - compression to boundedly many circuits.  **OPEN, ~55%**

⚠️ **The original statement of this thread was killed on 2026-08-23** - not because it is
false, but because it is `FrontB` in disguise.  `NaiveCompression` below quantifies over
all nontrivial integral words; one counterexample cycle `v` manufactures the family
`wpow v j` with `circuits = j * circuits v → ∞`, so bounding circuits over all words IS
asserting no counterexample exists.  Anyone attacking it is attacking Front B with zero
reduction.  The honest target - what an "`m`-cycle" in Simons-de Weger/Hercher actually
is - quantifies over `Primitive` words. -/

/-- The naive compression statement, kept so its degeneracy is on the record.  **Do not
attack this**: `naiveCompression_iff_frontB` shows it is Front B verbatim. -/
def NaiveCompression : Prop := ∃ C, ∀ v, IntegerCycle v → ¬ IsTrivial v → circuits v ≤ C

/-- **The degeneracy, as a theorem** (axiom-free): the naive bound is *equivalent* to
Front B.  Forward: a counterexample's powers have unboundedly many circuits.  Backward:
no counterexamples, so any bound works vacuously.  A statement equivalent to the target
is not a reduction of it. -/
theorem naiveCompression_iff_frontB : NaiveCompression ↔ FrontB := by
  constructor
  · rintro ⟨C, hC⟩ v hv
    by_contra hnt
    have hc1 : 1 ≤ circuits v := circuits_pos_of_integerCycle hv
    have hdv : 0 < den v := hv.2.2.1
    obtain ⟨b, t, rfl⟩ : ∃ b t, v = b :: t := by
      cases v with
      | nil => exact absurd rfl hv.1
      | cons b t => exact ⟨b, t, rfl⟩
    have hIC : IntegerCycle (wpow (b :: t) (C + 1)) :=
      (integerCycle_wpow_iff (by omega)).mpr hv
    have hNT : ¬ IsTrivial (wpow (b :: t) (C + 1)) := fun h =>
      hnt ((isTrivial_wpow_iff (ne_of_gt hdv) (by omega)).mp h)
    have hle := hC _ hIC hNT
    rw [circuits_wpow] at hle
    nlinarith [hle, hc1]
  · intro h
    exact ⟨0, fun v hv hnt => absurd (h v hv) hnt⟩

/-- **The compression lemma** (ours, hence a `def`): a nontrivial **primitive** integral
cycle cannot have arbitrarily many circuits.  Route 2's entire missing ingredient, now
stated with the primitivity the literature's "`m`-cycle" always meant.
⚠️ `experiments/circuits3.py` shows numerics cannot guide this: `gcd(W,D)` is not a metric
on "nearness to being a cycle", so the statement must be attacked directly.
🧪 Negative-harness note: this statement is compatible with the negative cycles' existence
(`−17`'s word is primitive with 2 circuits) - the sign-asymmetry of Front B must be
consumed by the *ladder*, not by compression. -/
def Compression : Prop :=
  ∃ C, ∀ v, Primitive v → IntegerCycle v → ¬ IsTrivial v → circuits v ≤ C

/-- The Simons-de Weger ladder completing at every fixed circuit count.  Their published
theorems cover specific small counts by computation; this is the *extrapolation*, so it is
a `def` and not an axiom.  (`hercher_min_circuit_count` below IS the proved part of the
ladder: rungs `≤ 91` hold, vacuously - no primitive nontrivial cycle lives there.) -/
def LadderCompletes : Prop :=
  ∀ C v, Primitive v → IntegerCycle v → circuits v ≤ C → IsTrivial v

/-- **Route 2's wiring**, provable now: compression plus the ladder gives Front B.  The
decomposition `exists_primitive_root` is what lets the primitive-only hypotheses cover
every word. -/
theorem frontB_of_compression (h1 : Compression) (h2 : LadderCompletes) : FrontB := by
  intro v hv
  by_contra hnt
  obtain ⟨C, hC⟩ := h1
  obtain ⟨u, j, hu, hj, rfl⟩ := exists_primitive_root v hv.1
  have hICu : IntegerCycle u := (integerCycle_wpow_iff hj).mp hv
  have hdu : 0 < den u := hICu.2.2.1
  have hNTu : ¬ IsTrivial u := fun h =>
    hnt ((isTrivial_wpow_iff (ne_of_gt hdu) hj).mpr h)
  exact hNTu (h2 C u hu hICu (hC u hu hICu hNTu))

/-- **[ASSUMED - published theorem]** No nontrivial primitive integral cycle has fewer
than 92 circuits.

Provenance: Hercher 2023 (*J. Integer Seq.* **26**, Article 23.3.5; verified firsthand
2026-08-22, summary in `papers/`): "there are no `m`-cycles for `m ≤ 91`".  His *m*
(local minima = maximal odd-runs of a genuine, single-traversal cycle of the shortened
map) is exactly `circuits v` on a `Primitive` word under the convention here.  Engine:
continued-fraction denominators of `log₂ 3` + reciprocal sums + the verification bound -
**no transcendence input** (method-checked against the full PDF).  The ladder this crowns:
Simons-de Weger 2005 (`m ≤ 68`) → 2010 (`76`) → Hercher 2018 (`77`) → 2023 (`91`). -/
axiom hercher_min_circuit_count :
    ∀ v, Primitive v → IntegerCycle v → ¬ IsTrivial v → 92 ≤ circuits v

/-- **The sharpened target** (2026-08-23): with Hercher's floor adopted, compression with
any constant `≤ 91` closes Front B outright - no ladder extrapolation needed.  This is
Route 2's whole remaining content in one sentence: *show a primitive nontrivial integral
cycle cannot have 92 circuits' worth of structure*. -/
theorem frontB_of_compression_le_91
    (h : ∀ v, Primitive v → IntegerCycle v → ¬ IsTrivial v → circuits v ≤ 91) :
    FrontB := by
  intro v hv
  by_contra hnt
  obtain ⟨u, j, hu, hj, rfl⟩ := exists_primitive_root v hv.1
  have hICu : IntegerCycle u := (integerCycle_wpow_iff hj).mp hv
  have hdu : 0 < den u := hICu.2.2.1
  have hNTu : ¬ IsTrivial u := fun h' =>
    hnt ((isTrivial_wpow_iff (ne_of_gt hdu) hj).mpr h')
  have h92 := hercher_min_circuit_count u hu hICu hNTu
  have h91 := h u hu hICu hNTu
  omega

/-! ## Thread 2 - bound the denominator from above.  **OPEN, ~12%**

The filter of `FRONT-B-ROUTES.md`, formalized: an *upper* bound on `|den|` closes the front
via Baker, whereas every Diophantine input bounds it from below and closes nothing.

⚠️ Same 2026-08-23 degeneracy repair as Thread 1: over all words, `den (wpow v j)`
explodes (`le_den_wpow`), so the naive bound was Front B in disguise too. -/

/-- The naive statement, kept for the record.  **Do not attack this**:
`naiveBoundedDen_iff_frontB` shows it is Front B verbatim. -/
def NaiveBoundedDen : Prop :=
  ∃ C, ∀ v, IntegerCycle v → ¬ IsTrivial v → (den v).natAbs ≤ C

/-- The degeneracy theorem for Thread 2 (axiom-free): a counterexample's powers have
unboundedly large denominators, so the naive bound is *equivalent* to Front B. -/
theorem naiveBoundedDen_iff_frontB : NaiveBoundedDen ↔ FrontB := by
  constructor
  · rintro ⟨C, hC⟩ v hv
    by_contra hnt
    have hdv : 0 < den v := hv.2.2.1
    have hIC : IntegerCycle (wpow v (C + 1)) :=
      (integerCycle_wpow_iff (by omega)).mpr hv
    have hNT : ¬ IsTrivial (wpow v (C + 1)) := fun h =>
      hnt ((isTrivial_wpow_iff (ne_of_gt hdv) (by omega)).mp h)
    have hbound := hC _ hIC hNT
    have hgrow : ((C : ℤ) + 1) ≤ den (wpow v (C + 1)) := by
      have := le_den_wpow (v := v) (by omega) (C + 1)
      push_cast at this
      linarith
    have h3 : (den (wpow v (C + 1)) : ℤ) ≤ (C : ℤ) :=
      le_trans Int.le_natAbs (by exact_mod_cast hbound)
    linarith
  · intro h
    exact ⟨0, fun v hv hnt => absurd (h v hv) hnt⟩

/-- Some uniform bound on the denominator of a nontrivial **primitive** integral cycle.
Knight (2026) proves the special case `den = 1` for high cycles. -/
def BoundedDen : Prop :=
  ∃ C, ∀ v, Primitive v → IntegerCycle v → ¬ IsTrivial v → (den v).natAbs ≤ C

/-- **The filter, as a theorem.**  Bounding the denominator above leaves only finitely many
exponent shapes - this is why an upper bound closes and a lower bound never can. -/
theorem finite_shapes_of_boundedDen (h : BoundedDen) :
    {p : ℕ × ℕ | ∃ v : List Bool, v.length = p.1 ∧ ones v = p.2 ∧
      Primitive v ∧ IntegerCycle v ∧ ¬ IsTrivial v}.Finite := by
  obtain ⟨C, hC⟩ := h
  refine Set.Finite.subset (baker_bounded_difference C) ?_
  rintro ⟨k, x⟩ ⟨v, hk, hx, hprim, hcyc, hnt⟩
  refine ⟨by rw [← hx]; exact hcyc.2.1, ?_⟩
  have := hC v hprim hcyc hnt
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
alone, and every Diophantine input supplies the same blade abc does.  (Primitive words
only, after the 2026-08-23 repair - powers of course have unbounded length.) -/
theorem length_bounded_of_abc_and_boundedDen (habc : AbcConjecture) (hbd : BoundedDen) :
    ∃ L : ℕ, ∀ v : List Bool, Primitive v → IntegerCycle v → ¬ IsTrivial v →
      v.length ≤ L := by
  obtain ⟨C, hCpos, hlow⟩ := den_lower_bound_of_abc habc
  obtain ⟨B, hB⟩ := hbd
  refine ⟨⌈C * (B : ℝ) ^ 2⌉₊, fun v hprim hcyc hnt => ?_⟩
  have hden := hB v hprim hcyc hnt
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
