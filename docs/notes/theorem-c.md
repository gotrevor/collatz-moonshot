# Theorem C: orbit questions for {2,3}-slope RCWA permutations are undecidable

**Abstract.**  A permutation `σ` of `ℤ` is *residue-class-wise affine* (RCWA) if for some modulus
`m` it acts on each residue class mod `m` by one affine map `n ↦ (a n + b) / c`.  Collatz's
permutation `U(2n) = 3n`, `U(4n+1) = 3n+1`, `U(4n+3) = 3n+2` is one, with slopes `3/2` and
`3/4`, which generate the group `2^ℤ 3^ℤ` of slopes.  We prove in Lean that, already for RCWA
permutations of `ℤ` with every slope in `2^ℤ 3^ℤ`, the basic orbit questions are undecidable.
Whether two given integers lie in one cycle is not computable.  There is a computable family
`e ↦ σ_e` such that `σ_e` has one orbit if the `e`-th partial recursive function is total and
infinitely many orbits otherwise.  So "`σ` has one orbit" is neither recursively enumerable nor
co-recursively enumerable, and "`σ` has finitely many orbits" is not computable.  The only
computability input is Mathlib's halting problem.  The result is about the class, and it says
nothing about `U` itself (§6).

All results are linked at commit [`3eb4643`][commit].  Every theorem below checks with
`#print axioms` against the standard three (`propext`, `Classical.choice`, `Quot.sound`),
verified 2026-10-16.  None takes a hypothesis.

## 1. Statements

A table ([`RcwaTable`][table]) is a modulus and one affine piece per residue class; it is
*exact* ([`Exact`][exact]) when every piece maps its class into `ℤ` with slope in `2^ℤ 3^ℤ`.
For an exact table `T` whose map `T.eval` is a bijection, `Equiv.ofBijective T.eval` is the
permutation.

* **Same-orbit** ([`not_computable_sameCycle'`][sc]): no computable `g : RcwaTable × ℤ × ℤ →
  Bool` decides, on exact bijective tables, whether `a` and `b` lie in one cycle.
* **Orbit count, Theorem C(1)** ([`orbit_count_family'`][ocf]): there is a computable
  `T : ℕ → RcwaTable`, each `T e` exact with bijective map, whose permutation has one orbit iff
  `φ_e` is total, and infinitely many orbits otherwise.
* **Arithmetic strength** ([`oneOrbit_not_re'`][nre], [`oneOrbit_not_coRE'`][ncore]): neither
  "one orbit" nor "more than one orbit" is an r.e. property of exact bijective tables.
* **Decidability** ([`not_computable_oneOrbit'`][nco], [`not_computable_finiteOrbits'`][ncf]).
* **Machine form** ([`exists_table_iff_mortal`][etm]): for every deterministic finite counter
  machine `U` there is an exact bijective table with one orbit if `U` halts from every
  configuration and infinitely many orbits otherwise.

## 2. The engine: a counter machine inside `ℤ` (Lemma P)

Fix `j ≥ 1` and `N = 4·5^{j−1}`, so `2^N ≡ 3^N ≡ 1 (mod 5^j)`.  On the *engine zone*, `n` stores a
machine configuration: the state is the discrete logarithm of `n mod 5^j` to base `3` (the
*phase*), and the two counters are `⌊v₂(n)/N⌋` and `⌊(v₃(n) − phase)/N⌋`.  The rest (the
remainders of the valuations and the part of `n` prime to `6`) is *junk*.  One machine rule is one
linear piece `n ↦ n · 2^{Nδ₁} 3^{Nδ₂ + s' − s}`: it moves the state to `s'`, the counters by
`(δ₁, δ₂)`, and leaves the junk alone ([`scale_spec`][scale]).  The zero tests are residue
conditions.  So the engine is the machine times the identity on the junk, with every slope in
`2^ℤ 3^ℤ`, and every machine configuration occurs with infinitely many junk values.

## 3. Completion: orbits are cut-free runs of a highway

A reversible machine's configuration graph has in- and out-degree at most one.  Sinks are sent
back to sources through a *highway* (a copy of `ℤ` threaded through the sources), which completes
the partial injection to a permutation.  Under two conditions, no bi-infinite run (H1) and every
finite run from a source ends at its paired sink (H2), the orbits are the maximal runs of the
highway between *cuts*, the sources with an infinite forward run: `#orbits = 1 + #cuts`
([`card_orbits`][co]).  Junk makes each cut appear infinitely often, so the count is `1` or `∞`.
A source `c` and its highway successor share a cycle iff the machine halts from `c`
([`sameCycle_enc_iff`][sce]).  The machine side needs a guarded-rule 2-counter machine that is
reversible and satisfies (H1) and (H2) on **every** configuration ([`Valid`][valid]).

## 4. Valid machines from Mathlib's halting problem

The machines come from a chain of compilations, each proved in Lean on all configurations.

1. **A fixed undecidable machine** ([`undecidableCM`][ucm]).  Mathlib compiles partial recursive
   codes to a 4-stack machine (`Turing.PartrecToTM2`).  Each stack becomes a base-5 numeral in one
   counter, giving one fixed counter machine, in Morita's quadruple format (Morita, *Theory of
   Reversible Computing*, Springer 2017, §9.2), whose halting is not computable as the input varies.
2. **History** ([`histWrap`][hw]), after Morita's Lemma 9.3: a history counter makes the machine
   reversible.
3. **Two counters** ([`godel`][gd]), after Morita's Lemma 9.7: the counters are packed as
   `J · ∏ pᵢ^{vᵢ}` in one counter, with a scratch counter.
4. **Doubling** ([`double`][db]), after Kari and Ollinger (MFCS 2008, Thm 3): run forward on one
   copy of the states, turn around where the machine is stuck, and retrace on a second copy.  This
   gives (H2) and the sink-to-source pairing.

Morita's lemmas are stated for runs from encoded inputs.  `Valid` needs every configuration,
including the junk ones the encodings never produce, and three changes to the constructions carry
that.  For the second and third, a computer check of the variant without the change finds the
failure.

* The history counter records **every** step (`hist ↦ K · hist + label`), not one bit per
  irreversible merge, so it rises along every boundary-to-boundary run from any configuration.
* Merges are separated by a **re-test** of the scratch counter, so every merge in the wrapper is a
  pair of complementary tests (Morita's syntactic reversibility).
* Every boundary state of the 2-counter compile is **guarded** by `x ≥ 1, y = 0`.  Without the
  guard, the `x = 0` junk configurations cycle.

With these, the mortality of the reverse machine follows from a loop condition (every loop off the
boundary moves some counter up and some down) and Dickson's lemma
([`reverse_immortal_iff_macro`][rim]); (H1) follows.  This gives
[`haltingUndecidable`][hu], and with §3, same-orbit.

## 5. The orbit count: a restart machine

A fixed machine gives a fixed permutation, so its orbit count is a constant; the orbit count needs
a computable family.  A *restart machine* ([`mortal_iff_total`][mit]) runs a universal machine on
`[2^x − 1, e]`, which halts iff `φ_e` halts on `0, …, 2^x − 1`.  Each simulated step costs one
token of a budget.  When the budget is spent, the machine clears its counters, rebuilds an honest
input, and restarts with the budget one larger.  From any configuration, junk included, one round
reaches an honest restart, and from then on the budget grows without bound.  So the machine halts
from every configuration iff `φ_e` is total.  Here `e` enters only as the length of a chain of
increments glued in after the history wrapper, and the 2-counter compile is local (each compiled
rule comes from one source rule), so the numbered machine is computable in `e`
([`totalityFamily`][tf]).  Mortality transfers through the compile in both directions, again on
all configurations ([`exists_table_iff_mortal`][etm]).  Totality is neither r.e. nor co-r.e.,
from Mathlib's halting problem, which gives §1.

## 6. What this does and does not say

The construction needs pieces that move the 2-adic and 3-adic valuations in both directions.
`U`'s slopes `3^a / 2^b` with `a, b ≥ 0` do not, so Theorem C says nothing about `U`'s own orbits.
It says that the orbit questions for this slope class have no uniform decision method, so an
argument about `U` has to use something particular to `U`.  The same shape is familiar from
generalized Collatz maps (Conway, 1972; Kurtz and Simon, 2007), which are RCWA maps but not
permutations.

[commit]: https://github.com/gotrevor/collatz-moonshot/tree/3eb4643
[table]: https://github.com/gotrevor/collatz-moonshot/blob/3eb4643/CollatzMoonshot/RcwaSameOrbit.lean#L60
[exact]: https://github.com/gotrevor/collatz-moonshot/blob/3eb4643/CollatzMoonshot/RcwaSameOrbit.lean#L78
[sce]: https://github.com/gotrevor/collatz-moonshot/blob/3eb4643/CollatzMoonshot/RcwaSameOrbit.lean#L1519
[valid]: https://github.com/gotrevor/collatz-moonshot/blob/3eb4643/CollatzMoonshot/RcwaSameOrbit.lean#L369
[scale]: https://github.com/gotrevor/collatz-moonshot/blob/3eb4643/CollatzMoonshot/RcwaEngineGen.lean#L385
[co]: https://github.com/gotrevor/collatz-moonshot/blob/3eb4643/CollatzMoonshot/RcwaMachine.lean#L434
[rim]: https://github.com/gotrevor/collatz-moonshot/blob/3eb4643/CollatzMoonshot/RcwaMachine.lean#L674
[ucm]: https://github.com/gotrevor/collatz-moonshot/blob/3eb4643/CollatzMoonshot/CounterMachineUniversal.lean#L962
[hw]: https://github.com/gotrevor/collatz-moonshot/blob/3eb4643/CollatzMoonshot/RcwaHalting.lean#L271
[gd]: https://github.com/gotrevor/collatz-moonshot/blob/3eb4643/CollatzMoonshot/RcwaHalting.lean#L785
[db]: https://github.com/gotrevor/collatz-moonshot/blob/3eb4643/CollatzMoonshot/RcwaHalting.lean#L1902
[hu]: https://github.com/gotrevor/collatz-moonshot/blob/3eb4643/CollatzMoonshot/RcwaHalting.lean#L2510
[sc]: https://github.com/gotrevor/collatz-moonshot/blob/3eb4643/CollatzMoonshot/RcwaHalting.lean#L2515
[etm]: https://github.com/gotrevor/collatz-moonshot/blob/3eb4643/CollatzMoonshot/RcwaOrbitCount.lean#L459
[mit]: https://github.com/gotrevor/collatz-moonshot/blob/3eb4643/CollatzMoonshot/RcwaTotalityRestart.lean#L1133
[tf]: https://github.com/gotrevor/collatz-moonshot/blob/3eb4643/CollatzMoonshot/RcwaTotality.lean#L56
[ocf]: https://github.com/gotrevor/collatz-moonshot/blob/3eb4643/CollatzMoonshot/RcwaTotality.lean#L92
[nre]: https://github.com/gotrevor/collatz-moonshot/blob/3eb4643/CollatzMoonshot/RcwaTotality.lean#L100
[ncore]: https://github.com/gotrevor/collatz-moonshot/blob/3eb4643/CollatzMoonshot/RcwaTotality.lean#L107
[nco]: https://github.com/gotrevor/collatz-moonshot/blob/3eb4643/CollatzMoonshot/RcwaTotality.lean#L114
[ncf]: https://github.com/gotrevor/collatz-moonshot/blob/3eb4643/CollatzMoonshot/RcwaTotality.lean#L121
