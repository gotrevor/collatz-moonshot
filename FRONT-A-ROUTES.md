# Front A route map: how divergence could actually be excluded 🧭

> 🧾 **The board is also Lean.**  `CollatzMoonshot/FrontA/Threads.lean` states the
> principal interfaces below.  Proposed new mathematics is a `def`; proved wiring and
> falsification facts are theorems.

*Companion to `FRONT-B-ROUTES.md`.  Front B asks whether a finite cycle can exist.  Front A
asks whether a positive orbit can be unbounded.  The two problems consume different evidence
and should keep different proof interfaces.*

## The exact drift currency

For the unaccelerated map, let `a(n,k)` and `b(n,k)` be the odd and even steps in the first
`k` iterates.  Above a floor `N`, `Rigidity/Drift.lean` proves

```
T^k(n) · 2^b ≤ n · (3 + 1/N)^a.
```

Thus a block descends whenever its odd-step frequency is below

```
q(N) := log 2 / log(2 · (3 + 1/N)).
```

The information-free threshold is `q(1) = 1/3`; a divergent orbit supplies arbitrarily high
eventual floors, and `q(N) ↑ q* := log 2 / log 6 ≈ 0.38685`.  In the shortcut-map convention
this is the familiar odd-step threshold `log 2 / log 3 ≈ 0.63093`.

`exists_floor_of_diverges` proves something stronger than mere `limsup = ∞`: a divergent
Collatz orbit eventually stays above every fixed height.  A repeat would make the orbit
periodic, so divergence makes the orbit injective, and an injective sequence of naturals can
visit a finite low interval only finitely often.

## Three filters 🚧

### 1. Pure ℤ₂ dynamics is blind

The 2-adic Collatz map is conjugate to the full one-sided shift.  Its invariant measures are
therefore abundant, including measures with the wrong parity frequency.  The proved
`-1 ↔ -2` 2-adic cycle has odd mass `1/2`, above `q*`.  Any unconditioned assertion about all
`T2`-invariant measures is false.

The arithmetic input must appear either as support on the closure of an actual positive
orbit, as an empirical-limit condition, or through an explicit archimedean/carry coupling.

### 2. Many divergent integers do not contradict Tao 2019

Tao's theorem controls `orbitMin n`, not eventual behavior.  If a large backward tree enters
one fixed divergent seed `d`, then every member `m` of that tree has

```
orbitMin(m) ≤ d.
```

For every `f(m) → ∞`, all sufficiently large members are therefore **Tao-good**:
`orbitMin(m) < f(m)`.  Even positive logarithmic density of divergent starting values would
not contradict the theorem if they all fall into one small divergent core.

The Lean witness is `mem_taoGood_of_reachesValue`.  This kills **raw backward-density
amplification** as a route.

### 3. Front A must not silently prove Front B

`DescentAll` is equivalent to the full Collatz conjecture.  It is a valid target, but it is not
a divergence-only consumption form: the minimum of a hypothetical nontrivial cycle cannot
descend.

The correctly scoped condition is

```
∀ n, Diverges n → ∃ k, T^k(n) < n.
```

`noDivergent_of_descends_if_diverges` proves that this already kills divergence by strong
induction.  A finite-certificate version is **repeat or descend**: every start either has two
equal iterates or eventually falls below itself.  The repeat branch deliberately permits
bounded nontrivial cycles; `noDivergent_of_repeatOrDescend` shows the disjunction closes only
Front A.  The converse is finite pigeonhole, so `repeatOrDescend_iff_noDivergent` proves this
certificate target is exactly Front A, not an accidental strengthening.

## Route A1 - Orbit-limit parity rigidity 🏔️

**Current lead.**  Average a positive orbit in compact `ℤ₂`, obtain empirical limit measures,
and force their odd mass below `q*`.  Clopen parity transports the measure statement back to
finite odd-step frequencies, while the free-floor theorem converts those frequencies into
archimedean descent.

The current pin is `ParityRigidityW1'`:

```
every invariant probability supported on a positive orbit closure
has μ(odd) < q*.
```

### Strength audit

* **W1 is not Front-A-only.**  W1 says every such measure charges `{1,2,4}`.  The uniform
  invariant measure on a hypothetical positive nontrivial cycle would violate W1, so W1
  already implies `NoNontrivialCycle`.  It does not implement the approach map's promised
  division in which rigidity permits atomic measures and arithmetic classifies them.
* **W1' has the right strength.**  Every positive cycle, trivial or not, has odd frequency
  below `q*`, because `3^a < 2^b`.  Conversely, if Front A holds then every positive orbit is
  eventually periodic and every invariant probability on its finite orbit closure is the
  uniform cycle measure.  After the standard finite-measure plumbing, one should therefore
  have the calibration theorem

  ```
  ParityRigidityW1' ↔ NoDivergentOrbit.
  ```

  This is useful: it says W1' is an exact change of language into a setting where rigidity
  tools might act.  It is not by itself a reduction in logical strength.
* **The current quantifier may be stronger than consumption needs.**  An orbit closure can
  support invariant measures that the orbit never samples statistically.  The board pins
  `EmpiricalParityRigidity`, asking only for a subsequential empirical odd-frequency limit
  below `q*`.  Proving that this weaker pin closes Front A requires finite-shift invariance and
  a tail-minimum/free-floor argument; this is now an explicit open thread rather than hidden
  inside W1'.

**Missing new mathematics**: an arithmetic intertwining theorem that makes the positive-orbit
conditioning visible to ×2×3 rigidity, or an entropy-generation theorem for empirical orbit
limits.  Krylov-Bogolyubov and Portmanteau are plumbing, not the hard step.

## Route A2 - Floor-preserving saturation of Tao's theorem 🌊

Combine the forward statistical theorem with density of backward Collatz trees, but use
**moving high-tail seeds**, not one fixed seed.  `exists_floor_of_diverges` gives, from one
counterexample, tails whose entire future lies above any prescribed `N`.  The required
saturation theorem must amplify those tails while ensuring the backward path does not dip
below the scale being protected.

A strong quantitative target is

```
∃ n, Diverges n
  → ∃ f → ∞,
      upperLogDensity {m | orbitMin(m) ≥ f(m)} > 0.
```

This contradicts Tao 2019 immediately.  `FloorPreservingSaturation` in the Lean board pins the
minimal output form: it produces an `f → ∞` for which Tao's good set fails to have logarithmic
density one, and `noDivergent_of_floorPreservingSaturation` performs the one-line consumption.

**Assets already available**: Tao 2019 forward mixing, Tao 2020 backward equidistribution, and
Krasikov-Lagarias-type backward-tree lower bounds.

**Missing new mathematics**: quantitative control of the *minimum along the backward branch*.
Counting preimages without this height condition is now ruled out, not merely viewed as weak.

## Route A3 - Symbolic/carry certificates 🤖

The Bernstein-Lagarias conjugacy turns the parity itinerary into a shift sequence, while
multiplication by `3` is a base-2 transducer.  A successful theorem has to distinguish the
itineraries of ordinary positive integers from the unrestricted 2-adic full shift.  Carries
are the concrete coupling between those two worlds.

There are two plausible output forms:

1. a Cobham/transducer rigidity theorem showing that a positive-integer itinerary cannot
   sustain the required near-critical drift indefinitely;
2. a machine-found, kernel-checked **repeat-or-descend certificate**, possibly using weighted
   automata, matrix interpretations, or richer parity/carry features.

The second output form is deliberately weaker than a universal termination certificate.  It
allows the repeat alternative and therefore does not claim to settle cycles.  This makes it a
clean target for Front A and a better search space than `DescentAll` when the two-proof
architecture is being respected.

Transfer-operator/spectral methods from `APPROACHES.md` fit here as an analytic certificate
variant: the desired spectral inequality must ultimately imply either empirical parity
rigidity or repeat-or-descend.

## Current priority order

1. **Orbit-limit parity rigidity**, but work with the weakest empirical pin that the drift
   consumption actually needs; keep the all-supported-measures W1' as the stronger target.
2. **Floor-preserving saturation**, beginning with inequalities for backward branches of the
   high-floor tails supplied by a hypothetical divergent orbit.
3. **Repeat-or-descend certificates**, using the existing carry/transducer infrastructure and
   treating a repeat as a permitted Front-B handoff rather than certificate failure.

No route is close.  The board's immediate value is negative and architectural: it prevents
raw density amplification, pure 2-adic measure claims, and universal-descent requirements
from being mistaken for correctly scoped Front-A progress.
