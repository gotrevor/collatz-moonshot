/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.FrontA.Paradoxical

/-!
# Assumed: Rozier--Terracol 2026, Theorem 3.2 (paradoxical segments from infinite stopping time)

Tier: **THEOREM-grade** — published, peer-reviewed (Olivier Rozier and Claude Terracol,
*Paradoxical behavior in Collatz sequences*, Discrete Mathematics 349 (2026), 115167;
arXiv:2502.00948v5).  Represented here by a narrow, provenance-documented axiom, per the repo's
Assumed policy: a published theorem may stand as an axiom rather than be re-formalized.

## What the axiom says (the paper's actual statement)

An integer `n ≥ 2` whose **shortcut stopping time is infinite** — `tstep^[j] n ≥ n` for every
`j` — produces **infinitely many paradoxical segments** (Theorem 3.2; the construction uses the
starts `2^k n` and infinitely many left approximations `3^a / 2^b < 1` of `1`).  The
`Paradoxical` predicate is exactly the paper's definition rendered in repository notation
(`CollatzMoonshot/FrontA/Paradoxical.lean`).  `NoDivergentOrbit` is **not** packaged into the
axiom — the Front-A consumption is derived separately below.

## The Front-A wiring

`finite_acyclicParadoxical_imp_noDivergent` is the intended derived implication
`FiniteAcyclicParadoxical → NoDivergentOrbit`.  It routes through one disclosed intermediate,
`diverges_imp_infinite_acyclicParadoxical`, which is the Front-A *specialization* the project
doc flags as owed: a divergent standard orbit is nonrepeating, has a tail value of infinite
shortcut stopping time, and its constructed segments cannot close cyclically, so they are
*acyclic* — this last step is a derived specialization of the paper, not its verbatim
statement, and is left as a scoped `sorry` (standard/shortcut bridge + acyclicity).

**Strength caveat (mandatory).** `FiniteAcyclicParadoxical` is a *sufficient* hypothesis for
Front A, and its own truth (global finiteness of paradoxical segments, Rozier--Terracol
Conjecture 6.1) is **stronger than the full Collatz conjecture**.  This wiring is therefore a
conditional reduction, not an easier route; it is BASELINE Front-A plumbing, and the novel
content of the project lives in the discovery lemmas (`headBlock_not_acyclicParadoxical`, the
`≥3` odd-blocks finding), not here.
-/

namespace CollatzMoonshot

open CollatzMoonshot.FrontB CollatzMoonshot.FrontA

/-- `n` has **infinite shortcut stopping time**: its accelerated orbit never drops below `n`
(`tstep^[j] n ≥ n` for all `j`).  This is Rozier--Terracol's hypothesis for Theorem 3.2. -/
def InfiniteStoppingTime (n : ℕ) : Prop := ∀ j, n ≤ tstep^[j] n

/-- There are only finitely many acyclic paradoxical segments (pairs `(start, length)`).  This
is the Front-A sufficient condition; its truth is Rozier--Terracol Conjecture 6.1, stronger
than Collatz. -/
def FiniteAcyclicParadoxical : Prop :=
  {p : ℕ × ℕ | AcyclicParadoxical p.1 p.2}.Finite

namespace Assumed

/-- **[ASSUMED — THEOREM-grade]** Rozier--Terracol 2026, Theorem 3.2.  An integer `n ≥ 2` of
infinite shortcut stopping time yields infinitely many paradoxical segments.

Provenance: Rozier & Terracol, *Paradoxical behavior in Collatz sequences*, Discrete
Mathematics 349 (2026), 115167 (arXiv:2502.00948v5), Theorem 3.2 and Corollary 3.3.  Stated in
repository notation; the paper's `Paradoxical` definition matches `FrontA.Paradoxical`. -/
axiom rozier_terracol_3_2 (n : ℕ) (h2 : 2 ≤ n) (hstop : InfiniteStoppingTime n) :
    {p : ℕ × ℕ | Paradoxical p.1 p.2}.Infinite

end Assumed

/-- **Front-A specialization (owed).**  A divergent standard-step orbit yields infinitely many
*acyclic* paradoxical segments.  This combines `Assumed.rozier_terracol_3_2` with (i) the
standard/shortcut iterate bridge that turns divergence into a tail value of infinite shortcut
stopping time, and (ii) the observation that a divergent (hence acyclic) orbit's constructed
segments cannot close cyclically.  Disclosed `sorry`: this derived specialization is the scoped
arithmetic bridge, not the cited axiom. -/
theorem diverges_imp_infinite_acyclicParadoxical (n : ℕ) (hn : 1 ≤ n) (hdiv : Diverges n) :
    {p : ℕ × ℕ | AcyclicParadoxical p.1 p.2}.Infinite := by
  sorry

/-- **The Front-A consumption theorem**: only finitely many acyclic paradoxical segments
implies no divergent orbit.  (Conditional reduction — see the strength caveat in the module
docstring.) -/
theorem finite_acyclicParadoxical_imp_noDivergent
    (hfin : FiniteAcyclicParadoxical) : NoDivergentOrbit := by
  intro n hn hdiv
  exact (diverges_imp_infinite_acyclicParadoxical n hn hdiv).not_finite hfin

end CollatzMoonshot
