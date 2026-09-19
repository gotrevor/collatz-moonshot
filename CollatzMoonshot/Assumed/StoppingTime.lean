/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.FrontA.LogTwoThreeDigits

/-!
# Assumed: the coefficient-stopping-time verification frontier

Tier: THEOREM-grade (published computation; not a formal proof anywhere).

Terras's coefficient stopping-time conjecture (`FirstCrossing.StoppingCorrect`) is verified
by Rozier and Terracol for every start up to `2.8 · 10¹⁹`.  The first-crossing rungs take that
range as the explicit `def` hypothesis `FirstCrossing.CSTVerified`; this file adopts it as a
named axiom, so the rungs can be stated unconditionally with the assumption visible in
`#print axioms`.  Per the repository's doctrine, the `def` form stays the primary statement and
this axiom is only a citation with a one-line upgrade path (a future formal verification would
replace it by a theorem of the same name).
-/

namespace CollatzMoonshot.Assumed

open CollatzMoonshot.FrontA CollatzMoonshot.FrontB CollatzMoonshot.FrontA.FirstCrossing

/-- **[ASSUMED - computation]** Terras's coefficient stopping-time conjecture holds for every
start `2 ≤ n ≤ 2.8 · 10¹⁹`: at its first coefficient crossing, `n` descends.

Provenance: Rozier, O., Terracol, C., *Paradoxical behavior in Collatz sequences*,
arXiv:2502.00948v5 (2025–2026), Corollary 5.4 (`t(n) = τ(n)` for `2 ≤ n ≤ 2.8·10¹⁹`), read
firsthand 2026-09-19.  Compute-trust caveat: a published computation, not a proof artifact.
The statement is finite and decidable in principle; it implies no open problem on its own
(the fidelity check every `Assumed/` entry owes: "what does this axiom imply by itself?"). -/
axiom cst_verified_rozier_terracol_2026 : CSTVerified

/-- Stopping-time correctness on every first crossing with at most fifty maximal odd runs,
unconditionally modulo the named computation axiom above. -/
theorem stoppingCorrect_of_oddRunCount_le_fifty {n m : ℕ} (hn : 2 ≤ n) (h : At n m)
    (hr : oddRunCount (traceWord n m) ≤ 50) : tstep^[m] n < n :=
  descends_of_oddRunCount_le_fifty cst_verified_rozier_terracol_2026 hn h hr

/-- Any survivor of its first crossing has more than `6.2 · 10¹⁵` odd steps, once it has at
most `96` odd runs. -/
theorem ones_ge_of_survives_of_runs_le {n m : ℕ} (hn : 2 ≤ n) (h : At n m)
    (hsurv : n ≤ tstep^[m] n) (hr : oddRunCount (traceWord n m) ≤ 96) :
    6234549927241963 ≤ ones (traceWord n m) :=
  ones_ge_of_survives_6e15 cst_verified_rozier_terracol_2026 hn h hsurv hr

end CollatzMoonshot.Assumed
