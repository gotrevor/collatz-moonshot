# HANDOFF 2026-09-22 - mechanism search at the run-count gap node (Fable + Astra)

Attended research day, two agents (Fable: `RESEARCH-2026-09-22-mechanism-search.md`;
Astra: `RESEARCH-2026-09-22-astra-integer-spacing.md`), conversation in
`agent-mail/collatz/` (eight messages, 17:43-19:11 UTC).  **No lap launched, none
authorized.  DIRECTION's no-lap-without-a-mechanism gate stands.**  Nothing on the board
clears it.

## Checkpoint

* Branch `main`, pushed.  Full build green (8787 jobs, pre-commit gate).
* New Lean, base three axioms: `FrontA/FirstCrossingResidue.lean` -
  `at_primitive` (a first-crossing word is never a proper power), `overshoot_modEq`
  (`3ᴷ·E ≡ N (mod D)`).
* New probes with pytest hand anchors: `experiments/sibling_survivors.py`
  (`test_sibling_survivors.py`, 3 passed) and Astra's controls in their note §4.

## 1. The logical split (agreed)

`StoppingCorrect ⟺ N_ε ∧ C_ε`, a tautology.  `N_ε`: every first-crossing survivor has
`r ≥ εK` odd runs (the repo's frozen node, the few-run exclusion made uniform).  `C_ε`: no
survivor has `r ≥ εK` runs.  `N_ε` does not imply CST; every many-run survivor, cycle or
not, lives in `C_ε`, including cycles whose crossing prefix has `≥ εK` runs (a sub-problem
of many-circuit cycles with no known mechanism).  A typical ballot word has `r ≈ 0.37K`.
The ladder has `r ≤ 50` modulo the named computation axiom
`cst_verified_rozier_terracol_2026`.
Mail: `20260922T174347Z-fable-*`, `20260922T175908Z-astra-*` (§1 of Astra's note).

## 2. Single congruence (Fable, proved on paper; Lean for the residue half)

For a word `v` and `E ≥ 0`: `{n ≥ 2 : traceWord n m = v ∧ Tᵐn = n+E} = {n ≥ 2 : n = (N−2ᵐE)/D ∈ ℤ}`.
Integrality already forces the residue class, so the `r` run-to-run admission equations
(Cramer, det `= D`) carry exactly one congruence.  Exact CST:
`[N·3⁻ᴷ mod D] > (N − 2D)/2ᵐ` for every first-crossing word; window `≤ K/(3u)`.
**Scope (Astra's correction, accepted):** this excludes a second independent
*congruence*; it does not exclude a useful *inequality* over jointly realizable states.
Mail: `20260922T180035Z-fable-*`.

## 3. Three failed relaxations, with their counterexamples (Astra, proofs in their note)

All three are necessary conditions on `(v, n)` that a genuine survivor satisfies, and all
three admit false candidates on one explicit all-length family: the Christoffel words
`p_i = ⌊i·log₂3⌋`, `m = p_K + 1`, which are first-crossing, have every odd run `≤ 2`
(so `r ≥ K/2`), `N/3ᴷ ∈ (K/6, (7K+1)/24]`, and `1 < u ≤ 1 + η` for arbitrarily large `K`.

| relaxation | statement | false candidate | mail / note |
|---|---|---|---|
| spacing (weak) | `u ≤ P_K(n) := ∏_{i<K}(1 + 1/(3(n+2i)))` | least odd `n ≥ K`; `D·n < N` and `P_K(n) > 10/9 > u` | `175908Z-astra`, note §3 |
| full-numerator spacing | exact rational `E = (N−Dn)/2ᵐ`, so `u(1+E/n) = 1 + S/n ≤ P_K(n)`, `S = N/3ᴷ` | `n = 8K+1`, `u ≤ 1.01`: `S ≤ (7K+1)/24` (adjacent-pair bound) and `P_K(n) ≥ 1 + K/(3(n+K−1))` (Cauchy) meet at `n ≥ 7K+1`; hand anchor `K=5, v=11011010, N=319, D=13, n=21, E=23/128`, realizing residue `123` descends | `190050Z-astra`, note §3 |
| exact prefix + optimal unordered tail | first `j` letters realized exactly (residue class mod `2ʲ`, prefix states pairwise distinct), tail bounded by the `K−k` smallest allowed odd integers `≥ n` | `2ʲ·j² = o(K)` (e.g. `j = ⌊½log₂K⌋`), odd `n ∈ [10K,12K]` in the class, `≥ 2√K − O(j²)` candidates after deleting the `≤ j(j+1)/2` collision values, while the interval holds at most one realizing residue; margin `9K² − 261Kk − 12K − 3k + 3 > 0`, extended across the interval by the positive coefficient `K−1−8k` | `190657Z-astra`, note §6; audit `190824Z-fable` |

Fable audited each proof step by hand (mail `180035Z`, `190207Z`, `190824Z`): no defect.
**What the third obstruction discards is the tail's temporal order**; it is a negative
theorem about that particular unordered-tail relaxation, not about every mixed form and
not about every integer-spacing method.

## 4. Corrected proofs and retracted claims (both sides)

* Fable, retracted: "`C_ε` contains the many-circuit cycle problem" (inclusion runs the
  other way); `E = 0` for cycle minima (only when the crossing is the full period);
  `r ≈ K/2`; entropy `0.951` (`0.950`); "cycle ⊆ `C`" (one rotation per negative cycle
  is ballot-forever); the lap formula without its rotation hypotheses; Hercher's 91 as
  pincer reach (68 on paper, 50 in Lean); "seed 5 is a scaling family" (one crossing, 39
  laps); "amortised bookkeeping cannot help" (true for congruences only); "entropy
  deficit and verified range are the only 3-specific inputs" (the two *known* ones);
  `√|B_m|` as a universal counting floor (the sieve shape only); "monotone necessary
  conditions are universally incomplete" and "the residue is the only non-monotone
  datum" (overreach; the concrete interval obstruction is the statement to keep);
  **"a survivor's pre-crossing states are automatically distinct"** (false: a repeated
  later state does not force an earlier crossing - 5n+1 state 13 at times 1 and 8,
  crossing at 274; keep distinctness or `NoNontrivialCycle` as an explicit hypothesis
  of every spacing bound).
* Fable, corrected proof of monotonicity of `f_K(n) = n(P_K(n) − 1)`: induction
  `f_{K+1} = f_K + (n + f_K)/(3(n+2K))`, update increasing in `f`, `n`-derivative
  `(2K − f)/(3(n+2K)²) ≥ 0` (Astra, note §7).
* Astra, corrected: the first hand anchor `n = 5` passes only the weak bound and fails
  full SP; replaced by `n = 21`.  The interval-extension step for the third obstruction
  was unstated, now explicit.

## 5. Controls that any future candidate must pass

* `5n+1`: first-crossing survivors `13, 17` (`E = 0`) and `5` (`m = 274`, `K = 118`,
  `39` runs, `E = 8`, one crossing).  A mechanism valid for every odd multiplier is
  false.  `python3 experiments/sibling_survivors.py survivors 5 1 100`.
* `3n−1`: no first-crossing survivor at all (`N < 0`); `n = 5` never crosses, the sign
  control for `CrossingExists`.
* The Christoffel family above, with the three candidate `n` of §3.
* Recorded before today: P6 / short-run families, 2305 vs 2313, Mersenne `q = 12 → 6`.

## 6. Exactly what remains unexcluded

* `C_ε` itself, for every `ε`.  In particular cycles whose crossing prefix has `≥ εK`
  runs, and the orbit-below-a-cycle shape (needs cycle exclusion first).
* Necessary conditions that couple the **tail's temporal order** to actual integer
  values, beyond unordered spacing.  Neither agent has a proposal.
* Mixed forms at scales `2ʲ·j² ≠ o(K)`, and integer-spacing methods other than the
  sorted-product form.
* `CrossingExists`: `ℕ_{≥2} ∩ C = ∅` for the ballot-forever Cantor set; only `N > 0`
  is load-bearing; no individual-orbit lever.

## 7. Next session

Re-read DIRECTION's gate.  Do not re-open: second-congruence searches, the three
relaxations above at any constants, minimal-counterexample suffix constraints,
ballot-residue discrepancy by counting, or a Christoffel/extremal-word residue signature.
A proposal must state which discarded datum it retains (tail order, or something not
in the sorted-product form), pass §5, and name its load-bearing step before any lap.
