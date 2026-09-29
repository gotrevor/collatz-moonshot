# Two six-step fixed-offset refills: bounded Lean lap

Own only `CollatzMoonshot/Obstructions/RayRefill.lean` and `HANDOFF-2026-09-29-ray-refill.md`.  The skeleton is installed in the repo.  Preserve all five definitions and all four frozen theorem statements exactly.  Parent has installed the root import and frozen RayRefillConsumers in `scripts/AxiomAudit.lean`; do not edit them.  Import `CoefficientRay` as staged.  At most **three Opus/low laps with a 35-minute supervisor limit**, no Aristotle.  No hard-family CRT theorem, no general return/covering claim, no rank theorem, and no unrelated edits.

The claims are two real positive paired trajectories under `FrontB.tstep`, each six steps.  The first changes the inherited relation `A+5=72(B−1)` to `A'+5=216(B'−1)`.  The second starts and ends with multiplier `216`.  Both targets strictly contract on the return.  The recurrence `refillT` gives arbitrarily high fresh binary precision after the first return while the old auxiliary difference is odd.  This is a local counterexample to monotone binary fuel, not a solution of full-state rank or original hard-family reachability.

## Exact intermediate values

For `refill0A t`, the six target values are

```
499+4608t → 749+6912t → 1124+10368t → 562+5184t
          → 281+2592t → 422+3888t → 211+1944t.
```

Their parities are `110010`.  For `refill0B t`, the six auxiliary values are

```
8+64t → 4+32t → 2+16t → 1+8t → 2+12t → 1+6t → 2+9t.
```

Their parities are `000101`.  For `refill1A t`, the target values are

```
9715+13824t → 14573+20736t → 21860+31104t → 10930+15552t
            → 5465+7776t → 8198+11664t → 4099+5832t.
```

Again the word is `110010`.  For `refill1B t`, the auxiliary values are

```
46+64t → 23+32t → 35+48t → 53+72t
       → 80+108t → 40+54t → 20+27t.
```

The word is `011100`.  Prove each one-step identity with a small private parity helper or by unfolding `tstep`; pin each intermediate expression and compose with `Function.iterate_succ`.  `omega` should handle the linear arithmetic, parity, natural subtraction, positivity, and strict contraction.  Avoid unfolding large recursive orbit expressions into one `omega` goal.  Hand anchors: `(499,8)→(211,2)` and `(9715,46)→(4099,20)`.

The fixed-offset equalities are elementary linear arithmetic after the exact endpoint lemmas:

```
(499+4608t)+5 =72((8+64t)−1),
(211+1944t)+5=216((2+9t)−1),
(9715+13824t)+5=216((46+64t)−1),
(4099+5832t)+5=216((20+27t)−1).
```

For `refillT_formula`, induction gives
`9(64·refillT k+7)+1=64(9·refillT k+1)=64^(k+1)`.
Then `refill0_fuel` follows from `refill0_actual` and that formula.  The old difference is `7+64·refillT k`, always odd.  The new difference is `9·refillT k+1=64^k`; the target relation supplies `A'+5=216·64^k`.  Do not replace the exact recurrence with an existential modular theorem.

The original hard-family CRT lifting, the absence of an unrestricted reset grammar, and the first-deviation determinant analysis remain paper-side in `RESEARCH-2026-09-29-ray-fuel-exit.md` (parent-owned).  After the proof is ready, build the module and root on the host; run `lake env lean scripts/AxiomAudit.lean` to check the already installed consumer.  No successor task.  Commit green work and finish with `box done --green` only after the checks actually pass.  These checks establish only the four local declarations.  Report any genuine statement defect rather than weakening a frozen type.
