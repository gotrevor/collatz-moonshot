# ON-LINE-REQUEST

Host sessions with egress: please answer inline as `ON-LINE-FINDINGS-<date>-<slug>.md`,
then `git mv` this entry's resolved block into `archive/findings/`.

## 2026-08-24 — Simons–de Weger cycle-count method (Front B `Compression`)

**Context.** The repo's Front B closer needs `Compression`: an *upper* bound `C` on the
circuit count (`m` = number of maximal odd-runs = local minima) of a primitive nontrivial
integer Collatz cycle. With `hercher_min_circuit_count` (≥92) any `C ≤ 91` closes Front B.
The literature bounds `m` from *below* (SdW 68→76, Hercher 77→91); the *upper* bound
appears absent. Before formalizing a decomposition I want the exact structure SdW exploit.

**Requests (any subset useful):**
1. Simons & de Weger, "Theoretical and computational bounds for m-cycles of the 3n+1
   problem" (Acta Arith. 117 (2005) 51–70) — PDF or the precise statement + proof sketch
   of how they reduce a *fixed*-`m` cycle to a bounded S-unit / linear-forms problem. In
   particular: for fixed `m`, how many `2^s 3^t` terms does the cycle equation have, and
   which finiteness theorem (Baker vs. Subspace/ESS) closes each `m`?
2. Does ANY published work give an *upper* bound on `m` for integer cycles (even
   conditional), or a structural reason `m` cannot be bounded elementarily? (Steiner 1977
   for `m=1`; anything for general `m`?)
3. The de Weger "1-cycle = Steiner" write-up: confirm the one-circuit case genuinely needs
   an effective irrationality measure for `log₂3` (relevant to our `SteinerOneCircuit`).

**Already on-box** (do not re-fetch): Hercher 2023, Eliahou 1993, Knight 2026,
Kurtz–Simon 2007, Conway 2013 (`papers/`).
