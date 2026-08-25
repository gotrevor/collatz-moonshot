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

## 2026-08-25 — Explicit hypergeometric construction for the `log₂3` effective measure (Front A crux)

**Context.** The sole open input behind the two-block exclusion is now reduced (sorry-free, in
`CollatzMoonshot/FrontA/PowSeparation.lean`, theorem `sep_two_three_of_gelfond_measure`) to ONE
uniform bound `hmeas : ∀ k m, 130 ≤ k → 3^k < 2^m < 2·3^k → 3^k ≤ (2^m − 3^k)·k^6`, i.e. an effective
(polynomial) irrationality measure of `log₂3` at exponent ≤ 7. This is the classical Gelfond/
Bennett–Bugeaud "distance between powers of 2 and 3." I need the EXACT construction to formalize it in
Lean (mathlib has irrationality of `log₂3` and the Chebyshev `lcm(1..n)` denominator bound — leg 1,
already landed in `FrontA/Gelfond.lean` — but nothing else). Legs 2–3 (remainder decay + non-vanishing)
need the source.

**Requests (fetch + summarize the construction; PDFs ideal):**
1. **Bugeaud, *Linear Forms in Logarithms and Applications*, §3.1** ("On the distance between powers of
   2 and 3") and the section "Effective irrationality measures for quotients of logarithms of
   integers." Want: the explicit Padé/hypergeometric approximant family (the polynomials or the
   integral representation), the remainder size bound, the denominator (lcm / Chudnovsky) bound, and
   the final explicit inequality for `|2^n − 3^m|` (with constants).
2. **Bennett–Bugeaud, "Effective results for restricted rational approximation," Acta Arith. 155
   (2012) 259–269** (`personal.math.ubc.ca/~bennett/BeBu.pdf`). Want the theorem statement + proof
   skeleton specialized to base-2/base-3 (the "`b^n ξ` distance-to-integer" form), and the exact
   effective exponent it yields.
3. **The proven irrationality measure `μ(log₂3)`** — the best published explicit value (is it ≤ 7? ≤
   5?), with citation. This fixes whether the `C = 6` in `sep_two_three_of_gelfond_measure` is
   provable-unconditionally (μ ≤ 7) or only conjecturally-true; if the proven μ > 7, tell me the value
   so I bump `C` and redo the concrete crossover/finite-check.

Aim: enough of the explicit construction to formalize legs 2–3 faithfully next lap (no guessing).

## 2026-08-25 (later) — SHARPENED: exact Rhin/Wu two-log construction + explicit constant

WebSearch (server-side) has now pinned the proven object: the effective input behind `sep_two_three`
is the **linear-independence measure of `{1, log 2, log 3}` < 7.616 (Rhin 1987)**, refined by **Wu,
*Math. Comp.* 72 (2003) no. 242, "On the linear independence measure of logarithms of rational
numbers"** (`ams.org/journals/mcom/2003-72-242/S0025-5718-02-01442-4/S0025-5718-02-01442-4.pdf`).
NOT Voutier 2111.01044 (that is roots of rationals `(a/b)^{m/n}`, off-path for logs). Please fetch +
summarize, PDFs ideal:

1. **Rhin 1987** (*Approximants de Padé et mesures effectives d'irrationalité*, Séminaire
   Delange–Pisot–Poitou / Progr. Math. 71) and/or **Wu 2003 (mcom link above)**: the explicit
   Padé-to-`log(1−z)` (or contour-integral) approximant family `A_n + B_n·log2 + C_n·log3`, the
   remainder size bound, the denominator (lcm/Chudnovsky) bound, and the FINAL explicit inequality
   `|q₀ + q₁ log2 + q₂ log3| ≥ c·H^{−τ}` with the exact **constant `c`, exponent `τ` (≤7.616?), and
   threshold `H₀`**. I need `c`, `τ`, `H₀` numerically to fix the honest exponent `C` and the
   native_decide finite-check bound in `sep_of_uniform_measure`.
2. The single-integral kernel Rhin uses (is it `∫₀¹ x^{αn}(1−x)^{βn}(…)^{γn} dx`? the exact exponents/
   weights) — this is what I would formalize as "leg 2" (remainder decay) analogously to the
   ζ(3) Beukers integral in `~/src/reservoir/ahhwuhu/zeta_3_irrational`.
3. Best published `μ(log₂3)` (irrationality measure of the RATIO log3/log2), if it exists separately.
