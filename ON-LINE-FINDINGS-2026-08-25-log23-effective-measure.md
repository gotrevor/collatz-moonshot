# ON-LINE-FINDINGS 2026-08-25 - the effective `log₂3` measure behind `sep_two_three` (Front A crux)

Answers the `2026-08-25` entry of `ON-LINE-REQUEST.md`.  Fulfilled by a networked host session on
2026-08-24 (host clock).

## 🔴 Bottom line, up front

1. **`C = 6` is not provable from today's literature, and it is not close.**  Your `hmeas` at
   exponent `C` needs an effective irrationality-measure exponent `E ≲ 5.48` for `log₂3`.  The best
   *fully explicit* published bound is **`E = 13.3`** (Rhin 1987); the best *asymptotic* one is
   **`7.616 + ε`** (Rhin, same paper), and that one carries an unpublished threshold `H₀(ε)`.  Both are
   above 7.  `C = 6` is almost certainly **true** (the continued fraction of `log₂3` behaves like a
   generic irrational, true measure ≈ 2), it is simply out of reach of proof.
2. **Recommended bump: `C = 15`, threshold `k ≥ 400`.**  Derivation and exact crossover numbers in §3.
   The finite check has to grow from `6 ≤ k < 130` to `6 ≤ k < 400` (`k^45 ≤ 2^k` first holds at
   `k = 387`).
3. **Bennett-Bugeaud (2012) is the wrong paper.**  Its actual title is *"Effective results for
   restricted rational approximation to **quadratic irrationals**"*; it bounds `‖bⁿ ξ‖` for `ξ` a real
   **quadratic** irrational.  It says nothing about `log₂3`.  Details in §5.
4. **The construction you want is free and I have it**: Wu, *On the linear independence measure of
   logarithms of rational numbers*, Math. Comp. **72** (2003) 901-911, Theorem 2, which is exactly the
   Padé/Rhin machine (integrand family, denominator `lcm`, remainder decay, non-vanishing), plus
   Rhin's explicit factor list for the `(1, log 2, log 3)` case.  §4.
5. **Front A and Front B now share one deep input.**  `SteinerOneCircuit` needs the same object; see
   `ON-LINE-FINDINGS-2026-08-24-simons-deweger-m-cycles.md` §3.

---

## 1. Sources actually read

| Source | Obtained | Status |
|---|---|---|
| Wu, *On the linear independence measure of logarithms of rational numbers*, Math. Comp. **72** (2003) 901-911 | free AMS PDF | ✅ read.  Local: `papers/wu-2003-linear-independence-logs.pdf` (gitignored) |
| Bennett & Bugeaud, *Effective results for restricted rational approximation to quadratic irrationals*, Acta Arith. **155** (2012) 259-269 | `irma.math.unistra.fr/~bugeaud/travaux/vbeff1.pdf` | ✅ read.  Local: `papers/bennett-bugeaud-2012-quadratic-irrationals.pdf` |
| Simons & de Weger v1.44 (2010); Simons, arXiv:2205.10582 | see the Front B findings | ✅ read (both quote Rhin's Proposition) |
| Zudilin, *An essay on irrationality measures of pi and other logarithms*, arXiv:math/0404523 | arXiv | ✅ read §3 (Rhin's construction, in Rhin's own linearised form) |
| Waldschmidt, *Perfect Powers: Pillai's works and their developments* | author's site | ✅ read (Ellison's bound, §6) |
| Bugeaud, *Linear Forms in Logarithms and Applications*, EMS 2018 | ❌ **paywalled**; only the table of contents is free | ⚠️ **not read** - see §6 |
| Rhin, Progress in Math. **71** (1987) 155-164 | ❌ **paywalled** Birkhäuser chapter | ⚠️ **not read** - see §7, this is the one gap that matters |

---

## 2. What is actually proven about `log₂3`

### 2.1 The explicit bound (this is the one to build on)

> **Rhin (1987), Proposition on p. 160.**  For integers `u₀, u₁, u₂` (not all zero) with
> `H = max(|u₀|, |u₁|, |u₂|)`,
> ```
> |u₀ + u₁ log 2 + u₂ log 3|  ≥  H^(-13.3)
> ```

Provenance: I did not read Rhin.  I read **two independent published applications** that quote it
identically and by page number:

- Simons & de Weger v1.44, **Lemma 12**: *"We apply the Proposition on p. 160 of [Rh] with `u₀ = 0`,
  `H = u₁ = K + L`, `u₂ = -K`"*, yielding `Λ > e^{-13.3(0.46057 + log K)}` (and `0.46057 = log δ`, so
  this is exactly `Λ > (K+L)^{-13.3}`).
- Simons, arXiv:2205.10582, **Lemmas 10 and 13**: *"We apply Rhin's proposition on p. 160 with
  `u₀ = 0`, `u₁ = 2K+L`, `u₂ = -(K+L)`.  Then `H = u₁ = 2K+L` and Rhin's estimate leads to
  `|Λ| ≥ [2K+L]^{-13.3}`."*

Simons & de Weger also state, on the choice of tool: *"For general linear forms `x log a + y log b`
the best results today are LMN for small `x, y` and Matveev for large `x, y`.  **For our specific case
`x log 2 + y log 3` however, the result of Rhin is best.**"*  So `13.3` is the sharpest fully explicit
constant available for this exact pair, as of 2010, and I found nothing newer (confidence 80%).

**Translation to an irrationality measure.**  With `u₀ = 0`, `u₁ = -p`, `u₂ = q`:
`|q log 3 - p log 2| = (log 2) q |δ - p/q|` with `δ = log₂3`, and `H ≈ δq`, so
**`μ(log₂3) ≤ 14.3`, explicitly and effectively.**

### 2.2 The asymptotic bound (sharper exponent, unusable threshold)

Wu 2003 §1, reporting the same Rhin paper: *"he obtained a linear independence measure of
`1, log 2, log 3` less than **7.616** ... This is the best linear independence measure known for
`1, log 2, log 3`, and it gives the best irrationality measure known of `log 3` (8.616)."*

"Linear independence measure `ν`" is Wu's Definition (1.2): for every `ε > 0` there is `H₀(ε)` with
`|p + q₁α₁ + ... + qₙαₙ| ≥ H^{-ν-ε}` for `H = maxᵢ|qᵢ| ≥ H₀(ε)`.  So `7.616` buys you
**`μ(log₂3) ≤ 8.616 + ε`**, but only past a threshold `H₀(ε)` that nobody has published.  Rhin's p. 160
Proposition is the price he pays to state something with no `ε` and no unstated threshold.

⚠️ Note the two numbers coexist in the **same paper**: `13.3` is the clean explicit statement, `7.616`
the asymptotic optimum of the same construction.  Do not "correct" one into the other.

### 2.3 Roads that do NOT get there (checked, so nobody re-walks them)

| Candidate | Verdict |
|---|---|
| Baker-Wüstholz (general `n` logs, linear in `log B`) | gives a polynomial measure but with `C(2,1) h'(2) h'(3) ≈ 1.4e9`, i.e. `μ ≲ 1.4e9`.  Useless numerically. |
| Laurent-Mignotte-Nesterenko (two logs, the standard sharp tool) | shape `exp(-C (log B)²)`, which decays **faster** than any fixed polynomial.  Sharper than Rhin for small `H`, weaker for large `H`.  Not an irrationality measure at all. |
| Ellison 1971 (the classical explicit `2ˣ` vs `3ʸ` result) | `\|2ˣ - 3ʸ\| > 2ˣ e^{-x/10}` for `x ≥ 12`, `x ∉ {13,14,16,19,27}` (Waldschmidt, *Perfect Powers*, §2.2.2).  **Exponential**, not polynomial: far too weak for `hmeas`. |
| `μ(log 3) ≤ 5.116` (Wu-Wang 2014), `μ(log 2) ≤ 3.57` etc. | measures of a **single** logarithm.  They say nothing about the two-log form `u₁ log 2 + u₂ log 3`, hence nothing about `log₂3`.  Do not chain them. |
| Bennett-Bugeaud 2012 | quadratic irrationals only.  §5. |

---

## 3. The bump: `C = 15`, threshold `k ≥ 400` 🔧

### 3.1 Derivation (all steps elementary once Rhin is assumed)

Assume `3^k < 2^m < 2·3^k`, and put `Λ = m log 2 - k log 3 ∈ (0, log 2)`.

1. `2^m - 3^k = 3^k (e^Λ - 1) ≥ 3^k · Λ`.
2. `2^m > 3^k > 2^k` forces `m > k`, so Rhin's `H = max(m, k) = m`.
3. `2^m < 2·3^k` forces `m < 1 + k δ`, `δ = log₂3 = 1.5849625...`.
4. Rhin: `Λ ≥ H^{-13.3} = m^{-13.3} > (1 + kδ)^{-13.3}`.
5. Hence `3^k ≤ (2^m - 3^k) · (1 + kδ)^{13.3}`, and it suffices that `(1 + kδ)^{13.3} ≤ k^C`,
   i.e. `C ≥ 13.3 · log(1 + kδ) / log k`.  That ratio **decreases** in `k`, so checking it at the
   threshold suffices.

### 3.2 The numbers (computed exactly; `experiments/` script below)

Minimal real `C` from step 5, at various thresholds `K₀`:

| `K₀` | with `E = 13.3` (explicit) | with `E = 7.616` (asymptotic) |
|---|---|---|
| 130 | 14.572 → **C = 15** | 8.344 → C = 9 |
| 200 | 14.464 → C = 15 | 8.283 → C = 9 |
| 387 | 14.332 → C = 15 | 8.207 → C = 9 |
| 400 | 14.326 → **C = 15** | 8.203 → C = 9 |
| 500 | 14.288 → C = 15 | 8.182 → C = 9 |

Downstream, `sep_of_measure` needs `k^{3C} ≤ 2^k`.  First `k` at which it holds **and keeps holding**:

| `C` | 6 | 9 | 10 | 14 | **15** | 16 |
|---|---|---|---|---|---|---|
| least `k` with `k^{3C} ≤ 2^k` | 126 | 208 | 237 | 356 | **387** | 418 |

(That is why your `crossover_130` works at `C = 6`: `k^18 ≤ 2^k` from `k = 126`.)

### 3.3 Concrete restatement for `PowSeparation.lean`

```lean
theorem sep_two_three_of_gelfond_measure
    (hmeas : ∀ k m : ℕ, 400 ≤ k → 3 ^ k < 2 ^ m → 2 ^ m < 2 * 3 ^ k →
        3 ^ k ≤ (2 ^ m - 3 ^ k) * k ^ 15)
    (k m : ℕ) (hk : 6 ≤ k) (h1 : 3 ^ k < 2 ^ m) (h2 : 2 ^ m < 2 * 3 ^ k) :
    3 ^ (3 * k) ≤ (2 ^ m - 3 ^ k) ^ 3 * 2 ^ k
```

with `crossover_400 : 400 ≤ k → k ^ 45 ≤ 2 ^ k` replacing `crossover_130`, and
`sep_two_three_small` extended from `k < 130` to `k < 400`.  `window_unique_m` still gives one `m`
per `k`, so that is 270 extra near-critical pairs; the largest numbers involved are `3^399 ≈ 10^190`.

Keeping `C` and the threshold as *parameters* of the reduction (rather than baking in 15 / 400) is
worth the small cost: if the Rhin threshold in §7 turns out to bite, the only thing that moves is the
instantiation.

---

## 4. The construction, for legs 2-3 🧮

Wu 2003 Theorem 2 is Rhin's machine written out in general.  It is **exactly** the leg-2 / leg-3
skeleton you asked for, and it plugs straight into the `lcm(1..n)` brick you already landed in
`FrontA/Gelfond.lean`.

> **Setup.**  `1 < a₁ < ... < a_m` integers, `Δ = gcd(a₁,...,a_m)`.  `Hₙ ∈ (Δ, x)ⁿ ℤ[x]`.
> ```
> Iₙ(aᵢ, aᵢ₊₁) = ∫_{aᵢ}^{aᵢ₊₁} (Hₙ(x)/xⁿ) dx/x
> Dₙ = lcm(1, 2, ..., max(n, deg Hₙ - n)),      K = lim (1/n) log Dₙ
> ```
> **Integrality (leg 3, the "these are integers" half).**  `Dₙ Iₙ(aᵢ,aᵢ₊₁) ∈ ℤ + ℤ log(aᵢ₊₁/aᵢ)`.
> Concretely, writing `Hₙ = Σⱼ Bⱼ xʲ`, term-by-term integration gives
> `Iₙ = Bₙ log(aᵢ₊₁/aᵢ) + Σ_{j≠n} (Bⱼ/(j-n))(aᵢ₊₁^{j-n} - aᵢ^{j-n})`, and `Dₙ` clears every
> denominator `|j - n| ≤ max(n, deg Hₙ - n)`.
> **Remainder decay (leg 2).**  `-τ⁽ⁱ⁾ = lim (1/n) log ( max_{aᵢ ≤ x ≤ aᵢ₊₁} |Hₙ(x)/xⁿ| )`.
> **Denominator growth.**  `rₙ = Dₙ Bₙ`, `Bₙ = (1/2πi) ∮_{|z|=ρ} (Hₙ(z)/zⁿ) dz/z`, so
> `lim (1/n) log|rₙ| = τ⁽⁰⁾ + K` with `τ⁽⁰⁾ = lim (1/n) log max_{|z|=ρ} |Hₙ(z)/zⁿ|`.
> **Conclusion.**  If the `τ⁽ⁱ⁾` are positive and pairwise distinct and `τ = minᵢ τ⁽ⁱ⁾ > K`, then for
> every `ε > 0` there is an **effectively computable** `H₀(ε)` with
> ```
> |p + Σᵢ qᵢ log(aᵢ₊₁/aᵢ)|  ≥  H^(-μ-ε),        μ = (τ⁽⁰⁾ + K)/(τ - K)
> ```
> for all integers with `H = maxᵢ|qᵢ| ≥ H₀(ε)`.

Wu's **Lemma 1** is the generic engine underneath (small linear forms `εₙ⁽ⁱ⁾ = rₙγᵢ - pₙ⁽ⁱ⁾` with
`lim (1/n) log rₙ ≤ σ` and `lim (1/n) log|εₙ⁽ⁱ⁾| = -τ⁽ⁱ⁾` imply the measure `σ/τ`), and it is where
the explicit `H₀(ε)` is constructed.  That lemma, not the integral bookkeeping, is the part your
legs 2-3 need to reproduce.

**Rhin's specific data for `(1, log 2, log 3)`** (Wu 2003, eq. (1.4)): take `a = (2, 3, 4)`, so the two
forms are `log(3/2)` and `log(4/3)`, and

```
Hₙ(x) = b₀ · Π_{i=1}^{6} Qᵢ(x)^{[bᵢ n]}
Q₁ = x - 2      Q₂ = x - 3      Q₃ = x - 4
Q₄ = 5x - 12    Q₅ = 17x² - 102x + 144      Q₆ = 19x² - 104x + 144
```

with the two integrals `∫₂³ Hₙ(x)/xⁿ dx/x` and `∫₃⁴ Hₙ(x)/xⁿ dx/x`.  (`Q₅` has real roots
`2.2724, 3.7276`, both inside `[2,4]`; `Q₆` has the complex pair `2.7368 ± 0.2977 i`; `Q₄` a root at
`2.4`.)  Wu's contribution is precisely a method (integer transfinite diameter + generalised
Müntz-Legendre polynomials + LLL) for *finding* such factors, since *"Rhin did not give a theoretical
justification for the use of `Q₄, Q₅, Q₆`."*

⚠️ **The exponents `b₁..b₆` are NOT in Wu**, only in Rhin.  I set up Wu's `μ = (τ⁽⁰⁾+K)/(τ-K)` and
searched numerically for a feasible exponent vector over those six factors and **found none**
(every candidate had `τ ≤ K`, i.e. infeasible; the plain choice `(x-2)ⁿ(x-3)ⁿ(x-4)ⁿ` gives
`τ = 1.830 < K = 2`).  So I have **not** reproduced `7.616`, and the `bᵢ` remain an unfetched datum.
Script: `experiments/rhin_mu_wu_framework.py` (self-contained, uv shebang).  Treat any `bᵢ` you
recover from it as unverified until it reproduces a published constant.

---

## 5. Bennett-Bugeaud 2012: wrong tree ❌

Read in full.  Actual title: **"Effective results for restricted rational approximation to
*quadratic irrationals*"**.  Throughout, `ξ` is a real algebraic number of degree `d ≥ 2`, and the
results bound `‖bⁿ ξ‖` (distance to the nearest integer) - i.e. they are about **blocks of zero
digits in the base-`b` expansion of an algebraic number**, not about powers of 2 versus powers of 3.

Main statements: Theorem 1.1 (Schinzel 1967, `‖bⁿξ‖ > b^{-n} exp{c(ξ,b) n^{1/7}}`), Theorem 1.2
(`v_b^eff(ξ) ≤ 1 - τ(ξ,P)`), Theorem 1.3 (`v_p^eff(√(p²+1)) ≤ 1 - τ₁`), Theorem 1.4
(`v_b^eff(√(b^{2k}+1)) ≤ (log 48)/(k log b)`, via Padé approximants).

`log₂3` is transcendental, so **none of it applies**.  The request's premise (that this paper
specialises to a "base-2/base-3 `bⁿξ` distance-to-integer form") does not hold.  Drop this line.

---

## 6. Bugeaud's book: what I can and cannot confirm ⚠️

**Confirmed** (from the free table of contents, `irma.math.unistra.fr/~bugeaud/travaux/LFLOGtoc.pdf`):
Chapter 3 is *"First applications"*, and

- **§3.1, p. 23 - "On the distance between powers of 2 and powers of 3"** ✅ exists, title as you had it
- **§3.2, p. 25 - "Effective irrationality measures for quotients of logarithms of integers"** ✅
- §3.3 "On the distance between two integral S-units", §5.1 the same for rational numbers, §6.2 Waring

**Not confirmed**: the contents.  The book is EMS, paywalled; only the TOC and front matter are free,
and I did not read a single theorem from it.  I am therefore **not** reporting what §3.1 states.

What I can say without opening it: the book's engine is the LMN / Matveev two-logarithm estimate
(chapter 2), and Simons & de Weger state flatly that for the specific pair `(2,3)` **Rhin beats that
family**.  So §3.1 is likely a `exp(-c (log n)²)`-shaped statement, which is not an irrationality
measure and would not give `hmeas` at any fixed `C`.  Confidence 75%; the way to settle it is to read
p. 23-26, which Cornell alumni EZproxy may or may not reach (EMS books are not in the licensed set
per `preferences/cornell-library-access.md`, so expect a purchase or an ILL).  **Ask if you want me to
chase it** - but on the evidence above it would be a confirmation exercise, not a source of a better
constant.

---

## 7. The one gap that matters: Rhin's threshold 🚨

Both published applications quote the Proposition as a bare `|Λ| ≥ H^{-13.3}` with **no stated range
of validity**.  In both, `H ~ 10^17` or larger, so any hypothesis of the form `H ≥ H₀` would be
invisible to them.  **Our application is different**: at `k = 400` we have `H = m ≈ 634`.  If Rhin's
Proposition carries a threshold above ~600, the `C = 15 / k ≥ 400` instantiation is unsound as
written, and the finite check has to swallow everything below the real threshold.

So, in order:

1. Treat `13.3` as **provenance-verified through two independent secondary uses**, and the
   **threshold as unknown**.  Do not write "for all `H ≥ 2`" in a docstring.
2. State the Lean hypothesis with its own explicit threshold parameter, exactly as in §3.3, and put
   the unknown in the docstring where it cannot be summarised away.
3. To close it: Rhin, *Approximants de Padé et mesures effectives d'irrationalité*, in *Séminaire de
   Théorie des Nombres, Paris 1985-86* (ed. C. Goldstein), **Progress in Mathematics 71**, Birkhäuser
   1987, pp. 155-164 - the Proposition is on **p. 160**.  Springer chapter DOI
   `10.1007/978-1-4757-4267-1_11`, paywalled.  This is a hand-download ask for Trevor (Cornell
   EZproxy, or ILL), not something a host session can fetch.  It is the single highest-value fetch
   left on this front.

---

## 8. Recommended shape for the Lean layer

**Formalising Rhin's proof is an expedition, not a lap.**  It needs: the integer transfinite diameter
optimisation, LLL-found auxiliary polynomials, contour asymptotics for `Bₙ`, and Wu's Lemma 1
threshold construction.  Nothing in mathlib is close.

The proportionate move, and the one consistent with how this repo already handles Hercher:

- Keep `sep_two_three_of_gelfond_measure` as the machine-checked reduction (it is the real asset).
- Disclose **one** named, THEOREM-grade axiom for the transcendence input, e.g.
  ```lean
  /-- **Rhin (1987), Proposition p. 160** (disclosed effective input).  ... -/
  axiom rhin_two_log (u₁ u₂ : ℤ) (h : (u₁, u₂) ≠ 0) :
      (max |u₁| |u₂| : ℝ) ^ (-(13.3 : ℝ)) ≤ |(u₁ : ℝ) * Real.log 2 + (u₂ : ℝ) * Real.log 3|
  ```
  with the threshold caveat welded into the docstring, and derive `hmeas` at `C = 15` from it.
- The same axiom discharges Front B's `SteinerOneCircuit` for `k ≥ 97` (see the Front B findings §3),
  so one disclosure buys both fronts.  That is a better trade than two bespoke axioms.
- Then `#print axioms` on the Front A headline names exactly one transcendence axiom plus Hercher,
  which is an honest and defensible footprint for a moonshot scaffold.
