# ON-LINE-FINDINGS 2026-08-24 - Simons-de Weger cycle-count method (Front B `Compression`)

Answers the `2026-08-24` entry of `ON-LINE-REQUEST.md`.  Fulfilled by a networked host session
on 2026-08-24 (host clock).

## Sources actually read (not cited-from-citations)

| Source | How obtained | Status |
|---|---|---|
| Simons & de Weger, *Theoretical and computational bounds for m-cycles of the 3n+1 problem*, **version 1.44, 31 Aug 2010** (v1.3 = Acta Arith. **117** (2005) 51-70) | `deweger.net/papers/[35a]SidW-3n+1-v1.44[2010].pdf` | ✅ full text read.  Local: `papers/simons-deweger-2010-m-cycles-v144.pdf` (gitignored) |
| Simons, *On the nonexistence of 2-cycles for the 3x+1 problem*, Math. Comp. **74** (2005) 1565-1572 | AMS free PDF | ✅ full text read.  Local: `papers/simons-2005-two-cycles.pdf` |
| Simons, *Cycles and divergent trajectories for a class of permutation sequences*, arXiv:2205.10582 | arXiv | ✅ read for the second, independent quotation of Rhin's Proposition |
| Rhin, *Approximants de Pade et mesures effectives d'irrationalite*, Progress in Math. **71** (1987) 155-164 | ❌ **paywalled** (Birkhauser/Springer chapter), not read | see the caveat in the Front A findings |

⚠️ **The 2005 Acta Arith. paper is superseded by the authors' own v1.44.**  v1.3 (= the published
paper) proves no nontrivial m-cycles for `m ≤ 68`; v1.44 proves `m ≤ 75` and improves every table.
Cite v1.44 for numbers, the Acta Arith. paper for the record.  Hercher 2023 (already on-box) then
takes it to `m ≤ 91`.

---

## 1. The exact structure SdW exploit

### 1.1 The chain equation (their §2.1)

An m-cycle has local minima `x_i` (odd) and maxima `y_i`, with `k_i` = length of the i-th odd run
and `l_i` = length of the following even run; `K = Σ k_i`, `L = Σ l_i`.  Then
`x_i = 2^{k_i} a_i - 1` for an integer `a_i ≥ 1`, going up gives `y_i = 3^{k_i} a_i - 1`, going down
gives `y_i = 2^{l_i} x_{i+1}`, and eliminating produces the **chain equation**

```
3^{k_i} a_i - 1 = 2^{k_{i+1} + l_i} a_{i+1} - 2^{l_i}     (i = 0 .. m-1, cyclically, a_m = a_0)
```

### 1.2 Fixed m is an m x m LINEAR system, not an S-unit equation 🔑

With `k_i, l_i` fixed this is **m linear equations in the m unknowns `a_i`**: `M a = (2^{l_i} - 1)`,
where `M` is the cyclic bidiagonal matrix with `-3^{k_i}` on the diagonal and `2^{k_{i+1}+l_i}` on
the superdiagonal (wrapping).  Then

```
det M = (-1)^{m-1} Δ,      Δ = 2^{K+L} - 3^K
```

and (Bohm-Sontacchi) the adjugate entries are `m_{i,j} = 2^{α_{i,j} + β_{i,j}} 3^{K - k_i - α_{i,j}}`
with `α_{i,j} = Σ_{h=i+1}^{j*} k_h`, `β_{i,j} = Σ_{h=i+1}^{j*} l_{h-1}` (`j* = j` if `i ≤ j`, else
`j + m`).  All entries are positive, which is how they get `Δ > 0` for free.  m-cycles correspond
1-1 to positive integer solutions `(k_i, l_i, a_i)`; for each `(k_i, l_i)` there is at most one.

**Direct answer to the request's question 1.**  For fixed `m` the cycle equation carries `m^2`
monomials `2^s 3^t` (the adjugate entries), but they never enter the transcendence step.  The only
object handed to transcendence theory is the **two-term linear form**

```
Λ = (K + L) log 2 - K log 3
```

independent of `m`.  There is **no S-unit equation and no growing term count** in their method.

### 1.3 Which finiteness theorem: Baker (two logs), NOT Subspace/ESS 🔑

Greps of the full v1.44 text for *subspace*, *Evertse*, *Schlickewei*, *Schmidt*, *S-unit* come up
empty.  The pincer is:

| Step | Statement | Where |
|---|---|---|
| Upper bound (elementary) | `0 < Λ < Σ_{i} 1/x_i ≤ m / x_min ≤ m / X_0` | Lemma 4, Cor. 5 |
| Chaining | `x_{i+1} < b^δ x_i^δ` with `δ = log3/log2 = 1.58496`, `b = (1 + X_0^{-1})/2^{1/δ} = 0.64576` | Lemma 6 |
| Upper bound (exponential in K) | `0 < Λ < m c_m 2^{-((δ-1)/(δ^m - 1)) K}`, `c_m` decreasing from `c_2 = 0.76479` to `0.30577` | Lemma 7 |
| **Lower bound (transcendence)** | `Λ > e^{-13.3 (0.46057 + log K)}`, i.e. `Λ > (K+L)^{-13.3}` | **Lemma 12**, from **Rhin's Proposition p. 160** |
| Contradiction | `K < K_1(m)`, the largest root of `e^{-13.3(0.46057 + log x)} = m c_m 2^{-((δ-1)/(δ^m-1)) x}` | Lemma 14 |
| Lower bounds on K | generalized Crandall: `K > q_n` whenever `q_n + q_{n+1} ≤ (log 2) X_0 / m`, `q_n` = CF denominators of `δ` | Lemma 10, Cor. 11 |

`0.46057 = log δ`, so Lemma 12 is exactly `Λ > H^{-13.3}` with `H = K + L`.  They say explicitly:
*"For general linear forms x log a + y log b the best results today are LMN for small x,y and Matveev
for large x,y.  For our specific case x log 2 + y log 3 however, the result of Rhin is best."*

### 1.4 Why the method stalls at m ≈ 75 (and why that is not fixable by more compute)

`k_1(m) := K_1(m)/(m δ^m)` **decreases to `13.3 log δ / (log 2 (δ-1)) = 15.107`**, so

```
K < ~15.11 · m · δ^m           (upper bound, exponential in m)
K > (a fixed number from X_0)  (lower bound, from the CF of δ; e.g. K > 5.75e15 for 30 ≤ m ≤ 333)
```

The exponential rate in the upper bound is `(δ-1)/(δ^m - 1) ~ δ^{-m}`: each extra circuit costs a
factor `δ` in the exponent, so the pincer opens up geometrically.  The border `m = 75/76` in v1.44
is set *entirely* by `X_0 = 5 · 2^60 > 5.7646e18` (Oliveira e Silva).  Their own closing sentence:
*"To show the nonexistence of nontrivial m-cycles for essentially larger ranges of m an entirely new
idea seems to be needed."*

Two more numbers worth having: for `76 ≤ m ≤ 77` only 3 (resp. 4) candidate `(K,L)` pairs survive,
each killed by a specific future value of `X_0` (they project 2011-2040 for those); for `78 ≤ m ≤ 90`
the surviving candidate counts grow 6, 9, 12, 19, 33, ... , 1456.

---

## 2. Is there ANY published upper bound on `m`?  ❌ No.

Searched the SdW/Simons/Hercher/Brox line and the general Collatz-cycle literature.  Every
published constraint runs the **other** way:

| Result | Direction |
|---|---|
| Steiner 1977 (1-cycles), Simons 2005 (2-cycles), SdW 2005 (`m ≤ 68`), SdW 2010 (`m ≤ 75`), Hercher 2023 (`m ≤ 91`) | rules out **small** m, i.e. `m ≥ 92` from below |
| SdW Theorem 3(d) | bounds `K, L, x_min` **above in terms of m** (`K < 15.11 m δ^m`), never `m` |
| SdW Cor. 11 last line | `K > 1.7095 m` for `m ≥ 527 875 035`, i.e. `m < 0.585 K`: an upper bound on `m` **in terms of K**, and `K` is unbounded |
| Brox, *Collatz cycles with few descents*, Acta Arith. **92** (2000) 181-188 | finitely many m-cycles with `m < 2 log K`: again the **small-m** side |

**Structural reason, stated plainly.**  With `hercher_min_circuit_count` in hand (`m ≥ 92`), an
unconditional `C ≤ 91` **is** the no-nontrivial-cycle theorem, not a lemma on the way to it.  So
`Compression` at `C ≤ 91` is Front B in its second costume: the repo already killed the first
costume (`NaiveCompression ↔ FrontB`, the `wpow` degeneracy) and the `Primitive` repair fixed the
*statement*, but it did not lower the *strength* of what is being asked.  Nothing in the literature
separates "bound the circuit count" from "kill the cycles"; the entire frontier is the slow march up
the small-m side, one `X_0` doubling at a time.

Two consequences for the route board:

1. 🔴 **The `FRONT-B-ROUTES.md` Route 2 model needs a correction.**  It says the cycle equation is an
   S-unit equation whose term count is the (unbounded) cycle length, so ESS is vacuous and a
   compression would let "Simons-de Weger's machinery finish, since it already handles every bounded
   circuit count."  The second half is **false as stated**: SdW do not handle every bounded `m`.  They
   handle `m ≤ 75` and *cannot* close `m = 78` even with `m` known and bounded, because for each `m`
   the closure needs its own lattice search plus a large enough `X_0`.  What actually finishes a
   bounded-`m` hypothesis is **Hercher 2023** (`m ≤ 91`, no transcendence), which the repo already
   axiomatizes.  So the true statement is: compression to `C ≤ 91` closes Front B **via Hercher**, and
   compression to any `C ≥ 92` closes nothing at all today.
2. 🟡 The "what we would see in their library" line ("every integral cycle has at most C circuits,
   proved by a rearrangement or extremal argument on parity words") is not contradicted by anything I
   found, but there is zero literature scaffolding for it: no partial result, no conditional version,
   no heuristic.  Worth noting that the heuristic *shape* of a hypothetical cycle runs against it:
   odd-run lengths are geometric with mean 2, so a random cycle with `K ~ 10^17` odd steps would have
   `m ~ K/2`, astronomically far from 91.  A proof of `m ≤ 91` is therefore not "compressing a
   structure we expect to be compressible"; it is proving that a structure we expect to be huge cannot
   exist.  (Confidence 85% that this heuristic framing is right; it is the standard random-walk model.)

---

## 3. The 1-circuit case genuinely needs an effective transcendence input ✅ (confirmed, 95%)

Three independent write-ups, all agreeing:

- **Steiner 1977** (per SdW §1.4): (i) an inequality for `(k+l)/k`; (ii) a numerical lower bound on
  `k` forcing `(k+l)/k` to be a **convergent of `δ`**; (iii) **an upper bound for `k` from Baker's
  theorem on linear forms in two logarithms** (Baker, *Mathematika* **15** (1968) 204-216);
  (iv) a lower bound on the partial quotients of `δ`, contradicted by direct CF computation.
- **de Weger, *Algorithms for Diophantine Equations*, CWI Tract 65 (1989), p. 108** - this is the
  "1-cycle = Steiner" write-up the request asks about.  Via **Waldschmidt's** bound he (implicitly)
  proves that `1 < 2^{k+l}/3^k < 1 + 3^{-0.1 k}` has **no solutions for `k ≥ 32`**.  Simons 2005
  Remark 2 restates it as: `0 < (k+l) log 2 - k log 3 < 2^{-0.158 k}` has no solutions for `k ≥ 32`,
  and notes this *"can shorten the proof for the nonexistence of 2-cycles (and also Steiner's proof)"*.
- **SdW 2010** with `m = 1` runs the same pincer with Rhin's bound in place of Baker's.

🔑 **The useful nuance for `SteinerOneCircuit`.**  The one-circuit case does **not** need a polynomial
irrationality measure.  The trivial (Liouville) bound is `Λ > log(1 + 3^{-k}) ~ 2^{-1.585 k}`, and the
elementary upper bound is `Λ < 1/x_min ≤ 1/(2^k - 1)`.  So the *whole* transcendence content is
**beating Liouville's exponent 1.585 down below 1**; de Weger's `2^{-0.158 k}` beats it by a factor
of 10 and is the weakest published statement that suffices.  That is a materially smaller target than
the polynomial measure Front A needs.

If instead you feed Rhin's polynomial bound (`Λ > (k+l)^{-13.3}`, see the Front A findings) into the
one-circuit pincer, the contradiction `2^k - 1 ≥ (k+l)^{13.3}` with `k+l = ⌈δ k⌉` first bites at

```
k ≥ 97          (verified by exact integer arithmetic; k = 96 fails, k = 97 holds)
```

leaving `k < 97` to Steiner's finite continued-fraction check.  That is a clean, fully explicit split
for a Lean attack on `OneCircuit`.

---

## 4. What this changes for the repo

- ✅ **Answered**: the SdW structure is a two-log Baker pincer over an `m x m` linear system, closed
  by Rhin's explicit Padé bound.  There is no S-unit decomposition to formalize and no ESS input.
- 🔴 **Correct `FRONT-B-ROUTES.md` Route 2**: "SdW already handles every bounded circuit count" is
  false; Hercher is what closes a bounded-`m` hypothesis, and only for `C ≤ 91`.
- ❌ **No upper bound on `m` exists**, published or conditional.  `Compression` remains
  Front-B-equivalent in strength.  Recommend it stay on hold and that `FRONT-B-ROUTES.md` record the
  equivalence explicitly, so a future lap does not re-open it as if it were a lemma.
- 🔁 **Both fronts now share one deep input.**  Front A's `sep_two_three` and Front B's
  `SteinerOneCircuit` both reduce to an effective lower bound on `|u_1 log 2 + u_2 log 3|`.  One
  disclosed Rhin-grade axiom would serve both.  See
  `ON-LINE-FINDINGS-2026-08-25-log23-effective-measure.md`.
