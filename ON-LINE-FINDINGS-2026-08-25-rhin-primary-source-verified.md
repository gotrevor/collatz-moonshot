# ON-LINE-FINDINGS 2026-08-25 - Rhin 1987 READ FIRSTHAND: threshold resolved, Wu typo found

Trevor hand-downloaded the paywalled chapter (Cornell institutional access) on 2026-08-24.  **The
primary source is now on-box**: `papers/rhin-1987-pade-mesures-effectives.pdf` (10 pp., pp. 155-164;
gitignored), plus the whole volume as `papers/seminaire-theorie-nombres-paris-1985-86.pdf`.
Read as rendered pages (the PDF is an Acrobat Paper-Capture OCR scan, so its text layer is not
trustworthy for math).

**This supersedes the "threshold unknown" caveat in the two earlier Front A findings docs.**

---

## 1. 🎉 The Proposition, p. 160, verbatim

> **Proposition.**  Soient `u₀, u₁, u₂` trois entiers tels que `H = max(|u₁|, |u₂|) ≥ 2`.  Alors la
> forme `Λ = u₀ + u₁ log 2 + u₂ log 3` vérifie
>
> (7) `|Λ| ≥ H^(-13.3)`.
>
> De plus pour `H ≥ H₀` (`H₀` effectivement calculable)
>
> (8) `|Λ| ≥ H^(-7.616)`.

Three things settled:

1. 🚨 **The threshold on (7) is `H ≥ 2`.**  Nothing large, nothing hidden.  **The `C = 15`,
   `k ≥ 400` instantiation is sound** (our `H = m ≈ 634`).  The open question from the earlier docs is
   closed; no finite check needs to grow to cover a mystery threshold.
2. **`H = max(|u₁|, |u₂|)` - `u₀` is NOT in the max.**  Our application has `u₀ = 0`, `u₁ = m`,
   `u₂ = -k`, and `m > k`, so `H = m` exactly as assumed.  Simons-de Weger's "H = u₁ = K+L" is the
   same reading.
3. **(8) carries no `ε`**: it is a clean `H^(-7.616)`, not `H^(-7.616-ε)`.  `H₀` is asserted
   "effectivement calculable" but **not stated**, so (8) remains unusable for a formal proof and (7)
   remains the operative bound.  (Wu's `ν < 7.616` phrasing adds the `ε` from his own definition.)

Also on the page, worth having:

- **"La méthode de Baker donne ici `2^50` au lieu de 13,3."**  Rhin's own comparison: Baker's method
  gives exponent `2^50 ≈ 1.13 × 10^15` for this pair.  Use that number, not my earlier
  Baker-Wüstholz estimate of `≈1.4 × 10^9`, when contrasting the two.
- The proof of (7) uses the best simultaneous approximations `q log 2 − p₁`, `q log 3 − p₂` for
  `q ≤ 7.32 × 10^12`, computed by **E. Dubois and P. Toffin** (Macsyma, Dubois's algorithm).
- (8) improves in particular E. Reyssat's irrationality measure for `log 3`.

---

## 2. 🚨 Wu 2003 eq. (1.4) has a typo in `Q₆`, and it matters

Rhin's Appendix item 2 (p. 162) gives the polynomial for (8) directly, in the same `x`-scale Wu uses:

> Pour démontrer (8) on étudie les deux intégrales `∫₂³ Hₙ(x)/x^(n+1) dx` et `∫₃⁴ Hₙ(x)/x^(n+1) dx`
> où `Hₙ(x) = 12^7 ∏_{i=1}^{6} Qᵢ(x)^([bᵢ n])` avec

| | `Qᵢ` | `bᵢ` |
|---|---|---|
| `Q₁` | `x − 3` | 0.704324 |
| `Q₂` | `x − 2` | 0.552418 |
| `Q₃` | `x − 4` | 0.447582 |
| `Q₄` | `5x − 12` | 0.109072 |
| `Q₅` | `17x² − 102x + 144` | 0.038934 |
| `Q₆` | **`19x² − 108x + 144`** | 0.054368 |

> N.B. : Les calculs peuvent être vérifiés facilement sur un micro ordinateur.

**Wu 2003 prints `Q₆ = 19x² − 104x + 144`.**  Rhin has **`−108`**, and Zudilin's `z`-scale factor
`19z² − 36z + 16` maps under `x = 3z` to `19x² − 108x + 144`, agreeing with Rhin.  So **Wu's `−104` is
a typo**, and it is not cosmetic: `−104` gives discriminant `−128` (complex roots), `−108` gives `+720`
(real roots inside `[2,4]`, which is the whole point of the factor).

⚠️ **Correction to the earlier findings doc**: it stated the Zudilin-to-Wu factor match was exact for
all six.  It is exact for `Q₁..Q₅` only; I mis-multiplied on `Q₆` and reported a match that was not
there.  Rhin is the arbiter and Zudilin agrees with him.

---

## 3. ✅ End-to-end verification: the framework reproduces 7.616

Taking Rhin's own text as N.B. suggests, `experiments/rhin_eval_at_rhin_exponents.py` evaluates Wu's
Theorem 2 formula `μ = (τ⁽⁰⁾ + K)/(τ − K)` at Rhin's exponents:

```
Σ bᵢ · deg Qᵢ = 2.000000        (deg Hₙ = 2n, as required)
K = 1                            (Dₙ = lcm(1..n))
τ⁽¹⁾ = τ⁽²⁾ = 1.509760           (the two intervals are BALANCED - the signature of an optimum)
τ⁽⁰⁾ = 2.882297
μ = 7.61593                      vs Rhin's published 7.616 ✅
```

With Wu's typo'd `Q₆` the same script gives `τ⁽¹⁾ = 1.4399 ≠ τ⁽²⁾ = 1.4042` (unbalanced) and
`μ = 9.602`.  The balance test alone would have caught the typo.

**Consequences:**

- ⚠️ **Retract the `Δ`-divisibility hypothesis.**  The earlier doc guessed that the `9.60 vs 7.616`
  gap came from dropping the ideal condition `Hₙ ∈ ((x,Δ)ℤ[x])ⁿ`.  That was wrong: the gap was
  entirely the typo, and the plain `Δ = 1`, `K = 1` reading of Wu's Theorem 2 is **exactly right**.
- ✅ The `μ` model is now a **trusted instrument**, verified against a published constant.  It can be
  used to explore variants (different factor sets, different `bᵢ`) with confidence.
- ✅ Legs 2 and 3 have a fully specified, reproducible target: integrand, exponents, denominators, and
  a numeric check that the assembled constants are right.

---

## 4. Rhin's own machinery, for the record (pp. 159-160)

Single-log setup: `d` a positive integer with `dz` integral, `Δ = ppcm(d, d−dz)`, `Hₙ ∈ ℤ[x]` of
degree `≤ 2n` in the ideal `((x, Δ)ℤ[x])ⁿ`, hence

```
Hₙ(x) = Σ_{j=0}^{n} bⱼ Δ^(n−j) x^j  +  Σ_{j=n+1}^{2n} bⱼ x^j        (bⱼ ∈ ℤ)
Iₙ = ∫₀¹ Hₙ(d − dzt) / ( dⁿ (1 − zt)^(n+1) ) dt
−z Iₙ = bₙ log(1−z) + Σ_{j=n+1}^{2n} (bⱼ/(j−n))((d−dz)^(j−n) − d^(j−n))
                    − Σ_{j=0}^{n−1} (bⱼ/(n−j))((Δ/(d−dz))^(n−j) − (Δ/d)^(n−j))
```

so with `dₙ = ppcm(1,…,n)` one gets `−z dₙ Iₙ ∈ ℤ log(1−z) + ℤ`; `bₙ` comes from a contour integral;
from `0 < |Iₙ| ≤ e^(an)` and `|bₙ| ≤ e^(bn)` plus **an explicit prime-number-theorem bound on `dₙ`**,
`μ(log(1−z)) = −(b+1)/(a+1) + 1` when `a < −1`.  Multi-log (`α₁,…,α_r` rational, `log(1−αᵢ)`
ℚ-linearly independent with `1`): same `Hₙ`, `Iₙ(αᵢ) = ∫₀¹ Hₙ(d − dαᵢt)/(dⁿ(1 − αᵢt)^(n+1)) dt`, and
`d_{rn} Iₙ(αᵢ) = P_{n,i} − d bₙ log(1−αᵢ)`.  **Studying `log(2/3)` and `log(4/3)` gives the
Proposition.**

📌 **Appendix item 1** gives a second fully worked example, the polynomial behind `μ(log 2) = 4.0765`:
`Hₙ(1+t) = ∏_{i=1}^{6} 2 Pᵢ(t)^([aᵢ n])` with `P₁ = t(1−t)`, `P₂ = t²+2t−1`, `P₃ = 6t²−5t+1`,
`P₄ = 7t²−6t+1`, `P₅ = 13t²−11t+2`, `P₆ = 2t⁴+3t³+3t²−5t+1` and `a = (0.84943, 0.02401, 0.091,
0.02068, 0.0113, 0.00179)`.  Useful as a smaller single-log rehearsal with a known answer.

---

## 5. Net effect

- ✅ **`C = 15`, threshold `k ≥ 400`, finite check `6 ≤ k < 400`** is sound and fully sourced.  The
  only remaining input is the Proposition itself, which is now a paper on the shelf rather than a
  citation.
- ✅ The same bound discharges Front B's `SteinerOneCircuit` for `k ≥ 97`.
- 🟡 If you ever want the sharper `7.616`, the missing piece is `H₀` in (8), which Rhin asserts is
  effectively calculable but does not compute.  Deriving it means effective two-sided asymptotics for
  `Iₙ` and `bₙ` at the exponents in §2 - real work, but now fully specified.
