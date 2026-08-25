# ON-LINE-FINDINGS 2026-08-25 (later) - the exact Rhin/Wu two-log construction

Answers the `2026-08-25 (later) — SHARPENED` entry of `ON-LINE-REQUEST.md`.  Host session,
2026-08-24 (host clock).  **Read `ON-LINE-FINDINGS-2026-08-25-log23-effective-measure.md` first** -
it answers items 1 and 3 of this block already (constants, `C`-bump, why Bennett-Bugeaud is off-path).
This file adds the three things that one did not have: **Rhin's actual exponents**, the **exact
kernel**, and the **explicit `H₀(ε)` machinery**.
> 🔴 **SUPERSEDED IN PART (2026-08-25): the Rhin paper is now ON-BOX and read firsthand** (`papers/rhin-1987-pade-mesures-effectives.pdf`).  The threshold on the explicit bound is **`H ≥ 2`** (nothing hidden), `H = max(|u₁|,|u₂|)`, and Wu's `Q₆` is a typo.  Read **`ON-LINE-FINDINGS-2026-08-25-rhin-primary-source-verified.md` first**; where the two disagree, that one wins.


Your read is confirmed on both counts: the proven object is Rhin's linear-independence measure of
`{1, log 2, log 3}`, and **Voutier 2111.01044 is off-path** (roots of rationals, not logs).

---

## 1. `c`, `τ`, `H₀` - the numbers you asked for

| Quantity | Value | Provenance |
|---|---|---|
| `τ` (explicit form) | **13.3** | Rhin 1987, Proposition p. 160 |
| `c` (explicit form) | **1** - the bound is a bare `H^{-13.3}`, no constant in front | quoted verbatim, twice: SdW v1.44 Lemma 12, Simons arXiv:2205.10582 Lemmas 10/13 |
| `H` | `max(|u₀|, |u₁|, |u₂|)` | ditto |
| `H₀` (explicit form) | ✅ **`H ≥ 2`** (Rhin p. 160, read firsthand 2026-08-25) | primary-source doc |
| `τ` (asymptotic form) | **7.616 + ε** (`ν(1, log2, log3) < 7.616`) | Rhin 1987, reported in Wu 2003 §1 |
| `H₀(ε)` (asymptotic form) | explicit formula exists, see §4 | Wu 2003, Lemma 1 proof, pp. 903-904 |

So: `|q₀ + q₁ log 2 + q₂ log 3| ≥ H^(-13.3)` is the honest, constant-free, `ε`-free statement, and
it is what fixes your exponent.  **`C = 15` with threshold `k ≥ 400`** (derivation, tables and the
`crossover_400` restatement are in the companion findings doc §3).

⚠️ **Your new `pow_le_two_pow_gen` (`k^C ≤ 2^k` for `k ≥ C²`, `C ≥ 4`) is lossy here.**  At `C = 15`
the downstream need is `k^45 ≤ 2^k`, so that lemma gives `k ≥ 2025`, while the exact crossover is
**`k = 387`** (verified by integer arithmetic, `experiments/sep_two_three_constants.py`).  Using the
general lemma inflates the finite check from 270 pairs to ~1900, with `3^2024 ≈ 10^966` at the top
end.  Recommend a `decide`-backed exact threshold for the one exponent you actually need.

---

## 2. 🔑 Rhin's polynomial, with the exponents

Wu 2003 gives Rhin's six factors but **not** the exponents.  Zudilin, *An essay on irrationality
measures of pi and other logarithms* (arXiv:math/0404523), **§3.4**, gives them explicitly.  Rhin
builds simultaneous approximations to `log a₁`, `log a₂` with `a₁ = 2/3`, `a₂ = 4/3`, `d = 3`, using

```
H_n(z) = 2^14 · 3^(2n+7)
       · (z − 1)^⌊0.704324 n⌋
       · (z − 2/3)^⌊0.552418 n⌋
       · (z − 4/3)^⌊0.447582 n⌋
       · (5z − 4)^⌊0.109072 n⌋
       · (17z² − 34z + 16)^⌊0.038934 n⌋
       · (19z² − 36z + 16)^⌊0.054368 n⌋
```

**Cross-verified against Wu's independent statement of the same construction.**  Wu eq. (1.4) lists
the factors at the `x = 3z` scale: `Q₁ = x−2`, `Q₂ = x−3`, `Q₃ = x−4`, `Q₄ = 5x−12`,
`Q₅ = 17x²−102x+144`, `Q₆ = 19x²−104x+144` ⚠️ **(Wu's `−104` is a TYPO; Rhin p. 162 has `−108`)**.
Substituting `x = 3z` maps each of Zudilin's factors
onto exactly one of Wu's, up to the powers of 3 that the `3^{2n}` prefactor absorbs:

| Zudilin (z-scale) | Wu (x-scale) | exponent |
|---|---|---|
| `z − 2/3` | `Q₁ = x − 2` | 0.552418 |
| `z − 1` | `Q₂ = x − 3` | 0.704324 |
| `z − 4/3` | `Q₃ = x − 4` | 0.447582 |
| `5z − 4` | `Q₄ = 5x − 12` | 0.109072 |
| `17z² − 34z + 16` | `Q₅ = 17x² − 102x + 144` | 0.038934 |
| `19z² − 36z + 16` | `Q₆ = 19x² − 108x + 144` ⚠️ (Wu prints `−104`; Rhin p. 162 confirms `−108`) | 0.054368 |

⚠️ **Correction (2026-08-25)**: the `Q₆` row is where Wu and Rhin/Zudilin part company, and my
original "all six match" claim was a mis-multiplication.  Rhin is the arbiter and Zudilin agrees with
him.  Everything else below stands, and the exponents satisfy, **exactly**,

```
Σ bᵢ · deg Qᵢ = 0.552418 + 0.704324 + 0.447582 + 0.109072 + 2(0.038934) + 2(0.054368) = 2.000000
```

i.e. `deg H_n = 2n`, which is precisely the degree condition the construction requires.  That the six
factors match under `x = 3z` **and** the exponents sum to exactly 2 is strong independent evidence the
two sources describe the same object and that the digits are transcribed correctly (confidence 95%).

---

## 3. The kernel: NOT the Beukers `∫₀¹ xᵅⁿ(1−x)ᵝⁿ … dx` shape ❌

Your guess was the ζ(3)-style single integral.  The actual family (Zudilin (24), = Wu's `Iₙ`) is

```
I(n; a_j) = (1 − a_j) ∫₀¹  H_n( d − d(1 − a_j)x )  /  [ dⁿ (1 − (1 − a_j)x)^(n+1) ]  dx     (j = 1,2)
```

with `d = 3`, `a₁ = 2/3`, `a₂ = 4/3`.  The substitution `z_j = d − d(1−a_j)x` turns these into the
clean x-scale form Wu uses,

```
I_n(a_i, a_{i+1}) = ∫_{a_i}^{a_{i+1}}  H_n(x) / xⁿ  ·  dx/x        over [2,3] and [3,4]
```

so the object being made small is `max_{z ∈ [2,3] ∪ [3,4]} |H_n(z)/z|^{1/n}`, and the whole design
problem is the **integer transfinite diameter** of `[2,4]` with the weight `1/z`.  Two consequences
for a Lean leg-2:

- The integrand is a **Padé-type approximant to the logarithm**, not a Beukers ζ(3) integral.  It is
  still an explicit real integral of an explicit algebraic integrand over `[0,1]` after the change of
  variables, so the same *style* of proof works; only the integrand differs.
- The extra factors `Q₄, Q₅, Q₆` are load-bearing, not decoration.  Without them the construction
  is **infeasible**, not merely weaker: the plain choice `(x−2)ⁿ(x−3)ⁿ(x−4)ⁿ` gives `τ = 1.830` against
  `K = 2`, i.e. the remainders do not beat the denominators at all.  With Rhin's six factors,
  `τ = 1.404` against `K = 1`.  (Both computed here, `experiments/rhin_mu_wu_framework.py`.)

### 3.1 If you want a Beukers-shaped warm-up first

For `log 2` alone the Beukers-style kernel does exist and is the exact analogue of the
public [`ahhwuhu/zeta_3_irrational`](https://github.com/ahhwuhu/zeta_3_irrational) integral:

```
D_n ∫₀¹ ( x(1−x)/(1+x) )ⁿ  dx/(1+x)  ∈  ℤ log 2 + ℤ,        D_n = lcm(1..n)
```

and more generally `D_n ∫₀¹ G_n( x(1−x)/(1+x) ) dx/(1+x) ∈ ℤ log 2 + ℤ` for any `G_n ∈ ℤ[y]` of
degree `≤ n` (Zudilin §3.2).  That is a much smaller first target with the same three legs, and it
exercises exactly the `lcm(1..n)` brick you already landed in `Gelfond.lean`.  It will **not** give a
two-log bound, so it is a warm-up, not a route.

---

## 4. Integrality (leg 3) and the explicit `H₀(ε)` (Wu Lemma 1)

**Leg 3, integrality.**  `H_n(z) ∈ ℤ[z]` of degree `≤ 2n` must have the shape (Zudilin (23))

```
H_n(z) = Σ_{ν=0}^{n} B_ν Δ^(n−ν) z^ν  +  Σ_{ν=n+1}^{2n} B_ν z^ν,     B_ν ∈ ℤ
```

where `Δ` is a common multiple of the numerators `c_j` and the denominator `d` (here: of `2, 4, 3`).
Term-by-term integration then gives `I(n; a_j) · D_n = −B_n log a_j + A_{n,j} ∈ ℤ log a_j + ℤ` with
`D_n = lcm(1, …, n)`.  In Wu's Theorem 2 the same condition reads `H_n ∈ (Δ, x)ⁿ ℤ[x]` with
`Δ = gcd(a₁,…,a_m)` **as printed**.

⚠️ **Exact-audit correction (2026-08-26): Wu's printed `gcd` is untenable.**  The same theorem also
prints `Dₙ=gcd(1,...,M)`, which would always equal one despite the subsequent claim `K>0`.  More
importantly, negative endpoint powers in the displayed termwise integral are not integral with a
gcd endpoint scale.  Both occurrences must be read as common multiples/LCMs.  Rhin's six weights
confirm this internally: the contents of `Qᵢ(12x)` have exact weighted `(v₂,v₃)=(2,1)`, so the
product lies in `(12,x)ⁿ`, with `12=lcm(2,3,4)` and the printed `12⁷` covering floor losses.  See
`CollatzMoonshot/FrontA/RhinKernel.lean` and `FRONT-A-RHIN-LITE.md`.

**Historical note (superseded by the correction above).**  Feeding
Rhin's exponents into Wu's `μ = (τ⁽⁰⁾ + K)/(τ − K)` with `Δ = 1` gives

```
K = 1,   τ⁽¹⁾ = 1.4399,   τ⁽²⁾ = 1.4042,   τ = 1.4042,   τ⁽⁰⁾ = 2.8813   →   ν ≈ 9.60
```

against Rhin's published `ν < 7.616`.  Feasible (`τ > K` ✅, so the construction is confirmed to work
at these exponents), but **lossy by ≈ 2**.  This diagnosis was made before the `Q₆` typo was found;
the gap was caused by `−104` versus Rhin's correct `−108`, not by a missing analytic gain.  The
`Δ`-divisibility is nevertheless genuinely required for integrality and is supplied by the exact
content balances.

**The explicit `H₀(ε)`.**  Wu's Lemma 1 (pp. 903-904, read from the rendered PDF, not OCR) constructs
it.  With `σ = lim (1/n) log|r_n|`, `τ = min_i τ⁽ⁱ⁾`, `m` the number of forms, and
`δ ≡ δ(ε) ∈ ]0, τ/6[` chosen so that `(σ+δ)/(τ−3δ) < σ/τ + ε/2`:

```
H₀(ε) = min{ N ≥ 1 :  N^(ε/2)   ≥ 2 e^(σ+δ) (2m)^((σ+δ)/(τ−δ))
                 and  N^(ετ/4)  ≥ (2 e^(σ+δ))^(τ+σ) m^(σ+δ) }
N(H)  = min{ N > n(ε) :  2mH < e^((τ−δ)N) }
```

giving `|p + q₁γ₁ + … + q_mγ_m| ≥ H^(−σ/τ−ε)` for `H = max_i|q_i| ≥ H₀(ε)`.

🚨 **The catch, stated plainly**: `H₀(ε)` above is explicit in `(σ, τ, m, ε)` **and `n(ε)`**, where
`n(ε)` is the index past which `e^(σ−δ)n ≤ |r_n| ≤ e^(σ+δ)n` and `max_i|ε_n^(i)| ≤ e^(−(τ−δ)n)`
actually hold.  Those are *limits* in Lemma 1's hypotheses, so `n(ε)` is not delivered by the lemma;
making it explicit means effective two-sided asymptotics for the integral and for `B_n` at Rhin's
exponents.  That is the real work in a formalization, and it is the same work that Rhin must have
done to state his p. 160 Proposition without an `ε`.

---

## 5. Item 3: a separately published `μ(log₂3)`?  No. ❌

Searched; found none.  The ratio's measure is only ever obtained from the two-log form.  With
`u₀ = 0`, `u₁ = −p`, `u₂ = q`, `|q log 3 − p log 2| = (log 2) q |δ − p/q|` and `H ≈ δq`:

```
μ(log₂3) ≤ 14.3        explicit, effective, no threshold caveat beyond Rhin's own (§1)
μ(log₂3) ≤ 8.616 + ε   asymptotic, past the unpublished H₀(ε)
```

⚠️ **Do not use Zudilin's Theorem 3 (`μ(γ) < 8.616` for `γ ∈ ℚ log2 + ℚ log3`) as a two-log bound.**
That is a statement about approximating a *single fixed* `γ` by rationals, with a `γ`-dependent
constant; our `Λ = m log 2 − k log 3` has a coefficient ratio that varies with `k`, so the family of
2-term measures does not assemble into a homogeneous 2-log bound.  The genuine 3-term linear
independence measure (`7.616`, or the explicit `13.3`) is the only thing that applies.  Same trap
kills any attempt to chain `μ(log 2) ≤ 3.57` and `μ(log 3) ≤ 5.116`.

---

## 6. Net effect on the plan

- ✅ You now have Rhin's exact approximant family, cross-verified two ways, and the exact kernel.
- ✅ `c = 1`, `τ = 13.3` fixes the honest exponent: **`C = 15`, `k ≥ 400`**, exact crossover 387.
- ⚠️ `H₀` for the explicit form is still unfetched, and it is the one thing that could move the
  threshold.  Rhin, Progr. Math. **71** (1987) 155-164, Proposition p. **160** - paywalled Birkhäuser
  chapter, DOI `10.1007/978-1-4757-4267-1_11`.  Hand-download ask.
- 🟡 Formalizing the construction end-to-end is an expedition (integer transfinite diameter, effective
  asymptotics for `n(ε)`).  The proportionate move remains: disclose one named Rhin-grade axiom, keep
  the machine-checked reduction, and note that the same axiom also discharges Front B's
  `SteinerOneCircuit` for `k ≥ 97`.
