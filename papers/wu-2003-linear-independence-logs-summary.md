# Wu - "On the linear independence measure of logarithms of rational numbers"

## Provenance
- **Author**: Qiang Wu.
- **Venue**: *Mathematics of Computation* **72** (2003), no. 242, 901-911, S 0025-5718(02)01442-4.
- **Source**: free AMS PDF.  **Local**: `papers/wu-2003-linear-independence-logs.pdf` (gitignored).
  **Verified firsthand 2026-08-24** (host session).

## Why it was reviewed
It is the **free, complete write-up of the Rhin/Padé machine** that produces effective lower bounds
for `|u₀ + u₁ log 2 + u₂ log 3|`, i.e. the sole deep input behind Front A's `sep_two_three` (and,
via `Λ = m log 2 - k log 3`, the effective irrationality measure of `log₂3`).

## The two facts to remember
1. **Rhin's constants, reported here** (§1): the best known linear independence measure of
   `1, log 2, log 3` is **`< 7.616`** (asymptotic, threshold `H₀(ε)` unpublished), giving the best
   known `μ(log 3) ≤ 8.616`.  The **fully explicit** companion, used by Simons-de Weger, is the
   Proposition on **p. 160** of the same Rhin paper: `|u₀ + u₁ log 2 + u₂ log 3| ≥ H^{-13.3}`.
2. **Theorem 2** is the general machine: `Hₙ ∈ (Δ,x)ⁿ ℤ[x]`, `Iₙ = ∫ Hₙ(x)/xⁿ dx/x` over consecutive
   `[aᵢ, aᵢ₊₁]`, denominators cleared by `Dₙ = lcm(1..max(n, deg Hₙ - n))` with `K = lim (1/n) log Dₙ`,
   remainder decay `τ⁽ⁱ⁾`, coefficient growth `τ⁽⁰⁾` from a Cauchy contour, and the measure
   `μ = (τ⁽⁰⁾ + K)/(τ - K)` provided `τ > K`.  **Lemma 1** is the generic criterion underneath and is
   where the effective `H₀(ε)` gets built.

## Rhin's explicit data for `(1, log 2, log 3)` (Wu eq. (1.4))
`a = (2,3,4)`; `Hₙ = b₀ Π Qᵢ^{[bᵢn]}` with `Q₁ = x-2`, `Q₂ = x-3`, `Q₃ = x-4`, `Q₄ = 5x-12`,
`Q₅ = 17x²-102x+144`, `Q₆ = 19x²-104x+144`; integrals over `[2,3]` and `[3,4]`.
⚠️ **The exponents `bᵢ` are in Rhin's paper, not here** - the one datum still unfetched.

**Full working notes, the `C = 15` bump, and the recommended Lean shape:**
`ON-LINE-FINDINGS-2026-08-25-log23-effective-measure.md`.

## Companion PDF fetched in the same session
- `papers/bennett-bugeaud-2012-quadratic-irrationals.pdf` - Bennett & Bugeaud, *Effective results for
  restricted rational approximation to **quadratic irrationals***, Acta Arith. **155** (2012) 259-269.
  ❌ **Not relevant to `log₂3`**: it bounds `‖bⁿ ξ‖` for `ξ` a real *quadratic* irrational.
