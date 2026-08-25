# Zudilin - "An essay on irrationality measures of pi and other logarithms"

## Provenance
- **Author**: Wadim Zudilin.  **Source**: arXiv:math/0404523.
- **Local PDF**: `papers/zudilin-2004-irrationality-measures-logs.pdf` (gitignored).
  **Verified firsthand 2026-08-24** (host session).

## Why it was reviewed
It carries **the one datum that Wu 2003 omits**: Rhin's actual exponents.  §3.4 states Rhin's
polynomial in full,

```
H_n(z) = 2^14 · 3^(2n+7) · (z−1)^⌊0.704324n⌋ (z−2/3)^⌊0.552418n⌋ (z−4/3)^⌊0.447582n⌋
       · (5z−4)^⌊0.109072n⌋ (17z²−34z+16)^⌊0.038934n⌋ (19z²−36z+16)^⌊0.054368n⌋
```

for simultaneous approximations to `log(2/3)` and `log(4/3)`, yielding **Theorem 3**: `μ(γ) < 8.616`
for every nonzero `γ ∈ ℚ log 2 + ℚ log 3`.  Under `x = 3z` these are exactly Wu's `Q₁..Q₆`, and the
exponents sum to `Σ bᵢ deg Qᵢ = 2.000000` (i.e. `deg H_n = 2n`) - two independent confirmations that
the transcription is right.

## Other useful pieces
- **§3.3** the general integral family `I(n; a_j) = (1−a_j)∫₀¹ H_n(d − d(1−a_j)x)/(dⁿ(1−(1−a_j)x)^{n+1}) dx`
  and the **integrality condition (23)** (`H_n(z) = Σ_{ν≤n} B_ν Δ^{n−ν} z^ν + Σ_{ν>n} B_ν z^ν`), which
  is the `Δ`-divisibility gain that a naive `Δ = 1` reading of Wu's formula loses.
- **§3.2** the Beukers-shaped `log 2` kernel `D_n ∫₀¹ (x(1−x)/(1+x))ⁿ dx/(1+x) ∈ ℤ log 2 + ℤ` - the
  closest analogue of the `zeta_3_irrational` integral, and a sane formalization warm-up.
- **Propositions 1 and 2** the linear-form-to-measure criteria (`μ ≤ 1 + C₁/C₀`).
- ⚠️ **Theorem 3 is a 2-term statement** (single `γ` vs rationals, `γ`-dependent constant).  It does
  **not** give a homogeneous two-log bound; only the 3-term linear independence measure does.

**Working notes:** `ON-LINE-FINDINGS-2026-08-25-rhin-wu-explicit-construction.md`.
