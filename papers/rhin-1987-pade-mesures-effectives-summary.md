# Rhin 1987 - "Approximants de Padé et mesures effectives d'irrationalité"

## Provenance
- **Author**: Georges Rhin (Université de Metz).
- **Venue**: *Séminaire de Théorie des Nombres, Paris 1985-86* (ed. Catherine Goldstein), **Progress
  in Mathematics 71**, Birkhäuser Boston 1987, **pp. 155-164**.  DOI `10.1007/978-1-4757-4267-1_11`.
- **Working PDF**: `papers/rhin-1987-pade-mesures-effectives.pdf` (gitignored and not redistributed);
  whole-volume working filename `papers/seminaire-theorie-nombres-paris-1985-86.pdf`. Read via
  institutional access on SpringerLink on 2026-08-24.
- ⚠️ The PDF is an **Acrobat Paper-Capture OCR scan** - its text layer mangles accents and math.
  **Read the rendered pages**, do not trust `pdftotext` here.

## The Proposition (p. 160) - why this paper was reviewed

> Soient `u₀, u₁, u₂` trois entiers tels que `H = max(|u₁|, |u₂|) ≥ 2`.  Alors la forme
> `Λ = u₀ + u₁ log 2 + u₂ log 3` vérifie **(7) `|Λ| ≥ H^{-13.3}`**.  De plus pour `H ≥ H₀`
> (`H₀` effectivement calculable) **(8) `|Λ| ≥ H^{-7.616}`**.

- 🔑 **Threshold `H ≥ 2`** - no hidden constraint, so small-`H` applications are fine.
- 🔑 **`u₀` is not in the max.**
- (8) has **no `ε`**, but its `H₀` is asserted-calculable and **never stated**, so (7) is the operative
  bound for any formal use.
- 💡 Same page: *"la méthode de Baker donne ici `2^50` au lieu de 13,3"*.  (7) rests on best
  simultaneous approximations for `q ≤ 7.32 × 10¹²` computed by E. Dubois and P. Toffin (Macsyma).

## Appendix item 2 (p. 162) - the polynomial behind (8)

`∫₂³ Hₙ(x)/x^{n+1} dx` and `∫₃⁴ Hₙ(x)/x^{n+1} dx` with `Hₙ(x) = 12⁷ ∏_{i=1}^{6} Qᵢ(x)^{[bᵢn]}`:

| `Q₁ = x−3` | `Q₂ = x−2` | `Q₃ = x−4` | `Q₄ = 5x−12` | `Q₅ = 17x²−102x+144` | `Q₆ = 19x²−108x+144` |
|---|---|---|---|---|---|
| 0.704324 | 0.552418 | 0.447582 | 0.109072 | 0.038934 | 0.054368 |

⚠️ **Wu 2003 eq. (1.4) prints `Q₆ = 19x²−104x+144` - a typo.**  Rhin has `−108` and Zudilin agrees.
Rhin's own N.B.: *"Les calculs peuvent être vérifiés facilement sur un micro ordinateur."*  Done:
`experiments/rhin_eval_at_rhin_exponents.py` gives `μ = 7.61593` with `−108` (and `9.602` with `−104`).

## Appendix item 1 (p. 161) - a smaller worked example
The `μ(log 2) = 4.0765` polynomial: `Hₙ(1+t) = ∏_{i=1}^{6} 2 Pᵢ(t)^{[aᵢn]}`, `P₁ = t(1−t)`,
`P₂ = t²+2t−1`, `P₃ = 6t²−5t+1`, `P₄ = 7t²−6t+1`, `P₅ = 13t²−11t+2`, `P₆ = 2t⁴+3t³+3t²−5t+1`,
`a = (0.84943, 0.02401, 0.091, 0.02068, 0.0113, 0.00179)`.  Single-log, known answer - a good rehearsal.

**Working notes**: `ON-LINE-FINDINGS-2026-08-25-rhin-primary-source-verified.md`.
