# Simons & de Weger - "Theoretical and computational bounds for m-cycles of the 3n+1 problem"

## Provenance
- **Authors**: John L. Simons (Groningen), Benne de Weger (Eindhoven).
- **Venue**: version 1.3 = *Acta Arithmetica* **117** (2005) 51-70, doi `10.4064/aa117-1-3`.
  ⚠️ **The live document is version 1.44, 31 Aug 2010**, which supersedes the published paper
  (`m ≤ 68` becomes `m ≤ 75`, every table improved, thanks to computations by Oliveira e Silva).
- **Source**: `deweger.net/papers/[35a]SidW-3n+1-v1.44[2010].pdf`.
- **Local PDF**: `papers/simons-deweger-2010-m-cycles-v144.pdf` (gitignored).
  **Verified firsthand 2026-08-24** (host session) - this summary is from the PDF, not from
  citations of it.

## Vocabulary map to this repo
Their `m` = `circuits v`; `K` = total odd steps (`ones v`); `L` = total even steps; `x_i` the local
minima, `y_i` the local maxima; `k_i`, `l_i` the odd/even run lengths; `δ = log 3 / log 2`;
`X_0` = the verified lower bound on `x_min` (`5 · 2^60` in v1.44).

## Main theorem (Thm 3)
(a) For every `m` there are only finitely many m-cycles (extends Brox).
(b) No nontrivial m-cycles for `1 ≤ m ≤ 75`.
(c) `76 ≤ m ≤ 77`: an explicit list of 3 resp. 4 candidate `(K, L)` pairs, each killed by a specific
future value of `X_0`.
(d) `m ≥ 78`: explicit bounds, all of the shape `K < ~15.11 · m · δ^m`.

## Method in one line
A **two-logarithm Baker pincer** on `Λ = (K+L) log 2 - K log 3`: an elementary upper bound
exponentially small in `K` (rate `(δ-1)/(δ^m - 1) ~ δ^{-m}`) against **Rhin's explicit lower bound**
`Λ > (K+L)^{-13.3}` (Lemma 12, from Rhin 1987 Prop. p. 160), plus a generalisation of Crandall's
lemma giving `K > q_n` from the continued fraction of `δ`, plus a lattice search for `69 ≤ m ≤ 90`.

## What it does NOT use
No S-unit equation, no subspace theorem / Evertse-Schlickewei-Schmidt, no growing number of
`2^s 3^t` terms.  For fixed `m` the cycle is an `m × m` **linear** system (`det M = ±(2^{K+L}-3^K)`);
the only transcendence object is the two-term form `Λ`.

## Why it stalls
The upper bound's exponential rate decays like `δ^{-m}` while the lower bound on `K` is fixed by
`X_0`, so the pincer opens geometrically.  Their conclusion: *"an entirely new idea seems to be
needed."*

**Full working notes, with the chain equation, every lemma, and the consequences for Front B:**
`ON-LINE-FINDINGS-2026-08-24-simons-deweger-m-cycles.md`.

## Companion PDFs fetched in the same session (all gitignored, all read firsthand)
- `papers/simons-2005-two-cycles.pdf` - Simons, *On the nonexistence of 2-cycles for the 3x+1
  problem*, Math. Comp. **74** (2005) 1565-1572.  Remark 2 is the **de Weger 1-cycle statement**:
  via Waldschmidt, `1 < 2^{k+l}/3^k < 1 + 3^{-0.1k}` has no solutions for `k ≥ 32`.
