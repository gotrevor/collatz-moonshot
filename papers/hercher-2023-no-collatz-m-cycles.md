# Hercher 2023 - "There are no Collatz m-Cycles with m ≤ 91"

## Provenance
- **Author**: Christian Hercher (Europa-Universität Flensburg).
- **Venue**: *Journal of Integer Sequences* **26** (2023), Article 23.3.5.  arXiv:2201.00406.
- **Local PDF**: `papers/hercher-2023-no-collatz-m-cycles.pdf` (gitignored; fetched from the
  JIS site).  **Verified firsthand 2026-08-22** (Ren) - this summary is from the PDF, not
  from citations of it.

## Main result

**Every nontrivial cycle has m ≥ 92 local minima** ("m-cycle" = nontrivial cycle with
exactly m local minima = m maximal odd-runs; Definition 5).  History chain, from the paper:
Simons-de Weger 2005: m ≥ 68 → SdW 2010 update: m ≥ 76 → Hercher 2018: m ≥ 77 → newer
X₀ alone gives m ≥ 83 → this paper: **m ≥ 92**.

⚠️ **Vocabulary mapping to this repo**: Hercher's *m* = `circuits v` (`FrontB/Threads.lean`);
his *K* (odd members) = `ones v`; his *L* (even steps); his map is the SHORTENED
`T(n) = n/2 | (3n+1)/2` - the same convention as the `FrontB` words and `Dictionary.lean`'s
`tstep`.

## Method - and what it does NOT use

Greps of the full PDF for Baker / Rhin / linear forms / transcendence come up **empty**.
The engine is: bounds on reciprocal sums `T(nᵢ) = Σ 1/C^k(nᵢ)` over consecutive local
minima (Lemma 12, Theorem 14: `Σ_{i≤m₁} T(nᵢ) < (97m₁+73)/60 · 1/X₀`-shaped), bounds on
`K/(K+L)` (Theorem 16), continued-fraction smallest-denominator arguments (Lemma 22), and
the computational verification bound `X₀`.  The m-cycle ladder is computation + elementary
Diophantine approximation - consistent with the FRONT-B-ROUTES filter: transcendence is
not even the opener here.

## Inputs and the live consequence 🔥

- Paper's input: `X₀ = 695·2⁶⁰` (Bařina, as of 2023).
- **Corollary 29**: if `X₀ ≥ 1536·2⁶⁰ = 3·2⁶⁹`, then every nontrivial cycle has
  **K > 1.375×10¹¹ odd members** (proved by his C++ residue-class program; Remark 28: his
  Theorem 27 cut the needed X₀ from 3781·2⁶⁰ to 2836·2⁶⁰, the program to 1536·2⁶⁰).
- **Bařina's frontier is past that**: `X₀ = 2075·2⁶⁰ ≈ 2^71.02`, completed 2025-01-15
  (see `papers/barina-2025-verification-limit.md`).  So **K > 1.375×10¹¹ is now
  unconditional** (modulo compute-trust of the distributed verification).  Implied
  un-shortened minimum cycle length ≈ 2.585·K ≈ **3.55×10¹¹ steps** - superseding the
  Eliahou-1993 axiom's 27,869,189 by 4 orders of magnitude.  ⚠️ Adoption into `Assumed/`
  is a separate, deliberate step - not done as of this writing.
