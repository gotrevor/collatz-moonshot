# Kurtz-Simon 2007 - "The Undecidability of the Generalized Collatz Problem"

## Provenance
- **Authors**: Stuart A. Kurtz, Janos Simon (U. Chicago).
- **Venue**: TAMC 2007, LNCS **4484**, pp. 542-553.  DOI 10.1007/978-3-540-72504-6_49.
- **Working PDF**: `papers/kurtz-simon-2007-gcp.pdf` (gitignored and not redistributed; extracted
  from the LNCS volume and read via institutional access on 2026-08-23). ⚠️ The
  freely-hosted UChicago copy (`people.cs.uchicago.edu/~simon/RES/collatz.pdf`) is an
  UNFINISHED DRAFT: its Sec. 3 is empty and its bibliography is `[?]`s.  This summary is
  from the published chapter, read firsthand.

## The theorems (published form)

- **Definition 1**: `g` is a *Collatz function* if for some modulus `m` and non-negative
  rationals `a_i, b_i` (`i < m`), `x ≡ i mod m ⟹ g(x) = a_i x + b_i ∈ ℤ`.  NB: affine,
  not just multiplicative - Conway 1972's theorem had all `b_i = 0`; KS do not.
- **Theorem 1 (Conway)**: from machine index `e`, compute `g_e` with `M_e(x)` converges iff
  `∃i, g_e^(i)(2^{x+1}) = 1`.
- **Theorem 2 (main)**: from `e`, compute `g_e` with **`M_e` total iff `∀x ∃i,
  g_e^(i)(x) = 1`** - every start, not just powers of 2.
- **Theorem 3**: GCP (the `∀x`-form, given `g`) is **Π⁰₂-complete**.
- Framing, their words: "We provide a heuristic explanation for the apparent difficulty of
  the problem."  Nothing here is about the 3x+1 instance itself (cf. Conway 1972: "our
  theorem says nothing about the Collatz game").

## The two devices of Sec. 3 (the actual novelty)

1. **Universal totality (3.1)**: `U(M)` runs THREE copies of `M` - C (main), A (checkpoint),
   B (replay verifier) - with step counters `b ≤ a ≤ c` in the configuration.  Big steps:
   advance B and C; at `b = a`, verify `B = A` (reflection), then checkpoint C into A and
   restart B from the true input.  A garbage start either breaks `b ≤ a ≤ c` (halt), or
   survives at most one reflection - after which B is an honest restart, so the SECOND
   reflection's comparison exposes the garbage checkpoint.  All runtime subroutines are
   non-nested counter-controlled loops, so they terminate from any state.  Hence: `M` total
   ⟹ `U(M)` halts from EVERY configuration, and `U(M)` computes the same partial function.
2. **Unintended factors (3.2)**: work mod `m` (product of distinct primes + a safety prime
   `p`).  A residue class containing NO valid-form integer (input `2^{x+1}`, state encoding,
   output `3^{k+1}`-being-reduced) gets `a_r = 1/m`, `b_r = (m-r)/m`: `x ↦ (x+m-r)/m < x`,
   strictly decreasing, with `k(1) = 1`.  Mixed garbage `x·z` (`z ≡ 1 mod m`) is simulated
   to completion (finite, by universal totality), stripped to `z' < z`, and descends.
   Strictly-decreasing big steps ⟹ everything funnels to 1.

## Why this repo cares

- Closes the last gap in the APPROACHES.md negative-drift resolution: the shrink-prime
  padding composes with the published construction at every joint (~97%; residual = not
  machine-checked).  Q-divisible integers descend to Q-free ones where KS machinery takes
  over; divergence witnesses are clean configuration encodings, Q-free by construction.
- 💡 Observation worth keeping: the KS construction has heavy contraction BUILT IN - every
  impossible residue carries multiplier `1/m`.  A careful class-count could plausibly show
  the canonical KS instances are ALREADY negative-drift; the padding argument stays the
  clean way to force it.
- The barrier's precise content (also in APPROACHES.md): TOT reduces to GCP, so no method
  uniform across the family exists.  It licenses nothing about the single instance 3n+1.
