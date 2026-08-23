# Bařina 2025 - the computational verification frontier

## Provenance
- **Paper**: D. Barina, *Improved verification limit for the convergence of the Collatz
  conjecture*, J. Supercomputing **81**, 810 (2025).  DOI 10.1007/s11227-025-07337-0
  (paywalled; not fetched).
- **Project page**: https://pcbarina.fit.vutbr.cz/ - **checked firsthand 2026-08-22** (Ren).

## The bound

**Convergence verified for all n < 2075·2⁶⁰ ≈ 2^71.02, completed 2025-01-15** (project log:
"the convergence of all numbers below 2^71 is verified").  Next milestone 2076·2⁶⁰ in
progress (~17% at check time).  The earlier peer-reviewed staging post: 2^68 (Barina 2020,
J. Supercomputing 77).

## Why we care

`X₀ = 2075·2⁶⁰` clears Hercher 2023's Corollary-29 threshold (`1536·2⁶⁰`) with 35% headroom
→ **K > 1.375×10¹¹ odd members in any nontrivial cycle, unconditionally** (modulo
compute-trust).  See `papers/hercher-2023-no-collatz-m-cycles.md`.

⚠️ Epistemic status: a distributed computation, not a proof artifact - THEOREM-grade for
`Assumed/` purposes by house convention (like the existing Barina 2⁶⁸ axiom), but the
compute-trust caveat should ride along in any docstring that cites it.
