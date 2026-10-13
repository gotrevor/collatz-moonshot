# HANDOFF: amusical continuous reversors

## 2026-10-13 — Lemma S proved; three targets remain

Concrete advance:

- `reversor_eq_of_stepSym_eq` is proved with its ratified statement unchanged.
- Added `AmusicalContinuousReversor/Itinerary.lean`.  Its load-bearing theorem
  `pow_two_dvd_sub_of_stepSym_iterate_eq` proves that a common step-symbol prefix of length `L`
  makes the difference divisible by `2^L`.  `eq_of_stepSym_iterate_eq` then proves injectivity of
  the full itinerary using `Nat.lt_two_pow_self`.
- The target proof derives `ι (amusicalInv^[k] n) = amusical^[k] (ι n)` directly from the
  reversor equation and applies itinerary injectivity to the pointwise symbol hypothesis.
- No ratified statement changed, no axiom or `native_decide` was added, and lines remain at most
  100 characters.

Verification:

- `lake build CollatzMoonshot.AmusicalContinuousReversor` — green, 8710 jobs.
- `~/personal/bin/lean-green ~/src/collatz-moonshot-amusical-contrev --target
  CollatzMoonshot.AmusicalContinuousReversor --axioms
  CollatzMoonshot.Amusical.reversor_eq_of_stepSym_eq` — FORMALIZE-TIER GREEN, 8710 jobs; the
  theorem's axiom ledger is exactly `Classical.choice`, `Quot.sound`, and `propext`.

Current blocker:

- Three target proofs remain: `reversor_const_of_twoAdicContinuous`,
  `reversor_const_of_threeAdicContinuous`, and `no_continuous_linear_reversor`.
- The missing reusable layer is exact cylinder transport/surjectivity, not itinerary uniqueness.
  `AmusicalWindow.lean` already supplies affine formulas on classes modulo `4^L` and `3^L`, but
  the next lap must package the mixed-prime intersection argument used in the kickoff paper proof.

Next highest-value attack:

1. Prove a forward-cylinder parametrization refining the new prefix-divisibility theorem: for a
   fixed length-`k` step word, express the cylinder as one class modulo its exact power of two and
   show `amusical^[k]` maps it affinely with coefficient `3^k`.
2. Combine that parametrization with coprimality of powers of two and three to choose the pullback
   point in Theorem A.  Add the elementary propagation lemma that `amusical^[k]` loses at most
   `2k` binary digits.
3. Mirror the construction for Theorem A′ only after Theorem A is kernel-green.  Then reuse both
   exact cylinder packages for Theorem C's finite-density count.

The untracked `CLAUDE.local.md` predates this lap and was deliberately left untouched.
