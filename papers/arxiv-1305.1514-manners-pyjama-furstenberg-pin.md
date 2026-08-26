# Pin note: Furstenberg ×2×3 topological rigidity — proof sources

**Formalized in `CollatzMoonshot/Rigidity/Furstenberg.lean` (2026-08-26), discharging the
former THEOREM-grade axiom in `Assumed/Furstenberg.lean`.**

## The pin source

**Manners, *A solution to the pyjama problem*, arXiv:1305.1514, §4** (local:
`arxiv-1305.1514-manners-pyjama.pdf`).  Section 4 reviews Furstenberg's Theorem IV.1 with a
complete proof sketch "broadly following Boshernitzan":

- **Theorem 4.1** = Furstenberg 1967 Thm IV.1: closed ⟨2,3⟩-invariant subsets of 𝕋 are 𝕋 or
  finite sets of rationals.  Our `Furstenberg.isClosed_invariant_finite_or_univ` proves the
  `Finite ∨ univ` form for any multiplicatively independent `p, q ≥ 2`.
- **Lemma 4.2** (≈ Furstenberg Lemma IV.1): for small `η`, `ηΦ ∩ [0,1)` is δ-dense — our
  `climb`, via `log_lattice_tail_dense` (density of `{r log p + s log q}` in a half-line tail).
- **Corollary 4.3**: closed invariant set with `0` (or a rational point) as limit point is 𝕋 —
  our `eq_univ_of_accPt_zero` / `eq_univ_of_accPt_torsion`.
- **The intersection induction**: `X_k = Y′ ∩ ⋂_{i≤k} (Y′ − a_i)` over a δ-dense grid of
  rationals fixed by `⟨p^m, q^m⟩`; each `X_k` infinite ⇒ its difference set is compact,
  invariant, accumulates at 0 ⇒ is 𝕋 ⇒ hands the next translate its witness.  Our `hXne`
  induction inside the main theorem.

## Formalization notes (the "chinks" ledger) 🕳️

1. **No mathematical error found.**  Manners' §4 sketch survives full formalization; every
   gap was routine.  This is a verification-grade reading of the Boshernitzan route.
2. **One glossed detail made explicit**: Cor 4.3's rational-limit-point case ("is similar, or
   can be deduced") needs care when the rational's denominator shares factors with `pq` — no
   `⟨p^m, q^m⟩` fixes `1/2` for `p = 2`.  Our `exists_fixed_in_orbit` fills this by pigeonhole
   on the finite orbit + smul-commutativity (no order/totient arithmetic), fixing a *modified*
   point `q^t • p^r • β` in the orbit; the translate trick then runs there.  Not an erratum —
   the sketch never claims the naive statement — but a genuine proof obligation the paper
   leaves silent.
3. **Grid denominators**: we use `d = (pq)^L + 1`, automatically coprime to `pq` at every
   scale (Manners: "denominators coprime to 2 and 3", existence left implicit).
4. **`exp` Lipschitz bound**: `e^a − e^b ≤ (a−b)e^a` needs *no* order hypothesis (from
   `1 + x ≤ e^x` alone) — `exp_sub_exp_le`.

## Companion sources (local PDFs, all gitignored)

- `arxiv-2110.05989-times2times3-survey.pdf` — **Tal**, survey of the *measure* conjecture
  (Lyons / Rudolph / Host / Parry proofs).  States Thm 1.1 (topological) but does not prove
  it; cites Furstenberg [10] and Boshernitzan.  Good background for the Rudolph-Johnson lane.
- `arxiv-1607.00670-generalizations-furstenberg-diophantine.pdf` — **Katz** (M.Sc. under
  Lindenstrauss).  Lemma 2.1 is the climb lemma with proof; Thm 1.1 generalizes density to
  `{a_n b_m c_k x}`.  Still defers the crux to Boshernitzan.
- `arxiv-2406.01353-bohr-recurrence-nonlacunary.pdf` — **Frantzikinakis–Host–Kra 2024**, Bohr
  recurrence of `{k! 2^m 3^n}`; Prop 4 (closed invariant sets in 𝕋^d contain rational points)
  *consumes* Furstenberg's theorem.  Also: Furstenberg Lemma IV.1 (non-lacunary ⟺ ratio → 1)
  — a formalizable spin-off we did not need.
- `arxiv-2301.08212-on-furstenberg-diophantine.pdf` — **Gayfulin–Moshchevitin**, the
  *effective* density version (BLMV-style rates, `1/(log log log M)^κ`), pigeonhole + digit
  combinatorics.  Not needed for the qualitative theorem; a future effective-layer source.
  (Same Moshchevitin whose theorem Vandehey's Lemma 3.2 mis-cites — small world.)

## Primary sources (not retrieved)

- Furstenberg 1967, *Math. Systems Theory* 1, Thm IV.1 — Springer paywall.
- Boshernitzan 1994, *Proc. AMS* 122, 67–70 — AMS backfile free in a browser; Cloudflare
  blocks curl (the known trap).  Not needed: Manners' presentation sufficed.

## Prior-art sweep (2026-08-26)

Apparently **first formalization in any prover** — hedge: survey-based.  Instruments: pinned
mathlib grep + `gh` open-PR search (zero Furstenberg hits); Reservoir corpus mirror (synced
2026-08-26); Lean Zulip via zulip-ro (24 channels / 365 days); lean-eval problem list.
⚠️ Naming trap for future searches: lean-eval's `furstenberg_topological` /
`furstenberg_measure` are the **multiple recurrence** theorems (Furstenberg–Weiss 1978 /
Furstenberg 1977), not ×2×3 rigidity; LeanFrontier's "Furstenberg" is the evenly-spaced-
topology primes proof.  formal-conjectures' `FurstenbergTimesPTimesQ.lean` states only the
open **measure** conjecture (sorry'd).
