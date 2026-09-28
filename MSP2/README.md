# MSP² in Lean 4

A Lean 4 formalization of the MSP² framework of **Mário Sousa Pereira and Enzo Mazzoni**:

> *MSP² : une représentation regroupée des trajectoires de Syracuse*, Revue Internationale du
> Chercheur 7(3) (2026) 1071-1129.  Zenodo [`10.5281/zenodo.22555969`](https://doi.org/10.5281/zenodo.22555969).

The authors asked for a Lean formalization and we are building one in the open.  The rule here
is to formalize the article **as written**: what the article proves becomes a theorem, the step
the article itself marks as open becomes an explicitly named hypothesis, and anything that turns
out to be false is recorded as false.  Section numbers (`§n.m`) refer to the article.

Build: `lake build MSP2` (it is a separate library in this repo; it shares no file with the
`CollatzMoonshot` moonshot proper, only imports its definition of the Collatz map and the
conjecture).

## Headline

`MSP2/Headline.lean`, **proved, no `sorry`**:

```lean
theorem conjecture_of_raccord  (h : Raccord)    : Conjecture   -- the open step ⟹ Collatz
theorem raccord_of_conjecture  (h : Conjecture) : Raccord      -- and conversely
theorem raccord_iff_conjecture : Raccord ↔ Conjecture
```

`Conjecture` is the repo's `CollatzMoonshot.Conjecture` (every positive integer reaches `1`).

## What is assumed

One hypothesis, `Raccord` (`MSP2/Hypothesis.lean`), and nothing is `axiom`: it is a `Prop` that
appears as a hypothesis where it is used.

The article says plainly that one step is still open (§16.2 "Statut de cette version", §16.7.4,
§20 "État de la démonstration"): the structural recurrence that guarantees the *raccord* in the
Generator Table at every coefficient `3ⁿ`.  §16.2 states what that step is meant to deliver:

> pour tout n fini, N ≤ 2ⁿ − 1 ⇒ il existe j fini tel que Tʲ(N) < N.

`Raccord` is exactly that statement.  **This is our reading of §16/§20, pending the authors' own
statement of the remaining step at every level `3ⁿ`.**  When they supply it, the finer statement
goes beside `Raccord`, together with a theorem showing it implies `Raccord`.

**What the headline shows.** As §16.2 phrases it, the open step is *equivalent* to the Collatz
conjecture.  That follows from the reading, not from a flaw in it: "every `N ≥ 2` eventually dips
below itself" is Terras's classical reformulation of Collatz (`CollatzMoonshot.conjecture_iff_descent`).
It tells us where all the difficulty sits.  The Generator Table can only contribute through a
finer, checkable statement placed underneath `Raccord`.

## What is proved or checked

| Article | Lean | Status |
|---|---|---|
| §15.9, §16.2: vertical loops at 9 (6 states) and 27 (18 states) | `Checks.tA_nine_loop`, `tA_twentyseven_loop` | ✅ checked |
| §9.9: blocking points 25, 385, 6145, 98305 | `Checks.blockB_values` | ✅ checked |
| §16.3-16.4: B constants 4, 13, 40, 121, 364, 1093 | `Checks.bConst_values` | ✅ checked |
| §16.3 Table 5: useful distances 4, 10, 28, 82, 244, 730 (first hit) | `Checks.table5_distances` | ✅ checked |
| §16.5: left route 1, 22, 13, 202, 121, 1822; Table 8 distances 6, 18, 54, 162, 486 | `Checks.cLeft_values`, `table8_distances` | ✅ checked |
| §16.2-16.5 Tables 4, 6, 9: row bounds for starts up to 7, 15, 31, 63, 127 | `Checks.tables_4_6_9` | ✅ checked |
| §16.7.4: Δ₀…Δ₄ = 2, −16, 38, −124, 362 (−16 and 38 match the §16.4 jumps) | `Checks.delta_values` | ✅ checked |
| §19: MSP²⁻ loops through −17 (length 11), −5 (length 3), −1 (fixed) | `Checks.msp2Neg_loops` | ✅ checked |
| §16.2 levels up to 127 are covered | `Checks.raccordLevel_seven` | ✅ proved |
| The open step ⟺ Collatz | `Headline.raccord_iff_conjecture` | ✅ proved |
| §2 odd run `M ↦ 3^r·u − 1`; §2.5 next odd is `6q ± 1`; §3 run-length families partition the odds | `Proved.msp2_odd_run`, `not_three_dvd_after_run`, `odd_family_unique` | ✅ proved |
| §9.8 family reproduction `A_{j+1} = 3A_j`; members `A_j·u + 1` are covered | `Proved.fam_reproduce`, `step_three_fam_zero`, `covered_fam_zero` | ✅ proved |
| §9.9 `B_j = 24·16ʲ + 1`, strict growth | `Proved.blockB_eq`, `blockB_succ_sub` | ✅ proved |
| §16.2 coverage up to `K` ⟹ reaching 1 up to `K`; MSP² vs Collatz coverage agree | `Proved.reachesOne_of_covered_upto`, `covered_iff_msp2` | ✅ proved |
| §16.3-16.5 closed forms, parity alternation, distances for all `n` | `Proved.bConst_closed`, `bConst_parity`, `tA_distance`, `cLeft_even_eq_bConst`, `tA_distance_opt2` | ✅ proved |
| §16.7.1 `T_A(b) ≡ b·2⁻¹ (mod A)`; §16.7.2 loop length `2·3ⁿ⁻¹` | `Proved.tA_two_mul`, `tA_period` | ✅ proved |
| `2` is a primitive root mod `3ⁿ` (needed by §16.3, §16.5, §16.7.2) | `Order.orderOf_two_zmod` | ✅ proved |
| §16.7.4 closed form of Δₙ, and the conditional step `Bₙ → Bₙ₊₁` | `Proved.delta_closed`, `bConst_succ_via_delta` | ✅ proved |
| §16.8 `(3ᵐ − 1)/2 > 2ᵐ − 1` for `m ≥ 2` | `Proved.residue_bound` | ✅ proved |

**`MSP2/` is `sorry`-free** (2026-09-28).  Every statement listed above is machine-checked, and
`#print axioms` on each reports only `propext`, `Classical.choice`, `Quot.sound`.  No statement was
weakened to get there: the frozen statements of `MSP2/Proved.lean` are proved as written.

The one piece of mathematics the article's distance claims need but does not prove in Lean-ready
form is that **`2` is a primitive root modulo `3ⁿ`**.  That is `MSP2/Order.lean`, also `sorry`-free:
a single lifting-the-exponent induction

  `2 ^ 3ⁿ = −1 + 3^(n+1)·cₙ` with `cₙ ≡ 1 (mod 3)`

gives `2^(3ⁿ) ≡ −1 (mod 3^(n+1))`, the exact 3-adic valuation of `2^(2·3ⁿ) − 1`, hence
`orderOf (2 : ZMod (3^(m+1))) = 2·3^m`; and the refinement `cₙ ≡ 1 (mod 3)` pins the cube root of
unity `2^(2·3ⁿ) ≡ 1 + 3^(n+1) (mod 3^(n+2))` that §16.5's two-sided distance lands on.

## Not yet stated

The inverse trees of §4-§7 (roots `6q ± 1`, leaf recurrences, entry and exit periods) and the
Generator Table of §11-§15 need definitions we have not written yet.  The finer form of the open
step will be stated in terms of the Generator Table, so the table comes next.  We have asked the
authors for the precise statement of the remaining step and for machine-readable Generator Table
data (Annex A).

## Notes on the text

- **§9.10 vs §20.** §9.10 asserts a coverage invariant: after block `j`, every canonical
  representative below `B_j` is already absorbed.  Since `B_j → ∞` (§9.9) and coverage is
  transmitted through the trees (§9.11), that invariant alone would give the conjecture.  §20
  counts §2-§9 as established and puts the remaining step in §16.  We read §9.10's invariant as
  carrying the same weight as `Raccord`.
- **§16.7.4 arithmetic.** With the §16.4 passage, the sum `3(Bₙ + 1) + Δₙ₊₁` (or
  `3(Aₙ + Bₙ + 1) + Δₙ₊₁`) equals `3ⁿ⁺³ − 1 = 2·Bₙ₊₁`, which is our `bConst_succ_via_delta`.  The
  article prints `2·3ⁿ⁺³ − 2` for that sum but reaches the same conclusion,
  `Bₙ₊₁ = (3ⁿ⁺³ − 1)/2`.

## Credit

The mathematics, and the MSP² and Generator Table framework, are the work of Sousa Pereira and
Mazzoni.  Any error in the Lean statements is ours: please open an issue.
