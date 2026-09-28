# Bounded Opus/low task: MSP² formalization, discharge `MSP2/Proved.lean`

Trevor asked (2026-09-27) for a public, warts-and-all Lean formalization of Sousa Pereira &
Mazzoni's MSP² article (Zenodo `10.5281/zenodo.22555969`).  The scaffold is in place and builds
green: `lake build MSP2`.  Read `MSP2/README.md` first.

## Scope

Edit **only** `MSP2/Proved.lean` (plus new helper files under `MSP2/` if one grows large, imported
from `MSP2/Proved.lean`) and `HANDOFF-2026-09-27-msp2.md`.  Do not touch `CollatzMoonshot/`,
`CollatzMoonshot.lean`, other notes, or experiments: other agents own them.

The statements in `MSP2/Proved.lean` are **frozen**.  An equivalent restatement is allowed for
elaboration; weakening a hypothesis or conclusion is not.  `MSP2/Hypothesis.lean` and
`MSP2/Headline.lean` are frozen and done.

## Objective

Replace each `sorry` in `MSP2/Proved.lean` with a proof.  Every numeric instance is already
confirmed in `MSP2/Checks.lean`, so a statement that looks false is far more likely to be a
transcription slip in the *statement*.  Re-read the cited section of the article (text below) and
report it; never weaken the statement silently.  **If a statement is genuinely false, that is a
result**: prove its negation in a new theorem next to it, leave the original with its `sorry`,
and record it in the README table as false, with the counterexample.

Suggested order, easiest first:

1. `blockB_eq`, `blockB_succ_sub`, `bConst_closed`, `bConst_parity`, `cLeft_even_eq_bConst`,
   `delta_closed`, `bConst_succ_via_delta`, `residue_bound`, `fam_reproduce`: induction +
   `omega`/`ring`/`push_cast`.
2. `step_three_fam_zero`, `covered_fam_zero`, `tA_two_mul`, `msp2_odd_run`,
   `not_three_dvd_after_run`, `odd_family_unique`.
3. `reachesOne_of_covered_upto` (strong induction, mirror `CollatzMoonshot.conjecture_of_descent`),
   `covered_iff_msp2`.
4. `tA_period`, `tA_distance`, `tA_distance_opt2`.  These need the order of `2` modulo `3ⁿ`,
   which is `2·3ⁿ⁻¹`.  Check mathlib for a primitive-root / `orderOf` lemma for `ZMod (3^n)`
   before building one; the article cites LTE (`multiplicity.pow_sub_pow_of_prime`-style lemmas).
   Route: `2·tA A b ≡ b`, so `tA^[i] b ≡ b·2⁻ⁱ (mod A)`, and `tA` maps `[0, A)` into itself.

## Done when

`MSP2/Proved.lean` has no `sorry`, `lake build MSP2` is green, and the README table rows read
"✅ proved" (or record a refutation).  Commit each green step.  Write
`HANDOFF-2026-09-27-msp2.md` and stop.  No successor task.

## Article text

The PDF is at `https://zenodo.org/api/records/22555969/files/48.%20Article.pdf/content`
(`curl -sSL … -o /tmp/msp2.pdf && pdftotext -layout /tmp/msp2.pdf -`).  It is in French.  If the
box has no network, work from the README and the docstrings, which cite section numbers.
