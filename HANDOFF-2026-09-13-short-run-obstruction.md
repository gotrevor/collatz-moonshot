# Handoff: primitive short-run rational obstruction complete

Date: 2026-09-13. Branch: `main`. Starting HEAD: `972c772`; clean worktree.
**Stopped: assigned bounded architecture/probe objective complete.** No push.
Read the CURRENT DIRECTIVE of `DIRECTION.md`, then this handoff and
`SHORT-RUN-OBSTRUCTION-2026-09-13.md`. DIRECTION was not edited: only altitude
laps may write it. Its selected mathematical question has now been answered.

## Concrete crux advance

The proposed rational bound M_Q is false already for Q=2. Put X=TF, Y=T²F,
A=XY, B=XYY. The family v_k=A^k B, k≥0, has

```
b=2k+3, a=3k+5, m=5k+8,
R=(27/32)^k*(243/256) ≤ 243/256 < 1,
z_i−2^q_i ≥ 8/5 > 0 at every odd-run head.
```

The macro maps f_A=27z/32+17/16 and f_B=243z/256+217/128 preserve
[34/5,434/13]. Their internal-prefix lower slacks are (24/5,8/5) and
(24/5,8/5,14/5). This gives the rational fixed cycle for every k by interval
invariance and the explicit affine fixed-point formula. Primitivity holds
in the existing `FrontB.Primitive` sense: any proper-power exponent would
divide both a and m, hence 5a−3m=1. This is an unbounded-family certificate,
not a finite-survivor extrapolation.

The admission arithmetic is fully separated:

```
D = 256*32^k − 243*27^k,
N = (9152*32^k − 7047*27^k)/5,
n0 = (−N * inverse(3^a)) mod 2^m.
```

Every family member begins TFTTFT, whose necessary congruence is
81n+119≡0 mod64, or n≡57 mod64. But N/D≤421/13<57, so **every member
fails integer admission**, with N−D*n0≤−320D/13<0. The full canonical
recurrence and finite exact values are in the note and experiment.

## Artifacts and proof level

- `SHORT-RUN-OBSTRUCTION-2026-09-13.md`: complete all-k mathematical proof,
  primitivity, cyclic boundaries, canonical residue recurrence, universal
  rejection, and costume check.
- `experiments/short_run_obstruction.py`: exact finite interval certificate
  plus 36 finite probes at k=0..32,64,128,256, reusing the existing cascade.
  It checks every q/e, z, minimum slack, R, N/D, n0, N−D*n0, and literal
  Boolean-word primitivity. Optional `--json PATH` exports all exact data.
- `STATUS.md`, `PENDING_WORK.md`: current completion and next-decision pointers.

No Lean source, theorem statement, axiom, sorry, build configuration, original
experiment, or census fixture was changed. The all-k proof is mathematical
prose supported by a rational certificate, **not yet a Lean theorem**. That
meets this directive's explicit exact-probe/refutation acceptance criterion.

## Verification actually run

1. `python3 experiments/short_run_obstruction.py` — PASS. Exact interval
   coefficient/endpoints/internal slack checks; all 36 cyclic identities and
   closed forms; every finite canonical trace and endpoint-slack identity;
   canonical recurrence; independent bit lifting for k≤8; exhaustive six-bit
   prefix-residue check; literal word-power checks independently of 5a−3m=1.
2. `python3 experiments/block_composition.py --controls` — PASS. Existing
   4000 actual cascades, rung-3 formula comparisons through m=18, omitted-joint
   negative controls, all 320 recorded admitting starts through 5000, and
   2305/2313 with unchanged remainders 7207/1375 and opposite admission.
   No fixed-b census was rerun; these are the unchanged regression controls.
3. `python3 experiments/paradoxical_excursion_audit.py` — PASS. All 15,300
   arbitrary-cut identities, row counts 4/19/101/0/155/41 at lengths
   8/27/46/54/65/73, all 320 admitting starts through 5000, shared-trunk
   controls, convergence controls, and the exact null-model checks.
   This does not repeat or strengthen the recorded complete 2..80 census.
4. `bash scripts/check-fixed-block-bound.sh` — full real `lean-green` gate,
   **8771 jobs; last line `✅ FORMALIZE-TIER GREEN`**. Six existing declarations
   audited. Composition uses the standard triple; length/nonvacuity results
   retain the eleven disclosed native certificates; boundary controls have
   no axioms. No new trust debt.
5. `git diff --check` before commit — clean.

## Current blocker and next highest-value attack

No blocker remains for the assigned rational-relaxation question. Global
admission across arbitrary words remains open: positivity, bounded individual
runs, primitivity, and a uniform gap from R=1 do not supply it. This family
is excluded by only six parity letters, so it does not refute arguments that
retain that congruence relative to the head threshold.

Return to altitude for the next scope decision. If authorized later, the
highest-value probe is whether an unbounded primitive rational family can
also survive a specified finite prefix-admission filter, or whether a new
quantitative canonical-residue exclusion is available. Do not promote a
global admitting-word length/run bound to an input: it restates restricted
finiteness. No such follow-on campaign was started in this bounded lap.

## Costume check and stopping action

Quantifiers proved: **∃Q=2, ∀M, ∃primitive rational cycle of length>M**
with the directive's bounds and strict joint positivity. All members are
nonadmitting, by a separate congruence proof. This refutes rational M_Q;
it does not refute Collatz, prove paradoxical finiteness, prove 2^b−1 optimal,
or rule out all improved real bounds. No literature-novelty claim is made.

Startup read the durable treadmill AGENTS, current directive, altitude First
attack and current status/pending context. No repository or ancestor local
AGENTS/CLAUDE files were present. Searched the read-only reference corpus and
read its closed-form validation and statement-faithfulness notes. No
Aristotle tool was available; no subagents or external messages were used.

Commit the green checkpoint, then call
`box done "Short-run rational M_Q refuted by a primitive Q=2 invariant-interval family; exact prefix congruence rejects every integer admission"`.
Stop. No `box stuck` or operator question is appropriate.
