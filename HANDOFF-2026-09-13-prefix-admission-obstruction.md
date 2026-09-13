# Handoff: Q=2, L=6 prefix-admission obstruction complete

Date: 2026-09-13. Branch: `main`. Starting HEAD: `bc4158e`; clean worktree.
**Stopped: the assigned bounded objective is complete.** DIRECTION.md is
unchanged because only altitude laps may write it. No push or subagents.

## Concrete crux advance

The displayed M statement is false. Keep X=TF and Y=TTF. For every j>=0,

```
w_j=(XY)^(2j+12) X Y^17,
b=4j+42, a=6j+71, m=10j+113,
R=(3^71/2^113)*(729/1024)^j < 1,
all odd-run head slacks z_i-2^q_i >= 8/5,
c_6=57,
N/D-57 >= 6402923708848027/703687441776640 > 0.
```

The macros `(XY)^2` and `(XY)^12 X Y^17` preserve [34/5,225], including
strict internal-head inequalities. The final macro maps the lower endpoint
above 58, so every fixed-cycle entry passes the prefix filter. Odd a,m and
5a-3m=16 imply gcd(a,m)=1, excluding every proper Boolean-word power.
The explicit length is unbounded; no finite exceptional j are omitted.

An independent integer-formula certificate exposes the new arithmetic.
For k=2j+12,

```
D=2^53*32^k-3^35*27^k > 0,
5N=2976838904967456448*32^k-29*3^35*27^k,
5*(N-57D)=409787117366273728*32^k+256*3^35*27^k > 0.
```

Both positive coefficients certify the strict margin for all parameters,
independently of sampled survivors. This completes the directive's explicit
counterfamily acceptance criterion as a **mathematical proof with an exact
rational certificate, not a new Lean theorem**.

## Search record, reuse and artifacts

First tested run-head rotations of the old family at k=0,1,2,4,16,64; all
tested rotations failed. The reproducible baseline retains all 99 rotations
at k=0..8 with N,D,c_6,c_m and both margins. An initial search of macros
with at most four (q,e) blocks found 18 individually positive subcritical
macros and no pair meeting the common-interval/lower-margin certificate.
Also tested bounded entry prefixes of length <=4 blocks before the old
family: none had both positive limiting internal slacks and limiting
threshold above its c_6. These are failed ansatz tests, not a population bound.

The successful next on-path route was a fixed longer terminal defect. Its
expanding Y blocks lift the entry threshold; twelve initial A blocks restore
contraction. Pairing further A blocks gives odd counts and a short primitivity
proof. Once this construction certified the exact question, search stopped.

- `PREFIX-ADMISSION-OBSTRUCTION-2026-09-13.md`: complete all-j proof, exact
  endpoint certificate, positive-coefficient margin, full-admission separation.
- `experiments/prefix_admission_obstruction.py`: imports the original affine,
  word, cascade, primitivity and certificate helpers; no replacement cascade.
  The optional `--json PATH` writes every q,e,z,slack,N,D,c_6,c_m, both margins,
  b,a,m,R and primitivity witness. No generated bulk fixture is committed.
- `STATUS.md` and `PENDING_WORK.md`: completion and next-decision pointers.

Read the durable treadmill policy, current direction, named first-attack
handoff, old obstruction proof/script and status/pending context. No local
AGENTS.md or CLAUDE files were present. Searched the read-only reference
corpus and read statement-faithfulness and closed-form-validation notes.
Checked the literal `FrontB.Primitive` definition. No external theorem lookup
or Aristotle job was needed: the bounded open construction was settled locally.

## Verification actually run

1. `python3 experiments/prefix_admission_obstruction.py` — PASS. Exact
   endpoint and all internal-head certificate; 99 old-family rotation controls;
   initial short-macro search; 36 exact cycles j=0..32,64,128,256. Each checks
   all cyclic heads against the existing cascade, explicit N,D and margin
   formulas, literal word primitivity, full canonical trace and endpoint
   margin. Independent bit lifting for j=0,1,2. All sampled full margins
   are negative; no universal full-admission sign is inferred.
   Also reran with `--json` to a temporary path inside the repository and
   checked the decoded 36 rows, 99 rotation controls, vertex/slack counts
   and both exact margin identities; the temporary artifact was removed.
2. `PYTHONPATH=experiments python3 -c 'from block_composition import controls; controls()'`
   — PASS. 4000 actual cascades, rung-3 formula controls through m=18,
   omitted-joint negative controls, all 320 reported starts through 5000,
   and unchanged 2305/2313 remainders 7207/1375 with opposite admission.
3. `python3 experiments/paradoxical_excursion_audit.py` — PASS. 15,300
   split identities, all 320 table controls and trunk counts, 2305/2313,
   exact model identities and bounds. This does not rerun or extend the
   recorded complete 2..80 census.
4. `python3 experiments/short_run_obstruction.py` — PASS. Original interval
   certificate and all 36 finite probes unchanged.
5. `bash scripts/check-fixed-block-bound.sh` — real full `lean-green` gate:
   **8771 jobs, six existing declarations axiom-audited, last line
   `✅ FORMALIZE-TIER GREEN`**. Composition uses the standard trust triple;
   length/nonvacuity inherits the eleven already-disclosed native certificates;
   boundary controls have no axioms. No Lean source or trust debt changed.
6. `git diff --check` — clean before commit.

## Costume check, blocker and next action

This is the old family with **15 Y blocks appended**, at even k>=12. The
new content is an all-parameter prefix margin. It refutes only boundedness
for the fixed Q=2, L=6 necessary-filter relaxation, at the given entry head.
It does not enforce the other m-6 parity letters or test all rotations.
The full canonical starts and margins are computed independently, with their
finite-check status explicit. No integer cycle, Collatz counterexample,
restricted-finiteness refutation, arbitrary-L theorem, or even-start bridge
is claimed. No global run/length bound was an input; no novelty is asserted.

No blocker remains for the assigned objective. Full arithmetic admission and
both Collatz fronts remain open but are outside this lap. **Next highest-value
action: altitude reconciliation and a new explicit scope decision**, with
this six-letter filter now known insufficient. Do not automatically raise L,
search full admission, or formalize the known positivity certificate as stretch.

Commit this coherent green checkpoint on `main`, then call
`box done "Q=2, L=6 bound refuted by all-parameter primitive padded family; exact prefix-margin certificate and full green gate"`
and stop. No `box stuck` or operator ask is appropriate.
