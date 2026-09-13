# Handoff: altitude review complete — primitive short-run positivity obstruction

Date: 2026-09-13. Branch: `main`. No push. **Stopped: assigned review complete.**
Read the CURRENT DIRECTIVE of `DIRECTION.md` first. This lap edited documentation
only; it did not begin the chosen proof campaign or add any Lean declarations.

## Concrete advance

Replaced the three-campaign-stale rung-3 directive with one bounded objective:
**decide whether primitive, uniformly short-run words can have arbitrarily long
rational affine cycles with strict positivity at every odd-run start.**
The exact proposed bound to prove/refute, all quantifiers, ranking, first attack,
and acceptance criteria are in `DIRECTION.md`. No family is claimed to exist yet.
`STATUS.md` and `PENDING_WORK.md` now point at this objective.

This is a route correction with exact probe refutations, not a sorry-count
improvement. Two claims failed actual integer controls:

- `runs ≥ 0.22*m`: 1807@46 has endpoint 1822, odd count 29, and **9** runs;
  1127@65 has endpoint 1154, odd count 41, and **13** runs. Both are subcritical
  with strict endpoint growth. The least observed ratio in the five census
  rows is 9/46, not 0.22. No asymptotic claim with a cutoff is refuted here.
- Normalizing an arbitrary segment by removing its initial even steps:
  **18@8 ends at 20**, with five odd steps and `243<256`; its **9@7** suffix
  has `243>128`, so is not subcritical. This refutes that proposed map, not
  `odd-start finiteness → unrestricted finiteness` itself.

Source inspection also sharpens the A2 distribution question. At fixed (m,a),
`r = -3^(-a)*N mod 2^m` is already implemented and follows from the iterate
identity. Conditioning on exact numerator fixes the residue; a new result
needs a specified coarse distribution or threshold discrepancy statement.
This is not a newly proved Lean distribution theorem.

## Reconciliation, in commit order

`git log --oneline 5a54acc..HEAD` was read at clean starting HEAD `9ae73a3`.

- `5a54acc`: rung-3 front-normalized **length-8 classification** complete,
  including exceptional lengths. Source statement and actual axiom ledger checked.
- `f8fa4a5`, `cf8d748`, `56304ac`, `5ea1b38`: ladder probes, block/null census,
  A1 instruments, then trunk grouping. These are inputs, not new proof targets.
- `26c49b9`: A2/B kickoff; its two assignments are now both complete.
- `9b5dc54`: recorded complete sweep 2..80, with nonempty lengths exactly
  8,27,46,65,73. All trunks at m≥27 lie on the trajectory of 27; the blanket
  claim including length 8 is false (trunks 7 and 11 are exceptions).
- `c3aba74`: A2 complete. Prefix numerator retained; model law proved about
  its model in the audit, not as a Lean limit theorem or actual census law.
- `529ccef`: B architecture lap 1; its remaining bridge and proposed factor 2
  are historical after the next commit.
- `4a12a68`: B complete, explicit `L(b)=4*((2^b-1)*(b+53342))^2+b`, all odd-start
  segments with at most b runs. Read the actual `FixedBlocks.lean` statement.
- `9ae73a3`: extra complete fixed-four-run word slices, all empty. No rung 4/5
  objective follows. Its script still contains an older “rung 6 at 27” sentence;
  the corrected complete-census minimum is 7. Direction records the conflict.

Read all three preceding 2026-09-13 handoffs, the kickoff, excursion audit,
block-composition note, current status/pending scheme, and the census source.
The treadmill AGENTS/review policies were read first. No repository AGENTS.md,
CLAUDE.md, or CLAUDE.local.md was present. Searched the read-only reference corpus
and read its reconciliation, frozen-statement probing, and cycle-identity notes.

## Ranking and literature check

Ranked by subjective probability times magnitude of **new** mathematics:
(3) many-short-runs obstruction first; (4) quantitative residue distribution
second; (2) normalization edge third; (1) integer-cycle transport fourth.
The detailed reasons and scopes are in DIRECTION, including the live primary
source link and the existing literature-ledger pointers.

Re-read Simons–de Weger v1.44 via its authors' PDF, especially §1.4 and the
chaining/separation bounds. The fixed-circuit finiteness statement is known;
transporting the current composition gives a weaker quantitative specialization.
The primary paper describes Steiner's one-circuit exclusion, which a length
bound alone does not prove. The old “source unavailable” rationale is obsolete;
no primary Steiner paper was separately obtained or claimed read this lap.
Neither a global compression theorem nor ladder completion follows. No theorem
was added to the literature ledger or asserted novel on the basis of a search.

## Current blocker and first attack

The open crux is information lost between the positive **rational** fixed-point
envelope and the integer parity trace. The known repeated-squaring bound has
exponent `2^b-1`; separation closes each fixed b, but supplies no uniform length
ceiling as b grows. A global run bound for actual segments would just repackage
the restricted finiteness target. The unrestricted finiteness edge also remains
open, and neither headline Collatz front is discharged.

**First attack next lap:** use `experiments/block_composition.py` to seek a
strictly positive short rational cycle, then break repetition by one bounded
block defect or use two patterns preserving a common rational interval. Seek
one fixed Q and a parameterized primitive family of unbounded length, with
`1≤q_i,e_i≤Q`, all affine identities and `z_i>2^q_i` exact. Check cyclic boundaries
and primitivity rather than merely repeating one word. An invariant or recurrence
must certify the unbounded family; finite survivors alone do not refute M_Q.
The reviewed directive does not assert that this construction will succeed.

**Costume check:** strict slack excludes the repeated trivial TF cycle; primitive
words exclude the old power degeneracy. Rational-cycle survivors are not claimed
to be actual paradoxical segments or integer cycles. Track canonical n0 and
`N-D*n0` separately to identify the missing congruence/admission input. A family
would refute the specified positivity-only length bound, not prove the squaring
exponent optimal or refute Collatz. Preserve the 320 controls and 2305/2313 pair.

One bounded architecture/probe lap is authorized by the directive; no extended
implementation campaign without a new family, inequality, or smaller obstruction.
No rung 4/5 classification, fixed-b rerun, constant sharpening, or unrelated work.

## Verification actually run

1. `bash scripts/check-fixed-block-bound.sh` — **8771 jobs, FORMALIZE-TIER GREEN**.
   This invokes the real full `lean-green` gate and audits six declarations.
   Composition and integer-cascade composition have only the standard triple;
   numerical/actual length bounds inherit the eleven explicitly allowed native
   certificates. `oddRunCount_boundary_controls` has no axioms. No new mathematical
   axiom is hidden by the allowlist; the existing gate script was unchanged.
2. `lake env lean --stdin`, with `import CollatzMoonshot` and `#print axioms` for:
   `conjecture_iff_split`, `finite_acyclicParadoxical_imp_noDivergent`,
   `FrontA.threeBlock_length_eq_eight_of_acyclicParadoxical`,
   `FrontA.trunk_acyclic_criterion`, and `FrontA.trunk_depth_data_insufficient`.
   Exit 0. All except rung 3 print the standard triple; rung 3 adds inherited
   Rhin-lite and window native certificates, with no math axiom or sorryAx.
3. `python3 experiments/paradoxical_excursion_audit.py` — passes 15,300 exact
   arbitrary-cut identities, all 320 admitting starts through 5000, the empty
   length-54 row in that range, prefix-remainder controls, convergence checks,
   and the exact model identities/rounding/error checks.
4. Inline exact-Python review probes using existing functions:
   - Scanned odd starts 3..5000 at m=8,27,46,65,73; counts 4,19,101,155,41;
     minimum runs 3,7,9,13,17 and the two density counterexamples above.
   - `assert check_residue_affine(12)` — all 8190 words of lengths 1..12,
     affine reconstruction versus independent bit lifting.
   - Complete pure-integer orbit enumeration through the existing N_max bound
     at m=8 (X=86, four starts) and m=27 (X=17344, nineteen starts).
   - Searched even starts for the failed normalization map, obtaining 18@8.
   Reproduction of the decisive finite witnesses is below.
5. `python3 experiments/paradoxical_orbit_census.py 27 --quiet --trunks` initially
   failed because system Python lacks numpy. No dependency was installed. The
   complete pure-integer m=27 scan above replaced it; no claim that the numpy
   command passed or that the full 2..80 scan was repeated this lap.
6. `git diff --check` — clean before commit. No proof-debt tally was used as
   progress, and no proof source, experiment source, or build configuration changed.

```sh
python3 - <<'PY'
import sys
sys.path.insert(0, 'experiments')
from paradoxical import seg_data, check_residue_affine
from paradoxical_block_distribution import n_odd_blocks
for n,m,b in [(1807,46,9),(1127,65,13)]:
    d=seg_data(n,m)
    assert d['d']>0 and n<d['y']
    assert n_odd_blocks(d['v'])==b and 50*b<11*m
    print(n,m,d['y'],d['a'],b)
d=seg_data(18,8); e=seg_data(9,7)
assert d['d']>0 and d['y']==20 and e['y']==20 and e['d']<0
assert check_residue_affine(12)
print('review refutations and residue controls PASS')
PY
```

## Completion action

Commit this coherent documentation checkpoint on main, then call
`box done "Altitude review complete: reconciled three campaigns and selected the primitive short-run positivity obstruction"`.
The assignment is the direction review, not the next mathematical objective.
Stop after this checkpoint. No operator decision is needed and `box stuck` is
not appropriate. No subagents, Aristotle proof jobs, or external messages were used.
