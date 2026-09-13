# KICKOFF 2026-09-13 — the excursion / null-model campaign (A2), then uniform fixed-block finiteness (B) 🧭

**Engine for A2 and B-architecture**: Codex, model `gpt-6-astra`, effort `high`.  **Branch**: `main`.
**Read this file, then `PENDING_WORK.md`, then the newest `HANDOFF-*.md`, before `DIRECTION.md`.**

## ⚠️ DIRECTION.md is one campaign stale — reconcile against git, not against prose

`DIRECTION.md`'s current directive (rung 3 of the odd-block ladder) is **COMPLETE**: `5a54acc`
("Front A: close the rung-3 classification") — every acyclic paradoxical segment whose word has
three odd blocks has length 8.  Do not restart it, and do not edit `DIRECTION.md` (altitude laps
own it).  This kickoff is the operator direction for the next two campaigns; it was written from
the host brief `~/personal/claude/knowledge/core/projects/moonshot-campaigns-2026-09-13-fable.md`
(not visible from the box - everything a lap needs is here).

## What Campaign A1 already established (host, 2026-09-13, commits `56304ac`, `5ea1b38`)

Instruments, all exact-integer, all with known-answer controls, in `experiments/`:

- `paradoxical_random_model.py` — the continuous null `R = S_N/(D·2^m)` by an `O(m·a)` DP, the
  closed form `S_N = C(m−1,a−1)3^(a−1) + Σ_{k≤a−2} C(m−1,k)(2^m − 2·3^k)`, the
  `Bin(m−1,½)/Bin(m−1,¾)` identity `S_N/4^m = (P(U≤a−2) − P(V≤a−2))/2 + P(V=a−1)/4`, the clipping
  check via `N_max = 2^(m−a+1)(3^(a−1) − 2^(a−1)) + 3^(a−1)`, and the odd-residue null
  `R_odd = Σ (2/M)·clamp(⌊(N−1−D)/(2D)⌋, 0, M/2)`.  `--selftest`, `--table`.
- `paradoxical_block_distribution.py` — the word census with per-word `E, H, Hs, P`, realized
  peak, endpoint ratio, first descent, hitting time; `--controls` runs the three word-level
  controls (7→8 orbit; `1^a0^b`; balanced ρ-word+`00`, `E ≥ a/24`, `Hs = 1`).
- `paradoxical_orbit_census.py` — **complete** census of all front-normalized acyclic paradoxical
  segments of a given length, every `a` at once, by enumerating odd starts up to the proved bound
  `X(m) = max_a ⌊(N_max(m,a) − 1)/D(m,a)⌋`; `--trunks` groups them by orbit minimum.

Results (complete at each length; null `R` is the continuous model):

| `m` | `a` | words | `R` | obs/`R` | odd blocks | starts | trunks (orbit minima) |
|---|---|---|---|---|---|---|---|
| 8 | 5 | 4 | 5.08 | 0.79 | 3 | 7–25 | 11, 5, 7 |
| 27 | 17 | 19 | 10.86 | 1.75 | 7–10 | 165–885 | 31, 47 |
| 46 | 29 | 101 | 18.69 | 5.40 | 9–15 | 91–4611 | 91, 47, 31, 71, 103, 61 |
| 54 | 34 | 0 | 6.36 | 0 | – | – | – |
| 65 | 41 | 155 | 42.35 | 3.66 | 13–21 | 73–4547 | 31, 47, 91, 103, 71, 23 |
| 73 | 46 | 41 | 7.91 | 5.18 | 17–22 | 487–4613 | 31, 47 |

**Every trunk at `m ≥ 27` lies on the trajectory of 27.**  An admitting segment is a descent
from `n` to its orbit minimum `t` (depth `k`, `j` odd steps, `n/t ≈ 2^k/3^j`) followed by `t`'s
climb over `m − k` steps; the words are preimage clusters of a few trunk climbs.  The start's
own excursion is small (endpoint ratio `1.001–1.05`, realized peak mostly `1.5–6`); `E = 10–200`
is the climb's additive remainder carried up the tree.  What fails in the null model is
independence, not integrality.  Every start found converges (`τ = 58–95`): finite verification
kills none of these, and the "exponential excursion in `m`" inference of the review's §7 is
withdrawn (finite verification gives a polynomial bound only).

## Campaign A2 — settle the excursion and null-model claims (1 lap, ≤ 90 min)

Audit and prove the exact identities above where a proof adds wiring value (Lean only for
statements that are correct and useful as nodes; an elementary derivation plus the exact probe is
enough to decide what deserves formalization).  Then **classify every candidate excursion node**
as proved / refuted / open-and-stronger-than-known-inputs / equivalent-to-an-existing-target /
not-yet-understood.  Candidates, in the order the data suggests:

1. **Trunk decomposition (exact).**  For an acyclic paradoxical segment `(n, m)` with orbit
   minimum `t = T^k(n)`: write the word as `descent · climb`; derive the exact criterion in terms
   of `N_climb`, `D`, `k`, `j`, `t`.  State it as a theorem about the climb word of `t` alone plus
   the preimage depth.  Controls: the table above (every row must satisfy it).
2. **Excursion-at-the-trunk.**  Does a paradoxical segment force a climb ratio of `t` that grows
   with `m` (polynomially? exponentially?) — and is that statement anything other than Front A
   restated?  The review's §7 claim was about the *start*; the data says the start is the wrong
   anchor.
3. **The null-model law** `R ~ 1/(2δ)` is a theorem about the model; record it as such, and
   record the independence failure (preimage clustering) as the reason the model is not a
   prediction.  Do not convert "quantitative" into "tractable".

Success = a checked null-model law and a precise decision on the excursion route: a valid new
implication, or the exact extra hypothesis it needs, or a refutation / exposed circularity.
Record whether any surviving claim concerns divergence only or also cyclic equality.  If the
only route to an exponential excursion statement assumes a global hitting-time bound or restates
Front A, say so and stop A2 — that is a successful outcome.

## Campaign B — uniform fixed-block finiteness (≤ 2 architecture laps, ≤ 3 h; implementation only if a decomposition survives)

Target (conventions frozen: front-normalized = first step odd; "runs" = maximal odd blocks):

```text
For every b there is an explicit L(b) such that every odd-start acyclic paradoxical
segment with at most b maximal odd runs has length at most L(b).
```

Controls: rung 1–2 exclusions, rung 3 = length 8 (`ThreeBlock.lean`), and the census: rungs 4–5
are empty at every length `≤ 80`; smallest realized block counts `3@8, 7@27, 9@46, 13@65, 17@73`
(so any `L(b)` grows about like `b/0.22`).  Donors: `FrontA/Paradoxical.lean`,
`FrontA/ThreeBlock.lean`, `FrontA/RhinLiteSep.lean`.

Architecture lap 1: derive the arbitrary-block integer cascade from the head-block identities;
locate exactly what the 2- and 3-block contraction uses; produce the decisive proposed
composition inequality and its smallest controls, tracking every bound's dependence on `b`, `a`,
run lengths and `D`.  A finite probe for `b = 4, 5` tests a proposed lemma; it is not the theorem.
Lap 2: prove it, refute it, or isolate the genuinely new arithmetic obligation.  A renamed copy
of the target is not a decomposition; an induction that imports the uniform theorem or global
Collatz under another name is a stop.  ⚠️ The preimage-cluster structure above is the first thing
a uniform argument meets: at `m = 46` the 9-block word and the 15-block words are the *same*
trunk climb seen from different depths.

Success = the uniform theorem, a substantive uniform composition lemma reducing it to a strictly
identified smaller obstruction, or a counterexample.  Stop after two architecture laps without a
new inequality, mechanism or refutation; do not launch the implementation tranche then.

## Lap discipline (every lap)

- Commit coherent progress; every lap ends with a commit or a written reason there is nothing to
  commit.  Targeted green build on the touched module is a checkpoint; name the evidence tier.
- Hypotheses stay visible; a refuted conjecture stays recorded as refuted.  No sorry-count gate:
  decomposing a fat `sorry` into named leaves is progress.
- Report at the campaign boundary in three words — running+advancing / running+stalled /
  stopped — plus at most two sentences: the mathematical advance and the next decision.
- No outward comments, email or publication prose.
