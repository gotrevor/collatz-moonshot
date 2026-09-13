# Campaign A2: exact trunk criterion and model law

**Decision: stop A2 successfully.** The exact decomposition survives with an indispensable
preimage remainder. The requested criterion using only the climb, depth and odd count is
refuted in Lean. The null asymptotic is a theorem about its artificial residue model; it
does not estimate the deterministic census without a new arithmetic distribution theorem.
No unconditional excursion-growth theorem in m or new closer for either Collatz front results.
Campaign B is the next campaign, not stretch work undertaken in this lap.

## 1. Exact decomposition and the missing datum

Use the shortcut map `T`, `x_i=T^i(n)`, `m=k+l`, `t=x_k`, `y=x_m`. Write the actual parity
word as `u ++ w`, with `|u|=k`, `ones(u)=j`, `|w|=l`, `ones(w)=b`, `a=j+b`. Put
`N_d=numer(u)`, `N_c=numer(w)`, `M=2^m`, `D=M-3^a`, `δ=D/M`. Then

```
2^k t = 3^j n + N_d                  2^l y = 3^b t + N_c
N(u ++ w) = 3^b N_d + 2^k N_c
3^j 2^l (y-n) = 3^j N_c + 2^l N_d - D t.                 (T)
```

These hold at every cut, without subcriticality or a minimum hypothesis. The existing
`traceWord_add` and `FrontB.numer_append` supply the word decomposition; the new
`FrontA.trunk_slack_identity` proves (T) directly from the two orbit identities.
For `n>2`, `m>0`, `D>0`, the exact acyclic criterion is

```
D t < 3^j N_c + 2^l N_d,                                 (AC)
```

proved as `trunk_acyclic_criterion`. Replace `<` by `=` for endpoint equality
(`trunk_equality_criterion`), or by `≤` for the non-strict paradoxical criterion.
Equivalently, `y/t > n/t = 2^k/3^j - N_d/(3^j t)`.
The minimum anchors the suffix but does not make the prefix monotone: it can contain
large earlier climbs. A peak over the whole segment is not the trunk's suffix peak.

**The omitted remainder changes admission, not just the numerical margin.**

| start | m | t | k | j | N_d | N_c | y | acyclic? |
|---|---|---|---|---|---|---|---|---|
| 2305 | 46 | 103 | 14 | 6 | 7207 | 216037099987 | 2308 | yes |
| 2313 | 46 | 103 | 14 | 6 | 1375 | 216037099987 | 2308 | no |

Both words have `a=29`, both starts are odd, and `103` is the minimum of both entire
segments. Their last 32 steps coincide. In (AC), `D t-3^j N_c = 21560735825920`;
the two right-hand corrections `2^l N_d` are `30953829302272` and `5905580032000`.
`trunk_depth_data_insufficient` kernel-checks the entire witness, including the minima.
Consequently no predicate of `(t,w,k,j,D)` alone can characterize admission of an
individual preimage. A statement asking whether *some* such preimage admits is different:
it must optimize over the realizable prefix remainders, preserving their arithmetic.
The sufficient condition `D t < 3^j N_c` is valid, but is not necessary.

## 2. Census controls and evidence tier

`experiments/paradoxical_excursion_audit.py` independently walks every odd start through
5000, reads its parity word, and reproduces every reported row. It checks (T), all three
sign cases, and the corrected endpoint bound below. This covers all 320 A1-reported starts
and checks the empty length-54 row in this range. **It does not redo A1's completeness
scan up to X(m)** (up to 1,363,096,076 here); the distinction is printed by the probe.

| m | starts | trunk counts | admissions lost if N_d is dropped | suffix peak/t range |
|---|---:|---|---:|---|
| 8 | 4 | 5:1, 7:1, 11:2 | 1 | 8/5 … 26/7 |
| 27 | 19 | 31:13, 47:6 | 6 | 350/47 … 890/31 |
| 46 | 101 | 31:22, 47:26, 61:1, 71:7, 91:39, 103:6 | 13 | 92/61 … 3644/31 |
| 54 | 0 | none | 0 | none |
| 65 | 155 | 23:1, 31:56, 47:48, 71:4, 91:40, 103:6 | 0 | 80/23 … 4616/31 |
| 73 | 41 | 31:26, 47:15 | 41 | 1079/47 … 4616/31 |

The probe also verifies convergence of every hit. Shortcut hitting-time ranges are
10–15, 70–80, 58–93, 72–112, and 89–106 at the five nonempty lengths, respectively.
Thus the kickoff's blanket `τ=58–95` is inaccurate; the convergence conclusion survives.

`trunk_climb_one_step_control` gives another kernel-checked boundary: `(n,m)=(91,46)`
has minimum `61` at step `45` and endpoint `92`. Its entire trunk climb is **one step**.
Thus the concrete normalized proposals `C_trunk ≥ m` and `C_trunk ≥ sqrt(m)` are false.
This does not refute a bound `C_trunk ≥ c m^p` with unspecified constants and a sufficiently
large cutoff, or an exponential bound with unspecified constants. The table alone cannot
decide those asymptotic statements. The probe also checks 15,300 arbitrary-cut identities,
including trivial-cycle equality, declining endpoints, and supercritical words.

## 3. Exact null identities: derivations, not fitted formulas

Population: words starting odd, length `m≥1`, `1≤a≤m`. Let `S(m,a)` be the sum of their
numerators. Appending an even letter leaves `N` fixed; appending odd sends `N` to
`3N+2^r` after a prefix of length `r`. For
`F_m(z)=Σ_a S(m,a) z^(a-1)`, this gives

```
F_1=1,
F_(m+1)=(1+3z) F_m + 2^m z (1+z)^(m-1),
F_m=(1+3z)^(m-1) + 2z [ (2+2z)^(m-1)-(1+3z)^(m-1) ]/(1-z).
```

The quotient is a polynomial (finite geometric sum). Extracting the coefficient of
`z^(a-1)` proves the closed form, including `a=1` with an empty sum:

```
S(m,a)=C(m-1,a-1)3^(a-1) + Σ_(r=0)^(a-2) C(m-1,r)(2^m-2·3^r).  (S)
```

For adjacent letters at positions `r,r+1`, replacing `TF` by `FT` raises `N` by
`2^r 3^(ones of following suffix)`. Sorting the letters after the forced first `T`
therefore proves the maximum at `T F^(m-a) T^(a-1)` and minimum at `T^a F^(m-a)`:

```
N_max = 2^(m-a+1)(3^(a-1)-2^(a-1)) + 3^(a-1),
N_min = 3^a-2^a.                                            (MAX)
```

Thus for `D>0`, every admitting start satisfies `n≤floor((N_max-1)/D)`, justifying
the mathematical bound behind A1's complete census. The new probe checks the swap,
sum, minimum and maximum formulas on **all words**, including supercritical ones,
through length 10. The existing DP/enumeration selftest checks all 78 subcritical
pairs through length 16, and DP versus closed form at the eight near-critical pairs.

For the odd-residue model choose uniformly from `{3,5,…,M+1}`. Counting `Dn<N` gives
exactly `clamp(floor((N-1-D)/(2D)),0,M/2)` favorable choices. Hence

```
p_cont=min(1,N/(DM)),
p_odd=(2/M) clamp(floor((N-1-D)/(2D)),0,M/2),
0 ≤ p_cont-p_odd < (3+1/D)/M.                                (ROUND)
```

The old comment's strict lower bound was wrong when both probabilities saturate at one;
it is corrected. The probe checks (ROUND) against directly counted odd residues, including
both clipping boundaries. It is an elementary counting theorem, not a statement about
actual canonical residues.

## 4. The null-model law (proved about the model)

**Theorem.** Along any sequence of integer pairs with `m→∞`, `3^a<2^m`, and
`a/m→ρ=log(2)/log(3)`, the continuous model and odd-residue model satisfy

```
2δ R → 1,                  2δ R_odd → 1,
δ=(2^m-3^a)/2^m.
```

In particular `R ~ 1/(2δ)`. The theorem does not require `δ→0`; it specifies relative
asymptotics when `δ` varies. Its evidence tier is the following mathematical proof plus
exact-integer probes, not a new Lean asymptotics theorem.

**Proof of unclipping.** In fact no admissible subcritical pair clips. From (MAX),
`N_max < (2/3) M (3/2)^a`, since the omitted term is `-M+3^(a-1)<0`.
If `M≥2·3^a`, then `D≥M/2`, so
`N_max/(DM) < (4/3)2^(-a) < 1`.
In the other regime and for `a≥6`, the repository's proved `FrontA.sep_two_three` says
`D≥3^a 2^(-a/3)`. Consequently

```
N_max/(DM) < (2/3)2^(-2a/3) < 1.
```

For `1≤a≤5` the near-window condition leaves only
`(m,a)=(2,1),(4,2),(5,3),(7,4),(8,5)`, all directly checked by the small selftest.
Thus `R=S/(DM)` for all actual subcritical parameters. This deduction uses the
already-proved separation theorem; it does not obtain a Diophantine lower bound
from binomial probability or silently assume that small `δ` cannot cause clipping.

**Proof of the limit and error bound.** Set `h=m-1`, `U~Bin(h,1/2)`, `V~Bin(h,3/4)`.
Dividing (S) by `M²` gives exactly

```
S/M² = [P(U≤a-2)-P(V≤a-2)]/2 + P(V=a-1)/4.                 (BIN)
```

Whenever `h/2<a-1<3h/4`, (BIN) and disjointness of the two V-events give

```
|1-2δR| ≤ P(U≥a-1)+P(V≤a-1)
         ≤ h/[4(a-1-h/2)²] + 3h/[16(3h/4-a+1)²].           (ERR)
```

The last inequality follows by applying Markov to the squared centered binomials;
their variances are `h/4` and `3h/16`. Since `1/2<ρ<3/4`, both gaps grow linearly
with m, and (ERR) tends to zero. The exact probe checks (BIN), unclipping and (ERR)
at m=100,200,400,800; the respective observed relative errors are approximately
`8.93e-3, 2.13e-4, 1.62e-7, 1.28e-13`. No floating-point comparison decides a check.

Finally (ROUND) gives `0≤R-R_odd<(3+1/D)C(m-1,a-1)/M`. The last factor is
`P(U=a-1)/2→0` by the same tail estimate, and `D≥1`, `δ<1`.
Thus the absolute model discrepancy tends to zero, and `2δR_odd→1` as well. ∎

**Why this is not a prediction.** The model chooses a surrogate residue independently
of the word's numerator. The actual canonical residue identifies the word through its
parity trace; hence its numerator is a deterministic, nonconstant function of that residue
on a nondegenerate fixed-(m,a) population. They cannot be independent. Clusters of
preimages sharing suffixes exhibit the concrete mechanism, and (AC) shows precisely
which prefix correction changes admission. Dependence *between different word events*
alone would not change their expected sum if the correct conditional marginals were
retained. It is the unsupported **residue/numerator marginal law** that prevents treating
R as an expected census count. Nor have the trunk clusters themselves been proved
independent. The orbit-census comment is corrected on this point. No claim that the
observed/model ratio diverges, converges, or has a specific law is justified here.

## 5. Excursion node classification and the remaining hypothesis

For a minimum `t>0`, put `C_end=y/t` and `C_trunk=max_(k≤i≤m) x_i/t`.
The exact additive expansion is `E=N/M=(1/2)Σ_(i odd) Q_(i+1)`, where Q is the
suffix multiplicative coefficient. Every suffix satisfies
`Q_(i+1) x_(i+1)≤y`, so `Q_(i+1)≤y/t`. Therefore every admitting segment satisfies

```
δ n < E ≤ a C_end/2 ≤ a C_trunk/2,
C_trunk ≥ C_end > 2δ n/a.                                 (E)
```

This is a valid useful implication, proved by the displayed finite sum and checked for
every census control. It relates growth to **start size**, not to length alone.
To obtain a bound `C_trunk>g(m)` from (E), the exact sufficient missing input is
`n≥a g(m)/(2δ)` for the admitting segments in question. No such start-length input
is supplied by the census, finite verification, or the null model.

| candidate node | classification | reason / exact scope |
|---|---|---|
| Exact decomposition with N_d | **proved** | New Lean identity and strict/equality criteria; valid for every cut. |
| Exact admission from (t,w,k,j,D) alone | **refuted** | Kernel witness 2305 versus 2313. An existential optimization over preimages is a different statement. |
| Drop N_d to get a sufficient test | **proved** | N_d≥0 in (AC); loses 61 of the 320 controls. |
| E and H sandwich: H/2≤E≤aH/2; Hs=max(1,3H/2) | **proved** | Finite suffix sum and maximum; existing exact controls. Does not identify a large realized excursion. |
| Large E forces unbounded Hs for arbitrary words | **refuted** | Balanced ρ-words followed by 00 have Hs=1, E≥a/24. These are word controls, not admitting-segment counterexamples. |
| Subcriticality bounds the prefix peak | **refuted** | `T^a F^b` has arbitrarily large prefix multiplier `(3/2)^a` with subcritical total coefficient. |
| C_trunk≥sqrt(m) (or ≥m), with unit coefficient and no cutoff | **refuted** | Kernel control (91,46) has C_trunk=92/61. |
| Some uniform polynomial or exponential lower rate in m for all admitting segments | **open-and-stronger-than-known-inputs** | No general refutation of unspecified constants; (E) needs a new start-length bound. Such a rate also excludes nontrivial cycles, as explained below. |
| Exponential excursion follows just from finite verification | **refuted as an inference** | Verification supplies no global hitting-time rate; all 320 examples converge. Neither their starts nor their trunks must exceed the verified bound. |
| Exponential trunk growth conditional on global logarithmic hitting time | **proved implication, hypothesis open-and-stronger-than-known-inputs** | If every n>2 has τ(n)≤C log n, then admitting m<τ(n), so n>exp(m/C). The proved polynomial separation δ≥c m^(-436) and (E) give C_trunk>c' exp(m/C)/m^437. The hitting-time premise already assumes quantitative global convergence. |
| Uniform bounded length of all acyclic paradoxical segments | **equivalent-to-existing-target** | Exactly FiniteAcyclicParadoxical: bounded length gives finitely many words and n<N/D; finiteness gives a maximum length. A front-normalized restriction gives only that restriction's finiteness, not automatically the unrestricted target. |
| Uniform bound on excursion derived by assuming that finiteness target | **proved but circular as a route** | A finite set has a maximum excursion. This cannot independently establish finiteness. |
| R~1/(2δ), and the same law for R_odd | **proved about the model** | (S), (MAX), separation, (BIN), (ERR), (ROUND). |
| Transfer the model law to the actual word census | **not-yet-understood** | Requires a quantitative arithmetic law for canonical residues versus numerators; clustering exposes the dependence but supplies no replacement law. |
| Every future long-segment trunk belongs to the trajectory of 27 | **open-and-stronger-than-known-inputs** | A1 observation through m=80, not a universal theorem. Its bounded suffix endpoints would bound all such starts; together with their verified convergence this would force finiteness in that scope. |

Here τ is the shortcut hitting time of `{1,2}`. On a convergent orbit, no value repeats
before τ; counting distinct integers below a peak gives only a linear bound on the
absolute peak in terms of τ (and a polynomial counting bound if using a different
encoding), not an exponential one. Finite verification gives a finite table of τ values,
not `τ(n)≤C log n` globally. If convergence and a bound on the *start* are absent,
this counting fact alone gives no growing ratio relative to the trunk.

**Cyclic equality is not discarded.** (T) and its equality theorem apply directly to
cycles. Moreover, even a lower bound `C_trunk≥g(m)→∞` stated only for *strict* acyclic
paradoxical segments would rule out nontrivial cycles: start at an odd cycle minimum,
traverse r full periods, then stop at a larger cycle member. The cycle multiplier q is
strictly below one by its positive additive remainder, so these words become subcritical
for large r, with lengths tending to infinity and a fixed bounded excursion. They are
strict AcyclicParadoxical segments despite repeating values. The definition means
endpoint growth, not pairwise-distinct orbit values. Thus the proposed universal
excursion law is not a divergence-only lemma. For divergence, such a lower bound by
itself supplies no contradiction without a separate upper bound.

**Next decision:** A2 has exposed the extra arithmetic datum and the global hypothesis
behind the exponential route. Stop that route here. Campaign B should derive an
arbitrary-block integer cascade and test a genuinely new composition inequality,
retaining preimage remainders; do not launch a new excursion formalization tranche.
