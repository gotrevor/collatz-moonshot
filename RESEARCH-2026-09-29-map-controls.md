# Known-negative map controls for the certificate-repair toolkit

```sh
./experiments/research_lifts.py map-control
./experiments/research_lifts.py supply 5 --multiplier 3 --offset -1
./experiments/research_lifts.py certificate --twos 4 --odd-sources 11 25 37 --multiplier 3 --offset -1
./experiments/research_lifts.py fate 5 --multiplier 3 --offset -1
./experiments/research_lifts.py cubic-twin 4307989
./experiments/research_lifts.py exchanges --multiplier 5
./experiments/research_lifts.py test
```

This is step 1 of [the ordinal-repair odds review](REVIEW-2026-09-29-ordinal-repair-odds.md): run the certificate-repair framework on maps where convergence is known to fail, and see whether anything in it is specific to 3x+1.

**Verdict.**  Every ingredient transfers.  Supply, exchanges, signed-flow extraction and the ω^ω obligation rank all exist for 3x−1 and 5x+1, at starts that never reach 1.  The toolkit's only sign-sensitive fact, the unit two-count inequality, separates 3x−1 but not 5x+1.  No 3x+1-specific lever emerged.  Per the review's gate, the **current** certificate-repair toolkit is retired as a proof route; its instruments remain useful as diagnostics.  This is a research retirement, not an impossibility theorem for repair methods: a method carrying a genuinely distinguishing input would be a new route.

## Maps and conjugation

Write \(T_{q,c}(x)=(qx+c)/2\) for odd \(x\) and \(x/2\) for even \(x\), and \(\rho_u=u/T_{q,c}(u)\).  The controls are \((q,c)=(3,-1)\) and \((5,1)\).

For 3x+1, \(r_u=2u/(3u+1)\).  At a negative label, \(r_{-u}=2u/(3u-1)=s_u\), the 3x−1 ratio.  So **3x−1 on positive integers is 3x+1 on negative integers**, and the 3x−1 semigroup is the 3x+1 semigroup with negated labels.  Every rational-function identity among 3x+1 ratios with affine labels \(f(a)\) holds among 3x−1 ratios with labels \(-f(-b)\).  The 2-adic and 3-adic congruence conditions are symmetric under negation.  Only positivity and size comparisons can distinguish the two.

Non-convergent positive starts: 3x−1 has the cycles \(5\to7\to10\) and \(17\to25\to37\to55\to82\to41\to61\to91\to136\to68\to34\), and 5x+1 has \(13\to33\to83\to208\to104\to52\to26\) and \(17\to43\to108\to54\to27\to68\to34\).  5x+1 at 7 does not reach 1 within the step cap and is conjecturally divergent; nothing below depends on that.

## The scalar of a flow is the evaluation of its boundary

For a finite edge flow \(f\) on the functional graph of any \(T_{q,c}\), each edge \(x\to T(x)\) carries the ratio \(x/T(x)=\mathrm{ev}(e_x-e_{T(x)})\), where \(\mathrm{ev}(e_v)=v\) extends multiplicatively.  Hence

\[
\prod_x (x/T(x))^{f(x)}=\mathrm{ev}(-\partial f).
\]

A scalar certificate of value \(n\) is therefore a flow whose boundary differs from the path boundary \(e_1-e_n\) by a defect \(\delta\) with \(\mathrm{ev}(\delta)=1\).  Convergence of \(n\) is the statement that \(e_1-e_n\) sums to zero on every weak component, which is exactly the signed-flow criterion (`SignedFlow.lean`, stated there for 3x+1; its proof uses only that the basin indicator is constant along edges, so it holds for any functional graph).  The kernel of \(\mathrm{ev}\) does not respect components, so a scalar certificate carries no information about the component of \(n\).  This is a one-line paper observation, not a Lean theorem.

## Supply transfers at non-convergent starts

`supply` solves an integer program for the fewest odd labels (labels ≤ 20000 whose \(u\) and \(T(u)\) are 60-smooth), then re-evaluates the word exactly.

| Map | n | Orbit | Word \(2^e\prod\rho_u\) | Label components |
|---|---|---|---|---|
| 3x−1 | 5 | cycle 5,7,10 | \(2^4\,s_{11}s_{25}s_{37}\) | 11→1; 25, 37→17-cycle |
| 3x−1 | 17 | 17-cycle | \(2^7\,s_{47}s_{551}s_{1003}s_{1025}s_{2597}\) | 5-cycle, 1, 5-cycle, 17-cycle, 1 |
| 5x+1 | 13 | 13-cycle | \(2^9\,t_{27}t_{403}t_{629}t_{11011}\) | 17-cycle, three unresolved at cap |
| 5x+1 | 17 | 17-cycle | \(2^7\,t_1t_{51}\) | both reach 1 |
| 5x+1 | 7 | unresolved | \(2^7\,t_3^2t_7\) | 3→1; 7 unresolved |

Hand check of the first row: \(T(11)=16\), \(T(25)=37\), \(T(37)=55\), and \(16\cdot(11\cdot25)/(16\cdot55)=5\).  Taking the four factors of 2 as the path \(16\to8\to4\to2\to1\), the flow is the path \(11\to1\) plus the segment \(25\to55\).  Its defect is

\[
\delta=e_5-e_{11}+e_{55}-e_{25},\qquad \mathrm{ev}(\delta)=\frac{5\cdot55}{11\cdot25}=1,
\]

with component sums \(+1\) on the 5-cycle, \(-1\) on the component of 1, and \(0\) on the 17-cycle.  Applegate–Lagarias characterize the whole 3x+1 semigroup; the analogous characterizations for these maps are not checked here and are not needed, because the explicit words already put scalar certificates at non-convergent starts.

## Exchanges transfer

- **3x−1, by conjugation.**  The CubicPeel cubic at \(a=-b\) becomes \(s_{5b+2}\,s_{(3b+1)/64}\,s_{5(2b+7)/93}=s_b\,s_{(3b-1)/58}\,s_{(2b+7)/21}\).  At \(b=4307989\) all six labels are positive, odd and prime to 3: \((21539947,201937,463225)\) against \((4307989,222827,410285)\), with common value \(574399/1938592\).
- **Every map has a 2-for-2 grammar.**  Exchange classes with labels below 300: 44 for 3x+1, 39 for 3x−1, 32 for 5x+1.  Hand-checked examples: \(r_7r_{121}=r_{11}r_{17}=11/26\) (the last move of the catalytic repair of 7), \(s_5s_{147}=s_7s_{15}=21/44\), \(t_5t_{91}=t_7t_{15}=35/228\).

## Where any rank must fail

On 3x−1, start from \(5=2^4s_{11}s_{25}s_{37}\).  Every move in the toolkit exists, and so does the multiset rank.  No terminal state exists, because \(e_1-e_5\) is not a boundary.  So any block rule with a strictly decreasing well-founded rank fails **coverage** somewhere in the repair of this certificate.  The failure is structural.  Under 3x−1, 5 is the least element of its component (1 through 4 reach 1), so the obligation "5 converges" admits no smaller-seed borrowing at any depth; the same holds at 17 (every start below 17 reaches 1 or the 5-cycle).  Under 5x+1 the least element of the 13-cycle's component is 5, since \(5\to13\) and 1 through 4 reach 1.  At 13 a smaller seed does exist, but borrowing it only moves the obligation to 5, where it fails.  A repair rank for 3x+1 must use a property that fails at these starts.

## What that property could be

The only sign-sensitive fact available is the **unit two-count inequality**.  Since \(\rho_u<2/q\) when \(c=+1\) and \(s_u>2/3\) for 3x−1, a value-one word with \(k\) odd labels and \(e\) twos satisfies \(q^k<2^{e+k}\) when \(c=+1\), and the reverse for 3x−1:

| Unit | k | e | Inequality |
|---|---|---|---|
| U8 (3x+1) | 5 | 3 | 243 < 256 |
| U13 (3x+1) | 8 | 5 | 6561 < 8192 |
| cycle 5 (3x−1) | 2 | 1 | 9 > 8 |
| cycle 17 (3x−1) | 7 | 4 | 2187 > 2048 |
| cycle 1 (5x+1) | 2 | 3 | 25 < 32 |
| cycle 13 (5x+1) | 3 | 4 | 125 < 128 |

It separates 3x−1 and fails to separate 5x+1, whose positive cycles are contracting words exactly as 3x+1 units are.  Separating 3x+1 from 5x+1 needs something about the multiplier beyond this sign.  The known candidates are the drift, \(\log(3/4)<0<\log(5/4)\), on the divergence side, and the Diophantine size of \(|2^m-3^k|\) against the word constant on the cycle side; they are candidates, not a proved exhaustive list.  The certificate-repair toolkit consumes neither.  They are the inputs of Front B and Front A respectively, so a repair proof using them would lean on those fronts for its distinguishing step.

## Consequence and scope

- The review's step 1 is complete and did not expose a 3x+1-specific lever.  The certificate-repair route (catalytic repair, borrowing, Q and cubic exchanges, completed blocks, ordinal repair) is **closed as a proof route**.  The obstructions of 2026-09-27..29 stand as its record; do not reopen it with another rule family or rank template.
- **Reopening criterion:** a rule or rank that provably fails on 3x−1 at 5 **and** on 5x+1 at 13, and names the input that makes it fail there (drift and the \(2^m-3^k\) arithmetic are the known candidates).
- `BoundedMerger` excludes bounded-depth smaller-seed mergers only; it does not exclude a locally computable rank.  Such a rank is not part of this toolkit and is not retired by this note.
- **Evidence tiers.**  Certificates, fates, the cubic twin, exchange counts and unit values are exact computations through the shipped CLI, with hand anchors in `experiments/test_research_lifts.py`.  The boundary-evaluation identity and the conjugation transfer are paper arguments.  Nothing new is claimed in Lean.  An optional Lean anchor would be the 3x−1 certificate at 5 together with its cycle, both decidable; no lap is launched for it.
