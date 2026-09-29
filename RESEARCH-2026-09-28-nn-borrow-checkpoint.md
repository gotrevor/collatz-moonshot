# From NN comparison to two symbolic supply rules

**2026-09-29 scope correction:** restricted-palette closure is optional, not a supply-existence prerequisite.  The known semigroup theorem supplies any finite 3-free catalyst.  See [the corrected route](RESEARCH-2026-09-29-unrestricted-supply-addendum.md); target-free vertex balance and termination remain open.

The productive connection is growing finite constructions with a uniform endpoint condition.  NN disjunctivity chooses a location for each requested word; Collatz must handle each prescribed integer.  The [source comparison](RESEARCH-2026-09-28-nn-collatz-bridge.md) identifies the exact NN consumers and the limits of the analogy.  In particular, the CRT mean theorem averages over a varying sample.  It does not supply directed vertex balance in one Collatz certificate.

## A positive induction step on a residue subclass

Write r_v=2v/(3v+1), and recall the lower five-head family
n(h)=9223+16320h, u(h)=3689+6528h, d(h)=5425+9600h.
Its established exchange is {5n,u} -> {n,d}, with u,d<n.  The outstanding supply problem is obtaining a unit word containing u.

The numerical row at h=2 is part of an exact family.  For every t>=0, set

| label | affine formula |
|---|---:|
| h | 2+95t |
| u | 16745+620160t |
| x | 3349+124032t |
| z | 785+29070t |
| b | 661+24480t |

Then u=5x, 76b=15x+1, and 64z=15x+5.  These identities imply

r_x r_z = r_u r_b.

All four labels are positive, odd and 3-free.  Moreover x,z,b<u<n.  Thus **if units supplying x and z are available**, multiplying those units and replacing {x,z} by {u,b} supplies a unit containing u.  This statement does not assume a trajectory for n.

[RecursiveBorrow.lean](CollatzMoonshot/Obstructions/RecursiveBorrow.lean) formalizes the legal pair replacement and the height/parity conditions.  It does not assert units for x,z, recursive closure, or full repair.

The second observed row, at h=1, also extends symbolically.  For h=1+79t:

| label | affine formula |
|---|---:|
| u | 10217+515712t |
| x | 3005+151680t |
| z | 5635+284400t |
| b | 2425+122400t |

Again r_x r_z=r_u r_b and x,z,b<u.  To derive it, write s=217+384h and use x=5s, u=17s, z=5(15s+1)/8, b=25(51s+1)/316.  The integrality condition reduces to h=1 modulo 79.  This second family is an exact algebraic/CLI result in this batch, not a claim about the Lean module.

## Arbitrarily long growth survives the first subclass

The shortcut orbit's fixed first six steps end at p(h)=11674+20655h, and all six values are above n(h).  On h=2+95t,

p(h)+1 = 52985+1962225t.

The coefficient 1962225 is odd.  For every j>=2 there is a least t modulo 2^j for which this quantity is divisible by2^j.  If p+1=2^q s with s odd and q>=j, then

T^(6+i)(n)=3^i 2^(q-i) s-1,  0<=i<=q.

These values stay above n.  The symbolic supply rule therefore applies to a subclass with unbounded initial growth, rather than only to the members already handled by descent at steps 7 or 8.  This is an elementary residue construction, not a probabilistic assertion about orbit parities.

## Why the failed affine scan did not exclude this

The retained `experiments/affine_scan.py scan` checks affine rows passing through sampled pairs of heights (0,2), (1,3), and (0,3), with the stated positivity, slope and input-height restrictions.  It finds no polynomial identity through those endpoint pairs.  Neither new residue subclass contains any of those pairs.  The failed test excludes interpolation across its selected anchors only; using it to dismiss all affine supply rules would have lost the formulas above.

At h=0, a complete fixed-label neighbor calculation finds no exchange introducing 3689 from two smaller positive odd inputs.  The weaker bound n=9223 admits {2635,3953}->{2767,3689}.  This is a possible exceptional base case, not an obstruction to every recursive scheme.

## A formal negative control for the CRT analogy

[LocalGlobalBorrow23.lean](CollatzMoonshot/Obstructions/LocalGlobalBorrow23.lean) proves both statements:

- For every prime power separately, positive odd 3-free smaller inputs satisfy the Q equation modulo that prime power with a suitable companion.
- No positive odd smaller input pair has an exact natural-number companion.

The witnesses may change with the prime.  A finite joint modulus already excludes every pair, so this is not a failure of CRT.  The [local-global note](RESEARCH-2026-09-28-collatz-local-global.md) gives the exact denominator test and a reproducible blocking modulus.

## The next mathematical target

Find a collection of supply rules closed under their required smaller inputs, with explicit base constructions and a decreasing rank.  The two rules above reduce label height but do not provide that closure.  For example, in the first rule, x is always 3349 modulo 6528, whereas the original auxiliary progression is 3689 modulo 6528, so even its first input leaves the original progression.  A mutually recursive collection of residue classes is the concrete target.

Even successful supply closure would settle only the borrowing part.  The full catalytic route still needs a target-free continuation balancing directed vertices after the five-head exchange.  The pairwise and anchored-operator branches retain their own independent missing estimates.

## Reproduction

Run the persistent external-CLI suites with `experiments/catalytic_palette.py test`, `experiments/repair_family.py test`, `experiments/borrowability_descent.py test`, and `experiments/affine_scan.py test`.  The probes expose complete fixed-label scans separately from bounded searches and symbolic formulas.  The standard root `lake build` includes both new Lean modules.

Validation: combined persistent subprocess suite, **38 passed**.  Both scoped Lean workers completed and their host root builds passed.  The exact 32-step growth controls for both supply subclasses are saved in [recursive_growth_32.json](experiments/recursive_growth_32.json); these evaluate only the six fixed steps and the algebraic odd-run formula.
