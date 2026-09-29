# A slope obstruction to uniformly bounded affine-orbit coalescence

> **Follow-through:** [Q1 coalescence and separation](RESEARCH-2026-09-29-q1-coalescence.md) now gives a sparse positive class and an all-depth obstruction to a uniform bound for the remaining Q1 pair.

This applies the repository's existing [fixed-tail slope obstruction](RESEARCH-2026-09-28-symbolic-repair.md) to the new hard64 auxiliary families.  The mechanism is already in the negative inventory; the new work is the ten-family ledger, its explicit finite-exception count, and identification of the sole slope-compatible auxiliary.  It does not address parameter-dependent path lengths or a catalytic relation that never asks two ordinary orbits to meet.

## Exact finite-exception theorem

Let $T(x)=x/2$ for even $x$ and $(3x+1)/2$ for odd $x$.  Let $n(s)=A+Bs$ and $u(s)=C+Ds$ be positive integer families for $s\in\mathbb N$, with $B,D>0$.  Suppose the reduced rational $B/D$ has a prime outside $\{2,3\}$ in its numerator or denominator.

For every fixed $K$, the set
\[
E_K=\{s\ge0:\exists\,0\le i,j\le K,\quad T^i(n(s))=T^j(u(s))\}
\]
is finite.  In fact $|E_K|\le(2^{K+1}-1)^2$.  Consequently, on **every infinite subclass** of parameters, all but finitely many members avoid coalescence within $K$ steps on each side.

*Proof.*  Fix a parity word $w$ of length $i$ and let $o(w)$ be its number of odd symbols.  On the branch realizing $w$,
\[
T^i(x)=\frac{3^{o(w)}x+\beta_w}{2^i}
\]
for a nonnegative integer $\beta_w$ depending only on $w$.  The formula follows by induction: an even step retains $\beta_w$, while an odd step replaces it by $3\beta_w+2^i$.  Fix also a parity word $v$ of length $j$.  Equality of the two affine branch formulas at parameter $s$ has slope coefficient
\[
\frac{3^{o(w)}B}{2^i}-\frac{3^{o(v)}D}{2^j}.
\]
If it vanished, then $B/D=2^{i-j}3^{o(v)-o(w)}$, whose reduced numerator and denominator have no prime outside $\{2,3\}$.  By hypothesis it is nonzero, so this branch pair contributes at most **one** parameter value.  There are at most $2^i2^j$ word pairs, including the empty word at length zero.  Summing over $0\le i,j\le K$ yields $(\sum_{i=0}^K2^i)^2=(2^{K+1}-1)^2$.  Correlated parity restrictions between $n(s)$ and $u(s)$ can only lower that count.  ∎

The condition is only a necessary test: a $\{2,3\}$-smooth slope ratio permits equal slopes for some word counts but does not force equal intercepts or realizable joint parity words.  The theorem is about a **fixed** $K$; allowing $i,j$ to grow with $s$ leaves a countable union of finite sets, which can be infinite.

## Hard64 slope ledger

Use the exact parameterization in [CubicPeel.lean](CollatzMoonshot/Obstructions/CubicPeel.lean):
\[
n(s)=25542881863+39026668800s,\qquad
m(s)=17959838810+27440626500s.
\]
For the older lower-family labels, substitute $t=16475+25172s$ and $h=2+95t=1565127+2391340s$ into
$c=3689+6528h$, $d=5425+9600h$, $b=661+24480t$, $x=3349+124032t$, and $z=785+29070t$.  The newer $q_1,q_2,e_1,e_2$ slopes come directly from CubicPeel.lean.  With $B=39026668800$, the exact reduced ratios are:

| Family $u$ | Slope $D$ | Reduced $B/D$ | Outside prime |
|---|---:|---:|---:|
| $m$ | 27440626500 | $64/45$ | $5$ |
| $c$ | 15610667520 | $5/2$ | $5$ |
| $d$ | 22956864000 | $17/10$ | $5,17$ |
| $b$ | 616210560 | $190/3$ | $5,19$ |
| $x$ | 3122133504 | $25/2$ | $5$ |
| $z$ | 731750040 | $160/3$ | $5$ |
| $q_1$ | 2744062650 | $128/9$ | none |
| $q_2$ | 6294624000 | $31/5$ | $5,31$ |
| $e_1$ | 3027931200 | $116/9$ | $29$ |
| $e_2$ | 5575238400 | $7$ | $7$ |

Thus the theorem excludes a uniform bounded ordinary-orbit coalescence strategy from $n(s)$ to **every listed label except $q_1(s)$**, on any infinite subprogression of $s$.  In particular, the smaller endpoint $m$ does not evade: $64/45$ contains a factor $5$.  These are exclusions of a proposed *bounded coalescence mechanism*, not exclusions of convergence or of a variable-length meeting.

The $q_1$ exception is algebraically real.  The committed formulas give
\[
128q_1(s)=9n(s)+1.
\]
Also $n(s)\equiv71\pmod{128}$, so its first seven shortcut parities are the fixed word $(1,1,1,0,1,0,1)$, with five odd steps.  Direct composition yields
\[
T^7(n(s))=\frac{243n(s)+283}{128}=27q_1(s)+2.
\]
This explains the $\{2,3\}$-smooth slope ratio.  It is **not** an orbit-coalescence identity with $q_1$: the two displayed values differ, and later bounded or unbounded meeting remains unproved by this test.

As a sanity control for the theorem's direction, $a(s)=T(n(s))$ has slope $58540003200$ and $B/D_a=2/3$, and the actual sixth iterate $p(s)=T^6(n(s))$ has slope $49393127700$ and $B/D_p=64/81$.  Both are $\{2,3\}$-smooth, as required by their known fixed-prefix relation to $n$.

This note uses exact affine formulas already present in the repository.  It adds no census, no claim about parameter-dependent coalescence time, and no Lean theorem.


The persistent `second-frontier-cubic` CLI now computes these slope ratios from adjacent affine rows and reports the surviving necessary-condition candidates.  Its subprocess suite checks all ten hand-derived ratios and the sole survivor `q1`.  Passing this test does not certify coalescence.
