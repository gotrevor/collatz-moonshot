# Finite prefix peeling is automatic; exact return and boundary tests

This audits the [ordinal repair checkpoint](RESEARCH-2026-09-29-ordinal-repair-checkpoint.md) against the [unrestricted supply lemma](RESEARCH-2026-09-29-unrestricted-supply-addendum.md).  Applegate–Lagarias supplies arbitrary finite 3-free catalysts, but a local peel that merely exposes known Collatz edges is automatic.  The useful boundary is exact: returning **one identical unit** after a fixed central script is equivalent to nonnegativity of the base endpoint plus 3-free support of its prefix-deficit catalyst.  A completed block is a sufficient search architecture; a finite signed exact-boundary flow is an alternative final certificate that needs no positivity.

## Automatic finite-prefix theorem

Let $T$ be the shortcut Collatz map, $g_x=x/T(x)$ its edge generator, and let $X$ be any finite positive generator word of scalar value $n$.  For a known finite actual prefix
$n=n_0\to n_1\to\cdots\to n_k$, let $F_k$ be the multiset of the $k$ edge generators $g_{n_i}$, with each occurrence still attached to its source vertex $n_i$.  Its scalar value telescopes to $v(F_k)=n/n_k$.

If every odd label in $F_k$ is prime to 3, Applegate–Lagarias gives a value-one word $W_k\supseteq F_k$.  Set $R_k=X+W_k-F_k$.  It is nonnegative and
\[
v(R_k)=\frac{v(X)v(W_k)}{v(F_k)}=n_k.
\]
Thus
\[
X+W_k=F_k+R_k
\]
exists for **every** such finite prefix and **every** scalar-$n$ word $X$.  If $3\nmid n$, every forward iterate remains prime to 3, so the hypothesis holds for every $k$.  More generally, the condition on $F_k$ is exact: a value-one word can contain it if and only if none of its odd labels is divisible by 3.  A prefix containing an odd multiple of 3 cannot be borrowed wholesale in this way.  After that odd step, the orbit is 3-free, so its later tail is eligible.

The boundary of the attached actual prefix is also automatic:
\[
\partial F_k=\sum_{i<k}(\mathbf e_{n_i}-\mathbf e_{n_{i+1}})
             =\mathbf e_n-\mathbf e_{n_k}.
\]
The remainder $R_k$ has **only a scalar value constraint**.  In particular, the factor 2 in a borrowed unit has no vertex source until one is assigned, and value one does not make the unit's directed boundary zero.

**No-progress criterion.**  A purported repair step has no more content than the known finite prefix plus semigroup supply if its conclusion is only the existence of $W_k,F_k,R_k$ above, with no return of the same $W_k$, no exact boundary/flow condition on $R_k$, and no independent decrease of a complete state.  Peeling two, six, or an arbitrarily selected finite number of actual edges does not change this.  A rank counting exposed/remaining edges can be lowered by choosing a longer prefix while the unpaid unit complement $W_k-F_k$ grows.  It cannot certify termination.

## Exact common-unit return criterion

Represent certificates as nonnegative integer vectors on the generators $2,r_u$.  Fix a finite ordered list of **central** oriented scalar-preserving rules $(\ell_i,r_i)$, without arbitrary unit insertion among them, and source vector $X$.  Put
\[
s_0=0,\quad s_j=\sum_{i\le j}(r_i-\ell_i),\quad
\Delta=s_N,\quad Y=X+\Delta,
\]
and define the finite prefix-deficit vector
\[
C(v)=\max\bigl(0,\max_i[\ell_i(v)-X(v)-s_{i-1}(v)]\bigr).
\]

**Completed-block theorem (fixed script).**  A block
\[
X\longrightarrow X+W
  \stackrel{\text{central script}}{\longrightarrow}Y+W
  \longrightarrow Y
\]
with a single value-one word $W$ inserted and returned, and nonnegative base endpoints, exists **if and only if** (i) $Y\ge0$ coordinatewise and (ii) every odd label in $C$ is 3-free.  Necessity: execution requires $W\ge C$, and a unit contains no 3-divisible odd factor.  Sufficiency: the Applegate–Lagarias criterion supplies $W\ge C$; the definition of $C$ makes every central rule available, and $Y\ge0$ permits the final return.  There is no useful word-size bound here, but none is needed for this existence statement.

This exposes the debt hidden by the current local peels.  In factor-count notation $[u]$ for one $r_u$, the two Q moves and the K64 cubic have total signed change
\[
\Delta_{\rm peel}
 =[n]+[a]+[d]+[b]+[e_1]+[e_2]
 -[5n]-[v]-[x]-[z]-[q_1]-[q_2].
\]
The fixed virtual prefix contains $[5n]$ and $[v]$, but does not contain the borrowed inputs $[x],[z],[q_1],[q_2]$.  Unless other **base** factors happen to supply those four labels, $X+\Delta_{\rm peel}$ has negative coordinates.  Making $W$ enormous does not help, because the same $W$ cancels at the block endpoint.  Additional central moves must replenish the consumed labels or replace the endpoint.  This is the precise gap between a scalar peel and a completed positive block.

## Signed flow is a different final acceptance condition

Let $B=\{u:T^j(u)=1\text{ for some }j\}$.  Its indicator is invariant under $T$: $\mathbf1_B(u)=\mathbf1_B(Tu)$.  For any **finite signed rational** edge flow $f$,
\[
\left\langle\mathbf1_B,\partial f\right\rangle
 =\sum_u f_u(\mathbf1_B(u)-\mathbf1_B(Tu))=0.
\]
Hence an exact boundary $\partial f=\mathbf e_n-\mathbf e_m$ with a known $m\in B$ forces $n\in B$; taking $m=1$ is the final case.  Positivity is unnecessary for this implication.  The existence of such a flow for arbitrary $n$ is itself equivalent to convergence, so it becomes a mathematical mechanism only when a **specified target-free construction** produces it, for example from a canonical certificate and a smaller known-basin endpoint.  Scalar product equality and the automatic finite-prefix boundary do not supply this missing exact boundary.

## An optional stronger local target

On the explicit K64 progression of [CubicPeel.lean](CollatzMoonshot/Obstructions/CubicPeel.lean), let $X_s(P_m)$ be the canonical inverse-five virtual certificate built from an arbitrary supplied balanced certificate $P_m$ for the smaller endpoint $m_s$.  Seek a **parameterized central script**, using Q moves, the proved variable cubic, and finitely described additional scalar identities, such that for every $s\ge0$ and every such $P_m$:

1. Its signed change extends $\Delta_{\rm peel}$, is supported on 3-free labels, and has a prefix-deficit catalyst $C_s$ with 3-free support.
2. $Y_s=X_s(P_m)+\Delta_s$ is coordinatewise nonnegative **without counting the borrowed unit**.  It contains the two genuine odd-edge factors $r_{n_s},r_{a_s}$ and has consumed the two virtual odd-edge factors $r_{5n_s},r_{v_s}$.
3. One identical AL-supplied unit $W_s\supseteq C_s$ can be inserted before and returned after the central script.  The script and its base endpoint are selected without reading the forward orbit of $n_s$ beyond those two explicit steps.

This **closed two-edge extraction** is strictly stronger than the present peels because the displayed $\Delta_{\rm peel}$ fails condition 2 whenever its four borrowed inputs are absent from the base.  It is not convergence restated: it asks only for two exact actual edges and allows the remaining certificate to have arbitrary directed defect.  Once a candidate block exists, a separate full-state rank can be tested across its completed endpoints; no decrease is asserted here.  A signed exact-boundary construction from $n_s$ to a known-basin $m_s$ would be a stronger alternative final target, with no positivity requirement, but merely postulating its existence would restate the restricted convergence claim.

The Applegate–Lagarias semigroup characterization is an established literature theorem, not yet a theorem in this repo's Lean development.  The completed-block criterion above is a paper proof.  No repo files or Lean builds were changed for this audit.


Operator assessment: this last fixed-script target is optional.  With unrestricted central scalar identities, endpoint selection can again be automatic via semigroup generation.  A prescribed rule family or a independently justified full-state rank is essential before treating it as a mechanism.  The main search now allows signed exact vertex balance as well as completed positive blocks.
