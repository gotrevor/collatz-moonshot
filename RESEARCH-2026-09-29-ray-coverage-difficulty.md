# Difficulty audit: universal coverage of the centered ray

Let \(T(x)=x/2\) for even \(x\) and \(T(x)=(3x+1)/2\) for odd \(x\).  The proposed state class consists of positive integer pairs

\[
 A+5=m(B-1),\qquad m=72\cdot3^j,\quad j\ge0,\quad B\ge2,
\]

where \(A\) is an actual frontier of a target orbit and \(B\) is its synchronized auxiliary.  A **return** means actual synchronized iterates \((A,B)\mapsto(A',B')\) that again satisfy this relation, with \(B'<B\).  The local rules and their uncovered residue are in `RESEARCH-2026-09-29-ray-fuel-exit.md`.

## What a complete coverage claim proves

Suppose a domain \(\mathcal S\) of represented positive pairs is closed under its asserted returns, and every \((A,B)\in\mathcal S\) has either (i) a finite target prefix reaching \(A=1\), or (ii) a finite actual return to another state in \(\mathcal S\) with smaller positive \(B\).  Strong induction on \(B\) proves that every represented target reaches 1.  The terminal must refer to the **target**: \(B=1\) cannot be a positive centered-ray state because it would force \(A=-5\).  A decrease of \(B\) at a point that leaves \(\mathcal S\) cannot be iterated and gives no such proof.

Conversely, if every represented target converges and the terminal is allowed at any actual synchronized time, its target eventually reaches 1, so the alternative above holds without using a return.  Thus the complete return-or-target-terminal statement is equivalent to convergence on its represented target set.  This equivalence identifies the unproved premise; it does not supply a mechanism for proving it.

For the present hard-family application, the restriction is already full Collatz strength.  The positive parameters with \(s=7+8t\), exact old fuel zero, and \(v\equiv7\pmod{4096}\) form an infinite arithmetic progression of original targets \(n(s)\).  Kenneth M. Monks' [Theorem 1.1, *The Sufficiency of Arithmetic Progressions for the 3x + 1 Conjecture*](https://monks.scranton.edu/files/pubs/SufficiencyRev4.pdf) proves that every positive arithmetic progression is **sufficient**: every positive orbit merges with an orbit from that progression.  Therefore convergence for all targets in this one uncovered progression implies convergence for every positive integer.  This is a literature input, not a theorem currently established in the repository's Lean development.  The converse follows from full Collatz convergence.  A universal coverage assertion on the actual hard progression is consequently equivalent to the full conjecture, despite its restricted-looking residue conditions.

There is also a simpler no-terminal obstruction.  If a nonempty positive ray class is closed under a proposed strict-\(B\) return, it has a state with least \(B\), which cannot return within that class.  In the unrestricted ray, \((A,B)=(67,2)\) is an explicit witness: no smaller positive \(B'\) can support a positive ray state.  In fact the finite shortcut chain is \(67,101,152,76,38,19,29,44,22,11,17,26,13,20,10,5,8,4,2,1\).  Thus a blanket demand for a same-ray return **without** a target terminal rejects a convergent state.  The well-founded rank requires a terminal or a justified transition to a different closed state class.

## The uncovered residue has one-sided descent, not coverage

After the first refill, the uncovered output \(m=216,e=0,v_1\equiv1\pmod{64}\) can be written

\[
 v_1=1+64h,\qquad (A,B)=(211+13824h,\ 2+64h),\qquad h\ge0.
\]

Its auxiliary has the fixed two-step prefix even, odd and

\[
 T^2(B)=2+48h<B\quad(h>0).
\]

At the same synchronized time the target has prefix odd, odd, so

\[
 T^2(A)=476+31104h,\qquad T^2(A)+5=648\bigl(T^2(B)-1\bigr)-167.
\]

The target is even and the centered-ray relation has acquired an offset.  For \(h=0\), \(B=2\) is periodic and the auxiliary inequality is equality; the actual hard-family intersection has \(h>0\).  The strict auxiliary descent for actual hard starts is real, but it is **not** a joint ray return and gives no connection from the target to an induction-known smaller value.  No proved inequality or transition currently turns this off-ray state into a covered class without analyzing the target's future parity choices.

A possible quantitative alternative makes the missing input explicit.  Fix the hard progression \(P\).  If, outside a finite base range, every positive \(x\) merged with some \(a\in P\) satisfying \(a\le Cx\), and every such \(a\) had an actual certificate to a positive \(b\le\rho a\), with \(C\rho<1\), then \(b<x\).  Strong induction on \(x\) proves convergence: \(b\) converges, hence \(a\) does, and the merger carries convergence to \(x\), even when \(b\) occurs before their common future.  Monks' theorem provides qualitative merging, not the size bound \(C\) used here; the present ray identities provide no uniform \(\rho\)-descent certificate on \(P\).  Those are the two unproved premises.  The finite-base carveout matters: demanding \(C\rho<1\) even at \(x=1\) would force a positive endpoint \(b<1\), an immediate contradiction.

For fixed affine parameter families and fixed admitted words, the combined cost is exactly the slope ratio \(\operatorname{slope}(b)/\operatorname{slope}(x)\).  A fixed-word merger equates the two slopes at the common future; it does **not** by itself impose that this combined ratio is at least one.  If \(b\) occurs after the common future and the ratio is below one, this is ordinary direct target descent.  If \(b\) occurs before it, the proposal is the smaller merged-seed problem, not a new consequence of the centered-ray coefficient.  Neither a size-controlled Monks merger nor a uniform premeeting smaller seed has been constructed for the hard progression.

**Verdict.**  The present return grammar has no complete coverage, and the uncovered class is not a negligible exception.  The observed two-step auxiliary inequality survives, but no joint excluding inequality or independently proved closure transition survives this audit.  Further isolated return scripts would only enlarge a finite menu; the mathematical target is a rule covering every output state, with a genuine target terminal and a decreasing rank on its closed domain.


## Quantitative-literature clarification

Monks, Monks, Monks and Monks, [*Strongly sufficient sets and the distribution of arithmetic sequences in the 3x+1 graph*, Theorem 4.1](https://www.mathematicalgemstones.com/maria/papers/mmmm.pdf), bound the number of inverse odd steps needed to reach an arithmetic progression, uniformly over starting vertices not divisible by 3.  Their count does not include inverse doublings.  We have not extracted the quantitative size constant from their construction here; its absence from this audit is not a claim that such a constant is mathematically unknown or impossible.  The necessary combined contraction remains unsupported.

The subsequent [bounded smaller-merger obstruction](RESEARCH-2026-09-29-bounded-small-merger.md) uses simultaneous binary and ternary congruences to obstruct every smaller seed at bounded depths.  It concerns a different target family from the catalytic hard progression and leaves variable-depth coverage open.
