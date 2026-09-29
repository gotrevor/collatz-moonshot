# A joint fuel refill on the first coefficient ray

Consider a positive integral pair

\[
 A=m2^e v-5,\qquad B=2^e v+1,\qquad m=72\cdot3^j,
\]

where \(v\) is odd.  Compare its parity words with the formal reference pair \((-5,1)\): the target has periodic word `110`, and the auxiliary has periodic word `10`.  The initial differences from the references have 2-adic valuations \(e+3\) and \(e\), respectively.  Each common branch divides a difference by 2 and multiplies it by either 1 or 3, so the **first** mismatches occur exactly at times \(e+3\) for \(A\) and \(e\) for \(B\).  This statement concerns separate shadows, not a joint return.

At the target mismatch time \(t=e+3\), let \(r=t\bmod3\).  Its reference value is \(a_r=-5,-7,-10\) for \(r=0,1,2\), and its actual value is \(a_r+Cv\), where

\[
 C=9\cdot3^j\cdot3^{t-\lfloor t/3\rfloor}
\]

is odd.  Taking the opposite branch from the reference at this first mismatch gives the new target difference

\[
 \begin{array}{c|c}r&\text{new difference}\\\hline
 0&(Cv+9)/2\\
 1&(Cv+13)/2\\
 2&(3Cv-19)/2.
 \end{array}
\]

Each expression may individually be very divisible by 2.  That alone says nothing about a common centered relation with the auxiliary.

## Exact joint return at old fuel zero

Set \(e=j=0\), so \(A_0=72v-5\), \(B_0=v+1\), and the old fuel \(v_2(B_0-1)=v_2(v)=0\).  For odd positive \(v\) satisfying \(v_2(9v+1)\ge6\), the following six-step words are admitted:

\[
\begin{array}{c|rrrrrrr}
 k&0&1&2&3&4&5&6\\\hline
 A_k&72v-5&108v-7&162v-10&81v-5&(81v-5)/2&(243v-13)/4&(243v-13)/8\\
 B_k&v+1&(v+1)/2&(v+1)/4&(v+1)/8&(3v+11)/16&(3v+11)/32&(9v+65)/64
\end{array}
\]

The words are `110010` and `000101`, respectively.  Substituting the 2-adic reference \(v_*=-1/9\) gives reference endpoints \((-5,1)\); equivalently the integer identities are

\[
64A_6=27A_0+31,\qquad 64B_6=9B_0+56,
\]
\[
 A_6+5=216(B_6-1),\qquad B_6-1={9v+1\over64}.
\]

Thus this is a **joint return** to the same centered state class \(A+5=m(B-1)\), with multiplier \(72\mapsto216\).  The new fuel is \(e'=v_2(9v+1)-6\), which can be any chosen nonnegative integer.  Choosing \(v_2(9v+1)\ge K+6\) refills at least \(K\) digits while old fuel remains zero.  For exact \(e'=K\), prescribe the following 2-adic bit too.

This particular six-step script is not iterable as written.  If its same affine words are evaluated at a general ray multiplier \(m=72\cdot3^j\), they give

\[
 A_6+5={27mv+216\over64},\qquad B_6-1={9v+1\over64}.
\]

The proposed next multiplier \(3m\) makes these equal for a full progression of \(v\) only when \(m=72\).  Also the target falls during the block: \(A_6/A_0\to27/64\) as \(v\to\infty\).  Hence a rank using only the precision cannot decrease at every return, but this example does not rule out a rank using size, multiplier, or amortized block cost.  This particular script is one refill, not an infinite trajectory.  A different \(j=1,e=0\) script exists in `RESEARCH-2026-09-29-ray-fuel-exit.md`.

If the first return refills exactly \(e'=6q\), the next \(q\) standard six-step shadow blocks are forced and consume that fuel.  At their end, with \(A_{\mathrm{start}}=72v-5\),

\[
 A_{\mathrm{end}}+5=\left({81\over64}\right)^q{27(A_{\mathrm{start}}+5)+216\over64},\qquad
 B_{\mathrm{end}}-1=\left({27\over64}\right)^q{9v+1\over64}.
\]

The auxiliary is strictly smaller at the end than at the start for every \(q\ge0\).  The leading target ratio is \((27/64)(81/64)^q\), which exceeds one exactly for \(q\ge4\); at \(q=4\) it is \(1162261467/1073741824>1\).  Since the additive constant in the target formula is positive, \(A_{\mathrm{end}}>A_{\mathrm{start}}\) for all positive \(v\) when \(q\ge4\).  Thus the target contraction during the refill does not by itself pay for an arbitrarily long replenished shadow.  The auxiliary still contracts.  These are finite, forced blocks, not a repeated refill rule.

## Realization in the positive hard family

The hard family has \(s=7+8t\), \(u=u_0+2Et\), \(E=12348281925\) odd, and \(z=9u+1\).  At its aligned time-nine checkpoint,

\[
 A+5={729z\over128},\qquad B-1={81z\over1024},\qquad m=72.
\]

Exact old fuel zero is exactly \(v_2(z)=10\).  Write \(z=1024w\) with \(w\) odd; then \(v=B-1=81w\).  Since \(z(t)\) has slope \(18E\) of 2-adic valuation one, \(v_2(z)=10\) selects one class \(t=t_0+2^{10}h\).  Along that class \(w=w_0+18Eh\).  Its slope has valuation one, so \(w\) traverses every odd residue class modulo every power of 2 as \(h\) varies.  Multiplication by 81 preserves this property.  Consequently \(v\equiv-1/9\pmod{2^{K+6}}\), and indeed exact \(v_2(9v+1)=K+6\), occur for infinitely many positive hard-family parameters with old fuel fixed at zero.  The ordinary integer divisibility \(81\mid v\) imposes no 2-adic restriction.

For these actual parameters, the original target is

\[
 n={1048576v-182817\over59049}.
\]

Throughout the displayed six-step block, \(A_k\ge A_6=(243v-13)/8>n\), since

\[
8\cdot59049(A_6-n)=5960299v+694899>0.
\]

The auxiliary satisfies \(B_k\le B_0=v+1<n\), since \(989527v>241866\) for every positive integral \(v\) here (in fact \(v\ge81\)).  Thus the refill is realized by positive, admitted hard-family prefixes before any target descent within this block.  These inequalities concern the block starting at the time-nine checkpoint; the earlier target-prefix lower bound is the separate hard-family shadow argument.  They do not assert that the full orbit never descends.

Two residue classes illustrate what the known local scripts do and do not cover.  First take \(v=775+4096h\), \(h\ge0\).  The first return gives \(v_1=B_6-1=109+576h\equiv45\pmod{64}\), with old fuel zero again.  The distinct \(j=1\) script from `RESEARCH-2026-09-29-ray-fuel-exit.md` is then admitted, and its output is

\[
 v_2=B_{12}-1={27v_1+1\over64}=46+243h,\qquad
 A_{12}=216v_2-5=9931+52488h.
\]

This target has descended below the original \(n\): after clearing the positive denominator in the displayed formula for \(n\),

\[
59049(n-A_{12})=226047964+1195603384h>0.
\]

The checkpoint is original target step 17, so this two-script intersection descends at step 29.  CRT supplies infinitely many parameters in the actual hard family with \(v\equiv775\pmod{4096}\); the formula above is stated for all \(h\), while only that intersection represents hard-family orbits.

In contrast, take \(v=7+4096h\).  The first admitted return gives \(v_1=B_6-1=1+576h\equiv1\pmod{64}\), still with fuel zero but now multiplier \(m=216\).  None of the three presently specified blocks applies: a normal shadow block needs fuel at least six, the \(j=0\) refill needs multiplier 72, and the separate \(j=1\) refill needs \(v_1\equiv45\pmod{64}\).  CRT again realizes infinitely many such positive hard-family parameters, and the six-step pre-descent inequalities above apply.  This is a coverage failure of the **known three-block grammar**, not an obstruction to every possible return script.

**Scope.**  A fuel-only strict-decrease rule fails even on positive pre-descent hard-family prefixes, because a joint return can have arbitrarily high new fuel at fixed old fuel zero.  The forced consumption of refilled fuel can outweigh the refill's target contraction.  Two special six-step scripts compose on one sparse class, while another infinite hard-family class leaves the known grammar immediately.  None of these finite identities excludes an adaptive, size-aware rank or gives a covering return mechanism.
