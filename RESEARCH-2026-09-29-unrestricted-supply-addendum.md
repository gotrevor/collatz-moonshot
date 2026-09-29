# Scope correction: unrestricted catalyst supply is already solved for 3-free labels

The [borrowing checkpoint](/Users/gotrevor/src/collatz-moonshot/RESEARCH-2026-09-28-borrow-checkpoint.md) treats construction from U2/U8/U13 and Q moves as a missing general prerequisite.  That is a legitimate **restricted-palette experiment**, but it is not an intrinsic supply obstacle for the Collatz catalytic route on 3-free scalar certificates.  [Applegate and Lagarias, *The 3x+1 Semigroup*](https://arxiv.org/html/math/0411140), Theorem 1.1, already supplies every needed value-one unit if arbitrary semigroup generator words are admissible.  The earlier audit was too defensive of the palette: “unrestricted scalar equivalence is tautological” is true, but does not invalidate using the proven semigroup theorem as a supply lemma.

## Exact unrestricted borrowing criterion

Let $S=\langle 2,r_u:u\ge1\text{ odd}\rangle$, with $r_u=2u/(3u+1)$.  A catalyst $C$ is a finite multiset of these generators, and $v(C)$ is its positive rational product.

**Proposition.**  There exists a finite word $W\supseteq C$ with $v(W)=1$ if and only if every odd label appearing in $C$ is prime to 3.

*Necessity.*  The denominator $3u+1$ is prime to 3, so $v_3(r_u)=v_3(u)\ge0$; also $v_3(2)=0$.  A word of value one has total valuation zero.  Therefore it cannot contain a label divisible by 3.

*Sufficiency.*  If every odd label of $C$ is 3-free, then $v(C)^{-1}$ has reduced denominator prime to 3.  The Applegate–Lagarias characterization says $v(C)^{-1}\in S$.  Choose any positive generator word $Z$ representing it; then $W=C+Z$ is an exact value-one word containing $C$.  No Collatz convergence assumption enters.  The result handles all multiplicities in one step, not just one label at a time.

For a certificate of scalar value $n$ with $3\nmid n$, every odd factor is automatically 3-free by the same valuation argument.  Any **actual positive scalar-preserving replay** from it also contains only 3-free labels.  A merely signed integer relation can use 3-divisible labels internally and yield a formal prefix-deficit catalyst that cannot be supplied; it must be replaced by a relation supported on 3-free labels before this lemma applies.  Thus **arbitrary finite 3-free catalyst availability is solved**.  In particular, the auxiliary $c(h)$ and the four $x/z$ input progressions in the two symbolic supply rules are all 3-free, so their unrestricted unit supply is immediate.  For $3\mid n$, a 3-divisible label can occur in a certificate but can never be inserted as part of a value-one unit; a repair must use the existing 3-adic charge or borrow only 3-free labels.  The universal supply statement must not be extended to 3-divisible catalysts.

This supply is effective in the ordinary computability sense.  Enumerate all finite $S$ words and compare their exact rational values with $v(C)^{-1}$.  The theorem guarantees eventual success for 3-free $C$.  The theorem alone gives no useful bound on word length, largest label, search time, or a rank decrease for a larger repair procedure.  It can also be used as an explicit external $\mathrm{Prop}$ hypothesis until formalized, because its proof is independent of Collatz convergence.  An executable Lean construction would need either an extracted algorithm or a justified terminating enumeration.

## Why the unrestricted equivalence warning is still correct

Suppose $X,Y$ are two **already specified** certificate words of the same 3-free scalar value $n$.  The semigroup theorem gives a word $Z$ of value $1/n$.  Then $Y+Z$ and $X+Z$ are both units, so arbitrary unit insertion and removal gives

\[
X\longrightarrow X+(Y+Z)=Y+(X+Z)\longrightarrow Y.
\]

This uses **different** units at the two ends and explicitly contains the chosen target $Y$.  It proves that unrestricted reachability between two known same-value words is vacuous; it does not choose $Y$, prove its vertex balance, or establish a terminating target-free procedure.  In particular, a finite repair to a supplied known orbit remains a diagnostic, not a convergence proof.

There is still a nontrivial *sufficient-method* version of catalytic repair.  Fix a central rule family, such as the Q exchanges plus the essential cubic, and require one **common** borrowed unit $W$ to be added and returned: $X\to X+W\to Y+W\to Y$.  A signed integer relation in the central rules gives a finite catalyst $C$ by the existing prefix-deficit formula.  If $C$ is 3-free, the proposition supplies a common $W\supseteq C$ automatically.  Thus on 3-free scalars, central integer-relation existence and the choice of a vertex-balanced endpoint become the live questions; restricted-palette borrowability is no longer a separate theorem prerequisite.  The common-$W$ convention prevents the two-unit tautology above, but is a chosen proof architecture, not a necessary property of every possible Collatz proof.

## Route correction

Use U2/U8/U13+Q closure when studying that palette's expressive power, optimizing small explicit certificates, or testing whether a proposed central move can be replayed with a tightly controlled library.  Do not require a uniform recursive borrowing derivation in that palette before attacking target-free balance for 3-free starts.  It would solve a stronger, self-imposed problem, and the four finite borrowing DAGs do not reduce the main uncertainty.

The next mathematical statement should take the Applegate–Lagarias supply proposition as known, hold the central move family and the common-unit convention explicit, and ask for a target-free construction of a balanced output together with a finite central relation and a well-founded rank.  A rank based on word length or maximum label must account for the potentially huge AL word, or be defined at the relation/flow level so that the bookend unit cancels.  No such balance or termination theorem is supplied here.  A proof for every positive 3-free start would extend to all positive starts: first remove factors of 2; if the resulting odd integer is divisible by 3, its next shortcut iterate is 2 modulo 3.  No general supply claim for 3-divisible catalyst labels is needed for that elementary reduction.
