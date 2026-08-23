# Eliahou (1993): lower bounds on nontrivial Collatz cycles

## Citation

Shalom Eliahou, “The 3x + 1 problem: new lower bounds on nontrivial cycle lengths,” *Discrete Mathematics* 118 (1993), 45–56. DOI: [10.1016/0012-365X(93)90052-U](https://doi.org/10.1016/0012-365X(93)90052-U).

## Elevator pitch

Eliahou turns a hypothetical Collatz loop into an exceptionally precise rational approximation to \(\log_2 3\). Continued fractions then show that no small cycle can supply such an approximation. Combined with the computational verification available in 1993, this forces every nontrivial cycle to contain at least 17,087,915 shortcut-map steps. More importantly, the method scales: as computation raises the smallest possible cycle element, the cycle-length bound jumps to successive continued-fraction thresholds.

## Executive summary

Eliahou proves that any nontrivial periodic orbit of the shortcut Collatz map

\[
T(n)=
\begin{cases}
n/2, & n\text{ even},\\
(3n+1)/2, & n\text{ odd}
\end{cases}
\]

must contain at least **17,087,915 elements**. This is a lower bound, not an existence result: the paper does not exhibit such a cycle or prove that one exists.

The argument combines two ingredients:

1. a product identity that forces the ratio “total steps / odd steps” in any cycle to be extremely close to \(\log_2 3\); and
2. continued fractions and Farey-pair arguments that determine which rational numbers can lie in that tiny interval.

The numerical bound uses the computational fact available at the time that every starting value through \(2^{40}\) reaches the trivial cycle. Consequently, every element of a hypothetical nontrivial cycle must exceed \(2^{40}\).

## Setup and main identity

Let \(\Omega\) be a cycle, let \(\Omega_1\) be its odd elements, and write

- \(k=|\Omega|\) for the total number of shortcut-map steps;
- \(k_1=|\Omega_1|\) for the number of odd steps;
- \(m=\min\Omega\) and \(M=\max\Omega\).

Multiplying the ratios \(T(n)/n\) around the cycle makes the orbit values telescope. Eliahou obtains

\[
\prod_{n\in\Omega_1}\left(3+\frac1n\right)=2^k.
\]

Bounding every odd cycle element between \(m\) and \(M\), then taking base-2 logarithms, gives

\[
\log_2\!\left(3+\frac1M\right)
< \frac{k}{k_1}
< \log_2\!\left(3+\frac1m\right).
\]

In particular,

\[
\log_2 3 < \frac{k}{k_1}
< \log_2\!\left(3+\frac1m\right).
\]

Thus a large lower bound on the smallest cycle element makes \(k/k_1\) an exceptionally close rational approximation to \(\log_2 3\), from above.

## Continued-fraction step

For a proposed lower bound \(m\), the paper defines \(K(m)\) as the smallest possible numerator \(k\) of a fraction \(k/\ell\) satisfying

\[
\log_2 3 < \frac{k}{\ell}
< \log_2\!\left(3+\frac1m\right).
\]

Eliahou proves that the minimizing fraction must be an upper convergent or intermediate convergent in the continued-fraction expansion of \(\log_2 3\). Consecutive upper convergents are Farey pairs, which sharply restricts every rational lying between them.

At \(m=2^{40}\), this calculation gives

\[
K(2^{40})=17{,}087{,}915.
\]

The relevant approximation is

\[
\frac{17{,}087{,}915}{10{,}781{,}274}\approx\log_2 3,
\]

where the numerator is the total shortcut period and the denominator is the number of odd elements.

The stronger structural result is that the period of a nontrivial cycle must have the form

\[
|\Omega|=301{,}994a+17{,}087{,}915b+85{,}137{,}581c,
\]

where \(a,b,c\) are nonnegative integers, \(b>0\), and \(ac=0\). The first admissible values are therefore 17,087,915; 17,389,909; 17,691,903; and so on.

## What the result does and does not establish

- It excludes every nontrivial cycle shorter than the bound.
- It does **not** prove the Collatz conjecture: an orbit might still diverge, or a much longer cycle might exist.
- The number 17,087,915 is not intrinsic to the Collatz map. It results from combining the proof with the 1993 computational cutoff. Better verified cutoffs produce larger bounds, in discontinuous jumps governed by continued-fraction convergents.
- The paper counts iterations of the shortcut map \(T\). Under the original map, where an odd step \(n\mapsto3n+1\) is counted separately from the following halving, the corresponding historical bound is 27,869,189 steps.

## Claimed Lean formalization

The public repository [tangentstorm/eliahou-collatz-bounds](https://github.com/tangentstorm/eliahou-collatz-bounds) presents a Lean 4/Mathlib formalization of Eliahou’s argument. Its documentation claims that the headline theorem `eliahou_bound`—every shortcut-map cycle with minimum element greater than \(2^{40}\) has at least 17,087,915 elements—is fully proved with no `sorry`, using only standard axioms.

The repository also explicitly marks `eliahou_precise`, intended to formalize Eliahou’s stronger linear-combination description of possible periods, as still containing a `sorry`. Accordingly, the repository claims machine-checked coverage of the main numerical lower bound, not a complete formalization of every result in the paper. This note records the repository’s stated status as of July 20, 2026; the build and proof dependency chain have not been independently reproduced or audited here.

## Current status (checked July 20, 2026)

The 17,087,915 figure is no longer the best published cycle-length bound.

Christian Hercher proved that verifying convergence through \(3\cdot2^{69}\) suffices to move to the next relevant continued-fraction threshold. David Bařina subsequently verified convergence through \(2^{71}\). The resulting published lower bounds are:

- **217,976,794,617 elements** under Eliahou’s shortcut map; equivalently
- **355,504,839,929 steps** under the original, unshortened Collatz map.

These are still lower bounds only; no nontrivial cycle is known.

Sources: [Hercher, *Journal of Integer Sequences* 26 (2023)](https://cs.uwaterloo.ca/journals/JIS/VOL26/Hercher/hercher5.html); [Bařina, *Journal of Supercomputing* 81 (2025)](https://doi.org/10.1007/s11227-025-07337-0).
