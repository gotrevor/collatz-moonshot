# Orbit minima of Collatz's original permutation

[ Claude wrote this note at my direction.  The Lean files it links are the authority.  -Trevor ]

**Abstract.**  Collatz's 1930s permutation of the integers, `U(2n) = 3n`, `U(4n+1) = 3n+1`,
`U(4n+3) = 3n+2` (Conway's "amusical permutation"), is expected to have infinitely many orbits
on `ℕ`; whether it has only finitely many is Klamkin's problem (a) (SIAM Review 1963), still
open.  An orbit of a nonnegative integer has a least element, so the
number of orbits is the number of *orbit minima*.  We prove, in Lean, that the orbit minima
have upper density **less than `1/20`**, and we give a closed-form prediction for their density,
`c = exp(−Σ_{k≥1} E[min(1, 2^(k+O_k)/3^k)]/k) ≈ 0.049780` with `O_k ~ Bin(k, 1/2)`, which matches
the number of apparent orbit minima in `1..10^6` (`0.049957`; both orbit directions pass
`n·2^120` without dropping below `n`) to within one binomial standard error.  A positive *lower* bound on
that density would settle Klamkin's problem; we record why the natural tools cannot give one.
We also observe that only six orbits on `ℕ` are known to be distinct.

All results are linked at commit
[`1fbd2e3`](https://github.com/gotrevor/collatz-moonshot/tree/1fbd2e3effe5c6306059a09a59a48368d25306fd).
Every proved statement below checks with `#print axioms` against the standard three
(`propext`, `Classical.choice`, `Quot.sound`) only.

## The problem

`U` is a bijection of `ℤ` with inverse `3m ↦ 2m`, `3m+1 ↦ 4m+1`, `3m+2 ↦ 4m+3`
([`amusical`](https://github.com/gotrevor/collatz-moonshot/blob/1fbd2e3effe5c6306059a09a59a48368d25306fd/CollatzMoonshot/Amusical.lean#L31)).
On `ℕ` its known cycles are `{0}`, `{1}`, `{2, 3}`, `{4, 6, 9, 7, 5}` and the 12-cycle through
`44` ([`amusical_cycle_fortyFour`](https://github.com/gotrevor/collatz-moonshot/blob/1fbd2e3effe5c6306059a09a59a48368d25306fd/CollatzMoonshot/Amusical.lean#L132)).
Klamkin (SIAM Review 5 (1963) 275-276; his `P` is `U⁻¹` on the positive integers, with the same
orbits) conjectured that the orbit of `8` is infinite and asked whether there are only finitely
many orbits.  Both are open (Lagarias's annotated bibliography 2003, entry Klamkin 1963:
"remains unsolved concerning the orbit of n = 8 and part (a)"; Lagarias, arXiv:2111.02635;
Tavares, Discrete Math. 313 (2013) 2139-2145, who reduces zero density of an orbit to a thread
condition).  Conway (Amer. Math. Monthly 120 (2013) 192-198, §5) calls "8 belongs to an infinite
cycle" the simplest assertion about this permutation that he believes true but unsettleable.

## 1. Window minima have an exact density (proved)

Call `n` an **`L`-window minimum** if `n ≤ U^t(n)` and `n ≤ U^{−t}(n)` for `1 ≤ t ≤ L`
([`IsWindowMin`](https://github.com/gotrevor/collatz-moonshot/blob/1fbd2e3effe5c6306059a09a59a48368d25306fd/CollatzMoonshot/AmusicalWindow.lean#L30)).

**Theorem 1.**  For every `L`, the `L`-window minima have natural density
`δ_L = f_L · b_L`, where `f_L` is the probability that the walk with steps `log(3/2)`,
`log(3/4)` (probability `1/2` each) stays positive for `L` steps, and `b_L` the same for steps
`log(2/3)`, `log(4/3)` (probabilities `1/3`, `2/3`)
([`windowMinDensity`](https://github.com/gotrevor/collatz-moonshot/blob/1fbd2e3effe5c6306059a09a59a48368d25306fd/CollatzMoonshot/AmusicalWindow.lean#L985);
`f_L`, `b_L` are the exact pattern sums
[`fwdSurv`](https://github.com/gotrevor/collatz-moonshot/blob/1fbd2e3effe5c6306059a09a59a48368d25306fd/CollatzMoonshot/AmusicalWindow.lean#L651),
[`bwdSurv`](https://github.com/gotrevor/collatz-moonshot/blob/1fbd2e3effe5c6306059a09a59a48368d25306fd/CollatzMoonshot/AmusicalWindow.lean#L660)).

*Proof idea.*  On a residue class mod `4^L·3^L` the first `L` forward and backward branches are
fixed, so `U^{±t}` is affine there; past a size threshold the window condition becomes a
congruence condition; the good classes are counted per direction (Haar measure is exactly
preserved) and combined by the Chinese remainder theorem.

`δ_1 = 1/3` is the density of local minima (the classes `±2 mod 6`), which Conway computes in
his "Congruence Paradox" (2013, Appendix 2)
([`windowMinDensity_one`](https://github.com/gotrevor/collatz-moonshot/blob/1fbd2e3effe5c6306059a09a59a48368d25306fd/CollatzMoonshot/AmusicalWindow.lean#L744)).
Further values: `δ_2 = 2/9`, `δ_3 = 1/6`, `δ_4 = 4/27`
([`windowDensity_values`](https://github.com/gotrevor/collatz-moonshot/blob/1fbd2e3effe5c6306059a09a59a48368d25306fd/CollatzMoonshot/AmusicalWindow.lean#L669)),
`δ_100 ≈ 0.05084`, `δ_200 ≈ 0.049888`.

## 2. Orbit minima have upper density below 1/20 (proved)

Every orbit minimum is an `L`-window minimum for every `L`
([`IsOrbitMin.isWindowMin`](https://github.com/gotrevor/collatz-moonshot/blob/1fbd2e3effe5c6306059a09a59a48368d25306fd/CollatzMoonshot/AmusicalWindow.lean#L643)),
so their upper density is at most `δ_L` for every `L`
([`orbitMin_density_le`](https://github.com/gotrevor/collatz-moonshot/blob/1fbd2e3effe5c6306059a09a59a48368d25306fd/CollatzMoonshot/AmusicalWindow.lean#L1038)).

**Theorem 2.**  `δ_200 < 1/20`
([`windowDensity_two_hundred_lt`](https://github.com/gotrevor/collatz-moonshot/blob/1fbd2e3effe5c6306059a09a59a48368d25306fd/CollatzMoonshot/AmusicalBound.lean#L567)),
hence for all large `X`, fewer than `X/20` of `0, …, X−1` are orbit minima
([`orbitMin_density_lt_one_twentieth`](https://github.com/gotrevor/collatz-moonshot/blob/1fbd2e3effe5c6306059a09a59a48368d25306fd/CollatzMoonshot/AmusicalBound.lean#L588)).
Equivalently: at most `X/20` orbits of `U` meet `[0, X)`, for large `X`.

## 3. The predicted density (conjecture)

Heuristically, treat the forward and backward orbits of a large `n` as the two independent
walks of Theorem 1, run forever.  For each finite horizon this is exact (Theorem 1: the residues
of `n` mod `4^L` and mod `3^L` are independent by CRT); the conjecture is that it persists to
infinite horizon.  Then `n` is an orbit minimum when both walks stay positive forever, with
probability `p_f · p_b`.  Sparre Andersen's theorem gives `p_f = exp(−Σ_k P(S_k ≤ 0)/k)` and
`p_b = exp(−Σ_k P(B_k ≤ 0)/k)`.  The two step laws are tilted negatives of each other:
`P(Y = −x) = e^{−x} P(X = x)` (`1/3 = ½·⅔`, `2/3 = ½·4/3`).  This is the product formula
`|s|_∞ |s|_2 |s|_3 = 1` for each branch slope `s = 3/2^a`: the 2-adic measure of a branch's
domain times `1/s` is the 3-adic measure of its image.  Hence `P(B_k ∈ A) = E[e^{−S_k}; −S_k ∈ A]`,
and since `S_k ≠ 0`, `P(B_k ≤ 0) = E[e^{−S_k}; S_k > 0]`.  The two series merge:

$$c = p_f\, p_b = \exp\Big(-\sum_{k\ge1} \frac1k\, \mathbb E\big[\min(1,\ 2^{k+O_k}/3^k)\big]\Big) \approx 0.049780,$$

`p_f ≈ 0.210136`, `p_b ≈ 0.236892`
([`minimaConstant`](https://github.com/gotrevor/collatz-moonshot/blob/1fbd2e3effe5c6306059a09a59a48368d25306fd/CollatzMoonshot/AmusicalConstant.lean#L29)).

**Conjecture.**  The orbit minima of `U` have natural density `c`
([`AmusicalMinimaDensityExact`](https://github.com/gotrevor/collatz-moonshot/blob/1fbd2e3effe5c6306059a09a59a48368d25306fd/CollatzMoonshot/AmusicalConstant.lean#L58)).

Evidence: Simons (arXiv:2205.10582, §5.1) found empirically, "no proof", that the number of
apparent divergent trajectories grows linearly with the range, with ratio "`.05X0`" for his `P(1, 3, 2, 2)`, which is `U⁻¹`
(same orbits); those are the orbit minima, and `c` is the first formula for the ratio that we
know of.  Of `1..10^6`, `49957`
integers have both orbit directions exceed `n·2^120` without
dropping below `n` (density `0.049957`; standard error `≈ 0.0002`), stable from `10^3` to
`10^6`.  Among long-window minima, being a global minimum shows no dependence on the residue
class mod `72`, `864` or `2592` once the window is long (the `χ²` excess decays to nothing by
`L = 80`), as the independence model predicts.  The upper half is a theorem on paper, not yet in Lean: `f_L ↓ p_f` and `b_L ↓ p_b` by
continuity of measure and Sparre Andersen's theorem (both walks drift upward and never tie,
since `3^k ≠ 2^m`), and the duality identity merges the two series, so `δ_L ↓ c` and the orbit
minima have upper density at most `c`
([`WindowDensityLimit`](https://github.com/gotrevor/collatz-moonshot/blob/1fbd2e3effe5c6306059a09a59a48368d25306fd/CollatzMoonshot/AmusicalConstant.lean#L40),
[`orbitMin_density_le_minimaConstant`](https://github.com/gotrevor/collatz-moonshot/blob/1fbd2e3effe5c6306059a09a59a48368d25306fd/CollatzMoonshot/AmusicalConstant.lean#L47)).  The measured
`0.049957` lies above both `c` and the proved `δ_200 = 0.049888`; these are asymptotic bounds,
and the excess is `0.8` standard errors.  The lower half is the open problem: any positive lower bound
gives infinitely many orbits
([`amusicalInfinitelyManyOrbits_of_minima`](https://github.com/gotrevor/collatz-moonshot/blob/1fbd2e3effe5c6306059a09a59a48368d25306fd/CollatzMoonshot/Amusical.lean#L195)).

## 4. Six orbits, and why the lower bound is hard

**Proposition.**  The orbits of `0, 1, 2, 4, 44, 8` are pairwise distinct
([`amusical_six_distinct_orbits`](https://github.com/gotrevor/collatz-moonshot/blob/1fbd2e3effe5c6306059a09a59a48368d25306fd/CollatzMoonshot/Obstructions/Amusical.lean#L187)).
We do not know a proof that `U` has a seventh orbit on `ℕ`
([`AmusicalAtLeastSevenOrbits`](https://github.com/gotrevor/collatz-moonshot/blob/1fbd2e3effe5c6306059a09a59a48368d25306fd/CollatzMoonshot/Obstructions/Amusical.lean#L217)):
separating any further orbit means showing some number never meets the orbit of `8`, and Conway
notes `8` and `14` might share one.  If there were only six, the orbit of `8` would have density
`1`.

Reductions proved along the way: zero density of every orbit implies infinitely many orbits
([`amusicalInfinitelyManyOrbits_of_zeroDensity`](https://github.com/gotrevor/collatz-moonshot/blob/1fbd2e3effe5c6306059a09a59a48368d25306fd/CollatzMoonshot/Amusical.lean#L217)),
and finitely many orbits would force some infinite orbit to return to linear size,
`U^j(x) ≤ C(|j| + 1)`, at arbitrarily late times
([`exists_linearlyRecurrent_of_finitelyManyOrbits`](https://github.com/gotrevor/collatz-moonshot/blob/1fbd2e3effe5c6306059a09a59a48368d25306fd/CollatzMoonshot/Amusical.lean#L275)).

Why the natural tools fail (each a row of
[`Maze.lean`](https://github.com/gotrevor/collatz-moonshot/blob/1fbd2e3effe5c6306059a09a59a48368d25306fd/CollatzMoonshot/Maze.lean);
the first two rest on proved theorems, the third on a believed proposition and an open Lean
target):

* **Density, measure and level-crossing counts balance on `ℕ`.**  For every `X`, as many
  `n < X` jump to `≥ X` as are reached from `≥ X`
  ([`amusical_mass_conservation`](https://github.com/gotrevor/collatz-moonshot/blob/1fbd2e3effe5c6306059a09a59a48368d25306fd/CollatzMoonshot/Obstructions/Amusical.lean#L38)).
  Any argument using only this balance also applies to `ℕ`, a union of infinitely many orbits.
* **Invariants are the problem in disguise.**  A `U`-invariant function with infinitely many
  values on `ℕ` exists if and only if there are infinitely many orbits
  ([`amusicalInfinitelyManyOrbits_iff_invariant`](https://github.com/gotrevor/collatz-moonshot/blob/1fbd2e3effe5c6306059a09a59a48368d25306fd/CollatzMoonshot/Obstructions/Amusical.lean#L96)).
* **Residues cannot certify a minimum.**  Every residue class mod `2^k 3^l` contains arbitrarily
  large non-minima (paper proof: steer the 2-adic digits past the class's forced prefix into a
  long run of `4m+1 ↦ 3m+1` steps; Lean target `exists_large_nonOrbitMin`, not yet proved), and
  the data show no residue dependence beyond the window condition
  (`MinimaNotResidueDetermined`, believed).

Structurally, `(ℤ₂ × ℤ₃, U)` is topologically conjugate to the full two-sided shift on three
symbols (future steps read 2-adic digits, past steps read 3-adic digits), and `U` on `ℤ` is its
restriction to the dense diagonal copy of the integers.  Klamkin's problem asks whether that
copy meets infinitely many shift orbits.  (Not formalized.)

## What is not claimed

No lower bound on the density of orbit minima, no seventh orbit, nothing about the orbit of `8`
beyond the classical facts.  `c` is an upper bound for the upper density by a paper argument not yet in
Lean, and its equality with the density is a conjecture; the conjugacy is stated without formal
proof.  We know no proof that *any* permutation of this residue-class-affine
kind has infinitely many orbits, except by a forward-invariant union of classes (as in Simons
§5.4); for `U` we know of none (none exists modulo any `M ≤ 300`).  For the wider class, Lagarias records that even the existence of a
single infinite orbit is open (annotated bibliography 2003, entry on Venturini 1992); for `U`,
either there are infinitely many orbits or an infinite one exists
([`amusicalInfinitelyManyOrbits_or_exists_infinite`](https://github.com/gotrevor/collatz-moonshot/blob/1fbd2e3effe5c6306059a09a59a48368d25306fd/CollatzMoonshot/Obstructions/Amusical.lean#L250)).

Prior-work search: Lagarias's annotated bibliographies (2003, 2006) and survey (2021), Conway
2013, Tavares 2013, Venturini 1997, Simons 2022, Matthews's survey, Kohl's RCWA thesis and
manual, Karras–de Weger 2026, OEIS A006368, and arXiv and web searches.  Not opened: Venturini
1992, Keller 1999, Guy's *Unsolved Problems* E17, Shanks 1965 and Atkin 1966 (known to us only
through Lagarias's summaries).  We did not find the window densities for `L ≥ 2`, the formula
for `c` or its derivation, the shift conjugacy for this permutation, or the six-orbit remark.
The one-sided halves of the conjugacy are classical (Matthews–Watts; Lagarias; Akin).

## Building

```
git clone https://github.com/gotrevor/collatz-moonshot && cd collatz-moonshot
git checkout 1fbd2e3effe5c6306059a09a59a48368d25306fd
lake exe cache get && lake build CollatzMoonshot.AmusicalBound CollatzMoonshot.Obstructions.Amusical
```
