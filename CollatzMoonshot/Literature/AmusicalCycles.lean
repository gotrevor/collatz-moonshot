/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.Amusical

/-!
# Cycles of the amusical permutation (literature)

What is known about the cycles of Collatz's permutation `U`, as of the 2026-10-12 sweep.

* **Atkin 1966** (SIAM Review 8, 234-236, a comment on Klamkin's Problem 63-13*): a method that
  in principle finds all cycles of a given period; by computer, no cycles of period `< 200` on
  the nonnegative integers beyond the known ones of periods 1, 2, 5, 12.  Read via Lagarias's
  annotated bibliography (2003, entry 11), not the original.
* **Simons 2022** (arXiv:2205.10582, "Cycles and divergent trajectories for a class of
  permutation sequences"): adapts the Simons-de Weger m-cycle method to a class `P(a,b,c,d)` of
  permutations of `ℕ₀` that contains `U` (as `P(2,2,1,3)`, analysed via the inverse
  `P(1,3,2,2)`).  For each `m` there are finitely many m-cycles, computably (Roth for finiteness,
  Baker for computability, Rhin's `log 2`/`log 3` bound for the numbers).  With numerics on all
  starts `< 10^6`, Corollary 11 lists the cycles with `m ≤ 5`; for `m = 3, 4, 5` it leaves open
  cycles with all elements `≥ 10^6` and `(K, L)` among `(389, 276)`, `(778, 552)`, `(957, 679)`,
  `(1167, 828)`, or `828 < L < 26893` (`K` non-multiples of `3`, `L` multiples of `3` in the
  inverse map's terms).  Corollary 11(b) prints the 12-cycle with two members missing, a typo.
* **Keller 1999** (Missouri J. Math. Sci. 11, 152-157, via Lagarias 2003 entry 94): every
  "type V" permutation `g_p` has finitely many cycles of each period; `g_3` is conjugate to `U`.
  For `U` this is elementary: each length-`p` branch pattern fixes at most one rational point.
* **Not yet read:** M. Tavares, *A remark about the density of the orbits of the Collatz
  permutation*, Discrete Math. 313 (2013) 2139-2145, doi:10.1016/j.disc.2013.05.003;
  G. Venturini, *On a generalization of the 3x+1 problem*, Adv. Appl. Math. 19 (1997) 295-305,
  doi:10.1006/aama.1996.0496 (source of conjectures C4/C5 in Lagarias 2021).  Both are free on
  ScienceDirect but bot-walled.

`AmusicalNoOtherCycles` and `AmusicalFinitelyManyCycles` (in `CollatzMoonshot.Amusical`) are the
open problems; Klamkin's orbit-of-8 question is `AmusicalOrbitOfEightInfinite`.
-/

namespace CollatzMoonshot.Literature

open CollatzMoonshot.Amusical

/-- **[Literature: Atkin 1966, via Lagarias 2003]**  Every nonnegative periodic point of period
`< 200` is one of the known cycle members. -/
def AtkinNoShortCycles : Prop :=
  ∀ n : ℤ, 0 ≤ n → ∀ p : ℕ, 0 < p → p < 200 → amusical^[p] n = n → n ∈ knownCycleMembers

/-- **[Literature: Simons 2022, Theorem 2(1)]**  For each `m`, only finitely many nonnegative
periodic points lie on cycles with `m` local minima. -/
def SimonsFiniteMCycles : Prop :=
  ∀ m : ℕ, {n : ℤ | 0 ≤ n ∧ n ∈ Function.periodicPts amusical ∧
    cycleLocalMinCount n (Function.minimalPeriod amusical n) = m}.Finite

/-- **[Literature: Simons 2022, Corollary 11(a)]**  A nonnegative periodic point whose cycle has
at most two local minima lies on `{0}`, `{1}`, `{2, 3}` or `{4, 6, 9, 7, 5}`. -/
def SimonsTwoCycles : Prop :=
  ∀ n : ℤ, 0 ≤ n → n ∈ Function.periodicPts amusical →
    cycleLocalMinCount n (Function.minimalPeriod amusical n) ≤ 2 → n ≤ 9

end CollatzMoonshot.Literature
