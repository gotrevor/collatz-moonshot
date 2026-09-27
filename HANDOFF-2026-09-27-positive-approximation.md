# HANDOFF 2026-09-27 — positive approximation coefficient theorem PROVED

Kickoff: `KICKOFF-2026-09-27-positive-approximation.md`.  Bounded obstruction
formalization, not a general Collatz campaign.  **Done in one lap; no successor
task.**

## Result

`CollatzMoonshot.Obstructions.ArithmeticLifts.positiveApproximationFamily :
PositiveApproximationFamily` is a machine-checked theorem, commit `70f312e`.

* Sole writer footprint: `CollatzMoonshot/Obstructions/PositiveApproximation.lean`.
  `ArithmeticLifts`, the root import, other modules and `DIRECTION.md` are
  untouched.
* Sorry-free on that file.  `#print axioms positiveApproximationFamily` is
  pinned in-file with `#guard_msgs` to exactly
  `[propext, Classical.choice, Quot.sound]` — no `native_decide`, no new axiom.
* Verified by real `lake build`: the module at 8715 jobs, and the full root
  build green at 8794 jobs via the pre-commit hook.

The frozen statement was **true as written**; no counterexample, no weakening.

## The proof, and what made it go through

Name the chain `napx K j = 3^j * 2^(K-j) - 1`, so `napx K 0 = 2^K - 1` is the
odd base of the dyadic ray and `napx K K = 3^K - 1` is the defect point.
Four facts carry everything:

1. **`napx_lt`** — strict monotonicity on `[0,K]`.  Proved from the exact
   identity `(3^j * 2^(K-j)) * 2^j = 2^K * 3^j` (`g_mul_pow`), which reduces
   `g j < g i` to `3^j * 2^i < 3^i * 2^j`, i.e. to `2^(i-j) < 3^(i-j)`.  This
   avoids any rational or real comparison, and it immediately gives
   injectivity (`napx_inj`), so the `Finset.Ico 1 K` sum inside `approxCoeff`
   has at most one live term.
2. **`napx_odd`** (`j < K`) and **`napx_mod_three`** (`1 ≤ j`).  Parity is what
   makes the ray and the finite chain disjoint (`ray_finAt_disjoint`), hence
   the 0/1 claim; and `≡ 2 [MOD 3]` is exactly the side condition under which
   `transfer`'s odd preimage branch fires.
3. **`napx_step`**: `3 * napx K j + 1 = 2 * napx K (j+1)` for `j < K`.  One
   lemma covers both the ray-base edge (`j = 0`) and every interior chain
   edge, which is why the `j = 1` case of the preimage analysis needs no
   separate arithmetic.
4. **`ray_any_iff`**: the `List.range (n+1)` cutoff in `rayCoeff` loses
   nothing, since `n = 2^j * base` with `0 < base` forces `j < 2^j ≤ n`.  As
   the kickoff anticipated, proving this ray-membership characterization
   *first* is what lets the rest of the proof ignore computability entirely.

The defect identity is then a **preimage count**, not a series manipulation.
`transfer a n` sums `a` over the shortcut preimages of `n`, so at `n`:

* the even preimage `2n` contributes the ray indicator
  (`rayAt_two_mul`, `not_finAt_two_mul`);
* the odd preimage `(2n-1)/3`, when it exists, contributes the indicator of
  the *image* chain `napx K 1, …, napx K K`
  (`approxCoeff_odd_preimage_eq_one` / `_eq_zero`);
* `approxCoeff K n` itself is the ray indicator plus the indicator of the
  shorter chain `napx K 1, …, napx K (K-1)`.

The difference is the indicator of `n = napx K K = 3^K - 1`.

### The one structural insight worth reusing

The naive "telescope the finite sum" reading of the paper proof invites a case
split on whether `3^K - 1` happens to lie on the dyadic ray through `2^K - 1` —
an exponential diophantine question with no elementary answer.  **The argument
never needs that disjointness.**  Stating the computation as a preimage
*multiplicity* rather than as a set union makes any accidental overlap cancel
identically on both sides of `transfer (approxCoeff K) n - approxCoeff K n`.
`finAt'_iff` splits the image chain off its last point; `finAt_ne_top` is the
only separation used, and it is pure monotonicity.  If this family is ever
generalized (other multipliers, other ray bases), keep the preimage-count
formulation and the same obstruction stays absent.

No norm, topology, summability, or asymptotics appears anywhere in the module.
The `‖·‖_s` bound of the research note stays paper-side; `geometric_endpoint_ratio`
in `ArithmeticLifts` already supplies its arithmetic core.

## Remaining crux (for the record, not assigned)

The formalized object is an *obstruction*: it certifies that no positive
constant `c` can enforce `‖(P-I)F‖_s ≥ c‖F‖_s` on positive connected sparse
integer-coefficient series.  That is a refutation of a proposed coercivity
route, not a Collatz advance.  The standing obstruction on the board is
unchanged — full admission `D·c_m < N` — and nothing here touches it.

Nothing is owed.  Stop.
