# Cubic peel: five frozen statements proved

`CollatzMoonshot/Obstructions/CubicPeel.lean` is sorry-free and axiom-clean
(`propext`, `Classical.choice`, `Quot.sound` only). Root `lake build` green.

## What is proved

With `t = 16475 + 25172*s`, `h = recursiveH t`, `n = lowerN h`, `a = tstep n`:

| def | closed form | value |
| --- | --- | --- |
| `cubicN` | `lowerN (recursiveH (16475+25172*s))` | `25542881863 + 39026668800*s` |
| `cubicA` | `(3n+1)/2` | `38314322795 + 58540003200*s` |
| `cubicV` | `5a-2` | `191571613973 + 292700016000*s` |
| `cubicM` | `(3v+1)/64` | `8979919405 + 13720313250*s` |
| `cubicQ1` | `(3a-1)/64` | `1795983881 + 2744062650*s` |
| `cubicQ2` | `5(2a-7)/93` | `4119819655 + 6294624000*s` |
| `cubicE1` | `(3a+1)/58` | `1981775317 + 3027931200*s` |
| `cubicE2` | `(2a-7)/21` | `3648983123 + 5575238400*s` |
| `cubicP` | `4*(8081927465+12348281925*s) - 1` | `32327709859 + 49393127700*s` |

1. `cubic_peel_value` — `certificateValue 0 [v,q1,q2] = certificateValue 0 [a,e1,e2]`.
   Both odd-label products equal `4(2a-7)/(3(9a+61))`. Proof: `odd_ratio` on all
   six labels, `field_simp`, unfold, `push_cast`, `ring`.
2. `cubic_peel_domain` — `cubicM < cubicN`; the four exchanged labels are all
   `< cubicM`; all seven of `n,a,v,q1,q2,e1,e2` are positive, odd, `3`-free.
   Every constant is odd and `3`-free, every slope is `6`-divisible, so `omega`
   discharges each leaf after `simp only` on the defs.
3. `cubic_peel_frontiers` — `tstep (cubicN s) = cubicA s` and
   `tstep (cubicV s) = 32 * cubicM s`, via `two_tstep_odd` then `omega`.
4. `cubic_peel_link` — `cubicN s = lowerN (recursiveH (16475 + 25172*s))`, by `ring`.
5. `cubic_peel_growth_congruence` — `∀ j, ∃ s, 2^(j+2) ∣ cubicP s + 1`. The slope
   `12348281925` is odd, hence coprime to `2^j`; a `ZMod (2^j)` modular inverse
   (`exists_lin`, the same construction as `exists_linear_sol` in
   `LocalGlobalBorrow23`, which is `private` there) solves the linear congruence,
   and the fixed factor `4` lifts `2^j ∣ 8081927465 + 12348281925*s` to `2^(j+2)`.

`h s % 4 = 3` holds for the whole slice (`h s = 1565127 + 2391340*s`), matching
the refinement note in the kickoff.

## Scope disclosure

* No claim about `AllowedMove`/the fixed `C5` palette, no restricted replay, no
  full repair, no balanced certificate, no trajectory convergence.
* The kickoff was revised mid-run (four → five statements; `K32` → `K64`
  coefficients). The revision landed after this session had already rewritten
  the stub file, so the *first four* signatures are carried over verbatim from
  the original stub with `K64` numbers substituted, and the fifth
  (`cubic_peel_growth_congruence`) is authored here to the revised kickoff's
  description. If the parent had a different intended signature for statement 5,
  restate it and the proof above transfers directly.
* One deliberate deviation: `(3v+1)/2 = 32 * cubicM` is stated with `cubicM`
  odd (`8979919405`), rather than `16 * cubicM` with an even `cubicM`. This keeps
  the kickoff's stated invariant that every actual `Nat` def has a positive odd
  `3`-free constant and a `6`-divisible slope.
* All numbers were checked independently in exact rational arithmetic for
  `s = 0..5` before the Lean proofs were written.

No next targets; the parent owns everything else in the repo.

## Checkpoint

* Branch: `main`. HEAD at end of lap: `3e60f4c`
  ("Prove the five frozen variable-cubic peel statements").
* Build state: root `lake build` green, 0 errors.
  `CollatzMoonshot/Obstructions/CubicPeel.lean`: 0 `sorry`, 0 `admit`.
  `#print axioms` on all five theorems: `propext`, `Classical.choice`,
  `Quot.sound` only.
* Committed by this lap: `CollatzMoonshot/Obstructions/CubicPeel.lean` and this
  document. Nothing else.
* Left uncommitted, and deliberately untouched (parent session's in-flight
  research, per the kickoff's ownership split): modifications to
  `CollatzMoonshot/Obstructions/AffineQLift.lean`,
  `HANDOFF-2026-09-29-affine-lift.md`,
  `RESEARCH-2026-09-28-borrow-checkpoint.md`,
  `RESEARCH-2026-09-28-nn-borrow-checkpoint.md`, four `experiments/*.py`, and the
  untracked `RESEARCH-2026-09-29-{affine-root-classification,
  borrowing-closure-audit,head-continuation,ordinal-repair-checkpoint,
  unrestricted-supply-addendum}.md`.
* `CollatzMoonshot.lean` already contained `import
  CollatzMoonshot.Obstructions.CubicPeel` before this lap (parent's edit, still
  uncommitted); the root build depends on it, so the parent's commit should
  include it.
* `DIRECTION.md`'s CURRENT DIRECTIVE is still the 2026-09-13 reflection pause,
  which predates the operator's scoped kickoff laps. Not edited (altitude laps
  own it).

## Exact next steps (for whoever picks this up)

This lap's scope is closed; there is no follow-on target inside it. If the
parent wants more from this file:

1. Reconcile statement 5. If the parent's revised stub had a different intended
   signature for the growth congruence than
   `∀ j, ∃ s, 2^(j+2) ∣ cubicP s + 1`, restate it; the `exists_lin` modular
   inverse plus the `4 → 2^(j+2)` lift transfers verbatim.
2. Decide `16 * cubicM` (even `cubicM = 17959838810`) vs the committed
   `32 * cubicM` (odd `cubicM = 8979919405`) in `cubic_peel_frontiers`. Both are
   true; only the committed one keeps every actual `Nat` def odd and 3-free.
3. `exists_lin` duplicates `exists_linear_sol` in `LocalGlobalBorrow23.lean`,
   which is `private` there. De-privatising that one and deleting the copy here
   is a clean small cleanup.
