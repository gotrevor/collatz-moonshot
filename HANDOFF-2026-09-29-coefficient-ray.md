# HANDOFF — coefficient-ray actual-edge obstruction (complete)

Scope: `CollatzMoonshot/Obstructions/CoefficientRay.lean` only.  All four
frozen targets are proved; definitions and theorem statements are unchanged.

## Status

`lake build` green (8823 jobs).  `lake env lean scripts/AxiomAudit.lean` runs
clean, including the frozen `CoefficientRayConsumers` section.  `#print axioms`
on `ray_six_steps`, `ray_edge_witness`, `ray_edge_exists`, `no_uniform_ray_rank`
gives exactly `[propext, Classical.choice, Quot.sound]` — no `native_decide`,
no project axiom.

## How the proofs go

Four private helpers were added above the frozen section:

* `tstep_even_val'` / `tstep_odd_val''` — the two parity forms of one
  accelerated step, on top of the public `two_tstep_odd` from `FiveHead`.
* `rayA_core {K} (0 < K) : tstep^[6] (64*K-5) = 81*K-5` — the `110110` word
  `64K-5 → 96K-7 → 144K-10 → 72K-5 → 108K-7 → 162K-10 → 81K-5`, with `K`
  opaque to `omega` so natural subtraction stays safe from `0 < K` alone.
* `rayB_core (w) : tstep^[6] (64*w+1) = 27*w+1` — the `101010` word; no
  positivity hypothesis is needed since no subtraction occurs.
* `rayK_pos`, `rayA_eq` — `0 < 72*3^j*w` and `rayA j w = 64*(72*3^j*w) - 5`.

`ray_six_steps` is `rayA_core`/`rayB_core` plus `81*(72*3^j*w) = 216*3^j*(27*w)`.

`ray_edge_witness` sets `K = 72*3^j*w`, records `72*w ≤ K` (from `1 ≤ 3^j`) so
that `rayA j w > rayB w` is an `omega` consequence, then discharges the two
affine identities `64*(81K-5) = 81*(64K-5)+85` and `64*(27w+1) = 27*(64w+1)+37`
by `omega`.  For `carriesSignature` the natural subtraction is eliminated first
(`Nat.cast_sub` under `5 ≤ 64*K` and `5 ≤ 81*K`), giving `(A:ℤ)+1 = 64K-4` and
`(A':ℤ)+1 = 81K-4`; then `72*3^j*(64w) = 64K` and `216*3^j*(27w) = 81K` by
`ring` after rewriting `(K:ℤ) = 72*3^j*w`.  Both endpoints therefore carry the
inherited offset `-4`.

`ray_edge_exists j` takes `w = 1` and repackages, with `τ.1 = 3*σ.1` from
`pow_succ`.  The witness pair genuinely depends on `j`.

`no_uniform_ray_rank` does well-founded induction on `hr` with predicate
`fun x => ∀ j, rank (raySignature j) = x → False`, stepping via
`hstep j : r (rank (raySignature (j+1))) (rank (raySignature j))`.  It is
stated for an arbitrary well-founded codomain, not `ℕ`.

## Independent anchor (checked, not committed as a target)

`rayA 0 1 = 4603`, `rayB 1 = 65`, and `tstep^[6] 4603 = 5827`,
`tstep^[6] 65 = 28` by `native_decide` in a scratch file — matching the
kickoff's hand anchor against the actual definitions.

## Scope notes

No hard-family CRT theorem, no convergence assumption, no strengthening of
`rayEdge`.  The module continues to claim only a local positive pair per edge
of the projected signature graph; lifting finite prefixes into the original
hard family remains outside this file.  Nothing else in the repo was touched.

## Checkpoint

* Branch: `main`
* HEAD at completion: `2fef69e` "Prove the four frozen coefficient-ray obstruction targets"
* `CollatzMoonshot/Obstructions/CoefficientRay.lean`: 0 `sorry`, 0 `axiom`.
* Working tree otherwise carries the parent's pre-existing uncommitted edits
  (`APPROACHES.md`, `CollatzMoonshot.lean`, `scripts/AxiomAudit.lean`,
  `experiments/`, research notes).  Those are **not mine** and were left alone.

## Next steps

None for this task — the kickoff's scope is closed and it authorizes no
successor.  If the parent wants to extend the module later, the natural
follow-ons, all explicitly out of scope here, are:

1. Lifting finite prefixes of the coefficient ray into the original hard
   family (paper/CLI result; belongs outside this module).
2. Generalizing `no_uniform_ray_rank` from state-only ranks to ranks that may
   read a bounded amount of orbit history.
3. A hard-family CRT theorem connecting `raySignature` to the real offsets.

`box done --green` was signalled after the green build and clean audit.
