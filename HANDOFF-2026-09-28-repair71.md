# Handoff: the frozen 71 repair under the restricted palette is proved

Date: 2026-09-29.  Branch `main`.  Scope: `CollatzMoonshot/Obstructions/Repair71.lean`,
`CollatzMoonshot/Obstructions/Repair71Data.lean`, this file.

## Result

`seventyOne_repair_restricted` is proved, with the frozen skeleton untouched:

```lean
theorem seventyOne_repair_restricted :
    Relation.ReflTransGen AllowedMove
      (16, (certificate71 : Multiset ℕ))
      (28, ((seventyOnePrefix.filter (fun u => u % 2 == 1) : List ℕ) : Multiset ℕ))
```

`RepairState`, `allowedUnit` and `AllowedMove` are byte-identical to the installed
skeleton.  No constructor was added, no arbitrary value-one word is inserted, and no
soundness assumption is taken on trust.

`#print axioms seventyOne_repair_restricted` gives
`[propext, Classical.choice, Quot.sound, repairActs_run._native.native_decide.ax_1_1]`.
The only extra axiom is the `native_decide` reduction of the finite run.
`step_sound` and `run_sound` — the entire mathematical content — are axiom-clean.
Root `lake build` is green (8810 jobs).

## Architecture

* `eraseList m l` removes the entries of `l` from `m` one at a time, failing on the
  first unavailable entry.  `eraseList_spec` gives `m' + ↑l = m`, which is exactly the
  `rest + ↑m.1` context shape the `AllowedMove` constructors demand.  This is what makes
  availability a *proved decomposition of the current multiset*, not a side check.
* `Act` / `decodeAct` / `step` / `run`: an executable `Option RepairState` interpreter
  that fails on the first unavailable or non-preserving move.  `step` re-derives
  legality with `legalPairMove` and availability with `eraseList` from the *current*
  multiset; JSON is only a proposal.
* `step_sound : step s a = some s' → AllowedMove s s'` maps each accepted branch onto
  exactly one `AllowedMove` constructor; `run_sound` folds it into `ReflTransGen`.
  The headline is `run_sound repairActs _ _ repairActs_run` — no scalar-equality
  shortcut anywhere.
* `Repair71Data.repairCode` is the 3281-entry action word, in 33 private chunks to keep
  list-literal elaboration shallow.  Encoding: `[a,b,c,d]` = quadratic `[a,b] → [c,d]`,
  `[0,i]`/`[1,i]` = insert/remove the `i`-th unit (`0=U2, 1=U8, 2=U13`), `[2]` = cubic
  `C5`, `[3]` = its reverse.

## The three edges, and how the borrowed word is earned

The action word is the concatenation of exactly the three required edges:

| indices | edge | length |
|---|---|---|
| 0 – 1505 | `x →* x + W` : build `W` from the seed units inside the certificate | 1506 |
| 1506 – 1774 | `x + W →* y + W` : the 269 ordered main schedule actions | 269 |
| 1775 – 3280 | `y + W →* y` : the formal inverse of block one, inside `y` | 1506 |

Block three is the literal formal inverse of block one (list reversed, `Q(r,i) ↦ Q(i,r)`,
insert ↦ remove), so the borrowed word is *returned*, not abandoned.

`W` is derived, never inserted.  Each borrow-DAG node `{label u, remove [a,b], insert [c,d]}`
expands to `deriv a ++ deriv b ++ [Q [a,b] [c,d]]`; a seed label resolves to `U2` for 1,
`U8` for `19,25,29,55,83` (including the labels shared with `U13`), `U13` otherwise.  The
96 DAG labels are distinct and disjoint from the unit labels, `u ∈ insert` was checked at
generation time, and every emitted `Q` is re-checked in-kernel by `legalPairMove`
(two-in/two-out, positive odd, `certificateValue 0` preserved).  The 7555 bridge node
`[1079,5035] → [1007,7555]` is inside block one like any other node — the obsolete
wave-one gap is closed by construction, not by an axiom.

Independently recomputed from the DAG and catalyst (generator `experiments`-side, then
re-verified in kernel by the run): `W` has 2667 twos and 4394 odd factors on 108 odd
labels (2667 + 4394 = the reported 7061 on 109 coordinates including label 0), matches
`replay.borrow_unit` coordinate-by-coordinate, and dominates every catalyst coordinate.
The middle endpoint is an exact multiset equality including the factor-2 count:
`16 + 9·3 − 3·5 = 28`.

## Open / next

Nothing is open in this module.  Caveat unchanged from the kickoff: this is a finite
repair certificate for *this* 71 certificate, not a terminating repair procedure for
arbitrary starts.  The reachability relation says nothing about how to choose a target
path for an unknown orbit.

The JSON artifacts, Python generator/replayer and persistent tests are integrated with the proof in the repository.  See `RESEARCH-2026-09-28-delegated-checkpoint.md` for the independent branches and remaining mechanisms.
