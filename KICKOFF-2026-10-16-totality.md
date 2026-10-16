# KICKOFF 2026-10-16: the totality family, `RcwaOrbitCount.TotalityFamily` discharged

Repo `collatz-moonshot` worktree `collatz-moonshot-amusical-zcore` (branch `wip/totality-2`).
Close every `sorry` in four new files, layered bottom-up:

| File | What | `sorry`s |
|---|---|---|
| `CollatzMoonshot/RcwaTotalityGlue.lean` | gluing an increment chain into a machine, before and after `histWrap` | 12 |
| `CollatzMoonshot/RcwaTotalityCompile.lean` | a computable numbering of `godel` of the glued wrapper, doubled on `ℕ` | 12 |
| `CollatzMoonshot/RcwaTotalityRestart.lean` | Lemma A: the restart machine, mortal iff `φ_e` total | 16 |
| `CollatzMoonshot/RcwaTotality.lean` | assembly: `totalityFamily` and the hypothesis-free corollaries | 2 |

The three assemblies are **already proved from the layer lemmas** (they compile with only
upstream `sorry`s): `totalityFamily`, `exists_computable_compile`, `mortal_asharp_iff`,
`mortal_iff_total`, plus `glueH_det`, `glueH_rev`, `asharp_det`, `u₂_det` and all corollaries.  So
closing the 42 leaf `sorry`s closes everything.

Imports: `RcwaOrbitCount.lean` (statements ratified; its `sorry`s are being closed **in parallel**
by the orbit-count treadmill in another worktree — use its statements freely, never edit it), and
through it `RcwaHalting`, `RcwaSameOrbit`, `RcwaMachine`, `CounterMachine`,
`CounterMachineUniversal` (all proved).  The `RcwaOrbitCount` statements used here:
`exists_macro_chain`, `histWrap_macro_sound`, `godel_mortal_iff`, `double_sourcesHalt_iff`,
`exists_forever_of_not_halts`, `halts_of_reaches`, and the corollary inputs
`mortalityUndecidable_of_totalityFamily`, `orbit_count_family`, `oneOrbit_not_re`,
`oneOrbit_not_coRE`, `not_computable_oneOrbit`, `not_computable_finiteOrbits`.

Sources: research note `~/personal/tmp/amusical-agents/out/undec-lemma.md` §7 (Lemma A) and §8;
`KICKOFF-2026-10-16-orbit-count.md` ("Later layer"); `KICKOFF-2026-10-16-cm-upper.md` (the
`histWrap` / `godel` / `double` proofs, same style).  Mathlib: `Computability/PartrecCode.lean`
(`evaln`, `evaln_complete`, `evaln_mono`, `primrec_evaln`, `eval_part`),
`Computability/TuringMachine/Config.lean` (`ToPartrec.Code.exists_code`),
`Computability/TuringMachine/ToPartrec.lean` (`trList`, `trNat`, `trPosNum`, `init`, `tr_eval`),
`Computability/Primrec/List.lean` (`list_map`, `list_flatMap`, `list_range`, `list_getD`,
`list_foldr`), `Primrec.dom_finite`.

## The route, and why

**Where `e` enters.**  Only as the *length* `L e = 1 + 5 · inputNum e` of a chain of `L + 1`
increments of the `main` counter, glued from `bnd hole` to `bnd back` into one fixed machine
`B₀ = histWrap (restart u) lab`.  Everything else (`u`, `restart u`, `lab`, the primes) is fixed.

**Lemma A** (`RcwaTotalityRestart`).  `restart u` gates every step of the fixed universal
counter machine `U₂ u` (Mathlib's TM2 compile `lcm (trNormal u halt)`, restricted to its finite
reachable set, as in `undecidableCM`) by a budget `p`, moving one token per step to `t`; an empty
budget restarts.  The restart clears `U₂`'s five counters and stops at `hole`; the chain adds
`L + 1 = 2 + 5 · inputNum e` to `main`, i.e. the numeral of `cons :: trList [e]`; from `back` the
machine pushes `bit1` `x` times (`main ↦ 5 · main + 4`, through `tmp`), restores `x`, sets
`p := t + 1` and enters `gate start`.  The main stack is then `trList [2^x − 1, e]`, and `u`
(from `exists_universal₂`) halts on `[a, e]` iff `φ_e` halts on all `y ≤ a`.  So the glued
machine is mortal iff `∀ x, φ_e` halts on `0 … 2^x − 1`, iff `Total e`.  Using "halts on an
initial segment" removes any need to decode `x` from `2^x − 1`.

**Uniform compile** (`RcwaTotalityCompile`).  The chain is glued *after* `histWrap`, so the
wrapper (and its labels, which `histWrap_rev` needs globally injective) is the fixed `B₀`, and the
state type grows only by `Fin L`.  `godel` is local (every non-guard rule comes from one rule of
`B`, and commutes with relabelling), so `godel (glue B₀ …  L)` is the image of two *fixed* finite
lists: `godel B₀` under `inl`, and `godel` of the one-rule unit `[some (), +main, none]` under the
plug map and under `L` link maps.  Numbering `inl` states by a fixed `fixNum` and chain state `k`'s
tags in block `k`, the numbered rule list is `explicitR L`: two constants plus `L` affinely
relocated copies of a constant.  `doubleN` is `double` on `ℕ`-numbered states, so `G L :=
doubleN (explicitR L) (S₀ + L · T)` is computable, and `doubleN_valid_iff` transfers `Valid` and
`SourcesHalt ↔ Mortal` from the ratified `double_valid` and `double_sourcesHalt_iff`.

**Why not the alternatives.**
* *A `Machine`-level prefix edit of one fixed compiled machine*: `e` must sit inside the restart
  loop (garbage configurations with a wrong stored `e` would otherwise decide mortality), so the
  edit would change the doubled dynamics and `Valid` (reversibility, `pair_sink`, `NoBiInfinite`,
  `EndToStart` on all configurations) would have to be re-proved for the edited machine.  Here
  `Valid` comes from `double_valid` unchanged.
* *Gluing the chain before `histWrap`*: `histWrap_rev` needs labels injective over all rules, so
  the label count `K` (and every wheel of the fixed part) would grow with `L`, and `HState`'s junk
  (`pre ρ` for every quadruple) would grow quadratically.  Gluing after wrapping costs only the
  generic `glueH_revMortal` and `glueH_mortal_iff`.
* *A computable compile of the whole typed pipeline with a renumbering-invariance lemma*: the
  locality of `godel` plus one fixed numbering does the same job with no explicit enumeration of
  `GRule` / `HRule` instances.

## Ratified, do not change

Every definition and theorem statement in the four files:

* **Glue:** `Quad.mapQ`, `CM.mapQ`, `chainFirst`, `chainNext`, `chain`, `glue`; `glue_step_inl`,
  `glue_step_inl_inv`, `glue_chain_reaches`, `glue_chain_reaches_of_inr`, `glue_not_stuck_chain`,
  `glue_det`, `glue_rev`, `glue_lapsMixed`, `glue_macroStep_cases`, `histWrap_src_ne_bnd`,
  `glueH_det`, `glueH_rev`, `glueH_revMortal`, `glueH_mortal_iff`.
* **Compile:** `GState.map`, `GState.base`, `GState.tag`, `GState.baseTagEquiv`, `guardRule`,
  `doubleN`, `layerEquiv`, `quadEquiv`, the two `Primcodable` instances, `unitRule`, `plugMap`,
  `linkMap`, `tagNum`, `fixNum`, `glueNum`, `lnum`, `fixTab`, `reloc`, `plugReloc`, `fixList`,
  `unitList`, `rsGlue`, `explicitR`; `godel_mono`, `godel_mapQ`, `godel_local`,
  `godel_single_mapQ`, `step_congr`, `machine_congr`, `doubleN_valid_iff`, `computable_mapQ`,
  `computable_doubleN`, `mem_rsGlue`, `rsGlue_num`, `computable_explicitR`,
  `exists_computable_compile`.
* **Restart:** `S₂`, `U₂`, `start₂`, `gIter`, `honest`, `ACtr`, `clrCtr`, `AState`, `ARule`,
  `restart`, `Asharp`, `acfg`; `exists_universal₂`, `trNat_two_pow_sub_one`, `num_trList_pair`,
  `halts_u₂_iff`, `u₂_det`, `finite_aState`, `restart_det`, `restart_src_ne_hole`,
  `restart_normalAt_back`, `asharp_det`, `reaches_round`, `reaches_gated`, `halts_of_stuck_gate`,
  `step_gate_zero`, `gate_halts_or_restart`, `halts_or_reaches_restart`, `halts_of_steady`,
  `not_halts_of_not_halts`, `mortal_asharp_iff`, `mortal_iff_total`.
* **Assembly:** `exists_lab`, `exists_primeData`, `totalityFamily`, `mortalityUndecidable`,
  `orbit_count_family'`, `oneOrbit_not_re'`, `oneOrbit_not_coRE'`, `not_computable_oneOrbit'`,
  `not_computable_finiteOrbits'`.

**Rules.**
* No `native_decide`, no axioms, no `maxHeartbeats` bumps.  Lean lines ≤ 100 characters.
* Do **not** edit `RESEARCH-*.md`, `RcwaOrbitCount.lean`, or any other existing `.lean` file.
* Commit after each proved lemma.  Notes as you go in `HANDOFF-totality.md`.
* Helper lemmas and definitions are welcome (above their first use).  Any cleaner route is fine as
  long as the ratified statements are unchanged.

**Order of attack.**
1. Glue §1 (`glue_*`): small, unblocks everything.
2. Compile §1 (`godel_*` locality), then `mem_rsGlue`, `rsGlue_num`.
3. Restart §1 (`exists_universal₂`, numerals, `halts_u₂_iff`), then `restart_det` and the run
   lemmas; `reaches_round` first (the honest pipeline), then the garbage lemma.
4. Glue §2 (`glueH_revMortal`, `glueH_mortal_iff`).
5. Compile §2-§3 (`machine_congr`, `doubleN_valid_iff`, computability).
6. `exists_lab`, `exists_primeData` (copy from `exists_valid_machine`).

## Truth checks already run (`tmp/drafter-total/`)

All Python, each with teeth that fail as they must.  Outputs `*.out` beside the scripts.

| Check | Result | Teeth |
|---|---|---|
| **A** `lemma_a_check.py`: the exact `ARule` restart machine with the chain glued (`L = 1, 3`), a toy `U₂` in place of the universal machine; mortality on a box of **every state × every counter** | toy total on honest inputs (loops on garbage `main = 1`): **0 / 29,184** configurations (counters in {0,1}) and **0 / 1,121,931** (counters in {0,1,2}) fail to halt; toy diverging at `x = 0`: some configuration runs on.  `reaches_round`'s formula exact on **19,683** starts | budget not growing (`p := 1` each round): total toy, yet a configuration runs on.  No budget gate: total toy, yet a garbage loop runs on |
| **N** `numeral_check.py`: `num (trList [2^x − 1, e]) = gIter x (2 + 5 · inputNum e)`, `trNat (2^x − 1) = bit1^x` | **0 / 480**, **0 / 20** bad | pushing `bit0` (digit 3): **440 / 480** bad |
| **G** `glue_check.py`: `glue (histWrap U) (bnd hole) (bnd back)` vs `glue U hole back`, `U` mortal / immortal (157 / 92 wrapper states) | Morita-deterministic and -reversible (0 violations); every backward run finite on the box; mortal on the box iff the A-level glue is (mortal: 0 / 0 capped; immortal: 108 / 5,130 capped) | a rule into `back`: 1 reversibility violation.  Chain on the unwrapped `U`: 1 violation.  A rule out of `hole`: 1 determinism violation |
| **C** `compile_check.py`: Lean's `godel` (guard at **every** base state, junk state included) of the glued wrapper, numbered by `glueNum`, vs `explicitR` | equal as sets for `L = 0 … 5` (18,252 fixed states, `T = 117`); `doubleN (explicitR 2)` (`K = 36,972`) deterministic, reversible, `pair_sink`, `EndToStart` on a box | `reloc` without the `back` case: 3 rules differ.  Guards only at occurring states: 1 differs.  All turnarounds: 79,812 determinism failures |

`glue_check.py` uses the orbit-count drafter's loop accelerator (copied, spot-checked there).
`cm_mirror.py` is the cm-upper drafter's mirror of `histWrap` / `godel` / `double`.

## Paper proofs (Ren)

Conventions.  `A ⊕ chain` states: `inl q` are `U`'s, `inr k` the chain's.  `Bd := inl '' B ∪
range inr`.  "Mapped rule": `ρ.mapQ inl` for `ρ ∈ U`.  Chain rules have sources `inl hole` and
`inr k` only, and targets `chainFirst back L`, `chainNext back k` (`inr _` or `inl back`).

### Glue §1 (≈ 420 lines)

* **`glue_step_inl`** (10).  The mapped rule is in `glue`.
* **`glue_step_inl_inv`** (25).  A rule with source `inl q`, `q ≠ hole`, is mapped (chain sources
  are `inl hole`, `inr _`); unmap with `Sum.inl_injective`.
* **`glue_chain_reaches_of_inr`** (40).  Induction on `L − k` (or on `k` downward): link `k` is an
  increment of `i` into `chainNext back k`; `Function.update` arithmetic.
* **`glue_chain_reaches`** (25).  The plug into `chainFirst back L`, then `_of_inr` at `0` (or
  `back` directly when `L = 0`).
* **`glue_not_stuck_chain`** (20).  An increment always fires.
* **`glue_det`** (50).  Two rules from one source: both mapped (`hU`, ops unchanged by `mapQ`),
  or both chain rules (the same rule: one rule per source), or mixed — impossible, a mapped rule
  from `inl hole` would be a rule of `U` from `hole` (`hhole`).
* **`glue_rev`** (60).  Into `inl q`, `q ≠ back`: only mapped rules (`hU`).  Into `inl back`: no
  mapped rule (`hback`), and exactly one chain rule (the plug if `L = 0`, link `L − 1`
  otherwise).  Into `inr j`: the plug (`j = 0`) or link `j − 1`, never both.
* **`glue_lapsMixed`** (60).  A closed walk off `Bd`: every source is `inl q` with `q ∉ B`, so not
  `inl hole` (`hhole : hole ∈ B`) and not `inr`; so every rule is mapped.  Unmap the walk
  (chaining equalities through `Sum.inl.inj`); `Op.delta` is unchanged; apply `h`.
* **`glue_macroStep_cases`** (100).  First step by a chain rule: its target is in `Bd` (`back ∈
  B`), so the run has length `1` (intermediate states are off `Bd`): the right disjunct.  First
  step by a mapped rule: by induction along the run, every intermediate state is `inl q'` with
  `q' ∉ B`, hence not `hole`, so each step is mapped (`glue_step_inl_inv`); the end is `inl q''`
  with `q'' ∈ B`.  Unmapping gives `MacroStep B U.Step`.

### Glue §2 (≈ 320 lines)

* **`histWrap_src_ne_bnd`** (10).  `cases` on `HRule`: only `guard` leaves a `bnd`, with source
  `bnd ρ.src`, `ρ ∈ U`.
* **`glueH_revMortal`** (120).  `revMortal_of_macro` (finite `HState Q ι K ⊕ Fin L`) with
  `glue_lapsMixed histWrap_lapsMixed` (`bnd hole ∈ range bnd`).  Potential on `Bd` states:
  `Φ b = (L + 2) · b.2 hist + pos b.1`, `pos (inl (bnd s)) = if s = hole then 0 else L + 1`,
  `pos (inr k) = k + 1`.  By `glue_macroStep_cases`, a macro step is (a) a mapped wrapper macro
  step: `histWrap_macro_hist` (needs `hU`, `hlab`) raises `hist` by `≥ 1`, `pos` falls by at most
  `L + 1`; or (b) a chain step: `hist` unchanged (the op is on `val i`), `pos` rises (`0 → 1` or
  `0 → L + 1` at the plug since `back ≠ hole`; `k + 1 → k + 2` or `L → L + 1`).  So `Φ` strictly
  rises along forward macro steps, and an infinite backward macro chain is an infinite descent
  in `ℕ`.
* **`glueH_mortal_iff`** (180).  Write `A := glue U hole back i L`, `B := glue (histWrap U lab) …`;
  both deterministic (`glue_det`).
  * (⇐, garbage) If some `B`-configuration does not halt, `exists_macro_chain` (finite types;
    `glue_lapsMixed histWrap_lapsMixed`) gives an infinite macro chain `b`.  Decode each step
    (`glue_macroStep_cases`): mapped wrapper macro steps are `U`-steps on the `val` counters
    (`histWrap_macro_sound`), chain steps are chain steps of `A` on the `val` counters.  The
    projections `(inl s | inr k, fun j => (b n).2 (.val j))` form an infinite `A`-run, so
    `¬ A.Halts` (`CM.not_halts_of_forever`), contradicting `Mortal A`.
  * (⇒) `CM.halts_iff_of_sim` (`B` deterministic) with `Sim c b := ∃ h, b = (lift c.1, hcfg c.2
    h)`, `lift = Sum.map bnd id`.  Steps: a mapped `U`-step lifts by `histWrap_macro` +
    `macroStep_transGen`, mapped into `B`; a chain step is the same chain step on `val i`.  Stuck:
    `inl hole` and `inr k` are never stuck (`glue_not_stuck_chain`); at `inl s`, `s ≠ hole`, `U`
    is stuck, and `B` halts in at most one step (no rule from `s`: `bnd s` is stuck; else `guard`
    to `act s`, where no `op ρ` fires — as in `histWrap_halts_of_stuck`, whose run never reaches
    `bnd hole`; reprove it in `B`).  So `B.Halts (lift c) ↔ A.Halts c`.

### Compile §1: locality (≈ 230 lines)

`cases` on `GRule` (30 constructors; `MoveRule` is a disjunction of two memberships).  Every
non-guard constructor has exactly one premise `⟨q, op, q'⟩ ∈ B` and side conditions on `j`,
`p i` only.

* **`godel_mono`** (15).  Rebuild the same constructor.
* **`godel_mapQ`** (60).  Same constructor at `f q`, `f q'`: the premise is the `mapQ` of the old
  one.
* **`godel_local`** (60).  `guard q` is the left disjunct; otherwise `β` is the premise's rule.
* **`godel_single_mapQ`** (90).  The premise `⟨q, op, q'⟩ ∈ {β.mapQ f}` gives `q = f β.src`, `op =
  β.op`, `q' = f β.dst`; the same constructor at `β.src`, `β.dst` is in `godel {β}`, and its
  `mapQ (GState.map f)` is `r`.  No injectivity needed.

### Compile §2: doubling on `ℕ` (≈ 300 lines)

* **`step_congr`** (30).  If a rule of `R` fires at `c`, `find?` on `R'` returns a firing rule of
  `R'`, and determinism of `R'` equates the targets; if none fires, none fires in `R'`.
* **`machine_congr`** (120).  `Deterministic M.rules` from `hmem`.  `step` agrees
  (`step_congr`), hence `run`, `IsSource`, `IsSink`, `Halts`, `NoBiInfinite`, `EndToStart`;
  `WF.src_lt`/`dst_lt`, `Reversible` by membership; `pair`, `pairFn` equal.
* **`doubleN_valid_iff`** (120).  `layerEquiv num (q, b) = 2 · num q + (if b then 1 else 0)`
  (`finProdFinEquiv`, `finTwoEquiv`).  `machine_congr` with `M := doubleN …`, `M' := double …`:
  `K = S * 2` both; `pair`: `(List.finRange (S*2)).map …` equals `(List.range (S*2)).map (xor 1)`
  pointwise (`List.map_coe_finRange` or `List.ext_getElem`); members via `mem_double`:
  `toRule (2 · num ·+ 1) ρ = toRule (2 · + 1) (ρ.mapQ num)` (cases on `ρ.op`), `(ρ.mapQ f).inv =
  ρ.inv.mapQ f`, and `turnRules rs nP nM q = turnRules (rs.map (mapQ num)) … (num q)` (the `any`
  condition agrees by injectivity of `num`).  An exact list equality also works if the turn-part
  `filterMap` over `List.finRange (S * 2)` cooperates.

### Compile §3: computability (≈ 280 lines)

* **`computable_mapQ`** (30).  Through `quadEquiv`: `(f a src, op, f a dst)`.
* **`computable_doubleN`** (150).  `Machine` is `Primcodable` through `Machine.equivProd`; `Rule`
  through `Rule.equivProd`.  `toRule n` is `(n src, t₁ op, t₂ op, d₁ op, d₂ op, n dst)` with the
  op-parts `Primrec.dom_finite`.  `turnRules`: rewrite the `filterMap` over the four patterns as a
  `flatMap` of `if … then [] else [r]`, and `List.any` as a `foldr`.  `list_map`, `list_flatMap`,
  `list_range`, `list_append`.
* **`computable_explicitR`** (100).  Constants `++` `list_map` with `computable_mapQ` of
  `plugReloc …  L` `++` `list_flatMap` over `list_range L` of `list_map` with `reloc … L k`.
  `reloc`, `plugReloc`: `Primrec.ite` on `n < T`, `k + 1 < L`, `0 < L`, arithmetic, and `fixTab`
  = `list_getD` of a constant list.

### Compile §4: the glued list (≈ 240 lines)

* **`mem_rsGlue`** (120).  (→) `fixList` members are in `godel B₀`; `godel_mapQ` puts their `inl`
  images in `godel (B₀.mapQ inl)` and `godel_mono` in `godel (glue …)`.  `unitList` members: the
  same with `{unitRule i}.mapQ (plugMap …)` = `{plug}` and `.mapQ (linkMap … k)` = `{link k}`, both
  in `chain ⊆ glue`.  (←) `godel_local`: a guard at `q`: its base is `inl h` (guard `h` is in
  `godel B₀`, mapped) or `inr k` (guard at `some ()` in the unit list, mapped by `linkMap k`).
  Otherwise `β ∈ glue`: mapped (`godel_single_mapQ` with `f = inl`, then `godel_mono` into
  `godel B₀`), the plug or a link (`godel_single_mapQ` with `plugMap` / `linkMap k`; `{β}` is
  `{unitRule i}.mapQ …`).
* **`rsGlue_num`** (120).  `List.map_append`, `List.map_flatMap`, `List.map_map`; `List.finRange L`
  to `List.range L` (`List.map_coe_finRange`, `List.flatMap_map`).  Pointwise:
  `glueNum (g.map inl) = fixNum g` (`baseTagEquiv` reconstruction `g.tag.map (fun _ => g.base) =
  g`); `glueNum (g.map (plugMap …)) = plugReloc … (lnum g)` and `glueNum (g.map (linkMap … k)) =
  reloc … k (lnum g)` by cases on `g.base` (`some ()`: tag `< T`, block `k` or the `hole` table;
  `none`: `T +` tag, block `k + 1`, block `0`, or the `back` table when the chain ends);
  `fixTab q j` for `j < T` is `fixNum ((tagNum.symm j).map fun _ => q)` (`List.getD_eq_getElem`,
  `List.getElem_map`, `List.getElem_finRange`).

### Restart §1: universality (≈ 190 lines)

* **`exists_universal₂`** (80).  `f v := Nat.rfind fun k => some (decide (∀ y ≤ v₀,
  (evaln k (ofNat Code v₁) y).isSome))` on `List.Vector ℕ 2`; the bounded `∀` as `List.all` over
  `List.range (v₀ + 1)` (a `foldr`), `primrec_evaln`, `Partrec.rfind`; `Nat.Partrec'.part_iff`,
  `exists_code`.  Dom: `rfind` terminates iff some `k` works for all `y ≤ a` iff each `y` halts
  (`evaln_complete`; take the max `k`, `evaln_mono`; back with `evaln_sound`).
* **`trNat_two_pow_sub_one`** (30).  Induction: `2^(x+1) − 1 = 2 (2^x − 1) + 1`, and `trNat (2m +
  1) = bit1 :: trNat m` (cases `m = 0` / `Num.pos p`, `trPosNum (bit1 p)`; see the `Num` casework
  in `computable_inputNum`).
* **`num_trList_pair`** (30).  `trList [a, e] = trNat a ++ cons :: trList [e]`; `num (bit1 :: l) =
  5 · num l + 4` (`num_cons`, `digit`), induction on `x` (`Function.iterate_succ_apply'`);
  `num (cons :: trList [e]) = 2 + 5 · inputNum e`.
* **`halts_u₂_iff`** (50).  As in `undecidableCM`: `CM.halts_restrict (reachSet_closed
  (tr_supports u halt))`, `halts_iff_eval` with `S = K'.elim (trList [2^x − 1, e]) [] [] []`,
  `stackVec S = honest (num …)` (`funext`, cases), `num_trList_pair`, `tr_eval`.

### Restart §2: the machine (≈ 150 lines)

* **`finite_aState`** (40).  An injection into `(S₂ u × Fin 4) ⊕ Fin 40` (or `Finite.of_injective`
  of a `Sum`-coding), `reachSet_finite`.
* **`restart_det`** (100).  By source, `cases h₁ <;> cases h₂` as in `histWrap_det`: `run s` —
  two `sim` rules come from distinct rules of `U₂` (`u₂_det`, `Op.map`); `gate`, `clr j`, `cx`,
  `mv`, `ml`, `cw`, `bt` — two tests of one counter; `clrZ` needs `j' = j + 1 < 5`, so `clr 4` has
  only `clrP`, `clrH`; `mlI` needs `1 ≤ j`, `j' = j + 1 ≤ 5`; `adI` needs `j' ≤ 3`.
* **`restart_src_ne_hole`**, **`restart_normalAt_back`** (5 each).  `cases`.

### Restart §3: runs (≈ 650 lines)

Write `A := Asharp u L`.  Helpers: lift `restart u`-steps to `A` (`glue_step_inl`); a generic
*drain loop* lemma (a test state `a`: `c P → a₁`, `a₁ : c−`, then a straight line of increments
back to `a`; `c Z → exit`) proved once by induction on `c`, and the straight-line run.

* **`reaches_round`** (300).  Phase by phase, with arbitrary counters:
  * `clr j`: drains `clrCtr j` to `0`, then `clr (j+1)` / `hole` (five drains);
  * `hole`: `glue_chain_reaches` adds `L + 1` to `main` (from `0`), reaching `back`; `back → cx`;
  * copy loop, induction on `x` with `tmp = 0` invariant: `cx₁` (`x−`), `cx₂` (`w+`), `mv` drains
    `main` into `tmp`, `ml` drains `tmp` adding `5` to `main` each, `ad 0 … 3` adds `4`: one lap
    is `main ↦ 5 · main + 4`, `x ↦ x − 1`, `w ↦ w + 1`; at `x = 0`, `cxZ → cw`;
  * `cw` drains `w` into `x` (`x := x + w`), `bt` drains `t` into `p`, `bt₃` adds `1` into
    `gate start`.
  Final counters equal `acfg (honest (gIter x (L+1))) (x + w) 0 (p + t + 1) 0` by `funext`
  (only `main` is nonzero among the `sim` counters).
* **`reaches_gated`** (50).  Induction on `StepsN`: `gateP`, `sp₁`, `sp₂`, then the `sim` rule of
  the `U₂`-step (`Op.map` of `Act`).
* **`halts_of_stuck_gate`** (40).  Three steps to `run s`; no `sim` rule fires (else `U₂` steps).
* **`step_gate_zero`** (10).  `gateZ`.
* **`gate_halts_or_restart`** (60).  Induction on `p`: `p = 0`: `step_gate_zero`.  `p + 1`: to
  `run s`; if `U₂` is stuck at `(s, v)`, halt (`halts_of_stuck_gate`); else one `U₂` step to `gate
  s'` with budget `p` (`reaches_gated` with `m = 1`) and recurse.
* **`halts_or_reaches_restart`** (200).  Case on the state.  `inr k`, `inl hole`: chain to `back`
  (`glue_chain_reaches_of_inr`), then as `back`.  Pipeline states (`back`, `cx…`, `mv…`, `ml…`,
  `ad j`, `cw…`, `bt…`, `clr j`, `clr' j`): each reaches the next loop head or halts (a decrement
  of a zero counter is stuck), and loop heads reach the next phase (drain lemma), ending at `gate
  start`; then `gate_halts_or_restart`.  `run s`: one `U₂` step to `gate s'` or halt.  `sp₁ s`,
  `sp₂ s`: to `run s` or halt.  `gate s`: `gate_halts_or_restart`.
* **`halts_of_steady`** (80).  `U₂` halts from `honest …` in `n` steps (`StepsN.of_reaches`).
  Strong induction on `n − t`: `reaches_round` to `gate start` with budget `t + 1`.  If `n ≤ t`:
  run `n` steps (`reaches_gated`) to a stuck `U₂` configuration with a token left
  (`halts_of_stuck_gate`).  Else the first `t + 1` steps of the run (a prefix of the halting run,
  by determinism `u₂_det` — use `StepsN` splitting) end at some `gate s` with budget `0`:
  `step_gate_zero` to `clr 0` with `acfg v' x 0 0 (t + 1)`, and recurse.
* **`not_halts_of_not_halts`** (80).  Every `U₂` configuration reachable from `honest …` steps
  (`exists_forever_of_not_halts`, or directly from `¬ Halts`).  So from `clr 0` with `acfg v x 0
  0 t` the machine reaches (`TransGen`) `clr 0` with `acfg v' x 0 0 (t + 1)` (`reaches_round`, `t
  + 1` gated steps, `step_gate_zero`).  An infinite `TransGen` chain in a deterministic machine
  does not halt (`StepsN.of_transGen` + strong induction on the halting step count).

### Assembly (≈ 40 lines)

* **`exists_lab`** (15), **`exists_primeData`** (25).  Copy the constructions in
  `exists_valid_machine` (`Fintype.equivFin` labels `+ 1`; `Nat.nth Nat.Prime ∘ equivFin`,
  `N = ∑ p`).

**Rough total: 2,500-3,000 lines.**  Largest: the restart runs (`reaches_round`,
`halts_or_reaches_restart`), the computability plumbing, `glueH_mortal_iff`.
