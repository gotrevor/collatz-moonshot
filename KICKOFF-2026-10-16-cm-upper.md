# KICKOFF 2026-10-16: the upper half, `UndecidableCM → HaltingUndecidable`; Theorem C same-orbit hypothesis-free

Repo `collatz-moonshot-amusical-round2` (branch `wip/cm-upper`): close every `sorry` in
`CollatzMoonshot/RcwaHalting.lean` (35 lemmas).  It imports `RcwaSameOrbit.lean` (proved, PR
#46), `RcwaMachine.lean` (proved, PR #45) and `CounterMachineUniversal.lean` /
`CounterMachine.lean` (statements, closed in parallel under `KICKOFF-2026-10-16-cm-format-lower.md`;
use their statements freely).  Do not edit any of those files.  The last two theorems,
`haltingUndecidable` and `not_computable_sameCycle'`, are already one-line proofs; they become
sorry-free when everything upstream is.

Sources: research note `~/personal/tmp/amusical-agents/out/undec-lemma.md` (§3 Lemma D, §4
Lemma M, §5 Lemma H, §6 Lemma G); Morita, *Theory of Reversible Computing* (2017) §9.2 (Lemma 9.3
history, Lemma 9.7 Gödel compile; extracted text `~/personal/tmp/ren-morita/ch9-2.txt`);
Kari–Ollinger, MFCS 2008 (Thm 3 doubling).  Our constructions differ from Morita's in three
load-bearing ways, each needed on *garbage* configurations: the history records **every** step
(`hist ↦ K · hist + lab ρ`), merges are separated by a re-test, and every Gödel boundary state
is guarded by `x ≥ 1, y = 0`.

## Ratified, do not change

Every definition and theorem statement in `RcwaHalting.lean`: `LapsMixed`, `HCtr`, `HState`,
`HRule`, `histWrap`, `hcfg`, `GState`, `MoveRule`, `GRule`, `godel`, `genc`, `PrimeData`,
`testOf`, `toRule`, `opFiresPat`, `turnRules`, `double`, `dcfg`; theorems
`wellQuasiOrderedLE_pi`, `revMortal_of_macro`, `macroStep_transGen`, `macroStep_functional`,
`histWrap_det`, `histWrap_rev`, `histWrap_normalAt`, `histWrap_lapsMixed`, `histWrap_macro`,
`histWrap_halts_of_stuck`, `histWrap_macro_hist`, `histWrap_revMortal`, `histWrap_halts_iff`,
`genc_inj`, `godel_det`, `godel_rev`, `godel_normalAt`, `godel_lapsMixed`, `godel_macro`,
`godel_halts_of_stuck`, `godel_macro_sound`, `godel_revMortal`, `godel_halts_iff`,
`double_deterministic`, `double_reversible`, `double_step_fwd`, `double_step_turn`,
`double_step_bwd`, `double_isSink_bwd`, `double_isSource`, `double_valid`, `double_halts_iff`,
`genc_hcfg_single`, `exists_valid_machine`, `haltingUndecidable_of_undecidableCM`,
`haltingUndecidable`, `not_computable_sameCycle'`.

No `native_decide`, no axioms, no `maxHeartbeats` bumps in statements.  Lean lines ≤ 100
characters.  Do **not** edit `RESEARCH-*.md`.  Commit after each proved lemma.  Notes as you go
in `HANDOFF-cm-upper.md`.  Helper lemmas and definitions are welcome (put them above their first
use).  Any cleaner route is fine as long as the ratified statements are unchanged.  Order of
attack: §4 (doubling, independent of §2-§3) and §1 first, then §2, §3, §5.

**Truth checks already run** (`tmp/drafter/cm_check.py`, a Python mirror of `histWrap`, `godel`,
`double`; output `tmp/drafter/cm_check.out`).  On a 9-rule irreversible 2-counter `U` (normal at
`q0`; halts on even inputs, diverges on odd): `histWrap` (214 states) Morita-deterministic and
reversible, 16 off-boundary cycles all mixed, macro formula `hist ↦ K · hist + lab ρ` on 336
boundary configurations (garbage counters included), no backward cycle and every backward run
finite on 25,680 configurations of *all* states.  `godel` of Morita's Example 9.4 (RCM(3)) and of
`histWrap U` (4,568 states): Morita-deterministic and reversible, all 424 off-boundary cycles
mixed, macro step = `B` step on 3,424 encodings with junk `1` and `11`, no backward cycle and
every backward run finite on 1,096,320 configurations (`x < 40`, `y < 6`, every state).
`double` (K = 9,136, guarded-rule semantics of `RcwaSameOrbit`): deterministic, reversible,
`pair_sink`, `EndToStart` on a box; end-to-end on a 2-rule `U` (halts at `n = 0`, diverges for
`n ≥ 1`).  **Teeth** (each fails as it must): no re-test in `histWrap` (9 Morita-reversibility
violations), no `x ≥ 1` guard in `godel` (760 backward cycles on garbage), a wrong restore prime
(faithfulness fails), turnarounds on every pattern (`Reversible` fails).

## Paper proofs (Ren)

Conventions.  `B` = boundary set; `MacroStep` = `RcwaMachine.MacroStep`.  A closed walk "off
`B`" is the hypothesis shape of `LapsMixed`.  For case bashes over `HRule`/`GRule` pairs:
`cases h₁ <;> cases h₂` then `simp_all`/`omega`; most of the `15² / 30²` pairs die on
`HState`/`GState` constructor mismatch in `src` (or `dst`).  `Op.delta` helper: `o.Act v w →
∀ j, (w j : ℤ) = v j + o.delta j` (prove once, by `cases o`).

### §1 Lemma M for counter machines (≈ 150 lines)

* **`wellQuasiOrderedLE_pi`** (30).  Transfer `Finsupp.wellQuasiOrderedLE` along
  `Finsupp.equivFunOnFinite` (order-preserving both ways: `Finsupp.le_def`); or induct on
  `Fintype.card` with the `Prod` instance (`WellQuasiOrder.lean:185`) and `Fin.consEquiv`.
* **`revMortal_of_macro`** (70).  `RevMortal M` is literally `¬` the left side of
  `RcwaMachine.reverse_immortal_iff_macro B M.Step hlap'` (with `V := ι → ℕ`, instance from
  `wellQuasiOrderedLE_pi`), so it suffices to prove `LapNotDown B M.Step` from `LapsMixed`.  As
  in `RcwaMachine.TwoCounter.lap_mixed`: given an off-`B` run `x m → … → x n` returning to its
  state, choose a rule `ρ i` for each step (`choose`), check the chaining hypotheses, and
  telescope with the `delta` helper: `∑ i < n - m, (ρ i).op.delta j = (x n).2 j - (x m).2 j`.
  The positive entry `j` gives `(x m).2 j < (x n).2 j`, refuting `(x n).2 ≤ (x m).2`.
* **`macroStep_transGen`** (15).  Induction on the witness length `n`.
* **`macroStep_functional`** (40).  Two witnesses `x, n` and `y, n'` from `b`; by
  `step_functional`, `x i = y i` for `i ≤ min n n'` (induction).  If `n < n'`, then `y n = x n`
  has state in `B` with `0 < n < n'`, contradicting the off-`B` clause of `y`; symmetric.

### §2 History wrapper (Lemma H) (≈ 700 lines)

Picture: from `bnd s` with `work = 0` go to `act s`, do `U`'s operation of rule `ρ` on the `val`
counters into `pre ρ`, re-test `work = 0` into `tr ρ`, move `hist` into `work` (loop `tr → tr₁
(hist−) → tr₂ (work+) → tr₃ (work P) → tr`), exit at `hist = 0` into the wheel `wh ρ.dst (lab
ρ)`.  The wheel `wh j (j ≥ 1) → wa j (hist+) → wh (j−1)` adds `j`; at `wh 0`, `work = 0` exits to
`bnd`, else `wb (work−) → wc (hist+) → wd → wh (K−1)` adds `K` per unit of `work`.  Net:
`(bnd s, v, h, 0) ⇒ (bnd ρ.dst, v', K·h + lab ρ, 0)`.

* **`histWrap_det`** (100).  By source: `bnd s` has only `guard` rules, all equal; `act s` has
  `op ρ` for `ρ` with source `s`, distinct `ρ` give distinct rules and `U.Det` makes them
  `test (val i)` with different symbols (`Op.map`); `tr ρ`: `trZ`/`trP`, `hist` tests; `wh s 0`:
  `whZ`/`whP` (`whInc` needs `1 ≤ j`); `wh s j`, `j ≥ 1`: only `whInc`; `wd s`: the `t` with
  `t + 1 = K` is unique (`Fin.ext`); the rest have one rule.
* **`histWrap_rev`** (130).  By destination: `bnd s ← wh s 0` only; `act s ← bnd s`; `pre ρ ← act
  ρ.src` (indexed by `ρ`); `tr ρ ← pre ρ (work Z), tr₃ ρ (work P)`; `wh s j ← tr ρ (hist Z, for
  the unique `ρ ∈ U` with `ρ.dst = s` and `lab ρ = j`: `hinj`), `wa s (j+1) (hist P)` if
  `j + 1 < K`, `wd s (hist P)` if `j + 1 = K`; `lab ρ ≥ 1` (`hlab`) keeps `trZ` out of `wh s 0`
  except through these.  Everything else has one rule in.
* **`histWrap_normalAt`** (10).  Only `whZ` enters a `bnd`, and needs `ρ ∈ U` with `ρ.dst = q₀`.
* **`histWrap_lapsMixed`** (200).  *Rank:* `act 0`, `pre 1`, `tr/tr₁/tr₂/tr₃ 2`, wheel states
  `3`.  Every rule off `bnd` keeps the rank (inside a *family*: the transfer of one `ρ`, or the
  wheel of one `s`) or raises it; a closed walk returns to its start, so all its rules are
  intra-family and (family index is preserved) in one family; `whZ` enters `bnd`, which the walk
  never visits.  *Flow:* inside a family every state has exactly one rule in and one rule out,
  so in a closed walk every family state is the source of the same number `c ≥ 1` of walk
  steps (count entries = exits at each state; `m ≥ 1`).  Transfer: lap `hist −c`, `work +c`.
  Wheel: lap `work −c`, `hist +K c` (`wc` once and `whInc` at `j = 1 … K−1` once per lap).
* **`histWrap_macro`** (120).  Build the run: guard, op (`hact`), re-test; transfer loop by
  induction on `h` (`(tr ρ, v', h−t, t) →* (tr ρ, v', 0, h)`); `trZ`; entry descent `wh j → wh 0`
  by induction on `j` (adds `j = lab ρ`); laps by induction on `work`.  None of these states is
  a `bnd` until the final `whZ`.  Helper: a `MacroStep` from `Relation.TransGen` of the step
  relation restricted to non-`B` targets, followed by one step into `B`.
* **`histWrap_halts_of_stuck`** (30).  If no rule of `U` leaves `s`, `bnd s` is stuck.
  Otherwise `guard` reaches `act s` (`work = 0`), whose rules are the `op ρ`, none of which fires
  (`U.Stuck`, `Op.map`).
* **`histWrap_macro_hist`** (60).  `b = (bnd s, w)`.  The only rule from `bnd s` needs `w work =
  0`, so `w = hcfg v h` with `v = w ∘ val`, `h = w hist`.  `act s` must fire some `op ρ` (else no
  macro step): `U.Step (s, v) (ρ.dst, v')`, and `histWrap_macro` is a macro step to `(bnd ρ.dst,
  hcfg v' (K h + lab ρ))`; `macroStep_functional` (`histWrap_det`) makes `b'` that.  `K ≥ 1`
  (`lab ρ : Fin K`) and `lab ρ ≥ 1` give `h < K h + lab ρ`.
* **`histWrap_revMortal`** (20).  `revMortal_of_macro` with `histWrap_lapsMixed`; an infinite
  backward macro chain `b` has `(b (n+1)).2 hist < (b n).2 hist` for all `n`, impossible in `ℕ`
  (`(b n).2 hist + n ≤ (b 0).2 hist` by induction).  The `Fintype` instances of `HState` and
  `HCtr` are derived.
* **`histWrap_halts_iff`** (25).  `CM.halts_iff_of_sim` with `Sim (s, v) b := ∃ h, b = (bnd s,
  hcfg v h)`, `hstep` from `histWrap_macro` and `macroStep_transGen` (pick the rule from
  `U.Step`), `hstuck` from `histWrap_halts_of_stuck`, determinism `histWrap_det`.

### §3 Gödel compile (Lemma G) (≈ 900 lines)

Picture (counter `0` = `x`, `1` = `y`; `p := p i` for the counter `i` of `q`'s rules):
`ent q (x P) → grd q (y Z) →` gadget.  `nop`: straight to `ent q'`.  Move: `a₁ (x Z → b₁; x P →
a₂ (x−) → a₃ (y+) → a₄ (y P) → a₁)` moves `x` into `y`; then `b₁ (y Z → ent q')`, increment: `b₁
(y P) → b₂ (y−) → mul 1 … mul p (x+ each) → b₃ (x P) → b₁` (`x := p y`); decrement: `b₁ (y P) →
dv 1 … dv p (y− each) → b₂ (x+) → b₃ → b₁` (`x := y / p`; stuck inside `dv` if `p ∤ y`).
Test: `w₁ j (x P) → w₂ j (x−) → w₁ (j+1)` for `j < p`, `w₁ p (y+) → w₂ p (y P) → w₁ 0` divides
`x` by `p` into `y` with remainder `j`; at `x = 0`, `w₁ 0` exits to `r₁ q' 0` for a `P` rule,
`w₁ j` (`1 ≤ j < p`) to `r₁ q' j` for a `Z` rule.  Restore at target `s`: `r₁ j (x+) → r₂ j (x P)
→ r₁ (j−1)` adds `j`, then `r₁ 0 (y P) → r₂ 0 (y−) → r₁ p` adds `p` per unit of `y`, and `r₁ 0
(y Z) → ent s`.

Arithmetic facts (one helper section, ≈ 80 lines): for `J > 0` coprime to every `p i`,
`p i ∣ J * ∏ p ^ v ↔ 1 ≤ v i` (`Nat.Prime.dvd_mul`, `Nat.Prime.dvd_of_dvd_pow`,
`(Nat.prime_dvd_prime_iff_eq _ _).1`, `hp.inj`); `∏ p ^ (update v i (v i + 1)) = p i * ∏ p ^ v`
(`Finset.prod_update_of_mem` or `Finset.mul_prod_erase`); every `x ≥ 1` is `J * ∏ p ^ v` with
`v i = x.factorization (p i)` and `J` coprime (`Nat.ordProj_dvd`, `Nat.ordCompl`, iterate over
`Finset.univ`, or `Nat.factorization_prod_pow_eq_self` restricted).

* **`genc_inj`** (40).  Evaluate `Nat.factorization` at `p i`: `v i = v' i`; cancel the product.
* **`godel_det`** (150).  By source, as in `histWrap_det`.  `B.Det`: `q` has one move rule, or
  tests of one counter `i` (so all `w`-gadget indices use the same `p i`), or `nop`.  `B.Rev`:
  the tests into `s` use one counter, so `r₂ s 0`'s `rDec` target is unique.  Index side
  conditions (`j.val < p i` vs `= p i`, `1 ≤ j` vs `= 0`) separate the rest; `PrimeData.le`
  isn't needed here, `2 ≤ p i` (prime) is.
* **`godel_rev`** (200).  By destination.  `ent s ← grd q (nop) | b₁ q (y Z) | r₁ s 0 (y Z)`:
  `B.Rev` says the rules of `B` into `s` are one move/nop rule, or tests (`rZ` only, all equal).
  `a₁ q ← grd q (y Z), a₄ q (y P)`; `b₁ q ← a₁ q (x Z), b₃ q (x P)`; `w₁ q 0 ← grd q (y Z),
  w₂ q p (y P)`; `r₁ s 0 ← r₂ s 1 (x P), w₁ q 0 (x Z, the unique `P`-rule into `s`)`; `r₁ s j`
  (`1 ≤ j < p`) `← r₂ s (j+1) (x P), w₁ q j (x Z, the unique `Z`-rule into `s`)`; `r₁ s p ← r₂ s 0`
  only; all others one rule.
* **`godel_normalAt`** (15).  Rules into `ent s` (`nop`, `b₁Z`, `rZ`) each need a rule of `B`
  into `s`.
* **`godel_lapsMixed`** (250).  As `histWrap_lapsMixed`.  Rank `grd 0`, `a 1`, `w 1`, `b/mul/dv
  2`, `r 3`; exits `a₁ → b₁`, `w₁ → r₁` raise it, `→ ent` leaves the walk.  Families: the
  `a`-loop of `q` (lap `x −c, y +c`), the `b`-loop of `q` (increment: `y −c, x +p c`;
  decrement: `y −p c, x +c`), the `w`-wheel of `q` (`x −p c, y +c`), the `r`-wheel of `s` (`y −c,
  x +p c`); one rule in and one out per family state (`B.Det`, `B.Rev` fix the family's prime).
* **`godel_macro`** (220).  Explicit runs, case on the rule of `B` behind `hstep` (unique by
  `B.Det`).  Loops by induction: transfer `x → y`; multiply (`mul` chain adds `p` per lap);
  divide (`v i ≥ 1` so `p ∣ y`: write `y = p y'`); wheel (`x = p a + j`, `j < p`, `a` laps then
  `j` single steps; `j = 0 ↔ v i ≥ 1`); restore (`j` increments then `a` laps).  All
  intermediate states are not `ent`.
* **`godel_halts_of_stuck`** (80).  `B.Stuck (q, v)`: no rule from `q` (stuck at `grd q`);
  a decrement with `v i = 0` (the `dv` chain gets stuck: `y = x` not divisible by `p`); tests with
  the missing branch (`w₁ j` with `x = 0` has only the `x P` rule).
* **`godel_macro_sound`** (100).  The first step is `guard` (`x ≥ 1`), the second a `y Z` test
  (`y = 0`; if `q` has no rule there is no second step).  Factor `x = J * ∏ p ^ v` with `J`
  coprime.  If `B` steps from `(q, v)`, `godel_macro` plus `macroStep_functional` (`godel_det`)
  identifies `b'`.  If `B` is stuck at `(q, v)`, the run of `godel_halts_of_stuck` is the unique
  run and reaches a stuck configuration before any `ent` (prove the stuck-run lemma with "no
  `ent` before the end" built in), so no macro step exists.
* **`godel_revMortal`** (60).  `revMortal_of_macro` with `godel_lapsMixed`.  Given an infinite
  backward macro chain `b`, `godel_macro_sound` at `b (n+1) → b n` decodes both ends; `genc_inj`
  makes the decodings of `b n` from the two adjacent macro steps agree (same `q` by the `ent`
  index, same `v` and `J`).  So `n ↦ (q_{n+1}, v_{n+1})` is an infinite backward chain of `B`,
  against `hmort`.
* **`godel_halts_iff`** (20).  `CM.halts_iff_of_sim` with `Sim c b := b = (ent c.1, genc p 1
  c.2)` (`J = 1`: positive, coprime to primes), `godel_macro` + `macroStep_transGen`,
  `godel_halts_of_stuck`, `godel_det`.

### §4 Doubling (Lemma D) (≈ 700 lines)

Facts first (helpers): with `n` injective, `Rule.Fires (toRule n ρ) (n q, a, b) ↔ ρ.src = q ∧ ∃ w,
ρ.op.Act ![a, b] w`, and then `Rule.target` is `(n ρ.dst, w 0, w 1)`; `opFiresPat ρ.op (0 < a) (0
< b) = true ↔ ∃ w, ρ.op.Act ![a, b] w`; `ρ.inv` fires at `w` iff `ρ` maps some `u` to `w`
(`Op.act_inv`).  Write `c₊ := dcfg e true c`, `c₋ := dcfg e false c`.  Every state `< K` is
`e (q, b)`; states `≥ K` appear in no rule.

* **`double_deterministic`** (100).  At `c₊`: rules of `R` from `c.1` (`R.Det`: equal or
  disjoint tests) and turnarounds (only where no rule fires, one per pattern).  At `c₋`: inverse
  rules of rules *into* `c.1` (`R.Rev`: equal or disjoint tests).  Mixed pairs have disjoint
  domains.
* **`double_reversible`** (150).  Same target in layer `+`: two rules of `R` into one
  configuration, `CM.step_injective` (`R.Rev`) gives equal sources.  Layer `−`, two inverse
  rules: their targets lie in the domains of two rules of `R` from one state, `R.Det` makes them
  one rule, then injectivity.  Inverse rule vs turnaround: the turnaround target lies where no
  rule of `R` from that state fires, the inverse rule's target where one does.  Two turnarounds:
  one pattern per target.
* **`double_step_fwd`, `double_step_turn`, `double_step_bwd`** (30 each).
  `RcwaSameOrbit.step_eq_of_fires` with `double_deterministic`, exhibiting the firing rule.
* **`double_isSink_bwd`** (40).  Rules from `c₋` are inverse rules; one fires iff `c` has an
  `R`-predecessor.
* **`double_isSource`** (40).  Only rules of `R` (layer `+`) enter layer `+`.
* **`double_valid`** (250).
  * `WF`: all states are `e _ < K`; `pair` is `(List.finRange K).map σ` with `σ` the layer swap,
    a bijection of `Fin K`, so a permutation of `List.range K` (`List.Perm`, e.g. via
    `List.perm_of_nodup_nodup_toFinset_eq` and `List.nodup_finRange`).  `pairFn (e (q, b)) =
    e (q, !b)`, `pairFn s = s` for `s ≥ K` (`List.getD`).
  * `rev`: `double_reversible`.
  * `pair_sink`: states `≥ K` are sinks and sources and `pairFn` fixes them.  `c₊` is never a
    sink (`double_step_fwd` or `double_step_turn`), and `c₋` is never a source (its predecessor
    is `d₋` with `R.Step c d`, or `c₊` by the turnaround).  `c₋` is a sink iff `R.IsSource c`
    iff `c₊` is a source (`double_isSink_bwd`, `double_isSource` and its converse).
  * `noBiInfinite`: along a bi-infinite chain all states are `< K`; layer `−` only steps to
    layer `−`.  If some index is in layer `−`, the tail from it is a forward chain of inverse
    steps, i.e. an infinite backward chain of `R` (`double_step_bwd` read backward via
    determinism), against `hmort`.  Otherwise all indices are layer `+` with no turnaround, and
    `i ↦ g (−i)` gives an infinite backward chain of `R`.
  * `endToStart`: a source `c` with state `≥ K` has `n = 0`, `d = c`.  A source `c₊` has
    `R.IsSource c`; the run is the `R`-run (layer `+`) up to the first `R`-halting `t` at step
    `m`, the turnaround, then the inverse run back, reaching `c₋` at step `2m + 1` (induction
    on `m` with `double_step_bwd`; the inverse run retraces by `R.Rev`).  Configurations before
    step `2m + 1` are not sinks (`+` never; `−` ones have `R`-predecessors), and the run is
    `none` after a sink, so `d = c₋` and `(pairFn d.1, d.2) = c`.  If the `R`-run never halts the
    run never reaches a sink.  No source starts in layer `−`.
* **`double_halts_iff`** (60).  (←) as in `endToStart`.  (→) If `R` does not halt from `c`, its
  run is infinite (`¬ Halts` + choice), so the layer-`+` run of the doubling is infinite and
  never a sink.

### §5 Assembly (≈ 200 lines)

* **`genc_hcfg_single`** (15).  `Fintype.prod_eq_single (.val i₀)`: off `val i₀` the exponent is
  `0` (`Pi.single_eq_of_ne`, `hcfg`); `1 * _`; `Matrix.cons` extensionality.
* **`exists_valid_machine`** (120).  `classical`; `Fintype Q`, `Fintype ι` from `Finite`.
  Labels: `lab ρ := ⟨Fintype.equivFin _ ρ + 1, _⟩ : Fin (Fintype.card (Quad Q ι) + 1)` (all `≥
  1`, injective).  Primes: `p c := Nat.nth Nat.Prime (Fintype.equivFin (HCtr ι) c)` (prime:
  `Nat.prime_nth_prime`; injective: `Nat.nth_injective` with `Nat.infinite_setOf_prime`),
  `N := ∑ c, p c` (or `Finset.sup`).  `B := histWrap U lab`, `R := godel B p N`, `rs :=
  (Finset.univ.filter (· ∈ R)).toList`, `e := Fintype.equivFin (GState _ N × Bool)`,
  `M := double rs e`, `s₀ := (e (.ent (.bnd q₀), true)).val`, `P := p (.val i₀)`.  `Valid`:
  `double_valid` from `godel_det`, `godel_rev`, `godel_revMortal` from `histWrap_det`,
  `histWrap_rev`, `histWrap_revMortal`.  `s₀ < K`: `Fin.isLt`.  For each `n`: the input is
  `dcfg e true (.ent (.bnd q₀), genc p 1 (hcfg (Pi.single i₀ n) 0))` (`genc_hcfg_single`); it is
  an `R`-source (`isSource_of_normalAt`, `godel_normalAt`, `histWrap_normalAt`), so
  `double_isSource`; halting via `double_halts_iff`, `godel_halts_iff`, `histWrap_halts_iff`.
* **`haltingUndecidable_of_undecidableCM`** (40).  `obtain ⟨Q, ι, _, _, U, q₀, i₀, enc, hU, hq₀,
  henc, hnot⟩ := h`; `classical`; `exists_valid_machine hU hq₀ i₀` gives `M, s₀, P`.  Given a
  decider `g`, `g' n := g (M, s₀, P ^ enc n, 0)` is computable (`Computable.pair`,
  `Computable.const`, `Primrec.nat_pow`/`RcwaSameOrbit.PrimInt.nat_pow` composed with `henc`),
  and `g' n = true ↔ U.Halts (q₀, Pi.single i₀ (enc n))`.  So `ComputablePred` (instance
  `Classical.decPred`, `Computable` of `decide` by `of_eq` with `Bool.eq_iff_iff`), against
  `hnot`.  Watch the `DecidableEq ι` instances (`Pi.single` in `UndecidableCM` is classical):
  `Subsingleton.elim` / `convert`.
* `haltingUndecidable`, `not_computable_sameCycle'`: already proved from the above.

Rough total: 2,500-3,500 lines.  Largest: the `godel` case bashes and runs (§3), then
`double_valid`.
