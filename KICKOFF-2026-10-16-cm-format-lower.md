# KICKOFF 2026-10-16: counter-machine format and the lower half (Mathlib halting → `UndecidableCM`)

Repo `collatz-moonshot-amusical-zcore` (branch `wip/cm-halting`): close every `sorry` in
`CollatzMoonshot/CounterMachine.lean` (the shared format, 11 lemmas) and
`CollatzMoonshot/CounterMachineUniversal.lean` (the lower half, 15 lemmas).  The upper half
(`RcwaHalting.lean`, `UndecidableCM → HaltingUndecidable`) has its own kickoff
(`KICKOFF-2026-10-16-cm-upper.md`) and can run in parallel: it only uses the statements here.
Sources: Morita, *Theory of Reversible Computing* (2017) §9.2 (Defs 9.1-9.4), Mathlib
`Computability/Halting.lean`, `TuringMachine/ToPartrec.lean`, `TuringMachine/Config.lean`,
`TuringMachine/StackTuringMachine.lean`, `StateTransition.lean`.

## Ratified, do not change

Every definition and theorem statement in both files.

* `CounterMachine.lean`: `Op` (`map`, `inv`, `Act`, `delta`), `Quad`, `Quad.inv`, `Cfg`, `CM`,
  `CM.Step`, `CM.Reaches`, `CM.Stuck`, `CM.Halts`, `CM.IsSource`, `CM.Det`, `CM.Rev`,
  `CM.NormalAt`, `CM.RevMortal`, `CM.restrict`, `UndecidableCM`; theorems `Op.act_functional`,
  `Op.act_injective`, `Op.act_inv`, `CM.step_functional`, `CM.step_injective`,
  `CM.isSource_of_normalAt`, `CM.not_halts_of_forever`, `CM.halts_iff_of_sim`,
  `CM.restrict_det`, `CM.restrict_normalAt`, `CM.halts_restrict`.
* `CounterMachineUniversal.lean`: the `Fintype K'` instance, `digitF`, `digit`, `undigit`, `num`,
  `stackVec`, `inputNum`, `Phase`, `LState`, `LCtr`, `divRules`, `backRules`, `gadget`, `lcm`,
  `repCfg`, `reachSet`; theorems `exists_universal`, `not_computable_universal`, `undigit_num`,
  `num_div_five`, `num_cons`, `stackVec_init`, `computable_inputNum`, `det_lcm`,
  `normalAt_lcm`, `stepAux_reaches`, `stuck_halt`, `halts_iff_eval`, `reachSet_finite`,
  `reachSet_closed`, `undecidableCM`.

No `native_decide`, no axioms, no `maxHeartbeats` bumps in statements.  Lean lines ≤ 100
characters.  Do **not** edit `RESEARCH-*.md`.  Commit after each proved lemma.  Notes as you go
in `HANDOFF-cm-format-lower.md`.  Helper lemmas and definitions are welcome (put them above
their first use).  Any cleaner route is fine as long as the ratified statements are unchanged.
Order of attack: `CounterMachine.lean` first (everything downstream uses it), then
`CounterMachineUniversal` §2 (numerals), §1 (universal code), §3-§4 (the compile, the bulk),
§5 last.

**Truth checks already run** (`tmp/drafter/lcm_check.py`, a Python mirror of `gadget`): every
push/pop/peek gadget is Morita-deterministic and computes `5n + digit a`, `(n / 5, n % 5)`,
`(n, n % 5)` on all 8,190 stacks of length ≤ 5; a broken push (4 increments per lap) fails.

## Paper proofs (Ren)

Notation: `Op.Act` is Morita's ID relation (Def 9.3) for one operation; a decrement fires only
from a positive counter.  Distinct counters are untouched (`∀ j ≠ i, w j = v j`), so prove
pointwise and `funext`.

### `CounterMachine.lean` (≈ 250 lines)

* **`Op.act_functional`, `Op.act_injective`** (10 each).  `cases o`; tests and `nop` force
  `w = v`; for `dec i`/`inc i` compare at `i` (`omega`) and off `i` (the frame clause).
* **`Op.act_inv`** (15).  `cases o`; `test` is self-inverse (`w = v` both ways), `dec`/`inc`
  swap (`0 < v i` comes from `v i = w i + 1`).
* **`step_functional`** (15).  Two rules `ρ, ρ'` fire at `c`.  If `ρ = ρ'`, `act_functional`
  and the shared `dst`.  If not, `Det` makes them `test i b`, `test i b'` with `b ≠ b'`; both
  `Act`s say `decide (0 < c.2 i) = b` and `= b'`.  Contradiction.
* **`step_injective`** (15).  Same with `Rev`, `act_injective` and the shared `src`; distinct
  tests give `d.2 = c.2 = c'.2` and then `b = b'`.
* **`isSource_of_normalAt`** (5).  A step into `(q₀, v)` has a rule with `dst = q₀`.
* **`not_halts_of_forever`** (20).  `Halts (x 0)` gives `d` with `ReflTransGen` and `Stuck d`.
  By induction on the `ReflTransGen` (from the head) and `step_functional`, `d = x n` for some
  `n`; but `Step (x n) (x (n+1))`.
* **`halts_iff_of_sim`** (60).  (←) Induct on `M.Reaches c z` from the head, carrying `Sim`
  (each `M` step becomes a `TransGen` of `M'`); at the end `hstuck`.  (→) Suppose `M'` halts at
  a stuck `d'` with `M'.Reaches c' d'` in `k` steps.  Strong induction on `k` with the claim
  "`Sim c c'` and `¬ M.Halts c` is impossible".  `¬ M.Halts c` gives `c` a successor `d` (else
  `c` is stuck and halts) and `¬ M.Halts d`; `hstep` gives `c' →⁺ e'` with `Sim d e'`.  Under
  `hdet` two runs from `c'` are prefixes of each other; since `d'` is stuck, the run `c' →⁺ e'`
  does not pass `d'` strictly, so `e' →* d'` in fewer than `k` steps.  A counted step relation
  (`Relation.ReflTransGen` ↔ `∃ n, Relation.iterate`… or your own `StepN`) keeps this clean.
* **`restrict_det`** (15).  A restricted rule `ρ` lifts to `⟨ρ.src.1, ρ.op, ρ.dst.1⟩ ∈ M`;
  distinct restricted rules with the same source lift to distinct rules (`Subtype.ext`).
* **`restrict_normalAt`** (5).
* **`halts_restrict`** (50).  For `c` with `c.1 ∈ S`: `(M.restrict S).Step c d ↔ M.Step (lift
  c) (lift d)`, and every `M`-successor of a configuration in `S` is in `S` (`hS`).  Transport
  `Reaches` both ways by induction, and `Stuck` likewise.

### `CounterMachineUniversal.lean`

**§1 Universal code (≈ 35 lines).**

* **`exists_universal`** (20).  Put `f₀ n := Nat.Partrec.Code.eval (Denumerable.ofNat _ n) 0`;
  `Partrec f₀` from `Nat.Partrec.Code.eval_part.comp (Computable.ofNat _) (Computable.const 0)`.
  `Nat.Partrec'.part_iff₁` turns it into `Nat.Partrec' (fun v : List.Vector ℕ 1 => f₀ v.head)`;
  `Turing.ToPartrec.Code.exists_code` gives `u` with `u.eval v.1 = pure <$> f₀ v.head`.  At
  `v = ⟨[n], rfl⟩`, `Part.dom` of `pure <$> _` is the domain.
* **`not_computable_universal`** (15).  A decider for `n ↦ (u.eval [n]).Dom` composed with
  `Computable.encode` decides `c ↦ (eval c 0).Dom` (`Denumerable.ofNat_encode`), contradicting
  `ComputablePred.halting_problem 0`.

**§2 Numerals (≈ 120 lines).**  `num (a :: l) = digit a + 5 · num l` with `1 ≤ digit a ≤ 4`.

* **`num_cons`** (2), **`num_div_five`** (8: `Nat.add_mul_div_left`, `digit a < 5`),
  **`undigit_num`** (10: `num l % 5 = 0` iff `l = []`, else `= digit a`; `cases a <;> rfl`).
* **`stackVec_init`** (8).  `funext`; `none ↦ 0`; `some k`: `cases k`, `K'.elim` and
  `Pi.single` simp lemmas.
* **`computable_inputNum`** (80).  `inputNum n = num (trNat n ++ [cons])`.  First
  `trNat n = (if n % 2 = 1 then bit1 else bit0) :: trNat (n / 2)` for `n ≠ 0` (via
  `trNum`/`trPosNum` and `Num.ofNat'` bit lemmas; `trNat 0 = []`).  So `I n := inputNum n` has
  `I 0 = 2` and `I n = (3 or 4) + 5 · I (n / 2)`.  Get `Primrec I` from
  `Primrec.nat_strong_rec` (`Primrec/List.lean`) with `α := Unit` and
  `g _ l := some (if l.length = 0 then 2 else d (l.length) + 5 * l.getD (l.length / 2) 0)`, where
  `d n = 3 + n % 2`; then `Primrec.to_comp`.

**§3 The compile (≈ 250 lines).**

* **`det_lcm`** (150-250, the case bash).  Helper: every rule of `gadget s v` has source
  `stmt s v` or `gad s v ph`, so two rules with one source come from one `gadget s v` (or are
  both the start rule).  Then per constructor of `s`, list the rules by source: `pa`, `pd`,
  `da j`, `db r` have exactly two rules, tests of one counter with `false`/`true`; every other
  source has one rule (`pg j`: increment iff `j < d`, `nop` iff `j = d`; `dg r j` likewise;
  `pe j`, `df r j` by index).  Tactics: `simp [gadget, divRules, backRules, List.mem_flatMap,
  List.mem_map, List.mem_filter]` then `fin_cases`/`omega` on `Fin` indices.
* **`normalAt_lcm`** (10).  No rule has destination `start`.

**§4 Simulation (≈ 400 lines, the bulk).**

* **Loop lemmas** (helpers, induction on the counter): with `w` the counters,
  * push move: `(gad pa, k = n, tmp = t) →* (gad pd, k = 0, tmp = t + n)`;
  * push return: `(gad pd, k = a, tmp = t) →* (gad (pg 0), k = a + 5 t, tmp = 0)`;
  * divide: `(gad (da j), k = n, tmp = t) →* (gad (db r), k = 0, tmp = t + (j + n) / 5)` with
    `r = (j + n) % 5`, for `j < 5`;
  * pop return (`e = 5`): `(gad (db r), k = a, tmp = t) →* (gad (db r), k = a + t, tmp = 0)`;
    peek return (`e = 1`): `k = a + 5 t`; then `db r` with `tmp = 0` exits;
  * digit/remainder adds: `pg j → pg d` and `dg r j → dg r r` add `d - j`, `r - j`.
  Counters as `Function.update` of `stackVec S`; `stackVec (update S k l) = update (stackVec S)
  (some k) (num l)` (helper).
* **`stepAux_reaches`** (150).  Induction on `s` (`TM2.Stmt` recursor).  `push k f q`: the push
  gadget lands on `stmt q v` with stack `k` equal to `num (f v :: S k)` (`num_cons`), then the
  IH for `q` at `update S k (f v :: S k)` (`stepAux` simp lemma `TM2.stepAux.eq_1`).  `pop`:
  `undigit (num (S k) % 5) = (S k).head?` (`undigit_num`), counter `num (S k) / 5 =
  num (S k).tail` (`num_div_five`).  `peek`: same remainder, stack restored.  `load`, `branch`
  (`cond` commutes with `stepAux`), `goto`: one `nop` (this is the `TransGen` case).  `halt`:
  zero steps, `isSome = false`.  Every nonempty case gives `TransGen` because its first rule is
  the `nop` out of `stmt s v`.
* **`stuck_halt`** (10).  `gadget halt v = []` and no other gadget has source `stmt halt v`.
* **`halts_iff_eval`** (80).  `TM2.step tr ⟨some l, v, S⟩ = some (stepAux (tr l) v S)` and
  `TM2.step tr ⟨none, _, _⟩ = none`.  (←) `StateTransition.mem_eval`: the TM2 run reaches
  `⟨none, v', S'⟩`; by induction along `StateTransition.Reaches` and `stepAux_reaches` the counter
  run reaches `repCfg ⟨none, v', S'⟩`, which is stuck (`stuck_halt`).  (→) Contrapositive: if the
  TM2 evaluation diverges, every reachable TM2 configuration is `⟨some l, …⟩` and steps to
  another `⟨some l', …⟩` (a `none` successor would make `eval` defined).  So `stepAux_reaches`
  gives `TransGen` between consecutive `repCfg`s; the infinite counter run and `det_lcm` give
  `¬ Halts` (as in `CM.not_halts_of_forever`; or apply `CM.halts_iff_of_sim`-style reasoning
  directly).  Alternative: Mathlib's `StateTransition.tr_eval_dom` with a choice-based step
  function for `lcm l₀`, using that `tr l` is never `halt` (`cases l`).

**§5 Finiteness and the interface (≈ 150 lines).**

* **`reachSet_finite`** (25).  `reachSet L ⊆ {start} ∪ stmt '' (S ×ˢ univ) ∪ gad '' (S ×ˢ univ
  ×ˢ univ)` with `S` the finite set of `s` with `some s ∈ TM2.stmts tr L`; `Set.Finite.image`,
  `Set.Finite.prod`, `Set.finite_univ` (`Option Γ'` and `Phase` are `Fintype`).
* **`reachSet_closed`** (80).  The start rule enters `stmt (tr l₀) none`, and `l₀ ∈ L` (first
  conjunct of `TM2.Supports`), so `some (tr l₀) ∈ TM2.stmts tr L` (`TM2.stmts₁_self`).  A gadget
  rule from `stmt s v` / `gad s v ph` enters `gad s v ph'` or `stmt q v'` with `q` a direct
  substatement of `s` (`TM2.stmts_trans` with `stmts₁`), or for `goto f` enters `stmt (tr (f v))
  v` with `f v ∈ L` (`TM2.stmts_supportsStmt hL` gives `SupportsStmt L (goto f)`).
* **`undecidableCM`** (50).  `obtain ⟨u, hu⟩ := exists_universal`; `L := codeSupp u
  Cont'.halt`, `l₀ := trNormal u Cont'.halt`, `hL := tr_supports u Cont'.halt`.  Take
  `Q := reachSet L` (finite by `reachSet_finite`, `Set.finite_coe_iff`), `ι := Option K'`,
  `M := (lcm l₀).restrict (reachSet L)`, `q₀ := ⟨.start, _⟩`, `i₀ := some K'.main`,
  `enc := inputNum`.  `Det`: `restrict_det (det_lcm _)`; normal form: `restrict_normalAt`;
  computability: `computable_inputNum`.  Halting: `halts_restrict (reachSet_closed hL)`, then
  `stackVec_init` (the two `DecidableEq (Option K')` instances agree: `Subsingleton.elim` or
  `convert`), `halts_iff_eval` at `S = K'.elim (trList [n]) [] [] []`, which is `init u [n]`,
  and `tr_eval` (`Part.dom` of `halt <$> _`).  So the predicate is `fun n => (u.eval [n]).Dom`,
  not computable by `not_computable_universal hu`.

Rough total: 1,100-1,500 lines.  The bulk is §4 (loop lemmas and `stepAux_reaches`) and
`det_lcm`.
