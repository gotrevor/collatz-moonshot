# KICKOFF 2026-10-16: Theorem C, orbit count (one orbit iff mortal, else infinitely many)

Repo `collatz-moonshot-rcwa-gen` (branch `wip/orbit-count`, based on the commit that makes Theorem
C's same-orbit part hypothesis-free).  Close every `sorry` in `CollatzMoonshot/RcwaOrbitCount.lean`
(29 theorems, 6 definitions).  It imports `RcwaHalting.lean`, which brings in `RcwaSameOrbit`, `RcwaMachine`,
`RcwaEngineGen`, `CounterMachine` and `CounterMachineUniversal`, all proved and axiom-clean.  Do not
edit any of those files.

Sources: research note `~/personal/tmp/amusical-agents/out/undec-lemma.md` (§2 orbit formula, §4
Lemma M, §7 Lemma A, §8 assembly) and `out/undec-r25.md` §6 ("the count is 1 or ∞").  Mathlib:
`Mathlib/Computability/Halting.lean` (`ComputablePred.rice`, `halting_problem_not_re`),
`PartrecCode.lean` (`exists_code`, `curry`, `eval_curry`, `primrec₂_curry`, `primrec_evaln`,
`evaln_complete`, `evaln_sound`), `RE.lean` (`REPred`, `Partrec.cond`).

## What this layer proves, and why it stops at an interface

**Hypothesis-free:** for every deterministic finite counter machine `U` there is an exact
`{2,3}`-slope RCWA table whose permutation of `ℤ` has **one orbit iff `U` is mortal** (halts
from every configuration) and **infinitely many orbits otherwise** (`exists_table_iff_mortal`).
This is the all-configurations content of `undec-lemma` (Lemma M forward, through H, G, D).

**Conditional:** undecidability of the orbit count needs a *family* of machines.  A fixed machine
gives a fixed `σ`, so its orbit count is a constant; unlike same-orbit, no choice of source state
or initial counters can carry the input.  The family `e ↦ M_e` must be computable, and
`exists_valid_machine` numbers states with `Fintype.equivFin` over types that would vary with `e`.
So the reduction is isolated as two interface Props, each a hypothesis and never an axiom:

* `MortalityUndecidable`: `SourcesHalt` is not computable on valid machines.  It gives
  `not_computable_oneOrbit` and `not_computable_finiteOrbits`.
* `TotalityFamily`: a computable family `F` of valid machines with `SourcesHalt (F e) ↔ Total e`.
  It gives `MortalityUndecidable`, Theorem C(1) as stated on paper (`orbit_count_family`), and
  the Π⁰₂-flavoured strengthening: "one orbit" is neither r.e. nor co-r.e. (`oneOrbit_not_re`,
  `oneOrbit_not_coRE`).

Discharging `TotalityFamily` is the next campaign (see "Later layer" at the end).

## Ratified, do not change

Every definition and theorem statement in `RcwaOrbitCount.lean`:

* **Definitions:** `OneOrbit`, `SourcesHalt`, `Mortal`, `MortalityUndecidable`, `Total`,
  `TotalityFamily`.
* **§1 Dichotomy:** `card_orbits_complete`, `infinite_divergent`, `not_diverges_of_sourcesHalt`,
  `oneOrbit_sigma_iff`, `card_orbits_sigma_eq_one_iff`, `card_orbits_sigma_eq_aleph0_iff`,
  `infinite_orbits_sigma_iff`, `tableOf_orbits`.
* **§2 Mortality transfer:** `lapNotUp_of_lapsMixed`, `exists_forever_of_not_halts`,
  `halts_of_reaches`, `exists_source_reaches`, `exists_macro_chain`, `histWrap_macro_sound`,
  `histWrap_mortal_iff`, `godel_mortal_iff`, `double_sourcesHalt_iff`,
  `exists_valid_machine_mortal`, `exists_table_iff_mortal`.
* **§3 Undecidability:** `computable_tableOf`, `not_computable_oneOrbit`,
  `not_computable_finiteOrbits`.
* **§4 Totality:** `total_not_computable`, `total_not_re`, `total_not_coRE`,
  `mortalityUndecidable_of_totalityFamily`, `orbit_count_family`, `oneOrbit_not_re`,
  `oneOrbit_not_coRE`.

**Rules.**
* No `native_decide`, no axioms, and no `maxHeartbeats` bumps in statements.
* Lean lines are at most 100 characters.
* Do **not** edit `RESEARCH-*.md`.
* Commit after each proved lemma.
* Keep notes as you go in `HANDOFF-orbit-count.md`.
* Helper lemmas and definitions are welcome; put each above its first use.
* Any cleaner route is fine as long as the ratified statements are unchanged.

**Order of attack.**
1. §2 helpers (`lapNotUp_of_lapsMixed` through `exists_macro_chain`).
2. §3 `computable_tableOf` and §4 `total_*`; both are independent of everything else.
3. §1.
4. The three layer theorems of §2.
5. The assemblies.

**Truth checks already run** (`tmp/drafter-orbit/orbit_check.py`, output `orbit_check.out`).  It
reuses the Python mirror of `histWrap` / `godel` / `double` from the cm-upper drafter
(`cm_mirror.py`).  Runs use an exact loop accelerator: a repeated lap is jumped as many times as
every test and decrement along it keeps its outcome.  On 337 raw-halting runs the accelerated run
ends at the identical configuration (`accel_spot.out`).

| Check | Result | Teeth (each fails as it must) |
|---|---|---|
| **A**: junk copies `build j 0 0 (1 + 6·5^j k) s c₁ c₂` | `j ∈ {1, 2}`, every `s` below the order of 3, `c < 3`, `k < 12`: **2,592** points, each in the engine, decoding to `(s, c₁, c₂)`, with pairwise distinct junk | `m = 1 + 2·5^j k` gives **36** bad points (`3 ∣ m`) |
| **B1**: `histWrap_mortal_iff` | `U_mortal`: **0 / 6,075** box configurations of the wrapper fail to halt.  `U_immortal`: **6,498 / 9,720** run on | the wheel's `wb` without `work−`: `U` mortal, but **4,275 / 6,075** wrapper configurations run on |
| **B2**: `godel_mortal_iff` | Morita's RCM(3): **0 / 27,840** run on.  A reversible increment loop: **4,912 / 8,000** run on | no `x ≥ 1` guard: `B` mortal, but **20** compile configurations run on (garbage cycles) |
| **B3**: `double_sourcesHalt_iff` | `double (godel RCM(3))`: all **1,656** box sources halt, and `R` is mortal on the box.  `double (godel loop)`: **6** sources run on, and `R` is not mortal | `R` a 2-cycle (reverse not mortal): no sources, so `SourcesHalt` holds vacuously, yet `R` is not mortal.  So `hmort` is needed |
| **C**: Lemma A (later layer, design check) | Restart machine around a total toy program: **0 / 6,075** run on.  Around a program diverging at input 2: **1,410 / 10,935** run on | a budget that does not grow (`P := 1` per round): total program, yet **4,320 / 6,318** run on |

## Paper proofs (Ren)

Conventions:
* `E` = `RcwaEngineGen.InEngine j`.
* "Engine source" = an element of `RcwaMachine.Src h.eng`, i.e. a point of `Line j M.rules`
  (`engine_symm_eq_none_iff`).
* `card_orbits` is `RcwaMachine.card_orbits`.
* The `Good` record supplies `h.one_le`, `h.fits`, `h.wf`, `h.fitsR`.

### §1 Dichotomy (≈ 230 lines)

* **`card_orbits_complete`** (25).  `Cardinal.mk_congr` of
  `Quotient.congr (Equiv.sumEmpty ℤ Empty)`.
  * The relations match on `inl a`, `inl b` by `h.sameCycle_iff`.
  * `inr` is `Empty.elim`.
* **`infinite_divergent`** (60).
  * *Setup.*  `c.1 < M.K`: otherwise no rule of `M` fires at `c` (`h.wf.src_lt`), so `c` is a
    sink, and `Halts` holds with `n = 0`.  So `c.1 < orderOf 3` by `h.fits`.
  * *The points.*  Put `m k := 1 + 6 · 5^j · k` and `n k := build j 0 0 (m k) c.1 c.2.1 c.2.2`.
    `build_spec` applies:
    * `0 < N j` (`N_pos`);
    * `m k` is odd and `≡ 1 (mod 3)`;
    * `(2^0 · 3^0 · m k : ZMod (5^j)) = 1` (cast `5^j ∣ m k − 1`).

    It gives `InEngine`, the phase and counters of `c`, and `junk = (0, 0, m k)`.
  * *Each `n k` is a divergent engine source.*  `decode j (n k) = c`.  It is a source by
    `engine_symm_eq_none_iff` (`Or.inr hc`), and it diverges by `h.diverges_iff`.
  * *Injective in `k`.*  Compare `(junk _).2.2`.
  * Conclude with `Infinite.of_injective`.
* **`not_diverges_of_sourcesHalt`** (20).  Take `s` with `s.1 ∈ Line`.
  * If `E s.1`, then `decode j s.1` is a machine source (`Line`), so it halts, and
    `h.diverges_iff` applies.
  * If `¬ E s.1`, then `h.eng s.1 = none` (`F_of_not_inEngine`).  So `fwd 1 = none`, and `s`
    does not diverge.
* **`oneOrbit_sigma_iff`** (3).  This is `RcwaSameOrbit.sameCycle_all_iff h h1 h2`.
* **`card_orbits_sigma_eq_one_iff`** (40).  Rewrite with `card_orbits_complete`, then
  `card_orbits h.eng h.tau h.theta (h.noBiInfinite h1) (h.endToStart h2)`.
  * (←) The divergent-source type is empty (`not_diverges_of_sourcesHalt`), so the count is
    `1 + 0`.
  * (→) If some source does not halt, `infinite_divergent` makes the second summand `≥ ℵ₀`, so
    the total is not `1` (`Cardinal.one_lt_aleph0`, `le_add_left`).
* **`card_orbits_sigma_eq_aleph0_iff`** (40).
  * (←) `≥ ℵ₀` as above.  `≤ ℵ₀` because `Orbits` is a quotient of `ℤ`
    (`Cardinal.mk_le_of_surjective Quotient.mk_surjective`, `Cardinal.mk_int`).
  * (→) `ℵ₀ ≠ 1`, then use `card_orbits_sigma_eq_one_iff`.
* **`infinite_orbits_sigma_iff`** (15).  `Cardinal.infinite_iff` and the two lemmas above.
* **`tableOf_orbits`** (30).
  * `hG := good_of_valid hM`.  `tableOf_spec` gives exactness and `eval = sigma …`.
  * `hb` comes from `sigma_bijective hG`.
  * `Equiv.ofBijective _ hb = sigmaPerm hG` by `ext` (as in `not_computable_sameCycle`).
  * Then apply `oneOrbit_sigma_iff` and `infinite_orbits_sigma_iff` with `hM.noBiInfinite`
    and `hM.endToStart`.

### §2 Mortality transfer (≈ 440 lines)

* **`lapNotUp_of_lapsMixed`** (35).  Mirror `lapNotDown_of_lapsMixed` line for line.
  * The `LapsMixed` lap has a *negative* entry `j`, so `(x n).2 j < (x m).2 j`.
  * That refutes `(x m).2 ≤ (x n).2`.
* **`exists_forever_of_not_halts`** (30).
  * The subtype `{d // ¬ M.Halts d}` is closed under some step.  If no step exists, `d` is
    `Stuck`, so `Halts` holds with `d` itself.  A step to a halting `d'` makes `d` halt
    (`ReflTransGen.head`).
  * `choose` a successor function, then iterate it (`Nat.rec`).
* **`halts_of_reaches`** (20).  Induction on `hr` (`ReflTransGen.head_induction_on`, generalizing
  `c`).  In the `head` case, `Step s s'` and `Halts s` give `Halts s'`:
  * write `s →* d` with `d` stuck;
  * `d = s` is impossible, since `s` steps;
  * otherwise the first step of `s →* d` is `s'` by `step_functional`.
* **`exists_source_reaches`** (35).  By contradiction.
  * Every `d` with `Reaches d c` is not a source, so it has a predecessor `d'`, and
    `Reaches d' c`.
  * Choose along the subtype to get `x : ℕ → Cfg` with `Step (x (n+1)) (x n)`.
  * This contradicts `RevMortal`.
* **`exists_macro_chain`** (15).
  * `exists_forever_of_not_halts`.
  * Then `(RcwaMachine.immortal_iff_macro B M.Step (lapNotUp_of_lapsMixed hlap)).1`, with the
    instance from `wellQuasiOrderedLE_pi`.
* **`histWrap_macro_sound`** (50).  Copy the first half of `histWrap_macro_hist`:
  * the guard step;
  * `op ρ'`;
  * `hbeq : b = (bnd ρ'.src, hcfg v h)`;
  * `hmac := histWrap_macro hρ' hact h`;
  * `macroStep_functional (histWrap_det hU)` gives
    `b' = (bnd ρ'.dst, hcfg v' (K h + lab ρ'))`.

  Read off `s = ρ'.src`, `s' = ρ'.dst`, and `b'.2 (.val i) = v' i`.  The step is
  `⟨ρ', hρ', rfl, rfl, hact⟩`.  `hlab` is not needed.
* **`histWrap_mortal_iff`** (40).
  * (→) Take `c = (q, v)` and use `(histWrap_halts_iff hU q v).1` at `(bnd q, hcfg v 0)`.
  * (←) Suppose `¬ Halts c`.  `exists_macro_chain histWrap_lapsMixed` gives `b`.  Decode each
    step with `histWrap_macro_sound`.
  * *The decodings agree.*  The `bnd` index of `b (n+1)` read from steps `n` and `n+1` is the
    same (`HState.bnd.inj`).  So `y n := (s n, fun i => (b n).2 (.val i))` satisfies
    `U.Step (y n) (y (n+1))`.
  * `CM.not_halts_of_forever hU` contradicts `Mortal U`.
  * Instances: `Finite (HState Q ι K)` is derived from `Fintype`.
* **`godel_mortal_iff`** (40).
  * (→) Use `godel_halts_iff hB hB' hp q v`.
  * (←) Same as for `histWrap`, with `godel_lapsMixed` and `godel_macro_sound`.
  * The decodings agree exactly as in `godel_revMortal`'s `key`: `GState.ent.injEq` and
    `genc_inj`.  This yields a forward `B`-chain, and `not_halts_of_forever hB`.
* **`double_sourcesHalt_iff`** (50).
  * (→) Given `c`, `exists_source_reaches hmort c` gives a source `s`.
    `double_isSource e hrs hdet hrev hs` makes `dcfg e true s` a source.  So it halts, and
    `double_halts_iff` turns that into `R.Halts s`.  Finish with `halts_of_reaches hdet`.
  * (←) Let `x` be a source.
    * If `K ≤ x.1`, no rule fires (`double_src_dst_lt`), so `x` is a sink and halts with `n = 0`.
    * Otherwise `x = dcfg e b c` (`exists_dcfg`).  `b = false` contradicts
      `double_not_isSource_bwd`.  For `b = true`, `isSource_of_double` and `double_halts_iff`
      apply.
* **`exists_valid_machine_mortal`** (50).  Copy the construction in `exists_valid_machine`
  (labels, primes, `B`, `R`, `rs`, `e`).  Then
  `double_sourcesHalt_iff`, `godel_mortal_iff`, `histWrap_mortal_iff` chain the three `↔`.
  There is no `NormalAt` hypothesis.
* **`exists_table_iff_mortal`** (20).  `tableOf M` with `exists_valid_machine_mortal` and
  `tableOf_orbits`.

### §3 Undecidability given `MortalityUndecidable` (≈ 45 lines)

* **`computable_tableOf`** (5).  `tableOf M = (reduce (M, (0, 0, 0))).1`: compose
  `Computable.fst`, `computable_reduce`, and `Computable.pair Computable.id (Computable.const _)`.
  Checked in scratch.
* **`not_computable_oneOrbit`** (15).  The decider is `g ∘ tableOf`, using `tableOf_orbits`.
  Checked in scratch:

  ```lean
  rintro ⟨g, hg, hspec⟩
  refine h ⟨g ∘ tableOf, hg.comp computable_tableOf, fun M hM => ?_⟩
  obtain ⟨hex, hb, h1, -⟩ := tableOf_orbits hM
  exact (hspec _ hex hb).trans h1
  ```

* **`not_computable_finiteOrbits`** (25).  On valid tables, `Finite ↔ ¬ Infinite ↔ SourcesHalt`
  (`not_infinite_iff_finite`).

### §4 Totality (≈ 270 lines)

* **`total_not_computable`** (30).  Rice with `C = {f | ∀ x, (f x).Dom}`:
  * transfer `ComputablePred Total` to codes along `Denumerable.ofNat` / `encode`;
  * `f = fun _ => Part.some 0` (`Nat.Partrec.const`) is in `C`;
  * `g = Nat.Partrec.none` is not.
* **`total_not_re`** (80).  Reduce co-halting at input `0`.
  * Take `G (c, x) := cond (evaln x c 0).isSome Part.none (Part.some 0)`, which is `Partrec`
    (`Partrec.cond`, `primrec_evaln`).
  * `exists_code` gives `d` with `eval d m = G (ofNat Code m.unpair.1, m.unpair.2)`.
  * Put `r c := encode (curry d (encode c))`.  It is computable (`primrec₂_curry`), and
    `eval (ofNat Code (r c)) x = G (c, x)` (`ofNat_encode`, `eval_curry`, `Nat.unpair_pair`).
  * So `Total (r c) ↔ ∀ x, evaln x c 0 = none ↔ ¬ (eval c 0).Dom` (`evaln_complete`,
    `evaln_sound`).
  * `REPred Total` composed with `r` (`Partrec.comp`) contradicts `halting_problem_not_re 0`.
* **`total_not_coRE`** (60).  Same, with `G' (c, x) := eval c 0` (constant in `x`):
  `Total (r' c) ↔ (eval c 0).Dom`, so `REPred (¬ Total ·)` contradicts
  `halting_problem_not_re 0`.
* **`mortalityUndecidable_of_totalityFamily`** (15).  The decider is `g ∘ F`, with
  `Classical.decPred`; `(hFe e).2` contradicts `total_not_computable`.
* **`orbit_count_family`** (30).  Take `T := tableOf ∘ F`, with `computable_tableOf.comp hF`.
  Then apply `tableOf_orbits (hFe e).1` and rewrite with `(hFe e).2`.
* **`oneOrbit_not_re`** (25).  `REPred (P ∘ T)` via `Partrec.comp`.  By `orbit_count_family`
  it is `Total`, which contradicts `total_not_re`.
* **`oneOrbit_not_coRE`** (25).  The same, contradicting `total_not_coRE`.

**Rough total: 900-1,100 lines.**  The largest pieces are `infinite_divergent`, the two
`card_orbits_*` lemmas, and `total_not_re`.

## Later layer (not in this kickoff): discharging `TotalityFamily`

This needs no new mathematics beyond `undec-lemma` §7, but it is a real engineering campaign.

1. **Lemma A, CM level** (1,000-1,500 lines).
   * *The machine.*  A restart wrapper `A_e` around a fixed deterministic universal `U₂`.  `U₂`
     is `lcm` of a two-input `ToPartrec` code: `CounterMachineUniversal.halts_iff_eval` is
     already general in the input stacks.
   * *RESTART:*
     * clear the `U₂` counters;
     * copy the read-only `X` through `W`;
     * move the spent budget `T` into `P` and add 1;
     * push the input numeral.
   * *SIM:* each `U₂` rule is gated by `P = 0 → RESTART`, else `P−`, `T+`.
   * *Where `e` enters.*  Only through a straight-line chain that pushes the digits of `e`.
     Feeding `U₂` the input `[2^x, e]` keeps the `x` part a loop: `bit1`, then `x` times `bit0`.
   * *Statement:* `Mortal (A e) ↔ Total e`.  Check **C** above tests this shape and its
     budget teeth.
2. **A computable compile** (1,500-2,500 lines).  The obstacle is that `exists_valid_machine`
   numbers states by choice, over types that vary with `e`.  Route:
   * a concrete compile on `ℕ`-numbered quadruples (labels = rule index + 1, primes =
     `Nat.nth Nat.Prime`, state numbering by an explicit pairing), proved `Primrec` with the
     `RcwaSameOrbit.PrimInt` toolkit;
   * its `Valid` and `SourcesHalt ↔ Mortal`, transported from the typed compile.  The transport
     needs a relabelling lemma: `Machine.Valid` and `SourcesHalt` are invariant under a
     renumbering of `[0, K)` that commutes with `pair`.
3. **Assembly** (200 lines): `TotalityFamily`.

* **Total: about 3-4.5k lines.**  Confidence 50% that it lands within two to three weeks of laps.
* **A cheaper partial discharge.**  `MortalityUndecidable` alone (Σ⁰₁; KO appendix Thm 1):
  restart around the existing fixed `undecidableCM` machine, with `n` loaded by a chain.
  * The same cost for item 2, but a smaller item 1.
  * It makes `not_computable_oneOrbit` hypothesis-free.
  * It does not give the r.e./co-r.e. pair.

**Not proposed: the Δ₂ form** ("one orbit" is not computable relative to the halting set).
Mathlib has `RecursiveIn` and `TuringDegree`, but no relativized universal code, halting theorem
or Rice.  Building them is an estimated 1,500+ lines of pure recursion theory.  Neither-r.e.-nor-
co-r.e. (§4) is the strongest form Mathlib supports cheaply.
