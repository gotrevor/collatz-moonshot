# KICKOFF 2026-10-16: Theorem C on ℤ assembled, same-orbit encodes halting (research §55-§57)

Repo `collatz-moonshot-amusical-zcore` (branch `wip/rcwa-sameorbit-2`): close every `sorry` in
`CollatzMoonshot/RcwaSameOrbit.lean`.  It imports `RcwaEngineGen.lean` (Lemma P at `r = 5^j`,
proved, PR #44) and `RcwaMachine.lean` (completion and Lemma M, proved, PR #45); do not edit
either, except one chore: replace the deprecated `Int.le_induction` at `RcwaMachine.lean:453` with
`Int.leInduction` (keep its statements unchanged).

## Ratified, do not change

Every definition and theorem statement in `RcwaSameOrbit.lean`: `IsRcwa23At`, `IsRcwa23`,
`RcwaTable` (`piece`, `eval`, `Exact`), `tableFrom`, `Test`, `Move`, `Cfg`, `Rule` (`Fires`,
`target`), `step`, `Deterministic`, `Reversible`, `run`, `IsSource`, `IsSink`, `Halts`,
`NoBiInfinite`, `EndToStart`, `isSourceB`, `Machine` (`pairFn`, `WF`, `Valid`), `ofInjective`,
`machine`, `decode`, `enc`, `move`, `F`, `Fits`, `engine`, `InClass`, `Line`, `IsHighway`, `hwIdx`,
`hwPos`, `hwPoint`, `hwNext`, `hwModulus`, `highwayAt`, `sigma`, `Good`, `sigmaPerm`, `level`,
`highwayOf`, `tableOf`, `reduce`, the `Primcodable` instances and equivalences,
`HaltingUndecidable`, and all theorem statements.  No `native_decide`, no axioms.  Lean lines
≤ 100 characters.  Do **not** edit `RESEARCH-*.md`.  Commit after each proved lemma.  Notes as you
go in `HANDOFF-rcwa-sameorbit.md`.  Order of attack: layers 1-4 first (the same-orbit theorem
`sameCycle_enc_iff` is the main result); `computable_reduce` (the largest lemma) last.  Helper lemmas are welcome (put them above their first use).
The definitions were `#eval`-checked at `j = 2`: `decode (enc c) = c` with `InEngine`, one `F`
step, `isSourceB`, and `tableFrom` on two toy maps.

## Paper proofs (Ren)

Notation: `ord := orderOf (3 : ZMod (5^j))`, `N := N j`, and the `RcwaEngineGen` API
(`inEngine_scale`, `phase_scale`, `C1_scale`, `C2_scale`, `junk_scale`, `scale_spec`,
`eq_of_decode_eq`, `exists_decode`, `one_le_C1_iff`, `one_le_C2_iff`, `phase_lt`,
`le_orderOf_three`, `dlog3_three_pow`, `build_spec`, `three_pow_N`, `two_pow_N`).  `move j n s' δ₁
δ₂` is literally `scale n (N * δ₁) (N * δ₂ + s' - phase j n)`.  First prove three helpers:

* `phase_lt_ord`: an engine point has `phase j n < ord` (`phase` is the least `k` with
  `3^k = n`, and `3^(k % ord) = 3^k`; `pow_mod_orderOf`, `List.find?` minimality).
* `decode_move`: for `InEngine j n`, `s' < ord`, `0 ≤ C + δ` on both counters, `move j n s' δ₁ δ₂`
  is on the engine, decodes to `(s', (C1 + δ₁).toNat, (C2 + δ₂).toNat)`, and has the same junk.
* `decode_inj`: engine points with equal `decode` and equal `junk` are equal (`eq_of_decode_eq`).

### Layer 1

* **`RcwaTable.isRcwa23_eval`.**  `M = T.modulus`.  If `n ≡ r [ZMOD M]` then `n % M = r % M`, so
  `T.piece n = T.piece r`; the index `(n % M).toNat < M = length`, so the piece is in the list
  and `slope` applies; `c * ((a n + b) / c) = a n + b` by `dvd` (`Int.mul_ediv_cancel'`).
* **`tableFrom_spec`.**  For `k < M`, `hf k` gives `(a, b, c)` with `c f n = a n + b` on the
  class.  Then `f (k + M) − f k = (a / c) M`, so `q = a / c` in `ℚ`, and for `n ≡ k`:
  `q.den (f n − f k) = q.num (n − k)` (clear denominators; `Rat.num_div_den`).  So
  `q.den · f n = q.num · n + (q.den · f k − q.num · k)`: this is `dvd`, and `eval n = f n`
  (`Int.mul_ediv_cancel_left`, `q.den ≠ 0`).  `slope`: `q.num / q.den = q = a / c = 2^i 3^j`.
  `length`: `List.length_map`, `List.length_range`.

### Layer 2

* **`step_eq_of_fires`.**  `List.find?` returns some earliest `ρ₀ ∈ R` with `ρ₀.Fires c`
  (`List.find?_eq_none` rules out `none`; `List.mem_of_find?_eq_some`, `List.find?_some`);
  `Deterministic` gives `ρ₀.target c = ρ.target c`.
* **`step_injective`.**  Two rules firing at `c, c'` with equal targets; `Reversible`.
* **`isSourceB_iff`.**  If `step R c' = some c` via `ρ`, then `c = ρ.target c'`, so
  `ρ.dst = c.1`, `c_i − d_i = c'_i ≥ 0`, and `c' = (ρ.src, (c_i − d_i).toNat)` (`ρ.Fires c'`
  gives `c'.1 = ρ.src`): the Boolean conjunct for `ρ` is true.  Conversely a true conjunct
  exhibits a predecessor.  `List.all_eq_true`.

### Layer 3

* **`enc_spec`.**  `enc j c = build j 0 0 1 c.1 c.2.1 c.2.2` (`ring`); `build_spec` with
  `e = D = 0`, `m = 1` (`2^0 3^0 1 = 1`) and `hc : c.1 < ord`.
* **`F_eq_some_iff`.**  (→) The earliest rule `ρ` firing at `decode n` has `ρ.dst < ord`
  (`hR`), and `Fires` gives `0 ≤ C + δ`, so `decode_move`: `m` is on the engine with the junk of
  `n`, and `decode m = ρ.target (decode n) = step R (decode n)`.  (←) Some rule fires, so
  `F n = some m''` with `decode m'' = decode m`, `junk m'' = junk n = junk m`; `decode_inj`.
* **`F_eq_move`.**  `F_eq_some_iff`, `step_eq_of_fires`, `decode_move`, `decode_inj`.
* **`move_slope`.**  `scale_spec` cast to `ℚ`; `2^{A.toNat} / 2^{(−A).toNat} = 2^A` (zpow,
  `Int.toNat_sub_toNat_neg`).
* **`F_injective`.**  Both points are on the engine; `F_eq_some_iff` gives equal junk and
  `step` images; `step_injective`; `decode_inj`.

### Layer 4

Set `f := engine hj hR h.rev` (with `hR : Fits j M.rules` from `wf` and `fits`), `α := ℤ`,
`H := Empty`.  Then `Src f = Line j M.rules`: an engine `x` with a machine predecessor `c'` has the
preimage with `decode = c'` and `junk x` (`exists_decode`, needing `c'.1 < ord`: rule sources are
`< K ≤ ord`); a non-engine `x` has none.  `Snk f` is the non-engine points plus the engine points
with `IsSink (decode n)`.  Engine points with phase `≥ K` have no rule (`WF`), so they are sources
and sinks, and `pairFn` fixes them (`List.getD` past the end): they behave like highway points.

* **`hwPoint_hwPos`.**  `cover` gives a class containing `n`, so `i := hwIdx hw n < k`
  (`List.findIdx_lt_length_of_exists`) and `hw[i]` contains `n` (`List.findIdx_getElem`).
  With `(r, m) = hw[i]`, `m > 0`, `m ∣ n − r`; `(k t + i) % k = i`, `(k t + i) / k = t`.
* **`hwPos_hwPoint`.**  `i := (p % k).toNat`, `t := p / k`, `x := r_i + m_i t` is in class `i`,
  hence in the line (`cover`); no class `j < i` contains `x` (`disjoint`,
  `List.pairwise_iff_getElem`), so `hwIdx hw x = i` (`List.findIdx_eq`); `Int.ediv_add_emod`.
* **`isHighway_highwayAt`.**  Put `L := hwModulus j`.  *Periodicity:* `n ∈ Line ↔ n % L ∈ Line`.
  `InEngine j n` depends on `n mod 5^j` (`5 ∤ n`, `3^phase ≡ n`, `phase`) and on `3^phase ∣ n`
  (`phase < N`), and `n ≠ 0` follows from `5 ∤ n`.  `IsSource (s, c₁, c₂)` depends only on `s`
  and on which of `c_i = 0`, `= 1`, `≥ 2` holds (`isSourceB_iff`: each candidate predecessor
  `c − δ` and its tests are determined by that pattern, `δ ∈ {−1, 0, 1}`), and `C₁ = 0, 1, ≥ 2`
  is `v₂ < N`, `< 2N`, `≥ 2N` (`2^{2N}`-periodic), `C₂ = 0, 1, ≥ 2` is `v₃ < s + N`, `< s + 2N`,
  `≥ s + 2N` with `s < N` (`3^{3N}`-periodic).  Then: `ne_nil` (class `0` is off the engine),
  `modulus` (`L` itself), `disjoint` (distinct residues `< L`; `List.Nodup.filter`,
  `List.nodup_range`), `cover` (periodicity; the representative is `(n % L).toNat`).
* **`sigma_bijective`.**  Show `sigma j M hw = sumEmpty ∘ completeFun f τ θ ∘ sumEmpty.symm` and
  use `RcwaMachine.completeFun_bijective`.  `θ : ℤ ≃ Src f ⊕ Empty` is `p ↦ inl ⟨hwPoint hw p, _⟩`
  with inverse `hwPos`.  `τ : Snk f ≃ Src f` is the identity on non-engine sinks and
  `n ↦ move j n (M.pairFn (phase j n)) 0 0` on engine sinks, inverse with the inverse permutation
  of `pairFn` (a bijection of `ℕ`: `pair_perm` on `range K`, identity from `K`).  `pair_sink`
  makes `τ` land in sources and its inverse in sinks; `decode_move`, `decode_inj` give the
  inverse laws.  Then `nu f θ (inl x) = inl (hwNext hw x)` for `x` in the line.
* **`isRcwa23At_sigma`.**  On one class mod `3^N L`: `InEngine`, `phase`, and each `Fires
  (decode n)` are constant (`htest`; the tests are `2^N ∣ n`, `3^{N + s} ∣ n`, `s < N`).  So
  `sigma` is one of: a `move` piece (`c σ n = a n`, `a / c = 2^{Nδ₁} 3^{Nδ₂ + s' − s}`,
  `scale_spec`); `hwNext` on class `i` (`m_i σ n = m_{i'} n + b`, `m_{i'} / m_i ∈ 2^ℤ 3^ℤ` as both
  are `5^j 2^α 3^β`; `hwIdx` is constant since every `m ∣ L`); or `hwNext ∘ τ` with
  `τ n = 3^d n`, `|d| < N`, `|d| ≤ v₃ n` when `d < 0`, and the class of `τ n` mod `L` constant on
  the class mod `3^N L`.  Compose the exact forms.
* **`sameCycle_hwNext_iff`.**  Conjugate as above.  With `p := hwPos hw n`, `θ p = n`,
  `θ (p + 1) = hwNext hw n`.  (←) `RcwaMachine.sameCycle_succ_of_not_diverges`.  (→)
  `RcwaMachine.not_sameCycle_of_cut` with `q = p`, `r = p + 1`.  Transfer:
  `fwd f k n = some x ↔ InEngine x ∧ junk x = junk n ∧ run R k (decode n) = some (decode x)`
  (induction, `F_eq_some_iff`), so `Diverges f n ↔ ¬ Halts R (decode n)`.  (H1) for `f`: an
  `F`-chain stays on the engine and decodes to a `step`-chain.  (H2) for `f`: a non-engine source
  is its own sink (`k = 0`) and `τ` fixes it; for an engine source reaching the sink `t`,
  `EndToStart` gives `(pairFn (phase t), C1 t, C2 t) = decode n`, and the junk is constant along
  the chain; `decode_inj`.
* **`sameCycle_enc_iff`.**  `sameCycle_hwNext_iff` at `enc j c` (`enc_spec`, `c.1 < K ≤ ord`).
* **`sameCycle_all_iff`.**  `RcwaMachine.sameCycle_all_iff` after the conjugation.  Sources of
  `f` are non-engine (never diverge) or engine points decoding to sources; a machine source with
  state `≥ ord` has no rule (`WF`, `K ≤ ord`), so it halts at once; a source with state `< ord` is
  `decode (enc j c)`.

### Layer 5

* **`good_of_valid`.**  `level M = K + 1 ≥ 1`; `K ≤ K + 1 ≤ ord` (`le_orderOf_three`);
  `isHighway_highwayAt`; the other fields from `Valid`.
* **`tableOf_spec`.**  `tableFrom_spec` with `isRcwa23At_sigma` at `L := hwModulus (level M)`:
  every highway modulus equals `L`, and `5^j 2^N 3^{2N} ∣ 5^j 2^{2N} 3^{3N}`.
* **`computable_reduce`.**  The bulk.  Build `Primrec`/`Computable` proofs bottom-up:
  `Test.ok`, `Move.val`, `Rule.Fires` (as a `Bool`), `Rule.target`, `step` (`List.find?` is
  `Primrec`: `Primrec.list_find?` or via `List.foldr`), `isSourceB`, `padicValInt 2`, `padicValInt
  3` (bounded search: `v_p(n) ≤ |n|`, `Nat.find` replaced by `List.range` search), `dlog3`,
  `phase`, `C1`, `C2`, `InEngine` (decidable, `ZMod (5^j)` equality via `Int.emod`), `scale`,
  `move`, `F`, `hwIdx`, `hwPos`, `hwPoint`, `hwNext`, `highwayAt` (`List.filter` over
  `List.range`), `sigma`, `tableFrom` (`ℚ` arithmetic, or rewrite with `Int.gcd` to stay in
  `ℤ`), `enc`.  Each is `Primrec` in its arguments including `j`; `Computable` follows.  Tip:
  prove `Primrec` versions of `ZMod (5^j)` operations by transporting to `ℤ` with `% 5^j`, since
  the type depends on `j`.
* **`not_computable_sameCycle`.**  Given `g`, set `g' := g ∘ reduce`, computable by
  `computable_reduce` and `Computable.comp`.  For valid `M`, `c.1 < K`, `IsSource c`:
  `tableOf_spec` makes `tableOf M` exact with `eval = sigma`; `Equiv.ofBijective (tableOf M).eval _`
  equals `sigmaPerm (good_of_valid hM)` (`Equiv.ext`); `sameCycle_enc_iff` gives `g' (M, c) =
  true ↔ Halts c`.  This contradicts `hlit`.

Any cleaner route is fine as long as the ratified statements are unchanged.
