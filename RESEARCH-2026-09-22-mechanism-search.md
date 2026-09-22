# Research 2026-09-22 (Fable): mechanism search at the run-count gap node 🔎

Attended research session, not a proof campaign.  Brief: `FABLE-NEXT-SESSION.md`.  The
no-lap-without-a-mechanism gate of `DIRECTION.md` stands; **no helper lap was launched** and
none is authorized by this document.  Everything below is either an exact statement with a
proof (paper or Lean), a finite control with hand anchors, or a candidate mechanism recorded
with the precise step at which it failed.

## 0. Verdict

1. **Goal audit.**  The frozen node `survivor ⟹ r ≥ εK` is the few-run exclusion made uniform
   in `K`.  It does **not** imply `StoppingCorrect`.  The exact remaining implication is its
   complement, `C_ε`: *no first-crossing survivor has `r ≥ εK` odd runs*.  `C_ε` contains the
   exclusion of every cycle whose crossing prefix has that many runs, and the exclusion of the
   "orbit below a cycle" family (§1.3), i.e. it is at least the many-circuit half of Front B,
   for which no mechanism exists in the literature or the repo.
2. **Round A (arithmetic).**  All run-to-run admission equations carry **exactly one
   congruence** (§2): integrality of `n = (N − 2ᵐE)/D` already forces the residue class.
   Multiplying run bounds loses magnitude only, and for short runs the magnitude information
   is `q_i ≈ 1–3` bits per run.  No new load-bearing step was found; the two candidates
   developed (§3, §4) fail at named steps.
3. **Round B (global).**  `CrossingExists ⟺ ℕ_{≥2} ∩ C = ∅` for the ballot-forever Cantor set
   `C ⊂ ℤ₂` (§5).  `C` contains every negative 3n+1 cycle and, for 3n−1, the positive
   3-cycle `5,7,10`, so the only load-bearing input is `N > 0`.  No individual-orbit mechanism
   found; the retired premises are not replaced.
4. **New, persisted.**  (a) A sibling-map control population: under `5n+1` the starts
   `13, 17` (cycles, `E = 0`) and `5` (enters the 13-cycle from below; `m = 274`, `K = 118`,
   `39` odd runs, `E = 8`) are first-crossing survivors - the first many-run survivor of the
   exact admission equations we have.  `experiments/sibling_survivors.py`,
   `test_sibling_survivors.py`.  (b) Two Lean facts, axiom-clean:
   `at_primitive` (a first-crossing word is never a proper power) and `overshoot_modEq`
   (`3ᴷ·E ≡ N (mod D)`), `FrontA/FirstCrossingResidue.lean`.

## 1. Goal audit: what the run-count node buys, exactly

Notation as in `FrontA/FirstCrossing.lean`: `At n m` (first crossing at `m`), `K = ones`,
`D = 2ᵐ − 3ᴷ > 0`, `N = numer v`, survivor `n ≤ y := tstep^[m] n`, overshoot `E = y − n`,
`r` = number of maximal odd runs.

**Node** `N_ε : ∀ n m, 2 ≤ n → At n m → n ≤ tstep^[m] n → ε·K ≤ r`.

### 1.1 `N_ε` is consistent with survivors

`N_ε` says nothing about a survivor with `r ≥ εK`.  A typical ballot word has `r ≈ K/2`, so
`N_ε` (with any ε < 1/2) excludes only an entropically thin corner of the words.  Formally:

    StoppingCorrect  ⟺  N_ε ∧ C_ε,     C_ε : ∀ n m, 2 ≤ n → At n m → n ≤ tstep^[m] n → r < ε·K.

(Trivial: a survivor violates one of the two.)  Proved so far is `N_ε` for the *fixed* bound
`r ≤ 50` (`stoppingCorrect_of_oddRunCount_le_fifty`) and, on paper, `r ≳ 2.17 ln K`.  The
pincer cannot reach `r ≥ εK` (reason in the blueprint leaf §4.6: the per-run chaining
`x_{i+1} < b^δ x_i^δ` charges `δ = log₂3` per run because a run of length `q` costs only the
divisibility `2^q ∣ x_i + 1`, whose worst case `x_i = 2^q − 1` does occur, e.g. `q = 12 → 6`).

### 1.2 `C_ε` contains a cycle-exclusion statement

A nontrivial cycle with minimum `n₀` produces `At n₀ m` for some `m ≤ period` with `y ≥ n₀`
(`noNontrivialCycle_of_stoppingCorrect`'s argument, `full_period_subcritical`).  Its
crossing-prefix run count is at most the circuit count.  So `C_ε` excludes every cycle whose
crossing prefix carries `≥ εK` runs.  Few-circuit cycles are excluded to 91 circuits
(Hercher) by the same pincer that gives `r ≳ 2.17 ln K`; **many-circuit cycles have no known
mechanism**.  A proof of `C_ε` would settle them.  This is the lower bound on the difficulty
of the complement.

### 1.3 The three failure shapes stay distinct

| shape | equation | `E` | where it lives |
|---|---|---|---|
| cycle | `D·n = N` | `0` | `C_ε` for its prefix run count; Front B |
| failed first-crossing descent | `D·n + 2ᵐE = N`, `0 < 3E < K` | `1 … ≈ r` | CST proper; the orbit may still descend later (a CST failure need not be a Collatz counterexample) |
| divergence | never crosses, or crosses and fails at its orbit minimum | - | `CrossingExists` (Π₂) or CST at the minimum |

New sub-shape of the second row, exhibited in `5n+1` and impossible to rule out for `3n+1`
without excluding cycles: **orbit below a cycle**.  If `T(n) = c` lies on a subcritical
cycle with word `w` (`Λ(w) := |w| log 2 − ones(w) log 3 > 0`) and `Λ₁ = log 2 − log 3 < 0` is
the walk after the first (odd) step, the first crossing of `n` is at `m = 1 + ℓ·|w|` with
`ℓ = ⌈|Λ₁|/Λ(w)⌉` laps, `K = 1 + ℓ·ones w`, `r = ℓ · (runs of w)` (linear in `K`), and
`E = c − n`.  For `5n+1`, `n = 5`, `w = 1110000`, `Λ(w) = 7 log 2 − 3 log 5 = 0.0237`,
`ℓ = 39`, `m = 274`, `E = 8`.  The hand computation is the pytest anchor.

### 1.4 What `N_ε` would still be worth

Nothing toward CST by itself.  It would be a uniform-in-`K` strengthening of the rung ladder
(`r ≤ 50` today), i.e. new mathematics of the few-run kind, and would exclude few-circuit
cycles uniformly.  Do not describe it as "the gap to CST"; the gap to CST is `C_ε`.

## 2. Round A: the run-to-run equations carry one congruence

Block form of the word: `v = 1^{q₁}0^{e₁} ⋯ 1^{q_r}0^{e_r}`, run starts `x₀ = n, x₁, …`,
cofactors `x_i + 1 = 2^{q_{i+1}} a_i` (`a_i` odd).  The exact run-to-run equation is

    3^{q_i} a_{i−1} + 2^{e_i} − 1 = 2^{e_i + q_{i+1}} a_i        (i = 1 … r−1),

with the closing row `3^{q_r} a_{r−1} − 1 = 2^{e_r}(2^{q₁} a₀ − 1 + E)`.  As a linear system
in `(a₀, …, a_{r−1})` its determinant is `∏ 2^{e_i+q_{i+1}} − ∏ 3^{q_i} = D` (Simons–de Weger's
matrix with the last row's constant shifted by `−2^{e_r}E`).  Cramer's rule gives every `a_i`
as `(integer)/D`; the `r` integrality conditions are equivalent to one another.

**Lemma (single congruence).**  For a word `v` (length `m`, `K` ones, `D > 0`) and `E ≥ 0`,

    { n ≥ 2 : traceWord n m = v ∧ tstep^[m] n = n + E }  =  { n ≥ 2 : n = (N − 2ᵐE)/D ∈ ℤ }.

*Proof.*  `⊆` is `overshoot_identity`.  `⊇`: if `D·n = N − 2ᵐE` then, modulo `2ᵐ`,
`−3ᴷ n ≡ N`, so `n ≡ −N·3^{−K} = R(v) (mod 2ᵐ)`, which is the dictionary
`traceWord n m = v`; the identity then gives `tstep^[m] n = n + E`.  ∎

So the positivity of every `x_i`, the divisibilities `2^{q_{i+1}} ∣ x_i + 1`, and the parity
compatibility of every carry are *consequences* of the one congruence `D ∣ N − 2ᵐE`; there is
no discarded congruence to recover.  What the pincer discards is magnitude: it uses
`a_i ≥ 1`, i.e. `x_i ≥ 2^{q_{i+1}} − 1`, which for a run of length 1–3 is `x_i ≥ 1 … 7`.
Amortising over a variable number of runs cannot help, because the total divisibility
information is `Σ q_i = K` bits, which is exactly `n mod 2ᵐ` restricted to the odd positions
(Terras), already used in full by `R(v)`.

**Exact form of CST.**  `2ᵐ ≡ 3ᴷ (mod D)`, so `E ≡ N·3^{−K} (mod D)` (`overshoot_modEq`), and
`3E < K` (`three_mul_overshoot_lt`).  Since `D > K/3` (by hand for `K ≤ 6`; beyond,
`sep_two_three` gives `3^{3K} ≤ D³·2^K`, so `D ≥ 3^K·2^{−K/3} ≫ K`), `E` **is** the least residue:

    StoppingCorrect  ⟺  for every first-crossing word v:  [N·3^{−K} mod D]  >  (N − 2D)/2ᵐ.

The window `(N − 2D)/2ᵐ ≤ N/2ᵐ ≤ K/(3u)` with `u = 2ᵐ/3ᴷ ∈ (1, 2]`, and `u` is a function of
`m` alone (`K` is determined by `m`).  Equivalently, in the start coordinate,
`n ≤ N/D ≤ K/(3(u − 1))`: the dangerous lengths are those with `u` near `1`, i.e. `m/K` near a
convergent of `log₂ 3`; for `u ≥ 1.1` a survivor's start is at most `≈ 3.3K`.  Persisted:
`sibling_survivors.py words M` asserts `max N/2ᵐ ≤ K/(3u)` over all first-crossing words to
length `M` (hand anchors at `m = 1, 2, 4, 5, 7, 8`).

**Walk form (exact, recorded so it is not re-derived).**  With `Λ_j` the ballot walk and
`p_i` the position of the `i`-th odd letter,

    N / 3ᴷ = ½ · Σ_{i<K} exp(Λ_{p_i + 1}),      N / D = ½ · Σ_{i<K} exp(Λ_{p_i+1}) / (e^{Λ_m} − 1).

The numerator is a sum over odd steps of the exponential of the walk depth after that step.
For a shallow walk (many short runs) `N/3ᴷ ≈ cK`; for a deep walk it is `o(K)`.  This is why
the many-short-runs regime has the *largest* admission window and the *least* magnitude
information - the two effects compound.

## 3. Candidate A (arithmetic): minimal-counterexample suffix constraint - FAILS

**Information used.**  CST for all starts below `n` (the induction hypothesis), which no
retired approach consumes.

**Hoped-for lemma.**  Let `n` be the least CST failure, word `v`, crossing at `m`.  Every
run start `x_j := tstep^[j] n`, `0 < j < m`, satisfies `x_j > n` (a repeat would make `n`
periodic with a subcritical period, contradicting `At`).  *Hoped:* each `x_j` descends at its
own first crossing, which occurs at the least `t > 0` with `Λ_{j+t} > Λ_j` and lies inside
`v`; in residue form `D_j · x_j > N_j` for every suffix, against `D · n ≤ N` for the word.

**Where it fails - immediately.**  Minimality of `n` gives CST only for starts *below* `n`,
and every run start is *above* `n`.  The hoped-for inequalities are CST for larger starts:
circular.  The `5n+1` control makes the failure concrete: `n = 5` is the least survivor, its
first run start `x₁ = 13` is itself a survivor (`E = 0`), and nothing about `5` forbids
that.  So the induction hypothesis constrains no run start, and there is no coupling between
the suffix cycle points `N_j/D_j` and `N/D` either (the suffix to its own crossing is a prefix
of a rotation, not the rotation, so the numerator-append identity does not chain them).
Retired.  The one-sided minimality lever in `DIRECTION.md` (the least failure has no prefix
that is the smaller-numerator member of a ballot pair) is unaffected and stays thin.

## 4. Candidate B (global): ballot-residue discrepancy - FAILS at the integer threshold

**Information used.**  The `a = 3`-specific input that §1.3's `5n+1` control forces on any
`C_ε` mechanism: for `3n+1` the ballot words are entropically rare, `|B_m| ≈ 2^{0.951 m}`
(odd-density threshold `log 2 / log 3 > ½`), whereas for `5n+1` (threshold `0.43 < ½`) they
have positive density and survivors exist.  The verified range is the only other
`3`-specific input, and it is finite.

**Statement.**  `min { R(v) : v ∈ B_m } > max_v N/D` where `R(v) = [−N·3^{−K}]_{2ᵐ}`; the
right side is `≤ K^{437}/(3c)` (Rhin-lite) and `≤ 3.3K` when `u ≥ 1.1`.

**Load-bearing step attempted.**  A lower bound on the least residue of the ballot set.
(i) Additive structure: `R(v) = −Σ_i 2^{p_i} 3^{−(i+1)} mod 2ᵐ` over the positions
`p₀ < ⋯ < p_{K−1}` with the staircase constraint `p_i ≤ c_i` (ballot); an adjacent swap
translates by `2^{p}3^{−(i+1)}` (`residue_adjacent_swap`).  The one-run word has
`R = 2ᴷ·[3^{−K}]_{2^L} − 1`, a pseudo-random point; every other ballot residue is that point
plus a signed sum of unit-times-power-of-two translations.  Bit `b` of `R` is fixed by the
letters at positions `≤ b` *and* by carries from all lower terms, so the top `m − O(log m)`
bits (which must all vanish for `R ≤ poly(m)`) depend on every letter.  No closed form; the
2026-09-19 probes (Christoffel minimiser, near-miss run counts) and the carry-budget null
already show the residues are uniform-looking.  (ii) Counting: the expected number of ballot
residues in `[2, W]` is `|B_m|·W/2ᵐ ≈ K^{437}·2^{−0.049 m}`, summable over `m`, which is the
heuristic for "finitely many CST failures" - but a discrepancy or large-sieve bound has error
`≳ √|B_m| ≫ 1`, and CST needs the exact count `0` at every `m`.  Fourier majorants were
retired 2026-09-19 for the same reason.

**Where it fails.**  No estimate of any known type reaches an error below `1` in the count.
The entropy deficit is a *density* input; the statement needed is *pointwise* over words.
This is DIRECTION's rank-8 row restated with the exact threshold: error `< 1` at window
width `≤ K/(3u)` in modulus `D ≈ 2ᵐ(1 − 1/u)`.

## 5. Round B: `CrossingExists` as a Cantor-set statement

`CrossingExists : ∀ n ≥ 2, ∃ m, 3^{K_m} < 2^m`.  Its failure at `n` is the *ballot-forever*
condition `2^j ≤ 3^{K_j}` for all `j`.  Let `C ⊂ ℤ₂` be the set of 2-adic integers whose
itinerary is ballot forever (closed, measure zero, uncountable; the finite-level sets are
unions of `|B_j|`-many residue classes mod `2^j`).  Then

    CrossingExists  ⟺  ℕ_{≥2} ∩ C = ∅.

Sign controls: `C ∋ −1` (all-odd), and every negative `3n+1` cycle (`−5 → −7 → −10`, word
`110`, density `2/3`; the 11-cycle at `−17`, density `7/11 > 0.631`) - negative cycles are
supercritical.  For `3n−1` on positives, `5 → 7 → 10` is a supercritical 3-cycle: `n = 5`
never crosses, so `CrossingExists` is **false for 3n−1**.  Hence any proof must use `N > 0`
(the `+1`); the mechanism cannot be drift-only, and it cannot be a density statement (Tao's
theorem is consistent with a single orbit, and `mem_taoGood_of_reachesValue` kills backward
amplification).  What positivity gives on an individual orbit: `tstep^[j] n ≥ n` for all `j`
(prefix supercritical), unboundedness (a bounded orbit is eventually a subcritical cycle whose
walk climbs), and infinitely many *future-maximum* times of the walk at which the orbit value
is itself ballot-forever.  None of this separates `ℕ` from `−ℕ` inside `ℤ₂` beyond the sign
of `N`, and I found no statement that does.  Recorded to stop re-derivation; **no lever**.

The blueprint's split "arithmetic kills near-cycles, symbolic kills ballot-forever" is
sharpened by the sign controls: for **CST** the sign control is vacuous (`3n−1` has no
first-crossing survivor at all, since `N < 0` makes `D·n + 2ᵐE = N` impossible - verified to
`10⁴` in the test), so the control for CST mechanisms is the **multiplier** (`5n+1`); for
**CrossingExists** the control is the **sign** (`3n−1`, `n = 5`).

## 6. Tests against the recorded counterexamples

| test | result |
|---|---|
| trivial `1/2` cycle, `n ≥ 2` boundary | `m = 2`, word `10`, `N = D = 1`, `R = 1`, `E = 0`: the `n = 1` survivor, excluded by `n ≥ 2` (test anchor) |
| negative cycles as sign control | supercritical, never cross: controls for `CrossingExists` only (§5) |
| `3n−1` positives | zero first-crossing survivors (`N < 0`); `5,7,10` refutes any drift-only `CrossingExists` argument |
| `5n+1` | survivors `13, 17` (`E = 0`) and `5` (`r = 39`, `E = 8`): refutes any `C_ε` argument valid for all odd multipliers |
| P6 / short-run rational families | rational positivity ≠ admission (`SHORT-RUN-`, `PREFIX-ADMISSION-OBSTRUCTION`); §2's lemma says the only admission datum is the one congruence, so no finite-prefix filter can be complete - consistent |
| `2305` vs `2313` | same `(t, w, k, j, D)`, different prefix remainders, opposite admission: the congruence is not a function of the trunk data - consistent with §2 |
| Mersenne `q = 12 → 6` | the pincer's worst case can repeat; the only bits a short run pins are its own `q` (§2) |
| word powers / repetitions | a first-crossing word is **never** a proper power (`at_primitive`, Lean); eventually-periodic words do arise (§1.3) and are the cycle problem |
| many-short-runs scaling | window `≤ K/(3u)` is run-count independent; magnitude information `Σ q_i = K` bits is fully spent by `R(v)`; `N/3ᴷ ≈ cK` is largest for shallow walks (§2) |
| `K → ∞`, `r ∝ K` | `5n+1`'s `n = 5` family scales: `ℓ` laps give `r = ℓ·runs(w)`, `K = 1 + ℓ·ones(w)`; the shape any `C_ε` proof must exclude for `3n+1` by excluding cycles |

## 7. What landed, verification, and handoff

Files: `CollatzMoonshot/FrontA/FirstCrossingResidue.lean` (+ root import),
`experiments/sibling_survivors.py`, `experiments/test_sibling_survivors.py`, this document,
pointer paragraphs in `DIRECTION.md` and `STATUS.md`.  Verification: module builds; both
theorems `#print axioms` = `[propext, Classical.choice, Quot.sound]`; pytest 3 passed; the
pre-commit gate ran the full build.

**For the next session** (exact statements to use, none of them a lap):

- The node to keep frozen is `C_ε` (§1.1), not `N_ε`; `N_ε` is the uniform rung ladder.
- Any proposed `C_ε` mechanism must (a) fail for `5n+1` on `n = 5`, `13`, `17`, i.e. consume
  the entropy deficit or the verified range, and (b) exclude the orbit-below-a-cycle shape,
  i.e. contain the many-circuit cycle problem.  Check (a) with
  `sibling_survivors.py survivors 5 1 100`.
- The single-congruence lemma (§2) closes the "amortised run constraint" question: there is
  no second congruence.  Do not re-open Round A with a different run bookkeeping.
- Open, and honest: a lower bound on `[N·3^{−K}]_D` over ballot words that beats `K/3`
  uniformly.  The only `3`-specific global input is the entropy deficit; the only known way
  to use it is counting, which stops at error `≳ √|B_m|`.  A mechanism would have to turn the
  deficit into a *pointwise* residue statement - that is the new mathematics, and it is the
  same wall as many-circuit cycles.
