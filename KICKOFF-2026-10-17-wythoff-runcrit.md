# KICKOFF 2026-10-17: the run criterion from Weyl (`RunCriterion` modulo `WeylEquidistributionMulti`)

Repo `collatz-moonshot`, branch `wip/wythoff-runcrit-m` (cut from `origin/main` after PR #68 merged).  Close every
`sorry` in one new file:

| file | content | sorries |
|---|---|---|
| `CollatzMoonshot/WythoffRunCriterion.lean` | phase coordinates of an up-point and three exact identities; the phase ⇔ parity correspondence; independence of the torus frequencies; Weyl ⇒ infinitely many box hits; the box of followers of a run-system solution; the headline `runCriterion_of_weyl` and Theorem N3 conditional on Weyl alone | 3 |

27 declarations (4 definitions, 23 theorems): 17 theorems proved, 3 assembled (`runSystem_phaseVec_iff`, `runCriterion_of_weyl`,
`n3_infinite_runs_of_weyl`), and 3 open leaves: `runSystem_phaseVec_of_odd`,
`linearIndependent_freqVec`, `exists_runBox`.  **The headline needs only the last two**;
`runSystem_phaseVec_of_odd` closes the "exact correspondence" iff, which is not on the
headline path.

**The base files are proved** (sorry-free): `WythoffGeneral` (`wy`, `WeylEquidistributionMulti`),
`WythoffAutomaton` (`xOf`, `synDiv`, `evenPhase`, `oddPhase`, Theorem N), `WythoffPisot`
(`stdRow`, `topRow`, `RunSystem`, `RunCriterion`, `n3_infinite_runs`).  Use them freely; **do not
edit them** (put helpers in the new file).  Imports: `Mathlib`, `CollatzMoonshot.WythoffPisot`.

Sources: `~/personal/tmp/amusical-agents/out/wythoff-classify.md` §1-§2 (Theorem N, the zonotope
criterion, the fresh steps of Theorem A), `wythoff-pisot.md` §1 (the half-scale run system).
The module docstring carries the paper proof.

**Setup.**  `α > 1`, `x = xOf α = β/2`, `P` monic of degree `d ≥ 2` with `P(x) = 0`,
`q_k = synDiv P x k`.  For an up-point `u = 2k`, `w_j = W^j(u) + 1`.
`phaseVec α u l` is `G_E(u)/2` for `l = 0` and `G(W^l u)/2` for `l ≥ 1`;
`freqVec α m l = (α/2)·x^l` (`l < m`); `boxCorner x ε m l = {−Σ_{j ≤ l} x^{l−j} ε_j}`;
`openBox f r = Π_l (f_l, f_l + r)`.

## Ratified, do not change

Every definition and theorem statement in the file:

* **Definitions:** `phaseVec`, `freqVec`, `boxCorner`, `openBox`.
* **Phases (all proved):** `phaseVec_zero`, `phaseVec_of_ne_zero`, `phaseVec_zero_mem`,
  `phaseVec_mem_of_odd`, `two_mul_stdRow_phaseVec`, `two_mul_topRow_phaseVec`,
  `half_iterate_eq`, `iterate_odd_iff_fresh`.
* **Correspondence:** `topRow_phaseVec_int_iff`, `stdRow_phaseVec_int_iff`,
  `iterate_odd_of_runSystem`, `irrational_xOf` (proved); `runSystem_phaseVec_of_odd` (open);
  `runSystem_phaseVec_iff` (assembled).
* **Independence:** `linearIndependent_freqVec` (open).
* **Weyl (all proved):** `measurableSet_openBox`, `volume_frontier_openBox`, `volume_openBox`,
  `setOf_fract_mem_openBox_infinite`.
* **Openness:** `half_int_pin` (proved); `exists_runBox` (open).
* **Headline:** `runCriterion_of_weyl`, `n3_infinite_runs_of_weyl` (assembled).

`WeylEquidistributionMulti` is a **literature hypothesis** (Weyl 1916 + Jordan-measurable
extension).  It stays a hypothesis; do not turn it into an `axiom`.  `RunCriterion` is now a
*conclusion* (`runCriterion_of_weyl`), exactly as stated in `WythoffPisot`.

## Rules

No `native_decide`, no axioms, no `maxHeartbeats` bumps.  Lean lines ≤ 100 characters.  **Never
change a ratified statement**; if one looks false, stop, record the counterexample in the
handoff and ask.  Commit after each proved lemma, and relabel its docstring `(drafted, NN%)` →
`(proved)`.  Notes as you go in `HANDOFF-wythoff-runcrit.md`.  Helper lemmas and definitions are
welcome (above their first use).  Build with `lake build CollatzMoonshot.WythoffRunCriterion`.

## Truth checks already run

`tmp/drafter-runcrit/check.py` (gitignored; copy of
`~/personal/tmp/amusical-agents/out/wythoff-runcrit-lean/check.py`, with `alglib.py`; uv script,
run directly, 39 s, output `check.out`; `quick` mode 7 s).  **Exact `W`**: every floor certified
by `alglib.py` (400-bit isolating intervals); phases in mpmath at 110 digits.  Members: the 6 N3
members (three class-N cubics, two real-inside quartics, the Salem quartic) and the bounded Y,
G(2,2), `x³ + x − 1`, G(3,2).  **218 checks (83 teeth), 0 failures:**

* *Identities*, for every `u ≤ 800`, any parity: `two_mul_stdRow_phaseVec` (`i = 1..4`),
  `two_mul_topRow_phaseVec`, `half_iterate_eq` (`l = 0..5`).
* *Correspondence*, every `k ≤ 6000`: `iterate_odd_iff_fresh`, both row-parity iffs,
  `runSystem_phaseVec_iff` for `n = d..d+6` (both truth values occur on every member with a run
  `≥ d`), `iterate_odd_of_runSystem` with the box dropped; bounded members show max run `J`.
* *Independence*: PSLQ (coefficients `≤ 10⁸`) finds no relation among `1, θ_0, …, θ_{d−2}`.
* *Box of followers*, scanning `k ≤ 4·10⁵` for `{kθ} − f ∈ (0, ρ)^{d−1}` around `ε*` = the
  phase vector of an actual long-run up-point: at every step the pin of `half_int_pin` on the
  actual errors predicts the parity exactly (0 contradictions over ~29 000 hits); the proof's
  worst-case error recursion is sound and every hit it certifies follows `ε*`; the explicit
  radius `r_cert = min_l μ_l/c_l` is positive (`10⁻⁴` to `4·10⁻²`) and its box has no failure.
* *Headline on `W`*: N3 members have runs of every length `≤ d + 4` after even `u ≤ 10⁵`, with
  counts roughly halving per length; bounded members have none of length `J + 1`.
* **Teeth** (each must fail and does): the row identity at `i = 0` (where `ε_0` is the even
  phase); the phase vector shifted by one; `half_iterate_eq` with `x^{l−j+1}`; one extra
  standard row in `RunSystem` (`i + d ≤ n + 1`); dropping the top row; the frequency
  `θ_{d−1}` (PSLQ finds `P`); the reducible `(t − 1)(t² + t − 1)` (dependent frequencies);
  large uncertified boxes (most hits fail: the box size matters); the wrong-sign corner
  `{+S*}`; the top-row pin with `q_0` in place of `q̃_0 = q_0 + 2a_0`.

## Paper proofs (one per open sorry)

* **`linearIndependent_freqVec`** (60-90 lines; headline path).  `PQ := P.map (algebraMap ℤ ℚ)`
  is irreducible (`Monic.irreducible_iff_irreducible_map_fraction_map`) and equals
  `minpoly ℚ x` (`minpoly.eq_of_irreducible_of_monic`), so `linearIndependent_pow x` gives
  `1, x, …, x^{d−1}` independent (`(minpoly ℚ x).natDegree = d`, `Monic.natDegree_map`).  Use
  `Fintype.linearIndependent_iff`: given `Σ_i g_i v_i = 0` over `Fin (d−1+1)` (`Fin.sum_univ_succ`,
  `v_0 = 1`, `v_{l+1} = (α/2)x^l`), substitute `α/2 = x/(2x − 1)` (`xOf_div_two_mul_sub_one`;
  `2x − 1 = 1/(α − 1) ≠ 0`) and multiply by `2x − 1`: `−g_0 + (2g_0 + g_1)x + Σ_{2≤j≤d−1} g_j x^j
  = 0`.  Apply the power independence (the coefficient vector `c_0 = −g_0`, `c_1 = 2g_0 + g_1`,
  `c_j = g_j`) to get all `c = 0`, hence `g = 0`.  Watch the `d − 1 + 1` vs `d` index casts:
  build the coefficient function on `Fin (minpoly ℚ x).natDegree` with `Fin.cast`.
* **`exists_runBox`** (150-250 lines; headline path; the only new mechanism).  Notation:
  `ε` = `phaseVec α (2k)`, `e_l = ε_l − ε*_l`, `μ_l = min(ε*_l, 1/2 − ε*_l) > 0` (from `hε.1`),
  `μ = min_{l<n} μ_l`.  Choose `r` as in the docstring (or by filters: every requirement is an
  inequality `C·r < μ` with explicit `C`; a `Finset.univ.inf'`-free route is
  `r = min (μ / (2K)^n) (min_l (1 − f_l))` with the second minimum over `Fin (d−1)` written as
  `⨅`, or just `r = μ/(2K)^n · (1 − max_l f_l)` using `Int.fract_lt_one`).  Prove by
  `Nat.strong_induction_on` the claim `∀ l < n, W^{l+1}(2k) odd ∧ |e_l| < η_l`, with three
  cases:
  * `l < d − 1`: from the box, `{kθ_l} = f_l + s` with `s ∈ (0, r)`; then
    `kθ_l + S_l − (⌊kθ_l⌋ − ⌊−S*_l⌋) = s + e_l + Σ_{j<l} x^{l−j} e_j` (`Int.fract`,
    `Int.self_sub_floor`), and the left side is in `½ℤ` by `half_iterate_eq`.  `ε_l ∈ [0, 1/2]`:
    `phaseVec_zero_mem` (`l = 0`) or `phaseVec_mem_of_odd` (IH at `l − 1`).  `half_int_pin`
    gives `s + e_l + Σ = 0`, i.e. the `½ℤ` value is an integer, so `iterate_odd_iff_fresh`
    gives oddness, and `|e_l| ≤ r + Σ x^{l−j}η_j < η_l`.
  * `l = d − 1`: `topRow` is linear; `T(ε) − T(ε*) = e_{d−1} + q̃_0 e_0 + Σ_{1≤k<d−1} q_k e_k`
    (split `Ico 1 d` at its top with `synDiv_natDegree_sub_one`).  `2T(ε) ∈ ℤ` from
    `two_mul_topRow_phaseVec` (all terms integer casts), `T(ε*) ∈ ℤ` from `hε.2.1`; pin, then
    `topRow_phaseVec_int_iff` (its `hfresh` is the IH at `l < d − 1`).
  * `l ≥ d`, `i = l − d + 1 ≥ 1`: the same with `stdRow` (`two_mul_stdRow_phaseVec`,
    `hε.2.2 i`, `stdRow_phaseVec_int_iff` with `hodd` from the IH).
  Suggested helpers: `stdRow_sub` / `topRow_sub` (linearity, from `stdRow_add_smul`), and a
  `fract` decomposition lemma `k θ + S − (⌊kθ⌋ − ⌊−S⌋) = {kθ} − {−S}`.
* **`runSystem_phaseVec_of_odd`** (60-90 lines; off the headline path).  Box: `ε_0 < 1/2` since
  `evenPhase α (2k) = ⌊kα⌋ + 1 − kα = 1 − {kα}` and `{kα} ≠ 0` (`hirr.intCast_mul`, `k ≠ 0`,
  `Int.fract_eq_zero` ⇒ integer); `ε_0 > 0` from `phaseVec_zero_mem`.  For `1 ≤ l < n`,
  `v = W^l(2k)` is odd and positive (`wy_pos_iff` iterated, `2k > 0`), so
  `phaseVec_mem_of_odd` gives `[0, 1/2)`, and `oddPhase α v ≠ 0` because
  `oddPhase α v = 0` would give `x(v + 1) = W(v) + 1 ∈ ℤ` (`wy_add_one_eq_ceil`) with
  `v + 1 ≠ 0`, contradicting `irrational_xOf` (as in
  `WythoffAutomaton.sum_coeff_iterate_eq_floor_add_one`).  Rows: `topRow_phaseVec_int_iff` and
  `stdRow_phaseVec_int_iff` (`.2`), the parities from `hodd`.

**Order of attack:** `linearIndependent_freqVec` (self-contained algebra) → `exists_runBox`
(these two close `runCriterion_of_weyl` and `n3_infinite_runs_of_weyl`) →
`runSystem_phaseVec_of_odd` (closes `runSystem_phaseVec_iff`).

Rough total: 300-450 lines.

**Stop condition.**  `CollatzMoonshot/WythoffRunCriterion.lean` sorry-free;
`lake build CollatzMoonshot.WythoffRunCriterion` green with no warnings; `#print axioms
runCriterion_of_weyl` and `n3_infinite_runs_of_weyl` show at most `propext`,
`Classical.choice`, `Quot.sound` (the Weyl hypothesis is a `Prop` argument, not an axiom).

**Out of scope (later layers):** positive *density* of the long-run up-points (the counting
version is one more `Tendsto` step from `setOf_fract_mem_openBox_infinite`'s limit); the
necessity half of the zonotope criterion; the mirror side (classify Theorem M); wiring
`CollatzMoonshot.lean`.
