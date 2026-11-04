# Natural density for Tao 2019 along Remark 1.16, and what `StageWordLaw` actually needs (2026-11-04)

Scout at the paper level.  No Lean edits, no commits.  Tao numbering is arXiv v5 (`~/personal/papers/tao-2019-almost-all-orbits.pdf`).  Tags: **[paper]** an argument I wrote or checked by hand, **[source]** read in a named document or Lean file, **[numeric]** from `experiments/conjugacy/affine_mixing.py`, output in `affine_mixing.out`.  Throughout `λ = log₂ 3`, `θ = λ/2`, `C* = 1/(1 − θ) = 4.8188…`, `U_y = Unif(odd ∩ [y, 2y])`, `N_y` is Tao's log-uniform law on `[y, y^α]`, `ν_x = Pass_x(N_{x^α})`.

## Bottom line

1. **The Remark 1.16 route is not a wall.**  The strengthened 1.14 follows from Tao's own (7.5) in one line plus a bookkeeping pass through §6; a second ingredient is needed that the remark's wording does not separate out, an Archimedean renewal theorem along `log₂ 3`.  Two write-ups carry it through to natural density (§4): Allikvere (Zenodo, unrefereed, not Lean-checked) and Mazur (ProofAtlas, about 50k lines of Lean over a 124k-line Tao port; I read the statements and did not replay it).  My independent derivation agrees with both on the mechanism and on the limit law.  Confidence that natural-density Prop 1.11 is true as stated: 92%.
2. **`StageWordLaw C` for `C ≤ 4` does not need Remark 1.16 at all.**  It sits at height `N^{0.17}`, where every exceptional set has power-saving density, and for those Inselmann's pullback lemma (arXiv:2402.03276, Lemma 2.16) transfers Terras's bound along the orbit with no mixing and no Fourier analysis (§7).  Eight windows reach `4.07 k`.  So normality of `𝒞_C` for `C ≤ 4` (`normal_of_stageWordLaw`) reduces to a short elementary argument.  Confidence: 88%.  This is the main correction to the framing of the brief.
3. **Where Remark 1.16 is really needed**: arbitrary targets `f → ∞`, and so the natural-density `timeLaw_upper`.  There the known exceptional set saves only a power of `log`, and pullback gives nothing.  (Inselmann reaches every fixed power and some subpolynomial targets.)

**Weight.**  Item 2 would turn the `1 < C ≤ 4` row of the §15 table in the conjugacy note from open to a theorem, and make the `C ≤ 4` log-density results corollaries.  It touches nothing past `C*`, nothing about any single orbit, and nothing about Collatz itself.

## 1. Where logarithmic density is used in §5

The only displays that need the form of the density are these **[paper]**.

- **After (5.19).**  The event `Aff_a(N_y) = M` pins `N = 2^{|a|}(M − F)/3^{n−m₀}`, so its log-uniform mass is `(1/normaliser) · 2^{−|a|} · 3^{n−m₀}/(M − F)`.  This factorisation is exact.  `2^{−|a|}` is the Geom(2) weight, and the rest is free of `|a|` once `M − F = (1 + O(x^{−c}))M`.  It is what produces (5.22), with `c_n` of (5.23) independent of `|a|`.
- **The range check after (5.19).**  From (5.9), (5.11): for `n ∈ I_y` and `a ∈ A^{(n−m₀)}`, `N` lies in `[y, y^α]`, so the window indicator is dropped.  This needs the window's log-width `(α−1) log y` to exceed the fluctuation `log^{0.6} x`.
- **The sum over `n`, after (5.21).**  (5.20) gives the same `Z` for every `n ∈ I_y`, and `#I_y ≈ ((α−1)/log(4/3)) log y` cancels the normaliser, leaving `P = (2/log(4/3)) Z + O(log^{−c} x)`.  No equidistribution of `n log₂ 3` is consulted, because all `n` get equal weight.

Tao's own diagnosis is at the end of §1.2: "the multiplicative inaccuracy of `exp(O(n^{1/2}))` in (1.17) is the main reason why we work with logarithmic density" **[source]**.  (1.19), Prop 1.9 via (5.4), Prop 5.2's event identities, and Lemma 5.3 are not specific to log density, though (5.16) (the source of the `log^{−c}` rate) comes from trimming the window edges.

**The brief's guess is right but incomplete.**  "Log-uniform is invariant under the multiplier, which absorbs `|a|`" describes the first two bullets, and the first is exact rather than approximate.  It omits the third, which is the one that creates new work: under `U_y` the same three steps become a sum along a line in the `(n, s)` plane, and that needs a renewal theorem.

**Natural-density Prop 1.11, precisely [paper].**  For `y ∈ [x^α, x^{α²}]`: `P(T_x(U_y) = ∞) ≪ x^{−c}` and `d_TV(Pass_x(U_y), ν_x) → 0`, at rate `log^{−c} x` if wanted.  The limit law is the same `ν_x`, not merely some law independent of `y`.  The exact formula is

    P(Pass_x(U_y) ∈ E) = Σ_n Σ_s Σ_X c_{n,s}(X) · P(|a| = s, F_{n−m₀}(a) = X) + small,
    c_{n,s}(X) = 3^{n−m₀} Σ_{M ∈ E′, M ≡ X} (1/M) ψ(2^s M / (3^{n−m₀} y)),   ψ(t) = 2t · 1_{[1,2)}(t).

For fixed `n, M` only one `s` survives, up to `±1`.  The natural-density input is thus forced to be about one exact value of `|a|` per `n`.

Variants: Allikvere's Theorem D has `Unif[y, y^α]` on both sides of (1.20); Mazur's `NDM2Bounds` has `‖Pass_x(U_y) − Pass_x(L_y)‖₁ ≤ C (log x)^{−d}` for all `d < 5/143`, on the block `[y, y^α]` **[source]**.  Natural density needs only dyadic stages or top blocks: `#{bad n < 2^k}/2^k → 0` iff `#{bad n ∈ [2^{k−1}, 2^k)}/2^{k−1} → 0`.

## 2. The mixing statement

**Prop 1.14\* (joint form).**  For all `1 ≤ m ≤ n` and every `A`,

    Σ_s Osc_{m,n}( P(|a| = s ∧ F_n(a) ≡ Y mod 3^n) )_Y  ≪_A  m^{−A},

equivalently `d_TV((|a|, F_n), (|a|, F_n + Unif(3^m Z/3^n Z))) ≪ m^{−A}` **[paper]**.  The `Aff` map is determined by `(|a|, F_n)`, so this is what "the entire random affine map" means.

**Conditional form.**  For `|s − 2n| ≤ C√(n log n)`: `Osc_{m,n}(F_n | |a| = s) ≪_{A,C} m^{−A}` for `n^{1/4} ≤ m ≤ n` (Allikvere Theorem C and Prop "telescoping") **[source]**.  It is equivalent up to the polynomial factor `1/P(|a| = s)` in that window.  The tail of `s` is removed by Chernoff.

**Weakest sufficient statement [paper, 80%].**  What §5 consumes along each line is

    (W)  sup_u Σ_n P(|a_n| = ⌊nλ + u⌋) · Osc_{m₀, n}(F_n | |a_n| = ⌊nλ + u⌋) → 0,

with `n` within `√(log x) · polylog` of `u/(2 − λ)`.  The weights sum to about `1/(2 − λ)`, since the `√n` values of `n` cancel the `1/√n` of the local limit theorem.  So a conditional oscillation that is `o(1)` on central lines suffices; it need not beat `1/√n`.  A crude pass through Lemma 5.3 asks for joint oscillation `≪ log^{−0.7−c} x`, which (W) improves.  This was derived but not written out in full, and the proved bound `m^{−A}` makes the distinction moot.

**Rate.**  It depends on how the chain is run.
- Splice (Mazur's structure, my derivation): `U_y → ν_x` once, then Tao's proved log chain.  The transport is used once, so **any `o(1)`** suffices for a density statement **[paper, 85%]**.
- Chain in `U` throughout (Allikvere's structure): the Tao §3 requirement `O((log log x)^{−1−c})`.

**Renewal, the second ingredient.**  Write the main term with `a = (a′, a″)`, `a″` the `m₀` coordinates that determine `F mod 3^{m₀}`.  They are independent of `a′`, and the inner sum is `R(u) = Σ_k E ψ(exp(u + |a′_k| log 2 − k log 3))`.  This is the renewal measure of a two-sided walk of drift `log(4/3)`, so `R(u) → (1/log(4/3)) ∫ψ(e^t)dt = 2/log(4/3)` as `u → −∞`, which is exactly the constant in Tao's formula after (5.21).  That cross-check is why the limit is `ν_x` **[paper]**.  Blackwell needs only that the walk is non-arithmetic, i.e. `log₂ 3` irrational (`irrational_logb_two_three` is in the repo).  A rate needs an irrationality measure: Allikvere uses Rhin's `μ ≤ 8.616` (rate `1/29`), Mazur Rhin's `13.3` line (`d < 5/143`) **[source]**.  So Baker-type input is needed only for quantitative statements, which sharpens Allikvere's remark that natural density "consumes" transcendence input **[paper, 80%]**: their second use of it (endpoint jitter, their Lemma "window-replacement") I believe can be replaced by the thin-band count in Lemma 5.3, but I did not write that out.

## 3. Does §6-§7 extend?  Yes, at `p = 1/2`, for central `s`

Take any `h: ℕ → ℂ` with `|h| ≤ 1`: `h = e^{iθ·}` or `h = 1_{s}`.

| Step | With the twist `E[χ(X_n) h(|a|)]` | Status |
|---|---|---|
| Pair sums, (7.4) | `|a| = Σ b_j` (plus `a_n` if `n` is odd) is measurable with respect to the conditioning `σ`-algebra | survives **[paper]** |
| Triangle inequality, (7.5) | `≤ ‖h‖_∞ · E ∏|f(3^{2j−2} 2^{−b[1,j]}, b_j)|`, because `h` factors out of the conditional expectation | survives |
| Lemma 7.2, white points | same `f`, conditioned on `b = 3` | untouched |
| §7.2, triangles | the field `θ(j, l)` depends on `ξ` alone | untouched |
| §7.3-7.4, `Hold`, Lemma 7.7, `Q` recursion | all for the **unconditioned** walk; the bound in (7.5) no longer mentions `h` | untouched |
| §6, head | `E_k, B_k, C_{k,l}`, Corollary 6.3, Plancherel (6.11) | untouched: `s` constrains only the tail |
| §6, tail factor | `E[χ′(X_{n″}) h(|a_{[1,n″]}| + c)]`, `n″ = n − k − j − 1 ≫ n`, with the remaining `j` coordinates fixed by conditioning | (7.5) again at `n″` |
| §6, telescope | reduction mod `3^{n′}` convolves `s` with an independent tail, and TV contracts | survives |

**Where positivity is used.**  Only at (7.5), and only after the twist has left: Tao remarks that Prop 7.3 is entirely "non-negative" **[source]**.  A complex twist costs nothing, since it is `b`-measurable of modulus 1: `sup_θ |E χ e^{iθ|a|}| ≤ E∏|f| ≪_A n^{−A}`.  For `h = 1_{s}`, positivity of `∏|f|` drops the indicator: `|E χ 1(|a| = s)| ≤ E∏|f|`, uniformly in `s`, and the conditional version pays `1/P(|a| = s) ≤ n^{1/2 + C²/4}` **[paper; also Allikvere Theorem B, source]**.  This is a one-line proof.  `SliceDecay.lean`'s docstring already states the `θ` case as a corollary of Tao's bound, so the 35% in note §11 for `TwistedSyracCharDecay` is out of date.

**A real tilt is not needed in the central window**, because at `p = 1/2` the slice has polynomial mass there.  The real tilt, `Pascal(p)`, is what `pascal_damping_decay` handles.  It is required for slices with `n/s` away from `1/2`, which C1 needs and this route does not.  That the note's line 1026 says "only `p = a/j`" is about all slices; for central `s`, Tao at `1/2` suffices.  `sliceCharDecay_of_pascalDampingDecay` is axiom-clean, verified today, on the same object.

**Prior repo work, for what it teaches.**
- `WeakDecayTwistBound.lean` twists by the *start's* residue mod `3^k`, a different twist.  Its `3^k` Fourier-weight loss has no analogue here.  The neighbouring `OverPrecSliceCharDecay` (partial damping with padded pairs) has the same shape as the `n″ < n` step above.
- `FourierTraps.lean` is the 2-adic mirror walk, shallower than its triangles.  Here the walk has slope `16/4 = 4` against `log₂ 9 = 3.17`, so the trap does not arise.
- `truncatedSyracMixing_of_sliceCharDecay` is still a `sorry` (`sorryAx` printed today, which also serves as a control for the axiom check).  It is the §6 pass for all slices in `[1/4, 11/20]`.  The central case above is easier, and Mazur's `exists_ndSection6FixedSplitOscillation_sq_le` is a Lean version of it **[source]**.

## 4. Literature

`papers followups` returned HTTP 429 twice.  Search then opened pages; everything below was read at the source unless marked.

**J. Allikvere, "Almost all Collatz orbits attain almost bounded values in natural density" v2, 22 Jul 2026, [doi:10.5281/zenodo.21340150](https://doi.org/10.5281/zenodo.21340150), unrefereed, AI use disclosed.**  Proves `Col_min(N) < f(N)` in natural density for every `f → ∞`, with exceptional ratio below `x` for fixed target `N₀` at most `O((log N₀)^{−1/29} + x^{−1/2000})`, and a clock of `ln N/ln(4/3) + O(ln^{0.8} N)` Syracuse steps.  How:
- Theorem B is sum-conditioned 1.17, by exactly the (7.5) argument above.
- Theorem C and the telescope are sum-conditioned 1.14, via §6 with the tail conditioned on `T = s − l`.
- Lemma "tilt": `d_TV(law(a₁…a_m | s), Geom(2)^m) ≪ (m log n/n)^{1/2}`.  This is the numerics' Part E.
- Theorem D is (1.19), (1.20) for `Unif[y, y^α]`.  `I_y` is replaced by a top-extended interval, because the uniform mass sits at the top of the block.
- The fibre sum uses `3^{−n′} C(s−1, n′−1) = 2^t P(s_{n′} = s)`, a hockey-stick identity that resums the top of each row, and a Gaussian sum over `n′` weighted by `2^{−{n′λ+u}}`, equidistributed by Erdős-Turán and Koksma.
- Then Tao §3 verbatim in the uniform measure.
- It works at coarse scale `m₁ = log^{0.4} x`, which is why the tilt lemma is needed.  Working at `m₀`, as in §2 above, the `a″` expansion replaces it.

**L. Mazur, "Natural-Density Almost-Bounded Collatz Orbits in Logarithmic Time" v2, 21 Jul 2026, [ProofAtlas](https://proofatlas.ai/formalizations/natural-density-log-time-collatz/), AI use disclosed.**  Clocks `145 log N` (Syracuse) and `436 log N` (raw).  Transport `NDM2Bounds` is `‖L(Pass_x U_y) − L(Pass_x L_y)‖₁ ≤ 384256 (log x)^{−d}`, for `d < 1/20, d < 1/(2κ)`, with `κ = 14.3` from Rhin, reconstructed from Padé in Lean.  It is band-local: every roughly `e`-fold band in the block, flat or harmonic, is within `7 (log B)^{−d}` of a common profile.  Then a top-block splice, (47) of the paper: bad count `≤ discarded + 2(E_sched + E_pass + E_target)`, with `E_target` the log-density chain.  The Lean carries the same mechanism: `exists_ndSection7FiberNumerator_polynomial_decay` is `‖E[χ 1(|a| = L)]‖ ≤ C/n^A` uniformly in `L`, with the comment "inserts the fixed-total selector before any absolute value is taken", and `exists_ndSection6FixedSplitOscillation_sq_le` is the §6 pass **[source]**.  The bundled evidence JSON records axioms `propext, Classical.choice, Quot.sound`; I did not replay the build.  Lean `v4.30.0-rc2` and Mathlib `5450b53`, against this repo's `v4.33.1` and `0df444a`, with its own Tao port, so `require` does not apply as is.  The paper names frozen commit `f386357…` and the site's ZIP is `ca3dd0d…`; I read the latter.

**Tao, blog comment, 23 Aug 2026** ([comment 694077](https://terrytao.wordpress.com/2019/09/10/almost-all-collatz-orbits-attain-almost-bounded-values/comment-page-5/#comment-694077)): "Apparently, there are now some AI-generated solutions to the natural density version of my result; if they check out…".  So the author has not vouched for them, as of that comment.

**M. Inselmann, ["An Approximation of the Collatz Map…"](https://arxiv.org/abs/2402.03276) v3, 13 Aug 2024.**  Theorem 1.1: for every `ε > 0`, on a natural-density-one set, `(√3/2)^k m^{1−ε} ≤ T^k(m) ≤ (√3/2)^k m^{1+ε}` for all `k ≤ log₂ m/(1 − θ)`.  Theorem 1.6: the same range for the count of odd letters.  Mechanism in §7.  He says the method seems unlikely to reach the full `f → ∞` statement.

**Also opened.**  Siegel-O'Dwyer [arXiv:2609.33018](https://arxiv.org/abs/2609.33018): number rings, abstract is logarithmic density and avoids Fourier decay; abstract only.  Gonçalves-Greenfeld-Madrid [arXiv:2111.06170](https://arxiv.org/abs/2111.06170), §1.3: log density for generic `f`, a Korec-type natural-density result.  Chang [arXiv:2603.11066](https://arxiv.org/abs/2603.11066): no natural-density upgrade; the search summary's "barrier" wording is about every-orbit statements.  **Not opened:** Kalafatelis (Preprints.org 202604.0411), cited by Mazur as a uniform-window shell-kernel reduction.

## 5. Numerics (`affine_mixing.out`)

**Exactness.**  Rows `P(|a| = s, F = Y)` are exact up to float rounding, for `n ≤ 13`.  Only the unconditioned law truncates, at `a_i ≤ 60`.

**Known-answer controls [numeric], all pass.**  Tao's tables at `n = 1, 2`, to `0.00e+00`.  `sup_ξ |E χ(F_n)|` matches the repo's `twisted_charfn.py`: `0.1293, 0.0609, 0.0383, 0.0319` at `n = 5, 8, 10, 11`; `sup_{ξ,θ}` at `n = 8` is `0.0662` against the repo's `0.066`.  Unconditioned `Osc_{m,13}` falls with `m`: `0.835, 0.715, 0.621, 0.547, 0.484, 0.429, 0.379, 0.332, 0.287, 0.241, 0.194, 0.140`.  It rises slowly with `n` at fixed `m` (`m = 1`: `0.70 → 0.835`), which Prop 1.14 allows.  This shows decay in `m` at finite `n`, not the asymptotic rate.

**Conditioned `Osc_{m,13}(F | s)`, measured against a random-map null** (same coarse law, atoms hashed uniformly into lifts):

| s | atoms/cell | m=1 | 2 | 3 | 4 | 6 | 8 | 10 | 12 | null (m=6) |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 21 = 2n−sd | 0.08 | 1.78 | 1.69 | 1.57 | 1.44 | 1.23 | 1.05 | 0.86 | 0.56 | 1.26 |
| 26 = 2n | 3.26 | 0.756 | 0.608 | 0.503 | 0.419 | 0.300 | 0.221 | 0.176 | 0.138 | 0.322 |
| 31 = 2n+sd | 54 | 0.481 | 0.326 | 0.228 | 0.162 | 0.086 | 0.049 | 0.036 | 0.030 | 0.084 |
| 32 = 2.5n | 89 | 0.450 | 0.295 | 0.200 | 0.138 | 0.069 | 0.038 | 0.027 | 0.023 | 0.066 |
| 36 = 2n+2sd | 523 | 0.359 | 0.206 | 0.125 | 0.077 | 0.032 | 0.015 | 0.010 | 0.009 | 0.028 |
| 39 = 3n | 1698 | 0.316 | 0.164 | 0.092 | 0.052 | 0.019 | 0.008 | 0.005 | 0.004 | 0.015 |

Reading **[numeric]**:
- Where the row has atoms to spare, oscillation falls by a factor of about `0.5-0.7` per `m`, consistent with the `exp(−cm)` of Remark 1.15, down to a floor set by the atoms.
- At fine scales it sits **below** the random-map null, by up to a factor of about 3, so the true map spreads more evenly than a random one.
- Across `s` the curves are ordered by atoms/cell, with no outlier and no parity effect (31 and 32 are in order, adjacent).

**`n` is too small to test the claim at central and lower `s`.**  `s = 2n − sd` has fewer than one atom per cell until `n = 31`, and `s = 2n` fewer than 100 until `n = 27`, so those rows cannot be flat at `n = 13` under any hypothesis.  For the same reason `JointOsc` is flat in `n` (`0.997, 0.867, 0.771, 0.695, 0.573, 0.475, 0.391, 0.263` at `n = 13`) and exceeds the unconditioned value.  So numerics support the rich rows only.  They do not test uniformity across the central window.

**Part D: the one-line step, tested.**  `max_s |E χ 1(|a| = s)| ≤ max_θ |E χ e^{iθ|a|}| ≤ E∏|f|` holds exactly at `n = 8, 10, 12`, on the worst `ξ` and on small `ξ`.  At `n = 12`, `ξ = 2^{15}`: `0.0111 ≤ 0.0351 ≤ 0.2858` (the last is a truncated lower estimate, so a violation would still show).  The worst `ξ` are powers of 2, as the note's §11 found.

**Part F: renewal, with teeth.**  `R` normalised to limit 1, min and max over `u`: along `θ = log₂ 3`, `0.9942-1.0067` at `D = 20` and `0.9993-1.0007` at `D = 1280`.  Rational controls do not converge: `θ = 3/2` stays at `0.8367-1.1748` and `8/5` at `0.9323-1.0694` for every `D`.

**Part G: the end-to-end statement, directly.**  `Pass_x`, `x = 2^{12}`, `2·10⁷` samples per law, full L1 on all 2048 odd locations against a log-uniform reference on `2^{32}..2^{48}`.  Two-sample null: `0.0087`.  Teeth: `U_y` at `y/x = 2^{0.25}, 2, 4, 8` gives `0.539, 0.259, 0.117, 0.030`, a near log window gives `0.0327`, so the instrument sees non-stabilised laws.  From `y/x = 2^{14}` to `2^{44}`, including tenths of a dyadic step around `2^{20}` and `y = 3^{20}, …, 3^{35}`, L1 stays in `0.0086-0.0097`, at the null, with no phase effect.  Same for location mod 81 (`0.0017-0.0022`, null `0.0021`) and bit-length.  The largest `y` drop up to 2% of orbits at a `2^{62}` overflow guard, which is noted in the output and changes nothing visible.  This is one small `x` and a direct check of the conclusion, so it is evidence and not an asymptotic test.

**Part H: pullback, §7 below.**

## 6. Attempts to refute

Nothing survived.  What I tried:

- **Conserved quantity between `s` and `F`.**  `F·2^s = W(S) = Σ_j 3^{j−1} 2^{b_j}`, with `b` from a uniform `(n−1)`-subset of `[1, s−1]`, an exact description.  The top digit of `F` carries `3^{n−1} 2^{−s}`, which depends on `s mod 2`.  But it is a translation inside the coset, and the conditional oscillation is translation-invariant.  Parity of `s` is therefore harmless **[paper]**, and the rows show no parity effect **[numeric]**.  `F mod 3 ≠ 0` for every `s`: a coarse constraint, already in the main term.
- **3-adic correlation.**  It exists: `law(F mod 3^k | s)` differs from `Syrac(3^k)`.  At `s = 2n ± √(2n)`, `k = 3`, the L1 distance falls from `0.374` to `0.252` as `n` goes from 6 to 13, ratio `0.67` against `√(6/13) = 0.68` **[numeric]**.  So it is a vanishing tilt of size `(k/n)^{1/2}`, as Allikvere's Lemma "tilt" states, and is not conserved.  It is carried by the `a″` expansion in the main term rather than lost.
- **2-adic correlation.**  `W(S)` is odd because its lowest term is `3^{n−1} · 2⁰`, so `N = (2^s M − W)/3^n` is automatically odd.  `N mod 2^{s+1}` is determined by `a`, and CRT against `3^{n′}` holds with room since the modulus `≪ M`.  There is no constraint **[paper]**.
- **A stage where natural density fails.**  The only `y`-dependence left in the main term is `R(u)`, and `sup_{u ≤ −D} |R(u) − limit| → 0` by non-arithmeticity, which is uniform in `y` **[paper]**.  This would break exactly if `log₂ 3` were rational, as the Part F controls show.  It is not.  Part G scans dyadic and `3^j` values of `y`, including fractional steps, for a Benford phase effect.
- **Could the two write-ups be wrong?**  I re-derived the main term independently, and it lands on Tao's constant `2/log(4/3)`.  The Lean is one more independent check (not replayed).

**One thing did survive as a correction**: the brief treats Remark 1.16 as the route to `StageWordLaw`, and it is not the shortest.  §7.

## 7. `StageWordLaw` for `C ≤ 4` without mixing

**Pullback lemma (Inselmann Lemma 2.16, re-derived here [paper, 95%]).**  If `|B ∩ [1, X]| ≤ X^{1−D}` for all `X`, then `{m : T^{⌊log₂ m⌋}(m) ∈ B}` has the same kind of bound, with a smaller positive exponent.

Proof, in my simpler form.  Let `k = ⌊log₂ m⌋`, `a` the number of odd letters among the first `k`, `M = T^k m`.  Then `M = 3^a m/2^k + offset`, `offset ≥ 0`.

- Off an exceptional set of power-saving size, `k/4 ≤ a ≤ 0.6 k` and `offset ≤ 2^{εk}`, because each term of the offset is `3^{c}/2^{ℓ+1}` with `c` the odd letters in a suffix of length `ℓ`, and letters are fair bits (Terras, Hoeffding).  Long suffixes give terms below 1, and suffixes shorter than `ε′k` give at most `(3/2)^{ε′k}`.
- Given `M` and `a`, `m` is pinned to an interval of length `≤ offset · 2^k/3^a`, and `M < 3^{a+1}`.  This is the only structural input, and it is Archimedean: no 3-adic mixing appears.
- Hence `#{good m : M ∈ B} ≤ Σ_a |B ∩ [1, 3^{a+1}]| · (2^{εk} 2^k/3^a + 1) ≪ k · 2^{k+εk} · 3^{−kD/4}`, using `3^a < 2^k` to absorb the `+1`.  The fraction is `≤ 2^{εk − cDk}`.  Choose `ε ≪ D`; the final exponent is the minimum of this and the exception's, small but positive.

Log-density methods could not use this because Tao's exceptional sets save only `log^{−c}`.  Here the targets are Terras events, whose exception is `2^{−Dk}`.

**The word law [paper, 88% overall].**  Fix `u, δ`.  Let `S₀` be the `m` whose first `size m` letters have the right frequency of `u` and of the letter `1`, within `δ`, on every prefix of length `≥ η size m`.  By the Terras bijection and Chernoff on `|u|`-spaced blocks, the complement has density `≪ X^{−D}`.  Set `S_{j+1} = S₀ ∩ {m : T^{⌊log₂ m⌋} m ∈ S_j}`, each with positive exponent by pullback.  For `m ∈ S_J`, the orbit splits into windows `[t_j, t_{j+1})` of `size(M_j)` letters of `M_j = T^{t_j} m`, each good.  The height identity (lower bound only) gives `size(M_{j+1}) ≥ (θ − ε′) size(M_j)`.  So `J` windows cover `(1 + θ + … + θ^{J−1} − O(ε′)) k` letters: `J = 8` gives `4.069 k`, enough for `C = 4`, with `J` windows contributing `J |u|` boundary error.  Hence `BadStart C u δ` has density `0`, i.e. `StageWordLaw C` for `C ≤ 4`, and `normal_of_stageWordLaw` (axiom-clean, verified today) gives normality.  `J` is a bounded constant, so no rate from any chain is needed.  Every `C < C*` follows the same way.

**Measured [numeric, Part H].**  Rare Terras events are not amplified at all: `P_m(T^k m ∈ B)/P_uniform(B)` is `0.98-1.02` for `k = 24, 32, 40` over `B` with mass down to `10^{−3}`, against a proved bound with a `2^{εk}` loss.  Control with teeth: the law of `M` is genuinely non-uniform (multiples of 3 have probability `0`; top `0.1%` of `M` carry `5.2%` of the mass at `k = 24`; one `M` has `410` preimages against `(2/√3)^k = 31.6`).  So a set adapted to `M`'s law could be amplified, and the proof's loss is real for sets without power-saving.  Stage frequencies of `11` over the first `C k` letters, fraction off by more than `0.02`, 500 starts: at `C = 4`, `0.490, 0.158, 0.002` at `k = 100, 400, 1600`; at `C = 5`, `0.678, 0.452, 0.230`; at `C = 6`, `0.842, 0.874, 0.986`.  `C = 6` is the control with teeth: its cycle tail is about 20% of the letters and moves the frequency by about `0.05`.  `C = 5` has no teeth at this threshold: its tail is about 3.6% of the letters, moving the frequency by about `0.009 < 0.02`, so its falling column says nothing against `not_normal_of_five_le`.

**The window chain, measured.**  `t_{j+1} = t_j + size(T^{t_j} m)`, 40 starts: at `k = 4000`, `t_8/k = 4.074` against the prediction `4.069`, and `t_9/k = 4.231` against `4.225`.  So `J = 8` clears `C = 4` by a thin margin and `J = 9` by a comfortable one.

**What the note's obstruction was.**  §15 says the obstruction is distance from `k`: letters past `k` are determined by the `k` bits of `n`, so slice laws see nothing once `t − k` passes `log k`.  That is right about slices and residues.  Pullback goes around it, by using the size of `M` rather than its residue.

## 8. Node graph

**Branch I, elementary, reaches `StageWordLaw` for `C ≤ 4` (and height law, any `C < C*`).**

| Node or edge | Status | Confidence | Weakest joint |
|---|---|---:|---|
| P1: Terras word set `S₀` has power-saving density | [paper], Terras in Lean | 98% | Chernoff on spaced blocks |
| P2: pullback lemma | [paper] + [source] Inselmann 2.16 + [numeric] | 95% | offset bound on a power-saving set |
| P3: `J = 8` windows cover `4k`, exponents stay positive | [paper] | 92% | bookkeeping, with margin `4.069` against `4` shrunk by `ε′`; if tight, `J = 9` gives `4.225` |
| P4: `P1-P3 ⇒ StageWordLaw C`, `C ≤ 4` | [paper] | 90% | even starts and `Nat.size` conventions in `BadStart` |
| `StageWordLaw ⇒ Normal` | Lean, axiom-clean, verified 2026-11-04 | - | - |

**Branch II, Remark 1.16, reaches natural-density `f → ∞` and the natural-density `timeLaw_upper`.**

| Node or edge | Status | Confidence | Weakest joint |
|---|---|---:|---|
| N1: Tao (7.5), Prop 7.3 | Lean in `TaoCollatz` (`charFn_decay_at`) | - | - |
| N1 ⇒ N2: fixed-total numerator `‖E χ 1(|a| = s)‖ ≪ n^{−A}`, uniform in `s` | [paper] one line; [source] Allikvere B, Mazur Lean; [numeric] Part D | 98% | none |
| N2 ⇒ N3: Prop 1.14\* | [paper] §3; [source] Allikvere C, Mazur Lean | 93% | bookkeeping of `s` through `E_k`, `k`, `l`; tail reduction to `n″` |
| N4: renewal `R(u) → 2/log(4/3)` | [paper]; [numeric] with rational controls | 97% qualitative, 90% with rate | smoothing `ψ`'s jumps |
| N3 + N4 ⇒ N5: `d_TV(Pass_x(U_y), ν_x) → 0` | [paper] sketch; [source] two write-ups; [numeric] Part G | 88-92% | fibre bookkeeping: replacing `M − F` by `M` in the indicator, partial rows, the Lemma 5.3 analogue |
| N5 + Tao log chain ⇒ natural Theorem 1.3 | [paper]; [source] Mazur (47) | 95% given N5 | none |
| N5 + note §16 chain ⇒ natural-density orbit laws, including `StageWordLaw` | [paper] | 85% given N5 | re-running `G_x` read-off with `U_y` at the top (Terras is exact there) |

**Recommendation.**  For `StageWordLaw`, Branch I: small, self-contained, and mostly lemmas the repo already has (`height_identity`, the Terras bijection).  For `timeLaw_upper` in natural density, Branch II would mean a port of Mazur or a re-proof on `TaoCollatz`, and it is a separate decision.

## 9. Not checked

- I did not replay Mazur's Lean build, and did not read his appendices line by line, nor Allikvere's §D.1 (Lemma "window-replacement") in full.  Neither has been refereed, as far as I found.
- (W) and "Baker not needed qualitatively" are my derivations and appear in neither source in that form.
- I did not write the Lean.  `BadStart`, `WindowMatch` and `tstep` were read, and `wdev_shift` is the window shift P4 needs, but nothing was checked at the level of a statement that would compile.
- Inselmann's paper is arXiv v3; I did not check for journal publication.  I read Lemmas 2.13-2.16 and re-derived the pullback in the shorter form of §7.
- Numerics do not test the central window at any `n` where it could fail (§5).

**Stale statements in the conjugacy note, flagged and not edited:** §16 ("`StageWordLaw` … is open", "what logarithmic density does not reach"), the §15 table row for `1 < C < C*` (70%), the obstruction paragraph in §15, and §11's 35% for `TwistedSyracCharDecay`.

Sources opened: [Tao blog comments](https://terrytao.wordpress.com/2019/09/10/almost-all-collatz-orbits-attain-almost-bounded-values/), [Allikvere](https://doi.org/10.5281/zenodo.21340150), [Mazur formalization](https://proofatlas.ai/formalizations/natural-density-log-time-collatz/), [Mazur paper](https://www.proofatlas.ai/papers/natural-density-log-time-collatz/Mazur_Natural_Density_Collatz_Orbits_in_Logarithmic_Time_v2.pdf), [Inselmann](https://arxiv.org/abs/2402.03276), [GGM](https://arxiv.org/abs/2111.06170), [Siegel-O'Dwyer](https://arxiv.org/abs/2609.33018), [Chang](https://arxiv.org/abs/2603.11066).
