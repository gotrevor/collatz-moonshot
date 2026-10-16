# HANDOFF cm-upper (RcwaHalting.lean)

Kickoff: `KICKOFF-2026-10-16-cm-upper.md`.  Branch `wip/cm-upper`.  Scoped objective:
`sorry-free:CollatzMoonshot/RcwaHalting.lean`.  Last commit: `4abc33f` (green).

## Done (all committed, green)
- §1 Lemma M: `wellQuasiOrderedLE_pi` (= mathlib `Pi.wellQuasiOrderedLE`), `revMortal_of_macro`
  (via `lapNotDown_of_lapsMixed`, `Op.act_delta`), `macroStep_transGen`, `macroStep_functional`.
- §4 Doubling: all.  Key: `fires_cases` / `double_step_cases`, `dcfg_inj`, run invariant `DInv`.
- §2 History: all.  `histWrap_lapsMixed` via constant rank (`hrank`) + integer potentials
  (`tF tH wF wH wZ`) + `walk_sum_zero`.  Generic `macroStep_of_chain` (Chain section) builds a
  `MacroStep` from `ReflTransGen` of off-boundary steps.
- §3 so far: `genc_inj`, `godel_macro`, plus helpers `dvd_enc_iff`, `enc_inc`, `enc_dec`,
  `enc_pos`, `gc`, `act_t0/t1/dec0/dec1/inc0/inc1`, `GOff`, `goff_of`, runs `g_transfer`,
  `g_mulChain`, `g_mul`, `g_dvChain`, `g_dv` (with remainder `r`), `g_wChain`, `g_w`,
  `g_rDesc`, `g_r`, `gmacro_of`.

## Open (13 sorries): §3 rest + §5
Order suggestion: `godel_halts_iff` (easy, from macro + stuck), stuck-chain, `godel_macro_sound`,
`godel_revMortal`, `godel_normalAt`, `godel_det`, `godel_rev`, `godel_lapsMixed`, then §5.

- **Stuck chain** (serves `godel_halts_of_stuck` and `godel_macro_sound`): prove
  `B.Stuck (q,v) → ∃ d, ReflTransGen (GOff B p N) (ent q, genc p J v) d ∧ (godel B p N).Stuck d`.
  Cases (B.Det makes them exhaustive): no rule from q → stuck at `grd q`; `dec i` with `v i = 0`
  → `g_dv` laps leave remainder `r = X % p i ∈ [1, p)`, then `dvIn`, `g_dvChain` m = r from
  dv 1 → stuck at `dv (r+1)` with y = 0 (all dv rules are `dec 1`); test with only `P` rule and
  `v i = 0` → `g_w` laps then `g_wChain` to `w₁ j` (x = 0, 1 ≤ j < p) stuck; only `Z` rule and
  `v i ≥ 1` → stuck at `w₁ 0` with x = 0.  Need helper: two test rules from q share the counter
  (B.Det), so `p i` agrees.
- **No macro after a stuck chain** (generic, Det): if `ReflTransGen (off-B steps) c d`, `d`
  stuck, then `¬ MacroStep B Step c b'`.  Proof: drop the first step of a partial macro run by
  determinism, head-induct along the chain.
- **godel_macro_sound**: first step is `guard` (x ≥ 1), n ≥ 2 since `grd ∉ ent`, second step from
  `grd q` is always `test 1 false` (y = 0).  Factor `x = J * ∏ p^v`: `v i := x.factorization (p i)`,
  `J := x / ∏ p^v` (`Nat.ordProj_dvd` per prime, product of coprime prime powers divides).  Then
  by_cases B steps: `godel_macro` + `macroStep_functional godel_det`; else stuck chain → contra.
- **godel_lapsMixed**: ranks `grd 0, a 1, b/mul/dv 2, w 3, r 4` (ent excluded).  On ranks 1, 3:
  x down / y up; ranks 2, 4: y down / x up.  Use ℚ potentials with per-rule STRICT inequality
  (`δ < ΔΦ` or `δ > ΔΨ`), sum with `Finset.sum_lt_sum_of_nonempty` + `walk_sum_zero` (ℤ version
  exists; make a ℚ/general ring version).  Worked-out potentials (c := 1/L, L lap length):
  * a: x Φ = a₁ 0, a₂ 1/4, a₃ -1/2, a₄ -1/4; y Ψ = a₁ 0, a₂ -1/4, a₃ -1/2, a₄ 1/4.
  * w (P = prime of q's tests, needs choice fn `tp q` + lemma `tp q = p i` via B.Det):
    x Φ(w₁ j) = -j/2, Φ(w₂ j) = -j/2 + 1/4 (p-free); y Ψ(w₁ j) = -2j c,
    Ψ(w₂ j) = -(2j+1)c + [j = P], c = 1/(2P+2).
  * b (P = `mp q`, variant `isInc q` by choice/classical), c = 1/(P+3):
    inc: y C = b₁ 0, b₂ c, mul j (j+1)c-1, b₃ (P+2)c-1; x D = b₁ 0, b₂ -c,
    mul j -(j+1)c+(j-1), b₃ -(P+2)c+P.
    dec: y C = b₁ 0, dv j jc-(j-1), b₂ (P+1)c-P, b₃ (P+2)c-P; x D = b₁ 0, dv j -jc,
    b₂ -(P+1)c, b₃ -(P+2)c+1.
  * r (P = `rp s`, lemma via B.Rev), c = 1/(2P+2): y C(r₁ 0) 0, C(r₂ 0) c,
    C(r₁ j≥1) (2+2(P-j))c-1, C(r₂ j≥1) (3+2(P-j))c-1; x D(r₁ 0) 0, D(r₂ 0) -c,
    D(r₁ j≥1) -(2+2(P-j))c+(P-j), D(r₂ j≥1) -(3+2(P-j))c+(P-j+1).
  All checked by hand per rule (see this lap's transcript reasoning); `j = P ≥ 2` side conditions
  come from the rule constructors.
- **godel_det / godel_rev**: 30² case bash like `histWrap_det` (`cases h₁ <;> cases h₂ <;>
  simp only [GState.*.injEq, reduceCtorEq] at hsrc`, then `case` per surviving pair).  Need
  helper facts from B.Det: a non-test rule from q is the only rule from q; tests from q share the
  counter; same-symbol tests from q coincide; from B.Rev: tests into s share the counter (for
  `rDec` targets).

## Infra notes
- Scratch files `tmp/cmu/*.lean` (namespace `CollatzMoonshot.RcwaHalting.S` to avoid clashes);
  `tmp/cmu/bin/chk FILE` retries `lake env lean` on transient host "Too many open files".
- Gotcha: `![a, b] 0` inside `decide (0 < _)` leaves a `Nat.decLt 0 (![a,b] 0)` instance after
  simp that no lemma matches; state Fin-2 lemmas over `v : Fin 2 → ℕ` / `gc x y` and pass
  `decide_eq_true (by omega)` explicitly.
- `hoff_of`/`goff_of` take target state & counters as implicit plain variables so `rfl` can
  assign them (projections of metavariables can't be assigned).
