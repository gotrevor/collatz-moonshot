# KICKOFF 2026-10-16: Theorem C machine core, completion orbit formula and Lemma M

Repo `collatz-moonshot-amusical-round2` (branch `wip/rcwa-machine`): close every `sorry` in
`CollatzMoonshot/RcwaMachine.lean`.  Sources: research notes `undec-lemma.md` (§2 Lemma C, §4
Lemma M) and `undec-r25.md` (§3 repairs, §6 completion lemma).

## Ratified, do not change

Every statement and definition in `RcwaMachine.lean`: `fwd`, `Src`, `Snk`, `Diverges`,
`NoBiInfinite`, `EndToStart`, `lineEmb`, `nu`, `completeFun`, `complete`, `Orbits`, `OffRun`,
`LapNotUp`, `LapNotDown`, `MacroStep`, `TwoCounter.Rule`, `TwoCounter.Rule.Fires`,
`TwoCounter.Step`, `TwoCounter.LapsMixed`, and all theorem statements.  No `native_decide`, no
new axioms.  Lean lines ≤ 100 characters.  Do **not** edit `RESEARCH-*.md`.  Commit after each
proved lemma.  Notes as you go in `HANDOFF-rcwa-machine.md`.  Helper lemmas and definitions are
welcome (put them above their first use).

## Paper proofs (Ren)

Notation: `σ := complete f τ θ`, `ν := nu f θ`, `ι := lineEmb f`; "position `p`" means the line
point `ι (θ p)`.  `σ (inl x) = inl y` when `f x = some y`; `σ (inl t) = ν (inl (τ t))` on a sink
`t`; `σ (inr h) = ν (inr h)`.  Useful helpers: `fwd f (n+1) x = (fwd f n x).bind f`, and the
PEquiv facts `f x = some y ↔ f.symm y = some x` (`PEquiv.eq_some_iff`) and injectivity.

### Completion

* **`completeFun_bijective`.**  Partition `α ⊕ H` into `A := inl '' {x | f x ≠ none}`,
  `S := inl '' Snk`, `inr '' H`.  On `A`, `σ = inl ∘ f`, injective (PEquiv) with image
  `inl '' {y | f.symm y ≠ none}` (non-sources).  On `S ∪ inr '' H`, `σ = ν ∘ (Sum.map τ id)`,
  which is `ι ∘ θ ∘ (+1) ∘ θ⁻¹ ∘ (τ ⊕ id)`: a composite of bijections onto `ι '' univ`
  `= inl '' Src ∪ inr '' H` (`ι` injective, as `Subtype.val` is).  The two images are disjoint
  (a source has no predecessor) and cover `α ⊕ H`.  Simplest Lean route: build the inverse
  explicitly (`inl y ↦ inl x` if `f.symm y = some x`, else `θ⁻¹ … - 1` then `τ⁻¹`/`inr`) and use
  `Function.bijective_iff_has_inverse`.
* **`sameCycle_succ_of_not_diverges`.**  If `θ p = inr h`, `σ (ι (θ p)) = ι (θ (p+1))`.  If
  `θ p = inl s` with `s` not divergent, take the least `n` with `fwd f (n+1) s = none`; then
  `fwd f n s = some t`, `t` is a sink, `σ^k (inl s) = inl (fwd f k s)` for `k ≤ n`, and
  `σ (inl t) = ν (inl (τ t)) = ν (inl s)` by (H2), which is position `p+1`.  So
  `σ^(n+1)` carries position `p` to `p+1`.
* **`not_sameCycle_of_cut`.**  *Forward lemma:* from position `j`, the forward `σ`-orbit visits
  line points only at positions `j, j+1, …` in order, and if position `j` is a divergent source
  it never visits another line point (it stays on `inl (fwd f k s)`, never a sink, never a
  source since each has a predecessor).  So the forward orbit of position `q ≤ p` visits only
  positions in `[q, p]`.  *Backward lemma:* `σ⁻¹` of position `p+1` is `inl t`, `t := τ⁻¹ s`;
  the backward `f`-chain from `t` is infinite, since if it reached a source `s'` in `n` steps
  then (H2) gives `τ t = s'`, so `s' = s` and `s` reaches the sink `t`, contradicting
  divergence.  So the backward orbit of any position `r ≥ p+1` visits only positions in
  `[p+1, r]`.  `SameCycle a b` means `σ^k a = b` for some `k : ℤ`; case on the sign of `k`
  (or use `SameCycle.symm` and `Equiv.Perm.SameCycle.exists_nat_pow_eq` style lemmas where a
  finite orbit is impossible).  (H1) is not needed here.
* **`card_orbits`.**  *Anchors.*  Every `inl x` lies on the orbit of some position: by (H1)
  either the backward chain of `x` reaches a source `s` (then `x` is on `s`'s forward chain,
  `SameCycle` with position `θ⁻¹ s`), or the forward chain reaches a sink `t` with infinite
  backward chain (if both chains were infinite, splice them into `g : ℤ → α` contradicting
  (H1)); in the latter case `τ t` is divergent (as in the backward lemma) and `inl x` is on the
  orbit of position `θ⁻¹ (τ t) + 1`.  Every `inr h` is a position.  *Blocks.*  Let
  `C := {p | θ p = inl s, s divergent}` (cuts).  By the previous two lemmas, positions `q < r`
  share an orbit iff `[q, r) ∩ C = ∅`.  So `Orbits σ ≃` the set of maximal intervals of `ℤ` cut
  after each point of `C`.  *Count.*  Map an orbit to `none` if it contains positions below
  every cut (or there is no cut), else to `some c` where `c` is the greatest cut below it
  (the interval is `[c+1, next cut]`).  This is a bijection `Orbits σ ≃ Option C` when `C` is
  bounded below or empty; when `C` is unbounded below the `none` class is empty and
  `#Orbits = #C = ℵ₀ = 1 + ℵ₀`.  Uniformly: `#Orbits = 1 + #C` in `Cardinal`, and
  `C ≃ {s : Src f // Diverges f s.1}` via `θ`.  A clean route: show `#Orbits ≤ 1 + #C` by the
  injection above and `#C ≤ #Orbits` plus `1 ≤ #Orbits`, then split on `C` finite (exact count
  `|C| + 1` from the sorted cuts) vs infinite (`Cardinal.add_eq_right`/`aleph0` arithmetic,
  everything countable since `ℤ ↠` positions and every orbit contains a position).
* **`sameCycle_all_iff`, `infinite_orbits_iff`.**  From `card_orbits`: `1 + κ = 1 ↔ κ = 0`, and
  `1 + κ` infinite `↔ κ` infinite (`Cardinal.mk_le_aleph0`… or `Cardinal.infinite_iff`).  One
  orbit `↔ Subsingleton (Orbits σ)` `↔ ∀ a b, SameCycle a b`.  Direct proofs from the two
  block lemmas are also fine.
* **`one_or_infinite_orbits`.**  Case on `∃ s, Diverges f s.1`; use the previous two.

### Lemma M

* **`visits_boundary_forward`.**  Suppose `(x n).1 ∉ B` for all `n ≥ N`.  `Q` finite, so some
  state `q` occurs at infinitely many indices `n ≥ N` (`Finite.exists_infinite_fiber` or
  `Set.Infinite` pigeonhole); enumerate them strictly increasing `k : ℕ → ℕ`
  (`Nat.nth` / `Set.Infinite.natEmbedding`, then sort, or `Nat.exists_strictMono`).  Dickson:
  `wellQuasiOrdered_le` on `fun i => (x (k i)).2` gives `i < j` with
  `(x (k i)).2 ≤ (x (k j)).2`.  `OffRun B Step x (k i) (k j)` holds, the states agree, so
  `LapNotUp` gives a contradiction.
* **`visits_boundary_backward`.**  Same pigeonhole and Dickson give `i < j` with
  `(x (k i)).2 ≤ (x (k j)).2`.  Reindex `y m := x (k j - m)`: a forward run from `y 0 = x (k j)`
  to `y (k j - k i) = x (k i)`, off `B`, same state; `LapNotDown` says the end is not `≤` the
  start, i.e. `¬ (x (k i)).2 ≤ (x (k j)).2`.  Contradiction.  (Alternatively derive it from the
  forward theorem applied to the flipped relation.)
* **`immortal_iff_macro`.**  (→) By the forward theorem the set of `B`-visit indices is infinite;
  enumerate it increasingly `k`, put `b n := x (k n)`; `MacroStep` from `b n` to `b (n+1)` is
  witnessed by `fun i => x (k n + i)` with length `k (n+1) - k n`; intermediate indices are not
  `B`-visits since `k` enumerates all of them.  (←) Concatenate: define the run by recursion on
  the macro steps (choose witnesses with `Classical.choose`), or get `x` from
  `Relation.TransGen`-style chaining; positivity of each length makes the run infinite.
* **`reverse_immortal_iff_macro`.**  Mirror of the previous one with the backward theorem; the
  macro step from `b (n+1) = x (k (n+1))` to `b n = x (k n)` is witnessed by
  `fun i => x (k (n+1) - i)`.
* **`TwoCounter.visits_boundary`.**  Apply the two abstract theorems with `V := ℕ × ℕ`
  (instance `WellQuasiOrderedLE (ℕ × ℕ)` resolves).  Need `LapNotUp B (Step R)` and
  `LapNotDown B (Step R)` from `LapsMixed`: given an off-`B` run `x` from `m` to `n` with equal
  states, choose for each `i < n - m` a rule `ρ i ∈ R` firing `x (m+i) → x (m+i+1)`.  Then
  `src`s are the states `∉ B`, `dst (ρ i) = (x (m+i+1)).1 = src (ρ (i+1))`, and
  `dst (ρ (n-m-1)) = (x n).1 = (x m).1 = src (ρ 0)`.  By induction (telescoping), the lap
  `∑ (ρ i).move` equals `((x n).2.1 - (x m).2.1, (x n).2.2 - (x m).2.2)` in `ℤ × ℤ`.  Mixed
  signs mean one coordinate strictly drops and the other strictly rises, which refutes both
  `(x m).2 ≤ (x n).2` and `(x n).2 ≤ (x m).2` (`Prod.mk_le_mk`, `Int.ofNat_lt`).

Any cleaner route is fine as long as the ratified statements are unchanged.
