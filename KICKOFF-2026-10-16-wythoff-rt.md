# KICKOFF 2026-10-16: Theorem RT, residue-transitivity of the rational Wythoff members

Repo `collatz-moonshot-amusical-round2` (branch `wip/wythoff-rt`): close every `sorry` in
`CollatzMoonshot/WythoffResidue.lean` (16 lemmas).  It imports Mathlib, `Amusical.lean` (for `U =
amusical`) and `WythoffRational.lean` (proved; reuse `Side`, `wythoff`, `wythoffInv`,
`wythoffPerm`, `wythoff_add_even`, `wythoff_add_odd`, `wythoff_plus_even`, `wythoff_minus_even`,
`wythoff_plus_odd`, `wythoff_minus_odd`, `ediv_eq_iff`, `wythoffInv_wythoff`,
`wythoff_wythoffInv`, `wythoff_pos_iff`, `parityClass_invariant_iff`, `absorbing_iff`, Lemma 1
`card_even_image_even/odd`, and `WythoffRationalMarkov.wythoffInv_add` if you import it).  Do not
edit `WythoffRational*.lean`, `Amusical.lean` or `AmusicalTrap.lean`.

Source: research note `~/personal/tmp/amusical-agents/out/wythoff-transitive.md` (§1 window
formula and reduced digraph, §2 base (B0), (B1), Lemma D, §3 Lemmas B, A, A₂, Theorem RT, §4 the
trap corollary).  Scripts `out/wythoff-transitive/transitive.py`, `steps.py`.

## Ratified, do not change

Every definition and theorem statement in `WythoffResidue.lean`:

* Definitions: `ResidueEdge`, `ResidueTransitive` (`∀ a b, ReflTransGen (ResidueEdge f M) a b`),
  `ResidueClosed`, `evenLo`, `oddLo`.
* §A digraph (**already proved**, axiom-clean, verified 2026-10-16): `residueClosed_iff_edge`,
  `residueTransitive_iff_closed`, `residueTransitive_symm_iff`, `residueTransitive_one`.
* §B window: `wythoff_even_window`, `wythoff_odd_window`, `exists_even_window`,
  `exists_odd_window`.
* §C odd `p`: `amusical_eq_wythoff` (**proved**), `residueTransitive_base_coprime` (B0),
  `residueTransitive_lift_dvd_p` (B), `residueTransitive_lift_dvd_qR` (A),
  `residueTransitive_lift_two_of_odd` (A₂), `residueTransitive_of_odd`,
  `amusical_residueTransitive` (proved from `residueTransitive_of_odd`),
  `eventually_mem_or_not_mem_of_closed`, `amusical_eventually_mem_or_not_mem` (proved from it).
* §D even `p`: `residueTransitive_base_two_pow` (B1), `residueTransitive_lift_two_of_four_dvd`
  (D), `residueTransitive_of_even_nonabsorbing`, `residueTransitive_of_odd_modulus`,
  `not_residueTransitive_of_absorbing_even`, `residueTransitive_absorbing_iff` (proved from the
  two before it), `residueTransitive_iff` (Theorem RT; proved from the parts),
  `two_minus_not_residueTransitive`.

No `native_decide`, no axioms, no `maxHeartbeats` bumps.  Lean lines ≤ 100 characters.  Do
**not** edit `RESEARCH-*.md`.  Commit after each proved lemma (or tight group).  Notes as you go
in `HANDOFF-wythoff-rt.md`.  Helper lemmas and definitions are welcome (above their first use; a
shared helper section is fine).  Any cleaner route is fine as long as the ratified statements are
unchanged.  If a ratified statement turns out false, stop that lemma, write the counterexample in
the HANDOFF, and move on; do not weaken it yourself.

**Order of attack (priority 1 = odd `p`, the `U` result, first):**
1. §B window (all four), then the helpers H1-H3 below.
2. (B0) `residueTransitive_base_coprime`.
3. The level-drop machinery H4, then A₂, B, A (in that order).
4. Assembly H5 → `residueTransitive_of_odd`; this closes `amusical_residueTransitive`.
5. `eventually_mem_or_not_mem_of_closed` (closes the `U` corollary).
6. Priority 2: `not_residueTransitive_of_absorbing_even`, `two_minus_not_residueTransitive`,
   `residueTransitive_of_odd_modulus` (H5 with `M` odd), then (B1), D, and
   `residueTransitive_of_even_nonabsorbing`.

## Truth checks already run

`tmp/drafter-rt/check.py [MMAX PMAX]` (gitignored; outputs `check.out` (36, 12; 16 s) and
`check-60-16.out` (34 s); 35/35 ok).  Mirrors the Lean definitions exactly: Python `//`, `%` =
`Int.ediv`, `Int.emod` for positive divisors; the residue digraph from `n ∈ [0, 2qRM)` (full
period, checked against `[−2P, 3P)`).  `tmp/drafter-rt/Axioms.lean` evaluates `wythoff .plus 3 1`
on `[−4, 8)` and prints the axioms of the proved lemmas.

* `residueTransitive_iff` on **9360** (member, `M`) pairs: every coprime `3 ≤ p ≤ 16`, both
  sides, `M ≤ 60`; each named part (odd `p`, even non-absorbing, odd modulus, absorbing at even
  `M`) separately.
* Trap form `residueTransitive_iff_closed` by enumerating all subsets of `ZMod M` (340 pairs,
  `p ≤ 7`, `M ≤ 10`, 33 of them non-transitive); reversal (`symm_iff`) on `p ≤ 9`, `M ≤ 12`.
* Window iff + existence, both sides and branches, `p ≤ 14`, `|y| ≤ 120`.
* `amusical = wythoff .plus 3 1` on `[−5000, 5000)`.
* Base and lifts as implications: B0 3788 instances, B1 348, D 528 (400 non-vacuous), B 5664,
  A 7848, A₂ 5760.
* Corollary: no proper nonempty eventually-periodic `C` (`M ≤ 8`) is eventually `U`-closed.
* **Known-answer controls:** `U` transitive at every `M ≤ 60` (computed from `amusical` itself);
  `4/1+`, `4/3+`, `6/1+`, `6/5+` transitive exactly at the odd `M ≤ 40`; `5/2±` at every `M`.
* **Teeth** (each fails as it must): `2/1−` (the swap) at every even `M ∈ [4, 28]`, so `3 ≤ p`
  is load-bearing; `2/1+` (identity) fails mod 3, so B0's `3 ≤ p` and `absorbing_iff`'s `4 ≤ p`
  are load-bearing; `residueTransitive_iff` without the absorbing disjunct; B1 at an absorbing
  member (`6/1+` mod 2); Lemma B with `ℓ = 2` (`4/1+`: `3 → 6`); the window shifted by `±1`;
  `4/1+` mod 4 with closed set `{0, 2}`; `amusical ≠ wythoff .minus 3 1`, `≠ wythoff .plus 3 2`;
  the evens are an eventually-periodic trap for `4/1+`.
* Not load-bearing (proof artifacts, true without them): B1's `p % 4 = 2 ∨ e = 1`, the
  coprimality hypothesis of Lemma D.

## Paper proofs (Ren)

Notation: `R := p − q`, `Q ∈ {q, R}` the branch divisor (`q` for even `n`, `R` for odd `n`).
`W(n + 2qm) = W n + pm` (`n` even), `W(n + 2Rm) = W n + pm` (`n` odd).  `gcd(q, R) = 1`
(`Nat.coprime_self_sub_right` + symm).  The W⁻¹ pieces are `c + pℤ ↦ a + 2Qℤ`,
`W⁻¹(m + py) = W⁻¹ m + 2Qy` (Markov file `wythoffInv_add`, or reprove via injectivity).

### §B window (≈ 80 lines)

* **`wythoff_even_window`** (25).  `+`: `W(2y) = py / q` (`wythoff_plus_even`); with `0 ≤ j < q`,
  `q ∣ py − j ⇔ py % q = j ⇔ (py / q) q = py − j` (`Int.emod_emod_of_dvd`, `Int.ediv_add_emod`,
  `Int.emod_def`; or `ediv_eq_iff` + `omega` after naming `t := py`).  `−`: `W(2y) = (py − 1)/q`,
  `1 ≤ j ≤ q`, set `j' := j − 1 ∈ [0, q)`, same argument with `py − 1`.  (→) is always free:
  `q ∣ W·q`.
* **`wythoff_odd_window`** (25).  `2y − 1` is odd, `(2y − 1 + 1)/2 = y`; `+`: `(py − 1)/R`,
  `j ∈ [1, R]`; `−`: `py / R`, `j ∈ [0, R)`.
* **`exists_*_window`** (15 each).  `j := lo + (py − lo) % Q` (`Int.emod_nonneg`,
  `Int.emod_lt_of_pos`, `Int.dvd_sub_of_emod_eq` / `Int.emod_emod_of_dvd`).

### Helpers (≈ 120 lines)

* **H1 (edges recur).**  For `n` and `k : ℤ`, `W(n + 2qRM k) ≡ W n (mod M)` (both branches via
  `wythoff_add_even/odd` with multiplier `R M k` / `q M k`).  So every edge `a → b` mod `M` is
  realized by `n` with `n ≥ N` for any `N`, and by `n` with `W n ≥ N` (H2).
* **H2 (`W → ∞`).**  `n ≥ 2 ⇒ W n ≥ n / (2 max(q, R))`-ish; easiest: `W` is a bijection of `ℤ`
  preserving `ℕ⁺` (`wythoff_pos_iff`), and `W n ≥ (n − 1)/2 · p / max(q, R) − 1`.  Only
  `Tendsto (wythoff s p q) atTop atTop` is needed.
* **H3 (reduced digraph, note §1).**  If `gcd(M', q R) = 1`: from residue `x` mod `M'` and an even
  representative `n = 2y`, every `j` in the even window occurs (as `y` runs over a class mod
  `M'/gcd(M', 2)`, `y mod q` runs over all of `ℤ/q`, CRT), giving edges `x → (py − j)·q⁻¹`; same
  for odd.  State in the form actually used by B0/B1: "if `x ≡ 2y (mod M')`, `j ∈ J_E`, then
  `ResidueEdge W M' x ((py − j) · q⁻¹)`" (with `q⁻¹ : ZMod M'` from `ZMod.unitOfCoprime`).

### (B0) `residueTransitive_base_coprime` (≈ 150 lines)

`M₀` odd, coprime to `2pqR`; `2, p, q, R` are units mod `M₀`.  Every `x : ZMod M₀` has both an
even and an odd representative.  By H3 the edges out of `x` include `x → (p·x/2 − j)/q` for every
`j ∈ J_E` (`y := x/2` in `ZMod M₀`) and `x → (p(x+1)/2 − j)/R` for every `j ∈ J_O`.
* *Weak step.*  Since `q + R = p ≥ 3`, one window has length `≥ 2`.  Say `q ≥ 2` (else `R ≥ 2`,
  symmetric).  For fixed `j`, `f_j : x ↦ (p x/2 − j)/q` is a bijection of `ZMod M₀`.
* *Avoid (S) here.*  The digraph contains the graph of the permutation `f_j`, and a permutation
  of a finite type has finite order (`orderOf_pos`, `pow_orderOf_eq_one`), so following `f_j` from
  `z := f_j x` returns to `x = f_j⁻¹ z`: `z ↝ x`.  With `x → f_{j+1} x = z − 1/q` this gives
  `z ↝ z − 1/q` for every `z`, hence `z ↝ z − k/q` for all `k`, and `1/q` generates `ZMod M₀`.
  Strong connectivity without stationary measures.

### H4 level-drop machinery (≈ 250 lines; shared by A₂, B, D)

Work with the trap form (`residueTransitive_iff_closed`).  An *S-set of level `j`* in `ZMod
(ℓ^e M')` is the set of residues `≡ c (mod ℓ^j M')`.  Core arithmetic fact: the image mod `M` of
an AP `{c + N t}` is the class of `c` mod `gcd(N, M)`, so a closed `C` containing one point of a
piece-AP contains the whole class mod `gcd(N, M)`.  For a piece `a + 2Qℤ` (forward) and an
S-set `S` of level `j`, `S ∩ piece` is an AP with step `lcm(ℓ^j M', 2Q)` (when nonempty; CRT),
mapped to an AP with step `p · lcm(ℓ^j M', 2Q)/(2Q)`.  Prove once: "the `ℓ`-adic valuation of
the image step is `v_ℓ(p) + max(j, v_ℓ(2Q)) − v_ℓ(2Q)`" and "the image contains an S-set of level
`min(e, that valuation)` around each image point".  Mathlib: `Nat.factorization`, `padicValNat`,
`Nat.Coprime.lcm_eq_mul`, `Int.emod_emod_of_dvd`, `ZMod.intCast_eq_intCast_iff_dvd_sub`.
An alternative that avoids valuations: induct on `e` (lift `ℓ^e M' → ℓ^{e+1} M'` one power at a
time), where "level drops" becomes a statement about one extra digit.

### A₂ `residueTransitive_lift_two_of_odd` (≈ 60)

`p` odd.  Every forward piece has domain step `2Q` (`v₂ ≥ 1`) and image step `p` (`v₂ = 0`), so
the forward image of an S-set of level `j ≥ 1` contains an S-set of level `≤ j − 1` (H4 with
`ℓ = 2`).  A nonempty closed `C` therefore contains a full fiber `F_{b'} = {x ≡ b' (mod M')}`.
Full fibers map onto full fibers along every `M'`-edge (image step has `v₂ = 0`), so `{b' : F_{b'}
⊆ C}` is nonempty and closed mod `M'`, hence everything.

### B `residueTransitive_lift_dvd_p` (≈ 80)

Same as A₂ for `W⁻¹` (pieces `c + pℤ ↦ a + 2Qℤ`; `ℓ^g ∥ p`, `ℓ ∤ 2Q`): levels drop by `g`.  Get
the statement for `W` from `residueTransitive_symm_iff` with `σ := wythoffPerm s hq hqp`
(`σ.symm = wythoffInv`, `rfl`), applied at both `M'` and `ℓ^e M'`.

### A `residueTransitive_lift_dvd_qR` (≈ 180)

`ℓ ∣ q`, `ℓ^f ∥ q` (the `ℓ ∣ R` case is symmetric with parities swapped; WLOG via a shared
helper parametrized by the branch).  Even (`q`) pieces drop the level by `f`; odd (`R`) pieces keep
it (`ℓ ∤ 2Rp`).  **Routing:** let `S ⊆ C` have level `j > 0` over `a'`.  (i) If `a' + M'ℤ`
contains evens (always if `M'` odd; if `M'` even, iff `a'` even), `S` contains an even point
(`ℓ` odd, CRT), and the `q`-step drops the level.  (ii) If `M'` even and `a'` odd, only odd pieces
meet `S`; for each, `S ∩ π ≠ ∅ ⇔ (a' + M'ℤ) ∩ π ≠ ∅` (`ℓ ∤ 2R`), and the image residues mod `M'`
agree (steps differ by the unit `ℓ^j`).  So every `M'`-edge out of `a'` is available at the same
level.  Strong connectivity mod `M'` gives a path from `a'` to the even vertex `0`; walk it at
constant level, then apply (i).  Induct on `j` (decreasing), then propagate full fibers as in A₂.

### (B1) `residueTransitive_base_two_pow` (≈ 220)

`p = 2p'`; `p'` is a unit mod `M'/2` (`p ≡ 2 (4)`: `p'` odd; `e = 1`: `M'/2 = M₀`).  `q, R` odd.
By H3 each `x` of parity `ε` has edges `x → (py − j)·Q_ε⁻¹` for `j ∈ J_ε`, and the target has
the parity of `j`.  For fixed `j`, `f_j : {parity ε} → {parity of j}` is a bijection.
* *Every edge on a cycle* (note (S) with `ν = φ × uniform`).  Combinatorial version (avoids
  measures): give the edge `x → f_j x` (`j ∈ J_ε`, `ε` = parity of `x`) the weight `φ(ε)/Q_ε`
  (denominators cleared to integers).  In-flow at `z` of parity `f` is `Σ_ε φ(ε)·#{j ∈ J_ε : j ≡
  f}/Q_ε = Σ_ε φ(ε) F(ε → f) = φ(f)` = out-flow (Lemma 1 counts are the chain's numerators).  A
  finite digraph with a positive circulation has every edge on a cycle: if `x → y` is not on one,
  the set `A` reachable from `y` excludes `x`, and in − out summed over `A` is `≥ w(x → y) > 0`.
  Full support of `φ` ⇔ non-absorbing (`absorbing_iff`: both off-diagonal entries positive).
* *Weakly connected.*  `z = (py − j)/Q` is solvable (some `x`) iff `j ≡ z (mod 2)`.  A window
  of length `≥ 3` contains, for each parity, some `j ≡ z` with `j + 1` also in it; both edges
  leave the same `x`, so `z ~ z − 1/Q` (undirected), and `1/Q` generates `ZMod M'`.  One of `q, R`
  is `≥ 3` (both odd, `p ≥ 4`).
* (W): every edge on a cycle + weakly connected ⇒ strongly connected (`Relation.ReflTransGen`
  along an undirected path, reversing each edge through its cycle).

### D `residueTransitive_lift_two_of_four_dvd` (≈ 120)

`v := v₂(p) ≥ 2`.  `W⁻¹` image of an S-set of level `j` (2-adic) has level `1 + max(j, v) − v ≤
max(j − 1, 1)`; iterate down to level 1 (a full parity fiber, i.e. a class mod `2M₀`).  Parity
fibers map onto parity fibers (step `2QM₀`, `gcd(Q, 2^e M₀) = 1`).  Conclude by the mod-`2M₀`
hypothesis for `W⁻¹` (`residueTransitive_symm_iff`).

### Assembly H5 (≈ 120)

Strong induction on `M`.  If an odd prime `ℓ ∣ M` divides `p` or `qR`, split `M = ℓ^e M'`, `ℓ ∤
M'` (`Nat.exists_eq_pow_mul_and_not_dvd`), recurse on `M' < M`, apply B or A.  Otherwise `M = 2^e
M₀` with `gcd(M₀, 2pqR) = 1`: `p` odd → B0 then A₂; `p` even → `e = 0`: B0; `p ≡ 2 (4)`: B1; `4 ∣
p`: B1 at `e = 1`, then D.
* `residueTransitive_of_odd`, `_of_even_nonabsorbing`: H5.
* `residueTransitive_of_odd_modulus`: H5 restricted to odd `M` (only B0, B, A; no parity chain),
  or case on `p` and reuse the two above for the non-absorbing cases.

### The rest (≈ 150)

* **`eventually_mem_or_not_mem_of_closed`** (80).  From `hper` get `N` with `n ≥ N → (n ∈ C ↔ n +
  M ∈ C)`, hence `n, n' ≥ N`, `n ≡ n' (M)` ⇒ same membership (induction on the difference /
  `M`).  `C̃ := {a | ∃ n ≥ N, (n : ZMod M) = a ∧ n ∈ C}`.  `C̃` is `ResidueClosed`: for `n ≡ a ∈
  C̃`, by H1/H2 pick `n' ≡ n (mod 2qRM)` with `n' ≥ N`, `n'` past the `hfwd` threshold, and `W n' ≥
  N`; then `n' ∈ C`, `W n' ∈ C`, `W n' ≡ W n`.  `residueTransitive_iff_closed` ⇒ `C̃ = ∅` (eventually
  `∉`) or `univ` (eventually `∈`).
* **`not_residueTransitive_of_absorbing_even`** (40).  `parityClass_invariant_iff` (←) gives `e`
  with `n ≡ e (2) → W n ≡ e (2)`.  With `h2 : 2 ∣ M`, `C := {a | ZMod.castHom h2 (ZMod 2) a = e}`
  is `ResidueClosed` (`ZMod.castHom_apply`, `ZMod.cast_intCast`), contains `(e.val : ZMod M)`
  and misses `(e.val + 1 : ZMod M)`; contradict `residueTransitive_iff_closed`.
* **`two_minus_not_residueTransitive`** (30).  `W_{2/1−}(2k) = 2k − 1`, `W(2k − 1) = 2k`.
  `C := {1, 2} ⊆ ZMod M`: `n ≡ 1` is odd (`2 ∣ M`) so `W n = n + 1 ≡ 2`; `n ≡ 2` is even so
  `W n = n − 1 ≡ 1`.  `C ≠ ∅`, and `0 ∉ C` since `M ≥ 4` (`ZMod.val` / `ZMod.intCast_cast`).

Rough total: **1,200-1,500 lines** (note's estimate ≈ 1000).  Priority 1 (window, H1-H4, B0,
A₂, B, A, H5 for odd `p`, the trap corollary) ≈ 850 of it; that alone makes "`U` has no periodic
trap at any modulus" a checked theorem.  Largest risks: H4's valuation bookkeeping and Lemma A's
routing (the note's 8 % reserve), and B1's circulation bookkeeping.
