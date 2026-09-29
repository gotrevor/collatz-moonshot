# HANDOFF 2026-09-29 — bounded merger to any smaller seed: both frozen theorems proved

## Status: COMPLETE

`CollatzMoonshot/Obstructions/BoundedMerger.lean` compiles with zero errors and zero
warnings.  Both frozen public statements are proved, byte-identical to the kickoff types:

- `crt_no_bounded_smaller_merge (K n) (hn : 6^K ≤ n) (h2 : 2^K ∣ n+1) (h3 : 3^K ∣ n)`
- `arbitrarily_large_no_bounded_smaller_merge (K M)`

`#print axioms` on both: `[propext, Classical.choice, Quot.sound]` only.  `lake build`
green (8825 jobs).  `lake env lean scripts/AxiomAudit.lean` clean — the
parent-owned `BoundedMergerConsumers` examples typecheck against the proved theorems.
Neither the root import nor `scripts/AxiomAudit.lean` was edited.

## Mathematical deviation from the paper proof (a simplification, not a weakening)

The paper (`RESEARCH-2026-09-29-bounded-small-merger.md`) and the kickoff both route the
contracting-slope case through a **signed** orbit: write `b = 2^d(n/3^q) − L`, observe
`b ≡ −L (mod 2^d)`, invoke a *parity transport lemma* so that `b` and the negative
integer `−L` share their first `d` parity letters, and then argue `z = T_ℤ^d(−L) < 0`.

**None of that is needed.**  The entire proof is carried out in `ℕ`.  What the signed
detour actually establishes is the single inequality `y < 3^a n`, where `y = tstep^[d] b`.
Unfolding the affine relation, that inequality is *exactly*

```
tstep^[d] b < N * 3 ^ ones (traceWord b d)      where N = n / 3^q,  b < N * 2^d.
```

So it follows from a scaled, strict, purely natural growth bound, proved by one induction
on `d` (`tstep_iterate_lt`):

```lean
∀ d C x, 0 < x → 0 < C → x < C * 2 ^ d → tstep^[d] x < C * 3 ^ ones (traceWord x d)
```

The induction scales the constant: an even letter halves the `2`-budget (`C` unchanged),
an odd letter replaces `C` by `3 * C` because `x` odd and `x < C * 2^(k+1)` force
`x ≤ C*2^(k+1) − 1`, hence `2 * tstep x = 3x + 1 ≤ 3C*2^(k+1) − 2 < 2 * (3C * 2^k)`.
The parity-transport lemma and the signed map `stepZ` are therefore **not used at all**,
and `FrontB/Negative.lean` is not imported beyond what `Q1Coalescence` already pulls in.

## Proof skeleton as it stands in the file

Private helpers, all in `ℕ`:

| lemma | content |
|---|---|
| `ones_le_length` | `ones v ≤ v.length` |
| `le_g` | `3 ^ ones v ≤ 2 ^ v.length + numer v` |
| `g_le` | `2 ^ v.length + numer v ≤ 2 ^ (v.length − ones v) * 3 ^ ones v` |
| `ones_append` | `ones (u ++ v) = ones u + ones v` |
| `traceWord_add` | `traceWord x (d+i) = traceWord x d ++ traceWord (tstep^[d] x) i` |
| `tstep_iterate_lt` | the scaled strict growth bound above |
| `tstep_iterate_le` | `2^m * (tstep^[m] x + 1) ≤ 3^m * (x+1)` |
| `odd_run` | `2^i ∣ n+1 → 2^i * (tstep^[i] n + 1) = 3^i * (n+1)` |

`crt_no_bounded_smaller_merge` then runs:

1. `odd_run` on `n` (via `pow_dvd_pow 2 hi`) gives the additive form
   `2^i * tstep^[i] n + 2^i = 3^i n + 3^i`.
2. `j ≤ i` is refuted with `tstep_iterate_le` plus `2^(i−j) * 3^j ≤ 3^i`, yielding `n ≤ b`.
   So `d := j − i > 0`.
3. `tstep_iterate_identity` on the length-`j` trace `v` of `b`, combined with step 1 and
   `2^j = 2^d * 2^i`, gives the **master equation**, entirely additive over `ℕ`:
   `3^p * b + gw = 2^d * 3^i * n + 2^d * 3^i`, with `p = ones v`, `gw = 2^j + numer v`.
4. Trichotomy on `2^d * 3^i` vs `3^p`:
   - `>` : `gw ≤ 2^(j−p) 3^p ≤ 6^K ≤ n` makes the intercept harmless, so `b > n`.
   - `=` : `2 ∣ 2^d * 3^i` (as `d > 0`) but `¬ 2 ∣ 3^p`.
   - `<` : the real case.  `p > i`, `q = p − i > 0`, `3^q ∣ n`, `n = 3^q N`, and the
     master equation rearranges to `b < N * 2^d` with no natural subtraction anywhere
     (`L` is never constructed).
5. In the `<` case, split `v = traceWord b d ++ traceWord y i` (`traceWord_add`),
   `p0 = ones v1`, `a' = ones v2 ≤ i`, so `p0 ≥ q`; set `a = p0 − q`, giving `a' = i − a`.
6. `tstep_iterate_lt d N b` gives `y < N * 3^p0 = 3^a * n`.
7. The tail affine relation plus step 1, with the common `3^i n` cancelled by `omega`:
   `3^(i−a) * y + (2^i + numer v2) = 3^i n + 3^i`.
8. `g_le v2` gives `2^i + numer v2 ≤ 2^a * 3^(i−a)`, and step 6 gives
   `3^(i−a) y + 3^(i−a) ≤ 3^i n`.  Together: `3^i + 3^(i−a) ≤ 2^a 3^(i−a) ≤ 3^a 3^(i−a) = 3^i`,
   i.e. `3^(i−a) ≤ 0`.  Contradiction.

`arbitrarily_large_no_bounded_smaller_merge` uses `Nat.chineseRemainder` on the coprime
pair `(3^K, 2^K)` with residues `0` and `2^K − 1`, then translates by `6^K * (M+1)` to
clear both `M` and `6^K`.  No computational inverse is used.

## Validation anchors in the file (all `by decide`, no `native_decide`)

- `6^1 ≤ 9 ∧ 2^1 ∣ 10 ∧ 3^1 ∣ 9`, and `∀ b < 9, 0 < b → ∀ i ≤ 1, ∀ j ≤ 1, tstep^[i] 9 ≠ tstep^[j] b`.
- `6^2 ≤ 63 ∧ 2^2 ∣ 64 ∧ 3^2 ∣ 63`, and the same exhaustive check at `K = 2` for `n = 63`.
- Countercontrol `tstep^[0] 31 = tstep^[3] 27`: `31` fails the `K = 2` cylinder
  (`4 ∤ 32`) and does merge with the smaller seed `27`, so the hypotheses are load-bearing.

Note the kickoff's countercontrol is stated as `27 → 41 → 62 → 31`, i.e. the *smaller*
seed `27` reaches `31` in three shortcut steps; the meeting is at depths `i = 0` on `n = 31`
and `j = 3` on `b = 27`, which is the orientation the anchor records.

## Statement defects found

None.  Both frozen types are correct as written and are not vacuous (the `K = 1` and
`K = 2` anchors above exhaust the conclusion by decision).

## Scope

This is an obstruction to *uniformly bounded* merger certificates only.  It does not
disprove variable-depth induction, exclude divergence or cycles, formalize Monks'
theorem, or claim historical novelty.

No successor task.
