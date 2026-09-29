# Symbolic structure in the `64k+7` virtual descent

This is a symbolic audit of the induction proposal in `RESEARCH-2026-09-28-induction-novelty-audit.md`.  It preserves the artificial inverse-5 word, the six-step virtual prefix, and the smaller-endpoint certificate as separate pieces.  It gives a finite-history interface and two exact obstructions; it does not claim a general repair algorithm or a Collatz estimate.

## The common construction, for every `k≥0`

Put `n=64k+7`, `m=45k+5`, and `a=5n=320k+35`.  The shortcut trajectory from `a` has the fixed parity word `O,O,E,E,E,E`:

```
320k+35 → 480k+53 → 720k+80 → 360k+40
         → 180k+20 → 90k+10 → 45k+5 = m.
```

Since `1/5=2² r₇² r₁₁ r₁₇ r₅₅ r₆₅ r₈₃`, the history-preserving virtual certificate built from any path certificate `C_m` of value `m` is

```
V_k(C_m)
 = (2⁶ r₇² r₁₁ r₁₇ r₅₅ r₆₅ r₈₃
       r_(320k+35) r_(480k+53)) · C_m.
```

The parenthesized factor has value `n/m` for every `k`, because the odd ratios and four even edges telescope from `5n` to `m`.  Thus `V_k(C_m)` has value `n`.  This is the exact common prefix to normalize before comparing repair derivations; it does not depend on a known trajectory of `n`.  Its contribution to the palette index `I=5t−3q−m₅−2m₁` is exactly `5·6−3·9=3` (`q` here counts odd factors), so `I(V_k(C_m))=I(C_m)+3`.  This can diagnose the required net C5 budget only after a target certificate is specified; it cannot predict the path of `n`.

For contrast, the **actual** first six shortcut steps from `n` have word `O,O,O,E,O,E` and end at `p=81k+10`:

```
64k+7 → 96k+11 → 144k+17 → 216k+26
      → 108k+13 → 162k+20 → 81k+10.
```

The two six-step endpoints have slopes 81 and 45.  Their difference is `p−m=36k+5`; there is no automatic common tail.

## Fixed-tail splicing cannot be the induction rule

Fix any two finite parity words, of lengths `r,s` with `a,b` odd symbols, and suppose they are valid continuations from `p=81k+10` and `m=45k+5` on an infinite arithmetic progression of `k`.  Their endpoints are affine functions of `k` with slopes `81·3^a/2^r` and `45·3^b/2^s`.  Equality for infinitely many `k` would require

```
81·3^a·2^s = 45·3^b·2^r,
```

which is impossible by 5-adic valuation.  Equivalently, each *fixed pair* of words can meet for at most one `k`.  Applying the same argument directly to `n` and `m` recovers the leading-coefficient obstruction behind the earlier bound `n<69·6^L` for a meeting of length at most `L`.  This is a restatement of that negative inventory in family coordinates, not a new exclusion of adaptive or growing repairs.

Consequently, a symbolic macro that merely keeps `C_m` untouched and splices a fixed-length path from `n` into a fixed position of that tail cannot serve all `k` in any infinite class.  A viable repair would need length growing with `k`, a state-dependent transformation of the supplied tail, or a different recursion interface.  A few successful numeric examples cannot overturn this slope obstruction.

## One exact self-return class, and its limit

`m` lies again in the family `7 mod 64` precisely when `k≡10 mod 64`, because `45⁻¹≡37 mod 64`.  Write `k=64ℓ+10`; then

```
n = 4096ℓ+647,
m = 64(45ℓ+7)+7,
k' = 45ℓ+7 = (45k−2)/64 < k.
```

This gives a precise sparse induction domain: a certificate for the smaller family member `m` could be the induction input for `n`.  It covers one of 64 `k` classes, and even that class still needs a legal repair of `V_k(C_m)` to a balanced path certificate for `n`.  The congruence is not a repair.  Repeated self-return requires further nested residue conditions and eventually exits because the parameter decreases.

The honest testable hypothesis for this branch is: **for every `ℓ≥0` and every supplied balanced path certificate `C_m` for `m=64(45ℓ+7)+7`, a restricted-palette script, constructed from `ℓ` and `C_m` without the forward trajectory of `n=4096ℓ+647`, repairs `V_k(C_m)` into some balanced path certificate for `n`.**  The required script must specify its borrowed-unit derivations and a decreasing recursive state.  No such script family is known.  Proving this partial branch would still leave the other 63 residue classes.

## What examples can measure

The suggested `n=2^j+7` and `n=2^j−57` correspond to adjacent parameters `k=2^(j−6)` and `k=2^(j−6)−1`, but they are **easy descent controls**, not a stress family.  Direct symbolic shortcut calculation gives

```
T^11(2^j+7) = 243·2^(j−11)+1 < 2^j+7       (j≥11),
T^8 (2^j−57) = 243·2^(j−8)−53 < 2^j−57      (j≥8).
```

For a genuine long-growth control, let `r_j` be the least nonnegative solution of `81r_j≡−11 (mod 2^j)`, `j≥6`.  Set `k_j=r_j` unless `r_j≡2 (mod 3)`, in which case set `k_j=r_j+2^j`.  Then `n_j=64k_j+7` is not divisible by 3, `k_j≡37 (mod 64)`, and the actual six-step endpoint satisfies

```
p_j=T^6 n_j=81k_j+10,
p_j+1=2^j s_j,                  1≤s_j<162,
T^(6+t)n_j=3^t·2^(j−t)s_j−1   (0≤t≤j).
```

Every one of those next `j` states is odd before its shortcut step, because `2^(j−t)s_j` is even for `t<j`; their values grow by the factor `3/2` on `x+1`.  All states through time `6+j` are at least `n_j`: the first six affine values listed above exceed `n_j`, and the odd run grows from `p_j>n_j`.  At `j=6`, `k_6=37`, `n_6=2375`, `s_6=47`, and `T^12 n_6=3^6·47−1=34262`.  The congruence `k_j≡37 (mod 64)` makes this long-growth family **disjoint** from the self-return class `k≡10 (mod 64)` for every `j≥6`; a repair confined to that sparse class does not address these controls.

Compare **central repair scripts** after separately marking borrowed-unit construction and return.  Repeated blocks in the long-growth family may expose a carry-dependent parametric rule; easy binary examples can serve as baseline controls.  Use unrelated held-out residues too.

Do not feed a known path of `n` into the relation search and then treat a repeated residual after canceling a shared `m/n` tail as predictive: the target path is the missing theorem.  A frozen candidate macro should be tested with only the supplied smaller certificate `C_m`; a finite holdout is discovery evidence, while a universal symbolic rule needs a proof of legal factor availability, vertex balance and a decreasing recursion measure.
