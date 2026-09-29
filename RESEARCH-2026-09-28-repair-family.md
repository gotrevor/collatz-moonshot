# Family profiles for the inverse-five certificate

```sh
./experiments/repair_family.py test
./experiments/repair_family.py family
./experiments/repair_family.py profile 135
./experiments/repair_family.py growth 6
```

This follows the [induction and novelty audit](RESEARCH-2026-09-28-induction-novelty-audit.md) and the [restricted repair of 71](RESEARCH-2026-09-28-palette-lattice.md).  Every profile uses the **same** Applegate-Lagarias inverse-five certificate for `n=64k+7`: the virtual six-step path starts at `5n`, ends at `m=45k+5<n`, then follows the known path of `m`.  The actual path of `n` is used only as a discovery oracle and as a target for the count ledger.  Nothing here selects that target path without knowing it.

The persistent CLI keeps the construction history separate.  For each start it reports the virtual prefix, the actual and smaller paths until their first meeting, their exact shared tail, the odd-factor multisets left after cancellation, and the necessary net counts of U2/U8/U13/cubic moves from `catalytic_palette.palette_ledger`.  It preserves signed residual labels and the parity prefix rather than reducing a repair to one scalar length.  The `family` command covers `2^j+7` and `2^j-57` for `6<=j<=16`, holdouts `64k+7` for `k=2,3,5,9,17`, and the growing-run controls below; duplicate starts are tagged as aliases.  There are 31 distinct starts in the 35 requested slots.

## The fixed-offset binary families are easy-prefix controls

For an integer `c` and fixed prefix length `L`, the first `L` shortcut parity bits of `2^j+c` agree with those of `c` whenever `j>=L`.  On that prefix the affine map has slope `3^a/2^L`, where `a` is the number of odd steps.  This gives two exact infinite subfamilies:

```
T^11(2^j+7)  = 243*2^(j-11)+1    < 2^j+7,     j>=11,
T^8 (2^j-57) = 243*2^(j-8)-53   < 2^j-57,    j>=8.
```

The first uses the 11-step path of 7 with five odd steps and endpoint 1; the second uses the first eight steps of the **negative input** `-57`, also with five odd steps, ending at `-53`.  The actual starts `2^j-57` in the stated domain are positive.  The inequalities are elementary: `243<2048` in the first, and `243<256` with the remaining difference `13*2^(j-8)-4>0` in the second.  Hand anchors are `T^11(2055)=244` and `T^8(199)=190`.  These are genuine symbolic descents for infinitely many starts, but they are ordinary parity-prefix induction, not a catalytic repair rule.  Repeated motifs observed as `j` grows are forced by the fixed low-bit offset.

The required net palette counts vary sharply even in these selected families.  For `n=71`, `(U8,U13,cubic forward)=(9,-3,-3)`; for `135`, `(-10,2,2)`; for `199`, `(11,-3,-3)`; for `263`, `(4,-2,-2)`; and for holdout `583`, `(0,-1,-1)`.  These are necessary signed totals, never an executable positive repair.  The full residual labels and exact actual-versus-smaller shared tails are regenerable with `profile n`.

## A growing-run stress family in the same progression

For each `j>=2`, choose

```
k_j = -11 * 81^(-1)  (mod 2^j),   0<=k_j<2^j.
```

If `k_j=2 mod3`, replace it by `k_j+2^j`.  Set `n_j=64k_j+7`.  This adjustment keeps the congruence and makes `3` coprime to `n_j`, since `n_j=k_j+1 mod3`.  Because 81 is odd its inverse modulo `2^j` exists.  Every `k_j` is positive and odd.

The actual first six steps, for every positive `k`, are

```
64k+7 -> 96k+11 -> 144k+17 -> 216k+26
      -> 108k+13 -> 162k+20 -> 81k+10.
```

All six new states exceed `64k+7`.  By construction `81k_j+10=2^j*s_j-1` with positive integer `s_j`.  The next `j` steps use the odd branch and strictly increase the state, ending at

```
T^(6+j)(n_j) = 3^j*s_j-1 > n_j.
```

Hence this infinite family has **no descent through step `j+6`**, unlike the fixed-offset examples.  At `j=2`, `k=1,n=71,s=23`, and the step-8 endpoint is 206.  At `j=6`, `k=37,n=2375,s=47`, and the step-12 endpoint is 34,262.  The CLI profiles `j=2,4,6,8,10,12,16,20`, deduplicating starts already present.  Its known later trajectories are finite observations; the proved statement here concerns only the initial `j+6` steps.  This is a better stress corpus for a proposed target-free repair, not evidence that the current palette repairs it.

## What the 3-adic labels do and do not obstruct

`r_3` is frozen under quadratic moves, and none of the fixed units or the essential cubic changes its multiplicity.  It does **not** obstruct any `n>=7` in this progression.  For every odd generator `r_u=u/T(u)`, `T(u)` is coprime to 3, so `v_3(r_u)=v_3(u)>=0`.  If `3|n`, the actual certificate's first factor `r_n` and the virtual certificate's first factor `r_(5n)` each consume the full `v_3(n)`.  Every other odd factor is therefore 3-free; in particular neither side contains `r_3`.  If `3∤n`, all odd factors are 3-free.

For `n=135`, the exact 3-divisible residual is `+r_135-r_675`.  This lies outside the **3-free search domain** used to find the 71 witness, so that existing search result says nothing about repairing 135.  It is **not** an invariant of the formal `AllowedMove`: that relation permits arbitrary legal positive-odd quadratic exchanges, including labels divisible by 3.  The CLI reports the mismatch to mark where a 71-specific search cannot be reused directly, not as a no-repair theorem.

## Reuse versus a parametric rule in the saved engine witnesses

The optional `compare` command accepts two signed lattice-witness JSON files and compares **oriented, constant-label** quadratic rows after expanding the sign of each coefficient.  The saved engine files for 199 and 263 both have complete finite repair witnesses, but their targets overlap the known 71 path heavily:

| Target | Constant Q rows shared with 71 | Shared weighted Q uses | First target join with 71 | Shared target tail |
|---|---:|---:|---|---:|
| 199 | 37 of 134 | 72 | `182` at steps `(16,5)` | 60 steps |
| 263 | 37 of 220 | 69 | `263` at steps `(0,14)` | 51 steps |

The 71 witness has 125 unique oriented Q rows.  For 199, rows touching its distinguished source labels `5n=995` and `(15n+1)/2=1493` occur five times each by coefficient weight; rows touching target label `n=199` occur 17 times.  For 263 the corresponding weights for `1315,1973,263` are `1,1,3`.  The exact numeric rows differ; the overlap is constant-label reuse.  More importantly, `263` itself is on 71's target orbit, so its entire known target trajectory is inherited.  These finite witness comparisons do not identify a rule parameterized by `n` or a decreasing repair measure.

The decisive missing result remains a symbolic, target-free transformation of the canonical inverse-five certificate, with legal catalysts and a strictly smaller proof state.  The fixed-offset families mainly measure selection bias, while the growing-run family tests whether any proposed transformation handles genuinely delayed descent.  None of the finite target-path profiles proves that transformation.
