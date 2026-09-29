# Bounded Lean task: Q1 positive coalescence and hard-shadow separation

Work only in `CollatzMoonshot/Obstructions/Q1Coalescence.lean` from the staged skeleton.  Import `CubicCarry`.  Preserve the two definitions and eight frozen theorem statements.  Every claim uses the actual `FrontB.tstep`.  Use at most two bounded laps: first the offset and positive class, then the hard-shadow ordered separation.  Do not weaken the final statement or add a convergence assumption.

## Reusable actual-orbit offset

Prove by induction on `k`, generalizing `x,d`:

```
T^[k](x+2^k*d) = T^[k]x + 3^(ones(traceWord x k))*d.
```

One step from `x+2d` shares `x`'s parity and equals `T(x)+(if x odd then 3*d else d)`.  The recursive trace definition supplies the exponent.  At `k=0`, the identity is immediate.  The `near_one_cycle_le_double` helper applies this at each `j≤K` to `1+2^K*u`.  The base orbit alternates `1,2`; its odd counts are `r` at time `2r` and `r+1` at time `2r+1`.  Thus the perturbation contracts by `3/4` per two steps, and every endpoint through depth `K` is at most twice the initial value.  A direct odd-even pair induction is also acceptable.

## Positive 11-step class and 18-step bridge

`branchQ t=105+2^11*t`.  Direct finite evaluation gives

```
T^[11](105)=38,      ones(traceWord 105 11)=6,
T^[11](2837)=38,     ones(traceWord 2837 11)=3,
2837=27*105+2.
```

The offset helper yields both endpoints `38+729*t`: the second offset is `27*t`, compensated by `3^3*27=729`.  Exact specialization:

```
q1(240+1024*t)
  = 660371019881+2809920153600*t
  = branchQ(322446787+1372031325*t).
```

`CubicCarry.cubic_carry_sixth` gives `T^[6](cubicN s)=18*q1(s)+1`, an odd number, so one actual step yields `T^[7](cubicN s)=27*q1(s)+2`.  `Function.iterate_add_apply` and the branch endpoint give the 18-versus-11 equality.  The common endpoint on the hard slice is `235063707761+1000210835925*t`, while `cubicN(hardParam t)=9391943393863+39963308851200*t`.  Constant and slope comparison proves strict 18-step descent.

## Hard-shadow ordered separation

Fix `K`, write `q=cubicQ1 s`, `n=cubicN s`, `w=9*q+1`.  Apply `CubicPeel.cubic_peel_growth_divisibility (K+1)`: it supplies `s` with `2^(K+3)|cubicP s+1`.  Since `cubicP s+1=2*w`, we have `w=2^(K+2)*u` for some `u>0`.  The existing affine forms give `128*q=9*n+1` and `T^[6]n=cubicP s=2*w−1>n`.

The first six `n` iterates have the affine values already listed in the `CubicCarry` kickoff, each at least `n`.  Starting at `p=T^[6]n=2^(K+3)*u−1`, induction on `0≤r≤K` gives

```
T^[r]p+1 = 3^r * 2^(K+3−r) * u.
```

The remaining power of two makes each pre-step value odd; its shortcut step rises.  Thus `n≤T^[i]n` for all `i≤K`, splitting `i≤6` from `i=6+r`.  A local general odd-run lemma is welcome if it shortens this proof.  `FrontA.FirstCrossingTwoRun.run_true` can certify the endpoint after the trace is established, but direct induction may be simpler.

The same divisibility gives `q≡3 (mod 4)`, so its first two steps are odd and

```
T^[2]q=(9*q+5)/4=1+w/4=:R=1+2^K*u.
```

Every later auxiliary prefix value `T^[j]q` with `2≤j≤K` is `T^[j−2]R≤2R` by the near-cycle helper.  The first two values `q,Tq` also satisfy `≤2R`.  Moreover `2R<n`: combine `4R=9q+5` with `9n+1=128q`; the strict inequality reduces to `47<175q`, valid for `q≥1`.  Hence all auxiliary prefix values are below `n`, while all original prefix values are at least `n`.  The pairwise no-meeting theorem follows directly from these two inequalities.

This proves failure of a **uniform bounded pairwise orbit splice** even on starts with arbitrarily long initial non-descent.  It does not exclude parameter-dependent meetings or supply a repair rank.  The older affine-slope obstruction in `RESEARCH-2026-09-29-affine-coalescence-slope.md` cannot exclude this pair because its slope ratio is `128/9`.  The separate `−1/13` synchronous nonmeeting and 15-step easy-descent control remain paper observations outside this Lean scope.


Operator scope: at most three Opus/low laps, 40-minute supervisor limit, no Aristotle.  The shared store was checked this turn and dependencies are warm.  Own only Q1Coalescence.lean and HANDOFF-2026-09-29-q1-coalescence.md.  Parent owns all other source/docs, including the root import and kickoff.  Do not alter any frozen definition or theorem statement; prove the ordered-separation claim itself, not a statement about an affine surrogate.  Helper lemmas inside this module are allowed.  Do not change existing modules.  Build module/root, commit green, then box done --green immediately.  No successor tasks.
