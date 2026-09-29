# Bounded mergers to arbitrary smaller seeds: bounded Lean campaign

Own only `CollatzMoonshot/Obstructions/BoundedMerger.lean` and `HANDOFF-2026-09-29-bounded-merger.md`.  Preserve both frozen theorem statements exactly.  Parent owns the root import and `BoundedMergerConsumers` in `scripts/AxiomAudit.lean`; do not edit them.  At most three Opus/low laps, 35-minute supervisor limit, no Aristotle.  This is a genuinely stronger negative than fixed-Q1 separation: the smaller positive seed is completely unrestricted, and the two prefix lengths are independently bounded.  Do not replace it by a finite scan, a fixed auxiliary result, or a conditional theorem.

Read `RESEARCH-2026-09-29-bounded-small-merger.md` for the complete paper proof.  This proof was independently checked by the parent and the research agent.  Report any statement defect immediately; do not weaken the frozen type.

## Suggested implementation structure

The import Q1Coalescence provides the actual map and parity-word tools.  Inspect `FrontB/Dictionary.lean`, the affine numerator definitions it imports, and `tstep_iterate_pow_two_offset`.  Private rational/integer helper maps and lemmas may be introduced, but the public targets must concern the actual natural `FrontB.tstep`.

For an arbitrary word of length j with p odd steps, let c be its affine numerator and g=2^j+c.  Starting at 1, g multiplies by 3 at an odd extension and adds 2^j at an even extension.  Prove `3^p ≤ g ≤ 2^(j-p)*3^p`.  The upper bound follows since c≥0 gives g≥2^j, so an even extension at most doubles g.

If `2^K ∣ n+1`, the first K steps of n are odd and `2^i*(T^i n+1)=3^i*(n+1)` for i≤K.  The one-step inequality `2*(T x+1)≤3*(x+1)` excludes j≤i for a smaller b.  Thus a purported meeting has d=j−i>0.  If the j-word on b has p odds, its affine relation gives

```
3^p*b = 2^d*3^i*n + 2^d*3^i - g.
```

If alpha=2^d*3^i/3^p>1, then alpha−1≥1/3^K and the intercept is strictly greater than −2^(j-p).  The hypothesis n≥6^K gives b>n.  Avoid rational denominators if more convenient by cross multiplying and using `3^p ≤ 3^K`.  Alpha=1 is impossible because d>0 and powers of 2 and 3 cannot coincide.  The only remaining case is p>i, q=p−i, and 2^d<3^q.

Because `3^q ∣ n`, write `b=2^d*(n/3^q)−L`.  Here L is a positive integer and `L<2^(j-p)`, by the bounds on g.  Work in integers to avoid saturating natural subtraction.  Thus b and −L agree modulo 2^d.  A signed-map parity transport lemma shows their first d words agree.  If p0 counts those odds and `z=T_Z^d(-L)`, then z<0 and

```
T^d b = 3^(p0-q)*n + z.
```

Since the remaining i letters have at most i odds, p0≥q.  Put a=p0−q.  The remaining word has i−a odds and a evens.

### Shorter final contradiction (no second signed transport needed)

Let g_tail=2^i+c_tail for that remaining word.  Equate its affine endpoint with T^i n and cancel the common `3^i*n` term.  This gives

```
3^(i-a)*z + g_tail = 3^i.
g_tail ≤ 2^a*3^(i-a).
```

Since z<0, this implies `3^a < 2^a`, impossible.  This replaces the final negative-path magnitude argument in the paper and avoids a second signed parity transport lemma.  Use whichever presentation simplifies Lean.

CRT supplies arbitrarily large n divisible by3^K with n+1 divisible by2^K; add multiples of6^K to exceed both M and6^K.  A deterministic diagnostic witness is

```
n = 3^K*((-inverse(3^K mod 2^K)) mod 2^K) + 6^K*(M+1).
```

No computational inverse is required in the theorem; Mathlib CRT/Coprime/ModEq existence should suffice.  K=0 has no problematic merger because both depths are zero; handle it separately if helpful.

## Validation and scope

Hand controls: K1 n9, target prefix9→14, no positive smaller seed meets within1 step on either side.  K2 n63, target63→95→143, likewise through2.  Countercontrols outside the cylinder: 27→41→62→31, so n31 has smaller seed27 meeting at depths0 and3; 15 and14 meet at20 after6 steps each.

Before this campaign the parent ran `lake-base status 4.33.1` and `relake plan --from /Users/gotrevor/.lake-base/4.33.1 /Users/gotrevor/src/collatz-moonshot`; the dependency tree is warm.  Do not download or deduplicate it.  Run the module, root build, and `lake env lean scripts/AxiomAudit.lean` after proving both public statements.  Parent's new CLI tests may arrive separately; do not edit them.  Commit green work.  Finish `box done --green` only after actual checks pass.  If the bounded run ends with unfinished lemmas, preserve a precise handoff explaining the mathematical or Lean blocker, without claiming completion or inventing successor tasks.

This proves an obstruction to uniformly bounded merger certificates.  It does not disprove variable-depth induction, exclude divergence or cycles, formalize Monks' theorem, or claim historical novelty.
