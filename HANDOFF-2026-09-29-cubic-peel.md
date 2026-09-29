# Cubic continuation on the hard CRT subclass

The five intended statements are in `CubicPeel.lean`: the exact cubic
certificate equality; positive odd 3-free edge labels and auxiliary bounds;
the two shortcut frontiers; the original-family link; and arbitrary-depth
2-power growth congruences. The smaller endpoint is
`cubicM s = 17959838810 + 27440626500*s`, which is even. Consequently
`tstep (cubicV s) = 16*cubicM s`. A worker temporarily halved this endpoint
to make it odd and changed 16 to 32; the parent restored the frozen meaning.
The seven edge labels are odd; the endpoint was never required to be odd.
CI's existing `scripts/AxiomAudit.lean` now checks the exact endpoint and
consumer signatures. The divisibility proof is retained as a helper for the
original explicitly written Nat.ModEq theorem.

Both products equal `4(2a-7)/(3(9a+61))`, where a=tstep(n). The CRT family
is n=25542881863+39026668800s, and
T^6(n)+1=4(8081927465+12348281925s). The source file proves the congruence
needed for arbitrary odd-run lengths; the dynamics interpretation is recorded
in `RESEARCH-2026-09-29-head-continuation.md`.

This is outside the fixed-C5 palette. It proves no full repaired flow,
borrowing return, rank decrease, or convergence. The completed block and
ordinal-rank target are in `RESEARCH-2026-09-29-ordinal-repair-checkpoint.md`.
