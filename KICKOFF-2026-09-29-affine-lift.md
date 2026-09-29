# Exact affine deformation, scoped research formalization

Own only `CollatzMoonshot/Obstructions/AffineQLift.lean` and
`HANDOFF-2026-09-29-affine-lift.md`. Prove four frozen statements, root build,
commit green, stop. Opus/low bounded; no Aristotle. Other agents own Python/docs.

Write F=1+3(3x+1)(3u+1)t, G=1+9u(3x+1)t,
H=1+9x(3u+1)t. Then U=uF, X=xF, B=bG, Z=zH,
3U+1=(3u+1)G, 3X+1=(3x+1)H.
The new cross-equation difference equals F*G*H times the old difference;
the residual linear-in-t coefficient cancels identically. `linear_combination`
with multiplier F*G*H after casting to integers, or a ring rearrangement
and congrArg on hQ, should close. Do not weaken the type.

Bounds: X<U by common positive F; Z=zH < uF since z<u and H<=F.
Parity: U,X added slope contains even 3x+1 or3u+1 because originalsodd;
B,Z same. All added slopes divisible3. Positive originallabels givepositive.
Unbounded: t=M+1 suffices since slope>=1 from hu.

This theorem is a calibration of novelty: an isolated numeric Q row
always creates an infinite family. It does not prove recursive closure,
units, or global repair. Shared store status and relake plan were checked
this session; dependencies already built. No package downloads required.
