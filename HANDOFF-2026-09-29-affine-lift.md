# Affine Q lifting: proved scope

`AffineQLift.lean` proves exact preservation of a quadratic cross identity,
smaller-input inequalities, positive odd 3-free labels, and unbounded heads.
For F=1+3(3x+1)(3u+1)t, G=1+9u(3x+1)t, H=1+9x(3u+1)t,
(U,B,X,Z)=(uF,bG,xF,zH), and the cross-equation difference is FGH times
the original difference. This calibrates infinitude: a single numeric row
already yields an infinite affine family.

The worker also proved compatibility of two rows with one matched head,
and two rows with one matched input/head. These reduce respectively to
(3x+1)t=(3x'+1)s and (3u+1)t=(3x2+1)s. Both have unbounded solutions.
These statements DO NOT cover diagrams with several shared labels, cyclic
constraints, fixed progressions, or supplied units. The initial handoff
incorrectly generalized them to all exchange compatibility; that prose has
been corrected. The theorem statements themselves retain their exact scope.

Frozen targets and the extra two-row statements were built and committed.
This scoped job is complete. Current research decision and the Goodstein
comparison live in `RESEARCH-2026-09-29-ordinal-repair-checkpoint.md`.
