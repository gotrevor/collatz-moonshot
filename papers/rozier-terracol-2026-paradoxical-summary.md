# Rozier--Terracol 2026: paradoxical Collatz sequences

Primary source: Olivier Rozier and Claude Terracol, *Paradoxical behavior in Collatz
sequences*, Discrete Mathematics 349 (2026), 115167,
<https://arxiv.org/html/2502.00948v5> (v5, 2026-05-17).

## Definitions

For the shortcut map `T(n)=(3n+1)/2` on odd `n` and `T(n)=n/2` on even `n`, a length-`j`
segment with `q` odd terms has

```text
T^j(n) = (3^q/2^j)n + E_j(n).
```

Apart from the stipulated trivial-cycle cases, it is paradoxical when
`3^q/2^j < 1` but `T^j(n) ≥ n`. It is cyclic when equality holds and acyclic when the
endpoint is strictly larger.

## Results used by this repository

- Theorem 2.4 orders parity words by shifting ones and gives sharp lower/upper remainder
  bounds for fixed `(j,q)`. This is the natural exact bound for branch-and-bound enumeration.
- Theorem 3.2: any `n≥2` with infinite stopping time (`T^j(n)≥n` for all `j`) produces
  infinitely many paradoxical segments starting at numbers `2^k n`.
- Corollary 3.3: finitely many paradoxical segments in total would imply Collatz.
- Theorem 4.2 and Corollary 4.3 constrain a paradoxical segment by the harmonic mean `h` of
  its odd terms:

  ```text
  log 2 / log(3 + h^-1) ≤ q/j < log 2 / log 3.
  ```

- Appendix A excludes the parity shape consisting of one initial odd block followed by an
  even block (outside the trivial/cyclic exclusions used there).

The paper verifies no paradoxical start strictly between `4614` and `2.8×10^19` using
published trajectory data, then conjectures that none starts above `4614`. The authors state
that conjecture is stronger than Collatz and the coefficient-stopping-time conjecture.

## Strength warning

Theorem 3.2 is theorem-grade literature and may be cited. Global finiteness is conjectural
and must not be axiomatized as a known result. Its implication to Collatz does not establish
that finiteness is an easier target. For a Front-A-only corollary, the repository must also
show that a divergent orbit yields infinitely many **acyclic** witnesses; this is a derived
specialization, not the verbatim published theorem statement.
