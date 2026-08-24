# Front A: parity reconstruction and the carry barrier

## Why this is the live pull

Milestone M2′ is complete:

```lean
parityRigidityW1'_imp_noDivergent :
  ParityRigidityW1' → NoDivergentOrbit
```

The measure-theory bridge is no longer the gap.  The remaining Front-A content is
arithmetic: explain why the parity itinerary of an **ordinary positive integer** cannot
sustain the critical upward drift forever.  Unrestricted 2-adic itineraries cannot work:
the Collatz map on `ℤ_[2]` sees the full binary shift, including the negative `-1 ↔ -2`
cycle with excessive odd mass.

The next concrete coordinate is the inverse parity map: read a finite shortcut-Collatz
parity word and reconstruct, one bit at a time, the unique starting residue that realizes
it.  The output bits are the binary digits of the starting integer; the internal endpoint
is the carry coupling the parity word to archimedean size.

## Exact finite-prefix machine

Use the shortcut map `FrontB.tstep`, its parity trace `FrontB.traceWord`, and the already
proved identity

```text
2^m · tstep^[m](n) = 3^a · n + numer(v),
  v = traceWord n m,  a = ones(v).
```

For every word `v` of length `m`, define its canonical reconstruction residue `R(v)` as the
unique `r < 2^m` satisfying

```text
2^m ∣ 3^(ones v) · r + numer(v).
```

Uniqueness follows because `3^(ones v)` is a unit modulo `2^m`.  The expected exact
dictionary is:

```text
traceWord n m = v  ↔  n ≡ R(v) (mod 2^m),
R(traceWord n m) = n mod 2^m.
```

If `b` is appended to `v`, then

```text
R(v ++ [b]) = R(v) + c·2^m,       c ∈ {0,1}.
```

Write `a = ones(v)`, `p = 3^a`, `r = R(v)`, and

```text
q = (p·r + numer(v)) / 2^m.
```

Then the one-bit reconstruction/carry update is

```text
c = parity(q) XOR b

b = 0:  q' = (q + c·p)/2,          p' = p
b = 1:  q' = (3·(q + c·p) + 1)/2,  p' = 3p.
```

Here `c` is the next binary digit of the reconstructed starting value, while `q` is the
endpoint reached by the current canonical representative.  This is the precise finite
object to experiment on and formalize.

## The positivity condition and the hard intersection

For an infinite parity word `w`, let `R_m = R(w.take m)`.  It is the parity itinerary of a
natural number `n` exactly when the nested residues eventually stabilize:

```text
∃ M, ∀ m ≥ M, R_m = n.
```

Equivalently, the reconstruction output bits `c_m` are eventually zero.  Thus a divergent
positive orbit would produce an input/output pair with all three properties:

1. the output bits are eventually zero (`w` comes from `ℕ`, not merely `ℤ₂`);
2. the input is not eventually periodic (otherwise two orbit states have every finite
   parity prefix equal, hence are equal and the orbit repeats);
3. on every divergent tail it sustains shortcut odd density at the critical scale
   `log 2 / log 3` (equivalently raw odd density `log 2 / log 6`) often enough to defeat
   the drift lemma.

Ruling out that intersection is genuine Front A.  Merely renaming it is not progress; a
useful theorem must exclude a nontrivial class of carry processes or produce a checkable
repeat-or-descend certificate.

## Mandatory strength audit

Every finite parity word is realized by one residue class modulo `2^m`.  Therefore:

- no finite forbidden-word argument can prove Front A;
- no automaton whose state remembers only a bounded parity suffix can prove Front A;
- a frozen finite table is meaningful only if its state also carries a rigorously controlled
  archimedean/carry quantity and yields a depth-independent inequality;
- increasing memory and observing fewer survivors is not by itself a theorem.

This is the forward analogue of the 3-adic adversary that capped the backward local-potential
lane.  Record failed finite-state potentials and the adversarial words that defeat them.

## Next project: experiment first, formal kernel second

### A. Exact experiment

Create `experiments/parity_reconstruction.py` with exact integer arithmetic.

- Implement both the modular definition of `R(v)` and the online `(r,q,p,c)` recurrence;
  exhaustively cross-check them and `traceWord` on all words through a useful depth.
- Verify the prefix-bijection and nesting properties, not just sampled Collatz orbits.
- Search high-odd-density words while optimizing several honest carry objectives: delayed
  nonzero output, small endpoint `q`, small normalized endpoint `q/3^a`, and candidate
  Lyapunov increments.  Use beam search only as discovery; recheck any result exhaustively
  or with an exact certificate.
- Stress bounded-memory candidate potentials at increasing depths.  Preserve minimal
  adversarial words/cycles when a potential class fails.
- Separately test periodic/eventually-periodic inputs as a calibration class.  They should
  be excluded from divergence for structural reasons, not reported as a Collatz advance.

The valuable output is a stable invariant, a depth-independent inequality, or a precise
no-go for a well-defined certificate class.  A large census alone is not enough.

### B. Lean kernel

Add `CollatzMoonshot/FrontA/ParityReconstruction.lean`, reusing the existing
`FrontB.Words`/`FrontB.Dictionary` identity rather than duplicating it.  Target a small,
sorry-free API:

- existence and uniqueness of the realizing residue modulo `2^v.length`;
- `R(traceWord n m) = n % 2^m`;
- prefix nesting and the exact one-bit carry recurrence above;
- equality of naturals whose finite parity traces agree at every length;
- an eventually periodic parity trace forces an orbit repeat, hence cannot diverge.

The last item is a baseline restricted theorem.  Do not spend most of the project polishing
it if it becomes routine.  Formalize an experimental certificate only if it is genuinely
depth-independent and survives the strength audit.

### C. Stop/go criterion

At the end, classify the pull honestly:

- **GO:** a stable carry invariant or certified restricted rigidity theorem stronger than
  eventual-periodicity was found; state the exact next theorem.
- **REDIRECT:** bounded carry/memory potentials fail; land the exact counterexample family
  or finite-state obstruction and explain which extra unbounded state is missing.
- **BASELINE ONLY:** the reconstruction API is complete but no new invariant appeared; do
  not manufacture more Lean plumbing.  Return for a mathematical re-scope.

Do not claim `ParityRigidityW1'`, `EmpiricalParityRigidity`, or Collatz from finite data.
