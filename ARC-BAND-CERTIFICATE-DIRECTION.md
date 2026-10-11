# Direction: domination for the component game, then the upper-edge certificate in Lean

Two targets, in this order.  Done when both are proved and `#print axioms` for each shows only `propext`,
`Classical.choice`, `Quot.sound` (plus `native_decide` axioms for item 2).

1. `ArcDelayGame.finiteMemoryRelaxedValue_of_componentK` (`CollatzMoonshot/Benchmark/ArcDelayGame.lean`).
2. `ArcBandCertificate.relaxedAboveUpperEdge` (`CollatzMoonshot/Benchmark/ArcBandCertificate.lean`).

Item 1 is complete (2026-10-10): the component strategy is constructed with the prescribed absolute
windows, and the floor/fractional-part and binary carry identities are proved in Lean.

Item 2 is complete (2026-10-11): `ArcBandCertificate.relaxedAboveUpperEdge` is proved from a Lean
transcription of the symbolic interval descent, a pointwise superset theorem, the checked triangle trees,
and the finite-zero left-shift argument.  Both ordered targets are complete.

Never weaken a statement.  Commit green after each milestone.  Edit only: the proof of item 1 (plus helper
lemmas placed directly above it), `ArcBandCertificate.lean`, new files `ArcBandCertificate*.lean` (root-import
them in `CollatzMoonshot.lean`), and this file.  Do not edit `experiments/` (the Python tool is the spec).

## Item 1: domination (small)

From a `KRelaxedStrategy β (1 - 2β) l k P` with some `P r` nonempty (`r < 2^k`, `1 ≤ k`), build a
`KComponentStrategy β k S`, contradicting `ComponentKValue`.  Take

    S := {p | ∃ m : ℤ, ∃ a ∈ P (m % 2^k).toNat, p.1 ≤ m + a ∧ m + a + l ≤ p.2}.

For `p ∈ S` with witnesses `m, a`, let `r = (m % 2^k).toNat` and take `u, j` from the relaxed step at `r, a`.
Use the component index `J = m + j`: the sub-window `[m + u, m + u + 2l/3]` lies in `p` and in
`[J + β, J + 1 - β]`, so `max p.1 (J + β) < min p.2 (J + 1 - β)` (strict because `l > 0`).  For the child at
shift `z`, the witnesses are `m' = ⌊3(m + u)/2⌋ + z 2^(k-1)` and `a' = Int.fract (3u/2 + (r % 2)/2)`.  The
identity `Int.fract (3(m+u)/2) = Int.fract (3u/2 + (m % 2)/2)` holds because `3m/2 = (3m - m%2)/2 + (m%2)/2`
(the first term an integer).  Reuse `ArcFattening.physical_child_decomposition`, `physical_child_fract` and
`physical_child_floor`, which prove exactly these identities (their residue helpers cover negative `m`).
And `m' mod 2^k` equals `((3r - r%2)/2 + ⌊3u/2 + (r%2)/2⌋.toNat) % 2^(k-1) + b 2^(k-1)` for one bit `b < 2`,
which the relaxed step covers.  Here `(3m - m%2)/2 ≡ (3r - r%2)/2 (mod 2^(k-1))` because `m ≡ r (mod 2^k)`,
and the floor is `≥ 0` because `u ≥ a ≥ 0`.

## Item 2: the band certificate (larger)

Complete (2026-10-11): `ArcBandCertificate.lean` implements the affine interval-list computation and proves
that every successful symbolic step evaluates to a superset of the semantic relaxed-strategy operator.
The generated triangle trees are checked by `certificate0` and `certificate1`; coefficient identities and
positive-multiple edge checks turn the vertex oracle into pointwise signs on each strict triangle interior.
All comparison forms have nonzero `β` coefficient, so `exists_beta_avoiding` shifts boundary points left
past the finite zero set and `RelaxedStrategy.mono` transports a hypothetical strategy to a certified leaf.
The headline theorem depends only on `propext`, `Classical.choice`, `Quot.sound`, and the two expected
per-certificate `native_decide` axioms.

The math: `ArcDelayGame.RelaxedAboveUpperEdge`'s docstring and `experiments/arc_band.py` (read both).
Astra (Codex) reviewed the tool and the boundary argument on 2026-10-10 and found no defect.

### Lean design (the checker is yours to shape; these are the obligations)

* `Aff := c + b β + w l` with `ℚ` coefficients, evaluated at real `(β, l)`.
* **Pointwise soundness of the descent.**  Fix real `(β, l)` with `0 < l`.  Let `F(Q) = {a ∈ Q | ∀ d ∈ {0, 1/2},
  ∃ u ∈ [a, a + l/3] ∩ G, Int.fract (3u/2 + d) ∈ Q}`, `G = [β, 1 - β - 2l/3] ∪ [1 + β, 2 - β - 2l/3]`.  A
  `RelaxedStrategy β (1-2β) l P` has `P ⊆ [0,1)` and `P ⊆ F(P)`; `F` is monotone, so `P ⊆ P_n` for the
  descent `P_0 = [0,1]`, `P_{n+1} = F(P_n)`.  The symbolic step (interval lists of `Aff` pairs, closed
  intervals, operations exactly as in `arc_band.py`: preimage `(2/3)(x + j - d)` for `j ∈ {0,1,2}`, intersect
  with `G`, Minkowski `[p - l/3, q]`, merge, intersect over `d`) must evaluate at `(β, l)` to a SUPERSET of
  `F` of the evaluated input, whenever every comparison it makes is decided by an oracle that is correct at
  `(β, l)` (sign `0` means the two forms are equal there).  Enumeration facts (Astra): `u ∈ [0, 3/2)`, so
  `⌊3u/2 + d⌋ ∈ {0, 1, 2}`, and arc lifts with `j < 0` cannot meet a legal window.
* **Vertex sign oracle on an open triangle.**  For a triangle with rational vertices `v₁ v₂ v₃` and a point
  `p = Σ λᵢ vᵢ`, `λᵢ > 0`, `Σ λᵢ = 1`: an affine `f` has `f p = Σ λᵢ f vᵢ`, so all `f vᵢ ≥ 0` with one `> 0`
  gives `f p > 0` (and all `= 0` means `f ≡ 0` on the plane only if the vertices are affinely independent; use
  syntactic equality of coefficients for sign `0`).  The barycentric `λᵢ` are affine in `p`; the checker
  verifies each `λᵢ` is a positive multiple of one of the leaf's accumulated constraints (below), so the
  constraints being `> 0` at `p` puts `p` in the open triangle.
* **Decision tree.**  `node f pos neg`: `pos` covers `f > 0`, `neg` covers `f < 0`.  `leaf v₁ v₂ v₃ n`: the
  descent on that triangle empties within `n` steps.  A point satisfying the root's strict constraints and
  `f ≠ 0` at every node reaches a leaf whose accumulated constraints are all `> 0` at it.
* **Boundary points (shift).**  Every `f` in the trees and every root constraint has a nonzero `β`
  coefficient (the checker verifies this).  For `p = (β₀, l₀)` with `1/10 ≤ β₀ ≤ 7/57`, `u(β₀) < l₀`: if
  `l₀ > 3/2 - 3β₀`, `G` is empty (`2l/3 > 1 - 2β`) and there is no strategy directly.  Otherwise pick
  `β' ∈ (β₀ - ε, β₀)` off the finitely many zeros of the listed forms (each has at most one zero on the line
  `l = l₀`), with `ε` small enough that `β' > 1/12` and `l₀ > u(β')`.  Then `(β', l₀)` is strictly inside one
  root piece, the tree applies, and `RelaxedStrategy.mono` (`β' ≤ β₀`) moves the conclusion to `(β₀, l₀)`.
* **Roots.**  Piece 0: `β > 1/12`, `β < 1/9`, `l > 3/4 - 39β/8`, `l < 3/2 - 3β`.  Piece 1: `β > 1/9`,
  `β < 7/57`, `l > 15/16 - 105β/16`, `l < 3/2 - 3β`.  (For `β < 1/9` the minimum in `u` is the first piece.)
* `native_decide` runs the checker on the data file.

### Data (landed)

`CollatzMoonshot/Benchmark/ArcBandCertificateData.lean`, GENERATED by `experiments/arc_band.py export PATH`
(do not edit by hand; ask for a regeneration if you need a different shape, or convert it in Lean).
It defines `Aff` (`c + b β + w l`, `ℚ` fields), `CTree` (`leaf v₁ v₂ v₃ depth | node f pos neg`), and
`root0 root1 : List Aff` (strict constraints, `form > 0`) with `tree0 tree1 : CTree`.  64 + 38 triangle
leaves, leaf depths `≤ 8`.  The Python twin of the checker (`check_tree`) verifies, per leaf: each barycentric
coordinate is a positive multiple of an accumulated constraint (root constraints, then `f` on `pos`, `-f`
on `neg` branches), and the descent with the vertex sign oracle is empty within `depth` steps; per tree:
every form has `b ≠ 0`.  Teeth-tested: a lowered leaf depth and swapped branches are both rejected.
