# From relation lattices to legally borrowed catalysts

The catalytic branch has two separate computational problems: finding an integer relation among allowed moves, and supplying the factors needed to execute it.  Separating them gives a constructive alternative to breadth-first search through all intermediate certificates.  This is elementary commutative rewriting, not a claim of a new general algebraic theorem or a Collatz proof.

## A signed relation has an explicit catalyst

Represent a certificate by its nonnegative integer multiplicity vector, including the factor 2 as a separate coordinate.  Every permitted reversible rule has input vector l and output vector r.  Unit insertion is a rule 0 -> u; removal is its reverse.

Suppose y-x is an integer linear combination of rule differences r-l.  Expand the combination into a finite ordered list of oriented rules (l_j,r_j), repeating and reversing rules as required.  Put s_0=0 and s_j=sum_(i<=j)(r_i-l_i).  Define, coordinatewise,

```
c(v) = max(0, max_j (l_j(v)-x(v)-s_(j-1)(v))).
```

Then each prescribed move is available in x+c+s_(j-1), and the sequence ends at y+c.  All vectors have finite support.  This c is the least common catalyst for that particular ordering.  Conversely, any finite path x+c -> y+c telescopes to an integer relation for y-x.

Thus integer relation-lattice membership is exactly reachability with some arbitrary common catalyst.  Rational row-span membership is insufficient: the integer coefficients matter.  This statement concerns a finite witness of moves, even when the allowed rule family is infinite.

## A catalyst must be borrowable under the actual rules

The preceding theorem does not authorize adding c to a Collatz certificate.  We need a word W reachable from the empty word using the chosen rules, with W>=c coordinatewise.  Such a W has scalar value one because all rules preserve scalar value.

Then there is an actual repair:

```
x -> x+W -> y+W -> y.
```

The first and last paths construct and unconstruct W.  The middle path uses the lattice witness, with the unused coordinates W-c carried along.  No unrestricted value-one insertion has been assumed.

Call a generator borrowable when it occurs in some word reachable from the empty word.  Finitely many individually borrowable generators can be borrowed simultaneously with any finite multiplicities: concatenate enough copies of their witness words.  Therefore every catalyst supported on borrowable generators can be supplied.

## Exact closure rule for discovering borrowable generators

Initialize the borrowable set with every generator in the permitted unit words.  If every generator appearing in the input of an allowed oriented rule is already borrowable, every generator in its output becomes borrowable.  Multiplicities cause no difficulty, because witnesses can be copied.  Store the derivation, not just the set.

This closure is also complete for which individual generators are borrowable.  In any finite derivation from the empty word, the inputs of the next move have already appeared; induction puts all its output generators in the closure.  Conversely, the witness construction above realizes every closure addition.  This is an infinite closure problem for the full quadratic family; any finite computed stage certifies only its included generators.

For the present palette, the initial odd labels are

```
1,5,7,11,17,19,25,29,55,65,83,
```

and the factor 2 is borrowable.  The permitted cubic immediately adds 13.  The quadratic rule {11,17} -> {7,121} makes 121 borrowable.  More concretely, applying it inside U13 gives the unit 2^5 r5 r7^3 r55 r65 r83 r121.  This explains how the catalyst used in the earlier cubic example can be supplied by the restricted palette.

## What this buys, and what it does not

For a concrete source and target, search for (1) an integer relation witness and (2) borrowability derivations covering its computed catalyst.  Together these are a finite, replayable repair certificate.  Failure of a finite lattice or closure truncation is not a global obstruction.

Even a complete scalar presentation would not manufacture a target path.  Repairs toward the known path for 71 remain a diagnostic of the presentation.  The separate Collatz task is to select a target or a well-founded repair measure that forces actual vertex balance without assuming termination of the orbit.

The other two research branches retain their own open inputs: a cycle-excluding joint arithmetic inequality, and an independent arithmetic estimate for anchored operator defects.  There is no shared single remaining crux.
