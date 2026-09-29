# One-lap target: legal Q move at two artificial five-head families

Copy the staged `FiveHead.lean` into the repo as a new
`CollatzMoonshot/Obstructions/FiveHead.lean`, importing `Repair71`.  Prove the
two frozen `legalPairMove = true` declarations and the elementary lower-height
inequality.  Do not add a unit-borrowing theorem, a general repair theorem, or
a Collatz conclusion.  Stop after one bounded proof lap and report the crux if
one equality remains open.

The exact frozen declarations are:

```lean
namespace CollatzMoonshot.Obstructions.ArithmeticLifts.RestrictedRepair

def observedN (h : ℕ) : ℕ := 1031 + 8868288 * h
def observedC (h : ℕ) : ℕ := 1045 + 8988672 * h
def observedD (h : ℕ) : ℕ := 5525 + 47523840 * h

theorem observed_five_head_pair (h : ℕ) :
    legalPairMove [5 * observedN h, observedC h]
      ([5 * observedN h, observedC h], [observedN h, observedD h]) = true

def lowerN (h : ℕ) : ℕ := 9223 + 16320 * h
def lowerC (h : ℕ) : ℕ := 3689 + 6528 * h
def lowerD (h : ℕ) : ℕ := 5425 + 9600 * h

theorem lower_five_head_pair (h : ℕ) :
    legalPairMove [5 * lowerN h, lowerC h]
      ([5 * lowerN h, lowerC h], [lowerN h, lowerD h]) = true

theorem lower_five_head_height (h : ℕ) :
    lowerC h < lowerN h ∧ lowerD h < lowerN h
end CollatzMoonshot.Obstructions.ArithmeticLifts.RestrictedRepair
```

`legalPairMove` is defined in `CatalyticRepair.lean`: its `decide` checks input
availability, pair lengths, positive odd labels, and equality of
`certificateValue 0` on the two pair lists.  Availability here is reflexive
because the state is exactly the input pair.  The first three conditions
should reduce with `simp` and `omega` after unfolding the six linear labels.
Do not try `native_decide` on a variable `h`.

For the value equality, use the odd-label formula
`(u:ℚ)/(tstep u:ℚ)=2*(u:ℚ)/(3*(u:ℚ)+1)`.  It follows from
`u%2=1` and `2*tstep u=3*u+1`; prove that latter Nat equality by unfolding
`tstep` and `omega`, then cast.  The four denominators are positive.  The
remaining equality is equivalent to

```text
d * (15*n + 1 - 12*c) = 5*c*(3*n + 1),
```

where `n`, `c`, `d` are cast to `ℚ`.  For each family this is a polynomial
identity in `h`, so `dsimp [observedN, observedC, observedD]` or the lower
counterparts, `push_cast`, and `ring` suffice.  Cross multiplication of the
ratio equality yields

```text
5*c*(3*n+1)*(3*d+1) = d*(15*n+1)*(3*c+1),
```

which is `Q5` after expansion.  This route avoids a large `norm_num` call on
symbolic rational division.  `lower_five_head_height` is linear arithmetic:
`n-c=5534+9792*h`, `n-d=3798+6720*h`.

The chosen progressions keep `n≡7 (mod 64)` and all four labels `n,c,d,5n`
positive, odd, and not divisible by 3.  These congruences explain the choice
of coefficients; the actual legality test asks only positive odd and value
equality.  A legal Q move under availability is the entire requested result.
In particular `observedC h>observedN h`, and no uniform legal unit containing
`observedC h` is known.  The lower family still leaves `lowerD h` in the word
and does not complete the virtual-to-actual repair.
