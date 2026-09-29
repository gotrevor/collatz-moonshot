# Endpoint matching for affine quadratic borrowing rules

Let `r_v=2v/(3v+1)`.  Work with integer-affine labels
`U(t),B(t),X(t),Z(t)` having positive slopes, positive values for all
sufficiently large integers `t`, and the exact rational-function identity

```text
r_U(t) r_B(t) = r_X(t) r_Z(t).
```

This is a classification **inside the positive-slope affine grammar**.  It
does not classify numeric quadratic exchanges or rules valid only after
reparametrizing a smaller residue class.

For `L(t)=a+bt`, `b>0`, put

```text
z(L)=-a/b,      p(L)=-(3a+1)/(3b)=z(L)-1/(3b).
```

These are the roots of `L` and `3L+1`; always `p(L)<z(L)`.  Clearing
denominators in the quadratic identity gives the multiset equality

```text
{z(U),z(B),p(X),p(Z)} = {z(X),z(Z),p(U),p(B)}.       (1)
```

All factors are linear.  Their leading-coefficient products are both
`9 slope(U) slope(B) slope(X) slope(Z)`, so (1) is also sufficient.

**Endpoint attachment.**  At least one of `X,Z` shares either U's zero
root or U's pole root.  Otherwise the occurrence of `z(U)` on the left of
(1) must match `p(B)` on the right, and `p(U)` on the right must match
`z(B)` on the left.  This says `p(B)=z(U)>p(U)=z(B)`, contradicting
`p(B)<z(B)`.  The argument needs no height assumption and survives
coincident roots because it is a multiset argument.

If both inputs `X,Z` are eventually strictly below `U`, relabel the
attached input as `X`.  Shared zero gives `X=qU`; shared pole gives
`3X+1=q(3U+1)`.  In either case `q=slope(X)/slope(U)` is rational with
`0<q<1`.  Equality `q=1` would give `X=U`, contrary to strict height.

With distinct roots, the remaining matches have two forms.  For shared
zero `z(X)=z(U)`, they are

| Form | Remaining root equalities |
|---|---|
| Two connected paths | `p(U)=z(B)`, `p(X)=z(Z)`, `p(B)=p(Z)` |
| Crossed rectangle | `p(U)=p(Z)`, `p(X)=p(B)`, `z(B)=z(Z)` |

For shared pole `p(X)=p(U)`, exchange zeros and poles in the same
multiset calculation:

| Form | Remaining root equalities |
|---|---|
| Two connected paths | `z(U)=p(B)`, `z(X)=p(Z)`, `z(B)=z(Z)` |
| Crossed rectangle | `z(U)=z(Z)`, `z(X)=z(B)`, `p(B)=p(Z)` |

The endpoint-attachment lemma, rather than this distinct-root table, is
the assertion used below; coincident roots may merge rows of the table.

Write `U=a+bt` with integer `a,b`, `b>0`, and `q=p/m` in lowest terms,
`0<p<m`.  Integer-affine `X` imposes exact denominator gates:

* If `X=qU`, then `m | gcd(a,b)`.
* If `3X+1=q(3U+1)`, then `m | gcd(3a+1,b)` and
  `p ≡ m (mod 3)`.  Indeed the slope of `X` is `pb/m` and its constant
  term is `(p(3a+1)/m-1)/3`; `m` is coprime to 3.

These are necessary conditions, not construction theorems.  For every
positive odd `a` coprime to 3, the full progression `U=a+6t` has
`gcd(a,6)=1` and `gcd(3a+1,6)=2`.  Zero sharing is impossible.  Pole
sharing would require `m=2,p=1`, violating `p ≡ m (mod 3)`.  Therefore
**no positive-slope integer-affine quadratic identity can introduce the
entire progression `a+6t` from two inputs eventually strictly below it**.
This does not exclude introductions on a thinner residue subclass or
individual numeric borrowability.

For the current two recursive supply classes, the gates are:

| Required label `U(t)` | `gcd(a,b)` | `gcd(3a+1,b)` |
|---|---:|---:|
| `3349+124032t` | 17 | 64 |
| `785+29070t` | 5 | 38 |
| `3005+151680t` | 5 | 8 |
| `5635+284400t` | 5 | 158 |

Thus this endpoint test does not close or obstruct these four supply
progressions.  It reduces a proposed full-parameter rule to finitely many
rational `q` denominators, followed by exact parity, 3-freeness, second
input, and height checks.  The separate eight-congruence computation in
`affine_scan.py closure` rules out only direct equality of one of these
inputs with either existing supplied-head progression.
