#!/usr/bin/env python3
"""Max |x_w| over all words w of length p <= 12, where x_w is the (rational) periodic point."""
import itertools
from fractions import Fraction
for p in range(1,13):
    best=Fraction(0)
    for w in itertools.product(range(3),repeat=p):
        a,b=Fraction(1),Fraction(0)
        for s in w:
            bits=1 if s==0 else 2; d=(0,1,-1)[s]
            a,b=a*3/2**bits,(b*3+d)/2**bits
        if a!=1: best=max(best,abs(b/(1-a)))
    print(p,float(best))
