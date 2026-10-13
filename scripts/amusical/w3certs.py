#!/usr/bin/env python3
"""Emit W3 certificates: 24 partial rules (forced values on cycle blocks) and, per completion,
an orphan word u (length L) with: for all s in Fin3^(L+2), exists j<L, f(s[j+2],s[j+1],s[j]) != u[j]."""
import itertools
src=open('w3check.py').read()
exec(src.split('blocks=list(')[0])  # defines cycles, partials
blocks=list(itertools.product(range(3),repeat=3))
def orphan(f):
    for L in range(1,8):
        imgs={tuple(f[(s[j+2],s[j+1],s[j])] for j in range(L)) for s in itertools.product(range(3),repeat=L+2)}
        for u in itertools.product(range(3),repeat=L):
            if u not in imgs: return u
used=sorted(set().union(*[set(P) for P in partials]))
print("blocks constrained by cycles:",len(used),"free:",[b for b in blocks if b not in used])
hist={}
lines=[]
for i,P in enumerate(partials):
    assert set(P)==set(used)
    free=[b for b in blocks if b not in P]
    row=[]
    for vals in itertools.product(range(3),repeat=len(free)):
        f=dict(P); f.update(zip(free,vals)); u=orphan(f); assert u
        hist[len(u)]=hist.get(len(u),0)+1; row.append(''.join(map(str,u)))
    lines.append(f"rule {i:2d}: "+' '.join(str(P[b]) for b in used)+"  orphans(free="+','.join(''.join(map(str,b)) for b in free)+" in lex order of values): "+' '.join(row))
print("orphan length histogram",hist)
open('w3certs.txt','w').write("blocks (a,b,c) = (sym V n, sym n, sym U n), order: "+' '.join(''.join(map(str,b)) for b in used)+"\n"+'\n'.join(lines)+'\n')
