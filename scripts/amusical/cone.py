#!/usr/bin/env python3
"""U(S) ⊆ S for S a union of classes mod M forces S = ∅ or ℤ: check that the residue graph
r -> U(x) mod M (x ≡ r mod M) is strongly connected, for M ≤ 200."""
def U(n): return 3*(n//2) if n%2==0 else (3*(n//4)+1 if n%4==1 else 3*(n//4)+2)
bad=[]
for M in range(1,201):
    adj={r:{U(r+M*k)%M for k in range(4*M)} for r in range(M)}  # x ≡ r: U x mod M depends on x mod 4M
    def reach(s,g):
        seen={s};st=[s]
        while st:
            u=st.pop()
            for v in g[u]:
                if v not in seen: seen.add(v);st.append(v)
        return seen
    radj={r:set() for r in range(M)}
    for r in adj:
        for v in adj[r]: radj[v].add(r)
    if len(reach(0,adj))<M or len(reach(0,radj))<M: bad.append(M)
print("not strongly connected:",bad)
