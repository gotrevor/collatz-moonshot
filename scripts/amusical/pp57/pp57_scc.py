import sys, time
from math import gcd
from pp57 import PP, DM
sys.setrecursionlimit(10000)

def lcm(a,b): return a*b//gcd(a,b)

def adjacency(f, M):
    L = lcm(M, DM)
    adj = [set() for _ in range(M)]
    for t in range(L):
        r, a, s, b = f.pieces[f.tab[t % DM]]
        y0 = s + b * ((t - r) // a)
        step = b * (L // a)
        g = gcd(step, M)
        src = adj[t % M]
        y0 %= g
        for k in range(M // g):
            src.add(y0 + k * g)
    return adj

def scc_count(adj):
    n = len(adj); index = [None]*n; low=[0]*n; onst=[False]*n; st=[]; idx=0; comps=0
    adjl = [list(e) for e in adj]
    for v0 in range(n):
        if index[v0] is not None: continue
        work=[(v0,0)]; index[v0]=low[v0]=idx; idx+=1; st.append(v0); onst[v0]=True
        while work:
            v,i = work[-1]
            if i < len(adjl[v]):
                work[-1]=(v,i+1); w=adjl[v][i]
                if index[w] is None:
                    index[w]=low[w]=idx; idx+=1; st.append(w); onst[w]=True; work.append((w,0))
                elif onst[w]: low[v]=min(low[v],index[w])
            else:
                work.pop()
                if work:
                    u=work[-1][0]; low[u]=min(low[u],low[v])
                if low[v]==index[v]:
                    comps+=1
                    while True:
                        w=st.pop(); onst[w]=False
                        if w==v: break
    return comps

if __name__ == "__main__":
    seed = int(sys.argv[1]); mods = [int(m) for m in sys.argv[2].split(",")]
    f = PP(seed)
    for M in mods:
        t = time.time()
        c = scc_count(adjacency(f, M))
        print(f"seed {seed} M={M}: {c} SCC  ({time.time()-t:.1f}s)", flush=True)
