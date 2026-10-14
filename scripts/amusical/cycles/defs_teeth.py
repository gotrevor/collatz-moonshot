"""Check the Lean definitions in AmusicalCycleBound.lean literally on known data."""
def U(n): return 3*(n//2) if n%2==0 else (3*(n//4)+1 if n%4==1 else 3*(n//4)+2)
def V(m): return 2*(m//3) if m%3==0 else (4*(m//3)+1 if m%3==1 else 4*(m//3)+3)
def it(f,j,x):
    for _ in range(j): x=f(x)
    return x
# A-star on known cycles
for x,p in [(2,2),(4,5),(44,12)]:
    pts=[it(U,j,x) for j in range(p)]; assert it(U,p,x)==x
    m=min(pts); e=sum(1 if y%2==0 else 2 for y in pts); k=e-p
    ok = 3**p*(3*m-1)**k <= 2**e*(3*m)**k <= 3**p*(3*m+1)**k
    print("A* cycle",x,"p,e,k,m",p,e,k,m,ok)
def M(p,e):
    D=abs(2**e-3**p); return ((e-p)*max(2**e,3**p)+D)//(3*D)
print("M(12,19)=",M(12,19))
def search(X,H,skip={1,2,4,44}):
    bad=[]
    for n in range(1,X+1):
        if n in skip: continue
        dip=any(it(U,j,n)<n or it(V,j,n)<n for j in range(1,H+1))
        noret=all(it(U,j,n)!=n for j in range(1,H+1))
        nomeet=all(it(U,a,n)!=it(V,H,n) for a in range(1,H+1))
        if not (dip or (noret and nomeet)): bad.append(n)
    return bad
print("CycleMinSearch 173 6 violations:", search(173,6))
print("teeth: with 44 not skipped, violations:", search(173,6,skip={1,2,4}))
print("teeth: H=5 skip none of 44 ->", search(173,5,skip={1,2,4}))
