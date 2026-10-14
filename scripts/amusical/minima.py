import sys, math
def U(n):
    if n%2==0: return 3*(n//2)
    if n%4==1: return 3*(n//4)+1
    return 3*(n//4)+2
def V(m):
    r=m%3
    if r==0: return 2*(m//3)
    if r==1: return 4*(m//3)+1
    return 4*(m//3)+3
def status(n, esc=2**120, cap=20000):
    # 'min' if both directions escape above n*esc without dipping below n; 'not' if dips; 'cyc' if returns
    for f in (U,V):
        x=n
        for _ in range(cap):
            x=f(x)
            if x==n: return 'cyc'
            if x<n: return 'not'
            if x>n*esc: break
        else: return 'unk'
    return 'min'
N=None
if __name__=="__main__":
  N=int(sys.argv[1])
  cnt={'min':0,'not':0,'cyc':0,'unk':0}
  marks=[10**k for k in range(2,10)]
  for n in range(1,N+1):
      cnt[status(n)]+=1
      if n in marks: print(n, cnt, 'min density %.4f'%(cnt['min']/n), flush=True)
  print(N,cnt,'min density %.4f'%(cnt['min']/N))
