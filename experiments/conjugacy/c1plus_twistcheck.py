# Exact check of the C1+ reduction: start-class-twisted slice sign sum
#   S = sum_{r in slice(j,a)} (-1)^{T^j r} e(eta r / 3^k)
# equals sum_xi ghat(xi) * sum_r e((3^k xi 2^{-j} - eta) N_r / 3^(a+k)),  N_r = 2^j T^j r - 3^a r,
# with g(y) = (-1)^y e(eta 2^j y / 3^(a+k)) on [0, 3^a).  Also prints sum|ghat| vs log M.
import cmath, math
def tstep(n): return n//2 if n % 2 == 0 else (3*n+1)//2
def e(x): return cmath.exp(2j*math.pi*x)
def check(j, a, k, eta):
    M = 3**a; Mk = 3**(a+k); inv = pow(pow(2, j, M), -1, M)
    sl = []
    for r in range(2**j):
        x = r; c = 0
        for _ in range(j):
            c += x % 2; x = tstep(x)
        if c == a: sl.append((r, x, 2**j*x - 3**a*r))
    S = sum((1 if y % 2 == 0 else -1)*e(eta*r/3**k) for r, y, N in sl)
    g = [(1 if y % 2 == 0 else -1)*e(eta*2**j*y/Mk) for y in range(M)]
    gh = [sum(g[y]*e(-xi*y/M) for y in range(M))/M for xi in range(M)]
    R = sum(gh[xi]*sum(e(((3**k*xi*inv - eta) % Mk)*N/Mk) for r, y, N in sl) for xi in range(M))
    l1 = sum(abs(z) for z in gh)
    print(f"j={j} a={a} k={k} eta={eta}: |S-R|={abs(S-R):.2e}  |S|={abs(S):.3f}  sum|ghat|={l1:.2f}  (2/pi)lnM+1={2/math.pi*math.log(M)+1:.2f}")
for args in [(10,4,1,1),(10,4,2,1),(10,4,2,3),(12,5,2,2),(12,6,1,2),(13,6,3,5)]:
    check(*args)
