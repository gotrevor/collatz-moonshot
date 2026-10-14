#!/usr/bin/env python3
"""Independent pure-Python re-implementations, compared with the C programs on sample ranges.

C1: cyclemin's classification (dip / survivor / cycle) on a range, with Python ints, plus a
    *naive* check for every survivor: U^j n != n for all 1 <= j <= 2H (no meet-in-the-middle).
C2: rsearch's classification (dip / runcap / cycle) on a range.
"""
import subprocess, re, sys

def U(x):
    if x % 2 == 0: return 3 * x // 2
    return (3 * x + 1) // 4 if x % 4 == 1 else (3 * x - 1) // 4
def V(x):
    r = x % 3
    return 2 * x // 3 if r == 0 else ((4 * x - 1) // 3 if r == 1 else (4 * x + 1) // 3)

def c_counts(prog, args):
    out = subprocess.run([prog] + [str(a) for a in args], capture_output=True, text=True, check=True)
    return out.stderr.strip(), [l for l in out.stdout.split('\n') if l]

def C1(lo, hi, H):
    dips = surv = found = 0; survivors = []
    for n in range(lo, hi):
        if n in (1, 2, 4, 44): continue
        f = g = n; st = None
        for j in range(1, H + 1):
            f = U(f)
            if f < n: st = 'dip'; break
            if f == n: st = 'cyc'; break
            g = V(g)
            if g < n: st = 'dip'; break
            if g == n: st = 'cyc'; break
        if st == 'dip': dips += 1
        elif st == 'cyc': found += 1
        else: surv += 1; survivors.append(n)
    # naive: survivors must have no return within 2H forward steps
    naive_ret = 0
    for n in survivors:
        x = n
        for j in range(1, 2 * H + 1):
            x = U(x)
            if x == n: naive_ret += 1; break
    err, lines = c_counts('./cyclemin', [lo, hi, H, 1])
    m = re.search(r'dips=(\d+) survivors=(\d+) found=(\d+)', err)
    c = tuple(map(int, m.groups()))
    ok = c == (dips, surv, found) and naive_ret == 0 and not lines
    print(f"C1 [{lo},{hi}) H={H}: python (dips,surv,found)={(dips, surv, found)} C={c}; naive returns among survivors={naive_ret}: {'PASS' if ok else 'FAIL'}")
    return ok

def C2(lo, hi, R):
    dips = cap = found = 0
    for n in range(lo, hi):
        if n in (1, 2, 4, 44): continue
        f = g = n; runs = 1; st = None
        while True:
            fo = f % 2
            f = U(f)
            if f == n: st = 'cyc'; break
            if f < n: st = 'dip'; break
            if f % 2 == 0 and fo == 1:
                runs += 1
                if runs > R: st = 'cap'; break
            g = V(g)
            if g < n: st = 'dip'; break
            if g == n: st = 'cyc'; break
        dips += st == 'dip'; cap += st == 'cap'; found += st == 'cyc'
    err, lines = c_counts('./rsearch', [lo, hi, R, 1])
    m = re.search(r'dips=(\d+) runcap=(\d+) found=(\d+)', err)
    c = tuple(map(int, m.groups()))
    ok = c == (dips, cap, found) and not lines
    print(f"C2 [{lo},{hi}) R={R}: python (dips,runcap,found)={(dips, cap, found)} C={c}: {'PASS' if ok else 'FAIL'}")
    return ok

if __name__ == '__main__':
    ok = C1(47000000, 47000400, 7800)
    ok &= C1(167195000, 167195300, 15933)
    ok &= C1(1, 20000, 200)
    ok &= C2(1, 300000, 8)
    ok &= C2(19999000000, 19999100000, 32)
    print('ALL PASS' if ok else 'SOME FAIL')
