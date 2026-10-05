#!/usr/bin/env -S uv run --quiet --with pytest python3
"""Mahler-type triage of Nashida's open entangled G_2 benchmark (exact arithmetic).

A map of G_2 branches on x mod 4 into x -> (A x + b)/2^e or halts (Nashida, "Expanding cycles are
not enough", Zenodo 10.5281/zenodo.23081447, Section 11; spec format `r:A,b,e;...`).

A map is *pure* when every non-halting residue is either expanding with one common ratio
rho = A/2^e > 1, or a unit step x -> x + b (A = 1, e = 0).  Along a non-halting orbit, let y_n be the
input of the n-th expanding step.  Then y_{n+1} = rho*y_n + c(y_n mod M), M = 2^(2+e), where c sums
the expanding step's b/2^e and the following unit shifts.  With c_min the least c and
y* = c_min/(1-rho), there is a real xi with

    xi*rho^n = y_n - y* + tau_n,   tau_n = sum_{j>=0} (c_{n+j} - c_min) rho^-(j+1),

so frac(xi*rho^n / M) lies in a computable union of windows, one per allowed class s mod M.
Halting at y < 1 is ignored, so the windows are supersets (sound for exclusion).

An infinite orbit is either periodic (xi = 0; then y_n lies in [y* - Delta/(rho-1), y*], a finite
check) or unbounded (xi > 0).  Flatto-Lagarias-Pollington (Acta Arith. 70, 1995): for xi > 0 and
rho = p/q in lowest terms, p > q >= 2, limsup - liminf of {xi*rho^n} is at least 1/p.  Dubickas
(Bull. LMS 2006, Thm 1) gives the same bound for {xi*rho^n + eta}, every real eta, so an arc that
wraps through 0 rotates into [0,1).  If the windows fit in one arc of length < 1/p and no small
periodic orbit exists, the map terminates on every positive integer.

    g2_mahler_triage.py windows SPEC          # one map, JSON
    g2_mahler_triage.py triage TSV [--hits]   # the benchmark list (maps_G2_open.tsv)
    g2_mahler_triage.py test                  # the persistent suite
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from collections import Counter
from fractions import Fraction as Fr
from pathlib import Path

K = 2
MOD = 1 << K


def parse(spec: str) -> dict[int, tuple[int, int, int]]:
    br = {}
    for part in spec.split(";"):
        if part.strip():
            r, v = part.split(":")
            A, b, e = (int(z) for z in v.split(","))
            br[int(r)] = (A, b, e)
    return br


def step(br, x: int):
    t = br.get(x % MOD)
    if t is None:
        return None
    A, b, e = t
    y = (A * x + b) >> e
    return y if y >= 1 else None


def classify(br) -> tuple[str, Fr | None]:
    ratios = {r: Fr(A, 1 << e) for r, (A, b, e) in br.items()}
    exp = {q for q in ratios.values() if q > 1}
    if any(q < 1 for q in ratios.values()):
        return "mixed-contracting", None
    if not exp:
        return "no-expanding", None
    if len(exp) > 1:
        return "multi-ratio", None
    (rho,) = exp
    if rho.denominator == 1:
        return "integer-ratio", rho
    return "pure", rho


def first_returns(br, rho: Fr):
    """Allowed classes s mod M and their constants c_s, or None if a unit cycle exists."""
    e_max = max(e for (A, b, e) in br.values() if Fr(A, 1 << e) == rho)
    M = 1 << (K + e_max)
    out = {}
    for s in range(M):
        r = s % MOD
        t = br.get(r)
        if t is None or Fr(t[0], 1 << t[2]) != rho:
            continue
        A, b, e = t
        img = (A * s + b) >> e  # exact: 2^e | A r + b
        w, c = img % MOD, Fr(b, 1 << e)
        for _ in range(MOD + 1):
            u = br.get(w)
            if u is None or Fr(u[0], 1 << u[2]) == rho:
                break
            c += u[1]  # unit step x -> x + b
            w = (w + u[1]) % MOD
        else:
            return None, M
        if br.get(w) is not None:
            out[s] = c
    return out, M


def arc(intervals):
    """Smallest closed arc of R/Z covering the intervals: (start, length, wraps)."""
    iv = sorted(((a % 1, a % 1 + (b - a)) for a, b in intervals))
    merged = []
    for a, b in iv:
        if merged and a <= merged[-1][1]:
            merged[-1][1] = max(merged[-1][1], b)
        else:
            merged.append([a, b])
    best_gap, start = Fr(-1), None
    for i, (a, b) in enumerate(merged):
        na = merged[(i + 1) % len(merged)][0] + (1 if i + 1 == len(merged) else 0)
        gap = na - b
        if gap > best_gap:
            best_gap, start = gap, na % 1
    length = 1 - best_gap if best_gap > 0 else Fr(1)
    return start, length, start + length > 1


def windows(spec: str) -> dict:
    br = parse(spec)
    kind, rho = classify(br)
    res = {"spec": spec, "kind": kind}
    if kind != "pure":
        return res
    cls, M = first_returns(br, rho)
    res["rho"] = str(rho)
    if cls is None:
        res["kind"] = "unit-cycle"
        return res
    if not cls:
        res["kind"] = "no-allowed-class"
        return res
    cmin = min(cls.values())
    delta = max(cls.values()) - cmin
    ystar = cmin / (1 - rho)
    tail = delta / (rho * (rho - 1))
    wins = {s: ((s - ystar + (c - cmin) / rho) / M, (s - ystar + (c - cmin) / rho + tail) / M)
            for s, c in cls.items()}
    start, length, wraps = arc(wins.values())
    lo, hi = ystar - delta / (rho - 1), ystar
    cycles = []
    for y0 in range(max(1, int(lo) - 1), int(hi) + 2):
        x, seen = y0, set()
        while x is not None and x not in seen and x <= 10 ** 6:
            seen.add(x)
            x = step(br, x)
        if x is not None and x in seen:
            cycles.append(y0)
    p = rho.numerator
    flp = length < Fr(1, p) and not cycles
    res.update({
        "M": M, "classes": {str(s): str(c) for s, c in cls.items()},
        "ystar": str(ystar), "windows": {str(s): [str(a), str(b)] for s, (a, b) in wins.items()},
        "arc_start": str(start), "arc_length": str(length), "wraps": wraps,
        "flp_bound": f"1/{p}", "small_cycle_starts": cycles,
        "verdict": "terminates-by-FLP" if flp else "window-too-wide",
    })
    return res


def triage(path: str, hits: bool) -> dict:
    rows = [ln.split("\t") for ln in Path(path).read_text().splitlines()[1:] if ln.strip()]
    tally, by_rho, verdicts, found = Counter(), Counter(), Counter(), []
    for row in rows:
        w = windows(row[1])
        tally[w["kind"]] += 1
        if w["kind"] == "pure":
            by_rho[w["rho"]] += 1
            verdicts[w["verdict"]] += 1
            if w["verdict"] == "terminates-by-FLP":
                found.append(w if hits else w["spec"])
    return {"maps": len(rows), "kinds": dict(tally), "pure_by_rho": dict(by_rho),
            "pure_verdicts": dict(verdicts), "flp_hits": found}


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("windows").add_argument("spec")
    t = sub.add_parser("triage")
    t.add_argument("tsv")
    t.add_argument("--hits", action="store_true", help="print full window data for each FLP hit")
    sub.add_parser("test")
    a = ap.parse_args(argv)
    if a.cmd == "test":
        return subprocess.call([sys.executable, "-m", "pytest", "-q",
                                str(Path(__file__).with_name("test_g2_mahler_triage.py"))])
    out = windows(a.spec) if a.cmd == "windows" else triage(a.tsv, a.hits)
    print(json.dumps(out, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
