#!/usr/bin/env -S uv run --quiet --with pytest python3
"""Upper edge of the memoryless relaxed game, verified symbolically in (beta, l).

`ArcDelayGame.RelaxedWidthBand` conjectures that on 1/10 <= beta <= 7/57 the memoryless relaxed game
(`ArcTrap.RelaxedStrategy`, arc [beta, 1 - beta]) wins exactly for widths 7/57 <= l <= u(beta),
u(beta) = min(3/4 - 39 beta/8, 15/16 - 105 beta/16).  This tool certifies the exclusion half above
the edge, l > u(beta).

Descent: every strategy P lies in each P_n, where P_0 = [0, 1] and P_{n+1} = P_n ∩ A_0 ∩ A_1 with
    A_d = { a : [a, a + l/3] meets G ∩ (2/3)(P_n + j - d) for some j in {0, 1, 2} },
    G   = [beta, 1 - beta - 2l/3] ∪ [1 + beta, 2 - beta - 2l/3]   (u's sub-window lies in an arc lift).
Intervals are closed (an over-approximation, so emptiness is sound).  Every endpoint is affine in
(beta, l).  On a convex polygon the descent runs with exact signs, splitting the polygon along any
comparison that changes sign inside it, so each leaf polygon carries one combinatorial descent that
is valid on its whole open interior.

    arc_band.py point BETA L [DEPTH]      exact descent at one rational point
    arc_band.py cover [DEPTH]             cover the region above the edge with polygons
    arc_band.py export PATH.lean          write the checked decision-tree certificate as Lean data
    arc_band.py test
"""
from __future__ import annotations

import subprocess
import sys
from fractions import Fraction as F

H, T = F(1, 2), F(2, 3)


class Aff:
    """c + b*beta + w*l"""
    __slots__ = ("c", "b", "w")

    def __init__(self, c, b=0, w=0):
        self.c, self.b, self.w = F(c), F(b), F(w)

    def __add__(self, o):
        o = o if isinstance(o, Aff) else Aff(o)
        return Aff(self.c + o.c, self.b + o.b, self.w + o.w)

    def __sub__(self, o):
        o = o if isinstance(o, Aff) else Aff(o)
        return Aff(self.c - o.c, self.b - o.b, self.w - o.w)

    def scale(self, k):
        return Aff(self.c * k, self.b * k, self.w * k)

    def at(self, p):
        return self.c + self.b * p[0] + self.w * p[1]

    def key(self):
        return (self.c, self.b, self.w)

    def __repr__(self):
        return f"({self.c} + {self.b}b + {self.w}l)"


BETA, L = Aff(0, 1, 0), Aff(0, 0, 1)


class Split(Exception):
    def __init__(self, f):
        self.f = f


class Region:
    """A convex polygon (vertex list), or a single point.  sign(f) is f's sign on the open interior."""

    def __init__(self, verts):
        self.verts = verts

    def sign(self, f):
        vals = [f.at(v) for v in self.verts]
        if all(v == 0 for v in vals):
            return 0
        if all(v >= 0 for v in vals):
            return 1
        if all(v <= 0 for v in vals):
            return -1
        raise Split(f)

    def clip(self, f, s):
        """The part of the polygon where s*f >= 0 (Sutherland-Hodgman against one half-plane)."""
        out, n = [], len(self.verts)
        for i in range(n):
            p, q = self.verts[i], self.verts[(i + 1) % n]
            fp, fq = s * f.at(p), s * f.at(q)
            if fp >= 0:
                out.append(p)
            if (fp > 0 > fq) or (fp < 0 < fq):
                t = fp / (fp - fq)
                out.append((p[0] + t * (q[0] - p[0]), p[1] + t * (q[1] - p[1])))
        return Region(out)

    def area2(self):
        v, n = self.verts, len(self.verts)
        return abs(sum(v[i][0] * v[(i + 1) % n][1] - v[(i + 1) % n][0] * v[i][1] for i in range(n)))


def le(x, y, R):
    return R.sign(y - x) >= 0


def normalize(iv, R):
    """Sort and merge closed intervals; drop empty ones."""
    iv = [(a, b) for a, b in iv if le(a, b, R)]
    # insertion sort with exact comparisons (lists are short)
    out = []
    for a, b in iv:
        i = len(out)
        while i > 0 and not le(out[i - 1][0], a, R):
            i -= 1
        out.insert(i, (a, b))
    merged = []
    for a, b in out:
        if merged and le(a, merged[-1][1], R):
            pa, pb = merged[-1]
            merged[-1] = (pa, b if le(pb, b, R) else pb)
        else:
            merged.append((a, b))
    return merged


def intersect(xs, ys, R):
    out = []
    for a, b in xs:
        for c, d in ys:
            lo = c if le(a, c, R) else a
            hi = b if le(b, d, R) else d
            if le(lo, hi, R):
                out.append((lo, hi))
    return normalize(out, R)


def gate():
    top = Aff(1) - BETA - L.scale(T)
    return [(BETA, top), (BETA + 1, top + 1)]


def step(P, R):
    res = P
    for d in (F(0), H):
        pre = [((p + (j - d)).scale(T), (q + (j - d)).scale(T)) for p, q in P for j in range(3)]
        S = intersect(normalize(pre, R), gate(), R)
        A = normalize([(p - L.scale(F(1, 3)), q) for p, q in S], R)
        res = intersect(res, A, R)
    return res


def descend(R, depth):
    """(steps to empty, None) or (depth, survivors)."""
    P = [(Aff(0), Aff(1))]
    for n in range(1, depth + 1):
        P = step(P, R)
        if not P:
            return n, None
    return depth, P


def point(beta, l, depth=12):
    return descend(Region([(F(beta), F(l))]), depth)


def u_edge(beta):
    return min(F(3, 4) - F(39, 8) * beta, F(15, 16) - F(105, 16) * beta)


def cover(poly, depth=12, max_leaves=20000):
    """Split poly until every leaf's descent is decided.  Returns (empty leaves, live leaves, max depth)."""
    todo, empty, live, worst = [Region(poly)], [], [], 0
    while todo:
        R = todo.pop()
        if R.area2() == 0:
            continue
        try:
            n, surv = descend(R, depth)
        except Split as sp:
            todo += [R.clip(sp.f, 1), R.clip(sp.f, -1)]
            if len(empty) + len(live) + len(todo) > max_leaves:
                raise RuntimeError("too many leaves")
            continue
        (live if surv else empty).append((R, n))
        worst = max(worst, n) if not surv else worst
    return empty, live, worst


B1, B2, B3 = F(1, 10), F(1, 9), F(7, 57)


def regions(lo=F(1, 12)):
    """The two convex pieces of {lo <= beta <= 7/57, u(beta) <= l <= 3/2 - 3 beta}, CCW.  The default lo sits
    left of 1/10 so that points on beta = 1/10 are reached by monotonicity from a leaf interior."""
    top = lambda b: F(3, 2) - 3 * b
    e1 = lambda b: F(3, 4) - F(39, 8) * b
    e2 = lambda b: F(15, 16) - F(105, 16) * b
    return [[(lo, e1(lo)), (B2, e1(B2)), (B2, top(B2)), (lo, top(lo))],
            [(B2, e2(B2)), (B3, e2(B3)), (B3, top(B3)), (B2, top(B2))]]


def root_constraints(lo=F(1, 12)):
    """Strict constraints (form > 0) of the two root pieces, matching `regions(lo)`."""
    top = Aff(F(3, 2), -3, -1)
    return [[BETA - lo, Aff(B2) - BETA, L - Aff(F(3, 4), -F(39, 8)), top],
            [BETA - B2, Aff(B3) - BETA, L - Aff(F(15, 16), -F(105, 16)), top]]


def clean(R):
    """Drop repeated and collinear vertices."""
    v = []
    for p in R.verts:
        if not v or v[-1] != p:
            v.append(p)
    if len(v) > 1 and v[0] == v[-1]:
        v.pop()
    changed = True
    while changed and len(v) > 3:
        changed = False
        for i in range(len(v)):
            a, b, c = v[i - 1], v[i], v[(i + 1) % len(v)]
            if (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0]) == 0:
                v.pop(i)
                changed = True
                break
    return Region(v)


def line_through(p, q):
    """An Aff vanishing on the line pq: (l - p_l)(q_b - p_b) - (beta - p_b)(q_l - p_l)."""
    return Aff(-p[1] * (q[0] - p[0]) + p[0] * (q[1] - p[1]), -(q[1] - p[1]), q[0] - p[0])


def barycentric(v):
    """Affine forms lam_i with lam_i(v_j) = [i == j]."""
    out = []
    for i in range(3):
        a, b = v[(i + 1) % 3], v[(i + 2) % 3]
        f = line_through(a, b)
        out.append(f.scale(1 / f.at(v[i])))
    return out


def positive_multiple(f, g):
    """r > 0 with f = r g coefficientwise, or None."""
    for x, y in ((f.c, g.c), (f.b, g.b), (f.w, g.w)):
        if y != 0:
            r = x / y
            break
    else:
        return None
    if r > 0 and f.key() == g.scale(r).key():
        return r
    return None


def build_tree(R, cons, depth=12):
    """Decision tree: ('node', f, pos, neg) with pos on f > 0, or ('leaf', v1, v2, v3, n)."""
    R = clean(R)
    try:
        n, surv = descend(R, depth)
    except Split as sp:
        f = sp.f
        return ("node", f, build_tree(R.clip(f, 1), cons + [f], depth),
                build_tree(R.clip(f, -1), cons + [f.scale(-1)], depth))
    assert surv is None, "live leaf"
    v = R.verts
    if len(v) == 3:
        return ("leaf", v[0], v[1], v[2], n)
    for k in range(2, len(v) - 1):
        f = line_through(v[0], v[k])
        if f.b != 0:
            return ("node", f, build_tree(R.clip(f, 1), cons + [f], depth),
                    build_tree(R.clip(f, -1), cons + [f.scale(-1)], depth))
    raise RuntimeError("no non-horizontal diagonal")


def check_tree(t, cons, forms):
    """Python twin of the Lean checker.  Returns the number of leaves."""
    if t[0] == "node":
        f = t[1]
        assert f.b != 0
        forms.append(f)
        return check_tree(t[2], cons + [f], forms) + check_tree(t[3], cons + [f.scale(-1)], forms)
    _, v1, v2, v3, n = t
    v = [v1, v2, v3]
    for lam in barycentric(v):
        assert any(positive_multiple(lam, g) for g in cons), "triangle edge not on a constraint"
    m, surv = descend(Region(v), n)
    assert surv is None and m <= n
    return 1


def certificate(lo=F(1, 12)):
    out = []
    for poly, cons in zip(regions(lo), root_constraints(lo)):
        t = build_tree(Region(poly), cons)
        forms = list(cons)
        leaves = check_tree(t, cons, forms)
        assert all(f.b != 0 for f in forms)
        out.append((cons, t, leaves))
    return out


def lean_q(x):
    x = F(x)
    return f"({x.numerator}/{x.denominator} : ℚ)" if x.denominator != 1 else f"({x.numerator} : ℚ)"


def lean_aff(f):
    return f"⟨{lean_q(f.c)}, {lean_q(f.b)}, {lean_q(f.w)}⟩"


def lean_tree(t, ind=4):
    pad = " " * ind
    if t[0] == "leaf":
        _, a, b, c, n = t
        pt = lambda p: f"({lean_q(p[0])}, {lean_q(p[1])})"
        return f"{pad}.leaf {pt(a)} {pt(b)} {pt(c)} {n}"
    return (f"{pad}.node {lean_aff(t[1])}\n{pad}  (\n{lean_tree(t[2], ind + 4)})\n"
            f"{pad}  (\n{lean_tree(t[3], ind + 4)})")


LEAN_HEADER = """/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib

/-!
# Certificate data for `ArcBandCertificate.relaxedAboveUpperEdge`

GENERATED by `experiments/arc_band.py export`; do not edit by hand.  Two decision trees, one per root piece
of `{1/12 < β < 7/57, u(β) < l < 3/2 - 3β}` (split at `β = 1/9`).  `node f pos neg`: `pos` covers `f > 0`,
`neg` covers `f < 0`.  `leaf v₁ v₂ v₃ n`: on the open triangle the memoryless relaxed descent (vertex sign
oracle) is empty within `n` steps, and each barycentric coordinate is a positive multiple of an accumulated
constraint (a root constraint, `f` on a `pos` branch, or `-f` on a `neg` branch).  Every form has a nonzero
`β` coefficient.  Python twin of the checker: `check_tree` in `arc_band.py`.
-/

namespace CollatzMoonshot.Benchmark.ArcBandCertificate

/-- The affine form `c + b β + w l`. -/
structure Aff where
  c : ℚ
  b : ℚ
  w : ℚ
  deriving DecidableEq, Repr

/-- A decision tree over the `(β, l)` plane with triangle leaves. -/
inductive CTree where
  | leaf (v₁ v₂ v₃ : ℚ × ℚ) (depth : ℕ)
  | node (f : Aff) (pos neg : CTree)
  deriving Repr
"""


def export(path):
    cert = certificate()
    body = [LEAN_HEADER]
    for i, (cons, t, leaves) in enumerate(cert):
        body.append(f"/-- Strict root constraints (`form > 0`) of piece {i}. -/\n"
                    f"def root{i} : List Aff :=\n  [{', '.join(lean_aff(f) for f in cons)}]\n")
        body.append(f"/-- Decision tree of piece {i} ({leaves} triangle leaves). -/\n"
                    f"def tree{i} : CTree :=\n{lean_tree(t, 2)}\n")
    body.append("end CollatzMoonshot.Benchmark.ArcBandCertificate\n")
    open(path, "w").write("\n".join(body))
    return [leaves for _, _, leaves in cert]


def main(argv):
    if not argv or argv[0] == "test":
        return subprocess.call([sys.executable, "-m", "pytest", "-q", __file__])
    if argv[0] == "point":
        depth = int(argv[3]) if len(argv) > 3 else 12
        n, surv = point(F(argv[1]), F(argv[2]), depth)
        print("EMPTY at step", n) if surv is None else print("LIVE after", n, [(float(a.at((F(argv[1]), F(argv[2])))), float(b.at((F(argv[1]), F(argv[2]))))) for a, b in surv])
        return 0
    if argv[0] == "cover":
        depth = int(argv[1]) if len(argv) > 1 else 12
        for i, poly in enumerate(regions()):
            empty, live, worst = cover(poly, depth)
            print(f"piece {i}: {len(empty)} empty leaves (max kill depth {worst}), {len(live)} live leaves")
            for R, n in live[:10]:
                print("  live", [(float(x), float(y)) for x, y in R.verts])
        return 0
    if argv[0] == "export":
        print("triangle leaves per piece:", export(argv[1]))
        return 0
    print(__doc__)
    return 2


# ---- persistent suite ----

def test_measure_twice_edge_point():
    """Known answers at beta = 0.12 (u = 0.15): empty within 8 steps just above, live just below."""
    n, surv = point(F(12, 100), F(1501, 10000))
    assert surv is None and n <= 8
    _, surv = point(F(12, 100), F(1495, 10000))
    assert surv is not None



def test_cover_above_edge():
    """Every leaf polygon above the edge empties within 8 steps, and no split line is horizontal."""
    lines, orig = set(), Region.clip

    def clip(self, f, s):
        lines.add(f.key())
        return orig(self, f, s)

    Region.clip = clip
    try:
        for poly, bound in zip(regions(), (7, 8)):
            empty, live, worst = cover(poly)
            assert not live and empty and worst <= bound
    finally:
        Region.clip = orig
    assert lines and all(b != 0 for _, b, _ in lines)


def test_certificate_tree_checks():
    """The exported decision tree passes the Python twin of the Lean checker."""
    cert = certificate()
    assert all(leaves > 0 for _, _, leaves in cert)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
