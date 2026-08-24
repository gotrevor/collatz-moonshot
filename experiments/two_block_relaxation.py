"""Two-block crux `b+d <= 5`: REFUTATION of the "elementary A/B route" (lap 2026-08-25-1500).

Context (see FRONT-A-PARADOXICAL.md, PENDING_WORK.md): the interior two-block exclusion
`le_two_blocks_not_acyclicParadoxical` is machine-checked modulo the single inequality
`b + d <= 5` inside `near_critical_containment`.  A prior lap ("MAJOR LEAD 2026-08-25-1230")
conjectured this closes ELEMENTARILY: it verified over ACTUAL INTEGER POWERS that

    ¬A ∧ ¬B ∧ subcritical ∧ U₁>0 ∧ b,d≥1  ⟹  b+d ≤ 5

    A : 3^(b+d) + 2^c·3^d < 2^m           (m = b+c+d+e)
    B : (2^m − 3^(b+d))·(2^d − 1) ≥ 3^b·(3^d − 2^d)
    U₁: 3^d < 2^c·(3^d − 2^d)             (i.e. U₁ = 3^d(2^c−1) − 2^(c+d) > 0)

and hoped `nlinarith`/`omega` over the exponent atoms would prove it (= the GO upgrade,
no Baker input).

This script REFUTES elementary provability.  A single `nlinarith` certificate is a
Positivstellensatz combination valid for ALL REAL values of the atoms
{2^b, 2^d, 2^c, 3^b, 3^d, 2^m} satisfying the hypotheses (plus any provable polynomial
couplings).  We show the REAL RELAXATION is FEASIBLE at arbitrarily large g = b+d — so no
such certificate can exist; the boundedness genuinely needs the actual-power / effective-
irrationality-of-log₂3 (Baker) structure.

Two checks:
  (1) STRESS (actual integer powers): the implication is TRUE, exactly 4 (b,d) pairs, all
      b+d ≤ 5, verified to g ≤ 200.  (So it is a true theorem — just not elementary.)
  (2) RELAXATION (reals, all polynomial couplings auto-satisfied by using real exponents):
      FEASIBLE at g ≈ 41 (and every large g).  A fully-checked witness is printed.

Conclusion: `b+d ≤ 5` is Baker-grade.  Matches Aristotle's independent linear-forms-in-logs
diagnosis and the earlier `dbig.py` "real bound is infinite" finding.  DO NOT re-attempt an
elementary nlinarith/omega bound on `b+d ≤ 5`.
"""
from fractions import Fraction as F


def stress(GMAX=200):
    """Actual integer powers: ¬A∧¬B∧subcrit∧U₁ ⟹ b+d≤5.  Returns the (b,d) solution set."""
    sols = set()
    over = []
    for g in range(2, GMAX + 1):
        P = 3 ** g
        m0 = P.bit_length()
        while 2 ** m0 <= P:
            m0 += 1
        for m in range(m0, m0 + 8):          # ¬B forces m near-critical; scan a few
            tm = 2 ** m
            D = tm - P
            for d in range(1, g):
                b = g - d
                if not (D * (2 ** d - 1) < 3 ** b * (3 ** d - 2 ** d)):   # ¬B
                    continue
                cmax = m - g                  # c+e = m-g, e>=0
                if cmax < 0:
                    continue
                for c in range(0, cmax + 1):
                    if not (tm <= P + 2 ** c * 3 ** d):                   # ¬A
                        continue
                    if not (3 ** d * (2 ** c - 1) - 2 ** (c + d) > 0):    # U₁>0
                        continue
                    sols.add((b, d))
                    if b + d >= 6:
                        over.append((b, c, d, m - g - c, m))
    return sols, over


def relaxation_witness(bb, dd):
    """Real relaxation at integer exponents (couplings exact).  Returns a fully-checked
    witness (C, V) or None.  Everything is a positive rational; no floating point."""
    A, B, R, S = 2 ** bb, 2 ** dd, 3 ** bb, 3 ** dd
    if A * B < 64 or R * S < 729:            # encodes g = b+d >= 6
        return None
    # C-interval from U₁ (lower) and (I)/(F1') (upper); V-interval from subcrit/lever/¬A/¬B.
    Clo = F(S, S - B)
    Cups = [F(R * (S - 1), A * (B - 1))]
    if A * B > S:
        Cups.append(F(R * S, A * B - S))
    Cup = min(Cups)
    if not (Clo < Cup):
        return None
    C = (Clo + Cup) / 2
    Vlo = max(F(R * S) + 1, F(A * B) * C)
    Vup = min(F(R * S) + C * S, F(R * S) + F(R * (S - B), B - 1))
    if not (Vlo <= Vup):
        return None
    V = (Vlo + Vup) / 2
    checks = {
        "subcrit (R*S < V)": R * S < V,
        "¬A (V ≤ R*S + C*S)": V <= R * S + C * S,
        "¬B ((V−R*S)(B−1) < R(S−B))": (V - R * S) * (B - 1) < R * (S - B),
        "U₁ (S < C(S−B))": S < C * (S - B),
        "lever (A*B*C ≤ V)": A * B * C <= V,
        "coupling S³≤B⁵": B ** 5 >= S ** 3,
        "coupling R³≤A⁵": A ** 5 >= R ** 3,
        "size A*B≥64": A * B >= 64,
        "size R*S≥729": R * S >= 729,
    }
    return C, V, checks


if __name__ == "__main__":
    sols, over = stress(200)
    print("STRESS (integer powers, g≤200):")
    print("  (b,d) solution set:", sorted(sols))
    print("  max b+d:", max(b + d for b, d in sols))
    print("  solutions with b+d≥6:", over)      # EMPTY -> implication true for integers
    print()
    print("RELAXATION (reals): fully-checked witness at g=41 (b=18, d=23):")
    w = relaxation_witness(18, 23)
    C, V, checks = w
    print(f"  C ≈ {float(C):.3e}   V ≈ {float(V):.3e}")
    for k, v in checks.items():
        print(f"    {k}: {v}")
    print("  ALL constraints satisfied:", all(checks.values()))
    print()
    print("Feasible g values in relaxation (b=d) up to 60:",
          [2 * k for k in range(3, 31) if relaxation_witness(k, k)])
    print()
    print("CONCLUSION: real relaxation feasible at unbounded g ⇒ no nlinarith certificate ⇒")
    print("`b+d ≤ 5` is Baker-grade (effective irrationality of log₂3), NOT elementary.")
