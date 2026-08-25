#!/usr/bin/env python3
"""Exact certificate probe for the denominator-1000 Rhin-lite kernel.

This script has no third-party dependencies.  It checks the finite arithmetic reflected in the
three ``RhinLite*.lean`` certificate modules.

For

    P(x) = prod_i Q_i(x)^w_i,

the logarithmic derivative of ``P(x)/x^1000`` has numerator

    S(x) = x * sum_i w_i Q_i'(x) prod_{j != i} Q_j(x)
           - 1000 prod_i Q_i(x).

Although ``P`` has degree 2000, ``S`` has degree only eight. Exact Sturm arithmetic was useful for
discovery, but the Lean proof is smaller: seven sign-changing brackets in ``(2,4)`` plus one in
``(-3,-2)`` give eight distinct roots, which exhaust a degree-eight polynomial. At an interior
nonzero maximum of ``|P(x)|/x^1000``, one of the seven positive roots must occur. Crude exact factor
bounds on every positive bracket prove the target ``(9/40)^1000`` bound numerically.
"""

from __future__ import annotations

import math
from fractions import Fraction


SCALE = 1000
WEIGHTS = (705, 551, 449, 109, 39, 54)
SELECTIONS = (352, 330, 192, 61, 27, 38)

# Ascending coefficients.
FACTORS = (
    (-3, 1),
    (-2, 1),
    (-4, 1),
    (-12, 5),
    (144, -102, 17),
    (144, -108, 19),
)
POSITIVE_CONSTANTS = (3, 2, 4, 12, 144, 144)
POSITIVE_LINEARS = (1, 1, 1, 5, 102, 108)

# Millionth brackets, found numerically but certified below with exact Sturm arithmetic.
ROOT_BRACKETS = (
    (2_115_103, 2_115_104),
    (2_223_243, 2_223_244),
    (2_312_512, 2_312_513),
    (2_520_895, 2_520_896),
    (3_474_818, 3_474_819),
    (3_652_359, 3_652_360),
    (3_780_897, 3_780_898),
)


def trim(p: list[Fraction]) -> list[Fraction]:
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def add(p: list[Fraction], q: list[Fraction]) -> list[Fraction]:
    out = [Fraction(0)] * max(len(p), len(q))
    for i, value in enumerate(p):
        out[i] += value
    for i, value in enumerate(q):
        out[i] += value
    return trim(out)


def scale(p: list[Fraction], c: Fraction) -> list[Fraction]:
    return trim([c * value for value in p])


def mul(p: list[Fraction], q: list[Fraction]) -> list[Fraction]:
    out = [Fraction(0)] * (len(p) + len(q) - 1)
    for i, pi in enumerate(p):
        for j, qj in enumerate(q):
            out[i + j] += pi * qj
    return trim(out)


def product(polynomials: list[list[Fraction]]) -> list[Fraction]:
    out = [Fraction(1)]
    for polynomial in polynomials:
        out = mul(out, polynomial)
    return out


def derivative(p: list[Fraction]) -> list[Fraction]:
    return trim([Fraction(i) * p[i] for i in range(1, len(p))] or [Fraction(0)])


def evaluate(p: list[Fraction], x: Fraction) -> Fraction:
    out = Fraction(0)
    for coefficient in reversed(p):
        out = out * x + coefficient
    return out


def divmod_poly(p: list[Fraction], q: list[Fraction]) -> tuple[list[Fraction], list[Fraction]]:
    p = trim(p.copy())
    q = trim(q.copy())
    if q == [0]:
        raise ZeroDivisionError
    quotient = [Fraction(0)] * max(1, len(p) - len(q) + 1)
    while p != [0] and len(p) >= len(q):
        degree = len(p) - len(q)
        coefficient = p[-1] / q[-1]
        quotient[degree] = coefficient
        for i, qi in enumerate(q):
            p[i + degree] -= coefficient * qi
        trim(p)
    return trim(quotient), trim(p)


def sturm_sequence(p: list[Fraction]) -> list[list[Fraction]]:
    sequence = [trim(p.copy()), derivative(p)]
    while sequence[-1] != [0]:
        _, remainder = divmod_poly(sequence[-2], sequence[-1])
        if remainder == [0]:
            break
        sequence.append(scale(remainder, Fraction(-1)))
    return sequence


def sign(value: Fraction) -> int:
    return (value > 0) - (value < 0)


def variations(sequence: list[list[Fraction]], x: Fraction) -> int:
    signs = [sign(evaluate(polynomial, x)) for polynomial in sequence]
    signs = [value for value in signs if value]
    return sum(a != b for a, b in zip(signs, signs[1:]))


def roots_between(sequence: list[list[Fraction]], a: Fraction, b: Fraction) -> int:
    if any(evaluate(polynomial, a) == 0 or evaluate(polynomial, b) == 0
           for polynomial in sequence[:1]):
        raise AssertionError("Sturm endpoint is a root")
    return variations(sequence, a) - variations(sequence, b)


def logarithmic_derivative_numerator() -> list[Fraction]:
    factors = [list(map(Fraction, factor)) for factor in FACTORS]
    all_factors = product(factors)
    result = scale(all_factors, Fraction(-SCALE))
    for i, (factor, weight) in enumerate(zip(factors, WEIGHTS)):
        others = product([q for j, q in enumerate(factors) if j != i])
        term = mul([Fraction(0), Fraction(1)], mul(derivative(factor), others))
        result = add(result, scale(term, Fraction(weight)))
    return result


def max_abs_on_interval(p: tuple[int, ...], a: Fraction, b: Fraction) -> Fraction:
    candidates = [abs(evaluate(list(map(Fraction, p)), a)),
                  abs(evaluate(list(map(Fraction, p)), b))]
    if len(p) == 3 and p[2]:
        vertex = Fraction(-p[1], 2 * p[2])
        if a <= vertex <= b:
            candidates.append(abs(evaluate(list(map(Fraction, p)), vertex)))
    return max(candidates)


def log_fraction(value: Fraction) -> float:
    return math.log(value.numerator) - math.log(value.denominator)


def main() -> None:
    degree = sum(weight * (len(factor) - 1) for weight, factor in zip(WEIGHTS, FACTORS))
    v2 = WEIGHTS[1] + 2 * WEIGHTS[2] + 2 * WEIGHTS[3] + 3 * WEIGHTS[4] + 4 * WEIGHTS[5]
    v3 = WEIGHTS[0] + WEIGHTS[3] + 2 * WEIGHTS[4] + 2 * WEIGHTS[5]
    assert (degree, v2, v3) == (2 * SCALE, 2 * SCALE, SCALE)
    assert sum(SELECTIONS) == SCALE
    assert all(selection <= weight for selection, weight in zip(SELECTIONS, WEIGHTS))

    block_term = 1
    for weight, selection, constant, linear in zip(
            WEIGHTS, SELECTIONS, POSITIVE_CONSTANTS, POSITIVE_LINEARS):
        block_term *= (math.comb(weight, selection) * linear**selection *
                       constant**(weight - selection))
    assert block_term >= 17**SCALE

    cauchy_left = (29**WEIGHTS[0] * 24**WEIGHTS[1] * 34**WEIGHTS[2] *
                   26**WEIGHTS[3] * 14072**WEIGHTS[4] * 14884**WEIGHTS[5])
    cauchy_right = 252**SCALE * 5**891
    assert cauchy_left <= cauchy_right

    critical = logarithmic_derivative_numerator()
    expected = [
        -5_971_968_000,
        13_269_961_728,
        -11_385_536_256,
        4_171_412_736,
        -28_892_592,
        -519_935_532,
        185_301_612,
        -27_888_891,
        1_615_000,
    ]
    assert critical == list(map(Fraction, expected))
    sturm = sturm_sequence(critical)
    assert len(critical) - 1 == 8
    assert evaluate(critical, Fraction(-3)) * evaluate(critical, Fraction(-2)) < 0
    assert roots_between(sturm, Fraction(-3), Fraction(-2)) == 1
    assert roots_between(sturm, Fraction(2), Fraction(4)) == len(ROOT_BRACKETS)

    target = Fraction(9, 40) ** SCALE
    covered = 0
    print("Rhin-lite exact balances:", (degree, v2, v3))
    print("central lower: block term >= 17^1000; log slack =",
          f"{log_fraction(Fraction(block_term, 17**SCALE)):.6f}")
    print("central upper: rho=14/5 gives <= 18^1000; log slack =",
          f"{log_fraction(Fraction(cauchy_right, cauchy_left)):.6f}")
    print("critical polynomial coefficients (ascending):", expected)
    print("auxiliary sign-changing root bracket: [-3,-2]")
    print("Sturm roots in (2,4):", roots_between(sturm, Fraction(2), Fraction(4)))
    print("\nbracket                         roots  upper^(1/1000)  slack to 9/40")
    for left, right in ROOT_BRACKETS:
        a = Fraction(left, 1_000_000)
        b = Fraction(right, 1_000_000)
        root_count = roots_between(sturm, a, b)
        assert root_count == 1
        covered += root_count
        factor_bounds = [max_abs_on_interval(factor, a, b) for factor in FACTORS]
        ratio = Fraction(1)
        for bound, weight in zip(factor_bounds, WEIGHTS):
            ratio *= bound**weight
        ratio /= a**SCALE
        assert ratio <= target
        root_rate = math.exp(log_fraction(ratio) / SCALE)
        slack = log_fraction(target / ratio)
        print(f"[{float(a):.6f}, {float(b):.6f}]       {root_count:2d}"
              f"       {root_rate:.9f}       {slack:.6f}")
    assert covered == roots_between(sturm, Fraction(2), Fraction(4))
    print("\nAll stationary points are covered; every bracket proves <= (9/40)^1000.")


if __name__ == "__main__":
    main()
