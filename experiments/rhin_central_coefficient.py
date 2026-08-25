#!/usr/bin/env python3
"""Exact central-coefficient probe for Rhin's six-factor two-log polynomial.

Rhin's auxiliary polynomial (constant prefactor omitted) is

    H_n(x) = prod_i Q_i(x)^floor(b_i*n),

where the decimal b_i are treated as the exact six-decimal rationals printed in
Rhin 1987.  This script incrementally builds H_n in Z[x] and inspects B_n =
[x^n]H_n using only Python integers.

Two important structural observations are exact, not experimental.

* Every Q_i has strictly alternating nonzero coefficients.  Thus Q_i(-x), up
  to its leading sign, has strictly positive coefficients, so every coefficient
  of H_n is nonzero whenever its index is at most deg H_n.
* The six printed weights satisfy exact degree/2-adic/3-adic balance equations.
  On replacing x by 12x, their contents contribute respectively 2n and n
  powers of 2 and 3 (before floor losses).  Rhin's prefactor 12^7 absorbs all
  floor losses.  Hence 12^n divides every coefficient of 12^7 H_n(12x), which
  is the arithmetic condition needed to clear endpoint powers in the integrals
  over [2,3] and [3,4].

The computation below checks the transcription/floor conventions and measures
the exponential growth that a future certificate must bound.
"""

from __future__ import annotations

import argparse
import math
import time
from dataclasses import dataclass


SCALE = 1_000_000


@dataclass(frozen=True)
class Factor:
    name: str
    coeffs: tuple[int, ...]  # ascending powers of x
    weight: int              # exact numerator over SCALE


FACTORS = (
    Factor("x-3", (-3, 1), 704_324),
    Factor("x-2", (-2, 1), 552_418),
    Factor("x-4", (-4, 1), 447_582),
    Factor("5x-12", (-12, 5), 109_072),
    Factor("17x^2-102x+144", (144, -102, 17), 38_934),
    Factor("19x^2-108x+144", (144, -108, 19), 54_368),
)


def mul_small(p: list[int], q: tuple[int, ...]) -> list[int]:
    """Multiply an integer polynomial by a degree-at-most-two polynomial."""
    out = [0] * (len(p) + len(q) - 1)
    for j, qj in enumerate(q):
        if qj:
            for i, pi in enumerate(p):
                out[i + j] += pi * qj
    return out


def log_abs_int(x: int) -> float:
    """Natural log of a nonzero arbitrarily large integer without float overflow."""
    x = abs(x)
    bits = x.bit_length()
    shift = max(0, bits - 53)
    return math.log(x >> shift) + shift * math.log(2.0)


def alternating_dense(p: list[int]) -> bool:
    """All coefficients are nonzero and alternate according to total degree."""
    degree = len(p) - 1
    return all(c != 0 and (c > 0) == ((degree - j) % 2 == 0)
               for j, c in enumerate(p))


def padic_valuation(x: int, prime: int) -> int:
    x = abs(x)
    if x == 0:
        raise ValueError("valuation of zero")
    result = 0
    while x % prime == 0:
        x //= prime
        result += 1
    return result


def scaled_content_valuation(factor: Factor, prime: int) -> int:
    """p-adic valuation of the content of Q(12x)."""
    return min(padic_valuation(coefficient * 12**degree, prime)
               for degree, coefficient in enumerate(factor.coeffs))


def expected_degree(n: int, factors: tuple[Factor, ...]) -> int:
    return sum((factor.weight * n // SCALE) * (len(factor.coeffs) - 1)
               for factor in factors)


def run(max_n: int, every: int, factors: tuple[Factor, ...]) -> None:
    degree_balance = sum(f.weight * (len(f.coeffs) - 1) for f in factors)
    two_balance = sum(f.weight * scaled_content_valuation(f, 2) for f in factors)
    three_balance = sum(f.weight * scaled_content_valuation(f, 3) for f in factors)
    if not all(alternating_dense(list(f.coeffs)) for f in factors):
        raise AssertionError("a transcribed Rhin factor is not alternating-dense")

    polynomial = [1]
    exponents = [0] * len(factors)
    zero_indices: list[int] = []
    first_central = None
    min_degree_gap = 0
    started = time.monotonic()

    print("n degree degree-n sign log|B_n|/n digits")
    for n in range(1, max_n + 1):
        for i, factor in enumerate(factors):
            exponent = factor.weight * n // SCALE
            delta = exponent - exponents[i]
            if delta not in (0, 1):
                raise AssertionError((n, factor.name, exponents[i], exponent))
            if delta:
                polynomial = mul_small(polynomial, factor.coeffs)
                exponents[i] = exponent

        degree = len(polynomial) - 1
        if degree != expected_degree(n, factors):
            raise AssertionError((n, degree, expected_degree(n, factors)))
        if not alternating_dense(polynomial):
            raise AssertionError(f"alternating-density failed at n={n}")

        min_degree_gap = min(min_degree_gap, degree - n)
        central = polynomial[n] if n <= degree else 0
        if central == 0:
            zero_indices.append(n)
        elif first_central is None:
            first_central = n

        if n == 1 or n == max_n or n % every == 0:
            if central:
                rate = log_abs_int(central) / n
                digits = int(log_abs_int(central) / math.log(10.0)) + 1
                sign = "+" if central > 0 else "-"
                print(f"{n:5d} {degree:6d} {degree-n:8d} {sign:>4s} "
                      f"{rate:12.9f} {digits:7d}")
            else:
                print(f"{n:5d} {degree:6d} {degree-n:8d} zero")

    elapsed = time.monotonic() - started
    print()
    print("factor weights:", dict((f.name, f.weight) for f in factors))
    print("factor exponents:", dict(zip((f.name for f in factors), exponents)))
    print("balance (degree, v2(Q(12x)), v3(Q(12x))):",
          (degree_balance, two_balance, three_balance),
          "target", (2 * SCALE, 2 * SCALE, SCALE))
    if (degree_balance, two_balance, three_balance) == (2 * SCALE, 2 * SCALE, SCALE):
        print("arithmetic balance: exact; 12^7 covers floor losses")
    else:
        print("arithmetic balance: FAILED (candidate is not a valid Rhin/Wu polynomial)")
    print("first n with a central coefficient:", first_central)
    print("central zeros:", zero_indices if zero_indices else "none")
    print("minimum degree-n over the scanned range:", min_degree_gap)
    print(f"elapsed: {elapsed:.3f}s")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-n", type=int, default=1000)
    parser.add_argument("--every", type=int, default=100)
    parser.add_argument(
        "--weights",
        help=("six comma-separated integer numerators over 1,000,000; weighted "
              "degrees must sum to 2,000,000"),
    )
    args = parser.parse_args()
    if args.max_n < 1 or args.every < 1:
        parser.error("--max-n and --every must be positive")
    factors = FACTORS
    if args.weights:
        try:
            weights = tuple(int(x) for x in args.weights.split(","))
        except ValueError as error:
            parser.error(f"invalid --weights: {error}")
        if len(weights) != len(FACTORS):
            parser.error("--weights requires exactly six integers")
        factors = tuple(Factor(f.name, f.coeffs, weight)
                        for f, weight in zip(FACTORS, weights))
    run(args.max_n, args.every, factors)


if __name__ == "__main__":
    main()
