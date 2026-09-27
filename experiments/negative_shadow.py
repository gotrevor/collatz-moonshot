#!/usr/bin/env -S uv run --quiet python3
"""Exact negative rational reference potentials.  See the accompanying research note.

This is a falsification instrument, not a convergence test.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
from itertools import product
from math import gcd
from pathlib import Path
import json
import subprocess
import sys


def step(n: int) -> int:
    return (3*n+1)//2 if n % 2 else n//2


def valuation(n: int) -> int:
    if n <= 0:
        raise ValueError("positive argument required")
    return (n & -n).bit_length()-1


def numerator(word: tuple[int, ...]) -> int:
    value, power_two = 0, 1
    for bit in word:
        value = 3*value + power_two if bit else value
        power_two *= 2
    return value


def references(depth: int) -> list[tuple[int, int]]:
    """Every negative periodic rational represented by a word of length <= depth."""
    result = set()
    for length in range(1, depth+1):
        for word in product((0, 1), repeat=length):
            den = 3**sum(word) - 2**length
            if den <= 0:
                continue
            a = numerator(word)
            common = gcd(a, den)
            result.add((a//common, den//common))
    return sorted(result)


def score(n: int, a: int, b: int) -> Fraction:
    """For primitive -a/b, q=b*n+a; score=q*2^v2(q)/a^2."""
    if n < 1 or a < b or b <= 0 or b % 2 == 0 or gcd(a,b) != 1:
        raise ValueError("need n>=1 and primitive -a/b<=-1 with odd denominator")
    q = b*n+a
    return Fraction(q << valuation(q), a*a)


def best(n: int, refs: list[tuple[int,int]]) -> tuple[Fraction, tuple[int,int]]:
    return max((score(n,a,b), (a,b)) for a,b in refs)


def envelope_witness(n: int, exponent: int) -> tuple[int, int]:
    """Primitive reference approaching the all-rational supremum (n+1)^2."""
    if n < 1 or exponent < 1:
        raise ValueError("positive n and exponent required")
    q = 2**exponent
    b = q//(n+1)
    if b % 2 == 0:
        b -= 1
    if b < 1:
        raise ValueError("exponent too small")
    return q-b*n, b


def cycle_witness(repeats: int) -> tuple[int, int]:
    """Inverse image of -1 along (odd, even)^repeats; denominator is 3^repeats."""
    if repeats < 0:
        raise ValueError("nonnegative repeats required")
    return 2*4**repeats-3**repeats, 3**repeats


def scan(depth: int, limit: int) -> dict:
    refs = references(depth)
    cache = {}
    def value(n):
        if n not in cache:
            cache[n] = best(n, refs)
        return cache[n]
    failures = []
    for n in range(3, limit+1):
        before, rb = value(n)
        after, ra = value(step(n))
        if after > before:
            failures.append({"n":n,"next":step(n),"before":str(before),
                             "after":str(after),"ref_before":rb,"ref_after":ra})
    return {"depth":depth,"limit":limit,"references":len(refs),
            "increases":len(failures),"first_increases":failures[:10]}


def main():
    if sys.argv[1:] == ["test"]:
        raise SystemExit(subprocess.call(["uv","run","--quiet","--with","pytest",
            "python3","-m","pytest",str(Path(__file__).with_name("test_negative_shadow.py")),"-q"]))
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    p=sub.add_parser("score")
    p.add_argument("n",type=int); p.add_argument("a",type=int); p.add_argument("b",type=int)
    p=sub.add_parser("scan")
    p.add_argument("--depth",type=int,default=10); p.add_argument("--limit",type=int,default=1000)
    p=sub.add_parser("envelope")
    p.add_argument("n",type=int); p.add_argument("exponent",type=int)
    p=sub.add_parser("cycle-witness")
    p.add_argument("repeats",type=int)
    args=parser.parse_args()
    if args.command == "score":
        print(json.dumps({"score":str(score(args.n,args.a,args.b)),
                          "upper":(args.n+1)**2}))
    elif args.command == "scan":
        print(json.dumps(scan(args.depth,args.limit),indent=2))
    elif args.command == "envelope":
        a,b=envelope_witness(args.n,args.exponent)
        print(json.dumps({"a":a,"b":b,"score":str(score(args.n,a,b)),
                          "upper":(args.n+1)**2}))
    else:
        a,b=cycle_witness(args.repeats)
        print(json.dumps({"a":a,"b":b,"weighted_score":str(b*score(1,a,b))}))


if __name__ == "__main__":
    main()
