"""Numerical check of every statement in Challenge.lean, with the definitions transcribed exactly.

Run: python3 check/statements.py
"""
from fractions import Fraction as F
from math import gcd
import random


def sawtooth(x):
    fr = x - (x.numerator // x.denominator)
    return F(0) if fr == 0 else fr - F(1, 2)


def dedekind_sum(h, k):
    return sum((sawtooth(F(r, k)) * sawtooth(F(h * r, k)) for r in range(k)), F(0))


def rem(k, h, j):
    a, b = k, h
    for _ in range(j):
        a, b = b, (a % b if b != 0 else a)  # Lean: n % 0 = n
    return a


def den(k, h, j):
    if j == 0:
        return 0
    q0, q1 = 0, 1
    for i in range(j - 1):
        r_i, r_i1 = rem(k, h, i), rem(k, h, i + 1)
        a = r_i // r_i1 if r_i1 != 0 else 0  # Lean: n / 0 = 0
        q0, q1 = q1, a * q1 + q0
    return q1


def steps(k, h):
    j = 0
    while not (rem(k, h, j) <= 1 or j == k + 1):
        j += 1
    return j


def log2(n):
    return n.bit_length() - 1 if n > 0 else 0


def is_prime(n):
    return n > 1 and all(n % d for d in range(2, int(n ** 0.5) + 1))


def small_ratio_sum(p, h):
    s = F(0)
    for u in range(1, p + 1):
        for v in range(1, p + 1):
            if gcd(u, v) == 1 and 2 * u * v < p:
                a = 1 if (h * v - u) % p == 0 else 0
                b = 1 if (h * v + u) % p == 0 else 0
                s += F(a - b, u * v)
    return s


def subgroup_small_ratio(p, H):
    s = F(0)
    for u in range(1, p + 1):
        for v in range(1, p + 1):
            if gcd(u, v) == 1 and 2 * u * v < p:
                x = u * pow(v, -1, p) % p
                s += F((1 if x in H else 0) - (1 if (-x) % p in H else 0), u * v)
    return s


checks = 0
# reciprocity
for h in range(1, 40):
    for k in range(1, 40):
        if gcd(h, k) == 1:
            assert dedekind_sum(h, k) + dedekind_sum(k, h) == (F(h, k) + F(k, h) + F(1, h * k)) / 12 - F(1, 4)
            checks += 1
# Euclid statements and Lemma 5.12, Lemma 5.13
for k in range(2, 70):
    for h in range(1, k):
        if gcd(k, h) != 1:
            continue
        n = steps(k, h)
        assert rem(k, h, n) == 1 and all(rem(k, h, j) >= 2 for j in range(n))
        assert all(rem(k, h, j) < rem(k, h, i) for i in range(n + 1) for j in range(i + 1, n + 1))
        assert all(rem(k, h, j) * den(k, h, j + 1) + rem(k, h, j + 1) * den(k, h, j) == k for j in range(n + 1))
        assert all((h * den(k, h, j) - (-1) ** (j + 1) * rem(k, h, j)) % k == 0 for j in range(n + 4))
        assert n <= 2 * log2(k) + 1
        main = sum(F((-1) ** (i + 1) * k, rem(k, h, i) * den(k, h, i)) for i in range(1, n + 1))
        assert abs(12 * dedekind_sum(h, k) - main) <= 4 * n
        for u in range(1, k):
            for v in range(1, k):
                if gcd(u, v) == 1 and 2 * u * v < k:
                    for eps in (1, -1):
                        if (h * v - eps * u) % k == 0:
                            assert any(rem(k, h, j) == u and den(k, h, j) == v and eps == (-1) ** (j + 1)
                                       for j in range(1, n + 1))
        checks += 1
# prime statements
primes = [p for p in range(2, 120) if is_prime(p)]
for p in primes:
    for h in range(1, p):
        n = steps(p, h)
        assert all(gcd(rem(p, h, j), den(p, h, j)) == 1 for j in range(1, n + 1))
        d = abs(12 * dedekind_sum(h, p) - p * small_ratio_sum(p, h))
        assert d <= 6 * n and d <= 12 * log2(p) + 6
        checks += 1
    rng = random.Random(p)
    sets = [set(), {0}, set(range(p))]
    for m in range(1, p):  # subgroups
        if (p - 1) % m == 0:
            g = next(g for g in range(1, p) if all(pow(g, (p - 1) // q, p) != 1 for q in range(2, p) if (p - 1) % q == 0 and is_prime(q)))
            sets.append({pow(g, m * i, p) for i in range((p - 1) // m)})
    for _ in range(3):
        sets.append({x for x in range(p) if rng.random() < 0.3})
    for H in sets:
        S = subgroup_small_ratio(p, H)
        assert sum((small_ratio_sum(p, x) for x in H), F(0)) == S
        assert abs(12 * sum((dedekind_sum(x, p) for x in H), F(0)) - p * S) <= len(H) * (12 * log2(p) + 6)
        checks += 1
print("all statements hold;", checks, "cases checked")
