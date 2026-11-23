"""Finite algebra checks for the two research packets, using integer certificates."""

from collections import Counter
from fractions import Fraction
from itertools import combinations
from math import gcd, isqrt, prod
import json


def trial_prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def factor(n):
    primes = []
    d = 2
    while d * d <= n:
        while n % d == 0:
            primes.append(d)
            n //= d
        d += 1
    if n > 1:
        primes.append(n)
    return primes


def finite_transfer():
    # Unit weights make every equality exact over Q. The lemma is linear in
    # arbitrary initial weights, and its asymptotic estimate uses log weights.
    x = 10_000
    band = {7, 11, 13}
    profile = {}
    twins = set()
    donors = set()
    for p in range(x + 1, 2 * x + 1):
        if not trial_prime(p):
            continue
        fac = factor(p + 2)
        unique = set(fac)
        mu = (-1) ** len(fac) if len(unique) == len(fac) else 0
        profile[p] = (len(unique & band), mu)
        if len(fac) == 1:
            twins.add(p)
        elif profile[p] == (0, -1) and len(unique) > 2:
            donors.add(p)
    assert donors and twins
    transfer = Fraction(len(twins), len(donors))
    initial = Counter(profile.values())
    after = Counter()
    for p, cell in profile.items():
        weight = 0 if p in twins else 1
        if p in donors:
            weight += transfer
        after[cell] += weight
    assert all(after[cell] == count for cell, count in initial.items())
    return dict(twins=len(twins), donors=len(donors), cells=len(initial),
                extra_donor_weight=str(transfer))


def proth_certificate(prime_candidate, exponent):
    k = (prime_candidate - 1) >> exponent
    assert k % 2 and k < (1 << exponent)
    return next((a for a in (3, 5, 7, 11, 13, 17, 19)
                 if pow(a, (prime_candidate - 1) // 2, prime_candidate)
                 == prime_candidate - 1), None)


def sharp_witness():
    e = 2203
    assert trial_prime(e)
    owner = (1 << e) - 1
    ll = 4
    for _ in range(e - 2):
        ll = (ll * ll - 2) % owner
    assert ll == 0  # Lucas–Lehmer proves the owner prime.
    small = 17
    m_primes = (257, 1009, 65537)
    assert all(trial_prime(t) for t in (small, *m_primes))
    m = prod(m_primes)
    # q near 2^706. Proth's test supplies an exact primality certificate.
    multiplier = (1 << 106) + 1
    while True:
        q = (multiplier << 600) + 1
        k = owner * q * small * m
        if gcd(k + 2, 2 * 3 * 5 * 7) == 1:
            base = proth_certificate(q, 600)
            if base is not None:
                break
        multiplier += 2
    x = (4 * k + 2) // 3
    # For eta=1/1000, lower and upper q exponents are 479/2000
    # and 959/4000. All power comparisons below are exact integers.
    assert 2 * (k + 2) > x >= k + 2
    assert x ** 479 < q ** 2000 and q ** 4000 < x ** 959
    assert small ** 1000 > x and small ** 500 <= x
    assert all(t ** 500 > x and t ** 100 <= x for t in m_primes)
    assert m ** 20 <= x
    assert 7 ** 1000 <= x < 11 ** 1000 and gcd(k + 2, 210) == 1
    factors = (q, small, *m_primes)
    assert all(t ** 25 <= x ** 6 for t in factors)
    assert owner ** 25 > x ** 6
    signed = 0
    terms = 0
    for j in range(len(factors) + 1):
        for subset in combinations(factors, j):
            value = prod(subset)
            if value ** 25 > x ** 6 and (owner * value) ** 100 > x ** 49:
                signed += (-1) ** j
                terms += 1
    assert signed == 1
    return dict(x_bits=x.bit_length(), owner_mersenne_exponent=e,
                tested_proth_multiplier=multiplier, proth_exponent=600,
                proth_witness=base, eligible_divisor_terms=terms,
                coefficient_of_log_owner=signed, output_rough_exponent="1/1000")


if __name__ == "__main__":
    print(json.dumps({"finite_reallocation": finite_transfer(),
                      "literal_sharp_cutoff": sharp_witness()},
                     indent=2, sort_keys=True))
