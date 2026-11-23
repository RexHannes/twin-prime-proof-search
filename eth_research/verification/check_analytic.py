"""Finite checks for the two sieve insertions and the five-prime unit counts."""
from fractions import Fraction
from itertools import combinations
from math import comb, gcd, prod, isqrt
import json


def prime_numbers(limit):
    flags = bytearray(b'\x01') * (limit + 1)
    flags[:2] = b'\x00\x00'
    for p in range(2, isqrt(limit) + 1):
        if flags[p]:
            flags[p*p::p] = b'\x00' * ((limit - p*p) // p + 1)
    return [p for p, present in enumerate(flags) if present]


def admissible(b):
    i, j, k, ell = b
    s = sum(b)
    return (i >= 3 and ell <= 48 and i+1 <= 19
            and all(t + 1 <= 19 or t >= 21 for t in b)
            and ell+1+s <= 96 and s+21 <= 96 and 100 <= 49+s
            and 51 <= i+k+ell and k+ell+2 <= 49)


def check():
    primes = prime_numbers(12000)
    rows = []
    total_tests = 0
    for y in [3, 7, 17, 29]:
        odd = [p for p in primes if 2 < p <= y]
        density = prod((1-Fraction(1,p) for p in primes if p<=y), start=Fraction(1))
        v = prod((1-Fraction(1,p-1) for p in odd), start=Fraction(1))
        singular = 2 * prod((1-Fraction(1,(p-1)**2) for p in odd), start=Fraction(1))
        assert v == singular * density
        for m in [1, 31, 31*37]:
            assert gcd(m, prod(odd)) == 1
            for q in primes:
                if q < 41:
                    continue
                count = sum((m*q-2)%p == 0 for p in odd)
                s = int(count==0)
                for r in [0, 2, 4]:
                    hi = sum((-1)**j * comb(count,j) for j in range(r+1) if j <= count)
                    defect = comb(count, r+1) if r+1 <= count else 0
                    assert hi - defect <= s <= hi
                    total_tests += 1
        rows.append({'y': y, 'v_over_density': str(singular)})
    bins = [b for b in combinations(range(3,49),4) if admissible(b)]
    assert len(bins) == 1566
    for i,j,k,ell in bins:
        assert i >= 4
        assert ell+1 <= 100-(i+j+k+ell+4)
        assert 100-(i+j+k+ell+4) >= 21
    return {'source_commit':'43facedcf40b2f998aa47f7198d6b9b5feb5b792', 'local_factors':rows,'bonferroni_pointwise_checks':total_tests,'valid_native_bins':len(bins),'smallest_possible_fifth_exponent_lower_bound':'21/100','purpose':'finite conventions only; analytic arguments require BV and PNT'}


if __name__ == '__main__':
    print(json.dumps(check(), indent=2))
