#!/usr/bin/env python3
"""Finite algebra and sign checks for the smooth-owner proof. No third-party modules."""

from __future__ import annotations

import cmath
import functools
import itertools
import json
import math
from fractions import Fraction


@functools.cache
def factors(number: int) -> tuple[int, ...]:
    result = []
    prime = 2
    while prime * prime <= number:
        while number % prime == 0:
            result.append(prime)
            number //= prime
        prime += 1
    if number > 1:
        result.append(number)
    return tuple(result)


def signed_divisors(primes: tuple[int, ...]):
    for rank in range(len(primes) + 1):
        for chosen in itertools.combinations(primes, rank):
            yield math.prod(chosen), (-1) ** rank


@functools.cache
def above(value: int, x: int, exponent: Fraction) -> bool:
    return value ** exponent.denominator > x ** exponent.numerator


def averaged_row(quotient_factors, owner, scale, u_law, d_law):
    acc = Fraction()
    for u, pu in u_law:
        for d, pd in d_law:
            sharp = sum(mu for b, mu in signed_divisors(quotient_factors)
                        if above(b, scale, u) and above(b*owner, scale, d))
            acc += pu*pd*sharp
    return acc


def prefix_row(quotient_factors, owner, scale, u_law, d_law):
    total = Fraction(int(not quotient_factors))
    for b, mu in signed_divisors(quotient_factors):
        after_u = sum(p for u, p in u_law if above(b, scale, u))
        after_d = sum(p for d, p in d_law if above(b*owner, scale, d))
        total -= mu*(1-after_u*after_d)
    return total


def verify_compensation():
    # One integer unit represents 1/120 of log x. Equal size bins can represent
    # distinct primes, so these tuples test independent labels, not actual powers.
    scale = 120
    v = 4
    t = 2*v
    h = scale//2 - 3*v
    u_law = (5, 6, 7, 8)

    def f(size):
        return Fraction(sum(size > u for u in u_law), len(u_law))

    def partition(total, least, budget):
        if total == 0:
            yield ()
        elif budget:
            for first in range(least, total + 1):
                for suffix in partition(total-first, first, budget-1):
                    yield (first,) + suffix

    def recorded_row(quotient):
        return sum((-1)**len(choice)*f(sum(choice)) for rank in range(len(quotient)+1)
                   for choice in itertools.combinations(quotient,rank))

    results = {"factor_profiles":0, "nonpositive_for_both_channels":0, "two_small_adverse":0,
               "nearhalf_semiprime":0}
    for parts in partition(scale, 2, 4):
        rows = [(p,p*recorded_row(parts[:i]+parts[i+1:]))
                for i,p in enumerate(parts) if p>v]
        raw = sum(row for _,row in rows)
        corrected = raw-sum((1+f(p)*Fraction(scale-p,p))*row for p,row in rows if p<=h)
        low = [p for p in parts if p<=t]
        if len(parts) == 1:
            assert raw == corrected == 0
        elif len(parts) == 2 and min(parts) <= h:
            assert raw <= 0 and corrected == 0
        elif len(parts) == 2:
            assert not low and raw == corrected == -scale
            results["nearhalf_semiprime"] += 1
        elif not low:
            assert raw == -scale and corrected == (sum(p<=h for p in parts)-1)*scale
        elif len(low) == 1:
            assert raw<=0 and corrected>=0
        if low and sum(low)<=v:
            assert raw == corrected == 0
        if raw<=0 and corrected>=0:
            results["nonpositive_for_both_channels"] += 1
        elif len(parts)>2:
            assert len(low)>=2 and sum(low)>v
            results["two_small_adverse"] += 1
        results["factor_profiles"] += 1
    assert all(v>0 for v in results.values())
    return results


def verify_product_cap():
    # Each integer coordinate of the log product is tested independently,
    # so the log identities are checked in the free group on prime labels.
    labels = (3, 5, 7, 11, 13, 17, 19)
    cutoff = max(labels)
    masks = range(1 << len(labels))

    def subsets(mask):
        subset = mask
        while subset:
            yield subset
            subset = (subset - 1) & mask
        yield 0

    product = [math.prod(p for i,p in enumerate(labels) if mask & (1<<i)) for mask in masks]
    prefix = [sum((-1)**part.bit_count() for part in subsets(mask)
                  if product[part] <= cutoff) for mask in masks]
    inverse = [1] + [0] * (len(masks) - 1)
    for mask in masks[1:]:
        inverse[mask] = -sum(prefix[part] * inverse[mask ^ part]
                             for part in subsets(mask) if part)
    for mask in masks:
        assert sum(inverse[p] * prefix[mask ^ p] for p in subsets(mask)) == int(not mask)
    c0 = [int(not mask) - inverse[mask] for mask in masks]
    c1 = [[sum(int(bool(p & (1<<i))) * prefix[p] * inverse[mask ^ p]
               for p in subsets(mask)) for mask in masks] for i in range(len(labels))]
    cases = tail_mismatch = 0
    for cap in (31, 70, 191, 1365, 24999):
        for mask in masks:
            allowed = [part for part in subsets(mask) if product[part] <= cap]
            p0 = sum(c0[p]*prefix[mask^p] for p in allowed)
            p1 = [sum(chan[p]*prefix[mask^p] for p in allowed) for chan in c1]
            scalar_target = prefix[mask] - int(not mask)
            log_target = [int(bool(mask & (1<<i))) * prefix[mask] for i in range(len(labels))]
            if product[mask] <= cap:
                assert p0 == scalar_target and p1 == log_target
                cases += len(labels) + 1
            elif p0 != scalar_target or p1 != log_target:
                tail_mismatch += 1
    assert cases and tail_mismatch
    return {"exact_scalar_or_log_coordinate_identities": cases,
            "high_product_configurations_with_residual": tail_mismatch}


def main():
    x = 6000
    u_law = [(Fraction(23,100),Fraction(1,3)), (Fraction(47,200),Fraction(1,6)),
             (Fraction(6,25),Fraction(1,2))]
    d_law = [(Fraction(12,25),Fraction(1,3)), (Fraction(97,200),Fraction(1,3)),
             (Fraction(49,100),Fraction(1,3))]
    output = {"squarefree_rows": 0, "prime_boundaries": 0, "semiprime_owners": 0,
              "kept": 0, "small_only": 0, "rank_only": 0, "small_and_rank": 0,
              "fourier_products": 0}
    max_fourier_error = 0.0
    for k in range(x//2-1, x-1):
        primes = factors(k)
        if len(set(primes)) != len(primes):
            continue
        for owner in primes:
            if not above(owner, x, Fraction(6,25)):
                continue
            quotient = tuple(p for p in primes if p != owner)
            direct = averaged_row(quotient, owner, x, u_law, d_law)
            assert direct == prefix_row(quotient, owner, x, u_law, d_law)
            output["squarefree_rows"] += 1
            if not quotient:
                assert direct == 0
                output["prime_boundaries"] += 1
            if len(quotient) == 1 and above(quotient[0],x,Fraction(6,25)):
                assert direct == -1
                output["semiprime_owners"] += 1
            small = any(p <= 3 for p in quotient)
            high_rank = len(quotient) >= 3
            region = ("small_and_rank" if small and high_rank else "small_only" if small
                      else "rank_only" if high_rank else "kept")
            output[region] += 1
            for freq in (0.0, 3.25, 19.0):
                explicit = sum(mu*cmath.exp(1j*freq*math.log(b)/math.log(x))
                               for b,mu in signed_divisors(quotient))
                product = math.prod(1-cmath.exp(1j*freq*math.log(p)/math.log(x))
                                    for p in quotient)
                max_fourier_error = max(max_fourier_error, abs(product-explicit))
                assert abs(product-explicit) < 4e-12
                output["fourier_products"] += 1
    assert sum(output[k] for k in ("kept","small_only","rank_only","small_and_rank")) == output["squarefree_rows"]
    assert all(output[k] > 0 for k in ("kept", "small_only", "rank_only", "small_and_rank"))
    # Rational outward checks for the high-output signed subbudget.
    ratio = Fraction(1, 10**8-1)
    assert 40000*ratio**2 < Fraction(5, 10**12)
    assert 4*ratio**2 < Fraction(5, 10**16)
    assert Fraction(2,1)/(Fraction(3,16)*Fraction(2,100)**2) < 40000
    output["high_output_rational_bounds"] = "passed"
    # Universal cutoff-sign dual certificate. Modulo X^4, the coefficients
    # of the product encode all active subset exponents for h(4y)=0.
    dual = [((1,)*8, Fraction(3,20)), ((1,1,2,2,2), Fraction(7,5)),
            ((2,)*4, Fraction(7,20))]
    mixed = [Fraction(0) for _ in range(4)]
    for labels, multiplier in dual:
        coeff = [1,0,0,0]
        for degree in labels:
            for j in range(3, degree-1, -1):
                coeff[j] -= coeff[j-degree]
        mixed = [a+multiplier*b for a,b in zip(mixed,coeff)]
    assert mixed == [Fraction(19,10),-4,0,0]
    assert 4*(1-mixed[0]/4) == Fraction(21,10)
    output["universal_cutoff_slope_times_width"] = "at least 21/10"
    # Strict boundary equality is excluded even for exact rational powers.
    assert not above(8, 64, Fraction(1,2))
    assert above(9, 64, Fraction(1,2))
    n = 1729
    assert factors(n) == (7,13,19) and factors(n-2) == (11,157)
    assert 7**4 > n and 19**20 < n**9 and 11**4 > n
    for owner in factors(n-2):
        rest = tuple(p for p in factors(n-2) if p != owner)
        assert averaged_row(rest, owner, n, u_law, d_law) == -1
    # At a=1/4, w<11 follows from log(x)<8 and log(11)>2.
    assert Fraction(27,10)**8 > n and 3**2 < 11
    output["adverse_example"] = {"x":n,"input_factors":[11,157],"output_factors":[7,13,19],
                                 "profile":-2,"signed_contribution":"2 log(1727)"}
    output["max_fourier_error"] = max_fourier_error
    output["compensation"] = verify_compensation()
    output["product_cap"] = verify_product_cap()
    output["status"] = "finite algebra checks passed"
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
