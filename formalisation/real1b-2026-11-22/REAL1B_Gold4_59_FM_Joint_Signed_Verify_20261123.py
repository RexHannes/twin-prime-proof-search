#!/usr/bin/env python3
"""Finite checks for the Gold 4.59 scoped joint signed source theorem.

This program checks exact rational geometry, kernel coefficients, numerical
budgets, and two finite integer examples. It does NOT prove the analytic
distribution or sieve theorems, certify originality, or establish G5.
Run: python3 REAL1B_Gold4_59_FM_Joint_Signed_Verify_20261123.py
"""
from __future__ import annotations

import hashlib
import json
from decimal import Decimal, localcontext
from fractions import Fraction as F
from itertools import combinations
from math import isqrt, prod


def need(condition, label):
    if not condition:
        raise AssertionError(label)


def decimal(q, precision=55):
    q = F(q)
    with localcontext() as ctx:
        ctx.prec = precision
        return str(Decimal(q.numerator) / Decimal(q.denominator))


def record(q):
    q = F(q)
    return {"numerator": str(q.numerator), "denominator": str(q.denominator),
            "decimal": decimal(q)}


def positive_boxes():
    boxes = []
    mass_lower = F(0)
    for ix in combinations(range(3, 49), 4):
        i1, i2, i3, i4 = ix
        s = sum(ix)
        if not (i1 + 1 <= 19 and all(i + 1 <= 19 or i >= 21 for i in ix)):
            continue
        if not (i4 + 1 <= 100 - s - 4 and 100 - s - 4 >= 21 and 100 - s <= 49):
            continue
        if not (i1 + i3 + i4 >= 51 and i3 + i4 + 2 <= 49):
            continue
        boxes.append(ix)
        mass_lower += F(200, prod(i + 1 for i in ix) * (100 - s))

        # Entire-box certificates, rather than sampling values of H.
        need(i1 >= 4, "All output factors exceed n^.04")
        lo = [F(i, 100) for i in ix] + [F(100 - s - 4, 100)]
        hi = [F(i + 1, 100) for i in ix] + [F(100 - s, 100)]
        need(all(hi[j] <= lo[j + 1] for j in range(4)), "Ordered disjoint bins")
        need(max(hi) <= F(49, 100), "Every singleton is active")
        need(hi[0] <= F(19, 100), "Smallest coordinate excludes good set")
        need(all(h <= F(19, 100) or l >= F(21, 100)
                 for l, h in zip(lo, hi)), "All factors avoid inactive gap")

        # Pairs with t5 use t5=1-t1-t2-t3-t4, not an independent interval.
        def pair_upper(i, j):
            if j < 4:
                return hi[i] + hi[j]
            return 1 - sum(lo[h] for h in range(4) if h != i)

        guaranteed_pairs = sum(pair_upper(i, j) <= F(49, 100)
                               for i, j in combinations(range(5), 2))
        need(guaranteed_pairs >= 8, "At least eight active pairs on whole box")
        need(1 - max(hi) >= F(51, 100), "No quadruple can occur")
        # Each of these >=8 pairs has a complementary triple >.51.
        need(10 - guaranteed_pairs <= 2, "At most two negative triples")
        need(1 - 5 + guaranteed_pairs - (10 - guaranteed_pairs) >= 2,
             "Native Phi lower bound 2")
        need(1 - 5 + 10 == 6, "Native Phi upper bound 6")

    need(len(boxes) == 1566, "Exact box count")
    need(mass_lower > F(".17222"), "Positive weighted profile lower bound")
    digest = hashlib.sha256(json.dumps(boxes, separators=(",", ":")).encode()).hexdigest()
    return {"count": len(boxes), "minimum_first_index": min(x[0] for x in boxes),
            "tuples_sha256": digest, "twice_profile_mass_lower": record(mass_lower),
            "native_coefficient_range_on_each_whole_box": [2, 6]}


def ordered_compositions(total, rank, minimum):
    if rank == 1:
        if total >= minimum:
            yield (total,)
        return
    for first in range(minimum, total // rank + 1):
        for rest in ordered_compositions(total - first, rank - 1, first):
            yield (first,) + rest


def direct_kernel_log_coefficients(t, u, d):
    out = []
    for ell, exponent in enumerate(t):
        if exponent <= u:
            out.append(0)
            continue
        others = [j for j in range(len(t)) if j != ell]
        value = 0
        for mask in range(1 << len(others)):
            selected = [j for h, j in enumerate(others) if mask >> h & 1]
            m = sum(t[j] for j in selected)
            if m > u and m + exponent > d:
                value += (-1) ** len(selected)
        out.append(value)
    return tuple(out)


def kernel_grid_checks():
    total, u, d = 1000, 240, 490
    counts = {}
    triangle_profiles = 0
    for rank in range(1, 5):
        count = 0
        for t in ordered_compositions(total, rank, u + 1):
            coeff = direct_kernel_log_coefficients(t, u, d)
            b = sum(c * exponent for c, exponent in zip(coeff, t))
            edges = [(i, j) for i, j in combinations(range(rank), 2)
                     if t[i] + t[j] <= d]
            if rank == 1:
                need(coeff == (0,), "Prime input has zero large-product kernel")
            else:
                expected = tuple(-1 + sum(i in edge for edge in edges)
                                 for i in range(rank))
                need(coeff == expected, "Full divisor kernel equals graph coefficients")
                triangle = rank == 4 and len(edges) == 3
                if triangle:
                    need(edges == [(0, 1), (0, 2), (1, 2)], "Only small-prime triangle")
                    need(b > 440 and b <= 470, "Triangle B bounds")
                    triangle_profiles += 1
                else:
                    need(b <= -20, "All other composite ranks have negative kernel")
                need(b <= -20 + (490 if triangle else 0), "Joint kernel inequality")
            count += 1
        counts[str(rank)] = count
    return {"denominator": 1000, "profiles_by_rank": counts,
            "triangle_profiles": triangle_profiles,
            "scope": "Finite limiting-profile checks; all-real proof is in the manuscript"}


def prime(n):
    if n < 2:
        return False
    for d in range(2, isqrt(n) + 1):
        if n % d == 0:
            return False
    return True


def integer_examples():
    examples = [
        (F(1, 100), [1093, 1097, 1283, 2459], [223, 233, 383, 433, 439]),
        (F(1, 1000), [100003, 100207, 100237, 110237],
         [4567, 5393, 10613, 14633, 28949]),
    ]
    result = []
    for sigma, inputs, outputs in examples:
        k, n = prod(inputs), prod(outputs)
        need(n == k + 2, "Exact fixed shift two")
        need(len(set(inputs)) == 4 and len(set(outputs)) == 5, "Both sides squarefree")
        need(all(prime(p) for p in inputs + outputs), "Every displayed factor is prime")
        alpha, beta = F(1, 4) - sigma, F(1, 2) - sigma
        need(all(p ** alpha.denominator > n ** alpha.numerator for p in inputs),
             "Exact polynomial input roughness")
        short = [(i, j) for i, j in combinations(range(4), 2)
                 if (inputs[i] * inputs[j]) ** beta.denominator <= n ** beta.numerator]
        need(short == [(0, 1), (0, 2), (1, 2)], "Actual input short-pair triangle")
        need(all(p ** 50 > n ** 9 for p in outputs), "Every output factor exceeds n^.18")
        need(all(p ** 1000 < n ** 199 or p ** 5 > n for p in outputs),
             "Exact exclusion of native narrow gap around exponent .2")
        need(any(p ** 1000 < n ** 199 for p in outputs), "Output is outside good set")
        # >.18 implies every pair <.46 and every triple >.54. Thus H=6,
        # no K marks occur, and the native retained rank is five.
        result.append({"sigma": str(sigma), "k": str(k), "n": str(n),
                       "input_prime_factors": inputs, "output_prime_factors": outputs,
                       "kernel_log_coefficients": [1, 1, 1, -1], "native_Phi": 6,
                       "scope": "Finite joint-source example, not an asymptotic population claim"})
    return result


def zero_chamber_example():
    factors = [1009, 1000003, 10000019]
    k = prod(factors)
    x = k + 2
    need(all(prime(p) for p in factors), "Zero chamber exact prime factors")
    need(factors[0] ** 25 <= x ** 6, "Zero chamber small nontrivial cofactor")
    need(all(p ** 25 > x ** 6 for p in factors[1:]), "Zero chamber large factors")
    need((factors[1] * factors[2]) ** 100 > x ** 49, "Zero chamber full long pair")
    coeff = []
    for i, ell in enumerate(factors):
        if ell ** 25 <= x ** 6:
            coeff.append(0)
            continue
        others = [p for j, p in enumerate(factors) if j != i]
        c = 0
        for mask in range(1 << len(others)):
            selected = [p for j, p in enumerate(others) if mask >> j & 1]
            m = prod(selected)
            if m ** 25 > x ** 6 and (m * ell) ** 100 > x ** 49:
                c += (-1) ** len(selected)
        coeff.append(c)
    need(coeff == [0, 0, 0], "Original full kernel vanishes exactly")
    return {"k":str(k), "x":str(x), "prime_factors":factors,
            "native_logarithmic_coefficients":coeff,
            "output_coefficient_assumption":"none"}


def budgets():
    sigma, alpha, lower_mass = F(1, 100), F(6, 25), F(".17222")
    theta, rho = F(49999, 100000), F(3999, 100000)
    need(2 * alpha < theta < F(1, 2), "Lower sieve fixed level")
    need(3 * rho < F(1, 2) and rho < F(1, 25), "Upper sieve fixed level")
    triangle_mass = sigma ** 3 / (24 * alpha ** 4)
    favorable = 2 * sigma * 4 * (theta - 2 * alpha) / theta ** 2 * lower_mass
    positive_cost = 6 * (F(1, 2) - sigma) * F(2, 1) / (3 * rho) * triangle_mass
    margin = favorable - positive_cost
    need(favorable == F(68853556, 62497500025), "Exact fixed-level favorable term")
    need(positive_cost == F(153125, 248769792), "Exact fixed-level triangle cost")
    need(margin == F(7558755113252227, 15547490081739244800), "Exact fixed-level margin")
    banked = F(".00048")
    need(margin > banked, "Outward joint source margin")
    lim_favorable = 8 * sigma * F(2, 25) * lower_mass
    lim_cost = 6 * (F(1, 2) - sigma) * F(50, 3) * triangle_mass
    need(lim_favorable - lim_cost == F(1892806579, 3888000000000), "Limiting budget")
    partial_crude = sigma ** 3 * (F(1, 2) - 3 * sigma) / alpha ** 4
    partial_weighted = sigma ** 3 * (F(1, 2) - F(17, 4) * sigma) / (alpha ** 3 * (F(1, 4) + 3 * sigma))
    need(partial_crude == F(47, 331776), "Additional crude source upper")
    need(partial_weighted == F(61, 516096), "Additional weighted source upper")

    cminus, uplus = F(".999892775499"), F("1.000107183501")
    pilot, strong = F(".999807183501"), F(".997720224")
    need(uplus - cminus == F(".000214408002"), "Inherited weak gap")
    need(cminus - pilot == F(".000085591998"), "Conditional pilot reserve")
    need(cminus + banked == F("1.000372775499"), "Full complementary target")
    need(pilot + banked == F("1.000287183501"), "Full complementary pilot target")
    need(strong + banked == F(".998200224"), "Full complementary historical target")

    # A ledger-level witness guards against calling the local margin a full gain.
    # It is not asserted to be a model for the primes or for all analytic inputs.
    aprime, ue, urest, t = F(".01"), F("-.00028"), F("1.00028"), F(0)
    need(ue == F(".02") * aprime - banked, "Joint relation in ledger witness")
    need(cminus <= ue + urest + t <= uplus, "Old strip admits ledger witness")
    need(urest + F(".02") * aprime > cminus + banked, "Complement still needs arithmetic")
    return {"sigma": str(sigma), "alpha": str(alpha), "lower_level": str(theta),
            "output_sieve_exponent": str(rho), "triangle_mass_upper": record(triangle_mass),
            "fixed_favorable": record(favorable), "fixed_positive_cost": record(positive_cost),
            "fixed_joint_margin_lower": record(margin),
            "outward_joint_margin": str(banked),
            "limiting_joint_margin_lower": record(lim_favorable - lim_cost),
            "additional_partial_upper_crude":record(partial_crude),
            "additional_partial_upper_weighted":record(partial_weighted),
            "complement_required_below": str(cminus + banked),
            "complement_pilot_ceiling": str(pilot + banked),
            "complement_historical_ceiling": str(strong + banked),
            "conditional_pilot_twin_reserve": str(cminus - pilot),
            "certified_terminal_gain": "0", "G3_originality_certified": False,
            "G5_closed": False, "ledger_witness_is_a_prime_model": False}


def main():
    result = {"status": "PASS_FINITE_CHECKS_ONLY", "date": "2026-11-23",
              "positive_boxes": positive_boxes(), "kernel_grid": kernel_grid_checks(),
              "integer_examples": integer_examples(), "zero_chamber_example":zero_chamber_example(),
              "budgets": budgets(),
              "analytic_theorems_verified_by_code": False,
              "external_originality_certified": False, "G5_closed": False}
    print(json.dumps(result, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
