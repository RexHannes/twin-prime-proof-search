"""Exhaust exact discrete exponent profiles for the fixed-power sign identities."""

from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import combinations
from math import comb
import json


def partitions(total, count, minimum=1):
    if count == 1:
        if total >= minimum:
            yield (total,)
        return
    for first in range(minimum, total // count + 1):
        for tail in partitions(total-first, count-1, first):
            yield (first,) + tail


@lru_cache(None)
def prefix(exponents, cutoff):
    coefficients = Counter({0: 1})
    for exponent in exponents:
        if exponent > cutoff:
            break
        previous = tuple(coefficients.items())
        for value, coefficient in previous:
            if value + exponent <= cutoff:
                coefficients[value + exponent] -= coefficient
    return sum(coefficients.values())


def check():
    total, cutoff, jmax = 40, 3, 3
    middle = total // 2 - 2*cutoff
    t = Fraction(cutoff, total)
    assert t < Fraction(1, 12) and (jmax+1)*t < Fraction(1, 3)
    constants = {}
    for j in range(2, jmax+1):
        constants[j] = (1 + 2**j * (2 + 1/t)
                        + sum(constants[i]*comb(j, i)*2**(j-i)
                              for i in range(2, j)))

    counts = Counter()
    for rank in range(1, 10):
        for exponents in partitions(total, rank):
            counts[rank] += 1
            small = tuple(x for x in exponents if x <= cutoff)
            sum_small = sum(small)
            j = len(small)
            m = sum(cutoff < x <= middle for x in exponents)
            ms = prefix(small, cutoff)
            # The prefix complement of the complete quotient vanishes normally,
            # whereas the unit quotient contributes one on a prime input.
            raw = 0
            for i, owner in enumerate(exponents):
                if owner <= cutoff:
                    continue
                quotient = exponents[:i] + exponents[i+1:]
                raw += owner * (int(not quotient)-prefix(quotient, cutoff))
            corrected = raw + total*m*ms
            assert raw == int(rank == 1)*total - (total-sum_small)*ms
            assert corrected == int(rank == 1)*total + ((m-1)*total+sum_small)*ms

            tags = {}
            pair_adjust = 0
            for i in range(2, min(jmax, j)+1):
                tags[i] = 0
                for chosen in combinations(range(j), i):
                    other = tuple(x for k, x in enumerate(small) if k not in chosen)
                    mu_prefix = prefix(other, cutoff)
                    tags[i] += mu_prefix
                    qs = sum(small[k] for k in chosen)
                    if i == 2 and qs > cutoff:
                        pair_adjust += (total-qs)*mu_prefix
            if rank <= 2:
                assert pair_adjust == 0
            if rank == 3:
                assert raw-pair_adjust <= 0 <= corrected
            surcharge = total*sum(constants[i]*value for i, value in tags.items())
            balanced_pair = rank == 2 and min(exponents) > middle
            if j <= jmax and not balanced_pair:
                assert raw-surcharge <= 0 <= corrected+surcharge
    return {"total_units": total, "U_units": cutoff, "H_units": middle,
            "J": jmax, "ordered_partitions_by_rank": dict(counts),
            "all_profiles": sum(counts.values()),
            "constants": {i: str(c) for i, c in constants.items()}}


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
