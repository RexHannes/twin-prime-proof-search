"""Check the finite physical coefficients and conservative numerical charge."""
from fractions import Fraction as Q
from itertools import combinations
from math import prod
import json


def subsets(items):
    for size in range(len(items) + 1):
        yield from combinations(items, size)


def check_terms():
    primes = [3, 5, 7, 11, 13, 17, 19, 23, 29, 37, 47, 71]
    # This additive function verifies the same finite log(k/d) arithmetic.
    log_weight = {p: p**2+1 for p in primes}
    prefix_cutoffs = [13, 16, 18, 22]
    lower_cut = 10
    upper_cut = 22
    low_prime_limit = 40

    def f_average(value):
        return Q(sum(value > u for u in prefix_cutoffs), len(prefix_cutoffs))

    def prefix(items):
        return sum((-1)**len(a)*(1-f_average(prod(a))) for a in subsets(items))

    verified = 0
    for rank in range(2, 7):
        for factors in combinations(primes, rank):
            k = prod(factors)
            if k <= low_prime_limit:
                continue
            lk = sum(log_weight[p] for p in factors)
            small = tuple(p for p in factors if p <= upper_cut)
            big = tuple(p for p in factors if p > upper_cut)
            j = sum(p <= low_prime_limit for p in big)
            raw = Q(0)
            low = Q(0)
            for ell in factors:
                if ell <= lower_cut:
                    continue
                rest = tuple(p for p in factors if p != ell)
                high = sum((-1)**len(t)*f_average(prod(t)) for t in subsets(rest))
                raw += log_weight[ell]*high
                if ell <= low_prime_limit:
                    low += (log_weight[ell]+f_average(ell)*(lk-log_weight[ell]))*high
            main = prefix(small)
            base = -main*sum(log_weight[p] for p in big)
            raw_formula = base - sum(log_weight[p]*prefix(tuple(q for q in small if q != p))
                                     for p in small if p > lower_cut)
            corrected_formula = base+j*main*lk + sum(
                f_average(p)*(lk-log_weight[p])*prefix(tuple(q for q in small if q != p))
                for p in small
            )
            assert raw == raw_formula and raw-low == corrected_formula
            verified += 1
    return verified


def main():
    harmonic32 = sum(Q(1, j) for j in range(1, 33))

    def log_low(n, d, terms):
        t = Q(n-d, n+d)
        return 2*sum(t**(2*j+1)/(2*j+1) for j in range(terms))

    assert log_low(2, 1, 3) > Q(".693")
    assert log_low(4, 3, 2) > Q(".287")
    assert harmonic32 < Q("4.059")
    assert log_low(20, 11, 2) > Q(".594")
    debit = Q(".55")*Q("1.64")*Q(81,110)*Q(".69")*Q(".287")*Q(69,169)**2
    assert debit == Q(313110797643,14280500000000) and debit > Q(".021")
    print(json.dumps({"physical_coefficient_tests": check_terms(),
                      "fixed_power_charge_lower_times_t": str(debit),
                      "fixed_power_charge_rounded_down": "0.021/t"}, indent=2))


if __name__ == "__main__":
    main()
