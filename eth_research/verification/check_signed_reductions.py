"""Reproduce two physical residual signs and exhaust the retuned divisor identity on a finite interval."""

import itertools
import json
import math

X = 10**20
WITNESSES = (
    ((3, 5, 7), 590760900827325373, (3777013, 4321123, 3800633), 1),
    ((7, 11), 810758267569684537, (3777013, 4321123, 3825049), -1),
)
LARGE_PREDECESSORS = {
    590760900827325373: {2: 2, 3: 1, 37: 1, 409: 1, 6427: 1, 506170891: 1},
    810758267569684537: {2: 3, 3: 1, 4730809: 1, 7140764821: 1},
}


def trial_factor(n):
    result = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            result[d] = result.get(d, 0) + 1
            n //= d
        d = 3 if d == 2 else d + 2
    if n > 1:
        result[n] = 1
    return result


def prove_prime(n, seen):
    if n in seen:
        return
    if n == 2:
        seen[n] = 1
        return
    factors = LARGE_PREDECESSORS[n] if n in LARGE_PREDECESSORS else trial_factor(n - 1)
    assert math.prod(p**e for p, e in factors.items()) == n - 1
    for p in factors:
        prove_prime(p, seen)
    for a in range(2, n):
        if pow(a, n - 1, n) == 1 and all(math.gcd(pow(a, (n - 1) // p, n) - 1, n) == 1 for p in factors):
            seen[n] = a
            return
    raise AssertionError(f"No Lucas primality witness for {n}")


def mobius_divisors(primes):
    for r in range(len(primes) + 1):
        for group in itertools.combinations(primes, r):
            yield math.prod(group), (-1)**r


def signed_witnesses():
    result = []
    primes = {}
    # log X < 50, 50^(1/100) < 21/20 < log 3 (use 2(1/2 + (1/2)^3/3)).
    assert 21**100 > 50 * 20**100 and 21 * 12 < 13 * 20
    for small, q, output_primes, expected_prefix in WITNESSES:
        for p in (*small, q, *output_primes):
            prove_prime(p, primes)
        s = math.prod(small)
        k = s * q
        n = math.prod(output_primes)
        assert n == k + 2 and X // 2 < n <= X
        assert len(set(output_primes)) == 3 and len(set((*small, q))) == len(small) + 1
        # Y = x^(2/25), H = x^(17/50), and w < 3.
        assert all(3 <= p and p**25 <= X**2 for p in small)
        assert s**25 > X**2 and q**50 > X**17
        assert all(n**2001 < p**10000 < n**4999 for p in output_primes)
        coefficient = sum(mu for d, mu in mobius_divisors(small) if d**25 <= X**2)
        assert coefficient == expected_prefix
        result.append({"k": str(k), "n": str(n), "input_primes": [*small, q],
                       "output_primes": output_primes, "small_product": s, "middle_count": 0,
                       "mobius_prefix": coefficient, "coefficient_of_log_q": -coefficient})
    return {"rows": result, "primes_certified_by_Lucas": len(primes)}


def exhaust_divisor_identity():
    rows = 0
    for k in range(2501, 5001):
        decomposition = trial_factor(k)
        if any(e > 1 for e in decomposition.values()):
            continue
        primes = tuple(decomposition)
        for y, h in ((3, 47), (11, 29), (17, 53), (21, 37)):
            small = tuple(p for p in primes if p <= y)
            m = sum(y < p <= h for p in primes)
            prefix = sum(mu for d, mu in mobius_divisors(small) if d <= y)
            for p in primes:
                complete_row = (sum(mu for e, mu in mobius_divisors(tuple(q for q in primes if q != p))
                                    if e > y and p * e > y**2) if p > y else 0)
                via_rewrite = int(len(primes) == 1) + (m - 1 + int(p in small)) * prefix
                assert complete_row + m * prefix == via_rewrite
            rows += 1
    return rows


def subsets(items):
    for i in range(len(items) + 1):
        yield from itertools.combinations(items, i)


def check_subset_corrections():
    # Evaluate two independent formal log-scalar assignments on finite labelled sets.
    counts = {"subsets": 0, "homogeneous_derangements": 0}
    cutoff = 40
    for small in ((3, 5, 7, 11, 13, 17), (7, 11, 13, 17, 19, 23, 29)):
        for amplitude in (-317, 163):
            prefixes, inverse, corrections = {}, {}, {}
            for group in subsets(small):
                prefixes[group] = sum(mu for d, mu in mobius_divisors(group) if d <= cutoff)
                if not group:
                    inverse[group], corrections[group] = 1, 0
                    continue
                inverse[group] = -prefixes[group]
                # Distinct integer log-surrogates indexed by prime labels verify linear arithmetic.
                base = (amplitude + sum(group)) * prefixes[group]
                corrections[group] = -base
                proper = [s for s in subsets(group) if s and s != group]
                for t in proper:
                    comp = tuple(v for v in group if v not in t)
                    inverse[group] -= inverse[t] * prefixes[comp]
                    corrections[group] -= corrections[t] * prefixes[comp]
                new_weight = base + sum(corrections[t] *
                    prefixes[tuple(v for v in group if v not in t)] for t in subsets(group) if t)
                assert new_weight == 0
                assert sum(inverse[t] * prefixes[tuple(v for v in group if v not in t)]
                           for t in subsets(group)) == 0
                counts["subsets"] += 1
                if all(p * p > cutoff for p in group):
                    j = len(group)
                    derangements = sum((-1)**i * (math.factorial(j) // math.factorial(i))
                                       for i in range(j + 1))
                    assert inverse[group] == derangements
                    if j >= 2:
                        assert corrections[group] == amplitude * derangements + math.factorial(j - 1) * sum(group)
                    counts["homogeneous_derangements"] += 1
    return counts


if __name__ == "__main__":
    print(json.dumps({"balanced_physical_tests": signed_witnesses(),
                      "squarefree_cutoff_cases": exhaust_divisor_identity(),
                      "labelled_correction_cases": check_subset_corrections()}, indent=2))
