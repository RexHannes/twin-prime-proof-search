"""Exact bounds for the native five-prime integral with polynomial face integration."""
from argparse import ArgumentParser
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations, product
from math import comb, factorial, lcm, prod
import json

EPSILON = F(1, 10**9)
SCALE = 10**20
CORNERS = list(product((0, 1), repeat=4))
ZERO = F(0)


def admissible(indices):
    i, j, k, l = indices
    s = sum(indices)
    return (i + 1 <= 19 and all(v + 1 <= 19 or v >= 21 for v in indices)
            and l + 1 + s <= 96 and s + 21 <= 96 and 100 <= 49 + s
            and 51 <= i + k + l and k + l + 2 <= 49)


@lru_cache(maxsize=None)
def upper_monomial(y, k):
    """Integral of u1...uk on [0,1]^3 over sum u >= y."""
    full = F(1, 2**k)
    if y <= 0:
        return full
    if y >= 3:
        return ZERO
    lower = ZERO
    for a in range(4):
        height = y - a
        if height <= 0:
            break
        for overlap in range(max(0, a - (3 - k)), min(k, a) + 1):
            multiplicity = (-1)**a * comb(k, overlap) * comb(3 - k, a - overlap)
            for chosen in range(overlap + 1):
                degree = 3 + k - overlap + chosen
                lower += multiplicity * comb(overlap, chosen) * height**degree / factorial(degree)
    return full - lower


@lru_cache(maxsize=None)
def upper_basis(y, ones):
    """Integrate a 3-coordinate multilinear corner basis above the face."""
    return sum((-1)**j * comb(3 - ones, j) * upper_monomial(y, ones + j)
               for j in range(4 - ones))


@lru_cache(maxsize=None)
def moments(faces):
    weights = []
    for bits in CORNERS:
        value = F(2, 16)
        for excluded, y in faces:
            ones = sum(bits) - bits[excluded]
            value += upper_basis(y, ones) / 2
        weights.append(value)
    common = lcm(*(w.denominator for w in weights))
    numbers = [w.numerator * (common // w.denominator) for w in weights]
    mass = sum(numbers)
    first = [sum(w for w, bits in zip(numbers, CORNERS) if bits[j]) for j in range(4)]
    assert 2 * common <= mass <= 6 * common and min(numbers) >= 0
    return common, numbers, mass, first


def clamp_face(y):
    return min(max(ZERO, y), F(3))


def verify_moments():
    assert upper_monomial(F(1), 0) == F(5, 6)
    assert upper_monomial(F(1), 1) == F(1, 2) - F(1, 24)
    assert upper_monomial(F(1), 2) == F(1, 4) - F(1, 120)
    assert upper_monomial(F(1), 3) == F(1, 8) - F(1, 720)
    for y in [F(0), F(1, 3), F(1), F(3, 2), F(2), F(8, 3), F(3)]:
        for m in range(4):
            assert upper_basis(y, m) + upper_basis(3 - y, 3 - m) == F(1, 8)
        assert sum(comb(3, m) * upper_basis(y, m) for m in range(4)) == upper_monomial(y, 0)


def enclosure(subdivisions):
    if subdivisions < 1:
        raise ValueError("subdivisions must be positive")
    mesh = 100 * subdivisions
    unit_half = F(mesh, 2)
    eps = mesh * EPSILON
    lower = upper = cells = boxes = 0
    for indices in filter(admissible, combinations(range(3, 49), 4)):
        boxes += 1
        shifts = [2 if indices[j] >= 21 else 1 for j in (2, 3)]
        bands = [range(j * subdivisions, (j + 1) * subdivisions) for j in indices]
        for lo in product(*bands):
            cells += 1
            free = mesh - sum(lo)
            assert free - 4 >= lo[-1] + 1
            faces = []
            for excluded, shift in zip((2, 3), shifts):
                base = unit_half - (sum(lo) - lo[excluded])
                faces.extend(((excluded, clamp_face(base + shift * eps)),
                              (excluded, clamp_face(base - eps))))
            common, weights, mass, first = moments(tuple(faces))
            xnums = [v * mass + a for v, a in zip(lo, first)]
            last = mesh * mass - sum(xnums)
            lower += mesh * mass**6 * SCALE // (common * prod(xnums) * last)
            for bits, weight in zip(CORNERS, weights):
                vertex_product = prod(a + b for a, b in zip(lo, bits)) * (free - sum(bits))
                denominator = common * vertex_product
                upper += (mesh * weight * SCALE + denominator - 1) // denominator
    assert boxes == 1566 and cells == boxes * subdivisions**4
    return dict(subdivisions=subdivisions, boxes=boxes, cells=cells, denominator=SCALE,
                J_lower_numerator=lower, J_upper_numerator=upper)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--subdivisions', type=int, default=2)
    args = parser.parse_args()
    verify_moments()
    print(json.dumps(enclosure(args.subdivisions), indent=2))
