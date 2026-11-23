"""Verify face moments via an independent elementary Laplace-transform formula."""
from collections import defaultdict
from fractions import Fraction as F
from math import factorial
from face_integral import EPSILON, upper_basis


def laplace_upper(y, ones):
    # Each factor is (s-1+exp(-s))/s^2 or (1-(1+s)*exp(-s))/s^2.
    coeff = {(0, 0): 1}
    for axis in range(3):
        factor = (((0, 0, 1), (1, 0, -1), (1, 1, -1))
                  if axis < ones else ((0, 1, 1), (0, 0, -1), (1, 0, 1)))
        nxt = defaultdict(int)
        for (delay, deg), value in coeff.items():
            for jump, power, sign in factor:
                nxt[delay + jump, deg + power] += value * sign
        coeff = nxt
    lower = sum(weight * max(0, y-delay)**(6-deg) / factorial(6-deg)
                for (delay, deg), weight in coeff.items() if y > delay)
    return F(1, 8) - lower


def check():
    ys = {F(i, 13) for i in range(40)} | {F(3)}
    for mesh in (200, 400):
        for n in range(-1, 5):
            for shift in (-1, 1, 2):
                ys.add(max(F(0), min(F(3), n + shift * mesh * EPSILON)))
    for y in sorted(ys):
        for j in range(4):
            assert laplace_upper(y, j) == upper_basis(y, j), (y, j)
    print(f"Independent Laplace check matched all {len(ys)*4} rational moments.")


if __name__ == '__main__':
    check()
