"""Check the finite Gold 4.60 constant using exact rationals, report §§B–E."""
from fractions import Fraction as Q
from itertools import combinations
from math import prod


def joint_gain():
    total = Q(0)
    for cell in combinations(range(3, 49), 4):
        i, j, k, l = cell
        s = sum(cell)
        if not (i + 1 <= 19 and all(t + 1 <= 19 or t >= 21 for t in cell)
                and l + 1 <= 96 - s and 96 - s >= 21 and 100 - s <= 49
                and i + k + l >= 51 and k + l + 2 <= 49):
            continue
        theta = Q(49999, 100000)
        for t in cell:
            level = min(Q(1, 2) + Q(t, 200), Q(5, 8) - Q(3 * (t + 1), 400))
            if level > Q(1, 2):
                theta = max(theta, level - Q(1, 1000))
        profile = Q(200, prod(t + 1 for t in cell) * (100 - s))
        z = (theta - Q(48, 100)) / theta
        if not 0 < z < 1:
            raise ValueError("Logarithm lower bound outside its interval")
        total += Q(1, 50) * (2 / theta) * 2 * (z + z**3 / 3) * profile
    return total


def check():
    lower = joint_gain()
    triangle = Q(153125, 248769792)
    if lower <= Q("0.0026942415488") or lower - triangle <= Q("0.00207"):
        raise ValueError("Boxwise signed margin failed")
    print("Exact boxwise sum minus the triangle cost exceeds 0.00207.")


if __name__ == "__main__":
    check()
