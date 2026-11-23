"""Rational two-sided budget on the exact REAL 1B source."""
from decimal import Decimal, localcontext
from fractions import Fraction as Q
from math import factorial
import json


def dec(q):
    with localcontext() as ctx:
        ctx.prec = 50
        return str(Decimal(q.numerator) / Decimal(q.denominator))


def exp_lower(v):
    return sum(v**k / factorial(k) for k in range(131))


def main():
    e = Q(1, 10**9)
    delta = e / 400
    good_lower = Q(1, 5) - e
    nu = Q(1, 5) - 2 * e
    beta = Q(1, 2) - 2 * e
    jp_balanced = 2*e / (beta*(1-beta))
    jp_short = (e / (good_lower * (1-good_lower))
                + e**2 / (2*good_lower**2*Q(3,5))
                + 3*(5*e)**4 / (factorial(5)*factorial(4)*good_lower**5))
    jp = jp_balanced + jp_short
    i2 = e / (nu*(1-nu))
    log_single = Q(26492, 1000)
    log_half = Q(26022, 1000)
    assert exp_lower(log_single) > (1-nu)/delta
    assert exp_lower(log_half) > (1-beta)/delta
    e4 = (log_single**2 * 2*e / (nu*(1-nu))
          + log_half**2 * 4*e / (beta*(1-beta)))
    r4 = Q(7,3) * e4
    tail = Q(7,3)*4 * Q(54**255, factorial(255)) / (1-Q(54,256))
    mu = 9 / (50*delta**2*factorial(99))
    low = 1 - Q(23,9)*jp_balanced - Q(7,3)*(jp_short+i2) - r4 - tail - mu
    high = 1 + jp+i2 + r4 + tail + mu
    jmin = Q(27547734178065116588, 10**20)
    jmax = Q(27560294635735393770, 10**20)
    box_low = -jmax
    box_high = Q(7,3)*jmax
    estimates = {
        "Jp_upper": jp, "Jp_balanced_upper": jp_balanced, "Jp_short_upper": jp_short,
        "I2_upper": i2, "E4_upper": e4,
        "R4_absolute_upper": r4, "tail_absolute_upper": tail,
        "calibrated_mean_absolute_upper": mu,
        "whole_plus_T_lower": low, "whole_plus_T_upper": high,
        "J_lower": jmin, "J_upper": jmax, "box_lower": box_low,
        "box_upper": box_high,
        "outside_plus_T_lower": low-box_high, "outside_plus_T_upper": high-box_low,
        "outside_plus_T_plus_primeBox_lower": low+jmin,
        "outside_plus_T_plus_primeBox_upper": high+jmax,
        "original_outside_threshold": Q("0.317014679964"),
    }
    assert low-box_high > Q("0.356873310610")
    assert high-box_low < Q("1.275656062359")
    print(json.dumps({key: dec(value) for key, value in estimates.items()}, indent=2))


if __name__ == "__main__":
    main()
