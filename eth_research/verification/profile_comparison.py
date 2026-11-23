"""Finite exact checks for the signed complete-upper comparison."""
from decimal import Decimal, getcontext
from fractions import Fraction as F
from itertools import combinations
from math import factorial, prod
import json


def check():
    eps = F(1, 10**9)
    centre = (103, 107, 150, 281, 359)
    subset_sums = [(r, sum(a)) for r in range(6) for a in combinations(centre, r)]
    assert min(abs(t - 500) for r, t in subset_sums) == 9
    assert sum((-1)**r for r, t in subset_sums if t < 500) == 2
    extra = 2 * 5**5 * F(2, 1000)**4
    assert extra == F(1, 10**7)
    # Gold 4.62 outside chamber, using coordinates (t1,t2,t3,t1+t3+t4).
    widths = [F(2, 100), F(3, 100), F(3, 100), F(6, 1000)]
    maxcoords = [F(11, 100), F(15, 100), F(19, 100), F(258, 1000), F(378, 1000)]
    old = 2 * prod(widths) / prod(maxcoords)
    assert old == F(400, 566181)
    improvement = (F('3.4002754') - F(10, 3)) * (old + extra)
    assert improvement > F('0.0000473004')
    # Explicit conservative negative triangle bound. pi > 3.14.
    a = F(1, 10**5)
    neg = F('3.14')**2 / 6 - 160*a
    assert neg > F('1.64') and a > 2 * eps
    first_tail = (1 + F(256**3, 64**3)) * 2**256 * F(27**255, factorial(255))
    ratio = F(257, 256)**3 * F(54, 256)
    assert ratio < F('.214') and F(7, 3) * first_tail / (1-ratio) < F('6.7e-61')
    getcontext().prec = 34
    return dict(Pi_positive_lower=str(old + extra), named_certificate_saving=str(improvement),
                named_certificate_saving_decimal=str(Decimal(improvement.numerator)/Decimal(improvement.denominator)),
                Pi_negative_lower=str(neg), tail_upper='6.7e-61')


if __name__ == '__main__':
    print(json.dumps(check(), indent=2))
