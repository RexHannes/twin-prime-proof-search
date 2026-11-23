"""Rational arithmetic for signed_rank_four.md, including every baseline debit."""
from decimal import Decimal, localcontext
from fractions import Fraction as Q
from math import comb, factorial

def decimal(x):
    with localcontext() as ctx:
        ctx.prec = 50
        return Decimal(x.numerator)/Decimal(x.denominator)

def certificate(j_upper=Q("0.27560294635735393770")):
    eps = Q(1, 10**9)
    delta = eps/400
    lower = Q(1,5) - eps
    nu = lower - eps
    beta = Q(1,2) - 2*eps
    rho = Q(1,100)
    lam = Q(7,3)
    c1 = Q("26.492")
    c2 = Q("26.022")
    c3 = Q("4.606")
    for c,m in [(c1,(1-nu)/delta),(c2,(1-beta)/delta),(c3,1/rho)]:
        assert sum(c**i/factorial(i) for i in range(131)) > m
    odd = sum(Q(comb(4,h)*h*(4-h),24) for h in (1,3))
    even = Q(comb(4,2)*2*2,24)
    assert odd == even == 1
    exceptional_old = 2*eps*c1**2/(nu*(1-nu))
    half = 4*eps*c2**2/(beta*(1-beta))
    exceptional_big = 2*eps*c3**2/(nu*(1-nu))
    exceptional_tiny = 2*eps*rho/(nu*Q(".29")*Q(".49"))
    old = lam*(exceptional_old+half)
    signed_only = lam*exceptional_old+(lam+1)*half/2
    both = lam*(exceptional_big+exceptional_tiny)+(lam+1)*half/2
    balanced = 2*eps/(beta*(1-beta))
    short = (eps/(lower*(1-lower)) + eps**2/(2*lower**2*Q(3,5))
             + 3*(5*eps)**4/(factorial(5)*factorial(4)*lower**5))
    i2 = eps/(nu*(1-nu))
    tail = lam*4*Q(54**255,factorial(255))/(1-Q(54,256))
    calibration = 9/(50*delta**2*factorial(99))
    low = 1-Q(23,9)*balanced-lam*(short+i2)-both-tail-calibration
    high = 1+balanced+short+i2+both+tail+calibration
    assert old > signed_only > both
    return dict(old=old, signed_only=signed_only, both=both, gain=old-both,
                whole_low=low, whole_high=high, outside_plus_T_lower=low-lam*j_upper,
                outside_upper=high+j_upper)
if __name__ == "__main__":
    for k,q in certificate().items():
        print(k,decimal(q))
