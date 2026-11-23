"""Exact finite counterexample search for the four-factor envelope and ledger arithmetic."""
from decimal import Decimal, getcontext
from fractions import Fraction as F
from itertools import combinations
from math import comb, factorial
from random import Random
import json

S = 10**12
e = S//10**9
nu = S//5 - 2*e
beta = S//2 - 2*e
gamma = S//2 - e
subsets = [tuple(p) for j in range(5) for p in combinations(range(4),j)]


def check_profile(t):
    assert all(x > 0 for x in t) and sum(t) == S
    kernel = 0
    faces = 0
    ideal = 0
    exact_half = False
    for a in subsets:
        s = sum(t[i] for i in a)
        macro = [t[i] for i in a if t[i] >= nu]
        if s < S//2:
            ideal += (-1)**len(a)
        if s == S//2:
            exact_half = True
        if beta < s < S//2:
            faces += 1
        if s > gamma or sum(macro) > beta:
            continue
        g = (1 if not macro else -1 if len(macro)==1 and S//5<macro[0]<=S//2
             else 1 if len(macro)==2 and all(y>S//5 for y in macro) and sum(macro)<S//2 else 0)
        kernel += (-1)**(len(a)-len(macro))*g
    if exact_half:
        return None
    assert ideal == 0
    rhs = 2*sum(nu<=x<=S//5 for x in t)+faces
    assert abs(kernel) <= rhs, (t,kernel,rhs)
    return (kernel, rhs)


def split(total, count, rng):
    cuts = [0] + sorted(rng.sample(range(1,total),count-1)) + [total]
    return [b-a for a,b in zip(cuts,cuts[1:])]


def search():
    rng=Random(86711)
    checks = 0
    skipped_half = 0
    nonzero = 0
    max_abs=0
    for j in [0,1,2,3,4]:
        for _ in range(9000):
            if j==0:
                t=split(S,4,rng)
            elif j==4:
                bad=S//5+rng.randint(-2*e-3,3)
                t=[bad]+split(S-bad,3,rng)
            else:
                subtotal=S//2+rng.randint(-2*e-3,3)
                t=split(subtotal,j,rng)+split(S-subtotal,4-j,rng)
            p=check_profile(t)
            if p is None:
                skipped_half+=1
            else:
                checks+=1
                nonzero+=int(p[0]!=0)
                max_abs=max(max_abs,abs(p[0]))
    return checks, skipped_half, nonzero, max_abs


def rounded_text(t):
    return str(Decimal(t.numerator)/Decimal(t.denominator))


def main():
    getcontext().prec=48
    checks, skipped, nonzero, max_abs=search()
    epsilon=F(e,S); N=F(nu,S); B=F(beta,S); a=F(1,5)-epsilon
    jcap=(epsilon/(a*(1-a))+2*epsilon/(B*(1-B))+epsilon**2/(2*a*a*F(3,5))
          +3*(5*epsilon)**4/(factorial(5)*factorial(4)*a**5))
    pair=epsilon/(N*(1-N))
    tail=F(1,10**58)
    calibrated=9*F(400000000000)**2/(50*factorial(99))
    env=27**2*(2*epsilon/(N*(1-N))+4*epsilon/(B*(1-B)))
    tail_analytic = F(41,9)*4*F(54**255,factorial(255))/(1-F(54,256))
    assert tail_analytic < 4*F(1,10**62)
    signed=F(23,9)*env
    lower=1-F(23,9)*(jcap+pair)-signed-tail-calibrated
    old=1-3*(jcap+pair)-F('0.000107163')-tail-calibrated
    outside=lower-F('0.682878095535')
    assert sum(comb(4,j)*j*(4-j) for j in range(1,4)) == 48
    assert signed < F('0.000053095501')
    assert lower > F('0.999946852110') and outside > F('0.317068756575')
    print(json.dumps({'commit':'43facedcf40b2f998aa47f7198d6b9b5feb5b792',
                      'pointwise_checks':checks,'samples_with_nonzero_kernel':nonzero,'largest_kernel_abs_sampled':max_abs,
                      'excluded_exact_half_unphysical_samples':skipped,
                      'high_rank_tail_cap':rounded_text(tail_analytic), 'E4':rounded_text(env), 'four_debit':rounded_text(signed),
                      'conditional_old_lower':rounded_text(old),'conditional_new_lower':rounded_text(lower),
                      'conditional_gain':rounded_text(lower-old),'conditional_outside_threshold':rounded_text(outside),
                      'actual_bound_on_outside':None},indent=2))


if __name__ == '__main__':
    main()
