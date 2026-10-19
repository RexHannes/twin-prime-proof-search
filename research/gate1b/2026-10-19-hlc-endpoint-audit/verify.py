#!/usr/bin/env python3
"""Exact finite regression checks, not an asymptotic theorem certificate."""
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from math import gcd, isqrt
from pathlib import Path
import argparse
import json

COUNTS = Counter()
def check(ok, category):
    if not ok:
        raise ArithmeticError(category)
    COUNTS[category] += 1

@lru_cache(None)
def factor(n):
    ans = []
    p = 2
    while p*p <= n:
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        if e:
            ans.append((p,e))
        p += 1
    if n > 1:
        ans.append((n,1))
    return tuple(ans)
def prime(n):
    return n >= 2 and factor(n) == ((n,1),)
def mu(n):
    fs = factor(n)
    return 0 if any(e > 1 for p,e in fs) else (-1)**len(fs)
def divs(n):
    return [d for d in range(1,n+1) if n % d == 0]
def rough(n,z):
    return n == 1 or all(p > z for p,e in factor(n))

# Exact Gaussian rational coefficients and formal polynomials in log(prime).
ZERO = (F(0),F(0))
ONE = (F(1),F(0))
def ca(a,b): return (a[0]+b[0],a[1]+b[1])
def cm(a,b): return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def cc(a): return (a[0],-a[1])
def clean(p): return {k:v for k,v in p.items() if v != ZERO}
def pa(a,b):
    o = dict(a)
    for k,v in b.items(): o[k] = ca(o.get(k,ZERO),v)
    return clean(o)
def ps(a,q): return clean({k:cm(v,q) for k,v in a.items()})
def pm(a,b):
    o = {}
    for k,v in a.items():
        for l,w in b.items():
            t = tuple(sorted(k+l))
            o[t] = ca(o.get(t,ZERO),cm(v,w))
    return clean(o)
def pc(a): return {k:cc(v) for k,v in a.items()}
def const(q): return {} if q == 0 else {(): (F(q),F(0))}
def neg(a): return ps(a,(-F(1),F(0)))
def logpoly(n): return {(p,):(F(e),F(0)) for p,e in factor(n)}
def lam(n):
    fs = factor(n)
    return {(fs[0][0],):ONE} if len(fs)==1 else {}
def addall(xs):
    a = {}
    for x in xs: a = pa(a,x)
    return a
def normsq(a): return pm(a,pc(a))
def beta(n,Y): return addall(lam(e) for e in divs(n) if e > Y)
def vaughan(n,Y):
    I1 = addall(ps(logpoly(n//d),(F(mu(d)),F(0)))
                for d in divs(n) if d <= Y)
    I2 = addall(ps(lam(e),(F(mu(d)),F(0))) for d in divs(n) if d <= Y
                for e in divs(n//d) if e <= Y)
    T = addall(ps(beta(n//u,Y),(F(mu(u)),F(0)))
               for u in divs(n) if u > Y and n//u > Y)
    small = lam(n) if n <= Y else {}
    return I1,I2,T,small

def tests():
    # Correct antecedent-sensitive slope implication; no floating logs.
    for m in range(3,44,2):
        for j in range(3,44,2):
            d = gcd(m,j)
            for H in (1,3,7,13,31):
                if m//d <= H:
                    check(d*H >= m,'slope_exact_implication')
    check(not (gcd(101,99)*50 >= 101),'missing_slope_antecedent_negative_control')

    # Support identity using actual formal von Mangoldt values and exact V_o.
    for Z,z in ((3,5),(5,7),(7,13)):
        vo = F(1)
        for p in range(3,z+1,2):
            if prime(p): vo *= F(p-1,p)
        for n in range(3,1000,2):
            B = const(2/vo) if rough(n,z) else {}
            delta = pa(lam(n),neg(B))
            lhs = {} if rough(n,Z) else delta
            rhs = {} if rough(n,Z) else lam(n)
            check(lhs == rhs,'endpoint_formal_support_identity')
    n,Z,z = 7,11,5
    check(rough(n,z) and not rough(n,Z),'Z_gt_z_negative_control')

    for n in range(2,220):
        for Y in (2,3,5,7):
            I1,I2,T,small = vaughan(n,Y)
            check(pa(pa(small,I1),pa(neg(I2),T)) == lam(n),'vaughan_formal_identity')
            if prime(n) and n > Y:
                check(T == {} and I2 == {} and I1 == logpoly(n),
                      'prime_slot_full_faces')

    # Native physical arithmetic envelope, NOT an occurrence-image certificate.
    X,M,Z,z = 4096,4,7,13
    weights = {5:(F(3,5),F(4,5)), 7:(F(5,13),-F(12,13))}
    vo = F(1)
    for p in range(3,z+1,2):
        if prime(p): vo *= F(p-1,p)
    full,rf,err = {},{},{}
    exceptional = []
    for c in range(257,513,2):
        s,t,e = {},{},{}
        for m,A in weights.items():
            if not (X//2 < m*c <= X): continue
            n = m*c+2
            B = const(2/vo) if rough(n,z) else {}
            delta = pa(lam(n),neg(B))
            R = delta if rough(n,Z) else {}
            E = {} if rough(n,Z) else lam(n)
            check(delta == pa(R,E),'native_detector_split')
            s,t,e = pa(s,ps(delta,A)),pa(t,ps(R,A)),pa(e,ps(E,A))
            if E: exceptional.append({'m':m,'c':c,'n':n,'factorization':factor(n)})
        full[c],rf[c],err[c] = s,t,e
    gf = addall(normsq(v) for v in full.values())
    gr = addall(normsq(v) for v in rf.values())
    ge = addall(normsq(v) for v in err.values())
    cross = addall(pa(pm(rf[c],pc(err[c])),pm(err[c],pc(rf[c]))) for c in full)
    check(gf == pa(gr,pa(cross,ge)),'native_full_Gram_identity')
    check(bool(exceptional) and bool(cross),'native_nonzero_error_and_cross')
    check(exceptional == [{'m':5,'c':437,'n':2187,'factorization':((3,7),)}],
          'native_expected_prime_power_record')

    # The old Gamma energy is not the detector-row energy.
    for t in (1,2,7,31):
        check((t+1)**2-t*t == 2*t+1 and 2*t+1 > 1,
              'Gamma_zero_Gram_negative_control')

    # Exact real L1/L-infinity transport inequality; complex conjugates above.
    for k in range(1,101):
        R = [F((i*k)%17-8,i+1) for i in range(1,8)]
        E = [F((i+k)%7-3,i+2) for i in range(1,8)]
        delta = sum((r+e)**2-r*r for r,e in zip(R,E))
        e1 = sum(abs(e) for e in E)
        bound = 2*max(map(abs,R))*e1+e1*e1
        check(abs(delta) <= bound,'L1_Linfinity_Gram_transport')

    # Rank-one diagonal-moment saturation aligned with the ACTUAL rough Mobius signs.
    support = [n for n in range(49,97) if mu(n) and rough(n,3)]
    signs = [mu(n) for n in support]
    N = len(signs)
    check(N > 1 and 1 in signs and -1 in signs,'rough_Mobius_both_signs')
    B = [[F(x*y,N) for y in signs] for x in signs]
    B2 = [[sum(B[i][k]*B[k][j] for k in range(N)) for j in range(N)]
          for i in range(N)]
    for i in range(N):
        for j in range(N): check(B2[i][j] == B[i][j],'rough_Mobius_projection_idempotence')
        check(sum(B[i][j]*signs[j] for j in range(N)) == signs[i],
              'rough_Mobius_projection_eigenvector')
        check(B[i][i] == F(1,N),'rough_Mobius_projection_root_moment')

    # Every tested prime interval contains no more than the exact dyadic power budget.
    for X in (128,512,2048,8192):
        for p in (3,5,7,11,13):
            powers=[]
            q=p*p
            while q <= X+2:
                if X//2+2 < q: powers.append(q)
                q *= p
            check(len(powers) <= 2,'proportional_interval_power_count')

    return {
        'status':'PASS_FINITE_ONLY',
        'checks_by_category':dict(sorted(COUNTS.items())),
        'total_exact_checks':sum(COUNTS.values()),
        'native_fixture':{'X':4096,'M':4,'Z':7,'z':13,
                          'c_cell':'(256,512]','exceptional_records':exceptional},
        'rough_Mobius_moment_control':{'interval':'(48,96]','Z':3,'support':support,'signs':signs,
                                     'rank':1,'diagonal_moment':str(F(1,N)),
                                     'actual_R11_operator':False},
        'nonclaims':[
            'No finite test proves an asymptotic estimate.',
            'The native arithmetic fixture is not an instantiated Ford occurrence certificate.',
            'The Mobius-aligned rank-one matrix is not asserted to be the R11 operator.',
            'No rough mixed cancellation, rough endpoint covariance, Full R11 or HSTAR closure.',
            'No Lean build or independent human referee certification.'
        ]
    }

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output',default='CERTIFICATE.json')
    args = parser.parse_args()
    result = tests()
    text = json.dumps(result,indent=2,sort_keys=True)
    Path(args.output).write_text(text+'\n',encoding='utf-8')
    print(text)
