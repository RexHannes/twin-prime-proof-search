"""Integer exponent checks, including clusters at all three native faces."""
from fractions import Fraction
from itertools import combinations
from random import Random

D = 10**12
eps = D//10**9
nu = D//5-2*eps
beta = D//2-2*eps
gamma = D//2-eps
rho = D//100

def subsets(indices):
    return (s for h in range(len(indices)+1) for s in combinations(indices,h))

def check(values):
    if any(v<=0 for v in values):
        return False
    all_i = list(range(4))
    sums = {s:sum(values[j] for j in s) for s in subsets(all_i)}
    if any(2*v==D for v in sums.values()):
        return False
    excluded = [i for i in all_i if nu<=values[i]<=D//5]
    h=0
    for s,z in sums.items():
        big=[values[i] for i in s if values[i]>=nu]
        if z<=gamma and sum(big)<=beta and all(t>D//5 for t in big):
            h += (-1)**len(s)
    keep=all_i[:]
    total=0
    for i in excluded:
        keep.remove(i)
        v=values[i]
        inc=sum((-1)**len(s) for s in subsets(keep) if sums[s]<D//2-v)
        assert abs(inc)<=2
        for j,u in enumerate(values):
            if j!=i and u<=rho:
                owner=sum(D//2-v-u<=values[k]<D//2-v for k in keep if k!=j)
                assert abs(inc)<=owner
        total+=inc
    no_exc=sum((-1)**len(s) for s in subsets(keep) if sums[s]<D//2)
    assert no_exc==total
    odd_omissions=even_omissions=0
    for s in subsets(keep):
        z=sums[s]
        if z>=D//2:
            continue
        if z<=gamma and sum(values[i] for i in s if values[i]>=nu)<=beta:
            continue
        assert z>beta
        if len(s)%2:
            odd_omissions+=1
        else:
            even_omissions+=1
    assert h==total+odd_omissions-even_omissions
    return True

def main():
    rng=Random(8824108)
    count=0
    for i in range(16000):
        t=rng.choice([nu,D//5,beta,gamma,D//5+2, D//5-4, rng.randrange(D//3)])+rng.choice([-2,-1,0,1,2])
        u=rng.choice([rho,1,2,100,eps,rng.randrange(1,D//3)])
        v=rng.choice([D//2-t,rng.randrange(1,D//3),D//5,nu,beta,gamma,D//2-t-u])+rng.choice([-2,-1,0,1,2])
        exps=[t,u,v,D-t-u-v]
        rng.shuffle(exps)
        count+=check(exps)
    print(f"{count} positive profiles checked away from half-equality")
if __name__=="__main__":
    main()
