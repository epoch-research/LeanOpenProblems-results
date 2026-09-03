#!/usr/bin/env python3
"""Finite algebra/counting checks for the auxiliary FourthEnergyGap.md.
Not a proof of Erdős 241 or a numerical asymptotic experiment.
"""
from collections import Counter
from itertools import combinations, combinations_with_replacement, product
from math import comb, factorial
from fractions import Fraction
import json


def audit(A):
    A = tuple(sorted(A))
    n = len(A)
    triples = list(combinations_with_replacement(A, 3))
    assert len({sum(t) for t in triples}) == len(triples), 'not strong B3'
    e3dist = Counter(sum(t) for t in product(A, repeat=3))
    E3 = sum(v*v for v in e3dist.values())
    assert E3 == 6*n**3-9*n*n+4*n
    e4dist = Counter(sum(t) for t in product(A, repeat=4))
    E4 = sum(v*v for v in e4dist.values())
    pairs = list(combinations(A, 2))
    m = Counter(sum(P)-sum(Q) for P in pairs for Q in pairs if not set(P)&set(Q))
    assert sum(m.values()) == 6*comb(n,4)
    assert all(2*v <= n for v in m.values())
    assert 0 <= E4-16*sum(v*v for v in m.values()) <= 168*n**4
    phi = lambda r: sum(A[n-1-i]-A[i] for i in range(r))
    for t,v in m.items():
        assert v*abs(t) <= phi(min(2*v,n-2*v))
        assert v*(2*(A[-1]-A[0])+abs(t)) <= n*(A[-1]-A[0])
    collisions = []
    quads = list(combinations(A, 4))
    for i,C in enumerate(quads):
        for D in quads[:i]:
            if not set(C)&set(D) and sum(C)==sum(D):
                collisions.append((C,D))
    flags = {}
    for B in combinations(A, 5):
        outside = set(A)-set(B)
        for P in combinations(B,2):
            value = sum(B)-2*sum(P)
            reps = [(x,y,z) for x,y in combinations(sorted(outside),2)
                    for z in outside-{x,y} if x+y-z == value]
            assert len(reps)<=1
            if reps:
                flags[(B,P)] = reps[0]
    assert len(flags) == 48*len(collisions)
    assert 24*len(flags) == 2*factorial(4)**2*len(collisions)
    for C,D in collisions:
        collision_flags=[]
        for X,Y in ((C,D),(D,C)):
            for P in combinations(Y,2):
                for T in combinations(X,3):
                    collision_flags.append((tuple(sorted(T+P)),P))
        assert len(collision_flags)==48
        for u,v in combinations(C+D,2):
            count=sum(u in B and v in B for B,_ in collision_flags)
            assert count == (16 if ((u in C)==(v in C)) else 18)
    assert E4 <= (Fraction(2)-Fraction(1,2552))*n**5+169*n**4
    return {'A': A, 'n':n, 'E3':E3, 'E4':E4,
            'eight_distinct_unordered_collisions':len(collisions),
            'five_set_flags':len(flags)}


if __name__ == '__main__':
    # This forced relation is four-versus-four, not a searched counterexample.
    base = [10**i for i in range(7)]
    last = sum(base[:4])-sum(base[4:])
    forced = base+[last]
    assert sum(base[:4]) == sum(base[4:])+last
    examples = [audit([0,1,4]), audit(forced)]
    # Exact rounding identity at rational sample values, independent of n's scale.
    for n in range(176,1000):
        k=n//176
        r=Fraction(n,176)-k
        delta=Fraction(n-88*k,58)
        assert 8*k*delta*n**3 == Fraction(n**5,2552)-Fraction(352,29)*r*r*n**3
        if n>=352:
            x=Fraction(k,n)
            assert Fraction(1,352)<=x<=Fraction(1,176)
            assert 2*(1-x)**5+240*x*x <= 2-10*x+260*x*x <= 2-8*x <= 2-Fraction(1,44)
    print(json.dumps({'status':'PASS', 'scope':'auxiliary finite identities only',
                      'examples':examples},indent=2))
