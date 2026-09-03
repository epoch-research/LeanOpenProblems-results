"""Exact audit of the balanced-relation fourth-order star calculation.
No Ramsey theorem is assumed. All reported finite checks use rational arithmetic.
"""
from fractions import Fraction as F
from itertools import product
from math import comb, factorial
import sympy as sp


def conditional(q, hub, incident):
    # E[(B-p)/(1-p) | shared types]; t-1 shared pair variables.
    t = len(incident) + 1
    u, v = 1-q, 1-2*q
    vals = (hub,) + tuple(incident)
    a = all(x != 0 for x in vals)  # no A
    b = all(x != 1 for x in vals)  # no S
    o = all(x == 2 for x in vals)  # all ordinary
    return 1 - F(a+b, 1)/u**(t-1) + F(o, 1)/v**(t-1)


def direct(q, t):
    pairs = [(i,j) for i in range(t) for j in range(i+1,t)]
    probs = [q, q, 1-2*q]
    total = F(0)
    for vals in product(range(3), repeat=1+len(pairs)):
        hub, es = vals[0], vals[1:]
        wt = probs[hub]
        for z in es:
            wt *= probs[z]
        value = F(1)
        for i in range(t):
            inc = [es[k] for k, pair in enumerate(pairs) if i in pair]
            value *= conditional(q, hub, inc)
        total += wt * value
    return total


def ma(q,t):
    return sum((-1)**r * comb(t,r) * (1-q)**(-comb(r,2))
               for r in range(t+1))


def mo(q,t):
    u, v = 1-q, 1-2*q
    out=0
    for a in range(t+1):
      for b in range(t-a+1):
        for c in range(t-a-b+1):
          z=t-a-b-c
          mult=factorial(t)//(factorial(a)*factorial(b)*factorial(c)*factorial(z))
          ue=(1-t)*(a+b)+comb(a,2)+comb(b,2)+z*(a+b)
          ve=(1-t)*c+comb(c,2)+c*(t-c)+a*b
          out += mult*(-1)**(a+b)*u**ue*v**ve
    return out


def formula(q,t):
    return 2*q*ma(q,t)+(1-2*q)*mo(q,t)


def source_check(d):
    root=1
    near=[root ^ (1<<i) for i in range(d)]
    from itertools import combinations
    stars=set()
    for x in near:
        centers=[x ^ (1<<i) for i in range(d)]
        others=[y for y in centers if y != root]
        for rest in combinations(others,3):
            S=tuple(sorted((root,)+rest))
            assert S not in stars
            stars.add(S)
            union=set()
            common=None
            for y in S:
                e={y ^ (1<<i) for i in range(d)}
                union |= e
                common = e if common is None else common & e
            assert common == {x}
            assert len(union)==4*d-9
    assert len(stars)==d*comb(d-1,3)
    return len(stars)


def run():
    print('Balanced-relation star audit (exact rational arithmetic)')
    nbal=0
    for K in [16,32,64]:
      for d in [8,16,32,64,128]:
        q=F(1,K*d); u=1-q; v=1-2*q
        p=1-u**(d-1); w=(u/v)**(d-1)-1
        assert 0<p<F(1,K)
        assert 0<w<=F(1,K-1)<1
        assert 1-2*u**(d-1)+v**(d-1)+w*v**(d-1)==p
        L=(K*d-2)**(d-1)
        r=(K*d-1)**(d-1)-L
        assert w==F(r,L)
        assert 0<r<L-d
        nbal += 1
    print(f'PASS: {nbal} exact balance, zero-one lift, and avoiding-injection tag checks.')
    n=0
    for q in [F(1,128),F(1,256),F(1,512),F(1,1024)]:
      for t in [2,3,4]:
        assert direct(q,t)==formula(q,t)
        n += 1
      M2=formula(q,2)
      assert M2==2*q*q/(1-q)**2
      M4=formula(q,4)
      kappa=M4-3*M2*M2
      assert kappa>=5*q**3
    print(f'PASS: {n} shared-variable enumeration/closed-form identities (including 2187 assignments per four-star).')
    q=sp.symbols('q'); u=1-q; v=1-2*q
    M2=sp.factor(formula(q,2)); M4=sp.factor(formula(q,4))
    assert sp.cancel(M2-2*q*q/u**2)==0
    assert sp.limit(ma(q,4)/q**2,q,0)==3
    assert sp.limit(mo(q,4)/q**3,q,0)==0
    C=sp.factor(M4-3*M2**2)
    assert sp.limit(M4/q**3,q,0)==6
    assert sp.limit(C/q**3,q,0)==6
    P=sp.Poly(sp.cancel(C*u**10*v**5/(2*q**3)),q)
    assert P.degree()==12 and P.eval(0)==3
    negative = sum(F(int(coeff),128**power[0]) for power,coeff in P.terms() if coeff<0)
    assert F(3)+negative>F(5,2)
    print('PASS: exact polynomial identities: M2=2q^2/(1-q)^2, M4=6q^3+O(q^4), kappa4=6q^3+O(q^4).')
    print('PASS: all-dimensional bound kappa4>=5q^3 for 0<q<=1/128, by negative-coefficient bound.')
    total=sum(source_check(d) for d in range(5,10))
    print(f'PASS: {total} rooted source four-stars; unique hub and union size 4d-9.')
    print('Exact normalized rooted cumulant load divided by d (decimal display only):')
    K=16
    for d in [8,16,32,64,128,256]:
        z=F(1,K*d)
        load=d*comb(d-1,3)*(formula(z,4)-3*formula(z,2)**2)
        assert load>=d*comb(d-1,3)*5*z**3
        print(f'  d={d:3}: {float(load/d):.9f}; limit 1/16^3={1/16**3:.9f}')
    print('Injective-transfer bound used in paper: |E_inj F-E_iid F| <= r(r-1)/N for |F|<=1.')
    print('This is NOT a Ramsey proof, a countercolouring, or a disproof of balanced packing.')

if __name__=='__main__':
    run()
