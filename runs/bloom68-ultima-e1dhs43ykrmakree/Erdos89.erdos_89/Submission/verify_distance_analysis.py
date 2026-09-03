#!/usr/bin/env python3
"""Exact checks accompanying the distance-matrix investigation (not a proof of
Erdos's conjecture or of the proposed amplification). No Lean files are changed.
"""
from collections import Counter
from fractions import Fraction as F
from math import comb
import random
import sympy as sp

# Exact arithmetic in Q(sqrt(3)); a pair (a,b) denotes a+b sqrt(3).
def q(a=0, b=0): return (F(a), F(b))
def add(x, y): return (x[0]+y[0], x[1]+y[1])
def neg(x): return (-x[0], -x[1])
def sub(x, y): return add(x, neg(y))
def mul(x, y): return (x[0]*y[0]+3*x[1]*y[1], x[0]*y[1]+x[1]*y[0])
def scale(a, x): return mul(q(a), x)
def total(xs):
    out = q()
    for x in xs: out = add(out, x)
    return out

def norm2(p): return add(mul(p[0], p[0]), mul(p[1], p[1]))
def squared_distance(p, v): return norm2((sub(p[0], v[0]), sub(p[1], v[1])))

def triangle(radius, t):
    c = (1-t*t)/(1+t*t)
    s = 2*t/(1+t*t)
    return [
        (q(radius*c), q(radius*s)),
        (q(-radius*c/2, -radius*s/2), q(-radius*s/2, radius*c/2)),
        (q(-radius*c/2, radius*s/2), q(-radius*s/2, -radius*c/2)),
    ]

def statistics(points):
    assert len(set(points)) == len(points)
    counts = Counter()
    for i, p in enumerate(points):
        for v in points[:i]: counts[squared_distance(p, v)] += 2
    n = len(points)
    assert q() not in counts
    assert sum(counts.values()) == n*(n-1)
    return len(counts), sum(r*r for r in counts.values())

def check_moments(points):
    n = len(points)
    qs = [norm2(p) for p in points]
    S = total(qs)
    T = total(mul(z,z) for z in qs)
    assert total(p[0] for p in points) == q()
    assert total(p[1] for p in points) == q()
    assert total(mul(z,p[0]) for z,p in zip(qs,points)) == q()
    assert total(mul(z,p[1]) for z,p in zip(qs,points)) == q()
    assert total(mul(p[0],p[0]) for p in points) == scale(F(1,2), S)
    assert total(mul(p[1],p[1]) for p in points) == scale(F(1,2), S)
    assert total(mul(p[0],p[1]) for p in points) == q()
    # These identities prove the spectral formula algebraically.
    assert S == q(F(5*n,2))
    assert T == q(F(17*n,2))

rng = random.Random(83457)
for m in (1,2,3,4,8,12):
    points=[]
    for j in range(2*m):
        t=F(rng.randrange(1,10**7), rng.randrange(1,10**7))
        points += triangle(F(1 if j<m else 2), t)
    n=len(points)
    check_moments(points)
    D,E=statistics(points)
    assert D == 2+3*m*(2*m-1), (m,D)
    assert E == 8*n*n-18*n, (m,E)
    print(f'Exact generic two-ring check: n={n}, D={D}, E={E}')

hexagon=[(q(1),q()),(q(F(1,2)),q(0,F(1,2))),
         (q(F(-1,2)),q(0,F(1,2))), (q(-1),q()),
         (q(F(-1,2)),q(0,F(-1,2))), (q(F(1,2)),q(0,F(-1,2)))]
structured=hexagon+[(scale(2,x),scale(2,y)) for x,y in hexagon]
check_moments(structured)
print('Exact aligned two-ring check:', 'n=12, (D,E)=', statistics(structured))

# Check the exact small-t sign obstruction on the square.
u,t=sp.symbols('u t')
K=sp.Matrix([[1,u,u,u**2],[u,1,u**2,u],
             [u,u**2,1,u],[u**2,u,u,1]])
v=sp.Matrix([1,-1,-1,1])
assert sp.factor(K.det()-(1-u*u)**4)==0
assert sp.expand((v.T*K*v)[0]-4*(1-u)**2)==0
series=sp.series((v.T*K*v)[0].subs(u,sp.exp(-t)),t,0,4)
assert series.removeO()==4*t*t-4*t**3
print('Square determinant and negative higher Taylor coefficient verified.')

# Check the conditional Schur-power moment identity exactly on a 3x3 grid.
P=[(x,y) for x in range(3) for y in range(3)]
z=[sp.Integer(x)+sp.I*y for x,y in P]
R=sp.Matrix([[(x-a)**2+(y-b)**2 for a,b in P] for x,y in P])
for k in (1,2,3):
    moments=sp.Matrix([[x**a*y**b for x,y in P]
                       for a in range(k) for b in range(k-a)])
    null=moments.nullspace()
    checks=null[:]
    if null: checks.append(sum((j*w for j,w in enumerate(null,1)),sp.zeros(len(P),1)))
    for w in checks:
        lhs=(-1)**k*(w.T*R.applyfunc(lambda s:s**k)*w)[0]
        rhs=0
        for a in range(k+1):
            moment=sum(w[i]*z[i]**a*sp.conjugate(z[i])**(k-a) for i in range(len(P)))
            rhs += comb(k,a)**2*sp.expand(moment*sp.conjugate(moment))
        assert sp.simplify(lhs-rhs)==0
print('Conditional Schur-power identities verified exactly for k=1,2,3.')

# Spot-check the proved support-weighted polynomial inequality using integers.
for _ in range(50):
    P=rng.sample([(x,y) for x in range(-4,5) for y in range(-4,5)],rng.randrange(2,20))
    n=len(P)
    c=Counter()
    for i,(x,y) in enumerate(P):
        for a,b in P[:i]: c[(x-a)**2+(y-b)**2]+=2
    for k in range(5):
        coefficients=[rng.randrange(-3,4) for _ in range(k+1)]
        def f(s): return sum(a*s**j for j,a in enumerate(coefficients))
        frob=n*f(0)**2+sum(r*f(s)**2 for s,r in c.items())
        assert n*n*f(0)**2 <= comb(k+2,2)*frob
print('Support-weighted polynomial inequality: all exact spot checks passed.')
