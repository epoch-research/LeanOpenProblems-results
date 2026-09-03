#!/usr/bin/env python3
"""Exact auxiliary checks for CriticalScaleCheckpoint.md; not a target proof."""
import sympy as s
from fractions import Fraction as F

x,p,n,N=s.symbols('x p n N',positive=True)
g0=s.Rational(2,3)-x*x+x**3/2
g1=(2-x)**3/6
mass=2*(s.integrate(g0,(x,0,1))+s.integrate(g1,(x,1,2)))
energy=2*(s.integrate(g0*g0,(x,0,1))+s.integrate(g1*g1,(x,1,2)))
assert mass==1 and energy==s.Rational(151,315)
diff=2-x-2*g0
assert s.expand(s.diff(diff,x)-(1-x)*(3*x-1))==0
assert diff.subs(x,s.Rational(1,3))==s.Rational(14,27)
beta=n*s.exp(-p)/2
b=2*N*(s.exp(p)-1)
Q=2*n*N*p
I1=2*n*N*s.log((2*N+b)/(2*N))
I2=n*n*N-2*n*n*N*N/(2*N+b)
assert s.simplify(I1-Q)==0
assert s.simplify(I2-(n*n*N-2*n*N*beta))==0
assert s.simplify(beta*Q+I2-beta*I1-n*n*N*(1-s.exp(-p)))==0
S5=sum(F(-1,8)**j/F(int(s.factorial(j))) for j in range(6))
assert 16*(1-S5)<F(37601,20000)
# This arithmetic checks only the implication from the quoted Fourier norm.
# It does not recertify the published numerical kernel norm itself.
assert F(9658413,10**7)**(-4)>F(22983,20000)

def g(t):
    t=abs(t)
    return F(2,3)-t*t+t**3/2 if t<=1 else (2-t)**3/6 if t<=2 else F(0)

for L in range(1,21):
    vals=[g(F(t,L))/L for t in range(-2*L,2*L+1)]
    assert sum(vals)==1 and max(vals)==F(2,3*L)
print('PASS: exact profile mass1, squared integral151/315, cap minimum14/27')
print('PASS: symbolic aggregate integral/cancellation identity')
print('PASS: rational Taylor bound16(1-exp(-1/8))<1.880050')
print('PASS: arithmetic implication of the published kernel-norm estimate')
print('PASS: exact integer-periodized smoothing kernels L=1..20')
print('Scope: auxiliary identities only; no strong-B3 fixed-excess family.')

# The threefold uniform convolution has maximum3/4, attained at3/2.
h3=-x*x+3*x-s.Rational(3,2)
assert s.expand(h3-(s.Rational(3,4)-(x-s.Rational(3,2))**2))==0
assert h3.subs(x,s.Rational(3,2))==s.Rational(3,4)
# Interval-core scaling: core cubic ratio is2*ell^2, not2/ell.
ell,v=s.symbols('ell v',positive=True)
gv=s.Rational(2,3)-v*v+v**3/2
assert s.expand(ell**3*gv/2-ell**2*(ell*gv/2))==0
print('PASS: triple-convolution maximum3/4 and exact interval-core scaling')
