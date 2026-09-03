#!/usr/bin/env python3
"""Exact checks for ExactPureSReport.md; no numerical Diophantine search.

The four LP vertices were selected separately using floating-point linear
programming with rational objectives and no value of S. This verifier uses
only Z/Q and checks both polynomial positivity and exact dual optimality.
The proofs of infinite positivity and the parametric obstructions are in
the accompanying report, not inferred from finitely many tests here.
"""
from fractions import Fraction as F
from math import factorial, gcd, prod
from pathlib import Path
import hashlib
import json
import sympy as sp

HERE = Path(__file__).resolve().parent
SPEC_HASH = 'c5c794ec0dcb35e079f78ce20043053fe0bf048aa47873395df7221ce5aea20d'
x, z, X, T, t = sp.symbols('x z X T t')


def v2(n):
    assert n > 0
    e = 0
    while n % 2 == 0:
        n //= 2
        e += 1
    return e


def coefficient_rows(N):
    """Return a[r][j]=[y^j] C_r(y), r,j>=1, via positive Q recurrence."""
    Q = [[1] + [0]*(j-1) for j in range(1,N+1)]
    rows = [[0]*(N+1)]
    for r in range(1,N+1):
        row = [0]
        for j in range(1,N+1):
            a = Q[j-1][-1]
            row.append(a)
            low = Q[j-1][:-1] + [0]
            new = [r*low[k] + (low[k-1] if k else 0) for k in range(j)]
            new[0] += a
            assert all(c >= 0 for c in new)
            Q[j-1] = new
        rows.append(row)
    return rows


ROWS = coefficient_rows(80)


def raw_P(r,j):
    """P_j with c=1, in z=x+1."""
    return sp.Poly(sp.rf(z,r) + sum(
        ROWS[k][j]*sp.rf(z+k,r-k) for k in range(1,r+1)), z)


def Q_polynomial(r,j):
    Q = sp.Poly(1,z)
    for k in range(1,r+1):
        a = Q.nth(j-1)
        assert a == ROWS[k][j]
        Q = sp.Poly(z+k,z)*(Q-sp.Poly(a*z**(j-1),z)) + sp.Poly(a,z)
        assert all(c >= 0 for c in Q.all_coeffs())
    return Q


def cone_data(r,M,a):
    """N(X+2,T+a), columns for P_j=sum_k b[j,k]*(x-2)^k."""
    A = sp.Poly(sp.rf(X+3,r),X)
    H = sp.Poly((X+r+3)*(X+3)**(M-1),X)
    nx, nt = r+M+1, M+1
    constant = sp.zeros(nx*nt,1)
    B = sp.zeros(nx*nt,M*(r+1))
    def fill(col,px,pt):
        for (ix,),cx in px.terms():
            for (it,),ct in pt.terms():
                col[ix*nt+it] = cx*ct
    fill(constant,A*H,sp.Poly((T+a)**M,T))
    for j in range(1,M+1):
        for k in range(r+1):
            px = sp.Poly((X+1)**k*(X+3)**(M-j),X)-H*sp.Poly(X**k,X)
            pt = sp.Poly((T+a-1)*(T+a)**(M-j),T)
            col = sp.zeros(nx*nt,1)
            fill(col,px,pt)
            B[:,(j-1)*(r+1)+k] = col
    objective = sp.zeros(M*(r+1),1)
    for j in range(1,M+1):
        objective[(j-1)*(r+1)] = 2**(M-j)
    return constant, B, objective


def S_interval(N):
    lo = sum((F(1,factorial(n)-1) for n in range(2,N+1)), F(0))
    # a_(n+1)/a_n < 1/(n+1), a_n=1/(n!-1).
    hi = lo + F(N+2,(N+1)*(factorial(N+1)-1))
    return lo, hi


def check_algebra():
    count=0
    for r in range(3):
        for M in range(1,4):
            A=sp.rf(x+1,r)
            H=(x+r+1)*(x+1)**(M-1)
            P=sum((j+1)*sum((k+1)*x**k for k in range(r+1))*t**(M-j)
                  for j in range(1,M+1))
            U=P/(A*t**M)
            shifted=U.subs({x:x+1,t:(x+1)*t},simultaneous=True)
            N=A*H*t**M+(t-1)*(P.subs({x:x+1,t:(x+1)*t},simultaneous=True)-H*P)
            assert sp.cancel(1/(t-1)+shifted-U-N/(A*H*t**M*(t-1)))==0
            D=2**(M-1)*factorial(r+2)
            assert sp.cancel(D*U.subs({x:2,t:2})-P.subs({x:2,t:2}))==0
            for n in range(2,8):
                d=factorial(n+r)*factorial(n)**(M-1)
                assert sp.cancel(U.subs({x:n,t:factorial(n)})-P.subs({x:n,t:factorial(n)})/d)==0
            count+=1
    print('algebra, boundary, orbit denominators:',count,'symbolic parameter pairs')


def check_matching_and_positivity():
    count=0
    for r in range(8):
        A=sp.Poly(sp.rf(z,r),z)
        for j in range(1,9):
            P=raw_P(r,j)
            quotient=sum((sp.div(A,sp.Poly(sp.rf(z,k)**j,z))[0]
                          for k in range(r//j+1)),sp.Poly(0,z))
            assert P==quotient
            Q=Q_polynomial(r,j)
            shifted=sp.Poly(P.as_expr().subs(z,z+1),z)
            identity=sp.Poly(sp.rf(z,r+1)*z**(j-1),z) \
                     -sp.Poly((z+r)*z**(j-1),z)*P+shifted
            assert identity==Q
            count+=1
    for r in range(5):
        for M in range(1,6):
            AH=sp.rf(z,r+1)*z**(M-1)
            N=AH+(t-1)*sum(z**(M-j)*Q_polynomial(r,j).as_expr()*t**(M-j)
                          for j in range(1,M+1))
            NT=sp.Poly(sp.expand(N.subs({z:X+3,t:T+1})),X,T)
            assert all(c>=0 for c in NT.coeffs())
    for r in range(1,81):
        assert ROWS[r][r]==1
        assert all(ROWS[r][j]==0 for j in range(r+1,81))
        if r>=2: assert ROWS[r][2]>=factorial(r-2)
    k=sp.symbols('k',integer=True,positive=True)
    assert sp.factor(2/((k-1)*k*(k+1)*(k+2))
            -sp.Rational(2,3)*(1/((k-1)*k*(k+1))-1/(k*(k+1)*(k+2))))==0
    print('matching/positive Q:',count,'exact cases; 25 raw numerator cones; C_r through r=80')


def check_primitive_arithmetic():
    Tr=0
    for r in range(1,81):
        cr=sum(ROWS[r][j]*2**(r-j) for j in range(1,r+1))
        Tr=2*(r+2)*Tr+cr
        A=factorial(r+2)//2
        B=F(1)+F(Tr,2**r*A)
        K=r+v2(A)
        assert Tr%2==1
        assert v2(B.denominator)==K
        # Exact pole-k=1 tail, including its central-binomial expression.
        pole_tail=F(1,5)*prod((F(2*j+1,2*(j+3)) for j in range(r)),start=F(1))
        pole_tail2=F(2*factorial(2*r),5*4**r*factorial(r)*factorial(r+2))
        assert pole_tail==pole_tail2
        for M in [r,r+1,K,K+1,K+3]:
            raw=B-F(1,2**M)
            if M!=K:
                assert v2(raw.denominator)==max(M,K)
                assert F(raw.denominator,2**M)>=1
            else:
                D0=2**r*A; Aodd=A//2**v2(A)
                assert raw.denominator==D0//gcd(D0,Tr-Aodd)
        if r==5:
            assert B==F(11203,8960)
    print('primitive 2-adic formulas and resonant gcd formula: r=1,...,80')


def check_gcd_and_correction():
    count=0
    for n in range(2,81):
        a=factorial(n)-1
        assert gcd(a,factorial(n+1))==1
        for r in range(11):
            Ar=factorial(n+r+1)//factorial(n+1)
            for M in (1,2,5):
                d=factorial(n+r+1)*factorial(n+1)**(M-1)
                assert gcd(a,d)==gcd(a,Ar)
                count+=1
    r,M=5,8
    assert M>=r and 6**M>=factorial(r+4) and 4**M>=r+5
    ratio_certificate=sp.Poly((X+4)**M-(X+r+5),X)
    assert all(c>=0 for c in ratio_certificate.all_coeffs())
    Ps=[raw_P(r,j) for j in range(1,M+1)]
    Ps[-1]+=sp.Poly(sp.rf(z,r),z)
    D=2**(M-1)*factorial(r+2)
    boundary=sum(int(P.eval(3))*2**(M-j) for j,P in enumerate(Ps,1))
    assert F(boundary,D)==F(11203,8960)
    def U(n):
        A=factorial(n+r)//factorial(n)
        return sum((F(int(P.eval(n+1)),A*factorial(n)**j)
                    for j,P in enumerate(Ps,1)),F(0))
    for n in range(2,81):
        assert F(1,factorial(n)-1)+U(n+1)-U(n)>0
    # A fully specified integer certificate in the requested family for 4S-5.
    c=11203
    P2=11200*boundary
    g=gcd(D*c,P2)
    assert (D*c//g,P2//g)==(4,5)
    lo,hi=S_interval(40)
    assert 0<4*lo-5<4*hi-5<F(1,71)
    print('M-independent gcd:',count,'exact cases; orbit-positive repair and primitive 4S-5 certificate')


def check_cone_certificates():
    certs=json.loads((HERE/'exact_pures_cone_certificates.json').read_text())
    loS,hiS=S_interval(50)
    for d in certs:
        r,M,a=d['r'],d['M'],d['a']
        constant,B,objective=cone_data(r,M,a)
        c=sp.Integer(d['c'])
        P=sp.Matrix([sp.Integer(v) for v in d['P']])
        slack=c*constant+B*P
        assert all(v>=0 for v in slack)
        ids=d['active']
        assert all(slack[i]==0 for i in ids)
        lam=B[ids,:].T.inv()*(-objective)
        assert all(v>=0 for v in lam)
        assert lam.dot(constant[ids,:])==objective.dot(P)/c
        D=2**(M-1)*factorial(r+2)
        P2=int(objective.dot(P)); g=gcd(D*int(c),P2)
        q,p=D*int(c)//g,P2//g
        assert (q,p)==(int(d['q']),int(d['p']))
        lo=q*loS-p; hi=q*hiS-p
        assert lo>0
        lower=lo.numerator//lo.denominator
        upper=-((-hi.numerator)//hi.denominator)
        assert F(lower)<=lo<hi<=F(upper)
        print(f'cone (r,M,a)=({r},{M},{a}): exact primal+dual; q={q}, p={p}; {lower} < L < {upper}')


def main():
    before=hashlib.sha256((HERE/'Spec.lean').read_bytes()).hexdigest()
    assert before==SPEC_HASH
    check_algebra()
    check_matching_and_positivity()
    check_primitive_arithmetic()
    check_gcd_and_correction()
    check_cone_certificates()
    after=hashlib.sha256((HERE/'Spec.lean').read_bytes()).hexdigest()
    assert after==before
    print('PASS: all exact checks; Spec.lean unchanged. No irrationality theorem claimed.')


if __name__=='__main__':
    main()
