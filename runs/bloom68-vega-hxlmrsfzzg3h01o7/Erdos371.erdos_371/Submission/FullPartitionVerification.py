#!/usr/bin/env python3
"""Certificates for FullPartitionResearch.md. No Lean files are used.

1. Exact finite deterministic partition trade, including all factorial tests
   through combined selected mass 1 and a deterministic Euler cycle.
2. Algebraic renewal checks for the compact-complement signed PD modes.
3. Certified quadrature of the PD ordering form above 1/3. Node values
   use Decimal at precision 65 and an explicitly bounded Ei-difference
   power series. Nodes are then rounded to rational multiples of 10^-30;
   the piecewise-linear ordering integral is accumulated as an INTEGER.
   Its error is bounded analytically, not by comparison of quadratures.

The analytic proofs (Palm formula, interpolation derivative bound, and
small-maximum tail bound) are in the accompanying note. This script is
not a test of the Erdős conjecture.
"""
from collections import Counter
from decimal import Decimal, localcontext, ROUND_HALF_EVEN
from fractions import Fraction as Q
from math import factorial
import time


def integer_partitions(n, minimum=1):
    if n == 0:
        yield ()
        return
    for k in range(minimum, n + 1):
        for p in integer_partitions(n-k, k):
            yield (k,) + p


def falling(n, k):
    z = 1
    for j in range(k):
        z *= n-j
    return z


def feature(alpha, p):
    a, b = Counter(alpha), Counter(p)
    z = 1
    for k, count in a.items():
        z *= falling(b[k], count)
    return z


def finite_certificate():
    P = list(integer_partitions(4))
    assert P == [(1,1,1,1), (1,1,2), (1,3), (2,2), (4,)]
    w = [1, 6, 8, 3, 6]
    K = [
        [0, 1,-2,-1, 2],
        [-1,0, 4, 3,-6],
        [2,-4, 0,-2, 4],
        [1,-3, 2, 0, 0],
        [-2,6,-4, 0, 0],
    ]
    C = [[w[i]*w[j]+K[i][j] for j in range(5)] for i in range(5)]
    assert all(C[i][j]>0 for i in range(5) for j in range(5))
    assert all(sum(C[i]) == 24*w[i] for i in range(5))
    assert all(sum(C[j][i] for j in range(5)) == 24*w[i] for i in range(5))
    assert all(K[i][j] == -K[j][i] for i in range(5) for j in range(5))
    selectors = [a for n in range(5) for a in integer_partitions(n)]
    tests = 0
    for alpha in selectors:
        for beta in selectors:
            if sum(alpha)+sum(beta)>4:
                continue
            f = [feature(alpha,p) for p in P]
            g = [feature(beta,p) for p in P]
            actual = sum(C[i][j]*f[i]*g[j] for i in range(5) for j in range(5))
            expected = Q(1)
            for k in alpha+beta:
                expected /= k
            assert Q(actual,576) == expected, (alpha,beta)
            tests += 1
    sign = lambda x: (x>0)-(x<0)
    total = sum(C[i][j]*sign(max(P[j])-max(P[i])) for i in range(5) for j in range(5))
    assert total == 8
    # Deterministic Hierholzer algorithm: always use the least available vertex.
    remaining = [row[:] for row in C]
    stack, tour = [0], []
    while stack:
        i = stack[-1]
        choices = [j for j in range(5) if remaining[i][j]]
        if choices:
            j = choices[0]
            remaining[i][j] -= 1
            stack.append(j)
        else:
            tour.append(stack.pop())
    tour.reverse()
    assert len(tour) == 577 and tour[0] == tour[-1]
    observed = [[0]*5 for _ in range(5)]
    for i,j in zip(tour,tour[1:]):
        observed[i][j] += 1
    assert observed == C
    assert sum(sign(max(P[j])-max(P[i])) for i,j in zip(tour,tour[1:])) == 8
    print('Finite model: 576-edge deterministic period; %d exact factorial tests; signed mean = 1/72.' % tests, flush=True)
    print('Transition-count matrix:', C, flush=True)


def symbolic_renewal_certificate():
    import sympy as s
    u = s.symbols('u', real=True)
    a0 = 2-s.exp(u)
    a1 = a0+u*s.exp(u-1)
    a2 = a1+(u-u*u/2)*s.exp(u-2)
    assert s.simplify(s.diff(a0,u)-(a0-2)) == 0
    assert s.simplify(s.diff(a1,u)-a1+a0.subs(u,u-1)) == 0
    assert s.simplify(s.diff(a2,u)-a2+a1.subs(u,u-1)) == 0
    assert s.simplify(a1.subs(u,1) - s.integrate(a0,(u,0,1))) == 0
    assert s.simplify(a2.subs(u,2)-a1.subs(u,2)) == 0
    assert s.simplify(a0.subs(u,0)-1) == 0
    print('Symbolic compact-complement renewal identities: passed.', flush=True)


def decimal_certificate():
    with localcontext() as ctx:
        ctx.prec = 65
        ctx.rounding = ROUND_HALF_EVEN
        D = Decimal
        one, two = D(1), D(2)
        c, d = D(9)/20, D(1)/2
        K_SERIES = 48
        # For 0 <= u <= 3/2, the omitted S(u)=sum u^k/(k*k!)
        # tail after 48 is < 2*(3/2)^49/(49*49!). This is exact rational.
        series_tail = 2*Q(3,2)**49/(49*factorial(49))
        assert series_tail < Q(1,10**53)

        def a(u, left=False):
            z = two-u.exp()
            if u>one or (u==one and not left):
                z += u*(u-one).exp()
            if u>=two:
                z += (u-u*u/2)*(u-two).exp()
            return z

        def S(u):
            term = u
            result = u
            for k in range(2,K_SERIES+1):
                term = term*u/k
                result += term/k
            return result

        def primitive_A(y, cc):
            u = y/cc
            ans = two*y-cc*u.exp()
            if y>=cc:
                ans += (y-cc)*(u-one).exp()
            return ans

        def primitive_B_difference(y1,y0,cc):
            u1,u0 = y1/cc,y0/cc
            ans = (y1/y0).ln()-(S(u1)-S(u0))
            if y1>=cc:
                ans += (u1-one).exp()-one
            if y0>=cc:
                ans -= (u0-one).exp()-one
            return ans

        def r(t,cc,left=False):
            if t<D(1)/2:
                J = (primitive_A(one-t,cc)-primitive_A(t,cc)
                     +(t-one+cc)*primitive_B_difference(one-t,t,cc))/cc
                return -a(t/cc,left=left)*J/t
            F = max(D(0),one-(one-t)/cc)
            return a(t/cc,left=left)*F/t

        # Elementary tail constants. All have margins vastly exceeding
        # the <10^-55 rounding errors of these small computations.
        assert (D(3)/4).exp() < D(9)/4
        R_c = max(abs(two*u.exp()-(two*u).exp()) for u in [D(5)/9,D(20)/27])
        R_d = max(abs(two*u.exp()-(two*u).exp()) for u in [D(1)/2,D(2)/3])
        assert R_c < D(9)/20 and R_d < D(29)/50
        assert (-D(20)/9).exp() < D(109)/1000
        assert (-two).exp() < D(17)/125
        # rho(3)=1-log(3)+int_1^2 log(v)/(v+1)dv. The integrand is
        # increasing, hence this RIGHT Riemann sum is an upper bound.
        N_RHO = 1000
        rho3_upper = one-D(3).ln()
        for j in range(1,N_RHO+1):
            v = one+D(j)/N_RHO
            rho3_upper += v.ln()/((v+one)*N_RHO)
        rho3_upper += D('1e-50')
        assert rho3_upper < D(1)/20
        print('rho(3) right-sum upper bound:', rho3_upper, flush=True)
        # 4 rho(4)=int_3^4 rho(t)dt <= rho(3), so rho(4)<1/80.
        tv_c = Q(109,1000)*(Q(9,20)*Q(1,20)+Q(11,20)*Q(1,80))
        tv_d = Q(17,125)*(Q(29,50)*Q(1,20)+Q(21,50)*Q(1,80))
        tail_bound = tv_c*tv_d
        assert tail_bound < Q(15,10**6)

        # Uniform grid; all derivative-break points 1/3,9/20,1/2,
        # 11/20,9/10,1 are grid points. At 9/20 keep both one-sided values.
        M = 30000
        SCALE = 10**30
        scale_D = D(SCALE)
        def node(i,cc,left=False):
            t = D(i)/M
            return int((r(t,cc,left=left)*scale_D).to_integral_value())
        numerator = 0
        prefix_f = prefix_g = 0
        f0,g0 = node(M//3,c),node(M//3,d)
        for i in range(M//3,M):
            f1,g1 = node(i+1,c,left=True),node(i+1,d,left=True)
            fs,gs = f0+f1,g0+g1
            numerator += 3*(prefix_f*gs-prefix_g*fs)
            numerator += 2*(f0*g1-f1*g0)
            prefix_f += fs
            prefix_g += gs
            f0,g0 = f1,g1
            if i+1 == 9*M//20:
                f0 = node(i+1,c,left=False)
        B_linear = Q(numerator,12*M*M*SCALE*SCALE)
        # Analytic bound: |r|<=3, |r''|<=1000 on each grid segment.
        # Hence L1 interpolation error <= (1000/18)/M^2 per density;
        # the ordering-form error is <= 4 times that.
        interpolation_error = Q(2000,9*M*M)
        # Node computation proof in the note gives error < 10^-29 each.
        # This 10^-25 allowance also covers all Decimal operation errors.
        total_error = interpolation_error+Q(1,10**25)
        lower,upper = B_linear-total_error,B_linear+total_error
        assert lower > Q(37,10**6)
        assert upper < Q(38,10**6)
        B_lower = lower-tail_bound
        assert B_lower > Q(2,10**5)
        # Density 1+(h_c(A)h_d(B)-h_d(A)h_c(B))/4 gives sign mean B/2.
        assert B_lower/2 > Q(1,10**5)
        print('Exact integer numerator for B_linear:', numerator, flush=True)
        print('Exact denominator for B_linear:', 12*M*M*SCALE*SCALE, flush=True)
        print('B_linear =', D(B_linear.numerator)/B_linear.denominator, flush=True)
        print('Analytic interpolation + rounding error <=', D(total_error.numerator)/total_error.denominator, flush=True)
        def outward(q, up=False):
            scale = 10**23
            n = -((-q.numerator*scale)//q.denominator) if up else (q.numerator*scale)//q.denominator
            return D(n)/D(scale)
        print('Certified B_high interval:', outward(lower),outward(upper,up=True), flush=True)
        print('Tail total-variation product bound:', tail_bound, '=', D(tail_bound.numerator)/tail_bound.denominator, flush=True)
        print('Certified full B lower bound:', outward(B_lower), flush=True)
        print('Certified ordering mean >', outward(B_lower/2), '> 1e-5.', flush=True)


if __name__ == '__main__':
    start = time.monotonic()
    finite_certificate()
    symbolic_renewal_certificate()
    decimal_certificate()
    print('All certificates passed in %.2f seconds.' % (time.monotonic()-start), flush=True)
