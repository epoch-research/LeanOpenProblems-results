#!/usr/bin/env python3
"""Exact finite checks accompanying finite_spectrum_pd_boundaries.md.

No bounded-window numerical Fourier test is used as a certificate of PD.
The analytic arguments in the note prove the all-frequency statements.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import gcd, isqrt, lcm
import random

import sympy as sp


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def rational_circle_point(radius, p, q):
    den = p * p + q * q
    return (F(radius * (q * q - p * p), den), F(radius * 2 * p * q, den))


def check_rational_parity():
    # These are finite test palettes, not a numerical proof of Bessel positivity.
    palettes = [(1,), (1, 3, 5, 7), (1, 101, 10001)]
    parameters = [(0, 1), (1, 1), (1, 2), (2, 3), (3, 5), (5, 7), (7, 8)]
    for radii in palettes:
        A = Counter()
        for j, radius in enumerate(radii):
            shell = set()
            for p, q in parameters:
                v = rational_circle_point(radius, p, q)
                shell.add(v)
                shell.add(tuple(-x for x in v))
            shell_mass = F(2**j)
            for v in shell:
                require(sum(x*x for x in v) == radius*radius, 'wrong circle')
                A[v] += shell_mass / len(shell)
        common = 1
        for v in A:
            for x in v:
                common = lcm(common, x.denominator)
        require(common % 2 == 1, 'common denominator is not odd')
        for v in A:
            a, b = (int(common*x) for x in v)
            require((a + b) % 2 == 1, 'parity character is not -1')
        off = sum(A.values(), F(0))
        value = F(1) - off
        require(off == 2**len(radii)-1, 'incorrect shell mass')
        require(value == 2 - 2**len(radii), 'incorrect negative witness')
        # Central coefficient off is necessary, and the triangle inequality
        # proves it sufficient for nonnegativity on the entire physical plane.
        repaired_ratio = (off + off) / off
        require(repaired_ratio == 2, 'incorrect repaired ratio')
        print(f'Rational palette {radii}: {len(A)} nonzero atoms, '
              f'odd denominator {common}, T(x*)={value}, repaired ratio=2')


def mul_pi(z):
    x, y = z
    return x-y, x+y


def add(z, w):
    return z[0]+w[0], z[1]+w[1]


def v2(n):
    require(n > 0, 'v2 requires a positive integer')
    k = 0
    while n % 2 == 0:
        k += 1
        n //= 2
    return k


def check_gaussian_filtration():
    for m in range(1, 9):
        P = {(0, 0)}
        power = (1, 0)
        for _ in range(m):
            P = P | {add(z, power) for z in P}
            power = mul_pi(power)
        n = 2**m
        require(len(P) == n, 'Gaussian digits collide')
        A = Counter((p[0]-q[0], p[1]-q[1]) for p in P for q in P)
        require(A[(0, 0)] == n and sum(A.values()) == n*n,
                'wrong autocorrelation normalization')
        layers = Counter()
        norms = set()
        for (x, y), a in A.items():
            norm = x*x+y*y
            if norm:
                norms.add(norm)
                layers[v2(norm)] += a
        require(set(layers) == set(range(m)), 'wrong occupied valuation layers')
        for k in range(m):
            tail = n + sum(a for j, a in layers.items() if j >= k+1)
            require(layers[k] == tail == n*n // 2**(k+1),
                    'sharp layer inequality failed')
        require(F(sum(A.values()), A[(0, 0)]) == 2**m,
                'filtration ratio is not sharp')
        print(f'Gaussian digits m={m}: n={n}, D={len(norms)}, '
              f'{m} valuation layers, every layer inequality is equality')


def canonical_pair(v):
    for x in v:
        if x:
            return v if x > 0 else tuple(-y for y in v)
    raise ValueError('zero frequency')


def compress(V, m):
    """The first m vectors are the standard rational basis in these tests."""
    r = len(V)-m
    q = r//2+1
    choices = list(range(-q, 0))+list(range(1, q+1))
    for t in product(choices, repeat=m):
        images = [sum(x*y for x, y in zip(v, t)) for v in V]
        if all(images):
            pairs = {abs(x) for x in images}
            require(len(pairs) <= q+r, 'compression pair-count failure')
            return t, images
    raise AssertionError('nonzero grid polynomial failed to have a witness')


def check_compression():
    rng = random.Random(81723)
    trials = 0
    for m in range(1, 5):
        for r in range(0, 7):
            for _ in range(8):
                V = [tuple(int(i == j) for i in range(m)) for j in range(m)]
                seen = set(V)
                while len(V) < m+r:
                    v = tuple(rng.randint(-12, 12) for _ in range(m))
                    if not any(v):
                        continue
                    v = canonical_pair(v)
                    if v not in seen:
                        seen.add(v)
                        V.append(v)
                t, images = compress(V, m)
                require(all(images), 'zero image in support')
                trials += 1
    for m in range(1, 11):
        N, r, ratio = m, 0, 2
        require(min(N+1, r+r//2+2) == ratio,
                'independent family does not attain rank bound')
    V = [(1, 0), (0, 1), (1, -1)]
    t, images = compress(V, 2)
    require(min(4, 1+1//2+2) == 3, 'wrong triangle bound')
    require(len({abs(x) for x in images}) == 2,
            'triangle should compress to two opposite pairs')
    print(f'Compression: {trials} exact supports checked; '
          f'triangle witness {t}, images {images}; independent and triangle '
          f'families attain their stated bounds')


def check_sos_hessian():
    for m in range(1, 11):
        theta = sp.symbols(f't0:{m}', real=True)
        T = 1 + sum(sp.cos(t) for t in theta)/m
        paired_sos = 0
        for j in range(0, m, 2):
            a = sp.cos(theta[j]/2)
            b = sp.cos(theta[j+1]/2) if j+1 < m else sp.Integer(0)
            # Squared modulus of sqrt(2/m) (a+i b), with real a,b.
            paired_sos += sp.Rational(2, m)*(a*a+b*b)
        require(sp.trigsimp(T-paired_sos) == 0, 'SOS identity failed')
        point = {t: sp.pi for t in theta}
        Hess = sp.hessian(T, theta).subs(point)
        require(Hess == sp.eye(m)/m, 'wrong zero Hessian')
        require(Hess.rank() == m, 'Hessian rank failure')
        primes = list(sp.primerange(1, 50))[:m]
        for p in primes:
            x, y = 1/sp.sqrt(p), sp.sqrt(1-sp.Rational(1, p))
            require(sp.simplify(x*x+y*y) == 1, 'explicit frequency is not unit')
        print(f'One-circle SOS m={m}: exact identity, Hessian rank {m}, '
              f'optimal complex square count {(m+1)//2}')


def check_circle_multiplicities():
    for k in range(0, 8):
        N = 5**k
        count = 0
        for x in range(-isqrt(N), isqrt(N)+1):
            y2 = N-x*x
            y = isqrt(y2)
            if y*y == y2:
                count += 1 if y == 0 else 2
        require(count == 4*(k+1), 'wrong Gaussian circle multiplicity')
        print(f'Circle N=5^{k}: r2(N)={count}, '
              f'projection norm squared={count}')


def main():
    check_rational_parity()
    check_gaussian_filtration()
    check_compression()
    check_sos_hessian()
    check_circle_multiplicities()
    print('PASS: all exact finite checks succeeded. Analytic assertions are '
          'proved in the accompanying note, not inferred from these tests.')


if __name__ == '__main__':
    main()
