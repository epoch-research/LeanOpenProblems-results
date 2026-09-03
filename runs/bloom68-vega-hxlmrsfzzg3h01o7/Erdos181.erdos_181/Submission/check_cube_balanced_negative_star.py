"""Exact audits of the fifth-star negative-load construction.
This is not a proof or disproof of the Ramsey conjecture in Spec.lean.
"""
from fractions import Fraction as F
from itertools import combinations, product
from math import comb
from collections import Counter

profiles = {}
for n in range(2, 6):
    edges = list(combinations(range(n), 2))
    counter = Counter()
    for mask in range(1 << len(edges)):
        degrees = [0]*n
        for i, (a, b) in enumerate(edges):
            if mask >> i & 1:
                degrees[a] += 1
                degrees[b] += 1
        if min(degrees):
            counter[tuple(sorted(degrees))] += 1
    profiles[n] = counter
assert profiles[5][(1, 1, 1, 1, 2)] == 30
assert all(sum(ds) >= 6 for ds in profiles[5])
assert all(ds.count(1) >= 2 for ds in profiles[5] if sum(ds) == 8)

def mul(xs):
    result = F(1)
    for x in xs:
        result *= x
    return result

def coeffs(K, d):
    q, u = F(1, K*d), 1-F(1, K*d)
    t = (d-2)*q
    w = comb(d-1, 2)*(q/u)**2
    a, b = {}, {}
    for j in range(1, 5):
        a[j] = (-1)**j * (j-1-t)/(u**j*(1+t))
        n = d-1-j
        b[j] = (-1)**j*w*u**(1-j)
        for z in range(3):
            diff = sum((-1)**(j-i)*comb(j, i)*int(z+i >= 3) for i in range(j+1))
            if z <= n:
                b[j] += diff*comb(n, z)*q**z*u**(1-j-z)
        b[j] /= (1+t)
    assert b[1] == -q/u*a[1]
    return q, u, a, b

def cond_moment(n, q, u, a):
    return sum(count*(q*u)**(sum(ds)//2)*mul(a[j] for j in ds)
               for ds, count in profiles[n].items())

def moments(K, d):
    q, u, a, b = coeffs(K, d)
    M = {n: q*cond_moment(n, q, u, a)+u*cond_moment(n, q, u, b)
         for n in (2, 3, 5)}
    assert M[2] == q*q*a[1]*a[1]
    return M

for K, d in ((16, 6), (16, 8), (32, 6), (16, 16)):
    q, u, a, b = coeffs(K, d)
    p = 1-u**(d-1)-(d-1)*q*u**(d-2)
    w = comb(d-1, 2)*(q/u)**2
    value = lambda z: F(1) if z >= 3 else w if z == 0 else F(0)
    def mean(f, n):
        return sum(comb(n, z)*q**z*u**(n-z)*f(z) for z in range(n+1))
    assert mean(lambda z: value(z), d-1) == p
    assert mean(lambda z: value(z+1), d-1) == p
    assert 0 < p < F(1, 2*K*K)
    assert 0 < w < 1
    for hub, co in ((0, b), (1, a)):
        for j in range(1, 5):
            actual = mean(lambda z: sum((-1)**(j-i)*comb(j, i)*value(hub+z+i)
                                        for i in range(j+1)), d-1-j)/(1-p)
            assert actual == co[j]
        row = {z: (mean(lambda r: value(hub+z+r), d-5)-p)/(1-p)
               for z in range(5)}
        exact = F(0)
        pairs = list(combinations(range(5), 2))
        for bits in product((0, 1), repeat=10):
            degrees = [0]*5
            for x, (i, j) in zip(bits, pairs):
                degrees[i] += x
                degrees[j] += x
            s = sum(bits)
            exact += q**s*u**(10-s)*mul(row[z] for z in degrees)
        assert exact == cond_moment(5, q, u, co)
    print('Exact balance, finite differences and all 1024 shared-type assignments:', K, d)

for K in (16, 32):
    lam = F(1, K)
    leading = F(5, 4)*(1-lam)*lam**8/(1+lam)**5
    for d in (64, 256, 4096, 65536, 1048576):
        M = moments(K, d)
        cumulant = M[5]-10*M[2]*M[3]
        count = d*comb(d-1, 4)
        ratio = count*M[5]/(leading*d)
        cratio = count*cumulant/(leading*d)
        assert M[5] > 0 and cumulant > 0
        if d == 1048576:
            assert abs(ratio-1) < F(1, 1000)
            assert abs(cratio-1) < F(1, 1000)
        print('K,d, negative moment-load / leading, negative cumulant-load / leading:',
              K, d, float(ratio), float(cratio))

# The asymptotic proof is analytic, not an extrapolation of these checks.
# Audit arithmetic and the character ranks in the explicit avoiding injection.
def rank(vectors):
    basis = {}
    for v in vectors:
        while v:
            j = v.bit_length()-1
            if j not in basis:
                basis[j] = v
                break
            v ^= basis[j]
    return len(basis)

for K in (16, 32):
    for d in (64, 128, 256, 1024):
        L, r = (K*d-1)**2, comb(d-1, 2)
        m = 1 << (d-1)
        k = (L-1).bit_length()
        assert k <= d//2
        base = (1 << (d//2))-1
        chars = [base] + [base ^ 1 ^ (1 << (d//2+j-1)) for j in range(1, k)]
        assert all(v.bit_count() == d//2 for v in chars)
        assert rank(chars+[(1 << d)-1]) == k+1
        s = (4*m+K*d*L-1)//(K*d*L)
        N = K*d*L*s
        tau = ((r-(d//2)*((1 << k)-1))*pow(d, -1, L)) % L
        assert (d*tau+(d//2)*((1 << k)-1)) % L == r
        largest_fibre = (((1 << k)+L-1)//L)*(m >> k)
        assert largest_fibre <= (K*d-1)*s
        assert 4*m <= N < 4*m+K*d*L
        print('Avoiding-injection character rank, tag sum and fibre capacity:', K, d)
print('PASS. No unrestricted Ramsey conclusion is asserted.')
