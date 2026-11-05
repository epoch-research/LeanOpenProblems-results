"""Exact, standard-library-only audit of a failed m0-dependent ESC transfer.

Every asserted factorization is obtained by trial division, including primality
of the numerator and of every prime factor of each first denominator. All
square-divisor residue boxes are exhaustively enumerated from these verified
prime-power factorizations. No finite sample is extrapolated to all primes.
Run: python3 Submission/LeastJacobiTransferAudit.py
"""

from fractions import Fraction
from math import isqrt, prod

P = 1_915_201
X0 = (P + 3) // 4


def factor(n: int) -> dict[int, int]:
    assert n > 0
    factors: dict[int, int] = {}
    q = 2
    while q <= isqrt(n):
        if n % q == 0:
            e = 0
            while n % q == 0:
                n //= q
                e += 1
            factors[q] = e
        q = 3 if q == 2 else q + 2
    if n > 1:
        factors[n] = 1
    return factors


def is_prime(n: int) -> bool:
    return n > 1 and factor(n) == {n: 1}


def square_divisors(n: int) -> set[int]:
    fs = factor(n)
    assert all(is_prime(q) for q in fs)
    assert prod(q**e for q, e in fs.items()) == n
    divs = {1}
    for q, e in fs.items():
        divs = {d * q**i for d in divs for i in range(2 * e + 1)}
    assert len(divs) == prod(2 * e + 1 for e in fs.values())
    assert all(n * n % d == 0 for d in divs)
    return divs


def jacobi(a: int, n: int) -> int:
    """Binary Euclidean Jacobi algorithm, for odd n>0."""
    assert n > 0 and n % 2 == 1
    a %= n
    sign = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                sign = -sign
        a, n = n, a
        if a % 4 == n % 4 == 3:
            sign = -sign
        a %= n
    return sign if n == 1 else 0


assert P == 24 * 79_800 + 1 and is_prime(P)
assert factor(P - 1) == {2: 6, 3: 2, 5: 2, 7: 1, 19: 1}
# Independent Lucas primality certificate: 11 has order P-1 (mod P).
assert pow(11, P - 1, P) == 1
assert [pow(11, (P - 1) // q, P) for q in (2, 3, 5, 7, 19)] == [
    1_915_200, 1_662_771, 1_682_006, 699_949, 1_084_060
]
assert [P % (4 * m - 1) for m in (1, 2, 3)] == [1, 1, 2]
assert [jacobi(P, 4 * m - 1) for m in (1, 2, 3)] == [1, 1, -1]
M0 = 3

print(f"p={P} is prime, x0={X0}, least negative Jacobi index m0={M0}")
print("m, h=4m-1, Jacobi(p/h), d target mod h, residues of all d|m^2")
for m in range(1, 13):
    h = 4 * m - 1
    ds = square_divisors(m)
    target = (-P * pow(4, -1, h)) % h
    residues = sorted({d % h for d in ds})
    hits = sorted(d for d in ds if (P + 4 * d) % h == 0 and 4 * d < P)
    if m < 12:
        assert target not in residues, (m, h, target, residues)
    else:
        assert m == 12 and hits == [24]
    print(m, h, jacobi(P, h), target, residues, "hits", hits)

print("j, x=x0+j, verified prime factorization, a=4j+3, "
      "Type-I/II targets, residues of all divisors of x^2")
for j in range(12):
    x, a = X0 + j, 4 * j + 3
    assert P < 4 * x and 2 * x < P and 4 * x - P == a
    ds = square_divisors(x)
    targets = ((-pow(4, -1, a)) % a, (-x) % a)
    residues = sorted({d % a for d in ds})
    if j < 11:
        assert all(t not in residues for t in targets), (j, x, targets, residues)
    else:
        assert j == 11 and all(t in residues for t in targets)
    print(j, x, factor(x), a, targets, residues)

# j=11 is the first successful full Type I *and* Type II first denominator.
x, a, c, d = X0 + 11, 47, 239_406, 24
assert c in square_divisors(x) and (4 * c + 1) % a == 0
assert d in square_divisors(x) and 0 < d < x and (x + d) % a == 0
assert x * x % c == 0 and x * x % d == 0
assert (P * x + x * x // c) % a == 0
assert (P * x + P * P * c) % a == 0
assert P * (x + d) % a == 0
assert P * (x + x * x // d) % a == 0
y1, z1 = (P * x + x * x // c) // a, (P * x + P * P * c) // a
y2, z2 = P * (x + d) // a, P * (x + x * x // d) // a
for y, z in ((y1, z1), (y2, z2)):
    assert 0 < x < y < z
    assert Fraction(4, P) == Fraction(1, x) + Fraction(1, y) + Fraction(1, z)

# m=12 is the first successful full Type-II modular parameter.
m, d = 12, 24
h = 4 * m - 1
assert d in square_divisors(m) and 4 * d < P
assert (P + 4 * d) % h == 0
quot = (P + 4 * d) // h
assert (P * m + d) % h == 0
x = (P * m + d) // h
y, z = P * m, P * (m * x // d)
assert quot == 40_751 and x == 488_988 and m * x % d == 0
assert 0 < d < x < y < z and Fraction(4, P) == (
    Fraction(1, x) + Fraction(1, y) + Fraction(1, z))
print("first full first-denominator index = 11; first full modular m = 12")
print("m=12,d=24: h=47, a=40751, (x,y,z) =", (x, y, z))
print("Consequently f(m0)=m0^2=9 does NOT force m<=f(m0) "
      "or a Type-I witness at j<=f(m0).")
