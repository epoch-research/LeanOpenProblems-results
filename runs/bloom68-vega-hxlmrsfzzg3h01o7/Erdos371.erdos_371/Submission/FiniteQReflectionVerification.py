"""Finite checks for FiniteQReflectionResearch.md; no conjecture is assumed."""
from bisect import bisect_left
from collections import Counter
from fractions import Fraction
from math import gcd, isqrt, log

LIMIT = 100_001
P = [0] * (LIMIT + 1)
P[1] = 1
for p in range(2, LIMIT + 1):
    if P[p] == 0:
        for m in range(p, LIMIT + 1, p):
            P[m] = p
primes = [p for p in range(2, LIMIT + 1) if P[p] == p]

# Coordinates are (p, k, s), with n=kq-1 if s=+1, n=kq if s=-1.
def index(q, st):
    p, k, s = st
    return k * q - (s == 1)


def step(q, st):
    p, k, s = st
    assert 1 <= k < p < q
    a = k * q - s
    assert a % p == 0
    b = a // p
    assert 1 <= b < q and P[b] <= p
    r = max(p, P[q - b])
    return r, p - k, -s


def factor_primes(a):
    out = []
    while a > 1:
        r = P[a]
        out.append(r)
        while a % r == 0:
            a //= r
    return out


q_tests = [q for q in primes if q <= 1000] + [1999, 4999, 9973, 19997]
state_checks = 0
iterate_checks = 0
incoming_checks = 0
max_depth = 0
samples = []
for q in q_tests:
    V = {}
    bad = transients = good_labels = 0
    for p in primes:
        if p >= q:
            break
        u = pow(p, -1, q)
        down, up = P[u] <= p, P[q-u] <= p
        bad += (not down) + (not up)
        good_labels += down and up
        transients += down != up
        if down:
            n = p*u - 1
            V[n] = (p, n//q, -1)
        if up:
            n = p*(q-u)
            V[n] = (p, (n+1)//q, 1)
    assert len(V) == 2*bisect_left(primes, q)-bad
    assert len(V) == 2*good_labels + transients
    edge = {}
    cycles = set()
    for n, st in V.items():
        p, k, s = st
        nxt = step(q, st)
        m = index(q, nxt)
        assert m == p*q-n-1 > 0
        assert V[m] == nxt
        assert nxt[2] == -s and nxt[0] >= p
        n2 = index(q, step(q, nxt))
        assert n2 == n+q*(nxt[0]-p)
        if nxt[0] == p:
            cycles.add(n)
            assert n2 == n
        if n+1 <= LIMIT:
            assert sorted((P[n], P[n+1])) == [p, q]
            assert s == (1 if P[n+1] > P[n] else -1)
        edge[n] = m
        state_checks += 1
    assert len(V)-len(cycles) == transients
    indeg = Counter(edge.values())
    assert sum(st[2]*(1+indeg[n]) for n, st in V.items()) == 0
    assert sum(abs(indeg[n]-1) for n in V) <= 2*transients
    assert abs(sum(st[2] for st in V.values())) <= transients

    # Formula (4): use exact trial divisibility up to p when a exceeds LIMIT.
    for n, st in V.items():
        p, k, s = st
        a = k*q-s
        rs = factor_primes(a) if a <= LIMIT else [r for r in primes[:bisect_left(primes, p)+1] if a % r == 0]
        incoming = [r*q-n-1 for r in rs if k < r <= p and P[q-a//r] <= r]
        assert len(incoming) == indeg[n]
        assert all(edge[m] == n for m in incoming)
        incoming_checks += 1

    mass = Counter({n: 1 for n in V})
    for j in range(25):
        assert sum(abs(mass[n]-1) for n in V) <= 2*transients
        iterate_checks += 1
        new_mass = Counter()
        for n, a in mass.items():
            new_mass[edge[n]] += a
        mass = new_mass
    for n in V:
        depth = 0
        m = n
        while m not in cycles:
            m = edge[m]
            depth += 1
            assert depth <= bisect_left(primes, q)
        max_depth = max(max_depth, depth)
    if q in [997, 4999, 19997]:
        samples.append((q, len(V), transients, bad, round(bad*log(q)**2/q, 4)))

# Independent completeness check by directly scanning integers for small q.
Q = 97
candidate = set()
for q in [q for q in primes if q <= Q]:
    for p in [p for p in primes if p < q]:
        u = pow(p, -1, q)
        if P[u] <= p:
            candidate.add(p*u-1)
        if P[q-u] <= p:
            candidate.add(p*(q-u))
direct = {n for n in range(2, Q*Q) if max(P[n], P[n+1]) <= Q
          and P[n]*P[n+1] > n+1}
assert candidate == direct

# Natural prefixes: preserve coordinates even when iterates are much larger
# than LIMIT. Every new cofactor whose P is requested is still less than q.
natural_checks = 0
natural_samples = []
for X in [1000, 10_000, 100_000]:
    active = transient = return_one = return_any = 0
    for n in range(2, X+1):
        p, q = sorted((P[n], P[n+1]))
        if p*q <= n+1:
            continue
        active += 1
        s = 1 if P[n+1] == q else -1
        st = (p, (n+(s == 1))//q, s)
        first = p*q-n-1
        cur = st
        last = [n, first]
        did_return = False
        for j in range(1, 10):
            cur = step(q, cur)
            m = index(q, cur)
            assert m >= last[j % 2]
            last[j % 2] = m
            if j == 1:
                transient += cur[0] > p
                return_one += m <= 2*X
            if j % 2 == 1:
                assert m >= first
                if m <= 2*X:
                    did_return = True
                    assert p*q <= 3*X+1
            natural_checks += 1
        return_any += did_return
    assert return_one == return_any
    natural_samples.append((X, active, transient, return_one))

# Exact rational verification of the Selberg identities used in the proof.
def mobius(n):
    sign = 1
    for p in primes:
        if p*p > n:
            break
        if n % p == 0:
            n //= p
            sign = -sign
            if n % p == 0:
                return 0
    return -sign if n > 1 else sign


def phi(n):
    ans = n
    for p in factor_primes(n):
        ans -= ans//p
    return ans


sieve_checks = 0
for z in range(2, 41):
    G = sum((Fraction(mobius(d)**2, phi(d)) for d in range(1, z+1)), Fraction())
    lam = {}
    for d in range(1, z+1):
        inner = sum((Fraction(mobius(h)**2, phi(h)) for h in range(1, z//d+1)
                     if gcd(h, d) == 1), Fraction())
        lam[d] = Fraction(mobius(d)*d, phi(d))*inner/G
        assert abs(lam[d]) <= Fraction(d, phi(d))
    assert lam[1] == 1
    quad = sum((lam[d]*lam[e]*Fraction(gcd(d,e), d*e)
                for d in range(1,z+1) for e in range(1,z+1)), Fraction())
    assert quad == 1/G
    sieve_checks += 1

print('Full-fiber state/cofactor checks:', state_checks)
print('Incoming-prime-factor checks:', incoming_checks)
print('Finite-iterate l1 checks:', iterate_checks)
print('Maximum observed transient depth:', max_depth)
print('Independent direct-sieve completeness:', len(direct), 'states')
print('Natural-prefix parity/escape checks:', natural_checks)
print('Exact rational Selberg checks:', sieve_checks)
print('q, |Vq|, transients, bad incidences, B(q)log(q)^2/q:')
for row in samples:
    print(row)
print('X, active, transient, sources whose odd iterates enter [1,2X]:')
for row in natural_samples:
    print(row)
print('All checks passed. The asymptotic sieve estimate is proved in the note, not by these tests.')
