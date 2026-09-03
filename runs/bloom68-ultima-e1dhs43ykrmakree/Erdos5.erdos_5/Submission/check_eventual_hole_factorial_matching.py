#!/usr/bin/env python3
"""Finite checks for EventualHoleContradictionAttempt.md.

Uses actual integer factorizations. No artificial prime indicator, asymptotic
claim, or assertion of an eventual prime-gap hole is tested here.
"""
from functools import lru_cache
from math import comb, factorial, gcd, isqrt, lcm, prod
from random import Random

from sympy import factorint, isprime, primerange
from sympy.ntheory.modular import crt


@lru_cache(maxsize=None)
def fac(n):
    assert n >= 1
    return {int(q): int(e) for q, e in factorint(n).items()}


def valuation(n, q):
    ans = 0
    while n % q == 0:
        ans += 1
        n //= q
    return ans


def moduli(H):
    Q = lcm(*range(1, H + 1))
    return Q, Q * prod(primerange(1, H + 1))


def allocate(m, H):
    """Assign every binomial prime power to the first valuation maximum."""
    fs = [fac(m + i) for i in range(1, H + 1)]
    all_primes = set().union(*(set(f) for f in fs))
    a = [1] * H
    for q in all_primes:
        vs = [f.get(q, 0) for f in fs]
        exponent = sum(vs) - valuation(factorial(H), q)
        assert 0 <= exponent <= max(vs)
        i = vs.index(max(vs))
        a[i] *= q ** exponent
    b = [(m + i + 1) // a[i] for i in range(H)]
    return a, b


def periodic_profile(m, H):
    """Independent computation using only residues modulo W_H."""
    b = [1] * H
    for q in primerange(1, H + 1):
        q = int(q)
        power, s = q, 1
        while power * q <= H:
            power *= q
            s += 1
        modulus = power * q
        residue = m % modulus
        truncated = []
        for i in range(1, H + 1):
            n = (residue + i) % modulus
            if n == 0:
                truncated.append(s + 1)
            else:
                truncated.append(valuation(n, q))
        idx = truncated.index(max(truncated))
        C = 0
        power = q
        for _ in range(s):
            C += (m + H) // power - m // power - H // power
            power *= q
        assert 0 <= C <= s
        for i, v in enumerate(truncated):
            b[i] *= q ** (s - C if i == idx else v)
    return b


def proper_matching_rank(m, H):
    """Maximum matching with proper prime divisors, via augmenting paths."""
    adjacency = [[q for q in fac(m + i) if q < m + i]
                 for i in range(1, H + 1)]
    owners = {}

    def augment(i, visited):
        for q in adjacency[i]:
            if q in visited:
                continue
            visited.add(q)
            if q not in owners or augment(owners[q], visited):
                owners[q] = i
                return True
        return False

    return sum(augment(i, set()) for i in range(H))


def check_allocation(m, H, check_rank=False):
    Q, W = moduli(H)
    a, b = allocate(m, H)
    assert prod(a) == comb(m + H, H)
    assert prod(b) == factorial(H)
    assert b == periodic_profile(m, H)
    assert all(Q % x == 0 for x in b)
    assert all(a[i] * b[i] == m + i + 1 for i in range(H))
    assert all(gcd(a[i], a[j]) == 1 for i in range(H)
               for j in range(i))
    if m > Q:
        assert min(a) > 1
        prime_sites = sum(bool(isprime(m + i)) for i in range(1, H + 1))
        assert sum(b[i] == 1 and isprime(a[i]) for i in range(H)) == prime_sites
        labels = [min(fac(a[i])) for i in range(H)
                  if not isprime(m + i + 1)]
        assert len(labels) == len(set(labels))
        assert all(min(fac(a[i])) <= (m + i + 1) // 2
                   for i in range(H) if not isprime(m + i + 1))
        if check_rank:
            assert proper_matching_rank(m, H) == H - prime_sites
    assert sum(any(q <= H for q in fac(x)) for x in a) <= len(list(primerange(1, H + 1)))
    for D in (1, 2, 3, 5):
        large = sum(x > H ** D for x in b)
        assert D * large <= H
    return a, b


def check_roots(H, residue):
    Q, W = moduli(H)
    m = residue + W  # positive representative; the profile depends only on residue
    a, b = check_allocation(m, H)
    J = [i for i in range(H) if gcd(a[i], W) == 1]
    assert len(J) >= H - len(list(primerange(1, H + 1)))
    slopes = [W // x for x in b]
    for q in primerange(1, max(50, 3 * H)):
        roots = [sum((a[i] + slopes[i] * t) % q == 0 for i in J)
                 for t in range(q)]
        if q <= H:
            assert sum(roots) == 0
        else:
            assert sum(roots) == len(J)
            assert max(roots, default=0) <= 1
            assert sum(v != 0 for v in roots) < q


def check_small_cofactor_universality():
    cases = 0
    for H in range(2, 25):
        qs = list(primerange(H + 30, H + 80))[:3]
        for k in range(1, isqrt(H) + 1):
            for q in qs:
                n = k * q
                for i in range(1, H + 1):
                    a, b = allocate(n - i, H)
                    assert a[i - 1] == q and b[i - 1] == k
                    cases += 1
    return cases


def check_disjoint_inventory():
    X, H, u, D = 25000, 3, 5, 2
    K = H ** D
    ps = list(primerange(X + 1, 2 * X + 100))
    anchors = [p for p, pp in zip(ps, ps[1:])
               if p + u + H <= 2 * X and pp > p + u + H]
    values = []
    good = primes_a = powers_a = small_a = large_b = 0
    large_modulus_codes = 0
    for p in anchors:
        m = p + u
        a, b = check_allocation(m, H)
        assert all(not isprime(m + i) for i in range(1, H + 1))
        values.extend(range(m + 1, m + H + 1))
        labels = [min(fac(x)) for x in a]
        assert len(set(labels)) == H
        modulus = prod(labels)
        assert gcd(p, modulus) == 1
        residue, computed_modulus = crt(labels, [-(u + i) for i in range(1, H + 1)])
        assert int(computed_modulus) == modulus
        assert (p - int(residue)) % modulus == 0
        if modulus > X:
            first = int(residue) + ((X - int(residue)) // modulus + 1) * modulus
            assert first == p and first + modulus > 2 * X
            large_modulus_codes += 1
        for aa, bb in zip(a, b):
            if bb > K:
                large_b += 1
            if any(q <= H for q in fac(aa)):
                small_a += 1
            if bb <= K and isprime(aa):
                assert bb >= 2
                primes_a += 1
            if bb <= K and len(fac(aa)) == 1 and not isprime(aa):
                powers_a += 1
            if bb <= K and all(q > H for q in fac(aa)) and len(fac(aa)) >= 2:
                good += 1
    assert len(values) == len(set(values))
    M = len(anchors)
    # Count the finite reservoirs by their representations, with exact endpoints.
    prime_rep = sum(sum(X < b * q <= 2 * X for q in primerange(2, 2 * X // b + 1))
                    for b in range(2, K + 1))
    prime_values = {b * q for b in range(2, K + 1)
                    for q in primerange(2, 2 * X // b + 1) if X < b * q <= 2 * X}
    assert 2 * K * K < X
    assert prime_rep == len(prime_values)  # unique prime factor > sqrt(2X)
    power_rep = 0
    for b in range(1, K + 1):
        for q in primerange(2, int((2 * X // b) ** 0.5) + 2):
            v = q * q
            while b * v <= 2 * X:
                if b * v > X:
                    power_rep += 1
                v *= q
    assert primes_a <= prime_rep and powers_a <= power_rep
    assert D * large_b <= M * H
    assert small_a <= M * len(list(primerange(1, H + 1)))
    assert good >= M * H - large_b - small_a - primes_a - powers_a
    assert D * good >= ((D - 1) * M * H
                        - D * M * len(list(primerange(1, H + 1)))
                        - D * (prime_rep + power_rep))
    return M, good, large_modulus_codes, prime_rep, power_rep


def main():
    cases = ranks = 0
    for H in range(2, 11):
        Q, _ = moduli(H)
        for m in range(0, 201):
            check_allocation(m, H)
            cases += 1
        for m in range(Q + 1, Q + 401):
            check_allocation(m, H, check_rank=m <= Q + 120)
            cases += 1
            ranks += m <= Q + 120
    rng = Random(20261106)
    periods = 0
    for H in range(2, 15):
        _, W = moduli(H)
        for _ in range(15):
            m = rng.randrange(0, 5000)
            b0 = check_allocation(m, H)[1]
            assert b0 == check_allocation(m + W, H)[1]
            assert b0 == check_allocation(m + 2 * W, H)[1]
            periods += 1
    root_cases = 0
    for H in range(2, 11):
        for residue in range(20):
            check_roots(H, residue)
            root_cases += 1
    universal_cases = check_small_cofactor_universality()
    inventory = check_disjoint_inventory()
    a, b = check_allocation(118, 3, check_rank=True)
    assert a == [119, 20, 121] and b == [1, 6, 1]
    assert isprime(113) and all(not isprime(n) for n in (119, 120, 121))
    a37, b37 = check_allocation(37, 3, check_rank=True)
    assert a37 == [19, 13, 40] and b37 == [2, 3, 1]
    assert isprime(37) and all(not isprime(n) for n in (38, 39, 40))
    assert all(gcd(n, 36) > 1 for n in (38, 39, 40))
    print(f"PASS: {cases} allocation/cofactor cases; {ranks} proper-matching ranks")
    print(f"PASS: {periods} independent period tests (each at m, m+W, m+2W)")
    print(f"PASS: {root_cases} cofactor-form root-count/admissibility tests")
    print(f"PASS: {universal_cases} small-cofactor universality cases, across all block positions")
    print("PASS: disjoint actual-prime-window inventory:", inventory)
    print("PASS: actual example p=113, offsets 6,7,8: a=", a, "b=", b)
    print("These checks verify finite identities, not any prime-gap asymptotic or conjecture.")


if __name__ == '__main__':
    main()
