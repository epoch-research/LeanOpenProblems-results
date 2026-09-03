#!/usr/bin/env python3
"""Independent exact-integer checks for CRTWindowReport.md.

No floating point, LP solver, conjectural assumption, or primorial reduction is
used. General claims have proofs in the report and/or Lean; finite checks are
regression tests, not extrapolations of an asymptotic bound.
"""
from hashlib import sha256
from itertools import product
from math import gcd, prod
from pathlib import Path

SPEC_HASH = "c961aa894dc05a671003b74cd770bf0efc120992bcaaa79466c418b03e1688e7"


def ceildiv(a, b):
    return (a + b - 1) // b


def crt(p, q, a, b):
    """Canonical root; p=1 is included for the Euclidean recursion."""
    assert p > 0 and q > 0 and gcd(p, q) == 1
    assert 0 <= a < p and 0 <= b < q
    j = ((a - b) * pow(q, -1, p)) % p if p > 1 else 0
    r = b + q * j
    assert 0 <= r < p * q and r % p == a and r % q == b
    return r


def direct_records(p, q):
    """Fill the CRT grid by visiting integer roots, then take prefix maxima."""
    n = p * q
    grid = [[None] * q for _ in range(p)]
    for r in range(n):
        assert grid[r % p][r % q] is None
        grid[r % p][r % q] = r
    maximum = [[-1] * (q + 1) for _ in range(p + 1)]
    records = set()
    for a in range(p):
        for b in range(q):
            maximum[a + 1][b + 1] = max(
                maximum[a][b + 1], maximum[a + 1][b], grid[a][b])
            if maximum[a + 1][b + 1] == grid[a][b]:
                records.add((a, b))
    return records, grid


def euclidean_records(p, q):
    if p == 1:
        return {(0, b) for b in range(q)}
    if q == 1:
        return {(a, 0) for a in range(p)}
    if p < q:
        old = euclidean_records(p, q - p)
        diagonal = {(i, q - p + i) for i in range(p)}
    else:
        old = euclidean_records(p - q, q)
        diagonal = {(p - q + i, i) for i in range(q)}
    assert old.isdisjoint(diagonal)
    return old | diagonal


def boundary_matching(p, q):
    """Bijection from grid boundary to records, increasing the CRT root.

    This is the construction in the proof of the prefix-count bound.
    """
    if p == 1:
        return {(0, b): (0, b) for b in range(q)}
    if q == 1:
        return {(a, 0): (a, 0) for a in range(p)}
    if p < q:
        match = boundary_matching(p, q - p)
        for i in range(p):
            match[(0, q - p + i)] = (i, q - p + i)
    else:
        match = boundary_matching(p - q, q)
        for i in range(q):
            match[(p - q + i, 0)] = (p - q + i, i)
    return match


def check_records_and_trimming():
    pairs = 0
    for p in range(2, 33):
        for q in range(p + 1, 91):
            if gcd(p, q) != 1:
                continue
            pairs += 1
            n = p * q
            records, grid = direct_records(p, q)
            assert records == euclidean_records(p, q)
            assert len(records) == p + q - 1
            full_favorable = {grid[a][b] + 1 for a, b in records} - {n}
            assert len(full_favorable) == p + q - 2
            strict_favorable = {
                t for t in full_favorable if t % p != 0 and t % q != 0}
            assert len(strict_favorable) == p + q - 2 - q // p
            match = boundary_matching(p, q)
            boundary = {(a, 0) for a in range(p)} | {(0, b) for b in range(q)}
            assert set(match) == boundary
            assert set(match.values()) == records
            assert len(set(match.values())) == len(match)
            for point, image in match.items():
                assert grid[point[0]][point[1]] <= grid[image[0]][image[1]]
            count = 0
            for t in range(1, n):
                count += t in full_favorable
                assert count <= ceildiv(t, p) + ceildiv(t, q) - 1
                if q - p >= 2 and t >= 2 and t in full_favorable:
                    assert (q - p) * (t - 1) >= p * (q - 1)
            first = min(full_favorable - {1})
            assert first == min(grid[1][0], grid[0][1]) + 1
    print(f"Euclidean records, exact favorable counts, prefix and gap bounds: {pairs} coprime pairs OK")


def check_exact_pair_union_bound():
    tested = 0
    for p in range(2, 13):
        for q in range(p + 1, 20):
            if gcd(p, q) != 1:
                continue
            n = p * q
            records, grid = direct_records(p, q)
            favorable = {grid[a][b] + 1 for a, b in records} - {n}
            count_p = [0] * p
            count_q = [0] * q
            for length in range(n + 1):
                if length:
                    x = length - 1
                    count_p[x % p] += 1
                    count_q[x % q] += 1
                # The pair intersection has root r, and at most one point here.
                actual = max(count_p[r % p] + count_q[r % q] - int(r < length)
                             for r in range(n))
                predicted = (ceildiv(length, p) + ceildiv(length, q)
                             - length // n - int(length % n in favorable))
                assert actual == predicted
                # Integral singleton counts are included: their allowed residue
                # sets are full columns/rows, NOT empty remainder intervals.
                if 0 < length < n:
                    a_max = max(count_p)
                    b_max = max(count_q)
                    floor_possible = any(
                        count_p[r % p] == a_max and count_q[r % q] == b_max
                        for r in range(length, n))
                    assert floor_possible == (length not in favorable)
                tested += 1
    print(f"Exact maximum-union formula against all residue phases: {tested} lengths OK")


# Fixed certificate, obtained once and verified here without an optimizer.
PRIMES17 = (2, 3, 5, 7, 11)
HIST17 = {1: 5, 2: 3, 3: 1, 4: 2, 5: 1, 7: 1, 8: 2, 11: 1, 16: 1}
BLOCK_ROOTS17 = [
    (1, 2, 0), (1, 4, 0), (1, 6, 2), (1, 8, 8), (1, 10, 0),
    (1, 12, 18), (1, 14, 18), (1, 16, 18), (1, 18, 18), (1, 20, 18),
    (1, 22, 18), (1, 24, 18), (1, 26, 18), (1, 28, 18), (1, 30, 18),
    (2, 4, 6), (2, 5, 0), (2, 8, 0), (2, 9, 3), (2, 12, 18),
    (2, 13, 18), (2, 16, 18), (2, 17, 18), (2, 20, 18), (2, 21, 18),
    (2, 24, 18), (2, 25, 18), (2, 28, 18), (2, 29, 18),
    (3, 4, 0), (3, 8, 0), (3, 12, 18), (3, 16, 18), (3, 20, 18),
    (3, 24, 18), (3, 28, 18),
    (4, 8, 21), (4, 9, 20), (4, 10, 21), (4, 11, 45), (4, 16, 20),
    (4, 17, 20), (4, 18, 20), (4, 19, 20), (4, 24, 20), (4, 25, 20),
    (4, 26, 20), (4, 27, 20),
    (5, 8, 21), (5, 10, 21), (5, 16, 20), (5, 18, 20), (5, 24, 20), (5, 26, 20),
    (6, 8, 21), (6, 9, 17), (6, 16, 17), (6, 17, 17), (6, 24, 17), (6, 25, 17),
    (7, 8, 30), (7, 16, 30), (7, 24, 30),
    (8, 16, 21), (8, 17, 21), (8, 18, 21), (8, 19, 21), (8, 20, 21),
    (8, 21, 21), (8, 22, 21), (8, 23, 21),
    (9, 16, 17), (9, 18, 17), (9, 20, 17), (9, 22, 17),
    (10, 16, 21), (10, 17, 21), (10, 20, 21), (10, 21, 21),
    (11, 16, 42), (11, 20, 42),
    (12, 16, 17), (12, 17, 17), (12, 18, 17), (12, 19, 17),
    (13, 16, 17), (13, 18, 17), (14, 16, 17), (14, 17, 17), (15, 16, 17),
]


def check_block_pair_counterexample():
    length, n = 17, 1 << len(PRIMES17)
    ds = [prod(p for i, p in enumerate(PRIMES17) if s >> i & 1) for s in range(n)]
    cs = [sum(c for t, c in HIST17.items() if t & s == s) for s in range(n)]
    assert sum(HIST17.values()) == length and HIST17.get(0, 0) == 0
    assert all(isinstance(c, int) and c >= 0 for c in HIST17.values())
    assert all(length // ds[s] <= cs[s] <= ceildiv(length, ds[s]) for s in range(n))
    es = [cs[s] - length // ds[s] for s in range(n)]
    seen = set()
    for a, b, r in BLOCK_ROOTS17:
        assert 0 < a < b < n and not a & b and (a, b) not in seen
        seen.add((a, b))
        assert r < ds[a] * ds[b] and r < 46
        assert es[a] == int(r % ds[a] < length % ds[a])
        assert es[b] == int(r % ds[b] < length % ds[b])
        assert es[a | b] == int(r < length % (ds[a] * ds[b]))
    assert seen == {(a, b) for a in range(1, n) for b in range(a + 1, n) if not a & b}
    assert len(seen) == 90
    # Direct enumeration independently checks the five-count impossibility.
    matches = []
    for a, b, c in product(range(2), range(3), range(7)):
        supports = [(x % 2 == a, x % 3 == b, x % 7 == c) for x in range(length)]
        counts = (sum(s[0] for s in supports), sum(s[1] for s in supports),
                  sum(s[2] for s in supports), sum(s[0] and s[2] for s in supports),
                  sum(all(s) for s in supports))
        if counts == (9, 6, 3, 1, 1):
            matches.append((a, b, c))
    assert not matches
    # This fixed-prime-set check is NOT a reduction of arbitrary primes to it.
    period = prod(PRIMES17)
    units = [r for r in range(period) if gcd(r, period) == 1]
    maxgap = max((units[(i + 1) % len(units)] - r) % period for i, r in enumerate(units))
    assert maxgap == 14
    print("17-row counterexample: all 32 rounded counts and 180 ordered block pairs OK; no common roots")


def check_other_exact_examples():
    # The report's six-prime 19-position cover, used only as a finite witness.
    ps = (2, 3, 5, 7, 11, 13)
    roots = (0, 1, 0, 3, 0, 9)
    assert all(any(x % p == a for p, a in zip(ps, roots)) for x in range(19))
    # Distinct large prime columns can be disjoint on every contained subinterval.
    length, ps = 1000, (101, 103, 107, 109, 113)
    rows = [{p for p in ps if (x + 1) % p == 0} for x in range(length)]
    assert all(len(s) <= 1 for s in rows)
    assert not rows[0]  # deliberately not a full cover!
    # Remainder-one cancellation checked against all phases of a small core.
    ps, length = (2, 3, 5), 61
    for residues in product(*(range(p) for p in ps)):
        correction = 0
        for mask in range(1, 1 << len(ps)):
            subset = [i for i in range(len(ps)) if mask >> i & 1]
            d = prod(ps[i] for i in subset)
            count = sum(all(x % ps[i] == residues[i] for i in subset) for x in range(length))
            e = count - length // d
            assert e == int(all(residues[i] == 0 for i in subset))
            correction += (-1) ** len(subset) * e
        assert correction == -int(any(a == 0 for a in residues))
    print("Six-prime cover19, noncovering disjoint-large-prime example, and all-bit remainder-one identity OK")


def main():
    spec = Path(__file__).with_name("Spec.lean")
    assert sha256(spec.read_bytes()).hexdigest() == SPEC_HASH
    check_records_and_trimming()
    check_exact_pair_union_bound()
    check_block_pair_counterexample()
    check_other_exact_examples()
    print(f"Spec.lean unchanged: {SPEC_HASH}")
    print("No asymptotic Jacobsthal bound is inferred from these checks.")


if __name__ == "__main__":
    main()
