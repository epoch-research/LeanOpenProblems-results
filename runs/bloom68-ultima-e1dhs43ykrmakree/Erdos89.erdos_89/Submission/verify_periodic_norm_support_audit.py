#!/usr/bin/env python3
"""Exact finite checks for periodic_norm_support_audit.md. Standard library only.
All inequalities and local masses are integer/Fraction calculations; no numerical
asymptotic inference. Run from any directory with python3.
"""
from fractions import Fraction as F
from itertools import combinations, product
from math import gcd, isqrt, lcm
from random import Random


def factors(n):
    ans = []
    p = 2
    while p * p <= n:
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        if e:
            ans.append((p, e))
        p += 1
    if n > 1:
        ans.append((n, 1))
    return ans


def vp(n, p, cap):
    if n == 0:
        return cap
    v = 0
    while v < cap and n % p == 0:
        n //= p
        v += 1
    return v


def vpi(a, b, cap):
    t = 0
    while t < cap and (a - b) % 2 == 0:
        a, b = (a + b) // 2, (b - a) // 2
        t += 1
    return t


def norm_cylinder(a, b, p, e):
    """Within the local norm support, image is n == a^2+b^2 mod q."""
    if p != 2:
        h = e + min(vp(a, p, e), vp(b, p, e))
    else:
        t = vpi(a, b, 2 * e)
        h = 2 * e if t == 2 * e else t + max(2, (2 * e - t) // 2 + 1)
    q = p ** h
    return q, (a * a + b * b) % q


def mu_residue(a, p, h):
    """Landau-support probability of a mod p^h, not representation weight."""
    q = p ** h
    a %= q
    if p % 4 == 1:
        return F(1, q)
    if not a:
        return F(1, 2 ** h if p == 2 else p ** (2 * ((h + 1) // 2)))
    t = vp(a, p, h)
    if p == 2:
        k = h - t
        if k == 1:
            return F(1, 2 ** h)
        return F(2, 2 ** h) if (a >> t) % 4 == 1 else F(0)
    return F(p + 1, p ** (h + 1)) if t % 2 == 0 else F(0)


def local_table(M):
    fs = factors(M)
    hs = [(p, 2 * e + (p == 2)) for p, e in fs]
    J = M * M * (2 if M % 2 == 0 else 1)
    points = list(product(range(M), repeat=2))
    conditions = [[norm_cylinder(a, b, p, e) for p, e in fs] for a, b in points]
    atoms = []
    for t in range(J):
        w = F(1)
        for p, h in hs:
            w *= mu_residue(t, p, h)
        if not w:
            continue
        mask = sum(1 << j for j, cs in enumerate(conditions)
                   if all(t % q == c for q, c in cs))
        atoms.append((mask, w))
    assert sum(w for _, w in atoms) == 1
    den = lcm(*(w.denominator for _, w in atoms))
    atoms_int = [(mask, int(w * den)) for mask, w in atoms]
    return points, atoms_int, den


def difference_mask(A, M):
    return sum(1 << j for j in {
        ((a - c) % M) * M + ((b - d) % M)
        for a, b in A for c, d in A})


def lambda_of(Bmask, atoms, den):
    return F(sum(w for mask, w in atoms if mask & Bmask), den)


def gap_bound(A, M):
    split = [(p, e) for p, e in factors(M) if p % 4 == 1]
    L = 1
    roots = []
    for p, e in split:
        q = p ** e
        s = next(s for s in range(q) if (s * s + 1) % q == 0)
        roots.append((q, s))
        L *= q
    counts = {}
    for a, b in A:
        y = sum(((a - s * b) % q) * (L // q) * pow(L // q, -1, q)
                for q, s in roots) % L
        counts[y] = counts.get(y, 0) + 1
    occupied = sorted(counts)
    best = None
    for j, r in enumerate(occupied):
        g = (occupied[(j + 1) % len(occupied)] - r) % L or L
        f = F(counts[r] * L, M * M)
        if best is None or f / g > best[0]:
            cg = F(1)
            for p, _ in split:
                gg = g
                while gg % p == 0:
                    cg /= p
                    gg //= p
            best = (f / g, f * cg, r, g)
    assert best[0] >= F(len(A), M * M)
    return best


def check_local_images():
    count = 0
    for p, e in [(2, 1), (2, 2), (2, 3), (3, 1), (3, 2),
                 (5, 1), (5, 2), (7, 1), (13, 1)]:
        m = p ** e
        h = 2 * e + (p == 2)
        q = p ** h
        images = [set() for _ in range(m * m)]
        for a in range(q):
            for b in range(q):
                images[(a % m) * m + b % m].add((a * a + b * b) % q)
        positive = {n for n in range(q) if mu_residue(n, p, h)}
        for a, b in product(range(m), repeat=2):
            qq, c = norm_cylinder(a, b, p, e)
            expected = {n for n in positive if n % qq == c}
            assert images[a * m + b] == expected, (p, e, a, b)
            count += 1
    print('Local norm-cylinder images: exact lift enumeration passed for', count,
          'Gaussian residue classes (including 2-adic extra precision).')


def check_masks():
    for M in range(1, 5):
        points, atoms, den = local_table(M)
        least = None
        for mask in range(1, 1 << (M * M)):
            A = [p for j, p in enumerate(points) if mask >> j & 1]
            lam = lambda_of(difference_mask(A, M), atoms, den)
            delta = F(len(A), M * M)
            assert lam >= delta
            ratio = lam / delta
            least = ratio if least is None else min(least, ratio)
        print(f'All {2**(M*M)-1} nonempty masks mod {M}: lambda >= delta; min lambda/delta = {least}.')
    # Split-prime sparse masks and their dense complements, plus arbitrary CRT correlations.
    M = 5
    points, atoms, den = local_table(M)
    total = 0
    for k in range(1, 5):
        for ids in combinations(range(25), k):
            chosen = set(ids)
            for A in ([points[j] for j in ids], [points[j] for j in range(25) if j not in chosen]):
                lam = lambda_of(difference_mask(A, M), atoms, den)
                gap = gap_bound(A, M)
                assert lam >= gap[1] >= gap[0] >= F(len(A), 25)
                total += 1
    print(f'Mod 5: {total} sparse/dense masks, including the stronger selected-gap bound, passed.')
    rng = Random(20260830)
    total = 0
    for M in [6, 8, 10, 12, 13, 15, 20, 25, 30, 65]:
        points, atoms, den = local_table(M)
        for _ in range(80 if M < 30 else 20):
            k = rng.randrange(1, min(len(points), 50) + 1)
            A = rng.sample(points, k)
            lam = lambda_of(difference_mask(A, M), atoms, den)
            gap = gap_bound(A, M)
            assert lam >= gap[1] >= gap[0] >= F(k, M * M), (M, A, lam, gap)
            total += 1
    print(f'{total} seeded correlated prime-power/mixed-modulus masks passed; mod 65 uses two split primes.')


def mul(x, y, M):
    a, b = x
    c, d = y
    return ((a * c - b * d) % M, (a * d + b * c) % M)


def unit_orbit(x, M):
    a, b = x
    return {(a % M, b % M), (-b % M, a % M), (-a % M, -b % M), (b % M, -a % M)}


def check_hilbert90():
    for M in [2, 3, 4, 5, 6, 8, 9, 10, 12, 13, 16, 20, 25, 30, 65]:
        fs = factors(M)
        G = [(a, b) for a, b in product(range(M), repeat=2) if gcd(a * a + b * b, M) == 1]
        image = set()
        for a, b in G:
            inv = pow(a * a + b * b, -1, M)
            d = ((a * a - b * b) * inv % M, 2 * a * b * inv % M)
            image.update(unit_orbit(d, M))
        local = {z for z in G if all(1 % q == c for q, c in
                                   (norm_cylinder(*z, p, e) for p, e in fs))}
        assert image == local
        if M in [4, 8, 13, 65]:
            print(f'Mod {M}: |G|={len(G)}, |local norm-one reductions|={len(local)}, '
                  f'|H|={len({min(unit_orbit(z, M)) for z in local})}.')
    # Finite norm mod 4 is too weak: this is NOT a genuine local norm-1 residue.
    assert (1 * 1 + 2 * 2) % 4 == 1
    assert norm_cylinder(1, 2, 2, 2) == (8, 5)
    print('Hilbert-90/unit correction verified exactly, including ramification at 2.')


def representations(n):
    r = isqrt(n)
    return {(a, b) for a in range(-r, r + 1) for b in range(-r, r + 1)
            if a * a + b * b == n}


def check_saturation_examples():
    M = 13
    b = (2, 6)
    points, atoms, den = local_table(M)
    B = {(0, 0), b, (-b[0] % M, -b[1] % M)}
    Bmask = sum(1 << (a * M + c) for a, c in B)
    assert lambda_of(Bmask, atoms, den) == F(14, 169)
    assert norm_cylinder(*b, 13, 1) == (13, 1)
    for n in [1, 313, 677]:
        assert n % 13 == 1
        assert not any((a % M, c % M) in B for a, c in representations(n))
    # Two distinct rational primes, generators in the same ray class [2+i].
    assert 5 == 2**2 + 1**2 and 421 == 15**2 + 14**2
    assert (15 % 13, 14 % 13) == (2, 1)
    n = 5 * 421
    actual = {(a % M, c % M) for a, c in representations(n)}
    local = {(a, c) for a, c in product(range(M), repeat=2) if (a * a + c * c - n) % M == 0}
    assert len(actual) == 12 and actual == local
    print('Mod 13: lambda({0,+/-(2+6i)})=14/169; genuine local exceptions 1,313,677 verified.')
    print('Orientation switch packet 2105=5*421: all 12 locally admissible unit residues attained.')
    X = 1_000_000
    r = isqrt(X)
    support = bytearray(X + 1)
    for a in range(r + 1):
        for c in range(isqrt(X - a * a) + 1):
            support[a * a + c * c] = 1
    support[0] = 0
    actual = bytearray(X + 1)
    for a0, c0 in B:
        amin = -r + (a0 + r) % M
        cmin = -r + (c0 + r) % M
        for a in range(amin, r + 1, M):
            for c in range(cmin, r + 1, M):
                n = a * a + c * c
                if 0 < n <= X:
                    actual[n] = 1
    checkpoints = {1, 39, 40, 1000, 10000, 100000, X}
    s = loc = act = 0
    print('Exact mod-13 population: X, S(X), locally admissible, actual F_B(X), missing')
    for n in range(1, X + 1):
        admissible = bool(support[n] and (n % 13 == 1 or n % 169 == 0))
        assert not actual[n] or admissible
        s += support[n]
        loc += admissible
        act += actual[n]
        if n in checkpoints:
            print(n, s, loc, act, loc - act)


def check_disk_sandwich():
    rng = Random(91)
    count = 0
    for M in [1, 2, 3, 5, 8, 13]:
        for R in [4, 10, 20]:
            residues = list(product(range(M), repeat=2))
            A = set(rng.sample(residues, min(7, len(residues))))
            B = {((a-c) % M, (b-d) % M) for a,b in A for c,d in A}
            P = [(a,b) for a in range(-R,R+1) for b in range(-R,R+1)
                 if a*a+b*b <= R*R and (a % M,b % M) in A]
            differences = {(a-c,b-d) for a,b in P for c,d in P}
            # Avoid floating sqrt(2): use the slightly weaker certified margin 2M.
            inner = max(0, 2*R-2*M)
            for a in range(-inner,inner+1):
                for b in range(-inner,inner+1):
                    if a*a+b*b <= inner*inner and (a % M,b % M) in B:
                        assert (a,b) in differences
            assert all((a % M,b % M) in B and a*a+b*b <= 4*R*R for a,b in differences)
            count += 1
    print(f'Actual endpoint/difference disk inclusions passed for {count} finite periodic disks.')


def check_small_modulus_exact_saturation():
    X = 5000
    checked = 0
    for M in range(1,6):
        r = isqrt(X)
        actual = [0]*(X+1)
        for a,b in product(range(-r,r+1),repeat=2):
            n = a*a+b*b
            if 0 < n <= X:
                actual[n] |= 1 << ((a % M)*M+b % M)
        conditions = [[norm_cylinder(a,b,p,e) for p,e in factors(M)]
                      for a,b in product(range(M),repeat=2)]
        for n in range(1,X+1):
            if actual[n]:
                expected = sum(1 << j for j,cs in enumerate(conditions)
                               if all(n % q == c for q,c in cs))
                assert actual[n] == expected, (M,n)
            checked += 1
    print(f'Exact saturation for every residue mod M=1,...,5 and every norm n<=5000: {checked} checks passed.')



def check_finite_gap_and_height():
    rng = Random(1908)
    checked = 0
    for L in [5, 13, 25, 65]:
        roots = []
        for p, e in factors(L):
            q = p ** e
            s = next(s for s in range(q) if (s*s + 1) % q == 0)
            roots.append((q, s, (L // q) * pow(L // q, -1, q)))
        def xy(z):
            a, b = z
            return (sum((a+s*b)*c for q,s,c in roots) % L,
                    sum((a-s*b)*c for q,s,c in roots) % L)
        for _ in range(100):
            P = rng.sample(list(product(range(-12,13), repeat=2)), 30)
            fibers = {}
            for z in P:
                fibers.setdefault(xy(z)[1], []).append(z)
            occupied = sorted(fibers)
            if len(occupied) < 2:
                continue
            choices = []
            for j, r in enumerate(occupied):
                nxt = occupied[(j+1) % len(occupied)]
                g = (nxt-r) % L
                choices.append((F(len(fibers[r]),g),r,nxt,g))
            _, r, nxt, g = max(choices)
            assert F(len(fibers[r]),g) >= F(len(P),L)
            b = fibers[nxt][0]
            d = gcd(g,L)
            xlabels = {xy(a)[0] % (L//d) for a in fibers[r]}
            labels = {(a[0]-b[0])**2+(a[1]-b[1])**2 for a in fibers[r]}
            assert len(labels) >= len(xlabels)
            for a in fibers[r]:
                N = (a[0]-b[0])**2+(a[1]-b[1])**2
                assert (N + g*(xy(a)[0]-xy(b)[0])) % L == 0
            for a,c in product(fibers[r], repeat=2):
                if (xy(a)[0]-xy(c)[0]) % (L//d) == 0:
                    assert ((a[0]-c[0])**2+(a[1]-c[1])**2) % (L*L//d) == 0
            checked += 1
    print(f'Actual finite cyclic-gap/residue-injection and large-ideal partitions: {checked} checks passed.')
    for p in [101, 1009, 10009]:
        assert p % 4 == 1 and all(p % d for d in range(2,isqrt(p)+1))
        r = p//5
        H = r+1
        P = [0,1,r,r+1]
        assert p > 4*H and gcd(*(a for a in P)) == 1
        differences = {a-b for a in P for b in P}
        D = {d*d for d in differences if d}
        assert len(D) == 4
        B = {d % p for d in differences}
        Factual = {a*a+b*b for a0 in B for j,k in product(range(-1,2),repeat=2)
                   for a,b in [(a0+j*p,k*p)] if 0 < a*a+b*b <= 4*H*H}
        assert Factual == D
        lam = F(len({d*d % p for d in differences if d}),p)+F(1,p*p)
        assert lam >= F(1,p)
        print(f'Primitive height obstruction: M={p}, R={H}, n=4, F_B(4R^2)=4, lambda={lam}.')



def main():
    check_local_images()
    check_masks()
    check_hilbert90()
    check_saturation_examples()
    check_disk_sandwich()
    check_small_modulus_exact_saturation()
    check_finite_gap_and_height()
    print('ALL EXACT CHECKS PASSED. These finite checks do not establish an asymptotic or a uniform contraction.')


if __name__ == '__main__':
    main()
