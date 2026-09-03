"""Exact construction audit for CubeParityPentagonResolution.md, section 8.
Not a proof of the unrestricted Ramsey conjecture in Spec.lean.
"""
from itertools import product
from collections import Counter

stats = Counter()

def check(q, binary, k):
    add = lambda a, b: a ^ b if binary else (a + b) % q
    neg = lambda a: a if binary else (-a) % q
    plus = lambda a, b: tuple(add(x, y) for x, y in zip(a, b))
    r = q if binary else (2 if q % 2 == 0 else 1)
    s = r.bit_length() - 1
    def pi(v):
        a = 0
        for i, x in enumerate(v):
            a = add(a, x if i % 2 == 0 else neg(x))
        return a if binary else a % r
    torsion = [a for a in range(q) if add(a, a) == 0]
    assert len(torsion) == r
    args = list(product(range(q), repeat=k))
    P = [tuple(x for a in p for x in (a, a)) for p in args]
    Q = [tuple([neg(b[-1])] + [x for a in b[:-1] for x in (a, a)] + [b[-1]])
         for b in args]
    I = [tuple([a] * (2*k)) for a in torsion]
    assert set(P) & set(Q) == set(I)
    covered, A = set(), []
    for p in P:
        if p not in covered:
            A.append(p)
            covered.update(plus(p, v) for v in I)
    assert covered == set(P)
    assert len(A) == q**k // r
    V = list(product(range(q), repeat=2*k))
    H = {plus(a, b) for a in A for b in Q}
    assert len(H) == len(A) * len(Q)
    assert H == {v for v in V if pi(v) == 0}
    orbit_seen, orbits = {0}, []
    for a in range(1, q):
        if a not in orbit_seen:
            orb = {a, neg(a)}
            orbits.append(orb)
            orbit_seen.update(orb)
    for signs in product((-1, 1), repeat=len(orbits)):
        h = [1]*q
        for orb, sign in zip(orbits, signs):
            for a in orb:
                h[a] = sign
        def red(v):
            value = 1
            for a in v:
                value *= h[a]
            return value == 1
        assert all(red(v) for v in P + Q)
        W, basis = {0}, []
        for v in V:
            if len(W) == r:
                break
            w = pi(v)
            if w not in W and red(v):
                basis.append(v)
                W |= {a ^ w for a in W}
        d = 2 * ((q**k).bit_length() - 1)
        if len(W) == r:
            stats['red cases'] += 1
            da, db = len(A).bit_length()-1, len(Q).bit_length()-1
            assert da + db + s == d
            image = []
            for x in range(1 << d):
                a = A[x & ((1 << da)-1)]
                b = Q[(x >> da) & ((1 << db)-1)]
                z, v = x >> (da+db), plus(a, b)
                for i, lift in enumerate(basis):
                    if (z >> i) & 1:
                        v = plus(v, lift)
                image.append(v)
            colour = True
        else:
            stats['blue cases'] += 1
            char = next(c for c in range(1, r)
                        if all((c & w).bit_count() % 2 == 0 for w in W))
            halves = [[], []]
            for v in V:
                halves[(char & pi(v)).bit_count() % 2].append(v)
            assert len(halves[0]) == len(halves[1]) == len(V)//2
            assert all(not red(v) for v in V
                       if (char & pi(v)).bit_count() % 2)
            image = [halves[x.bit_count() % 2][x >> 1] for x in range(1 << d)]
            colour = False
        assert len(set(image)) == 1 << d
        assert 4 * len(image) > len(V)
        for x, u in enumerate(image):
            for i in range(d):
                y = x ^ (1 << i)
                if x < y:
                    v = image[y]
                    assert u != v
                    difference = tuple(add(a, neg(b)) for a, b in zip(u, v))
                    assert red(difference) == colour, (q, binary, k, signs, x, i)
                    stats['edges'] += 1
        stats['colourings'] += 1
        stats['vertices'] += len(image)
    print('PASS', 'F2^2' if binary else f'Z/{q}', 'k=', k, flush=True)

for q in range(2, 10):
    for k in (1, 2):
        check(q, False, k)
for k in (1, 2):
    check(4, True, k)
print(dict(stats))
