#!/usr/bin/env python3
"""Exact/finite checks for sparse_distance_class_rigidity.md.

The asymptotic probability and rigidity statements are proved in the note.
These checks use exact number-field arithmetic, integer matrices modulo a
prime (with a known characteristic-zero kernel), and literal subset tests.
No distance tolerances, optimizers, or Lean changes are used.
"""
from itertools import combinations, product
from pathlib import Path
import hashlib
import numpy as np
import sympy as sp
from sympy.polys.matrices import DomainMatrix


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def sub(a, b):
    return tuple(x - y for x, y in zip(a, b))


def scale(c, a):
    return tuple(c * x for x in a)


def mul(a, b, m):
    out = [0] * m
    for j, x in enumerate(a):
        for k, y in enumerate(b):
            e = j + k
            out[e % m] += x * y * (2 if e >= m else 1)
    return tuple(out)


def norm(z, m):
    return add(mul(z[:m], z[:m], m), mul(z[m:], z[m:], m))


def field_gadget_check(m):
    E = [tuple(int(j == k) for j in range(m)) for k in range(m)]
    O = (0,) * m
    T = E + [add(a, b) for a, b in combinations(E, 2)]
    pairs = [(a + b, a + scale(-1, b)) for a, b in product(E, E)]
    for x in T:
        pairs.append((x + O, O + x))
        x2 = mul(x, x, m)
        pairs.append((sub(x2, E[0]) + scale(2, x), add(x2, E[0]) + O))
    assert all(norm(v, m) == norm(w, m) for v, w in pairs)
    theta = 2 if m == 1 else 2 ** sp.Rational(1, m)
    K = sp.QQ if m == 1 else sp.QQ.algebraic_field(theta)
    powers = [K.convert(theta ** j) for j in range(m)]

    def element(v):
        return sum((K.convert(c) * e for c, e in zip(v, powers)), K.zero)

    def row(z):
        x, y = element(z[:m]), element(z[m:])
        return [x * c for c in z] + [y * c for c in z]

    rows = [[a - b for a, b in zip(row(v), row(w))] for v, w in pairs]
    C = DomainMatrix(rows, (len(rows), 4*m), K)
    zero = [K.zero] * m
    dilation = powers + zero + zero + powers
    rotation = zero + [-a for a in powers] + powers + zero
    V = DomainMatrix([[a, b] for a, b in zip(dilation, rotation)], (4*m, 2), K)
    assert (C * V).is_zero_matrix
    rank = C.rank()
    assert rank == 4 * m - 2, (m, rank)
    if m > 1:
        deriv = [K.zero] + [K.convert(j) * powers[j - 1] for j in range(1, m)]
        false_derivation = DomainMatrix(
            [[a] for a in deriv + zero + zero + deriv], (4*m, 1), K
        )
        assert not (C * false_derivation).is_zero_matrix
    bound = max(abs(c) for pair in pairs for z in pair for c in z)
    assert bound <= 5
    print(f"field m={m}: {len(rows)} exact norm identities; "
          f"infinitesimal rank={rank}/{4*m}, nullity=2; max coefficient={bound}")


def modular_rank(A, p=1000003):
    A = np.asarray(A, dtype=np.int64) % p
    nrows, ncols = A.shape
    r = 0
    for j in range(ncols):
        nz = np.flatnonzero(A[r:, j])
        if not len(nz):
            continue
        k = r + int(nz[0])
        A[[r, k], :] = A[[k, r], :]
        A[r, j:] = (A[r, j:] * pow(int(A[r, j]), p - 2, p)) % p
        idx = np.flatnonzero(A[r + 1:, j]) + r + 1
        if len(idx):
            A[idx, j:] = (A[idx, j:] - A[idx, j, None] * A[r, j:]) % p
        r += 1
        if r == nrows:
            break
    return r


def colored_matrix(points):
    n = len(points)
    reps = {}
    rows = []
    for i, j in combinations(range(n), 2):
        h = sub(points[i], points[j])
        d = sum(x * x for x in h)
        row = np.zeros(2 * n, dtype=np.int64)
        row[2*i:2*i+2] = h
        row[2*j:2*j+2] = [-x for x in h]
        if d not in reps:
            reps[d] = row
        else:
            rows.append(row - reps[d])
    return np.asarray(rows), len(reps)


def planar_rank_check(points, label):
    A, D = colored_matrix(points)
    n = len(points)
    V = []
    for x, y in points:
        V.extend(([1, 0, x, -y], [0, 1, y, x]))
    V = np.asarray(V, dtype=np.int64)
    assert not np.any(A @ V)
    assert sp.Matrix(V.tolist()).rank() == 4
    rank = modular_rank(A)
    # The exact integer kernel has dimension >=4. The modular minor gives
    # characteristic-zero rank >=2n-4, so the actual rational rank is exact.
    assert rank == 2 * n - 4
    print(f"{label}: n={n}, D={D}, exact colored rank={rank}, nullity=4")


def exists_joint(A, shifts):
    """Does some a satisfy A[a+s] for every integer 2D shift s?"""
    lo = [max(-s[j] for s in shifts) for j in range(2)]
    hi = [min(A.shape[j] - s[j] for s in shifts) for j in range(2)]
    if any(lo[j] >= hi[j] for j in range(2)):
        return False
    test = np.ones((hi[0]-lo[0], hi[1]-lo[1]), dtype=bool)
    for sx, sy in shifts:
        test &= A[lo[0]+sx:hi[0]+sx, lo[1]+sy:hi[1]+sy]
    return bool(np.any(test))


def certificate_check(ell, density, seed):
    # Coefficient box [0,2M]^2, a translate of the centered box in the note.
    M = 100
    H = M // 10
    rng = np.random.default_rng(seed)
    S = rng.random((2*M+1, 2*M+1)) < density
    L = 2*M + 1 - ell
    A = np.ones((L, L), dtype=bool)
    G = list(product(range(ell+1), repeat=2))
    for x, y in G:
        A &= S[x:x+L, y:y+L]
    assert np.any(A)
    demands = 0
    max_size = 0
    for h in product(range(-H, H+1), repeat=2):
        for e in [(1, 0), (0, 1)]:
            he = add(h, e)
            assert exists_joint(A, [(0, 0), h, he]), (ell, h, e)
            U = set(G) | {add(h, u) for u in G} | {add(he, u) for u in G}
            max_size = max(max_size, len(U))
            demands += 1
    # Check the actual deterministic conditions: short-step connectivity
    # and an anchor net. The proof obtains them via occupied coarse cells;
    # checking them directly avoids a needlessly strong finite-size demand.
    anchors = [tuple(map(int, p)) for p in np.argwhere(A)]
    buckets = {}
    for k, p in enumerate(anchors):
        buckets.setdefault((p[0]//H, p[1]//H), []).append(k)
    reached = {0}
    queue = [0]
    for k in queue:
        p = anchors[k]
        b = (p[0]//H, p[1]//H)
        for dx, dy in product(range(-1, 2), repeat=2):
            for j in buckets.get((b[0]+dx, b[1]+dy), []):
                if j not in reached and max(abs(t) for t in sub(p, anchors[j])) <= H:
                    reached.add(j)
                    queue.append(j)
    assert len(reached) == len(anchors)
    # A point within H-1 of an anchor is within H of all three anchors
    # a, a+e1, a+e2. Prefix sums make these literal integer-box tests fast.
    pref = np.pad(A.astype(np.int64), ((1, 0), (1, 0))).cumsum(0).cumsum(1)
    for p in product(range(2*M+1), repeat=2):
        lo = [max(0, t-(H-1)) for t in p]
        hi = [min(L, t+(H-1)+1) for t in p]
        count = (pref[hi[0], hi[1]] - pref[lo[0], hi[1]]
                 - pref[hi[0], lo[1]] + pref[lo[0], lo[1]])
        assert count > 0, (ell, p)
    assert max_size <= 3 * (ell+1)**2
    print(f"literal certificate ell={ell}: N={S.size}, retained={int(S.sum())}, "
          f"anchors={int(A.sum())}, triple demands={demands}, "
          f"connected anchors and full-box net; max union size={max_size}; PASS")


def main():
    spec = Path(__file__).with_name('Spec.lean')
    expected_hash = 'c2fbaabe5ad8088f856ca97625747c7a01754f3c149dd6a493454e776de290db'
    assert hashlib.sha256(spec.read_bytes()).hexdigest() == expected_hash
    for m in [1, 3, 5, 7]:
        field_gadget_check(m)
    planar_rank_check(list(product(range(2), repeat=2)), 'single unit square')
    planar_rank_check(list(product(range(3), repeat=2)), '3x3 unit patch')
    rng = np.random.default_rng(20260829)
    sample = [p for p in product(range(11), repeat=2) if rng.random() < .72]
    planar_rank_check(sample, 'independent thinned integer grid')
    certificate_check(ell=1, density=.65, seed=410)
    certificate_check(ell=2, density=.78, seed=411)
    print('Spec.lean SHA-256 unchanged:', expected_hash)
    print('ALL SPARSE DISTANCE-CLASS RIGIDITY CHECKS PASSED')


if __name__ == '__main__':
    main()
