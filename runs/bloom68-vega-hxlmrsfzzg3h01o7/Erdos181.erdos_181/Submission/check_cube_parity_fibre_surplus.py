#!/usr/bin/env python3
"""Exact checks for the fibre-surplus theorem; no embedding search.

The all-dimensional statements are proved in CubeParityFibreSurplus.md.
This checks the finite local inequalities and the audited sharp examples.
The base-five encodings below are deliberately UNCOLOURED controls.
"""
from itertools import combinations, product
from collections import Counter, defaultdict
from hashlib import sha256
from pathlib import Path


def h(a):
    return 1 if a % 5 in (0, 1, 4) else -1


def sign(x, y):
    ans = 1
    for a, b in zip(x, y):
        ans *= h(a - b)
    return ans


def cube_edges(d):
    for v in range(1 << d):
        for j in range(d):
            if not (v >> j) & 1:
                yield v, v ^ (1 << j)


def induced_edges(S):
    return [(u, v) for u, v in combinations(S, 2)
            if (u ^ v).bit_count() == 1]


def local_cube_checks():
    # Exhaustive local sanity check, not the proof for arbitrary d.
    maxima = []
    checked = 0
    for k in range(6):
        best = 0
        for S in combinations(range(16), k):
            E = induced_edges(S)
            assert len(E) <= k
            best = max(best, len(E))
            if k and len(E) == k:
                degrees = sorted(sum(v in e for e in E) for v in S)
                assert ((k == 4 and degrees == [2, 2, 2, 2]) or
                        (k == 5 and degrees == [1, 2, 2, 2, 3]))
            checked += 1
        maxima.append(best)
    assert maxima == [0, 0, 1, 2, 4, 5]
    print('Q4 local subsets checked:', checked, '; edge maxima:', maxima)


def bipartite(V, E):
    col = {}
    adj = {v: [] for v in V}
    for u, v in E:
        adj[u].append(v)
        adj[v].append(u)
    for root in V:
        if root in col:
            continue
        col[root] = 0
        todo = [root]
        while todo:
            u = todo.pop()
            for v in adj[u]:
                if v in col:
                    if col[v] == col[u]:
                        return False
                else:
                    col[v] = 1 - col[u]
                    todo.append(v)
    return True


def pentagon_checks():
    checked = 0
    for c in (1, -1):
        E0 = [(u, v) for u, v in combinations(range(5), 2)
              if h(u-v) == c]
        assert len(E0) == 5
        for mask in range(1, 32):
            V = [v for v in range(5) if (mask >> v) & 1]
            allowed = [e for e in E0 if all(v in V for v in e)]
            for emask in range(1 << len(allowed)):
                E = [e for j, e in enumerate(allowed) if (emask >> j) & 1]
                if bipartite(V, E):
                    assert len(E) <= len(V) - 1
                checked += 1
    print('Pentagon vertex/edge subgraphs checked in both colours:', checked)


def matrix(t, c):
    R2 = [[1, 1], [1, 4]]
    B2 = [[1, 1], [2, 3]]
    R3 = [[1, 0, 1], [1, 1, 0], [0, 1, 1]]
    B3 = [[1, 0, 2], [2, 1, 0], [0, 2, 1]]
    blocks = []
    if t % 2:
        blocks.append(R3 if c == 1 else B3)
    blocks += [R2 if c == 1 else B2] * ((t - (3 if t % 2 else 0)) // 2)
    M = [[0] * t for _ in range(t)]
    off = 0
    for B in blocks:
        for i in range(len(B)):
            for j in range(len(B)):
                M[off+i][off+j] = B[i][j]
        off += len(B)
    assert off == t
    return M


def mv(M, x):
    return tuple(sum(a*b for a, b in zip(row, x)) % 5 for row in M)


def audit_fibres(F, d):
    assert len(F) == 1 << d and len(set(F)) == len(F)
    t, m = len(F[0]), len(F)
    groups = [defaultdict(list) for _ in range(t)]
    for v, x in enumerate(F):
        for i in range(t):
            groups[i][x[:i] + x[i+1:]].append(v)
    defect = 0
    good_from_fibres = 0
    occupied = []
    for G in groups:
        occupied.append(len(G))
        for S in G.values():
            assert len(S) <= 5
            e = len(induced_edges(S))
            assert e <= len(S)
            good_from_fibres += e
            defect += len(S) - e
    good = sum(sum(a != b for a, b in zip(F[u], F[v])) == 1
               for u, v in cube_edges(d))
    assert good == good_from_fibres
    extra = d*m//2 - good
    assert extra == m*(d-2*t)//2 + defect
    assert extra >= m*(d-2*t)//2
    return extra, defect, occupied


def sharp_examples():
    for t in range(2, 6):
        d, m = 2*t, 1 << (2*t)
        Z = [tuple(((v >> (2*i)) & 1) + 2*((v >> (2*i+1)) & 1)
                   for i in range(t)) for v in range(m)]
        extra, defect, _ = audit_fibres(Z, d)
        assert extra == defect == 0
        for c in (1, -1):
            F = [mv(matrix(t, c), z) for z in Z]
            assert len(set(F)) == m
            assert all(sign(F[u], F[v]) == c for u, v in cube_edges(d))
            original_extra, _, occupied = audit_fibres(F, d)
            # Every monochromatic pentagon fibre is a forest in the source.
            assert original_extra >= m*(d-2*t)//2 + sum(occupied)
            assert original_extra >= m*(d-2*t)//2 + t*((m+4)//5)
            print('Sharp audited cube:', 'red' if c == 1 else 'blue',
                  't=', t, 'd=', d, 'vertices=', m,
                  'all edges checked=', d*m//2,
                  'basis-extra=', extra, 'basis-defect=', defect)


def uncoloured_control():
    # This is NOT a monochromatic Q9 certificate.
    d, t = 9, 4
    F = [tuple((v // (5**i)) % 5 for i in range(t)) for v in range(1 << d)]
    extra, defect, _ = audit_fibres(F, d)
    colours = Counter(sign(F[u], F[v]) for u, v in cube_edges(d))
    assert colours[1] and colours[-1]
    assert extra == 256 + defect
    print('UNCOLOURED base-five Q9 injection:',
          'extra=', extra, 'defect=', defect, 'edge colours=', dict(colours))
    print('Theorem requirements for monochromatic Q9 at t=4:',
          'at least 256 edges outside any fixed Hamming basis;',
          'at least 668 edges changing >=2 ORIGINAL coordinates.')


def main():
    local_cube_checks()
    pentagon_checks()
    sharp_examples()
    uncoloured_control()
    spec = Path(__file__).with_name('Spec.lean')
    digest = sha256(spec.read_bytes()).hexdigest()
    assert digest == '9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b'
    print('Spec.lean unchanged; SHA-256:', digest)
    print('PASS: exact local and construction checks; no embedding search.')


if __name__ == '__main__':
    main()
