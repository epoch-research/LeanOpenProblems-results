#!/usr/bin/env python3
"""Exact audits of proved identities/constructions, NOT an embedding search."""
from itertools import product
from fractions import Fraction
from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SPEC_HASH = "9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b"


def h(x):
    return 1 if x % 5 in (0, 1, 4) else -1


def sign(x, y):
    out = 1
    for a, b in zip(x, y):
        out *= h(a - b)
    return out


def rank_mod(A, p):
    A = [[x % p for x in row] for row in A]
    r = 0
    for j in range(len(A[0])):
        pivot = next((i for i in range(r, len(A)) if A[i][j]), None)
        if pivot is None:
            continue
        A[r], A[pivot] = A[pivot], A[r]
        scale = pow(A[r][j], -1, p)
        A[r] = [(scale*x) % p for x in A[r]]
        for i in range(len(A)):
            if i != r:
                z = A[i][j]
                A[i] = [(a-z*b) % p for a, b in zip(A[i], A[r])]
        r += 1
        if r == len(A):
            break
    return r


# Entries are rows; columns are the monochromatic line directions.
BLOCKS = {
    1: {2: [[1, 1], [1, -1]],
        3: [[1, 0, 1], [1, 1, 0], [0, 1, 1]]},
    -1: {2: [[1, 1], [2, -2]],
         3: [[1, 0, 2], [2, 1, 0], [0, 2, 1]]},
}


def matrix(t, colour):
    assert t >= 2
    sizes = ([3] if t % 2 else []) + [2] * ((t - 3) // 2 if t % 2 else t // 2)
    A = [[0] * t for _ in range(t)]
    offset = 0
    for k in sizes:
        for i, row in enumerate(BLOCKS[colour][k]):
            for j, x in enumerate(row):
                A[offset+i][offset+j] = x % 5
        offset += k
    assert offset == t and rank_mod(A, 5) == t
    return A


def embedding(A, word):
    t = len(A)
    z = [((word >> (2*i)) & 1) + 2*((word >> (2*i+1)) & 1) for i in range(t)]
    return tuple(sum(a*b for a, b in zip(row, z)) % 5 for row in A)


def matmul(A, B):
    return [[sum(a*b for a, b in zip(row, col)) for col in zip(*B)] for row in A]


def polynomial_at_matrix(A, coeffs):
    n = len(A)
    I = [[int(i == j) for j in range(n)] for i in range(n)]
    out = [[0] * n for _ in range(n)]
    power = I
    for c in coeffs:
        out = [[x+c*y for x, y in zip(row, prow)] for row, prow in zip(out, power)]
        power = matmul(power, A)
    return out


def main():
    assert sha256((ROOT / 'Spec.lean').read_bytes()).hexdigest() == SPEC_HASH
    H = [[h(a-b) for b in range(5)] for a in range(5)]
    assert all(sum(row) == 1 for row in H)
    # (X-1)(X^2-2X-4) = X^3 - 3X^2 - 2X + 4.
    assert polynomial_at_matrix(H, [4, -2, -3, 1]) == [[0]*5 for _ in range(5)]
    H2 = matmul(H, H)
    assert sum(H[i][i] for i in range(5)) == 5
    assert sum(H2[i][i] for i in range(5)) == 25
    # Dimension, these two traces, and the distinct-root annihilator
    # give multiplicities 1,2,2 (trace alone would not suffice).
    print('PASS base row sums, traces of H and H^2, and exact spectral polynomial; eigenvalue multiplicities 1,2,2.')

    G = [[int(h(a-b) == -1) for b in range(4)] for a in range(4)]
    assert rank_mod(G, 2) == 4
    phi = [tuple(int(i == j) for i in range(4)) for j in range(4)] + [(1, 1, 1, 1)]
    def B(x, y):
        return sum(x[i]*G[i][j]*y[j] for i in range(4) for j in range(4)) % 2
    for a, b in product(range(5), repeat=2):
        assert B(phi[a], phi[b]) == int(h(a-b) == -1)
    for subset in __import__('itertools').combinations(phi, 4):
        assert any(sum(v[i] for v in subset) % 2 for i in range(4))
    print('PASS all 25 symplectic Gram identities; rank 4; no affine 2-plane in the five-point alphabet.')

    for colour in (1, -1):
        for k in (2, 3):
            A = BLOCKS[colour][k]
            assert rank_mod(A, 5) == k
            for col in zip(*A):
                for a in range(1, 5):
                    assert sign(tuple(a*x % 5 for x in col), (0,)*k) == colour
    print('PASS 2- and 3-dimensional block bases, all nonzero line multiples in their declared colour.')

    total_edges = 0
    for t in range(2, 8):
        for colour in (1, -1):
            A = matrix(t, colour)
            images = [embedding(A, w) for w in range(1 << (2*t))]
            assert len(set(images)) == len(images)
            edges = 0
            for w, image in enumerate(images):
                for bit in range(2*t):
                    if not (w >> bit) & 1:
                        assert sign(image, images[w ^ (1 << bit)]) == colour
                        edges += 1
            assert edges == t * (1 << (2*t))
            total_edges += edges
        print(f'PASS t={t}: both explicit Q_{2*t}, {1 << (2*t)} vertices each, every edge checked.')
    print(f'PASS {total_edges} explicit cube edges checked in total.')

    for t in range(1, 6):
        words = list(product(range(5), repeat=t))
        row = [sign((0,)*t, w) for w in words]
        assert sum(row) == 1
        assert row.count(-1) == (5**t-1)//2
        assert row.count(1)-1 == (5**t-1)//2
    print('PASS exact half-degrees for t=1,...,5, with red diagonal removed.')

    # Exact arithmetic in Q(sqrt(5)) for the affine obstruction's Fourier values.
    def add(x, y):
        return (x[0]+y[0], x[1]+y[1])
    def mul(x, y):
        return (x[0]*y[0]+5*x[1]*y[1], x[0]*y[1]+x[1]*y[0])
    one, two = (Fraction(1), Fraction(0)), (Fraction(2), Fraction(0))
    a = (Fraction(-1, 2), Fraction(1, 2))
    cos72 = (Fraction(-1, 4), Fraction(1, 4))
    cos144 = (Fraction(-1, 4), Fraction(-1, 4))
    assert add(one, mul(two, a)) == (0, 1)
    assert add(one, mul(mul(two, a), cos72)) == (Fraction(5, 2), Fraction(-1, 2))
    assert add(one, mul(mul(two, a), cos144)) == (0, 0)
    print('PASS exact Fourier values sqrt(5), (5-sqrt(5))/2, 0 for the kernel bound.')

    # A red source square has nonzero coordinatewise integer winding.
    square = [(i, i) for i in range(4)]
    assert all(sign(square[i], square[(i+1) % 4]) == 1 for i in range(4))
    increments = [((square[(i+1) % 4][0] - square[i][0] + 2) % 5) - 2 for i in range(4)]
    assert increments == [1, 1, 1, 2] and sum(increments) == 5
    print('PASS legal red square with coordinate increment sum 5: no torus-style integer lift.')
    print('Spec.lean SHA-256:', SPEC_HASH)
    print('NO SEARCH performed. These audits do not assert an all-map dimension bound or settle the endpoint.')


if __name__ == '__main__':
    main()
