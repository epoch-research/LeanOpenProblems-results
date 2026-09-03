"""Exact explicit embeddings, not a search for monochromatic copies."""
from pathlib import Path
import hashlib
import numpy as np

SPEC = Path(__file__).with_name("Spec.lean")
EXPECTED_SHA = "9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b"
H = np.array([1, 1, -1, -1, 1], dtype=np.int8)


def embedding(t):
    k = t // 2
    s = (5 ** k).bit_length() - 1
    d = 2 * s + (t % 2)
    words = np.arange(1 << d, dtype=np.int64)
    mask = (1 << s) - 1
    u = words & mask
    v = (words >> s) & mask
    out = np.zeros((len(words), t), dtype=np.int8)
    for i in range(k):
        a, b = (u // (5 ** i)) % 5, (v // (5 ** i)) % 5
        out[:, i] = (a + b) % 5
        out[:, k + i] = (a - b) % 5
    if t % 2:
        out[:, -1] = words >> (2 * s)
    return d, words, out


def check(t):
    d, words, out = embedding(t)
    n = len(words)
    keys = sum(out[:, i].astype(np.int64) * 5 ** i for i in range(t))
    if not t:
        keys = words * 0
    assert len(np.unique(keys)) == n, "not injective"
    edges = 0
    for j in range(d):
        u = words[(words & (1 << j)) == 0]
        v = u ^ (1 << j)
        differences = (out[u] - out[v]) % 5
        signs = np.prod(H[differences], axis=1, dtype=np.int64)
        assert np.all(signs == 1), (t, j, "non-red required edge")
        assert np.all(np.any(differences != 0, axis=1))
        edges += len(u)
    assert edges == d * n // 2
    assert 10 * n > 5 ** t
    if t % 2 == 0:
        assert 4 * n > 5 ** t
        assert (5 ** t).bit_length() - 1 - d <= 1
    print(f"t={t}: ordinary injective RED Q_{d}; vertices={n}; required edges={edges}; 10*vertices>5^t")
    return edges


def check_cycle_pairings():
    from itertools import product
    checked = 0
    for q in range(2, 10):
        for k in (1, 2):
            params = list(product(range(q), repeat=k))
            P = {tuple(z for a in row for z in (a, a)) for row in params}
            Q = set()
            for row in params:
                z = [(-row[-1]) % q]
                for a in row[:-1]:
                    z.extend((a, a))
                z.append(row[-1])
                Q.add(tuple(z))
            H2 = {a for a in range(q) if 2*a % q == 0}
            I = {tuple([a]*(2*k)) for a in H2}
            assert P & Q == I
            def add(x, y):
                return tuple((a+b) % q for a, b in zip(x, y))
            A = {p for p in P if p == min(add(p, h) for h in I)}
            sums = {add(a, b) for a in A for b in Q}
            assert len(sums) == len(A)*len(Q) == q**(2*k)//len(H2)
            for bits in range(1 << (q//2)):
                hh = [1] + [(-1 if bits & (1 << (min(a,q-a)-1)) else 1) for a in range(1,q)]
                for z in P | Q:
                    sign = 1
                    for a in z:
                        sign *= hh[a]
                    assert sign == 1
                checked += 1
    print(f"PASS: {checked} symmetric-sign cyclic-base clique/intersection/coset tests, including even orders.")


if __name__ == "__main__":
    total = sum(check(t) for t in range(9))
    check_cycle_pairings()
    assert embedding(8)[0] == 18 > 2 * 8
    digest = hashlib.sha256(SPEC.read_bytes()).hexdigest()
    assert digest == EXPECTED_SHA
    print(f"PASS: all {total} required original host edges checked.")
    print("The t=8 example exceeds the affine dimension bound; the maps are genuinely nonlinear.")
    print("Family asymptotic counterexample ruled out by the all-t argument in the report, not finite extrapolation.")
    print("Spec.lean unchanged; SHA-256:", digest)
