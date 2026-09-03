#!/usr/bin/env python3
"""Coordinate audits for CubeSwitchedSymplecticInvestigation.md.

This checks proved constructions and identities, not searches for Ramsey
counterexamples.  All vector spaces are binary, with interleaved symplectic
coordinates (e_1,f_1,e_2,f_2,...).
"""
from random import Random
import hashlib
from pathlib import Path


def bit(x, i):
    return (x >> i) & 1


def B(x, y, r):
    return sum(bit(x, i) * bit(y, i + 1) +
               bit(x, i + 1) * bit(y, i)
               for i in range(0, r, 2)) & 1


def q0(x, r):
    return sum(bit(x, i) * bit(x, i + 1)
               for i in range(0, r, 2)) & 1


def colour(x, y, g, r):
    assert x != y
    return B(x, y, r) ^ g(x) ^ g(y)


def linear_image(t, basis):
    z = 0
    for i, a in enumerate(basis):
        if bit(t, i):
            z ^= a
    return z


def independent_basis(candidates, dimension):
    pivots = {}
    ans = []
    for a in candidates:
        z = a
        while z:
            k = z.bit_length() - 1
            if k in pivots:
                z ^= pivots[k]
            else:
                pivots[k] = z
                ans.append(a)
                break
        if len(ans) == dimension:
            return ans
    raise AssertionError(("claimed spanning set does not span", dimension, len(ans)))


def audit_cube(images, d, g, r, c):
    assert len(images) == 1 << d
    assert len(set(images)) == 1 << d, "noninjective construction"
    assert all(0 <= x < 1 << r for x in images)
    for t, x in enumerate(images):
        for i in range(d):
            if not bit(t, i):
                assert colour(x, images[t ^ (1 << i)], g, r) == c


def shear_basis(r, c):
    """The explicit r-vector basis for v=e_1, q=q0, r>=4."""
    assert r >= 4 and r % 2 == 0
    v, w = 1, 2
    a0 = w ^ (c * v)
    ans = [a0] + [a0 ^ (1 << i) for i in range(2, r)]
    ans += [w ^ ((c ^ 1) * v) ^ (1 << 2) ^ (1 << 3)]
    assert len(ans) == r
    independent_basis(ans, r)
    for a in ans:
        assert B(v, a, r) == 1 and q0(a, r) == c
    return ans


def spanning_shear(r, h, c):
    v = 1
    for x in range(1 << r):
        assert h(x) == h(x ^ v)
    basis = shear_basis(r, c)
    ans = []
    for t in range(1 << r):
        x = linear_image(t, basis)
        ans.append(x ^ (h(x) * v))
    return ans


def unswitched_half_cube(r, c):
    """Q_(r-1) in B=c on the hyperplane with last f-coordinate 1."""
    assert r >= 4 and r % 2 == 0
    D = r - 2
    # The auxiliary space has coordinates (z,t) and Q(z,t)=q0(z)+t.
    if c == 0:
        basis = [1 << i for i in range(D)] + [3 ^ (1 << D)]
    else:
        basis = [1 << D] + [(1 << i) ^ (1 << D) for i in range(D)]
    independent_basis(basis, D + 1)
    ans = []
    for t in range(1 << (D + 1)):
        aux = linear_image(t, basis)
        z, a = aux & ((1 << D) - 1), bit(aux, D)
        ans.append(z ^ ((q0(z, D) ^ a) << D) ^ (1 << (D + 1)))
    return ans


def quadratic_function(r, pairs, linear, constant):
    def g(x):
        return (constant ^ ((linear & x).bit_count() & 1) ^
                (sum(bit(x, i) * bit(x, j) for i, j in pairs) & 1))
    return g


def quadratic_cube(r, original_g, c):
    """Construct the cube from the three-case quadratic theorem."""
    assert r >= 6 and r % 2 == 0
    gzero = original_g(0)
    g = lambda x: original_g(x) ^ gzero
    G = lambda x, y: g(x ^ y) ^ g(x) ^ g(y)
    e = [1 << i for i in range(r)]
    Grows = [tuple(G(a, b) for b in e) for a in e]
    Brows = [tuple(B(a, b, r) for b in e) for a in e]
    if not any(any(row) for row in Grows):
        ell = sum(g(1 << i) << i for i in range(r))
        translation = sum(bit(ell, i + 1) << i | bit(ell, i) << (i + 1)
                          for i in range(0, r, 2))
        assert all(B(translation, x, r) == g(x) for x in range(1 << r))
        return [x ^ translation for x in unswitched_half_cube(r, c)], r - 1, "affine"
    if Grows == Brows:
        basis = independent_basis((x for x in range(1, 1 << r) if g(x) == c), r)
        return [linear_image(t, basis) for t in range(1 << r)], r, "Cayley"

    v = next(x for x in range(1, 1 << r)
             if tuple(G(x, a) for a in e) not in
             (tuple(0 for _ in e), tuple(B(x, a, r) for a in e)))
    coord = (v & -v).bit_length() - 1
    correction = q0(v, r)
    q = lambda x: q0(x, r) ^ (correction * bit(x, coord))
    assert q(v) == 0
    h = lambda x: g(x) ^ q(x)
    Pv = lambda x: G(v, x) ^ B(v, x, r)
    W = [x for x in range(1 << r) if Pv(x) == 0]
    H = [x for x in range(1 << r) if Pv(x) == h(v)]
    assert len(W) == len(H) == 1 << (r - 1)
    assert v in W
    assert any(B(v, x, r) == 1 for x in W)
    assert all(h(x) == h(x ^ v) for x in H)
    basis = independent_basis((x for x in W if B(v, x, r) == 1 and q(x) == c), r - 1)
    a = H[0]
    ans = []
    for t in range(1 << (r - 1)):
        x = a ^ linear_image(t, basis)
        ans.append(x ^ (h(x) * v))
    assert set(ans) == set(H)
    return ans, r - 1, "generic quadratic"


def is_affine_table(table, r):
    k = table[0]
    coeff = [table[1 << i] ^ k for i in range(r)]
    return all(table[x] == (k ^ (sum(bit(x, i) * coeff[i] for i in range(r)) & 1))
               for x in range(1 << r))


def flat_squares(images, d, r):
    for t in range(1 << d):
        for i in range(d):
            for j in range(i + 1, d):
                if bit(t, i) or bit(t, j):
                    continue
                x00, x10 = images[t], images[t ^ (1 << i)]
                x01, x11 = images[t ^ (1 << j)], images[t ^ (1 << i) ^ (1 << j)]
                if B(x00 ^ x11, x10 ^ x01, r):
                    return False
    return True


def canonical_potential(images, d, r):
    p = [0] * (1 << d)
    for t in range(1, 1 << d):
        low = t & -t
        u = t ^ low
        p[t] = p[u] ^ B(images[u], images[t], r)
    consistent = all((p[t] ^ p[t ^ (1 << i)]) == B(images[t], images[t ^ (1 << i)], r)
                     for t in range(1 << d) for i in range(d))
    return p, consistent


def run():
    checks = {}
    # Exhaust the arbitrary quotient truth table only in the minimum dimension
    # of the shear lemma.  This verifies its formula, not a cube-existence search.
    count = 0
    for mask in range(1 << 8):
        r = 4
        h = lambda x, mask=mask: bit(mask, x >> 1)
        g = lambda x: q0(x, r) ^ h(x)
        for c in (0, 1):
            images = spanning_shear(r, h, c)
            audit_cube(images, r, g, r, c)
            count += 1
            bad = 5
            perturbed = lambda x: g(x) ^ int(x == bad)
            preimage = images.index(bad)
            face = [images[t] for t in range(1 << r) if bit(t, 0) != bit(preimage, 0)]
            audit_cube(face, r - 1, perturbed, r, c)
            assert sum(perturbed(x) for x in range(1 << r)) & 1
            for v in range(1, 1 << r):
                derivative = [perturbed(x) ^ perturbed(x ^ v) for x in range(1 << r)]
                assert not is_affine_table(derivative, r)
    checks["spanning shear cubes (both colours, all 256 quotient tables at r=4)"] = count
    checks["one-point perturbations: injective Q_(r-1), odd weight, no affine derivative"] = count

    # Higher-dimensional high-degree instances of exactly the same theorem.
    count = 0
    for r in (6, 8, 10):
        h = lambda x, r=r: int((x >> 1) == ((1 << (r - 1)) - 1)) ^ bit(x, 2) ^ (bit(x, 3) * bit(x, 4))
        g = lambda x, r=r: q0(x, r) ^ h(x)
        for c in (0, 1):
            audit_cube(spanning_shear(r, h, c), r, g, r, c)
            count += 1
    checks["higher-dimensional explicit high-degree spanning shear cubes"] = count

    count = 0
    for r in (4, 6, 8, 10):
        for c in (0, 1):
            audit_cube(unswitched_half_cube(r, c), r - 1, lambda x: 0, r, c)
            count += 1
    checks["unswitched Q_(r-1) constructions in both colours"] = count

    # Fixed-seed coefficient stress tests of the proved quadratic algorithm.
    rng = Random(181)
    types = {"affine": 0, "Cayley": 0, "generic quadratic": 0}
    for r in (6, 8, 10):
        pairs = [(i, j) for i in range(r) for j in range(i + 1, r)]
        parameters = [([], 0, 0), ([], (1 << r) - 1, 1),
                      ([(i, i + 1) for i in range(0, r, 2)], 0, 0),
                      ([(i, i + 1) for i in range(0, r, 2)], 13, 1),
                      ([(0, 2)], 7, 1)]
        for _ in range(24):
            parameters.append(([p for p in pairs if rng.randrange(2)], rng.randrange(1 << r), rng.randrange(2)))
        for ps, linear, constant in parameters:
            g = quadratic_function(r, ps, linear, constant)
            for c in (0, 1):
                images, d, case = quadratic_cube(r, g, c)
                audit_cube(images, d, g, r, c)
                assert d >= r - 1
                types[case] += 1
    checks["quadratic-construction audits by case"] = types

    # Exact ordinary-injection square/potential equivalence, and random-switch
    # probability on each tested fixed framework; no existence search is done.
    frameworks = []
    r, d = 4, 3
    for _ in range(20):
        frameworks.append(rng.sample(range(1 << r), 1 << d))
    frameworks.append([t for t in range(1 << d)])
    for c in (0, 1):
        frameworks.append(unswitched_half_cube(r, c))
    for images in frameworks:
        p, consistent = canonical_potential(images, d, r)
        assert consistent == flat_squares(images, d, r)
        mono_patterns = 0
        for mask in range(1 << (1 << d)):
            edge_colours = {B(images[t], images[t ^ (1 << i)], r) ^ bit(mask, t) ^ bit(mask, t ^ (1 << i))
                            for t in range(1 << d) for i in range(d)}
            mono_patterns += len(edge_colours) == 1
        assert mono_patterns == (4 if consistent else 0)
    checks["fixed-framework square criterion and exactly four two-colour switch patterns"] = len(frameworks)

    # Exact candidate-list identity and the complementary-colour partition.
    r, d = 6, 4
    g = lambda x: q0(x, r) ^ int(x == 0) ^ (bit(x, 0) * bit(x, 2) * bit(x, 5))
    E = [t for t in range(1 << d) if t.bit_count() % 2 == 0]
    O = [t for t in range(1 << d) if t.bit_count() % 2]
    labels = dict(zip(E, rng.sample(range(1 << r), len(E))))
    used = set(labels.values())
    for y in O:
        ns = [labels[y ^ (1 << i)] for i in range(d)]
        u0 = ns[0]
        flat = {z for z in range(1 << r) if z not in used and
                all(B(u ^ u0, z, r) == (g(u) ^ g(u0)) for u in ns[1:])}
        lists = []
        for c in (0, 1):
            algebraic = {z for z in flat if B(u0, z, r) ^ g(z) == c ^ g(u0)}
            direct = {z for z in range(1 << r) if z not in used and
                      all(colour(u, z, g, r) == c for u in ns)}
            assert algebraic == direct
            lists.append(algebraic)
        assert not (lists[0] & lists[1]) and (lists[0] | lists[1]) == flat
    checks["two-colour affine-flat/list identity"] = len(O)

    # The Hadamard identity is exact; diagonal-switching invariance is algebraic.
    r = 4
    H = [[(-1) ** B(x, y, r) for y in range(1 << r)] for x in range(1 << r)]
    assert all(sum(H[x][z] * H[z][y] for z in range(1 << r)) == ((1 << r) if x == y else 0)
               for x in range(1 << r) for y in range(1 << r))
    checks["Hadamard identity H^2=N I at r=4"] = "PASS"

    # Audit the strictly negative existence exponent, not a finite-host search.
    r = 64
    exponents = {c: r * (r - c + 1) + 2 - (1 << (r - c - 1)) for c in range(1, 17)}
    assert all(e < 0 for e in exponents.values())
    checks["maximal-degree/no-affine-cube existence bound at r=64, 1<=c<=16"] = "strictly negative"
    for r in range(8, 514, 2):
        d0 = (r * r - 1).bit_length() + 2  # ceil(2 log_2 r) + 2, exactly
        assert d0 <= r
        assert (1 << (d0 - 1)) >= 2 * r * r
        assert r * (d0 + 1) + 2 - (1 << (d0 - 1)) < 0
    checks["d0 dimension/exponent audit for every even 8<=r<=512"] = "PASS"

    spec = Path(__file__).with_name("Spec.lean")
    digest = hashlib.sha256(spec.read_bytes()).hexdigest()
    assert digest == "9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b"
    checks["Spec.lean SHA-256 (unchanged)"] = digest
    for name, result in checks.items():
        print(f"PASS: {name}: {result}")
    print("These audits check stated formulas; the all-dimensional claims rest on the proofs in the note.")


if __name__ == "__main__":
    run()
