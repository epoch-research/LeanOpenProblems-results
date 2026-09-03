#!/usr/bin/env python3
"""Independent finite audits for CubeJointSignedCompletionAttempt.md.

The all-orders claims are proved in the report, not by this script.  This
script never imports Spec.lean, any old verification script, or any conjecture.
Exact counting is used; transcendental lower bounds are evaluated at 70 digits.
"""
from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import combinations, permutations, product
from math import comb, factorial, prod
from pathlib import Path
import hashlib
import random

import mpmath as mp
import sympy as sp

mp.mp.dps = 70
RNG = random.Random(20260903)
ROOT = Path(__file__).resolve().parent
SPEC_HASH = "9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b"
STATS = Counter()


def spec_guard():
    digest = hashlib.sha256((ROOT / "Spec.lean").read_bytes()).hexdigest()
    assert digest == SPEC_HASH, digest
    return digest


def real(x):
    x = F(x)
    return mp.mpf(x.numerator) / x.denominator


def falling(n, k):
    return prod(range(n-k+1, n+1)) if k <= n else 0


def log_c(alpha, degree=None):
    """Log of the exact finite-degree factor, or its degree-infinity limit."""
    a = real(alpha)
    assert 0 <= a <= 1
    denominator_log = (1-a)*mp.log(1-a) if a < 1 else mp.mpf(0)
    if degree is None:
        return -a-denominator_log
    assert degree >= 1
    if degree == 1 and a == 1:
        return mp.mpf(0)
    return (degree-a)*mp.log(1-a/degree)-denominator_log


def collision_bound(total, injective, loads, degrees):
    """Check both final bounds, only when their stated hypotheses hold."""
    if any(a > 1 for a in loads):
        STATS["overloaded examples (no bound asserted)"] += 1
        return
    assert total > 0 and injective > 0
    log_ratio = mp.log(real(F(injective, total)))
    finite = sum(log_c(a, d) for a, d in zip(loads, degrees) if d)
    entropy = sum(log_c(a) for a in loads)
    assert log_ratio + mp.mpf("1e-58") >= finite, (loads, degrees, log_ratio, finite)
    assert finite + mp.mpf("1e-58") >= entropy
    STATS["collision bounds verified"] += 1


# -- Polynomial multiplication and independent disjoint-set enumeration. --
def multiply(p, q):
    result = defaultdict(int)
    for a, x in p.items():
        for b, y in q.items():
            result[tuple(i+j for i, j in zip(a, b))] += x*y
    return dict(result)


def image_polynomial(weights, n):
    return {tuple(int(v in S) for v in range(n)): w
            for S, w in weights.items() if w}


def audit_core_product(cores, n):
    """Each core is an image-subset -> internally injective weight dictionary."""
    polynomial = {(0,)*n: 1}
    totals = [sum(p.values()) for p in cores]
    assert all(t > 0 for t in totals)
    loads = [sum(F(sum(w for S, w in p.items() if v in S), t)
                 for p, t in zip(cores, totals)) for v in range(n)]
    degrees = [sum(any(v in S and w for S, w in p.items()) for p in cores)
               for v in range(n)]
    for p in cores:
        polynomial = multiply(polynomial, image_polynomial(p, n))
    total = prod(totals)
    assert sum(polynomial.values()) == total
    sf = sum(w for exponent, w in polynomial.items() if max(exponent, default=0) <= 1)
    direct = 0
    for choices in product(*(list(p.items()) for p in cores)):
        used = set()
        weight = 1
        for S, w in choices:
            if used.intersection(S):
                break
            used.update(S)
            weight *= w
        else:
            direct += weight
    assert direct == sf
    collision_bound(total, sf, loads, degrees)
    STATS["positive-core products"] += 1


# -- Local capacity calculation, derived independently by minimization. --
def audit_univariate_capacity():
    alphas = [F(0), F(1, 8), F(1, 4), F(1, 2), F(3, 4), F(1)]
    for d in range(1, 10):
        for trial in range(12):
            roots = [F(2)]*d if trial == 0 else [F(RNG.randint(1, 9), RNG.randint(1, 7)) for _ in range(d)]
            s = sum(roots)
            for alpha in alphas:
                a = real(alpha)
                if alpha == 0:
                    cap_p = cap_t = mp.mpf(1)
                else:
                    cap_t = real(s) if alpha == 1 else real(s)**a / (a**a*(1-a)**(1-a))
                    if d == 1 and alpha == 1:
                        cap_p = real(s)
                    else:
                        # Strictly increasing logarithmic derivative; bisection
                        # finds the actual minimizer, not the AM--GM surrogate.
                        lo, hi = mp.mpf(0), mp.mpf(1)
                        mean = lambda t: sum(real(r)*t/(1+real(r)*t) for r in roots)
                        while mean(hi) <= a:
                            hi *= 2
                        for _ in range(260):
                            mid = (lo+hi)/2
                            if mean(mid) < a:
                                lo = mid
                            else:
                                hi = mid
                        t = (lo+hi)/2
                        cap_p = prod(1+real(r)*t for r in roots)/t**a
                factor = mp.exp(log_c(alpha, d))
                assert cap_t + mp.mpf("1e-55") >= factor*cap_p
                if trial == 0:
                    assert mp.almosteq(cap_t, factor*cap_p, rel_eps=mp.mpf("1e-55"))
                STATS["univariate capacities"] += 1
    print("Local capacity lemma: numerical minimization, all endpoints, and sharp equal-root cases passed.")


# -- List cores: exhaustive finite tests and nonuniform positive weights. --
def audit_lists():
    n = 4
    choices = [tuple(v for v in range(n) if mask >> v & 1) for mask in range(1, 1 << n)]
    for r in range(1, 4):
        for lists in product(choices, repeat=r):
            cores = [{frozenset([v]): 1 for v in L} for L in lists]
            audit_core_product(cores, n)
    for _ in range(100):
        n, r = 6, RNG.randint(1, 4)
        rows = [[RNG.randint(0, 3) for _ in range(n)] for _ in range(r)]
        if any(not sum(row) for row in rows):
            continue
        cores = [{frozenset([v]): w for v, w in enumerate(row) if w} for row in rows]
        audit_core_product(cores, n)
    for n in range(1, 10):
        for r in range(1, min(n, 5)+1):
            total, inj = n**r, falling(n, r)
            collision_bound(total, inj, [F(r, n)]*n, [r]*n)
            # The entropy factor equals the integral birthday lower bound.
            log_lower = -r-(n-r)*mp.log(1-real(F(r, n))) if r < n else -r
            assert mp.almosteq(sum(log_c(F(r, n)) for _ in range(n)), log_lower)
    print("List cores: all nonempty 4-site lists through 3 rows, weighted lists, and birthday cases passed.")


# -- Sum-of-squares cores: minors vs determinants and leverage scores. --
def gram_core(V):
    r, n = V.shape
    gram = V*V.T
    assert gram.det() > 0
    weights = {}
    for S in combinations(range(n), r):
        w = int(V[:, S].det())**2
        if w:
            weights[frozenset(S)] = w
    total = sum(weights.values())
    assert total == gram.det()
    inverse = gram.inv()
    for v in range(n):
        minor_marginal = F(sum(w for S, w in weights.items() if v in S), total)
        leverage = (V[:, v].T*inverse*V[:, v])[0]
        assert sp.Rational(minor_marginal.numerator, minor_marginal.denominator) == leverage
    STATS["Gram determinants / leverage laws"] += 1
    return weights


def audit_gram_cores():
    for _ in range(65):
        n = 6
        ranks = RNG.choice([(1, 2), (2, 2), (1, 1, 2), (2, 3), (3,)])
        cores = []
        for r in ranks:
            while True:
                V = sp.Matrix([[RNG.randint(-2, 2) for _ in range(n)] for _ in range(r)])
                if (V*V.T).det() > 0:
                    break
            cores.append(gram_core(V))
        audit_core_product(cores, n)
    H = sp.Matrix([[(-1)**((i & j).bit_count()) for j in range(8)] for i in range(8)])
    for ranks in [(2, 2), (2, 3), (1, 2, 3), (4,), (4, 4)]:
        cores = [gram_core(H[:r, :]) for r in ranks]
        audit_core_product(cores, 8)
    print("SOS cores: independent minor sums, Gram determinants, leverage scores, and disjoint products passed.")


# -- A whole source-disjoint gas, checked against full source injections. --
def audit_positive_source_gas():
    n, h = 8, 4
    H = sp.Matrix([[(-1)**((i & j).bit_count()) for j in range(n)] for i in range(n)])
    catalogue = list(combinations(range(h), 2))
    core = {}
    for i, U in enumerate(catalogue):
        base = gram_core(H[[i, (i+1) % n], :])
        total = sum(base.values())
        amplitude = 10**12 if i == 0 else 3**i
        core[U] = {S: F(amplitude*w, total) for S, w in base.items()}
        for v in range(n):
            assert sum(w for S, w in core[U].items() if v in S)/amplitude == F(2, n)
    singleton = {frozenset([v]): F(1, n) for v in range(n)}
    reference, globally_injective = F(0), F(0)
    family_count = 0
    for mask in range(1 << len(catalogue)):
        family = [U for i, U in enumerate(catalogue) if mask >> i & 1]
        occupied = [u for U in family for u in U]
        if len(set(occupied)) != len(occupied):
            continue
        family_count += 1
        r = h-len(occupied)
        factors = [core[U] for U in family]+[singleton]*r
        audit_core_product(factors, n)
        polynomial = {(0,)*n: 1}
        for factor in factors:
            polynomial = multiply(polynomial, image_polynomial(factor, n))
        sf = sum(w for exponent, w in polynomial.items() if max(exponent) <= 1)
        # A second route uses only full injections of all h SOURCE vertices.
        # Split each image-set weight equally among its |U|! bijections.
        direct = F(0)
        for f in permutations(range(n), h):
            weight = F(1, n**r)
            for U in family:
                image = frozenset(f[u] for u in U)
                weight *= core[U].get(image, F(0))/factorial(len(U))
            direct += weight
        assert direct == sf
        reference += prod(sum(core[U].values()) for U in family)
        globally_injective += direct
    assert family_count == 10
    assert mp.log(real(globally_injective/reference))+mp.mpf("1e-55") >= sum(log_c(F(h, n)) for _ in range(n))
    STATS["positive source-gas family/full-injection comparisons"] = family_count
    print("Positive source-polymer gas: all compatible families, arbitrary amplitudes, and free isolates agree with full injections.")


# -- Exact full cube injections: two separately implemented counters. --
def cube_edges(d):
    return [(u, u ^ (1 << i)) for u in range(1 << d) for i in range(d) if not (u >> i & 1)]


def host(n, kind):
    A = [[0]*n for _ in range(n)]
    for i in range(n):
        for j in range(i):
            value = 1 if kind == "red" else (int((i < n//2) == (j < n//2)) if kind == "two-cliques" else RNG.randrange(2))
            A[i][j] = A[j][i] = value
    return A


def direct_cube(A, d, keep_images=False):
    n, h = len(A), 1 << d
    edges = cube_edges(d)
    counts = [0, 0]
    images = Counter()
    for f in permutations(range(n), h):
        colors = {A[f[u]][f[v]] for u, v in edges}
        if len(colors) == 1:
            c = colors.pop()
            counts[c] += 1
            if keep_images:
                images[frozenset(f)] += 1
    return counts, images


def conditional_cube(A, d):
    n, h = len(A), 1 << d
    even = [v for v in range(h) if v.bit_count() % 2 == 0]
    odd = [v for v in range(h) if v.bit_count() % 2]
    adj = {y: [y ^ (1 << i) for i in range(d)] for y in odd}
    counts = [0, 0]
    lower = mp.mpf(0)
    for labels in permutations(range(n), len(even)):
        f = dict(zip(even, labels))
        X = [v for v in range(n) if v not in labels]
        for c in (0, 1):
            lists = [[v for v in X if all(A[f[x]][v] == c for x in adj[y])] for y in odd]
            if any(not L for L in lists):
                continue
            matching_count = sum(len(set(t)) == len(t) for t in product(*lists))
            counts[c] += matching_count
            D = [len(L) for L in lists]
            loads = [sum(F(1, len(L)) for L in lists if v in L) for v in X]
            degrees = [sum(v in L for L in lists) for v in X]
            if max(loads, default=F(0)) <= 1:
                value = prod(D)*mp.exp(sum(log_c(a, deg) for a, deg in zip(loads, degrees) if deg))
                assert real(matching_count)+mp.mpf("1e-55") >= value
                lower += value
                STATS["good pinned cube/color sectors"] += 1
    assert real(sum(counts))+mp.mpf("1e-50") >= lower
    return counts


def audit_pair_factor_identity(A):
    # Direct independent-label product, including all non-edge collision factors.
    d, h, n = 2, 4, len(A)
    edges = set(cube_edges(d))
    for sign in (-1, 1):
        numerator = 0
        for labels in product(range(n), repeat=h):
            weight = 1
            for u in range(h):
                for v in range(u+1, h):
                    x, y = labels[u], labels[v]
                    M = 0 if x == y else 2*A[x][y]-1
                    weight *= 1-int(x == y)+(sign*M if (u, v) in edges else 0)
            numerator += weight
        counts, _ = direct_cube(A, d)
        assert numerator == (1 << len(edges))*counts[int(sign == 1)]
    # All even spectral-edge subsets, sampled WITHOUT replacement.
    even_sum = 0
    for labels in permutations(range(n), h):
        signs = [2*A[labels[u]][labels[v]]-1 for u, v in edges]
        for mask in range(1 << len(signs)):
            if mask.bit_count() % 2 == 0:
                even_sum += prod(signs[i] for i in range(len(signs)) if mask >> i & 1)
    assert 2*even_sum == (1 << len(edges))*sum(direct_cube(A, d)[0])
    STATS["original pair-factor and parity identities"] += 1


def audit_cube_counts():
    for d, n, reps in [(1, 4, 8), (2, 5, 12), (2, 6, 12), (2, 8, 8), (3, 8, 3)]:
        for trial in range(reps):
            kind = "red" if trial == 0 else "two-cliques" if trial == 1 else "random"
            A = host(n, kind)
            direct, _ = direct_cube(A, d)
            conditional = conditional_cube(A, d)
            assert direct == conditional, (d, n, kind, direct, conditional)
            STATS["full cube count comparisons"] += 1
            if d == 2 and n <= 6 and trial < 3:
                audit_pair_factor_identity(A)
    print("Cube linkage: direct full injections = pinned-list counts, with every cross-collision excluded.")
    print("Original f_uv expansion and global even-parity projection also agree exactly.")


# -- Averaging-before-cumulants obstruction, two independent calculations. --
def p_add(p, q, sign=1):
    r = [F(0)]*max(len(p), len(q))
    for i, x in enumerate(p): r[i] += x
    for i, x in enumerate(q): r[i] += sign*x
    while len(r) > 1 and not r[-1]: r.pop()
    return tuple(r)


def p_mul(p, q):
    r = [F(0)]*(len(p)+len(q)-1)
    for i, x in enumerate(p):
        for j, y in enumerate(q): r[i+j] += x*y
    return tuple(r)


def partitions(items):
    if not items:
        yield []
        return
    x, *rest = items
    for pi in partitions(rest):
        yield [frozenset([x])]+pi
        for i in range(len(pi)):
            yield pi[:i]+[pi[i] | {x}]+pi[i+1:]


def matching_moment(mask, n):
    k = mask.bit_count()
    edges = sum(mask & (3 << (2*j)) == 3 << (2*j) for j in range(4))
    return F(falling(n, k), n**k)*(2**(edges-1) if edges else 1)


def audit_joint_cumulant():
    nsource = 8
    fall = [(F(1),)]
    for k in range(1, nsource+1):
        fall.append(p_mul(fall[-1], (F(1), F(-(k-1)))))
    moments, connected = {}, {}
    for mask in range(1 << nsource):
        edges = sum(mask & (3 << (2*j)) == 3 << (2*j) for j in range(4))
        scale = 2**(edges-1) if edges else 1
        moments[mask] = tuple(scale*x for x in fall[mask.bit_count()])
    for k in range(1, nsource+1):
        for mask in range(1, 1 << nsource):
            if mask.bit_count() != k: continue
            least = mask & -mask
            value = moments[mask]
            sub = (mask-1) & mask
            while sub:
                if sub & least:
                    value = p_add(value, p_mul(connected[sub], moments[mask ^ sub]), -1)
                sub = (sub-1) & mask
            connected[mask] = value
    expected = tuple(map(F, [-2, 8, 148, -1528, 11230, -42976, 68400, -40320]))
    assert connected[(1 << nsource)-1] == expected
    all_partitions = list(partitions(list(range(nsource))))
    assert len(all_partitions) == 4140
    for n in (32, 64, 100):
        direct = sum((-1)**(len(pi)-1)*factorial(len(pi)-1)*prod(
            matching_moment(sum(1 << v for v in block), n) for block in pi)
            for pi in all_partitions)
        polynomial_value = sum(c/F(n)**j for j, c in enumerate(expected))
        assert direct == polynomial_value < -1
    positive_bound = F(8, 32)+F(148, 32**2)+F(11230, 32**4)+F(68400, 32**6)
    assert positive_bound < 1
    for d in range(4, 9):
        # Fix coordinate 0; even parity on the remaining d-1 coordinates.
        matching = [(2*y, 2*y+1) for y in range(1 << (d-1)) if y.bit_count() % 2 == 0]
        vertices = set(v for edge in matching for v in edge)
        induced = {tuple(sorted(edge)) for edge in cube_edges(d) if set(edge) <= vertices}
        assert induced == {tuple(edge) for edge in matching}
        assert len(matching) == (1 << d)//4
        assert comb(len(matching)-1, 3) >= 1
    print("Joint scalar-cumulant obstruction: exact polynomial", list(expected))
    print("Independent 4,140-partition sums and all-dimensional induced-matching construction passed.")


# -- Actual joint cube image law is not automatically real stable. --
def audit_nonstable_mixture():
    for a in (4, 5, 6):
        A = host(2*a, "two-cliques")
        counts, image_weights = direct_cube(A, 2, keep_images=True)
        coefficients = Counter()
        for S, w in image_weights.items():
            coefficients[sum(v < a for v in S)] += w
        expected = {0: falling(a, 4), 2: 2*falling(a, 2)**2, 4: falling(a, 4)}
        assert dict(coefficients) == expected
        assert sum(counts) == sum(expected.values())
        # Perfectly flat one-point marginals despite non-real-rooted specialization.
        Z = sum(image_weights.values())
        for v in range(2*a):
            assert F(sum(w for S, w in image_weights.items() if v in S), Z) == F(4, 2*a)
        q = sum(sp.Integer(c)*sp.Symbol("t")**k for k, c in coefficients.items())
        assert sp.Poly(q).coeff_monomial(sp.Symbol("t")) == 0
        assert sp.Poly(q).coeff_monomial(1) > 0
        STATS["nonstable actual joint image laws"] += 1
    print("Joint image-law obstruction: full-injection counts verify the non-real-rooted specialization and flat marginals.")


def main():
    print("Spec.lean SHA-256 before:", spec_guard())
    audit_univariate_capacity()
    audit_lists()
    audit_gram_cores()
    audit_positive_source_gas()
    audit_cube_counts()
    audit_joint_cumulant()
    audit_nonstable_mixture()
    print("\nAudit totals:")
    for name, number in sorted(STATS.items()):
        print(f"  {name}: {number}")
    print("Spec.lean SHA-256 after:", spec_guard())
    print("PASS: all finite checks. No universal good pinned sector or Ramsey bound is certified.")


if __name__ == "__main__":
    main()
