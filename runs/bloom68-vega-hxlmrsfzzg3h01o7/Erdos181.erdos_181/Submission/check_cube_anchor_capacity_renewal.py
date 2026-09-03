#!/usr/bin/env python3
"""Finite audits for CubeAnchorCapacityRenewal.md (not a renewal proof).

Standard library only. Exact rational checks are used for the combinatorial
probability statements. The large Hadamard host is implicit, not allocated.
"""
from __future__ import annotations

from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
import hashlib
from itertools import combinations, permutations, product
import json
from math import factorial, lcm, log, prod
from pathlib import Path
from random import Random

ROOT = Path(__file__).resolve().parent
SPEC_SHA = "9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b"
RNG = Random(20260825)


def falling(n, k):
    if k > n:
        return 0
    return prod(range(n-k+1, n+1))


def subsets(mask):
    s = mask
    while True:
        yield s
        if not s:
            break
        s = (s-1) & mask


def gram_checks():
    count = 0
    # All zero-one 2x3 and 3x3 matrices, plus rectangular 3x2 matrices.
    for M, n in [(2, 3), (3, 2), (3, 3)]:
        for bits in product(range(2), repeat=M*n):
            A = [bits[a*n:(a+1)*n] for a in range(M)]
            q = [F(sum(row), n) for row in A]
            c = [[F(sum(A[a][j]*A[b][j] for j in range(n)), n)
                  for b in range(M)] for a in range(M)]
            R = [[c[a][b]-q[a]*q[b] for b in range(M)] for a in range(M)]
            for h in range(6):
                zs = [sum(all(A[a][j] for j in cols) for a in range(M))
                      for cols in product(range(n), repeat=h)]
                mu = F(sum(zs), len(zs))
                var = F(sum(z*z for z in zs), len(zs))-mu*mu
                assert mu == sum(x**h for x in q)
                assert var == sum(c[a][b]**h-(q[a]*q[b])**h
                                  for a in range(M) for b in range(M))
                if h == 0:
                    assert var == 0
                elif h == 1:
                    assert var == sum(map(sum, R))
                else:
                    linear = h*sum(q[a]**(h-1)*R[a][b]*q[b]**(h-1)
                                   for a in range(M) for b in range(M))
                    remainder = sum(
                        R[a][b]**2 * sum((i+1)*(q[a]*q[b])**i*c[a][b]**(h-2-i)
                                        for i in range(h-1))
                        for a in range(M) for b in range(M))
                    assert linear >= 0 and remainder >= 0
                    assert var == linear+remainder
                count += 1
    return count


@lru_cache(None)
def permutation_space(n):
    ps = list(permutations(range(n)))
    masks = {}
    for j, pi in enumerate(ps):
        for s in range(1 << n):
            key = tuple((u, pi[u]) for u in range(n) if s >> u & 1)
            masks[key] = masks.get(key, 0) | (1 << j)
    events = []
    for key, mask in masks.items():
        src = sum(1 << u for u, _ in key)
        ran = sum(1 << b for _, b in key)
        events.append((key, src, ran, mask, F(1, falling(n, len(key)))))
    assert len(ps) == factorial(n)
    return ps, events


def force(pi, key):
    out = list(pi)
    for u, b in key:
        v = out.index(b)
        out[u], out[v] = out[v], out[u]
    return tuple(out)


def coupling_checks():
    forcing_queries = forcing_pairs = preserved_positions = 0
    for n in range(2, 6):
        ps, events = permutation_space(n)
        for key, src, ran, _, _ in events:
            outputs = Counter()
            for pi in ps:
                out = force(pi, key)
                outputs[out] += 1
                assert all(out[u] == b for u, b in key)
                # This simultaneously checks preservation of EVERY event true
                # at pi whose source/range are disjoint from the forced event.
                for u in range(n):
                    if not (src >> u & 1) and not (ran >> pi[u] & 1):
                        assert out[u] == pi[u]
                        preserved_positions += 1
                forcing_pairs += 1
            assert len(outputs) == factorial(n-len(key))
            assert set(outputs.values()) == {falling(n, len(key))}
            forcing_queries += 1
    return forcing_queries, forcing_pairs, preserved_positions


def intersects(E, Q):
    return bool(E[1] & Q[1] or E[2] & Q[2])


def independent_moment(n, supports, weights, probs):
    ans = F(0)
    for s in range(1 << n):
        prob = prod(probs[u] if s >> u & 1 else 1-probs[u] for u in range(n))
        exponent = sum(w for support, w in zip(supports, weights)
                       if support & ~s == 0)
        ans += prob * (1 << exponent)
    return ans


def conditional_lll_checks():
    family_count = query_count = cylinder_count = polynomial_count = 0
    for n, reps in [(4, 14), (5, 16), (6, 18)]:
        ps, events = permutation_space(n)
        # Keep the incidence budget small enough that a two-point hit set
        # has tilted Bernoulli parameter below one, as required in (19).
        min_size = 3 if n == 4 else 2
        candidates = [E for E in events if min_size <= len(E[0]) <= min(4, n)]
        all_mask = (1 << len(ps))-1
        for rep in range(reps):
            fam = RNG.sample(candidates, 1+rep % (n-1))
            z = [2*E[4] for E in fam]
            assert all(0 < v <= F(1, 2) for v in z)
            for i, E in enumerate(fam):
                neighbor_product = prod(1-z[j] for j, Q in enumerate(fam)
                                        if j != i and intersects(E, Q))
                assert E[4] <= z[i]*neighbor_product
            forbidden = 0
            for E in fam:
                forbidden |= E[3]
            good = all_mask & ~forbidden
            den = good.bit_count()
            assert den > 0
            src_products = [prod(1-z[j] for j, E in enumerate(fam)
                                 if E[1] >> u & 1) for u in range(n)]
            ran_products = [prod(1-z[j] for j, E in enumerate(fam)
                                 if E[2] >> b & 1) for b in range(n)]
            stretch = 1/(min(src_products)*min(ran_products))
            # Every partial injection, including all full permutation queries.
            for Q in events:
                adjprod = prod(1-z[j] for j, E in enumerate(fam) if intersects(E, Q))
                actual = F((good & Q[3]).bit_count(), den)
                assert actual <= Q[4]/adjprod
                assert 1/adjprod <= stretch**len(Q[0])
                query_count += 1
            good_ps = [pi for j, pi in enumerate(ps) if good >> j & 1]
            # Summing cylinder probabilities into one fixed range set; this
            # retains the (s)_k numerator and then audits polynomial domination.
            for hit in [1, (1 << 0) | (1 << (n-1))]:
                theta = F(hit.bit_count(), n)*stretch
                assert theta < 1
                marked = [sum(1 << u for u in range(n) if hit >> pi[u] & 1)
                          for pi in good_ps]
                for support in range(1 << n):
                    k = support.bit_count()
                    actual = F(sum(support & ~s == 0 for s in marked), den)
                    exact_bound = stretch**k * F(falling(hit.bit_count(), k), falling(n, k))
                    assert actual <= exact_bound <= theta**k
                    cylinder_count += 1
                supports = [sum(1 << u for u in RNG.sample(range(n), RNG.randrange(0, 4)))
                            for _ in range(n+1)]
                weights = [RNG.randrange(1, 4) for _ in supports]
                actual_moment = F(sum(1 << sum(w for S, w in zip(supports, weights)
                                               if S & ~s == 0) for s in marked), den)
                iid_moment = independent_moment(n, supports, weights, [theta]*n)
                assert actual_moment <= iid_moment
                polynomial_count += 1
            family_count += 1
    return family_count, query_count, cylinder_count, polynomial_count


def read_d_checks():
    cases = []
    # All families of nonempty supports on three independent variables.
    for family in range(1 << 7):
        supports = [s for s in range(1, 8) if family >> (s-1) & 1]
        cases.append((3, supports, [1]*len(supports), [F(1, 3), F(1, 2), F(2, 3)]))
    for _ in range(180):
        n = RNG.randrange(1, 7)
        supports = [RNG.randrange(1 << n) for _ in range(RNG.randrange(1, 8))]
        weights = [RNG.randrange(1, 4) for _ in supports]
        probs = [RNG.choice([F(1, 4), F(1, 3), F(1, 2), F(2, 3), F(3, 4)])
                 for _ in range(n)]
        cases.append((n, supports, weights, probs))
    for n, supports, weights, probs in cases:
        d = max([1]+[sum(S >> u & 1 for S in supports) for u in range(n)])
        actual = independent_moment(n, supports, weights, probs)
        holder_rhs_power = F(1)
        for S, w in zip(supports, weights):
            pS = prod(probs[u] for u in range(n) if S >> u & 1)
            holder_rhs_power *= 1+pS*((1 << (d*w))-1)
        assert actual**d <= holder_rhs_power
    return len(cases)


def finite_population_checks():
    cases = distinct = 0
    for n in range(1, 41):
        for s in range(n+1):
            for k in range(n+1):
                assert F(falling(s, k), falling(n, k)) <= F(s, n)**k
                cases += 1
        for h in range(n+1):
            assert F(falling(n, h), n**h) >= 1-F(h*(h-1), 2*n)
            distinct += 1
    return cases, distinct


def range_pruning_checks():
    cases = 0
    for n0 in [8, 9, 10, 12, 14]:
        m, d = 6, 3
        supports = [tuple(sorted({x, (x+1) % m, (x+2) % m})) for x in range(m)]
        families = []
        for i, S in enumerate(supports):
            maps = [phi for phi in permutations(range(n0), len(S))
                    if 0 in phi or (phi[0] == 1 and phi[1] == 2)]
            families.append(maps)
        p = max(F(len(fam), falling(n0, len(S)))
                for S, fam in zip(supports, families))
        old_range = [F(0)]*n0
        for S, fam in zip(supports, families):
            atom = F(1, falling(n0, len(S)))
            for phi in fam:
                for b in phi:
                    old_range[b] += atom
        assert sum(old_range) <= m*d*p
        for gamma in [2, 3, 4, 100*d]:
            threshold = gamma*m*d*p/n0
            deleted = {b for b in range(n0) if old_range[b] > threshold}
            r = len(deleted)
            assert r < F(n0, gamma) or r == 0
            n = n0-r
            assert n >= d
            new_range = [F(0)]*n0
            new_source = [F(0)]*m
            for S, fam in zip(supports, families):
                h = len(S)
                ratio = F(falling(n0, h), falling(n, h))
                # Exact product and the logarithmic ratio bound used in (12).
                assert ratio == prod(F(n0-j, n-j) for j in range(h))
                assert log(float(ratio)) <= float(F(h*r, n-h+1))+1e-12
                kept = [phi for phi in fam if not (set(phi) & deleted)]
                assert F(len(kept), falling(n, h)) <= ratio*p
                atom = F(1, falling(n, h))
                for phi in kept:
                    for b in phi:
                        new_range[b] += atom
                    for u in S:
                        new_source[u] += atom
            max_ratio = F(falling(n0, d), falling(n, d))
            assert max(new_source) <= max_ratio*d*p
            for b in range(n0):
                assert new_range[b] <= max_ratio*old_range[b]
                if b not in deleted:
                    assert new_range[b] <= max_ratio*threshold
            if gamma == 100*d:
                assert r < F(n0, 100*d)
            cases += 1
    return cases


def t_value(d):
    # ceil(3 log_2(d+1)+20), computed exactly even adjacent to powers of two.
    return 20+(((d+1)**3-1).bit_length())


def constant_checks():
    assert next(d for d in range(1, 200) if 2*t_value(d) < d) == 79
    ds = set(range(79, 1500))
    for j in range(7, 513):
        ds.update([(1 << j)-1, 1 << j, (1 << j)+1])
    count = admissible_dimensions = 0
    for d in sorted(ds):
        t = t_value(d)
        if 2*t >= d:
            continue
        admissible_dimensions += 1
        assert d >= 41
        # Does not construct m=2^(d-1) when d is enormous.
        assert d-1 >= (24*d*d-1).bit_length()
        assert 1 << t >= (1 << 20)*(d+1)**3
        for K2 in [F(1, 4), F(1), F(16), F(10**6)]:
            kappa = K2+1
            for multiplier in [1, 1 << 20, 1 << 200]:
                C = 10000*kappa*multiplier
                p = F(2000)*kappa/(C*(1 << t))
                ell = 8*d*p+1600*d*d*p/C
                assert p <= F(1, 5*(1 << 20)*(d+1)**3)
                assert ell <= F(1, 100*d)
                assert F(1, 64)-24/C > F(1, 128)
                tail_exponent = C*(1 << t)/(2048*d)
                assert tail_exponent >= 512*C*d*d
                assert C+d <= 2*C*d*d < tail_exponent
                assert 4096*K2*d/(C*(1 << t)) < 1-1/C
                count += 1
    return count, admissible_dimensions, max(ds).bit_length()


def syndrome(z, d):
    out = 0
    for i in range(d):
        if z >> i & 1:
            out ^= i
    return out


def gf2_rank(vectors):
    basis = {}
    for v in vectors:
        while v:
            i = v.bit_length()-1
            if i in basis:
                v ^= basis[i]
            else:
                basis[i] = v
                break
    return len(basis)


def syndrome_checks():
    pairs = neighbor_cases = admissible_shift_cases = 0
    for d in range(2, 15):
        r = (d-1).bit_length()
        q = 1 << r
        assert gf2_rank([(1 << r) | i for i in range(d)]) == r+1
        sy = [syndrome(z, d) for z in range(1 << d)]
        X = [z for z in range(1 << d) if z.bit_count() % 2 == 0]
        Y = [z for z in range(1 << d) if z.bit_count() % 2]
        fibers = Counter(sy[y] for y in Y)
        assert set(fibers) == set(range(q))
        assert set(fibers.values()) == {len(Y)//q}
        neighborhoods = []
        for x in X:
            classes = [sy[x ^ (1 << i)] for i in range(d)]
            assert len(set(classes)) == d
            assert classes == [sy[x] ^ i for i in range(d)]
            neighborhoods.append(sum(1 << s for s in classes))
        if d <= 9:
            for c in range(q):
                members = [y for y in Y if sy[y] == c]
                for a, b in combinations(members, 2):
                    assert (a ^ b).bit_count() >= 4
                    pairs += 1
        for tau in range(1, (d-1)//2+1):
            S = set(range(tau)) | {q//2+i for i in range(tau)}
            smask = sum(1 << s for s in S)
            T = [y for y in Y if sy[y] in S]
            assert len(T) == 2*tau*len(Y)//q
            assert F(len(T), len(Y)) <= F(2*tau, d)
            for classes in neighborhoods:
                meet = (classes & smask).bit_count()
                assert tau <= meet <= 2*tau < d
                neighbor_cases += 1
    # Actual theorem values of t: test the syndrome arithmetic without
    # allocating the exponentially many cube vertices.
    # d=79 is admissible but d=80 is not, because t jumps from 39 to 40.
    assert 2*t_value(79) < 79 and 2*t_value(80) == 80
    for d in [79, 81, 127, 128, 129, 255, 256, 257, 511, 512, 1024, 4096]:
        t = t_value(d)
        assert 2*t < d
        r = (d-1).bit_length()
        q = 1 << r
        assert gf2_rank([(1 << r) | i for i in range(d)]) == r+1
        S = set(range(t)) | {q//2+i for i in range(t)}
        for shift in range(q):
            meet = sum((shift ^ s) < d for s in S)
            assert t <= meet <= 2*t < d
            admissible_shift_cases += 1
    return pairs, neighbor_cases, admissible_shift_cases


def find_matching(domains):
    owner = {}

    def augment(x, seen):
        for a in domains[x]:
            if a in seen:
                continue
            seen.add(a)
            if a not in owner or augment(owner[a], seen):
                owner[a] = x
                return True
        return False

    for x in domains:
        assert augment(x, set()), "Hall failed in the actual certificate"
    result = {x: a for a, x in owner.items()}
    assert len(result) == len(domains)
    assert len(set(result.values())) == len(domains)
    assert all(result[x] in domains[x] for x in domains)
    return result


def maximum_weighted_load(domains, coefficients, N):
    denom = lcm(*(len(D) for D in domains.values()))
    loads = [0]*N
    for x, D in domains.items():
        w = coefficients[x]*(denom//len(D))
        for a in D:
            loads[a] += w
    return F(max(loads), denom)


def hadamard_certificate():
    # P_ab=1[dot(a,b)=0]. E=P-J/2=H/2 and HH^T=N I, so K=1/2.
    # Directly check the Walsh identity at an independently allocatable size.
    small = 16
    for a in range(small):
        for b in range(small):
            inner = sum((-1)**((a & j).bit_count()+(b & j).bit_count())
                        for j in range(small))
            assert inner == (small if a == b else 0)
    r, d, tau = 18, 5, 1
    N = 1 << r
    M = N-1
    X = [x for x in range(1 << d) if x.bit_count() % 2 == 0]
    Y = [y for y in range(1 << d) if y.bit_count() % 2]
    q = 1 << (d-1).bit_length()
    S = {0, q//2}
    T = [y for y in Y if syndrome(y, d) in S]
    J = [y for y in Y if y not in T]
    g = dict(zip(J, RNG.sample(range(1, N), len(J))))
    g_initial = dict(g)
    assert F(N, len(X)) >= 10000*F(5, 4)
    assert 2*t_value(d) >= d  # Deliberately NOT a large-d theorem instance.

    def edge(a, b):
        return (a & b).bit_count() % 2 == 0

    assert all(edge(a, 0) for a in range(N))
    # A is exactly the row-degree-pruned set in this implicit example:
    assert abs(F(N//2-1, N-1)-F(1, 2)) <= F(1, 100*d)
    assert abs(F(1)-F(1, 2)) > F(1, 100*d)
    neighbors = {x: [x ^ (1 << i) for i in range(d)] for x in X}
    h = {x: sum(y in g for y in neighbors[x]) for x in X}
    domains = {x: [a for a in range(1, N)
                   if all(edge(a, g[y]) for y in neighbors[x] if y in g)]
               for x in X}
    initial_sizes = {x: len(D) for x, D in domains.items()}
    assert all(len(domains[x]) >= F(M, 1 << (h[x]+1)) for x in X)
    initial_load = maximum_weighted_load(domains, {x: 1 for x in X}, N)
    assert initial_load < F(1, 64)
    remaining = {x: sum(y in T for y in neighbors[x]) for x in X}
    Gamma = maximum_weighted_load(domains, {x: 4**remaining[x] for x in X}, N)
    Lambda = 4*N*max(sum(F(4**(remaining[x]-1), initial_sizes[x])
                         for x in X if y in neighbors[x]) for y in T)
    assert Gamma < 1 and Lambda < N-len(J)-len(T)
    prefixes = []

    def verify_and_record(new_y):
        f = find_matching(domains)
        odd = {y: g.get(y, 0) for y in Y}
        assert len(set(g.values())) == len(g) and 0 not in g.values()
        assert all(a != 0 for a in f.values())
        for x in X:
            for y in neighbors[x]:
                assert edge(f[x], odd[y])
        prefixes.append({"new_odd_label": new_y,
                         "odd_images_separated": dict(sorted(g.items())),
                         "even_images": dict(sorted(f.items())),
                         "domain_sizes": {x: len(domains[x]) for x in X}})
        return f, odd

    f, odd = verify_and_record(None)
    k = {x: 0 for x in X}
    for y in T:
        affected = [x for x in X if y in neighbors[x]]
        occupied = set(g.values()) | {0}
        chosen = None
        for b in range(1, N):
            if b in occupied:
                continue
            cuts = {x: [a for a in domains[x] if edge(a, b)] for x in affected}
            if all(4*len(cuts[x]) >= len(domains[x]) for x in affected):
                chosen = b
                break
        assert chosen is not None
        g[y] = chosen
        for x in affected:
            domains[x] = cuts[x]
            k[x] += 1
            assert len(domains[x])*4**k[x] >= initial_sizes[x]
        f, odd = verify_and_record(y)
    assert len(g) == len(Y) and len(set(odd.values())) == len(Y)
    final_load = maximum_weighted_load(domains, {x: 1 for x in X}, N)
    assert final_load <= Gamma
    full_image = {z: ("B", odd[z]) if z.bit_count() % 2 else ("L", f[z])
                  for z in range(1 << d)}
    assert len(set(full_image.values())) == 1 << d
    squares = 0
    for i, j in combinations(range(d), 2):
        for z in range(1 << d):
            if (z >> i & 1) or (z >> j & 1):
                continue
            face = [z, z ^ (1 << i), z ^ (1 << i) ^ (1 << j), z ^ (1 << j)]
            assert len({full_image[v] for v in face}) == 4
            for u, v in zip(face, face[1:]+face[:1]):
                if u in f:
                    assert edge(f[u], odd[v])
                else:
                    assert edge(f[v], odd[u])
            squares += 1
    cert = {"scope": "small-dimension audit, not a theorem-admissible dimension",
            "host": "P_ab = 1[dot_F2(a,b)=0], disjoint copies of F2^18",
            "N": N, "K": "1/2", "d": d, "toy_t": tau,
            "T": T, "initial_g": g_initial,
            "initial_max_load": str(initial_load), "Gamma": str(Gamma),
            "Lambda": str(Lambda), "final_max_load": str(final_load),
            "prefixes": prefixes, "verified_edges": d*len(X),
            "verified_coordinate_squares": squares}
    (ROOT / "CubeAnchorCapacityRenewalCertificates.json").write_text(
        json.dumps(cert, indent=2, sort_keys=True)+"\n")
    return len(prefixes), d*len(X), squares, initial_load, final_load


def replay_certificate():
    """Independent replay, using GF(2) ranks instead of domain enumeration."""
    cert = json.loads((ROOT / "CubeAnchorCapacityRenewalCertificates.json").read_text())
    N, d = cert["N"], cert["d"]
    r = N.bit_length()-1
    assert N == 1 << r
    X = {z for z in range(1 << d) if z.bit_count() % 2 == 0}
    Y = set(range(1 << d))-X
    count = 0
    previous_odd = None
    for state in cert["prefixes"]:
        f = {int(x): a for x, a in state["even_images"].items()}
        g = {int(y): b for y, b in state["odd_images_separated"].items()}
        sizes = {int(x): s for x, s in state["domain_sizes"].items()}
        assert set(f) == X and set(g) <= Y
        assert len(set(f.values())) == len(X) and len(set(g.values())) == len(g)
        assert all(0 < v < N for v in list(f.values())+list(g.values()))
        if previous_odd is not None:
            assert len(g) == len(previous_odd)+1
            assert all(g[y] == b for y, b in previous_odd.items())
        previous_odd = g
        for x in X:
            columns = [g[y] for i in range(d) if (y := x ^ (1 << i)) in g]
            rank = gf2_rank(columns)
            assert sizes[x] == (1 << (r-rank))-1
            assert all((f[x] & b).bit_count() % 2 == 0 for b in columns)
            count += 1
    assert set(g) == Y
    assert cert["verified_edges"] == d*(1 << (d-1))
    assert cert["verified_coordinate_squares"] == d*(d-1)//2*(1 << (d-2))
    return count


def main():
    got = hashlib.sha256((ROOT / "Spec.lean").read_bytes()).hexdigest()
    assert got == SPEC_SHA
    print("Spec.lean SHA-256:", got, flush=True)
    print("Exact all-orders Gram/direct-sampling cases:", gram_checks(), flush=True)
    print("Permutation forcing (queries, input/output pairs, preserved positions):",
          coupling_checks(), flush=True)
    print("Conditional LLL (families, ALL partial queries, hit-set cylinders, polynomial moments):",
          conditional_lll_checks(), flush=True)
    print("Exact read-d Holder moment cases:", read_d_checks(), flush=True)
    print("Finite-population / distinct-sampling cases:", finite_population_checks(), flush=True)
    print("Range-pruning and renormalization cases:", range_pruning_checks(), flush=True)
    print("Constant budgets (parameter cases, dimensions, largest dimension bit-length):",
          constant_checks(), flush=True)
    print("Syndromes (same-class pairs, explicit neighbor cases, theorem-scale shifts):",
          syndrome_checks(), flush=True)
    print("Hadamard certificate (actual matching prefixes, edges, squares, initial/final max load):",
          hadamard_certificate(), flush=True)
    print("Independent certificate replay, GF(2)-rank/domain cases:", replay_certificate(), flush=True)
    assert hashlib.sha256((ROOT / "Spec.lean").read_bytes()).hexdigest() == SPEC_SHA
    print("PASS: all audits. The full constant-C embedding and capacity renewal remain UNPROVED.")


if __name__ == "__main__":
    main()
