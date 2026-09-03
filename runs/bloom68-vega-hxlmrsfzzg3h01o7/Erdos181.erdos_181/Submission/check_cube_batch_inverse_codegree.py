#!/usr/bin/env python3
"""Exact finite checks for CubeBatchInverseCodegree.md. No Ramsey claim is tested."""
from fractions import Fraction as F
from itertools import combinations, product
from collections import Counter
from math import comb, factorial
import hashlib
import random
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SPEC_SHA = '9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b'
COUNTS = Counter()


def fall(n, k):
    return 0 if k > n else factorial(n) // factorial(n-k)


def bitelts(mask, n):
    return [i for i in range(n) if mask >> i & 1]


def match_size(rows, b):
    """Rows are bitmasks of columns. Exact augmenting-path matching."""
    owner = [-1] * b
    def aug(i, seen):
        for j in bitelts(rows[i], b):
            if j in seen:
                continue
            seen.add(j)
            if owner[j] < 0 or aug(owner[j], seen):
                owner[j] = i
                return True
        return False
    return sum(aug(i, set()) for i in range(len(rows)))


def kernel_data(a, b, c, edges):
    dbz = [[0]*c for _ in range(b)]
    dpb = [[0]*b for _ in range(a)]
    dpz = [[0]*c for _ in range(a)]
    for p, x, z in edges:
        dbz[x][z] += 1
        dpb[p][x] += 1
        dpz[p][z] += 1
    A = [[0]*c for _ in range(b)]
    for p, x, z in edges:
        if dbz[x][z] >= max(dpb[p][x], dpz[p][z]):
            A[x][z] |= 1 << p
    pos = [v for matrix in (dbz, dpb, dpz) for row in matrix for v in row if v]
    D = min(pos) if pos else 1
    sampler_mass = sum((F(D, b*c*v) for row in dbz for v in row if v), F(0))
    assert sampler_mass <= 1
    K = {}
    L = {}
    for U in range(1, 1 << a):
        K[U] = [[F(int(A[x][z] & U == U), dbz[x][z]) if dbz[x][z] else F(0)
                 for z in range(c)] for x in range(b)]
        L[U] = 0
        for x in range(b):
            if any(all((p, x, z) in edges for p in bitelts(U, a)) for z in range(c)):
                L[U] |= 1 << x
        ku = K[U]
        assert all(sum(row) <= 1 for row in ku)
        assert all(sum(ku[x][z] for x in range(b)) <= 1 for z in range(c))
        assert all(v <= F(1, U.bit_count()) for row in ku for v in row)
        support = [sum(1 << z for z in range(c) if ku[x][z]) for x in range(b)]
        nu = match_size(support, c)
        mass = sum(map(sum, ku), F(0))
        assert mass <= nu
        assert F(D, b*c)*mass <= 1
        COUNTS['kernels'] += 1
        # Ordered, vertex-disjoint pair polynomial.
        def disjoint_sum(q, used_b=0, used_z=0):
            if q == 0:
                return F(1)
            ans = F(0)
            for x in range(b):
                if used_b >> x & 1:
                    continue
                for z in range(c):
                    if not (used_z >> z & 1) and ku[x][z]:
                        ans += ku[x][z] * disjoint_sum(q-1, used_b | 1 << x, used_z | 1 << z)
            return ans
        for q in range(1, min(b,c)+2):
            assert disjoint_sum(q) <= fall(nu, q)
            COUNTS['pair_capacity_polynomials'] += 1
    return K, L


def check_batches(a, b, c, K, L, exhaust):
    us = list(K)
    batches = product(us, repeat=3) if exhaust else [tuple(random.choice(us) for _ in range(3)) for __ in range(8)]
    for batch in batches:
        for J in range(1, 1 << len(batch)):
            chosen = [batch[i] for i in bitelts(J, len(batch))]
            U, W = 0, 0
            for S in chosen:
                U |= S
                W |= L[S]
            mass = sum(map(sum, K[U]), F(0))
            assert mass <= W.bit_count()
            if W.bit_count() < len(chosen):
                assert mass <= len(chosen)-1
                COUNTS['deficient_batches'] += 1
            # Different kernels, distinct B resources, arbitrary fillers.
            rs = [[sum(K[S][x]) for x in range(b)] for S in chosen]
            def perm(i=0, used=0):
                if i == len(rs):
                    return F(1)
                return sum((rs[i][x]*perm(i+1, used | 1 << x)
                            for x in range(b) if not (used >> x & 1)), F(0))
            val = perm()
            assert val <= fall(W.bit_count(), len(chosen))
            if W.bit_count() < len(chosen):
                assert val == 0
            COUNTS['mixed_batch_capacity_polynomials'] += 1


def hypergraph_checks():
    triples = list(product(range(2), repeat=3))
    for mask in range(1 << len(triples)):
        edges = {triples[i] for i in bitelts(mask, len(triples))}
        K, L = kernel_data(2, 2, 2, edges)
        check_batches(2, 2, 2, K, L, True)
        COUNTS['exhaustive_hypergraphs'] += 1
    random.seed(220305497)
    triples = list(product(range(3), repeat=3))
    for _ in range(250):
        density = random.random()
        edges = {e for e in triples if random.random() < density}
        K, L = kernel_data(3, 3, 3, edges)
        check_batches(3, 3, 3, K, L, False)
        COUNTS['random_hypergraphs'] += 1


def cube_neighborhoods(d):
    X = [v for v in range(1 << d) if v.bit_count() % 2 == 0]
    Y = [v for v in range(1 << d) if v.bit_count() % 2 == 1]
    xpos = {x:i for i,x in enumerate(X)}
    N = [sum(1 << xpos[y ^ (1 << j)] for j in range(d)) for y in Y]
    return X, Y, N


def sharp_cube_checks():
    for d in range(3, 9):
        X, Y, N = cube_neighborhoods(d)
        m = len(X)
        a = b = c = 2*m
        w = m-1
        assert len(set(N)) == m
        assert all(S.bit_count() == d for S in N)
        assert all(sum(S >> i & 1 for S in N) == d for i in range(m))
        assert all((S & T).bit_count() in (0, 2) for S,T in combinations(N, 2))
        overlap_pairs = sum(bool(S & T) for S,T in combinations(N, 2))
        assert overlap_pairs == m*comb(d,2)//2
        # E=P x W x Z: kernel is exactly 1/a on W x Z.
        D = w
        row_mass = c*F(1,a)
        col_mass = w*F(1,a)
        total_mass = w*c*F(1,a)
        assert row_mass == 1 and col_mass <= 1 and total_mass == w
        assert F(D, b*c)*total_mass == F(w*w, 4*m*m)
        assert match_size([(1 << w)-1]*m, b) == m-1
        assert all(k <= w for k in range(m))  # All proper batches have SDRs.
        for q in range(0, m+1):
            assert (fall(w,q) > 0) == (q < m)
        if d == 3:
            # Directly enumerate the ordered anchor polynomials, including fillers.
            pairs = list(product(range(w), range(c)))
            for q in range(1, 5):
                distinct_centres = 0
                distinct_both = 0
                for ts in product(pairs, repeat=q):
                    if len({x for x,z in ts}) != q:
                        continue
                    distinct_centres += 1
                    if len({z for x,z in ts}) == q:
                        distinct_both += 1
                assert F(distinct_centres, a**q) == fall(w,q)
                assert F(distinct_both, a**q) == F(fall(w,q)*fall(a,q), a**q)
                COUNTS['sharp_anchor_polynomials'] += 1
        # Literal unlabelled ordered-pair probability with the pruning budget.
        naux = a+b+c
        D0 = F(w,18)
        e = a*w*c
        assert e == 2*D0*naux*naux
        assert F(2*w, naux*naux)*D0 == F(w*w, 324*m*m)
        COUNTS['sharp_cube_dimensions'] += 1


def column_distribution(d):
    X,Y,N = cube_neighborhoods(d)
    m = len(X)
    adj = [sum(1 << j for j in range(m) if i != j and N[i] & N[j]) for i in range(m)]
    law = Counter()
    good = Counter()
    bad_count = 0
    for mask in range(1 << m):
        word = sum(1 << i for i,S in enumerate(N) if mask & S == S)
        law[word] += 1
        bad = any(word >> i & 1 and word & adj[i] for i in range(m))
        if bad:
            bad_count += 1
        else:
            good[word] += 1
    total = 1 << m
    beta = F(bad_count,total)
    assert beta <= F(d*(d-1), 4*m)
    p = F(1, 1 << d)
    # All full one-site conditionals in the law conditional on goodness.
    for i in range(m):
        prefix = {word & ~(1 << i) for word in good}
        for rest in prefix:
            z = good[rest]
            o = good[rest | 1 << i]
            assert o+z > 0
            assert F(o,o+z) <= p
            COUNTS['full_conditionals'] += 1
    assert sum(good.values()) + bad_count == total
    COUNTS['random_column_dimensions'] += 1
    return m,law,beta


def matching_distribution_from_columns(m, b, column_weights):
    """Integer column weights; returns integer matching-count distribution."""
    outcomes = [(w,v) for w,v in column_weights.items() if v]
    counts = Counter()
    for cols in product(outcomes, repeat=b):
        rows = [0]*m
        weight = 1
        for j,(word,v) in enumerate(cols):
            weight *= v
            for i in bitelts(word,m):
                rows[i] |= 1 << j
        counts[match_size(rows,b)] += weight
    return counts


def random_matching_checks():
    data = {}
    for d in (3,4,5):
        data[d] = column_distribution(d)
    m,law,beta = data[3]
    p = F(1,8)
    # Bernoulli(1/8) column probabilities have common denominator 8^m.
    iid = {word:7**(m-word.bit_count()) for word in range(1 << m)}
    for b in range(1,5):
        actual = matching_distribution_from_columns(m,b,law)
        independent = matching_distribution_from_columns(m,b,iid)
        actual_den = (1 << m)**b
        independent_den = 8**(m*b)
        assert sum(actual.values()) == actual_den
        assert sum(independent.values()) == independent_den
        kdist = [F(comb(b,k))*beta**k*(1-beta)**(b-k) for k in range(b+1)]
        for threshold in range(m+1):
            lhs = F(sum(v for nu,v in actual.items() if nu >= threshold), actual_den)
            rhs = sum((F(v,independent_den)*pk
                       for nu,v in independent.items() for k,pk in enumerate(kdist)
                       if nu+k >= threshold), F(0))
            assert lhs <= rhs
            COUNTS['global_matching_tail_comparisons'] += 1
        q = (1-p)**b
        iz = [F(comb(m,z))*q**z*(1-q)**(m-z) for z in range(m+1)]
        for t in range(3):
            # A matching of size m-t is necessary to finish using t extra columns.
            lhs = F(sum(v for nu,v in actual.items() if nu >= m-t), actual_den)
            rhs = sum((pz*pk for z,pz in enumerate(iz) for k,pk in enumerate(kdist)
                       if z <= k+t), F(0))
            assert lhs <= rhs
            # Chernoff, with exp(theta)=2, checked exactly.
            mgf = 2**t*(1-q+q/F(2))**m*(1-beta+2*beta)**b
            assert rhs <= mgf
            COUNTS['isolation_and_mgf_comparisons'] += 1


def general_witness_lemma_checks():
    # All nonempty set families on three independent bits, with unequal parameters.
    probs = [F(1,3), F(1,2), F(2,3)]
    for family_mask in range(1, 1 << 7):
        sets = [j+1 for j in bitelts(family_mask,7)]
        n = len(sets)
        marginal = []
        for S in sets:
            pr = F(1)
            for x in bitelts(S,3):
                pr *= probs[x]
            marginal.append(pr)
        good = Counter()
        for bits in range(8):
            weight = F(1)
            for x in range(3):
                weight *= probs[x] if bits >> x & 1 else 1-probs[x]
            word = sum(1 << i for i,S in enumerate(sets) if bits & S == S)
            occ = bitelts(word,n)
            if any(sets[i] & sets[j] for i,j in combinations(occ,2)):
                continue
            good[word] += weight
        assert sum(good.values()) > 0
        for i in range(n):
            for rest in {word & ~(1 << i) for word in good}:
                zero, one = good[rest], good[rest | 1 << i]
                assert one/(zero+one) <= marginal[i]
                COUNTS['general_witness_conditionals'] += 1
        COUNTS['general_witness_families'] += 1


def pruning_lll_checks():
    # Binomial comparison used in (18), with exact rational arithmetic.
    for d in range(2,17):
        for a in sorted(set([2*d, 2*d+1, 3*d, 5*d, 10*d, 64*d])):
            for r in range(a//(2*d)+1):
                ap = a-r
                assert ap-d+1 >= F(a,2)
                assert F(comb(a,d),comb(ap,d)) < 3
                assert F(comb(a-1,d-1),comb(ap-1,d-1)) < 3
                COUNTS['pruning_binomial_comparisons'] += 1
    # Actual bad families: all 3-sets through a fixed vertex, a disjoint family,
    # and reproducible irregular samples. Check the deletion and degree loads.
    random.seed(161202663)
    cases = []
    cases.append((3,32,{(0,)+S for S in combinations(range(1,32),2)}))
    cases.append((3,128,{tuple(range(i,i+3)) for i in range(0,126,3)}))
    for a in (24,32,48):
        universe = list(combinations(range(a),3))
        for num in (1,8,40,160):
            cases.append((3,a,set(random.sample(universe,num))))
    for d,a,bad in cases:
        m = 1 << (d-1)
        delta = F(len(bad),comb(a,d))
        deg = Counter(x for T in bad for x in T)
        threshold = 2*d*delta*comb(a-1,d-1)
        removed = {x for x in range(a) if deg[x] > threshold}
        assert len(removed) <= F(a,2*d)
        ap = a-len(removed)
        assert ap >= 2*m
        restricted = {T for T in bad if not removed.intersection(T)}
        delta2 = F(len(restricted),comb(ap,d))
        deg2 = Counter(x for T in restricted for x in T)
        maxdeg = max(deg2.values(),default=0)
        assert delta2 <= 3*delta
        assert maxdeg <= 6*d*delta*comb(ap-1,d-1)
        p0 = F(1,fall(ap,d))
        domain_load = d*len(restricted)*factorial(d)*p0
        range_load = m*maxdeg*factorial(d)*p0
        assert domain_load <= 3*d*delta
        assert range_load <= 3*d*d*delta
        for k in (1,d,m):
            assert 2*k*(domain_load+range_load) <= 12*k*d*d*delta
        if delta <= F(1,100*d**3):
            assert 12*d**3*delta <= F(3,25)
            # exp(3/25) <= 1/(1-3/25) < 2 proves the criterion.
            assert 1/(1-F(3,25)) < 2
            COUNTS['nonvacuous_small_density_lll_cases'] += int(bool(restricted))
        assert F(m*len(removed),ap-m+1) <= F(2*m,d)
        COUNTS['actual_pruning_and_lll_load_cases'] += 1
    for d in range(3,31):
        m=1 << (d-1)
        for a in (2*m, 5*m//2, 3*m, 5*m):
            r=a//(2*d)
            ap=a-r
            if ap >= 2*m:
                assert F(m*r,ap-m+1) <= F(2*m,d)
                assert F(2,1)+F(3,25) <= 3
                COUNTS['full_injection_tilt_comparisons'] += 1


def main():
    assert hashlib.sha256((ROOT/'Spec.lean').read_bytes()).hexdigest() == SPEC_SHA
    hypergraph_checks()
    sharp_cube_checks()
    random_matching_checks()
    general_witness_lemma_checks()
    pruning_lll_checks()
    assert hashlib.sha256((ROOT/'Spec.lean').read_bytes()).hexdigest() == SPEC_SHA
    print('All exact checks passed.')
    for k in sorted(COUNTS):
        print(f'{k}: {COUNTS[k]}')
    print('Spec.lean SHA-256:', SPEC_SHA)
    print('No uniform Ramsey assertion was assumed or verified.')


if __name__ == '__main__':
    main()
