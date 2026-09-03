"""Audit the uniform statements in PartialAffineB3.md.

This is not a full-flat or unrestricted partial-flat search.  It checks exact
identities on selected finite examples, plus the linear algebra of two members
of a proved infinite family.  Repeated factors are always included.

Run: sage Submission/partial_affine_b3_audit.sage
"""
from itertools import combinations, combinations_with_replacement, product
from collections import Counter, defaultdict
from pathlib import Path
import json
import random

ROOT = Path('/workspace/leanproject/Submission')
F2 = GF(2)
PR = PolynomialRing(F2, 'T')
T = PR.gen()
rng = random.Random(int(20260829))


def strong_b3(S):
    seen = set()
    for x,y,z in combinations_with_replacement(S, 3):
        value = x*y*z
        if value in seen:
            return False
        seen.add(value)
    return True


def reciprocal_sum(K, S):
    return sum((1/x for x in S), K.zero())


def random_flat(n,k):
    K = GF(2^n, 'z')
    V, frm, to = K.vector_space(map=True)
    U = [K.zero()]
    while len(U) < 2^k:
        v = frm(V([rng.randrange(2) for _ in range(n)]))
        if v not in U:
            U += [u+v for u in U]
    a = K.one()
    while a in U:
        a = frm(V([rng.randrange(2) for _ in range(n)]))
    return K, U, a


def linearized(P, x):
    K = x.parent()
    value = K.zero()
    power = x
    for coefficient in P.list():
        if coefficient:
            value += power
        power = power^2
    return value


def operator_matrix(K, P):
    V, frm, to = K.vector_space(map=True)
    cols = [to(linearized(P, frm(v))) for v in V.basis()]
    return matrix(F2, cols).transpose(), V, frm, to


def affine_solution_dimension(M, rhs):
    augmented = M.augment(matrix(F2, list(rhs)).transpose())
    if augmented.rank() != M.rank():
        return None
    return M.ncols() - M.rank()


def small_subset_audit(K, U, a, label):
    A = [a+u for u in U]
    aset = set(A)
    uset = set(U)
    m = len(A)
    assert len(aset) == m and K.zero() not in aset
    PP = PolynomialRing(K, 'X')
    X = PP.gen()
    P_U = prod(X-u for u in U)
    beta = P_U(a)
    u0 = P_U.derivative()[0]
    assert P_U.derivative().degree() == 0 and u0 != 0 and beta != 0
    R = reciprocal_sum(K, A)
    assert R == u0/beta and R != 0
    c0 = 1/R
    stable = set(x^2/c0 for x in A) == aset
    normalized = (P_U(c0*X)+beta)/(c0^m)
    coefficient_test = all(x == 0 or x == 1 for x in normalized.list())
    assert stable == coefficient_test
    if stable:
        k = int(ZZ(m).log(2))
        assert normalized[0] == 1 and normalized[1] == 1
        p = sum((F2(int(normalized[2^i] == 1))*T^i for i in range(k+1)), PR.zero())
        assert p.degree() == k and (T^K.degree()-1) % p == 0
        assert ((T^K.degree()-1)//p)(1) == 0

    b3_count = 0
    inverse_pair_checks = 0
    for mask in range(2^m):
        S = [x for i,x in enumerate(A) if (mask >> i) & 1]
        sset = set(S)
        D = [x for x in A if x not in sset]
        dset = set(D)
        N,d = len(S),len(D)
        pairs = list(combinations_with_replacement(S,2))
        pair_counts = Counter(x+y for x,y in pairs)
        ordered_pair_counts = Counter(x+y for x,y in product(S,repeat=2))
        assert pair_counts[K.zero()] == N
        for u in U:
            if u != 0:
                assert 2*pair_counts[u] == ordered_pair_counts[u]
                assert ordered_pair_counts[u] == len(sset & {x+u for x in sset})

        loads = Counter({z: int(z in sset) for z in A})
        reps = defaultdict(list)
        petals = defaultdict(list)
        for c in S:
            for x,y in pairs:
                if x == c or y == c:
                    continue
                center = x+y+c
                assert center in aset
                value = x*y/c
                u = center+c
                v = x+c
                assert v in uset and value == center+(v^2+u*v)/c
                assert value != center
                reps[value].append((c,x,y))
                petals[(center,c)].append(value)
                loads[center] += 1

        for z in A:
            for c in S:
                values = petals[(z,c)]
                assert len(values) == len(set(values))
                assert len(values) == pair_counts[z+c]-int(z in sset)

        conv_S3 = Counter(x+y+z for x,y,z in product(S,repeat=3))
        conv_D3 = Counter(x+y+z for x,y,z in product(D,repeat=3))
        for z in A:
            assert 2*loads[z] == conv_S3[z]-(N-2)*int(z in sset)
            assert conv_S3[z] == m^2-3*m*d+3*d^2-conv_D3[z]
            assert 0 <= conv_D3[z] <= d^2
            assert N*(2*N-m) <= conv_S3[z] <= m^2-3*m*d+3*d^2
        required = N + N*binomial(N,2)
        assert sum(loads.values()) == required

        packing = all(len(v) == 1 for v in reps.values()) and not (set(reps) & sset)
        b3 = strong_b3(S)
        assert packing == b3
        if b3:
            b3_count += 1
            assert len(set(reps) | sset) == required
            if stable:
                assert 3*N <= 2*m+int(c0 in aset)
            for a1,b1 in combinations(S,2):
                w = a1*b1
                rw = {u for u in U if u != 0 and w/u in uset}
                eps = int(w.sqrt() in uset)
                t = a1+b1
                dd = len(dset & {x+t for x in dset})
                assert len(rw)+eps <= 4*d-2*dd
                B = {x+a1 for x in dset} | {x+b1 for x in dset}
                assert len(B) == 2*d-dd
                for u in rw:
                    assert u in B or w/u in B
                inverse_pair_checks += 1
    return {
        'label':label, 'field_degree':int(K.degree()), 'flat_size':int(m),
        'field_modulus':str(K.modulus()),
        'affine_points':[int(x.integer_representation()) for x in A],
        'direction_points':[int(x.integer_representation()) for x in U],
        'affine_shift':int(a.integer_representation()),
        'subsets_checked':int(2^m), 'b3_subsets_checked':int(b3_count),
        'inverse_pair_checks':int(inverse_pair_checks),
        'scaled_frobenius_stable':bool(stable)
    }


def invariant_flat_audit(j, enumerate_points=False):
    ell = 4^j
    n = 5*ell
    k = (5*ell+1)//3
    t = (ell+2)//6
    Phi = T^4+T^3+T^2+T+1
    P = (T+1)^(ell-1)*Phi^t
    assert P.degree() == k and n == 3*k-1
    assert (T^n-1) % P == 0
    assert ((T^n-1)//P)(1) == 0
    K = GF(2^n, 'z')
    M,V,frm,to = operator_matrix(K,P)
    rhs = to(K.one())
    assert M.right_kernel().dimension() == k
    a = frm(M.solve_right(rhs))
    U_basis = [frm(v) for v in M.right_kernel().basis()]
    assert linearized(P,a) == 1
    assert linearized(P,a^2+a) == 0
    for u in U_basis:
        assert linearized(P,u) == 0 and linearized(P,u^2) == 0

    intersections = {}
    for degree,expected in [(n//2,None),(ell,ell-1)]:
        Msub,_,_,_ = operator_matrix(K,T^degree+1)
        stacked = M.stack(Msub)
        rr = vector(F2,list(rhs)+[0]*n)
        dim = affine_solution_dimension(stacked,rr)
        assert dim == expected
        intersections[str(degree)] = None if dim is None else int(dim)

    sample = next(x for x in [a]+[a+u for u in U_basis] if x^(2^ell) != x)
    assert linearized(P,sample) == 1
    y = sample^2
    order = 1
    while y != sample:
        y = y^2
        order += 1
    assert order == n
    size = 2^k
    short = 2^(ell-1)
    assert short % ell == 0 and (size-short) % n == 0
    expected_cycles = {int(ell):int(short//ell),int(n):int((size-short)//n)}
    orbit_bound = sum(count*((2*length)//3) for length,count in expected_cycles.items())
    result = {
        'j':int(j),'ell':int(ell),'n':int(n),'k':int(k),'t':int(t),
        'operator_polynomial':str(P),'flat_size':int(size),
        'maximal_subfield_intersection_dimensions':intersections,
        'full_field_sample_frobenius_order':int(order),
        'cycle_counts_from_proof':expected_cycles,
        'orbit_cardinality_upper_bound':int(orbit_bound),
        'cubic_ratio_upper_bound':float(QQ(orbit_bound^3)/(2^n-1))
    }
    if enumerate_points:
        U = [K.zero()]
        for u in U_basis:
            U += [x+u for x in U]
        A = {a+u for u in U}
        assert len(A) == size and K.zero() not in A and K.one() not in A
        assert {x^2 for x in A} == A
        assert reciprocal_sum(K,A) == 1
        unseen = set(A)
        cycles = Counter()
        while unseen:
            x = next(iter(unseen))
            y = x
            cycle = []
            while y not in cycle:
                assert y in unseen
                cycle.append(y)
                y = y^2
            assert y == x
            unseen.difference_update(cycle)
            cycles[len(cycle)] += 1
            for z in cycle:
                zz,z4 = z^2,z^4
                assert zz != z and zz^3 == z^2*z4
        assert dict(cycles) == expected_cycles
        result['enumerated_cycle_counts'] = {int(length):int(count) for length,count in cycles.items()}
        result['three_factor_identities_checked'] = int(size)
        assert orbit_bound == 82
    return result


def bose_reciprocal_audit(e):
    assert e % 3 == 1
    q = 2^e
    K = GF(q^3,'z')
    g = K.multiplicative_generator()
    theta = g^((q^3-1)//7)
    assert theta^7 == 1 and theta != 1 and theta^q == theta^2
    assert theta^q != theta
    h = g^((q^3-1)//(q-1))
    params = [K.zero()]+[h^i for i in range(q-1)]
    assert len(set(params)) == q and all(t^q == t for t in params)
    A = [theta+t for t in params]
    S = [theta+t for t in params if t != 0 and t != 1]
    assert len(S) == q-2 and strong_b3(A) and strong_b3(S)
    full = reciprocal_sum(K,A)
    assert full == 1/(theta^q+theta) and full != 0
    assert full == 1/theta+1/(theta+1)
    assert reciprocal_sum(K,S) == 0
    ratio = QQ(len(S)^3)/(q^3-1)
    assert ratio < 1
    return {
        'e':int(e),'q':int(q),'field_degree':int(3*e),
        'affine_binary_dimension':int(e),'full_size':int(q),'partial_size':int(q-2),
        'partial_density':str(QQ(q-2)/q),
        'full_repeated_triples_checked':int(binomial(q+2,3)),
        'partial_repeated_triples_checked':int(binomial(q,3)),
        'full_reciprocal_nonzero':True,'partial_reciprocal_zero':True,
        'cubic_ratio':str(ratio),'cubic_ratio_decimal':float(ratio)
    }


report = {'status':'scoped uniform results only; unrestricted critical problem unresolved'}
report['partial_identities'] = []
for n,k in [(5,2),(8,3),(9,3)]:
    K,U,a = random_flat(n,k)
    report['partial_identities'].append(small_subset_audit(K,U,a,'selected_random_flat'))
# A Frobenius-stable critical 8-point example checks the orbit bound on every subset.
K = GF(2^8,'z')
P = (T+1)^3
M,V,frm,to = operator_matrix(K,P)
a = frm(M.solve_right(to(K.one())))
U = [K.zero()]
for v in M.right_kernel().basis():
    u = frm(v)
    U += [x+u for x in U]
report['partial_identities'].append(small_subset_audit(K,U,a,'frobenius_stable_8_point_flat'))
print('Partial flower and actual reciprocal-intersection identities verified.',flush=True)
report['critical_invariant_family'] = [invariant_flat_audit(1,True),invariant_flat_audit(2,False)]
print('Infinite-family linear algebra and the 128-point cycle certificate verified.',flush=True)
report['reciprocal_cancellation_bose'] = [bose_reciprocal_audit(4),bose_reciprocal_audit(7)]
print('Bose reciprocal cancellation verified with repeated triples at q=16,128.',flush=True)
out = ROOT/'partial_affine_b3_audit.json'
with out.open('w') as f:
    json.dump(report,f,indent=2)
print(json.dumps(report,indent=2))
