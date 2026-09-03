"""Run with: sage -python Submission/quadratic_switching_density_audit.py.

Exact audits for QuadraticSwitchingDensity.md.  No subset search is used
as asymptotic evidence.  The large-field incidence statistics are diagnostic;
the uniform mixing theorem is proved in the accompanying note.
"""
import os
os.environ['OPENBLAS_NUM_THREADS'] = '1'
import hashlib
import itertools
import json
import time
from collections import Counter, defaultdict
from pathlib import Path

import numpy as np
from sage.all import GF, PolynomialRing, prod

ROOT = Path(__file__).resolve().parent
PROTECTED = ('Spec.lean', 'Reductions.lean')


def hashes():
    return {name: hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
            for name in PROTECTED}


def monic_irreducibles(F, degree):
    R = PolynomialRing(F, 'X')
    X = R.gen()
    for cs in itertools.product(list(F), repeat=degree):
        g = X**degree + sum((cs[i]*X**i for i in range(degree)), R.zero())
        if g.is_irreducible():
            yield g


def eligible_quadratics(F, f):
    for W in monic_irreducibles(F, 2):
        if not f.resultant(W).is_square():
            yield W


def universal_discriminant_audit(F, f, W):
    B = PolynomialRing(F, ['t', 'a'])
    t, a = B.gens()
    RX = PolynomialRing(B, 'x')
    x = RX.gen()
    ff, ww = RX(f.list()), RX(W.list())
    C, rem = (ff(t)*ww*(x-a)**2 - ww(t)*ff*(t-a)**2).quo_rem(x-t)
    assert rem == 0
    D = C.discriminant()
    assert D.degree(t) <= 12 and D.degree(a) <= 8
    fac = list(D.factor())
    assert any(e % 2 and g.degree(t) > 0 and g.degree(a) > 0 for g,e in fac)

    # Both f and W split here; this also works when F is not prime.
    L = F.extension(6, 'z')
    A = PolynomialRing(L, 'a')
    aa = A.gen()
    RL = PolynomialRing(L, 'X')
    fl, wl = RL(f.list()), RL(W.list())
    alpha = fl.roots()[0][0]
    beta, betap = [z for z,_ in wl.roots()]

    def specialize(poly, tv):
        return sum((L(c)*tv**ti*aa**ai
                    for (ti,ai),c in poly.dict().items()), A.zero())

    # Specialize the UNIVERSAL CUBIC discriminant; computing a quadratic
    # discriminant after the degree drop would be a different operation.
    ga = fl.quo_rem(RL.gen()-alpha)[0]
    assert specialize(D, alpha) == wl(alpha)**4*ga.discriminant()*(aa-alpha)**8
    wt = t*t + B(W[1])*t + B(W[0])
    Dbar, rem = D.quo_rem(wt)
    assert rem == 0
    assert specialize(Dbar, beta) == (
        4*fl(beta)**3*(aa-beta)*(aa-betap)**3*A(f.list()))
    return {'q': int(F.cardinality()), 'f': str(f), 'W': str(W),
            'factor_bidegrees_over_Fq': [
                [int(g.degree(t)), int(g.degree(a)), int(e)] for g,e in fac],
            'specializations_14_15': True}


def disc_columns(F, f, W, ts):
    A = PolynomialRing(F, 'a')
    a = A.gen()
    RX = PolynomialRing(A, 'x')
    x = RX.gen()
    ff, ww = RX(f.list()), RX(W.list())
    keys, exceptional = [], []
    for i,t in enumerate(ts):
        C, rem = (f(t)*ww*(x-a)**2-W(t)*ff*(t-a)**2).quo_rem(x-t)
        assert rem == 0
        D = C.discriminant()
        assert D != 0
        key = prod([g.monic() for g,e in D.factor() if e % 2], A.one())
        keys.append(key)
        if D.degree() != 8 or key.degree() == 0:
            exceptional.append(i)
    hist = Counter(keys)
    return keys, exceptional, max(hist.values())


def audit_case(F, f, W, direct=False, subsets=False, statistics=False):
    q = int(F.cardinality())
    R = f.parent()
    X = R.gen()
    ts = list(F)
    assert f.is_irreducible() and W.is_irreducible()
    c = f.resultant(W)
    assert not c.is_square()
    eps = [1 if (-f(t)).is_square() else -1 for t in ts]
    prime = F.is_prime_field()
    if prime:
        ints = [int(t) for t in ts]
        coeff = [-int(W(t))*pow(int(f(t)), -1, q) % q for t in ts]
        fcs = [int(f[i]) for i in range(4)]
        wcs = [int(W[i]) for i in range(3)]
    else:
        coeff = [-W(t)/f(t) for t in ts]

    mat = np.zeros((q,q), dtype=np.float64)
    edges = set()
    all_split = 0
    for ai,a in enumerate(ts):
        buckets = defaultdict(list)
        for ti,t in enumerate(ts):
            if ai != ti:
                k = (coeff[ti]*(ints[ti]-ints[ai])**2 % q if prime
                     else coeff[ti]*(t-a)**2)
                buckets[k].append(ti)
        for k, roots in buckets.items():
            assert len(roots) <= 4
            if len(roots) != 4:
                continue
            all_split += 1
            assert prod(eps[t] for t in roots) == -1
            if prime:
                # Independent integer coefficient multiplication.
                pcs = [1]
                for ti in roots:
                    out = [0]*(len(pcs)+1)
                    for j,b in enumerate(pcs):
                        out[j] = (out[j]-ints[ti]*b) % q
                        out[j+1] = (out[j+1]+b) % q
                    pcs = out
                expect = [0]*5
                for i,b in enumerate(wcs):
                    for j,d in enumerate([ints[ai]**2, -2*ints[ai], 1]):
                        expect[i+j] = (expect[i+j]+b*d) % q
                for i,b in enumerate(fcs):
                    expect[i] = (expect[i]+int(k)*b) % q
                assert pcs == expect
            else:
                P = prod([X-ts[i] for i in roots], R.one())
                assert P == W*(X-a)**2+k*f
            if sum(eps[i] for i in roots) == 2*eps[ai]:
                edge = (ai, tuple(sorted(roots)))
                assert edge not in edges
                edges.add(edge)
                mat[ai,roots] = 1
    assert int(mat.sum()) == 4*len(edges)
    assert all(int(s) % 4 == 0 for s in mat.sum(axis=1))

    report = {'q': q, 'field_modulus': str(F.modulus()), 'f': str(f), 'W': str(W),
              'sigma': sum(eps), 'split_distinct_quartics': all_split,
              'good_quartic_fibers': len(edges),
              'all_split_polynomial_identities_verified': True}
    collision_masks = []
    if direct:
        K = F.extension(f, 'theta')
        # Relative extension construction can use a different absolute generator.
        RK = PolynomialRing(K, 'X')
        theta = RK(f.list()).roots()[0][0]
        w = W(theta)
        us = [(theta-K(t)) if e == 1 else w/(theta-K(t))
              for t,e in zip(ts,eps)]
        assert len(set(us)) == q
        m = (q**3-1)//2
        assert w**m == -1
        assert all(u**m == 1 for u in us)
        assert all((theta-K(t))**m == e for t,e in zip(ts,eps))
        ps = [us[i]*us[j] for i,j in itertools.combinations_with_replacement(range(q),2)]
        assert len(ps) == len(set(ps))
        seen = defaultdict(list)
        recovered = set()
        triple_pairs = 0
        for I in itertools.combinations_with_replacement(range(q),3):
            v = prod(us[i] for i in I)
            for J in seen[v]:
                triple_pairs += 1
                assert set(I).isdisjoint(J)
                collision_masks.append(sum(1 << i for i in set(I+J)))
                I0,J0 = I,J
                ri = sum(eps[i] == -1 for i in I0)
                rj = sum(eps[i] == -1 for i in J0)
                assert ri != rj
                if ri > rj:
                    I0,J0,ri,rj = J0,I0,rj,ri
                if rj-ri == 1:
                    P = [i for i in I0 if eps[i] == 1] + [j for j in J0 if eps[j] == -1]
                    Q = [i for i in I0 if eps[i] == -1] + [j for j in J0 if eps[j] == 1]
                    if Q[0] == Q[1] and len(set(P)) == 4:
                        recovered.add((Q[0], tuple(sorted(P))))
            seen[v].append(I)
        assert recovered == edges
        report['direct_repeated_triples_checked'] = q*(q+1)*(q+2)//6
        report['direct_collision_pairs'] = triple_pairs
        report['quartic_edges_equal_direct_square_Q_collisions'] = True

    if subsets:
        rowmasks = [sum(1 << t for t in range(q) if mat[a,t]) for a in range(q)]
        degrees = [int(mat[a].sum()) for a in range(q)]
        emasks = [sum(1 << t for t in set((a,)+roots)) for a,roots in edges]
        tested = b3_count = 0
        for mask in range(1 << q):
            quartic_free = not any(mask & e == e for e in emasks)
            b3 = not any(mask & e == e for e in collision_masks)
            if b3:
                b3_count += 1
                assert quartic_free
            if quartic_free:
                tested += 1
                lhs4 = sum(degrees[a] for a in range(q) if mask >> a & 1)
                rhs = sum(degrees[a]-(rowmasks[a]&mask).bit_count()
                          for a in range(q) if mask >> a & 1)
                assert lhs4 <= 4*rhs
        report['all_parameter_subsets_checked'] = 1 << q
        report['quartic_free_subsets_cover_inequality_verified'] = tested
        report['strong_B3_subsets_independently_checked'] = b3_count

    if statistics:
        keys, bad, maxfiber = disc_columns(F, f, W, ts)
        report['degree_or_square_discriminant_exceptions'] = len(bad)
        report['maximum_geometric_discriminant_square_class_fiber'] = maxfiber
        report['blocks'] = []
        bad = set(bad)
        for sg in [1,-1]:
            ais = [i for i in range(q) if eps[i] == sg]
            for tg in [1,-1]:
                tis = [i for i in range(q) if eps[i] == tg]
                c0 = 1/8 if sg == tg else 1/24
                goodts = [i for i in tis if i not in bad]
                block = {'center_sign': sg, 'root_sign': tg,
                         'predicted_density': c0,
                         'observed_density': float(mat[np.ix_(ais,tis)].mean())
                         if ais and tis else None}
                if ais and goodts:
                    B = mat[np.ix_(ais,goodts)]-c0
                    gram = B.T @ B
                    for i,t in enumerate(goodts):
                        for j,s in enumerate(goodts):
                            if keys[t] == keys[s]:
                                gram[i,j] = 0
                    block['max_distinct_class_centered_covariance_over_sqrt_q'] = float(
                        np.abs(gram).max()/np.sqrt(q))
                report['blocks'].append(block)
    return report


def main():
    before = hashes()
    started = time.time()
    small, symbolic, large = [], [], []
    # Every eligible W for every irreducible f in the two smallest fields.
    for q in [3,5]:
        F = GF(q, 'v')
        for f in monic_irreducibles(F,3):
            for W in eligible_quadratics(F,f):
                small.append(audit_case(F,f,W,direct=True,subsets=True))
        print('all f,W checked at q=%d' % q, flush=True)
    # Every eligible W for one specified f in further small fields.
    for q in [7,9,11,13]:
        F = GF(q, 'v')
        f = next(monic_irreducibles(F,3))
        for W in eligible_quadratics(F,f):
            small.append(audit_case(F,f,W,direct=True,subsets=(q<=9)))
        print('all W checked for specified f at q=%d' % q, flush=True)
    # Bivariate identities and exceptional-family diagnostics.
    for q in [3,5,7,9,11,27,81,101]:
        F = GF(q, 'v')
        f = next(monic_irreducibles(F,3))
        W = next(eligible_quadratics(F,f))
        symbolic.append(universal_discriminant_audit(F,f,W))
        if q in [27,81]:
            large.append(audit_case(F,f,W,statistics=True))
        print('discriminant specializations checked at q=%d' % q, flush=True)
    for q in [101,251,503,1009]:
        F = GF(q)
        R = PolynomialRing(F,'X')
        X = R.gen()
        f = next(X**3+a*X+b for a in F for b in F
                 if (X**3+a*X+b).is_irreducible())
        W = next(eligible_quadratics(F,f))
        large.append(audit_case(F,f,W,statistics=True))
        print('incidence and discriminant statistics checked at q=%d' % q, flush=True)
    after = hashes()
    assert before == after
    out = {'status': 'all exact assertions passed',
           'scope': 'algebraic and finite incidence audits, not an extrapolated proof',
           'protected_file_hashes': before,
           'small_field_case_count': len(small),
           'direct_repeated_triples_checked': sum(r.get('direct_repeated_triples_checked',0) for r in small),
           'all_parameter_subsets_checked': sum(r.get('all_parameter_subsets_checked',0) for r in small),
           'quartic_cover_inequalities_checked': sum(r.get('quartic_free_subsets_cover_inequality_verified',0) for r in small),
           'split_quartic_identities_checked': sum(r['split_distinct_quartics'] for r in small+large),
           'discriminant_specialization_audits': symbolic,
           'small_field_cases': small,
           'incidence_statistics': large,
           'elapsed_seconds': time.time()-started}
    (ROOT/'quadratic_switching_density_results.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in
                      ('small_field_cases','incidence_statistics','discriminant_specialization_audits')},indent=2))


if __name__ == '__main__':
    main()
