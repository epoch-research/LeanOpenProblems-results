# Targeted exact audit for WildArtinSchreierB3.md.
# Run from the repository root:
#     sage Submission/wild_artin_schreier_b3_audit.sage
# No random search. All triple multisets are checked in the stated fixed cases.
from itertools import combinations_with_replacement
from collections import Counter
from pathlib import Path
import json
import time


def quintic_resultant(b2, b1, b0, c, d):
    """Res(t^3+b2*t^2+b1*t+b0, t^5+c*t+d), in characteristic 5."""
    a = -b2^3 + 2*b2*b1 - b0
    b = -b2^2*b1 + b1^2 + b2*b0 + c
    e = (b1-b2^2)*b0 + d
    return matrix([
        [e, -a*b0, a*b2*b0-b*b0],
        [b, e-a*b1, a*(b2*b1-b0)-b*b1],
        [a, b-a*b2, e-b*b2+a*(b2^2-b1)],
    ]).det()


def symbolic_audit():
    A = PolynomialRing(GF(5), names=('b2','b1','b0','c','d'))
    b2,b1,b0,c,d = A.gens()
    T = PolynomialRing(A, 't'); t = T.gen()
    exact = (t^3+b2*t^2+b1*t+b0).resultant(t^5+c*t+d)
    formula = quintic_resultant(b2,b1,b0,c,d)
    assert exact == formula
    depressed = (-b0^5 + c*b1*b0^3 + 2*c*d*b0^2
                 -c*(b1^2+c)^2*b0 + d*b1*(b1^2+c)^2 + d^3)
    assert exact.subs({b2:0}) == depressed
    # Cubic translation t=x+3*b2.
    aa = b1-2*b2^2
    bb = b0-2*b2*b1+b2^3
    dd = d+3*b2^5+3*c*b2
    translated = (-bb^5+c*aa*bb^3+2*c*dd*bb^2
                  -c*(aa^2+c)^2*bb+dd*aa*(aa^2+c)^2+dd^3)
    assert exact == translated
    # Every monomial has total degree <=5 in the cubic coefficients.
    degree_in_cubic_coefficients = max(sum(e[:3]) for e in exact.exponents())
    assert degree_in_cubic_coefficients == 5
    # Check the universal critical-point quartic for f=t^3-t.
    B = PolynomialRing(GF(5), names=('x','u2','u1','u0'))
    x,u2,u1,u0 = B.gens()
    f = x^3-x; u = u2*x^2+u1*x+u0
    W = f.derivative(x)*u-f*u.derivative(x)
    assert W == u2*x^4+2*u1*x^3+(u2+3*u0)*x^2-u0
    # Independent coordinate verification: the critical-line map has no conic relation.
    P = PolynomialRing(GF(5),'x'); x = P.gen()
    v = [x^4+x^2, 2*x^3, 3*x^2-1]
    quadratics = [v[i]*v[j] for i in range(3) for j in range(i,3)]
    assert matrix(GF(5), [[p[k] for k in range(9)] for p in quadratics]).rank() == 6
    # A genuine two-direction symbolic pencil, not a single finite specialization.
    G = PolynomialRing(GF(5), names=('u','v')); u,v = G.gens()
    E = G.fraction_field()
    L = PolynomialRing(E,'z'); z = L.gen()
    C = PolynomialRing(L,'t'); t = C.gen()
    pp = t^3+t+1+z*(t^2+u*t+v)
    generic_r = pp.resultant(t^5-t-1)
    generic_delta = pp.discriminant().monic()
    assert generic_r.degree() == 5 and generic_r.derivative().degree() == 3
    assert generic_delta.degree() == 4 and generic_delta.is_irreducible()
    rr = generic_r % generic_delta
    rank_r = matrix(E,[[(rr^j % generic_delta)[i] for i in range(4)] for j in range(4)]).rank()
    rank_r2 = matrix(E,[[(rr^(2*j) % generic_delta)[i] for i in range(4)] for j in range(4)]).rank()
    assert rank_r == rank_r2 == 4
    return {
        'determinant_matches_resultant': True,
        'depressed_cubic_formula_verified': True,
        'translated_formula_verified': True,
        'degree_in_cubic_coefficients': int(degree_in_cubic_coefficients),
        'critical_quartic_verified': True,
        'critical_line_map_quadratic_relations': 0,
        'expanded_resultant': str(exact),
        'generic_two_direction_example': {
            'P': str(pp), 'R': str(generic_r),
            'discriminant_monic': str(generic_delta),
            'resultant_degree': int(generic_r.degree()),
            'derivative_degree': int(generic_r.derivative().degree()),
            'discriminant_irreducible_over_F5_u_v': True,
            'rank_1_R_R2_R3': int(rank_r),
            'rank_1_R2_R4_R6': int(rank_r2),
        },
    }


def field_code(a):
    try:
        return int(a.integer_representation())
    except AttributeError:
        return int(a)


def field_context(q):
    Q = GF(q, name='b')
    T = PolynomialRing(Q,'t'); t = T.gen()
    f = t^3+t+(Q(1) if q == 5 else Q.gen()+1)
    assert f.is_irreducible()
    K = GF(q^3, name='w')
    emb = Hom(Q,K).list()[0]
    roots = f.map_coefficients(emb).roots()
    assert len(roots) == 3 and all(e == 1 for _,e in roots)
    alpha = roots[0][0]
    theta = -alpha
    M = (q^3-1)//2
    g = K.multiplicative_generator()^2
    assert g.multiplicative_order() == M
    es = sorted(list(Q), key=field_code)
    code = {a:i for i,a in enumerate(es)}
    assert code[Q(0)] == 0 and code[Q(1)] == 1
    add = [[code[a+b] for b in es] for a in es]
    mul = [[code[a*b] for b in es] for a in es]
    neg = [code[-a] for a in es]
    inv = [0]+[code[a^(-1)] for a in es[1:]]
    return Q,T,t,f,K,emb,theta,M,g,es,code,add,mul,neg,inv


def case_audit(ctx, name, numerator, denominator):
    started = time.time()
    Q,T,t,f,K,emb,theta,M,g,es,code,add,mul,neg,inv = ctx
    q = int(Q.cardinality()); M = int(M)
    params = [a for a in es if numerator(a) != 0 and denominator(a) != 0]
    vals = [numerator(a)/denominator(a) for a in params]
    phi = [(theta+emb(a))/(theta^q+emb(a))*emb(v)^2 for a,v in zip(params,vals)]
    assert len(set(phi)) == len(params)
    assert all(z^M == 1 for z in phi)
    H = q^2+q+1
    assert all(z^H == emb(v^6) for z,v in zip(phi,vals))
    logs = [int(discrete_log(z,g,ord=Integer(M),operation='*')) for z in phi]
    assert all(g^a == z for a,z in zip(logs,phi))
    pcs = [code[a] for a in params]
    vcs = [code[v] for v in vals]
    nf0,nf1,nf2 = (neg[code[f[i]]] for i in range(3))
    by_log = {}
    by_key = {}
    counts = Counter()
    squarefree_counts = Counter()
    first_squarefree = {}
    repeated_witness = None
    any_witness = None
    six_witness = None
    samples = []
    total = repeated = 0
    for tri in combinations_with_replacement(range(len(params)),3):
        i,j,k = tri
        x,y,z = pcs[i],pcs[j],pcs[k]
        xy = mul[x][y]; xpy = add[x][y]
        p2 = neg[add[xpy][z]]
        p1 = add[xy][mul[xpy][z]]
        p0 = neg[mul[xy][z]]
        us = [add[p0][nf0],add[p1][nf1],add[p2][nf2]]
        lead = next(a for a in us if a != 0)
        uu = [mul[a][inv[lead]] for a in us]
        rv = mul[mul[vcs[i]][vcs[j]]][vcs[k]]
        square = mul[rv][rv]
        key = ((uu[0]*q+uu[1])*q+uu[2])*q+square
        logsum = (logs[i]+logs[j]+logs[k]) % M
        if logsum in by_log:
            old_key,old = by_log[logsum]
            assert old_key == key
            assert set(old).isdisjoint(tri)
            if any_witness is None:
                any_witness = (old,tri)
            if repeated_witness is None and (len(set(old)) < 3 or len(set(tri)) < 3):
                repeated_witness = (old,tri)
        else:
            by_log[logsum] = (key,tri)
        if key in by_key:
            assert by_key[key] == logsum
        else:
            by_key[key] = logsum
        counts[logsum] += 1
        if len(set(tri)) == 3:
            squarefree_counts[logsum] += 1
            if logsum in first_squarefree:
                old = first_squarefree[logsum]
                assert len(set(old+tri)) == 6
                if six_witness is None:
                    six_witness = (old,tri)
            else:
                first_squarefree[logsum] = tri
        else:
            repeated += 1
        if total < 12 or total % 20003 == 0:
            samples.append(tri)
        total += 1
    assert total == binomial(len(params)+2,3)
    assert len(by_log) == len(by_key)
    # Resultants, rather than just table arithmetic, at deterministic samples.
    for tri in samples:
        P = prod(t-params[i] for i in tri)
        rr = P.resultant(numerator)/P.resultant(denominator)
        assert rr == prod(vals[i] for i in tri)
        if denominator == 1 and numerator.degree() == 5 and numerator[5] == 1:
            if all(numerator[j] == 0 for j in (2,3,4)):
                assert rr == quintic_resultant(P[2],P[1],P[0],numerator[1],numerator[0])

    def witness(pair):
        if pair is None:
            return None
        a,b = pair
        P = prod(t-params[i] for i in a)
        Qp = prod(t-params[i] for i in b)
        u = Qp-f; v = P-f
        j = next(j for j in range(3) if u[j] != 0)
        lam = v[j]/u[j]
        assert P == f+lam*(Qp-f) and lam not in (0,1)
        rp = P.resultant(numerator)/P.resultant(denominator)
        rq = Qp.resultant(numerator)/Qp.resultant(denominator)
        assert rp^2 == rq^2
        assert prod(phi[i] for i in a) == prod(phi[i] for i in b)
        return {
            'parameters_left': [str(params[i]) for i in a],
            'parameters_right': [str(params[i]) for i in b],
            'codes_left': [field_code(params[i]) for i in a],
            'codes_right': [field_code(params[i]) for i in b],
            'P': str(P), 'Q': str(Qp), 'lambda_in_P=f+lambda*(Q-f)': str(lam),
            'R_P': str(rp), 'R_Q': str(rq),
            'scalar_sign': 1 if rp == rq else -1,
            'cyclic_logs_left': [logs[i] for i in a],
            'cyclic_logs_right': [logs[i] for i in b],
            'common_sum_mod_M': int(sum(logs[i] for i in a) % M),
            'six_distinct_parameters': len(set(a+b)) == 6,
        }

    result = {
        'name': name, 'q': q, 'base_field_modulus': str(Q.modulus()),
        'f_minimal_polynomial_of_minus_theta': str(f),
        'extension_field_modulus': str(K.modulus()), 'theta': str(theta),
        'cyclic_generator': str(g), 'M': M,
        'numerator': str(numerator), 'denominator': str(denominator),
        'allowed_parameters': len(params), 'all_triple_multisets': int(total),
        'triples_with_repetitions': int(repeated),
        'distinct_product_values': len(counts),
        'product_values_with_collisions': sum(n >= 2 for n in counts.values()),
        'product_values_with_two_squarefree_triples': sum(n >= 2 for n in squarefree_counts.values()),
        'unordered_collision_pairs': int(sum(n*(n-1)//2 for n in counts.values())),
        'maximum_triple_fiber': int(max(counts.values())),
        'fiber_histogram': {str(n):int(k) for n,k in sorted(Counter(counts.values()).items())},
        'all_multisets_projective_scalar_cyclic_equivalence_checked': True,
        'resultant_sample_checks': len(samples),
        'any_collision': witness(any_witness),
        'collision_involving_repetitions': witness(repeated_witness),
        'six_distinct_root_collision': witness(six_witness),
    }
    if q == 5:
        maximum = 0; best = None; valid = 0
        for mask in range(1 << len(params)):
            ids = [i for i in range(len(params)) if mask & (1 << i)]
            sums = [(logs[i]+logs[j]+logs[k]) % M
                    for i,j,k in combinations_with_replacement(ids,3)]
            if len(sums) == len(set(sums)):
                valid += 1
                if len(ids) > maximum:
                    maximum = len(ids); best = ids
        result['q5_all_subsets'] = {
            'strong_B3_maximum': maximum, 'valid_subsets': valid,
            'maximizer_parameters': [str(params[i]) for i in best],
        }
    result['seconds'] = float(round(time.time()-started,3))
    print(json.dumps({k:result[k] for k in ('name','q','allowed_parameters','all_triple_multisets',
          'product_values_with_collisions','product_values_with_two_squarefree_triples','seconds')}, default=int),flush=True)
    return result


def pencil_audit(ctx):
    Q,T,t,f,*_ = ctx
    A = PolynomialRing(Q,'L'); L = A.gen()
    B = PolynomialRing(A,'t'); tt = B.gen()
    records = []
    for u in (T(1),t,t^2,t^2+t+1):
        P = B(f)+L*B(u)
        F = tt^5-tt-1
        R = P.resultant(F)
        D = P.discriminant()
        assert R.degree() <= 5 and R.derivative().degree() <= 3
        assert R == quintic_resultant(P[2],P[1],P[0],A(-1),A(-1))
        S = PolynomialRing(Q,'s'); s = S.gen()
        C = PolynomialRing(S,'L'); LL = C.gen()
        RR = C(R); DD = C(D)
        branch = (RR-s).resultant(RR.derivative())
        doubled = DD.resultant(RR-s)
        assert branch.degree() <= 3 and doubled.degree() <= 4
        records.append({
            'q': int(Q.cardinality()), 'U': str(u), 'R': str(R),
            'R_derivative': str(R.derivative()), 'cubic_discriminant': str(D),
            'finite_branch_polynomial': str(branch),
            'doubled_root_scalar_polynomial': str(doubled),
            'specialized_branch_gcd_degree': int(branch.gcd(doubled).degree()),
            'specialized_sign_gcd_degree': int(doubled.gcd(doubled(-s)).degree()),
        })
    return records


result = {
    'status': 'Exact targeted verification of the proved obstruction, not a B3-excess construction.',
    'definition': 'Strong B3; all triple multisets, including repeated parameters.',
    'symbolic': symbolic_audit(),
    'cases': [], 'pencils': [],
}
for q in (5,125):
    ctx = field_context(q)
    Q,T,t,f,*_ = ctx
    assert Q(1).trace() != 0
    result['pencils'].extend(pencil_audit(ctx))
    result['cases'].append(case_audit(ctx,'Artin-Schreier a=1',t^5-t-1,T(1)))
    result['cases'].append(case_audit(ctx,'linearized c=1,d=1',t^5+t+1,T(1)))
    # F(t)=(1/t)^5-(1/t)-1; no finite zero, one pole of order 5.
    result['cases'].append(case_audit(ctx,'Artin-Schreier after H(t)=1/t',1-t^4-t^5,t^5))
    if q == 5:
        result['cases'].append(case_audit(ctx,'inseparable c=0,d=1',t^5+1,T(1)))
Path('Submission/wild_artin_schreier_b3_audit.json').write_text(json.dumps(result,indent=2,default=int)+'\n')
print('All assertions passed; wrote Submission/wild_artin_schreier_b3_audit.json',flush=True)
