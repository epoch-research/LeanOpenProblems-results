"""Run with: sage -python Submission/quadratic_switching_audit.py.

Exact finite-field checks of the propositions in CharacterSwitching.md.
The mathematical proof allows all odd prime powers. This audit uses primes
so that coefficients and displayed parameter indices have no embedding ambiguity.
No finite output here is an asymptotic counterexample.
"""
import json
import itertools
from pathlib import Path
from sage.all import GF, PolynomialRing

ROOT = Path(__file__).resolve().parent

def audit(q):
    F = GF(q)
    assert F.is_prime_field() and q % 2
    K = GF(q**3, 'z')
    theta = K.multiplicative_generator()
    R = PolynomialRing(F, 'X')
    X = R.gen()
    f = R(theta.minpoly())
    M, m = q**3 - 1, (q**3 - 1)//2
    def chi(x):
        assert x != 0
        v = x**m
        assert v in (K(1), K(-1))
        return 1 if v == 1 else -1
    z = [theta - K(t) for t in range(q)]
    negative = [int(chi(v) == -1) for v in z]
    sigma = sum(chi(v) for v in z)
    quadratics = [X*X + a*X + b for a in F for b in F]
    eligible = [W for W in quadratics
                if W.is_irreducible() and chi(W(theta)) == -1]
    assert sum(chi(W(theta)) for W in quadratics) == q
    assert len(eligible) == (q*q - 2*q + sigma*sigma)//4
    W = eligible[0]
    w = W(theta)
    values = [v if not r else w/v for v, r in zip(z, negative)]
    assert len(set(values)) == q
    assert all(chi(v) == 1 for v in values)
    logs = []
    for v in values:
        e = int(v.log(theta))
        assert e % 2 == 0 and 0 <= e < M
        logs.append(e//2)
    assert all(theta**(2*e) == v for e, v in zip(logs, values))
    pair_sums = [(logs[i] + logs[j]) % m
                 for i,j in itertools.combinations_with_replacement(range(q), 2)]
    assert len(pair_sums) == len(set(pair_sums))
    buckets = {}
    collision_pairs = 0
    first = repeated = None
    for I in itertools.combinations_with_replacement(range(q), 3):
        s = sum(logs[i] for i in I) % m
        for J in buckets.get(s, []):
            assert sum(negative[i] for i in I) != sum(negative[j] for j in J)
            collision_pairs += 1
            if first is None:
                first = (I,J)
            if repeated is None and (len(set(I)) < 3 or len(set(J)) < 3):
                repeated = (I,J)
        buckets.setdefault(s, []).append(I)
    report = {'q':q, 'f':str(f), 'W':str(W), 'modulus':m,
              'sigma':sigma, 'eligible_W':len(eligible), 'B2_verified':True,
              'triple_collision_pairs':collision_pairs}
    if first is not None:
        I,J = repeated or first
        ri, rj = sum(negative[i] for i in I), sum(negative[j] for j in J)
        if ri > rj:
            I,J,ri,rj = J,I,rj,ri
        d = rj-ri
        P, Q = R.one(), R.one()
        for t in I:
            if negative[t]:
                Q *= X-t
            else:
                P *= X-t
        for t in J:
            if negative[t]:
                P *= X-t
            else:
                Q *= X-t
        T, remainder = (P-W**d*Q).quo_rem(f)
        assert remainder == 0 and T != 0 and T.degree() <= d-1
        assert P.degree() == 3+d and Q.degree() == 3-d
        assert P-W**d*Q == f*T
        report['certificate'] = {'I':I, 'J':J, 'negative_counts':[ri,rj],
            'd':d, 'P':str(P), 'Q':str(Q), 'R':str(T),
            'integer_sums':[sum(logs[i] for i in I),sum(logs[j] for j in J)]}
    if q <= 19:
        report['exponents_by_parameter'] = logs
        report['negative_by_parameter'] = negative
    return report

if __name__ == '__main__':
    reports = [audit(q) for q in [3,5,7,11,19,31,61,101]]
    text = json.dumps(reports, indent=2)
    (ROOT/'quadratic_switching_results.json').write_text(text+'\n')
    for r in reports:
        print('q=%d, W=%s, eligible=%d, B2=true, triple collision pairs=%d'
              % (r['q'],r['W'],r['eligible_W'],r['triple_collision_pairs']))
