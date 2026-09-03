"""Exact algebra/winding checks for IntegerSwitchingStability.md.
Run: sage -python Submission/integer_switching_stability_audit.py
No SAT, integer-subset optimization, or finite-to-asymptotic inference.
"""
import os
os.environ['OPENBLAS_NUM_THREADS'] = '1'
import hashlib
import itertools
import json
import time
from math import factorial
from collections import Counter
from pathlib import Path
from sage.all import GF, PolynomialRing, QQ, prod, gcd

ROOT = Path(__file__).resolve().parent
PROTECTED = ('Spec.lean', 'Reductions.lean', 'SignedSums.lean')


def hashes():
    return {p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in PROTECTED}


def irreducibles(F, degree):
    R = PolynomialRing(F, 'X'); X = R.gen()
    for cs in itertools.product(list(F), repeat=degree):
        f = X**degree + sum((cs[i]*X**i for i in range(degree)), R.zero())
        if f.is_irreducible():
            yield f


def multipliers(F, f):
    R = f.parent(); X = R.gen()
    for cs in itertools.product(list(F), repeat=3):
        W = sum((cs[i]*X**i for i in range(3)), R.zero())
        c = f.resultant(W)
        if c and not c.is_square():
            yield W


def universal_identities():
    B = PolynomialRing(QQ, ['c0','c1','c2','l','mu','nu','t','a'])
    c0,c1,c2,l,mu,nu,t,a = B.gens()
    R = PolynomialRing(B, 'X'); X = R.gen()
    f = X**3+c2*X**2+c1*X+c0
    W = l*X**2+mu*X+nu
    At, rem = (f(t)*W-W(t)*f).quo_rem(X-t); assert rem == 0
    Ct, rem = (f(t)*W*(X-a)**2-W(t)*f*(t-a)**2).quo_rem(X-t)
    assert rem == 0
    Ct += (1-l)*f(t)*f
    Dt = W(t)*W+(l-1)*At
    assert Ct.degree() == 3 and Ct[3] == f(t)
    # Read the quadratic in a without a huge multivariate resultant.
    coeffs = []
    for i in range(3):
        coeffs.append(sum((R(c.derivative(a, i)(a=0))/factorial(i)*X**j
                           for j,c in enumerate(Ct.list())), R.zero()))
    assert coeffs[1] == -2*(t*At+f(t)*W)
    assert coeffs[2] == At
    assert coeffs[1]**2-4*coeffs[2]*coeffs[0] == 4*f(t)*f*Dt
    g = X**2+(c2+a)*X+c1+c2*a+a*a
    Q = W-(l-1)*g
    expected = ((l-1)*(l+3)*a*a + 2*(l-1)*((l+1)*c2-mu)*a
                +(mu-(l-1)*c2)**2-4*nu+4*(l-1)*c1)
    assert Q.discriminant() == expected
    Dspecial = R([c(l=-3,mu=-2*c2,nu=c2*c2-4*c1) for c in Dt.list()])
    assert Dspecial.discriminant() == -16*f(t)*(-9*c0+4*c1*c2-c2**3+(3*c1-c2**2)*t)
    return {'disc_a_identity': True, 'exceptional_multiplier_identity': True,
            'cubic_leading_coefficient': True}


def generic_family(F, f, W, deep=False):
    B = PolynomialRing(F, ['t','a']); t,a = B.gens()
    R = PolynomialRing(B, 'X'); X = R.gen()
    ff = R(f.list()); ww = R(W.list()); l = W[2]
    At, rem = (ff(t)*ww-ww(t)*ff).quo_rem(X-t); assert rem == 0
    Dt = ww(t)*ww+(l-1)*At
    discD = Dt.discriminant()
    assert discD != 0 and discD.degree(t) <= 4
    Ct, rem = (ff(t)*ww*(X-a)**2-ww(t)*ff*(t-a)**2).quo_rem(X-t)
    assert rem == 0
    Ct += (1-l)*ff(t)*ff
    assert Ct[3] == ff(t)
    # Exact check over the rational function field, for every audited W.
    C0 = R([c(a=0) for c in Ct.list()])
    C1 = R([c.derivative(a)(a=0) for c in Ct.list()])
    C2 = R([c.derivative(a,2)(a=0)/F(2) for c in Ct.list()])
    assert C1*C1-4*C0*C2 == 4*ff(t)*ff*Dt
    result = {'q':int(F.cardinality()), 'f':str(f), 'W':str(W),
              'disc_D_degree':int(discD.degree(t))}
    if not deep:
        return result
    Delta = Ct.discriminant()
    assert Delta.degree(t) <= 12 and Delta.degree(a) <= 8
    fac = list(Delta.factor())
    # A moving odd factor over F_q is necessary, though not by itself
    # a replacement for the geometric-factor proof in the note.
    assert any(e % 2 and z.degree(t)>0 and z.degree(a)>0 for z,e in fac)
    result['Delta_factor_bidegrees'] = [[int(z.degree(t)),int(z.degree(a)),int(e)] for z,e in fac]
    # All three roots of f lie in this extension, including non-prime F.
    L = F.extension(3, 'z')
    Q = PolynomialRing(L, 'a'); aa = Q.gen()
    RX = PolynomialRing(L, 'X'); xx = RX.gen()
    fl, wl = RX(f.list()), RX(W.list())
    for beta,_ in fl.roots():
        gb = fl.quo_rem(xx-beta)[0]
        spec_t = sum((L(c)*beta**ti*aa**ai for (ti,ai),c in Delta.dict().items()), Q.zero())
        assert spec_t == wl(beta)**4*gb.discriminant()*(aa-beta)**8
        spec_a = sum((L(c)*aa**ti*beta**ai for (ti,ai),c in Delta.dict().items()), Q.zero())
        assert spec_a != 0
    result['root_of_f_specializations'] = True
    return result


def choose_polynomials(q, all_f=False):
    F = GF(q, 's')
    fs = list(irreducibles(F,3)) if all_f else [next(irreducibles(F,3))]
    return F,fs


def small_algebra_and_fibers():
    counts = Counter(); deep_reports = []
    for q, all_f in [(3,True),(5,True),(7,False),(9,False),(11,False)]:
        F,fs = choose_polynomials(q,all_f)
        for fi,f in enumerate(fs):
            R=f.parent(); X=R.gen()
            signs = {a: 1 if (-f(a)).is_square() else -1 for a in F}
            ws = list(multipliers(F,f))
            assert len(ws) == (q**3-1)//2
            for wi,W in enumerate(ws):
                typ = ('constant' if W.degree()==0 else 'linear' if W.degree()==1
                       else 'monic_quadratic' if W[2]==1 else 'nonmonic_quadratic')
                counts['multipliers_'+typ] += 1
                # The universal generic identities are exhaustively audited
                # for the smallest fields, and for all W in the specified f
                # in the other fields.
                deep = fi == 0 and (wi < 3 or wi == len(ws)-1 or (typ=='nonmonic_quadratic' and wi % 43 == 0))
                r = generic_family(F,f,W,deep)
                if deep: deep_reports.append(r)
                counts['generic_families'] += 1
                l=W[2]
                # Scanning polynomial roots verifies the pencil, not B3
                # independence numbers or any claimed asymptotic density.
                for a in F:
                    for k in F:
                        P = W*(X-a)**2+((1-l)*X+k)*f
                        assert P.degree()==4 and P.is_monic()
                        roots = [t for t in F if P(t)==0]
                        if len(roots)!=4 or a in roots:
                            continue
                        assert prod(signs[t] for t in roots)==-1
                        counts['split_distinct_fibers'] += 1
                        if sum(signs[t] for t in roots)!=2*signs[a]:
                            continue
                        counts['good_fibers'] += 1
                        assert prod((X-t for t in roots),R.one()) == P
                        for t in roots:
                            kval = -W(t)*(t-a)**2/f(t)-(1-l)*t
                            assert kval==k
                            C = (P.quo_rem(X-t))[0]
                            assert C.degree()==3
                            counts['good_incidences'] += 1
                counts['field_multiplier_cases'] += 1
    return dict(counts), deep_reports


def characteristic_three_corner():
    reports=[]
    for q in [3,9,27,81]:
        F=GF(q,'s'); R=PolynomialRing(F,'X'); X=R.gen()
        count=0
        for c1 in F:
            image={x**3+c1*x for x in F}
            for c0 in F:
                if -c0 in image:
                    continue
                f=X**3+c1*X+c0
                assert f.is_irreducible()
                assert c1 and (-c1).is_square()
                assert f.resultant(R(-c1)).is_square()
                count+=1
        assert count==q*(q-1)//3
        reports.append({'q':q,'irreducible_depressed_cubics':count,
                        'degenerate_multiplier_forced_square':True})
    return reports


def winding_audit():
    report=[]; totals=Counter(); cyclic_not_integer=[]; local_absence_examples=[]
    for q in [5,7,9,11,17,31]:
        F,fs=choose_polynomials(q)
        f=fs[0]; R=f.parent(); X=R.gen()
        K=F.extension(3,'z'); RK=PolynomialRing(K,'Y')
        th=RK(f.list()).roots()[0][0]; M=q**3-1; m=M//2
        coords={K(c0)+K(c1)*th+K(c2)*th**2:(c0,c1,c2)
                for c0,c1,c2 in itertools.product(list(F),repeat=3)}
        assert len(coords)==q**3
        base=K.multiplicative_generator()
        # Several genuinely different generators, including inversion.
        exponents=[]
        for e in [1,5,7,11,M-1]:
            if gcd(e,M)==1 and e%M not in exponents:
                exponents.append(e%M)
        for e in exponents[:3]:
            g=base**e; tab={}; v=K.one()
            for b in range(M):
                tab[v]=b; v*=g
            assert len(tab)==M
            bs={t:tab[th-K(t)] for t in F}
            E={t:1 if bs[t]%2==0 else -1 for t in F}
            for T in sorted(set([0,1,m//4,-m//3,m])):
                w=g**(2*T-1); W=R(list(coords[w]))
                assert not f.resultant(W).is_square()
                actual={t:(bs[t]//2 if E[t]==1 else (M-1-bs[t])//2+T) for t in F}
                cyclic={t:actual[t]%m for t in F}
                for t in F:
                    u=th-K(t) if E[t]==1 else w/(th-K(t))
                    assert (g*g)**actual[t]==u
                hist=Counter(); local=0
                for a in F:
                    for k in F:
                        P=W*(X-a)**2+((1-W[2])*X+k)*f
                        roots=[t for t in F if P(t)==0]
                        if len(roots)!=4 or a in roots or sum(E[t] for t in roots)!=2*E[a]:
                            continue
                        majority=[t for t in roots if E[t]==E[a]]
                        minority=[t for t in roots if E[t]!=E[a]]
                        assert len(majority)==3 and len(minority)==1
                        b=minority[0]
                        diff=sum(actual[t] for t in majority)-2*actual[a]-actual[b]
                        assert diff%m==0
                        hist[int(diff//m)]+=1
                        # A nonzero winding is NOT an integer collision.
                        # Save actual B3 examples on these five parameters,
                        # verifying every repeated triple directly.
                        vals0=sorted(set(actual[t] for t in [a]+roots))
                        if diff and len(vals0)==5 and T==0 and len(cyclic_not_integer)<8:
                            sums0=[sum(xs) for xs in itertools.combinations_with_replacement(vals0,3)]
                            if len(set(sums0))==len(sums0):
                                cyclic_not_integer.append({'q':q,'generator_exponent':e,'T':T,
                                    'W':str(W),'integer_set':vals0,'m':m,
                                    'left_triple':[actual[t] for t in majority],
                                    'right_triple':[actual[a],actual[a],actual[b]],
                                    'winding':int(diff//m),'repeated_triples_verified':len(sums0)})
                        cyc_diff=sum(cyclic[t] for t in majority)-2*cyclic[a]-cyclic[b]
                        assert cyc_diff%m==0 and -2<=cyc_diff//m<=2
                        # Every common short integer arc, not just the
                        # canonical interval, has zero winding.
                        vals=[actual[a]]+[actual[t] for t in roots]
                        if 3*(max(vals)-min(vals))<m:
                            assert diff==0
                            local+=1
                        # Check all cuts for short circle arcs and lift all
                        # five parameters to that same arc.
                        for cut in set(cyclic[t] for t in [a]+roots):
                            lifted={t:cut+(cyclic[t]-cut)%m for t in [a]+roots}
                            vals2=list(lifted.values())
                            if 3*(max(vals2)-min(vals2))<m:
                                assert sum(lifted[t] for t in majority)==2*lifted[a]+lifted[b]
                                totals['short_circle_arc_checks']+=1
                                # Moving a globally selected root to another
                                # period makes it LOCALLY absent, not deleted.
                                # Verify this distinction on an actual B3 set.
                                if len(local_absence_examples)<3 and len(set(vals2))==5:
                                    for moved in roots:
                                        moved_lifts=dict(lifted)
                                        moved_lifts[moved]+=m
                                        av=sorted(moved_lifts.values())
                                        tsums=[sum(xs) for xs in itertools.combinations_with_replacement(av,3)]
                                        if len(set(tsums))!=len(tsums):
                                            continue
                                        local_lo=min(vals2); local_hi=max(vals2)
                                        locally_present={t for t in [a]+roots
                                                         if local_lo<=moved_lifts[t]<=local_hi}
                                        local_absent=set([a]+roots)-locally_present
                                        assert a in locally_present
                                        assert local_absent=={moved}
                                        assert all((moved_lifts[t]-lifted[t])%m==0 for t in [a]+roots)
                                        assert sum(t not in locally_present for t in roots)==1
                                        local_absence_examples.append({'q':q,'m':m,'T':T,
                                            'all_five_parameters_globally_selected':True,
                                            'before_moving':sorted(vals2),'after_moving':av,
                                            'moved_from':lifted[moved],'moved_to':moved_lifts[moved],
                                            'local_interval':[local_lo,local_hi],
                                            'locally_absent_root_count':1,
                                            'repeated_triples_verified':len(tsums)})
                                        break
                        totals['winding_identities']+=1
                totals['models']+=1; totals['short_raw_window_checks']+=local
                report.append({'q':q,'generator_exponent':e,'T':T,'W':str(W),
                               'windings':dict(sorted(hist.items())), 'short_window_fibers':local})
    return dict(totals),report,cyclic_not_integer,local_absence_examples


def real_analysis_checks():
    R=PolynomialRing(QQ,'s'); s=R.gen()
    h0=s*s/2
    h1=(-2*s*s+6*s-3)/2
    # Distribution of 2*x+y for x,y uniform on [0,1].
    kappa=2*((s/2*h0).integral()(1)-(s/2*h0).integral()(0))
    kappa+=((h1/2).integral()(2)-(h1/2).integral()(1))
    assert kappa==QQ(11)/24
    B=PolynomialRing(QQ,['cp','cm','a']); cp,cm,a=B.gens()
    lhs=3*(cp*cp+cm*cm)+2*cp*cm
    assert 2*lhs == 4*(cp+cm)**2+2*(cp-cm)**2
    # The middle ratio is increasing on [1,2].
    num=(a+2)**3
    assert a*num.derivative(a)-num == 2*(a-1)*(a+2)**2
    assert QQ(3)**3/32==QQ(27)/32
    assert QQ(4)**3/(32*2)==1
    # Exact finite-mesh version of the periodic-capacity optimization.
    # Each residue has at most one unit of total density across its lifts;
    # a residue with only one position has capacity at most 3/4 there.
    checks=0
    for L in [1,2,7,60,120]:
        for K in range(2*L+1):
            alpha=QQ(K)/L
            one=min(K,2*L-K)
            two=max(0,K-L)
            capacity=(QQ(3)/4*one+two)/L
            envelope=QQ(3)/4*alpha if K<=L else QQ(1)/2+alpha/4
            assert capacity==envelope
            if alpha:
                assert 2*envelope**3/alpha<=1
            checks+=1
    return {'short_arc_kernel_integral':str(kappa),
            'pointwise_imbalance_identity':True,
            'span_envelope_endpoints':['27/32','1'],
            'periodic_capacity_mesh_checks':checks,
            'middle_ratio_monotone':True}


def main():
    start=time.time(); before=hashes()
    print('Universal identities...',flush=True)
    universal=universal_identities()
    print('Finite-field algebra and fibers...',flush=True)
    counts,deep=small_algebra_and_fibers()
    print('Integer winding checks...',flush=True)
    wcounts,windings,integer_examples,local_absence=winding_audit()
    char3=characteristic_three_corner()
    real=real_analysis_checks()
    after=hashes(); assert before==after
    out={'scope':'Exact algebra and winding checks; analytic uniform theorem proved in the note, not inferred from this audit.',
         'universal':universal,'finite_field_counts':counts,'deep_discriminant_checks':deep,
         'winding_counts':wcounts,'winding_cases':windings,
         'integer_B3_but_not_cyclic_examples':integer_examples,
         'globally_selected_but_locally_absent_examples':local_absence,
         'characteristic_three_corner':char3,'real_kernel_checks':real,
         'protected_hashes':after,'protected_unchanged':True,'seconds':round(time.time()-start,3)}
    path=ROOT/'integer_switching_stability_results.json'
    path.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'finite_field_counts':counts,'winding_counts':wcounts,
                      'deep_cases':len(deep),'protected_unchanged':True,
                      'seconds':out['seconds']},indent=2),flush=True)

if __name__=='__main__': main()
