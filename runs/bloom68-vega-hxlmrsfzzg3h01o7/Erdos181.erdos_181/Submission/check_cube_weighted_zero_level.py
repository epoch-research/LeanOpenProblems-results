"""Exact audits of auxiliary full-pattern potential and weighted Kneser identities.
This does not test/prove the missing dimension-uniform zero-level estimate.
"""
from collections import Counter, defaultdict
from fractions import Fraction as Q
from itertools import combinations, permutations, product
from math import comb, prod
import random
import hashlib

SPEC = '/workspace/leanproject/Submission/Spec.lean'
EXPECTED_HASH = '9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b'

def edges(d):
    return [(x, x ^ (1 << i)) for x in range(1 << d)
            for i in range(d) if not (x & (1 << i))]

def host_colour(N, kind, seed=0):
    rng = random.Random(seed)
    if kind == 'star':
        return {(u,v): int(u == 0) for u,v in combinations(range(N), 2)}
    if kind == 'cycle':
        return {(u,v): int((v-u) in (1,N-1)) for u,v in combinations(range(N), 2)}
    return {(u,v): rng.randrange(2) for u,v in combinations(range(N), 2)}

def colour(c,u,v):
    return c[(u,v) if u<v else (v,u)]

def direct_counts(d,N,c,q):
    E=edges(d)
    out=Counter()
    byset=defaultdict(Counter)
    occ=defaultdict(Counter)
    total=0
    for f in permutations(range(N),1 << d):
        sig=sum(colour(c,f[x],f[y]) << j for j,(x,y) in enumerate(E))
        wt=prod(q[v] for v in f)
        out[sig]+=wt
        byset[frozenset(f)][sig]+=1
        for v in f:
            occ[sig][v]+=wt
        total+=1
    assert sum(out.values()) == prod(range(1,(1 << d)+1))*sum(
        prod(q[v] for v in S) for S in combinations(range(N),1 << d))
    return out,byset,occ,total

def potential_audit():
    d,N=2,6
    c=host_colour(N,'star')
    q=[2]+[1]*5 # actual weights q/2
    T,byset,occ,num=direct_counts(d,N,c,q)
    M=max(T.values())
    active={s for s,t in T.items() if t==M}
    assert len(active)==5 and 0 in active and M==120
    pi={s:Q(3,4) if s==0 else Q(1,16) for s in active}
    load={v:sum(pi[s]*Q(occ[s][v],T[s]) for s in active) for v in range(N)}
    assert load=={0:Q(1,4),**{v:Q(3,4) for v in range(1,N)}}
    assert sum(load.values())==4
    assert 5*Q(3,4)<=4
    # exp(4 Phi)=M(w)^4/prod(w)^3 at kappa=3/4.
    def objective(w):
        cnt=Counter()
        for S,pats in byset.items():
            wt=prod(w[v] for v in S)
            for s,k in pats.items(): cnt[s]+=k*wt
        return max(cnt.values())**4/prod(w)**3
    wstar=[Q(1)]+[Q(1,2)]*5
    optimum=objective(wstar)
    cases=0
    for w in product([Q(1),Q(1,2),Q(1,3),Q(2,3)],repeat=N):
        assert objective(w)>=optimum
        cases+=1
    print(f'Full-pattern convex/KKT certificate: {num} injections, {cases} exact potential comparisons PASS')

def swap(x):
    a=x&1; b=(x>>1)&1
    return x^3 if a!=b else x

def fold_sig(sig,E,keep):
    Eidx={frozenset(e):i for i,e in enumerate(E)}
    def fold(x):
        a=x&1; b=(x>>1)&1
        if a!=b and a!=keep: return swap(x)
        return x
    return sum(((sig>>Eidx[frozenset((fold(x),fold(y)))])&1)<<j
               for j,(x,y) in enumerate(E))

def reflection_audit(d,N,c,q,seed):
    T,_,_,num=direct_counts(d,N,c,q)
    E=edges(d); h=1<<d; r=h//4
    F=[x for x in range(h) if (x&1)==((x>>1)&1)]
    U=[x for x in range(h) if (x&1)==1 and ((x>>1)&1)==0]
    V=[swap(x) for x in U]
    Fset=set(F); Uset=set(U); Vset=set(V)
    EB=[(j,x,y) for j,(x,y) in enumerate(E) if x in Fset and y in Fset]
    EA=[(j,x,y) for j,(x,y) in enumerate(E) if x in Uset or y in Uset]
    EC=[(j,x,y) for j,(x,y) in enumerate(E) if x in Vset or y in Vset]
    assert len(F)==2*r and len(EA)==len(EC)==(d+2)*r//2
    selected=list(range(1<<len(E))) if d==2 else sorted(set(
        [0,(1<<len(E))-1,max(T,key=T.get)]+random.Random(seed).sample(list(T),9)))
    spectral_cases=intersection_cases=0
    for sig in selected:
        lhs=2*T[sig]-T[fold_sig(sig,E,0)]-T[fold_sig(sig,E,1)]
        rhs=0
        for fvals in permutations(range(N),len(F)):
            f=dict(zip(F,fvals))
            if any(colour(c,f[x],f[y])!=((sig>>j)&1) for j,x,y in EB): continue
            X=[v for v in range(N) if v not in fvals]
            sets=list(combinations(X,r)); idx={frozenset(S):i for i,S in enumerate(sets)}
            masks=[sum(1<<v for v in S) for S in sets]
            a=[0]*len(sets); b=[0]*len(sets)
            for z in permutations(X,r):
                S=idx[frozenset(z)]; wt=prod(q[v] for v in z)
                af={**f,**dict(zip(U,z))}
                bf={**f,**dict(zip(V,z))}
                if all(colour(c,af[x],af[y])==((sig>>j)&1) for j,x,y in EA): a[S]+=wt
                if all(colour(c,bf[x],bf[y])==((sig>>j)&1) for j,x,y in EC): b[S]+=wt
            disj=[(i,j) for i in range(len(sets)) for j in range(len(sets)) if masks[i]&masks[j]==0]
            for arr,fold in [(a,fold_sig(sig,E,1)),(b,fold_sig(sig,E,0))]:
                if T[fold]==0:
                    assert all(not (arr[i] and arr[j]) for i,j in disj)
                    intersection_cases+=1
            v=[x-y for x,y in zip(a,b)]
            quad=sum(v[i]*v[j] for i,j in disj)
            rhs-=prod(q[u] for u in fvals)*quad
            # Independent exact check of the Kneser j=0,1,2 projections.
            n=len(X); L=comb(n,r); D=comb(n-r,r)
            Z=sum(v); norm=sum(z*z for z in v)
            p0=Q(Z*Z,L)
            delta=[sum(v[i] for i,S in enumerate(sets) if u in S)-Q(r*Z,n) for u in X]
            p1=Q(n*(n-1),L*r*(n-r))*sum(z*z for z in delta)
            p2=norm-p0-p1
            assert p2>=0 and (r!=1 or p2==0)
            q1=Q(r,n-r); q2=Q(r*(r-1),(n-r)*(n-r-1)) if r>=2 else 0
            assert quad==D*(p0-q1*p1+q2*p2)
            spectral_cases+=1
        assert lhs==rhs, (d,N,sig,lhs,rhs)
    print(f'Weighted full-injection reflection Q_{d}, N={N}: {num} injections, '
          f'{len(selected)} patterns, {spectral_cases} spectral/conditional checks, '
          f'{intersection_cases} zero-fold intersecting checks PASS')

def hoffman_audit():
    count=0
    for n,r in [(5,1),(7,2),(8,3),(9,3),(10,4)]:
        sets=list(combinations(range(n),r)); L=len(sets)
        masks=[sum(1<<v for v in S) for S in sets]
        q1=Q(r,n-r)
        q3=Q(r*(r-1)*(r-2),(n-r)*(n-r-1)*(n-r-2)) if r>=3 else Q(0)
        for kind in ['star','two_of_three']:
            if kind=='two_of_three' and r<2: continue
            for seed in range(5):
                rng=random.Random(seed+10*n+r)
                w=[Q(rng.randint(1,5),5) for _ in range(n)]
                a=[prod(w[v] for v in S)*rng.randint(1,4)
                   if ((0 in S) if kind=='star' else len(set(S)&{0,1,2})>=2) else Q(0)
                   for S in sets]
                assert all(not(a[i] and a[j]) for i in range(L) for j in range(L)
                           if masks[i]&masks[j]==0)
                Z=sum(a); norm=sum(v*v for v in a)
                theta=[sum(a[i] for i,S in enumerate(sets) if v in S)/Z for v in range(n)]
                delta=[sum(a[i] for i,S in enumerate(sets) if v in S)-Q(r,n)*Z for v in range(n)]
                p0=Z*Z/L
                p1=Q(n*(n-1),L*r*(n-r))*sum(v*v for v in delta)
                # Construct Pi_1 independently and check both its norm and orthogonality.
                coeff=[Q(n*(n-1),L*r*(n-r))*z for z in delta]
                proj=[sum(coeff[v] for v in S) for S in sets]
                assert sum(v*v for v in proj)==p1
                assert sum((a[i]-Z/L-proj[i])*proj[i] for i in range(L))==0
                assert (1+q3)*p0 <= (q1-q3)*p1+q3*norm
                chi=L*norm/(Z*Z)
                assert 1+q3 <= (q1-q3)*Q(n*(n-1),r*(n-r))*sum(
                    (t-Q(r,n))**2 for t in theta)+q3*chi
                count+=1
    print(f'Weighted intersecting-family first-harmonic inequality: {count} exact cases PASS')

if __name__=='__main__':
    assert hashlib.sha256(open(SPEC,'rb').read()).hexdigest()==EXPECTED_HASH
    potential_audit()
    reflection_audit(2,5,host_colour(5,'cycle'),[5,2,3,1,4],0)
    reflection_audit(2,7,host_colour(7,'random',7),[5,1,4,3,2,1,5],1)
    reflection_audit(3,9,host_colour(9,'random',11),[5,2,3,1,4,5,1,2,3],2)
    hoffman_audit()
    assert hashlib.sha256(open(SPEC,'rb').read()).hexdigest()==EXPECTED_HASH
    print('Spec.lean unchanged; no completing Ramsey theorem or zero-level spectral bound proved.')
