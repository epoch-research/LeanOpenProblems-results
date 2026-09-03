"""Exact character-dependent switches of cyclic strong B3 sets.

The input B is in Z/M with M even. For odd s, define
    T_s(b) = b (b even), s-b (b odd),
and divide each result by 2 in the index-two subgroup.
Equal-count triples are automatically unique if B is strong B3.
This script audits all triples, including repeats; it also tests straightening.
Run with sage -python Submission/character_switching.py.
"""
import sys, json, itertools, collections, math, time
from sage.all import GF, discrete_log, ZZ

def base(q, degree):
    K=GF(q**degree, 'z'); z=K.multiplicative_generator()
    M=q**degree-1 if degree==3 else (q**degree-1)//(q-1)
    B=[int((z+K(a)).log(z)) % M for a in range(q)]
    if degree==4: B.append(0) # projective point at infinity
    assert len(set(B))==len(B)
    return M,B

def collisions(A,m,labels=None,full=False):
    seen={}; bad=[]
    for I in itertools.combinations_with_replacement(range(len(A)),3):
        v=sum(A[i] for i in I)%m
        if v in seen:
            J=seen[v]
            if labels is not None:
                assert sum(labels[i] for i in I)!=sum(labels[i] for i in J)
            if not full: return I,J
            bad.append((I,J))
        else: seen[v]=I
    return bad if full else None

def switches(M,B,mode,limit=None):
    assert not M%2
    labels=[b%2 for b in B]
    assert collisions(B,M) is None
    results=[]
    for s in range(1,M,2):
        A=[((b if not r else s+(-b if mode=='reciprocal' else b))%M)//2
           for b,r in zip(B,labels)]
        # Duplicate images produce equal-count collisions in straight mode,
        # but reciprocal mode equal-count property holds even with duplicates?
        # Distinct parity preimages can collide; then counts differ, as expected.
        bad=collisions(A,M//2,labels)
        if bad is None: results.append((s,A))
        if limit and len(results)>=limit: break
    return results

if __name__=='__main__':
    qs=list(map(int,sys.argv[1:])) or [3,5,7,11,13,17,19]
    for q in qs:
      for degree in [3,4]:
        start=time.time(); M,B=base(q,degree)
        for mode in ['reciprocal','straight']:
            res=switches(M,B,mode)
            print(json.dumps({'q':q,'degree':degree,'M':M,'size':len(B),'mode':mode,
                'solutions':len(res),'first':res[:1],'seconds':round(time.time()-start,3)}),flush=True)
