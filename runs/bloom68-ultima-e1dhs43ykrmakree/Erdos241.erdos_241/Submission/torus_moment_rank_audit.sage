"""Exact structural audit, not a proof of the asymptotic conjecture."""
import itertools, json
from pathlib import Path

def add(a,b): return tuple(x+y for x,y in zip(a,b))
def neg(a): return tuple(-x for x in a)
def sub(a,b): return add(a,neg(b))
def unit(n,i): return tuple(1 if j==i else 0 for j in range(n))
def root_window(n):
    e=[unit(n,i) for i in range(n)]; zero=(0,)*n
    return sorted({zero}|{sub(x,y) for x in e for y in e})
def fisher_window(n):
    e=[unit(n,i) for i in range(n)]
    charge={add(add(e[a],e[b]),neg(e[c])) for a in range(n) for b in range(a,n) for c in range(n)}
    return sorted({sub(x,e[-1]) for x in charge})
def shift(S,q,mod=None):
    index={x:i for i,x in enumerate(S)}; entries={}
    for j,x in enumerate(S):
        y=(x+q)%mod if mod else add(x,q)
        if y in index: entries[(index[y],j)]=1
    return matrix(QQ,len(S),len(S),entries,sparse=True)
def comm(A,B): return A*B-B*A

def signature_integer_spectrum(A):
    assert A==A.transpose()
    pol=A.charpoly(); factors=pol.factor(); pos=negc=zero=0
    for f,k in factors:
        assert f.degree()==1, (f,k)
        ev=-f[0]/f[1]
        if ev>0: pos+=k
        elif ev<0: negc+=k
        else: zero+=k
    return (int(pos),int(negc),int(zero))

out={'scope':'Exact finite matrix checks; no asymptotic proof or disproof','formal':[]}
for n in range(2,7):
    e=[unit(n,i) for i in range(n)]
    roots=[sub(e[i],e[-1]) for i in range(n-1)]
    V=root_window(n); W=fisher_window(n)
    d=n*n-n+1; H=(n^3-n^2+2*n)//2; R=H-d
    assert len(V)==d and len(W)==H
    T=[shift(V,q) for q in roots]; L=[shift(W,q) for q in roots]
    rho=(3*n*n-5*n+4)//2
    for Ti,Li in zip(T,L):
        assert Ti.rank()==2*n-2
        assert comm(Ti,Ti.transpose()).rank()==4*n-6
        assert Li.rank()==rho
        assert comm(Li,Li.transpose()).rank()==3*n*n-9*n+8
    if n>=3:
        for i in range(n-1):
            for j in range(i):
                assert comm(T[i],T[j].transpose()).rank()==2*n-4
                assert comm(L[i],L[j].transpose()).rank()==(3*n*n-11*n+12)//2
    K=block_matrix(QQ,[[comm(A,B.transpose()) for B in T] for A in T])
    sig=signature_integer_spectrum(K)
    expected=(1,1) if n==2 else (R-binomial(n-1,2)+1,R)
    assert sig[:2]==tuple(map(int,expected)),(n,sig,expected)
    row={'n':int(n),'d':int(d),'H':int(H),'formal_root_shift_rank':int(2*n-2),
         'formal_fisher_shift_rank':int(rho),'root_aggregate_signature':sig}
    out['formal'].append(row)
    print(json.dumps(row))

A=[0,1,4]; M=13
triples=list(itertools.combinations_with_replacement(A,3))
sums=[sum(t)%M for t in triples]
assert len(sums)==len(set(sums))==10
S=sorted({(a+b-c)%M for a in A for b in A for c in A})
V=sorted({(a-b)%M for a in A for b in A})
assert S==[x for x in range(M) if x!=6]
T=[shift(S,q,M) for q in [1,4]]
assert all(t.rank()==11 and comm(t,t.transpose()).rank()==2 for t in T)
K=block_matrix(QQ,[[comm(t,u.transpose()) for u in T] for t in T])
assert K.rank()==5
Ep=sorted(set(S)-set(V)); Em=sorted({(-x)%M for x in S}-set(V))
assert Ep==[2,5,7,8,11] and Em==[2,5,6,8,11]
assert len(set(Ep)&set(Em))==4
out['actual_Z13']={'A':A,'M':M,'triple_sums':sorted(sums),'Fisher_frequencies':S,
                   'root_frequencies':V,'Eplus':Ep,'Eminus':Em,
                   'actual_shift_rank':11,'actual_self_commutator_rank':2,
                   'actual_aggregate_commutator_rank':int(K.rank()),'ambient_complement':1}
out['status']='PASS'
Path('Submission/torus_moment_rank_audit.json').write_text(json.dumps(out,indent=2,default=int)+'\n')
print('PASS: exact formal ranks n=2..6 and actual Z13 counterexample; no target theorem proved.')
