"""Exact verification of fixed examples of the proved pair-witness theorem."""
from itertools import product, combinations
from fractions import Fraction
from pathlib import Path
import hashlib


def relation(n, kind):
    R = [[False]*n for _ in range(n)]
    if kind == 'matching':
        for a in range(n):
            R[a][a ^ 1] = True
    elif kind == 'loops':
        for a in range(n):
            R[a][a] = True
    elif kind == 'two_cycles':
        for cycle in (list(range(5)), list(range(5,n))):
            for a,b in zip(cycle,cycle[1:]+cycle[:1]):
                R[a][b]=R[b][a]=True
    else:
        raise ValueError(kind)
    return R


def check(n, d, kind):
    R = relation(n,kind)
    counts = [0]*n
    pairs = list(combinations(range(d),2))
    for x in product(range(n), repeat=d):
        if any(R[x[i]][x[j]] for i,j in pairs):
            counts[x[0]] += 1
    assert len(set(counts)) == 1, 'not exactly balanced'
    p = Fraction(sum(counts), n**d)
    assert p <= Fraction(1,4)
    delta = max(map(sum,R))
    assert Fraction(delta,n) <= 24*p/(7*d*(d-1))
    even = [x for x in range(1<<d) if x.bit_count()%2 == 0]
    m=len(even)
    assert n>=m
    F = [set() for _ in range(n)]
    for i,j in combinations(range(m),2):
        if (even[i]^even[j]).bit_count()==2:
            F[i].add(j); F[j].add(i)
    bad = [set(j for j in range(n) if j!=i and R[i][j]) for i in range(n)]
    f=list(range(n))
    def conflicts():
        return [(i,j) for i in range(n) for j in F[i] if i<j and f[j] in bad[f[i]]]
    steps=0
    while (cs:=conflicts()):
        u,v=cs[0]
        inv={a:i for i,a in enumerate(f)}
        A={inv[a] for w in F[u] for a in bad[f[w]]}
        S={inv[a] for a in bad[f[u]]}
        T={z for w in S for z in F[w]}
        z=next(z for z in range(n) if z not in A|T|{v})
        before=set(cs)
        f[u],f[z]=f[z],f[u]
        after=set(conflicts())
        assert after < before, 'switch created a conflict or failed to remove one'
        steps += 1
    assert len(set(f[:m]))==m
    ind={x:i for i,x in enumerate(even)}
    for y in range(1<<d):
        if y.bit_count()%2:
            image=[f[ind[y^(1<<j)]] for j in range(d)]
            assert all(not R[a][b] for a,b in combinations(image,2))
    print(f'PASS: {kind}, N={n}, d={d}, p={p}, exact balance/degree bound; avoiding injection after {steps} valid switches.')


if __name__=='__main__':
    for args in [(8,2,'matching'),(16,3,'matching'),(32,4,'matching'),(32,3,'two_cycles'),(32,4,'loops')]:
        check(*args)
    sha=hashlib.sha256(Path(__file__).with_name('Spec.lean').read_bytes()).hexdigest()
    assert sha=='9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b'
    print('Spec.lean unchanged:',sha)
    print('This audits fixed examples of a paper theorem, not the general balanced claim or Erdős181.')
