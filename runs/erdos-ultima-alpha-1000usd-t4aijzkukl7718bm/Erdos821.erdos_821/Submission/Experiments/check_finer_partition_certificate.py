"""Independent exact-rational check of an abstract finite partition model.
Not a theorem about primes and not a Lean proof of Erdős 821.
"""
from fractions import Fraction
from collections import Counter
from functools import lru_cache
from math import factorial, comb, prod
from pathlib import Path
import json

@lru_cache(None)
def partitions(n, cap):
    if n == 0:
        return ((),)
    return tuple((j,) + p for j in range(min(n, cap), 0, -1)
                 for p in partitions(n-j, j))

def z(p):
    return prod(j**k * factorial(k) for j,k in Counter(p).items())

def check():
    path=Path(__file__).with_name('finer_partition_cap2_certificate_24_4.json')
    d=json.loads(path.read_text())
    N=d['N']; R=d['halfLevel']; root=d['root']
    assert (N,R,root)==(24,12,4)
    data=[(tuple(p), Fraction(w)) for p,w in d['data']]
    assert len({p for p,w in data})==len(data)
    for p,w in data:
        assert all(j>0 for j in p)
        assert sum(p)==N and root*max(p)>N
        assert 0<w<=Fraction(2,z(p))
    assert sum(w for p,w in data)==1
    patterns=[p for n in range(R+1) for p in partitions(n,n)]
    patterns += [(j,) for j in range(R+1,N+1)]
    cdata=[(Counter(p),w) for p,w in data]
    for p in patterns:
        pat=Counter(p)
        m=sum(w*prod(comb(c[j],a) for j,a in pat.items())
              for c,w in cdata if all(c[j]>=a for j,a in pat.items()))
        assert m==Fraction(1,z(p)), p
    print(f'Exact check passed: {len(data)} outcomes, {len(patterns)} moment equations, density cap 2.')

if __name__=='__main__':
    check()
