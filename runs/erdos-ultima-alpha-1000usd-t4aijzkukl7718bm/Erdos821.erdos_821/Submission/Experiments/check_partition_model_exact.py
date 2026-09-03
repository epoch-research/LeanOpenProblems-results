"""Check a finite partition certificate with Python integers and fractions.
This is not a Lean proof and makes no assertion about the distribution of primes.
Usage: python3 check_partition_model_exact.py certificate.json [density_cap]
"""
from fractions import Fraction
from collections import Counter
from functools import lru_cache
from math import factorial, comb, prod, lcm
from pathlib import Path
import json, sys

@lru_cache(None)
def partitions(n, cap):
    if n == 0:
        return ((),)
    return tuple((j,) + p for j in range(min(n, cap), 0, -1)
                 for p in partitions(n-j, j))

def z(p):
    return prod(j**k * factorial(k) for j,k in Counter(p).items())

def check(path, density_cap):
    d=json.loads(Path(path).read_text())
    N=d['N']; R=d['halfLevel']; root=d['root']
    data=[(tuple(p), Fraction(w)) for p,w in d['data']]
    assert 0 <= R <= N and root >= 1
    assert len({p for p,w in data})==len(data)
    D=lcm(*(w.denominator for p,w in data))
    integer_data=[(p, w.numerator*(D//w.denominator)) for p,w in data]
    for p,W in integer_data:
        assert all(j>0 for j in p)
        assert sum(p)==N and root*max(p)>N
        assert 0<W and W*z(p)<=density_cap*D
    assert sum(W for p,W in integer_data)==D
    patterns=[p for n in range(R+1) for p in partitions(n,n)]
    patterns += [(j,) for j in range(R+1,N+1)]
    cdata=[(Counter(p),W) for p,W in integer_data]
    for pat0 in patterns:
        pat=Counter(pat0)
        moment=sum(W*prod(comb(c[j],a) for j,a in pat.items())
                   for c,W in cdata if all(c[j]>=a for j,a in pat.items()))
        assert moment*z(pat0)==D, pat0
    print(f'EXACT check passed: N={N}, level={R}, root={root}, '
          f'{len(data)} outcomes, {len(patterns)} equations, density cap={density_cap}.')
    print(f'Common denominator has {len(str(D))} decimal digits.')

if __name__=='__main__':
    check(sys.argv[1], int(sys.argv[2]) if len(sys.argv)>2 else 2)
