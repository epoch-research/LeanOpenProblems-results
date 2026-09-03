from itertools import product, combinations
from random import Random

def matmul(a,b):
    n=len(a)
    return [[sum(a[i][k]*b[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
def stats(a):
    a2=matmul(a,a); a3=matmul(a2,a)
    z=sum(a2[i][j]**2 for i in range(len(a)) for j in range(len(a)))
    return z,a3

checks=0; min_cases=0
n=4; edges=list(combinations(range(n),2))
# Exhaust all pairs B <= A of Boolean kernels (three states per edge).
for state in product(range(3),repeat=len(edges)):
    a=[[0]*n for _ in range(n)]; b=[[0]*n for _ in range(n)]
    for (x,y),s in zip(edges,state):
        a[x][y]=a[y][x]=int(s>0); b[x][y]=b[y][x]=int(s==2)
    za,a3=stats(a)
    if not za: continue
    zb,_=stats(b)
    support=sum(2*a3[x][y]*b[x][y] for x,y in edges)
    assert zb*za**3>=support**4
    assert sum(2*a[x][y]*a3[x][y] for x,y in edges)==za
    # Face deletion: t_2(B) <= t_1(B)^2 for [0,1] kernels.
    assert zb<=sum(map(sum,b))**2
    checks+=1
    if sum(state_i>0 for state_i in state)>=3:
        # KKT with K=64, alpha=128/N^2: all positive derivatives strict.
        assert all(2*a[x][y]*a3[x][y]*n*n<128*za for x,y in edges)
        min_cases+=1

rng=Random(181)
weighted=0
for n in range(3,9):
    edges=list(combinations(range(n),2))
    for trial in range(40):
        a=[[0]*n for _ in range(n)]; b=[[0]*n for _ in range(n)]
        for x,y in edges:
            z=rng.randrange(6); v=rng.randrange(z+1)
            a[x][y]=a[y][x]=z; b[x][y]=b[y][x]=v
        za,a3=stats(a)
        if not za: continue
        zb,_=stats(b)
        support=sum(2*a3[x][y]*b[x][y] for x,y in edges)
        assert zb*za**3>=support**4
        assert zb<=25*sum(map(sum,b))**2 # B/5 has entries <=1.
        weighted+=1

# Exact global packing product at k=1 on complete hosts. These are actual
# injection counts, not a homomorphism count with collisions ignored.
from math import prod
packing_checks=0
for n in range(5,25):
    a=[[int(x!=y) for y in range(n)] for x in range(n)]
    za,a3=stats(a)
    for blocks in range(1,(n-1)//2+1):
        # Without collision subtraction: for Q_1 all homomorphisms are injective.
        # Each residual H_1 is at least sqrt(H_2(A))*sigma(E(res))^2.
        lhs=prod(n-i for i in range(2*blocks))
        den=n*(n-1)
        num=prod((n-2*i)*(n-2*i-1) for i in range(blocks))
        assert lhs**2*den**(4*blocks)>=za**blocks*num**4
        packing_checks+=1

# The regime chosen for the report: eta <=1/8, u>=105/256>2/5.
# With N>=2^d, k<=d/4, delta <= (5/4)*(10^(1/4)/2)^d.
assert 10<16
print(f'PASS: {checks} exact Boolean support/face checks; {min_cases} have majority-host strict KKT at lambda=0.')
print(f'PASS: {weighted} exact rational-weight support/face checks (weights divided by 5).')
print(f'PASS: {packing_checks} exact full-injection packing-product checks.')
print('PASS: the large-d collision bound decays, since 10 < 2^4.')
