import sympy as sp
from itertools import combinations, product


def add(a,b): return tuple(x+y for x,y in zip(a,b))
def sub(a,b): return tuple(x-y for x,y in zip(a,b))
def scale(c,a): return tuple(c*x for x in a)
def mul(a,b,m):
    z=[0]*m
    for j,x in enumerate(a):
        for k,y in enumerate(b):
            e=j+k
            z[e % m] += x*y*(2 if e >= m else 1)
    return tuple(z)

def check(m):
    E=[tuple(int(j==k) for j in range(m)) for k in range(m)]
    O=(0,)*m
    T=E+[add(a,b) for a,b in combinations(E,2)]
    IJ=list(combinations(range(2*m),2))
    IJ=[(i,j) for i in range(2*m) for j in range(i,2*m)]
    def gram_row(v):
        return [v[i]*v[j]*(1 if i==j else 2) for i,j in IJ]
    def eq(v,w):
        return [a-b for a,b in zip(gram_row(v),gram_row(w))]
    pairs=[]
    for a,b in product(E,E):
        pairs.append((a+b,a+scale(-1,b)))
    for x in T:
        pairs.append((x+O,O+x))
        x2=mul(x,x,m)
        pairs.append((sub(x2,E[0])+scale(2,x),add(x2,E[0])+O))
    C=sp.Matrix([eq(v,w) for v,w in pairs])
    rank=C.rank()
    dim=len(IJ)-rank
    maxcoef=max(abs(c) for pair in pairs for v in pair for c in v)
    # Every trace-form Gram matrix H=diag(lambda(b_i b_j), lambda(b_i b_j))
    # must satisfy all finite constraints.
    trace_matrices=[]
    for k in range(m):
        A=sp.Matrix([[mul(a,b,m)[k] for b in E] for a in E])
        H=sp.diag(A,A)
        trace_matrices.append(sp.Matrix([H[i,j] for i,j in IJ]))
    Z=sp.Matrix.hstack(*trace_matrices)
    assert C*Z == sp.zeros(C.rows,m)
    assert Z.rank()==m
    assert dim==m, (m,dim)
    # Original real norm identities hold in the field itself, not merely numerically.
    def norm(v): return add(mul(v[:m],v[:m],m),mul(v[m:],v[m:],m))
    assert all(norm(v)==norm(w) for v,w in pairs)
    print(f'm={m}: Gram variables={len(IJ)}, rank={rank}, nullity={dim}; max gadget coefficient={maxcoef}; all field identities exact')

if __name__=='__main__':
    for m in [1,3,5,7]: check(m)
