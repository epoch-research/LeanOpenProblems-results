"""Consistency checks for the explicit extension and star-cut lemmas.
The mathematical proofs are in Submission/Erdos74Amplification.md.
"""
from collections import deque
from itertools import product, combinations
import networkx as nx
import random

def edge(u,v): return tuple(sorted((u,v)))

def layer_pair(d):
    if d <= 1: return (1,0)
    if d == 2: return (1,2)
    if d == 3: return (0,2)
    return (0,1)

def min_colouring(G):
    vs=list(G)
    for k in range(1,len(vs)+1):
        for vals in product(range(k),repeat=len(vs)):
            c=dict(zip(vs,vals))
            if all(c[u]!=c[v] for u,v in G.edges()):return c,k
    return {},0

def extend(G,p0,S):
    """Construct (4) when the auxiliary labelled graph is balanced.
    Returns None if this finite check fails; never assumes balancedness.
    """
    S={edge(*e) for e in S}
    F={edge(u,v) for u,v in G.edges() if p0[u]==p0[v]}
    B=G.copy();B.remove_edges_from(F|S)
    assert all(p0[u]!=p0[v] for u,v in B.edges())
    W=set(v for e in F|S for v in e)
    adj={v:[] for v in W}
    def add(u,v,z):adj[u].append((v,z));adj[v].append((u,z))
    for u,v in F|S:add(u,v,1 ^ (edge(u,v) in S))
    for u in sorted(W):
        ds=nx.single_source_shortest_path_length(B,u,cutoff=4)
        for v in W:
            if u<v and v in ds:add(u,v,ds[v]%2)
    q={}
    for root in sorted(W):
        if root in q:continue
        q[root]=0;todo=[root]
        while todo:
            u=todo.pop()
            for v,z in adj[u]:
                val=q[u]^z
                if v in q:
                    if q[v]!=val:return None
                else:q[v]=val;todo.append(v)
    X={v for v in W if q[v]!=p0[v]};Y=W-X
    ds={v:0 for v in X};todo=deque(X)
    while todo:
        u=todo.popleft()
        for v in B[u]:
            if v not in ds:ds[v]=ds[u]+1;todo.append(v)
    assert all(ds.get(y,float('inf'))>4 for y in Y)
    c={v:layer_pair(ds.get(v,float('inf')))[p0[v]] for v in G}
    assert all(c[v]==q[v] for v in W)
    assert all(c[u]!=c[v] for u,v in B.edges())
    assert all(c[v]!=2 for u in W for v in B[u])
    U={v for e in S for v in e}
    J=G.subgraph(U)
    hc,h=min_colouring(J)
    for v in U:
        if hc[v]!=0:c[v]=hc[v]+1
    assert all(c[u]!=c[v] for u,v in G.edges())
    assert len(set(c.values()))<=max(3,h+1)
    return c,F,h,ds

# Table: check every possible adjacent-level configuration explicitly.
checks=0
for a,b in product(range(7),repeat=2):
    if abs(a-b)<=1:
        for bit in (0,1):
            assert layer_pair(a)[bit]!=layer_pair(b)[1-bit]
            checks+=1
print('layer-edge configurations checked:',checks)

# Long odd cycles: S is empty and is NOT a full cut-defect vector.
long_count=0
for n in (9,11,17,33,65,101):
    G=nx.cycle_graph(n);p0={v:v%2 for v in G}
    out=extend(G,p0,set());assert out is not None
    assert len(out[1])==1 and out[2]==0
    assert 2 in out[0].values()
    long_count+=1
print('nontrivial long-cycle extensions:',long_count)

# Hajós(K4, odd cycle): long global parity is not imposed by the short rows.
# K4-ab is on a=0,b=n,c=n+1,d=n+2; a is identified with cycle vertex 0,
# cycle edge 0--1 is removed, and b--1 is added.
hajos_count=0
for n in (51,75,101):
    G=nx.cycle_graph(n);G.remove_edge(0,1)
    a,b,c,d=0,n,n+1,n+2
    G.add_edges_from([(a,c),(a,d),(b,c),(b,d),(c,d),(b,1)])
    p0={v:v%2 for v in range(n)}
    p0.update({b:0,c:1,d:1})
    S={edge(c,d)}
    out=extend(G,p0,S);assert out is not None
    assert len(out[1])==2 and out[2]==2
    assert len(set(out[0].values()))==3
    # All cycles using the long cycle piece are longer than 8(t+s)=24.
    assert n-1 > 8*(len(out[1])+len(S))
    hajos_count+=1
print('nontrivial S!=empty extensions:',hajos_count)

# Exhaust all labelled graphs on 5 vertices and all cuts. S=F is always
# legitimate; this tests arbitrary support colourings, including nonbipartite U.
full_count=0
vs=list(range(5));edges=list(combinations(vs,2))
for mask in range(1<<len(edges)):
    G=nx.Graph();G.add_nodes_from(vs)
    G.add_edges_from(e for i,e in enumerate(edges) if mask>>i&1)
    for vals in product((0,1),repeat=4):
        p0=dict(zip(vs,(0,)+vals))
        S={edge(u,v) for u,v in G.edges() if p0[u]==p0[v]}
        out=extend(G,p0,S)
        assert out is not None
        full_count+=1
print('all five-vertex graph/cut extensions:',full_count)

# Small random cases with arbitrary S: balanced auxiliary labels suffice.
rng=random.Random(7416);balanced=unbalanced=0
for _ in range(500):
    G=nx.gnp_random_graph(6,.35,seed=rng.randrange(1<<30))
    p0={v:rng.randrange(2) for v in G}
    S={edge(u,v) for u,v in G.edges() if rng.random()<.25}
    out=extend(G,p0,S)
    if out is None:unbalanced+=1
    else:balanced+=1
print('random arbitrary-S cases, balanced/unbalanced:',balanced,unbalanced)

# Pair-witness star skeletons, including extensive sharing of the internal
# witnesses. Exhaust all cuts whenever there are at most 14 total vertices.
star_cases=star_cuts=0
for d in range(3,7):
    pairs=list(combinations(range(d),2))
    mappings=[]
    mappings.append([0]*len(pairs)) # One common star centre.
    if d+len(pairs)<=14:mappings.append(list(range(len(pairs))))
    for _ in range(12):
        z=rng.randrange(1,6)
        mappings.append([rng.randrange(z) for e in pairs])
    for mapping in mappings:
        G=nx.Graph();G.add_nodes_from(range(d))
        for (u,v),i in zip(pairs,mapping):G.add_edges_from([(u,d+i),(v,d+i)])
        vv=list(G)
        for vals in product((0,1),repeat=len(vv)-1):
            col=dict(zip(vv,(0,)+vals))
            a=sum(col[v]==0 for v in range(d));b=d-a
            bad=sum(col[u]==col[v] for u,v in G.edges())
            assert bad>=min(a,b)
            star_cuts+=1
        star_cases+=1
print('star skeletons/cuts checked:',star_cases,star_cuts)

# If a pair of ports has no common neighbour, explicitly check the rainbow
# extension used in the terminal lemma, for palettes q=3,...,6.
rainbow=0
for q in range(3,7):
    for _ in range(50):
        d=q+2;A=list(range(d+4));BB=list(range(d+4,d+10))
        G=nx.Graph();G.add_nodes_from(A+BB)
        for a in A:
            for b in BB:
                if rng.random()<.4:G.add_edge(a,b)
        # Enforce that ports 0 and 1 have no common neighbour.
        for z in list(set(G[0]) & set(G[1])):G.remove_edge(1,z)
        col={v:3 for v in A};col[0]=1;col[1]=2
        for j in range(3,q+1):col[j-1]=j
        for v in BB:col[v]=2 if G.has_edge(0,v) else 1
        assert all(col[u]!=col[v] for u,v in G.edges())
        assert set(col[v] for v in range(d))==set(range(1,q+1))
        rainbow+=1
print('rainbow-extension certificates:',rainbow)
print('ALL CHECKS PASSED')
