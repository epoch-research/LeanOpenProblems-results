#!/usr/bin/env python3
"""Constructive audits for HighLeafParentFindings.md; not a general ES proof.

Run: python3 Submission/HighLeafParentChecks.py
Uses the already-existing constructive CL implementation only as a forest
embedding routine. Does not modify/import any Lean specification.
"""
from __future__ import annotations
from collections import Counter
from itertools import combinations, permutations, product
import hashlib
import networkx as nx
from CommonMarkedForestChecks import compile_components, common_marked_forest

ST = Counter()
SPEC_HASH = '674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103'


def trees(k):
    return list(nx.nonisomorphic_trees(k + 1))


def small_color(T):
    col = nx.bipartite.color(T)
    A = {v for v in T if col[v] == 0}
    B = set(T) - A
    return (A, B) if len(A) <= len(B) else (B, A)


def parents(T):
    return {next(iter(T[v])) for v in T if T.degree(v) == 1}


def verify(T, G, f, p=None):
    assert set(f) == set(T)
    assert len(set(f.values())) == len(T)
    assert all(G.has_edge(f[u], f[v]) for u, v in T.edges())
    if p is not None:
        assert p in parents(T) and G.degree(f[p]) >= len(T) - 1
    ST['explicit full embeddings checked'] += 1
    return f


def greedy(T, G, p, s, allowed=None):
    allowed = set(G) if allowed is None else set(allowed)
    f = {p: s}
    order = [p]
    for u in order:
        for v in T[u]:
            if v in f:
                continue
            opts = set(G[f[u]]) & allowed - set(f.values())
            assert opts
            f[v] = min(opts)
            order.append(v)
    assert len(f) == len(T)
    return f


def is_critical(G, k):
    n, m = len(G), G.number_of_edges()
    if m != (k - 1) * n // 2 + 1:
        return False
    adj = [sum(1 << w for w in G[v]) for v in range(n)]
    es = [0] * (1 << n)
    for S in range(1, 1 << n):
        z = S & -S
        v = z.bit_length() - 1
        R = S ^ z
        es[S] = es[R] + (adj[v] & R).bit_count()
        if S != (1 << n) - 1 and 2 * es[S] > (k - 1) * S.bit_count():
            return False
    return True


def colored_core(G, k, alpha, beta):
    assert alpha <= beta and alpha + beta == k + 1
    X, Y = small_color(G)
    C = set(G)
    def surplus(S):
        return (G.subgraph(S).number_of_edges()
                - (beta - 1) * len(S & X) - (alpha - 1) * len(S & Y))
    q0 = surplus(C)
    assert q0 > 0
    while True:
        old = surplus(C)
        v = next((v for v in sorted(C)
                  if len(set(G[v]) & C) <= (beta - 1 if v in X else alpha - 1)), None)
        if v is None:
            break
        C.remove(v)
        assert surplus(C) >= old
        ST['asymmetric peeling deletions'] += 1
    assert C and surplus(C) > 0
    assert len(C & X) <= len(C & Y)
    high = [v for v in C & X if len(set(G[v]) & C) >= k]
    assert high and all(G.degree(v) >= k for v in high)
    assert all(len(set(G[v]) & C) >= (beta if v in X else alpha) for v in C)
    ST['asymmetric high cores constructed'] += 1
    return C, X, Y, min(high)


def colored_embedding(G, T, p, certificate):
    C, X, Y, s = certificate
    A, B = small_color(T)
    assert p in A
    f = {p: s}; order = [p]
    for u in order:
        for v in T[u]:
            if v in f:
                continue
            side = X if v in A else Y
            opts = (set(G[f[u]]) & C & side) - set(f.values())
            assert opts
            f[v] = min(opts); order.append(v)
    verify(T, G, f)
    assert G.degree(f[p]) >= len(T) - 1
    ST['smaller-color roots at high vertices'] += 1
    return f


def core_embedding(G, T, ell):
    k = len(T) - 1
    Q = nx.k_core(G, k - 1)
    assert Q
    highs = [v for v in Q if G.degree(v) >= k]
    assert highs
    s = min(highs); p = next(iter(T[ell]))
    S = T.copy(); S.remove_node(ell)
    f = greedy(S, Q, p, s)
    fresh = set(G[s]) - set(f.values())
    assert fresh
    f[ell] = min(fresh)
    ST['arbitrary-leaf core extensions'] += 1
    return verify(T, G, f, p)


def select_U(T, A, h, p):
    assert 1 <= h < len(A) and p in A and T.degree(p) >= 2
    I = {v for v in A if T.degree(v) >= 2}
    if len(I) >= h:
        U = {p} | set(sorted(I - {p})[:h - 1])
    else:
        U = I | set(sorted(A - I)[:h - len(I)])
    assert len(U) == h and p in U
    assert sum(T.degree(u) for u in U) >= 2 * h
    assert T.subgraph(U).number_of_edges() == 0
    ST['parent-containing independent selections'] += 1
    return U


def forest_embedding(F, G, B):
    order = sorted(B)
    lookup = {v: i for i, v in enumerate(order)}
    adj = [sum(1 << lookup[w] for w in G[v] if w in lookup) for v in order]
    assert len(B) >= len(F)
    assert all(a.bit_count() >= F.number_of_edges() for a in adj)
    marks = {min(C) for C in nx.connected_components(F)}
    comp = compile_components(F, marks)
    full = (1 << len(B)) - 1
    ff = common_marked_forest(adj, full, full, comp)
    ST['constructive CL forest embeddings'] += 1
    return {u: order[v] for u, v in ff.items()}


def multipartite_embedding(G, parts, T, p):
    k = len(T) - 1; n = len(G); t = n - k
    assert 2 * G.number_of_edges() > (k - 1) * n
    A, B = small_color(T)
    assert p in A and T.degree(p) >= 2
    hp = [C for C in parts if len(C) <= t]
    H = set().union(*hp)
    h = len(H)
    assert H == {v for v in G if G.degree(v) >= k} and h > 0
    if h >= len(A):
        X = set()
        for C in hp:
            X |= C
            if len(X) >= len(A):
                break
        assert len(A) <= len(X) <= len(A) + t - 1
        Y = set(G) - X
        assert len(Y) >= len(B)
        f = dict(zip(sorted(A), sorted(X)))
        f.update(zip(sorted(B), sorted(Y)))
        ST['multipartite high-part grouping'] += 1
    else:
        L = set(G) - H
        for C in parts:
            if C <= L:
                assert len(C) <= t + h
        assert all(len(set(G[v]) & L) >= k - 2*h for v in L)
        U = select_U(T, A, h, p)
        F = T.subgraph(set(T) - U).copy()
        f = forest_embedding(F, G, L)
        f.update(zip(sorted(U), sorted(H)))
        ST['multipartite deficit/forest branch'] += 1
    return verify(T, G, f, p)


def partitions(n, lo=1):
    if n == 0:
        yield ()
    for a in range(lo, n + 1):
        for rest in partitions(n - a, a):
            yield (a,) + rest


def clique_join(a, sizes):
    G = nx.complete_graph(a); modules=[]; start=a
    for b in sizes:
        C = set(range(start, start+b)); start += b; modules.append(C)
        G.add_nodes_from(C); G.add_edges_from(combinations(C, 2))
        G.add_edges_from((x, y) for x in range(a) for y in C)
    return G, set(range(a)), modules


def clique_join_critical(a, sizes, k):
    # Max over each clique module occurs at an endpoint (coordinate convexity).
    G, S, modules = clique_join(a, sizes)
    if G.number_of_edges() != (k-1)*len(G)//2+1:
        return False
    def contrib(x, b):
        return b*(b+2*x-k)  # doubled surplus contribution
    for x in range(a):
        if x*(x-k)+sum(max(0, contrib(x,b)) for b in sizes) > 0:
            return False
    # For x=a a proper set must omit some module vertex.
    for j, b in enumerate(sizes):
        caps = list(sizes); caps[j] = b-1
        if a*(a-k)+sum(max(0, contrib(a,c)) for c in caps) > 0:
            return False
    return True


def clique_join_embedding(G, S, modules, T, p):
    k = len(T)-1; a=len(S); A,B=small_color(T)
    assert p in A and T.degree(p)>=2
    assert all(G.degree(s)>=k for s in S)
    if a >= len(A):
        f=dict(zip(sorted(A),sorted(S)))
        f.update(zip(sorted(B), sorted(set(G)-set(f.values()))))
    else:
        assert all(len(C)-1>=k-2*a for C in modules)
        U=select_U(T,A,a,p)
        F=T.subgraph(set(T)-U).copy()
        f=forest_embedding(F,G,set(G)-S)
        f.update(zip(sorted(U),sorted(S)))
    ST['critical clique-join embeddings']+=1
    return verify(T,G,f,p)


def blowup_cycle(cap):
    G=nx.Graph(); parts=[]; at=0
    for a in cap:
        C=set(range(at,at+a));at+=a;parts.append(C);G.add_nodes_from(C)
    for i,C in enumerate(parts):
        G.add_edges_from((u,v) for u in C for v in parts[(i+1)%len(parts)])
    return G


def critical_cycle(cap,k):
    # All proper induced subsets: multiaffine maximum on each G-v box.
    q=len(cap)
    for j in range(q):
        c=list(cap);c[j]-=1
        for mask in range(1<<q):
            x=[c[i] if mask>>i&1 else 0 for i in range(q)]
            val=2*sum(x[i]*x[(i+1)%q] for i in range(q))-(k-1)*sum(x)
            assert val<=0
            ST['cycle blow-up proper-box corners']+=1
    G=blowup_cycle(cap)
    assert G.number_of_edges()==(k-1)*len(G)//2+1
    return G


def audits():
    atlas=nx.graph_atlas_g()
    cache={k:trees(k) for k in range(1,12)}
    # Tree-only facts: every support in the smaller color can be retained in U.
    for k in range(2,12):
        for T in cache[k]:
            A,B=small_color(T)
            assert parents(T)&A
            for p in parents(T)&A:
                for h in range(1,len(A)):
                    select_U(T,A,h,p)
            if max(dict(T.degree()).values())>k//2:
                assert all(v in parents(T) for v in T if T.degree(v)>k//2)
    print('Tree-selection and large-degree/support facts: PASS', flush=True)

    for G in atlas:
        n=len(G)
        if n<2:continue
        for k in range(1,n):
            if not is_critical(G,k):continue
            ST['critical atlas hosts']+=1
            assert nx.is_connected(G)
            H={v for v in G if G.degree(v)>=k}
            surplus=sum(G.degree(v)-k+1 for v in H)
            deficit=sum(k-1-G.degree(v) for v in set(G)-H)
            assert surplus-deficit==2*G.number_of_edges()-(k-1)*n
            if nx.is_bipartite(G):
                ST['bipartite critical atlas hosts']+=1
                cores={}
                for T in cache[k]:
                    A,B=small_color(T); ab=(len(A),len(B))
                    if ab not in cores:cores[ab]=colored_core(G,k,*ab)
                    for p in A:
                        colored_embedding(G,T,p,cores[ab])
            if nx.k_core(G,k-1):
                for T in cache[k]:
                    for ell in T:
                        if T.degree(ell)==1:core_embedding(G,T,ell)
    print('Critical atlas/core and bipartite constructions: PASS', flush=True)

    for k,cap in [(6,(2,3,3,3,2,2)),(8,(2,5,4,5,2,7)),
                  (10,(3,4,4,4,3,17))]:
        G=critical_cycle(cap,k); cores={}
        for T in cache[k]:
            A,B=small_color(T);ab=(len(A),len(B))
            if ab not in cores:cores[ab]=colored_core(G,k,*ab)
            for p in A:colored_embedding(G,T,p,cores[ab])
    # The old critical wing maximum-root obstruction is a positive instance here.
    from IncidenceCriticalRootChecks import host, degree_four_tree
    G,s,AA,BB=host(9)
    T,u,_,_=degree_four_tree(9)
    A,B=small_color(T);certificate=colored_core(G,19,len(A),len(B))
    f=colored_embedding(G,T,u,certificate)
    assert f[u]!=s and G.degree(f[u])>=19 and u in parents(T)
    ST['old maximum-root obstruction resolved by another high']+=1
    print('Larger critical bipartite constructions: PASS', flush=True)

    for n in range(3,13):
        for sizes in partitions(n):
            if len(sizes)<2:continue
            G=nx.complete_multipartite_graph(*sizes)
            parts=[];at=0
            for c in sizes:parts.append(set(range(at,at+c)));at+=c
            for k in range(2,min(n,9)):
                if 2*G.number_of_edges()<=(k-1)*n:continue
                for T in cache[k]:
                    A,B=small_color(T)
                    p=min(parents(T)&A)
                    multipartite_embedding(G,parts,T,p)
    print('Complete multipartite positive-density construction: PASS', flush=True)

    for a in range(1,7):
        for eps in (1,2):
            num=a*(a-1)+eps
            for b in range(eps,num+1):
                if num%b:continue
                k=2*a+b-1
                if not 2<=k<=11:continue
                sizes=[b]*(a+num//b)
                assert clique_join_critical(a,sizes,k)
                G,S,modules=clique_join(a,sizes)
                for T in cache[k]:
                    A,B=small_color(T);p=min(parents(T)&A)
                    clique_join_embedding(G,S,modules,T,p)
    a,k,sizes=4,11,[4]*5+[5]
    assert clique_join_critical(a,sizes,k)
    G,S,modules=clique_join(a,sizes)
    for T in cache[k]:
        A,B=small_color(T);p=min(parents(T)&A)
        clique_join_embedding(G,S,modules,T,p)
    print('Critical clique-join constructions: PASS', flush=True)

    # Check the exact extension disjunction on every applicable small injection.
    for G in atlas:
        if not 2<=len(G)<=5:continue
        for k in range(1,min(5,len(G))):
            for T in cache[k]:
                ell=min(v for v in T if T.degree(v)==1)
                p=next(iter(T[ell]));S=T.copy();S.remove_node(ell)
                for image in permutations(G,len(S)):
                    f=dict(zip(S,image))
                    if not all(G.has_edge(f[u],f[v]) for u,v in S.edges()):continue
                    s=f[p];d=G.degree(s)
                    q=len(set(G[s])&set(image))
                    missed=sum(v!=s and not G.has_edge(s,v) for v in image)
                    fresh=len(set(G[s])-set(image))
                    assert fresh==d-q==missed-(k-1-d)
                    disj=(d>=k or (d<=k-1 and missed>=k-d))
                    assert (fresh>=1)==disj
                    ST['exact leaf-extension identities']+=1
    print('Exact high/low extension disjunction: PASS', flush=True)
    assert hashlib.sha256(open('Submission/Spec.lean','rb').read()).hexdigest()==SPEC_HASH
    print('Spec.lean hash unchanged:',SPEC_HASH)
    print('AUDIT TOTALS:')
    for key,value in sorted(ST.items()):print(f'  {key}: {value}')

if __name__=='__main__':audits()
