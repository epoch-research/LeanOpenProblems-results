#!/usr/bin/env python3
"""Exact verification of the analytical findings from this closing attempt."""
import itertools as it
import json
import random
import networkx as nx
from GlobalClosingIndependentChecks import (HERE, canon, edge, embedding, verify_embedding,
                                         seed_circuit, random_matching, critical)
from GlobalClosingCriticalSearch import tree_examples


def pendant_path(T,u,v):
    H=T.copy();H.remove_edge(u,v)
    A=H.subgraph(nx.node_connected_component(H,u)).copy()
    if A.degree(u)>1 or max(dict(A.degree()).values(),default=0)>2: return None
    path=[u];prev=None
    while True:
        nxt=[w for w in A[path[-1]] if w!=prev]
        if not nxt: break
        assert len(nxt)==1
        prev=path[-1];path.append(nxt[0])
    assert set(path)==set(A)
    return path


def bare_pinch(T,M):
    G=T.copy();G.remove_edges_from(M);z=len(T);G.add_node(z)
    G.add_edges_from((z,v) for a in M for v in a)
    return G,z


def check_leg_lifts():
    one=two=0
    for n in range(2,12):
        for T in nx.nonisomorphic_trees(n):
            T=canon(T)
            for a,b in T.edges():
                for u,v in [(a,b),(b,a)]:
                    path=pendant_path(T,u,v)
                    if path is None: continue
                    G,z=bare_pinch(T,[(u,v)])
                    f=list(T);f[path[0]]=z
                    for j in range(1,len(path)):f[path[j]]=path[j-1]
                    verify_embedding(G,T,f);one+=1
                    if len(path)>=3:
                        M=[(u,v),(path[-2],path[-1])]
                        assert len({w for e in M for w in e})==4
                        G,z=bare_pinch(T,M)
                        f=list(T);f[path[0]]=z
                        for j in range(1,len(path)):f[path[j]]=path[-1-j]
                        verify_embedding(G,T,f);two+=1
    print('explicit leg lifting maps checked:',dict(one_virtual_edge=one,two_virtual_edges=two),flush=True)


def subdivided_double_star(r):
    assert r>=5
    H=nx.Graph([(0,1),(0,2),(0,3),(1,4),(1,5)])
    T=nx.Graph();T.add_nodes_from(range(6));j=6
    for a,b in H.edges():
        T.add_edges_from([(a,j),(j,b)]);j+=1
    # Lengthen one pendant arm by 1+2(r-5) edges. The hub distance stays two.
    a=next(w for w in T[2]);b=2
    for _ in range(1+2*(r-5)):
        T.remove_edge(a,b);T.add_edges_from([(a,j),(j,b)]);a=j;j+=1
    T=canon(T)
    assert len(T)==2*r+2 and T.number_of_edges()==2*r+1
    assert [v for v,d in T.degree() if d==3]==[0,1]
    assert nx.shortest_path_length(T,0,1)==2
    middle=nx.shortest_path(T,0,1)[1]
    G=T.copy();G.remove_edge(0,middle)
    fresh=list(range(len(T),len(T)+r-1));z=len(T)+r-1
    G.add_nodes_from(fresh+[z]);G.add_edges_from((z,w) for w in [0,middle]+fresh)
    return T,G,z


def check_internal_edge_obstruction():
    for r in range(5,14):
        T,G,z=subdivided_double_star(r)
        assert nx.is_tree(G)
        assert max(dict(T.degree()).values())==3
        assert all(T.degree(w)>=2 for p in [0,1] for w in T[p])
        eligible=[v for v in G if sum(G.degree(w)>=2 for w in G[v])>=3]
        assert eligible==[0,1]
        assert nx.shortest_path_length(G,0,1)==3
        assert sum(G.degree(w)>=2 for w in G[z])==2
        assert embedding(G,T) is None
        assert not nx.algorithms.isomorphism.GraphMatcher(G,T).subgraph_is_monomorphic()
        assert min(dict(G.degree()).values())==1
        assert G.number_of_edges() < r*len(G)+1
    print('fresh-leaf internal-edge obstruction: nine all-role exact checks; none is critical',flush=True)


def check_strict_circuit():
    out=json.loads((HERE/'GlobalClosingStrictCircuit.json').read_text())
    r,n=out['r'],out['n']
    G=nx.Graph();G.add_nodes_from(range(n));G.add_edges_from(out['edges'])
    assert G.number_of_edges()==r*n+1==65
    maximum=[-10000]*n
    adj=[sum(1<<v for v in G[u]) for u in G]
    # Independent exact subset enumeration, every proper nonempty set.
    edges=[0]*(1<<n)
    for S in range(1,(1<<n)-1):
        bit=S&-S;u=bit.bit_length()-1;rest=S^bit
        edges[S]=edges[rest]+(adj[u]&rest).bit_count()
        size=S.bit_count();maximum[size]=max(maximum[size],edges[S]-r*size)
    assert maximum[1:]==out['max_proper_surplus_by_size']
    assert max(maximum[1:])<=-1
    assert G.has_edge(0,1) and G.has_edge(1,3) and G.has_edge(3,0)
    H=G.copy();ordering=[];later=[]
    while H:
        v=min(H,key=lambda u:(H.degree(u),u));later.append(H.degree(v));ordering.append(v);H.remove_node(v)
    assert max(later)<=6
    high=[v for v in G if G.degree(v)>=9]
    residual={v:min(d for _,d in G.subgraph(set(G)-{v}).degree()) for v in high}
    assert all(d==5 for d in residual.values())
    T=nx.Graph([(0,6),(6,7),(7,1),(0,8),(8,2),(1,9),(9,4),(0,3),(1,5)])
    T.add_nodes_from(range(10))
    assert nx.is_tree(T) and max(dict(T.degree()).values())==3
    assert sorted(len(S) for S in nx.bipartite.sets(T))==[5,5]
    assert all(6+T.degree(u)+T.degree(v)<12 for u,v in T.edges())
    assert all(6+T.degree(u)+T.degree(v)<12 for z in T if T.degree(z)==2
               for u,v in it.combinations(T[z],2))
    f=embedding(G,T);assert f is not None
    verify_embedding(G,T,f)
    out.update(degeneracy_order=ordering,later_degrees=later,
               high_vertex_residual_minimum_degree=residual,
               target_edges=list(T.edges()),target_embedding=f)
    (HERE/'GlobalClosingStrictCircuit.json').write_text(json.dumps(out,indent=2))
    print('strict circuit: all 65534 proper subsets checked',flush=True)
    print('maxima by subset order:',maximum[1:],flush=True)
    print('6-degeneracy order:',ordering,'later degrees:',later,flush=True)
    print('ordinary target embedding:',f,'; all high-vertex apex budgets fail:',residual,flush=True)



def check_matching_component_budget():
    rng=random.Random(83776);tests=0;disconnected=0
    for r in range(1,7):
        k=2*r+1
        for typ in range(3):
            C=seed_circuit(r,typ,rng)
            for q in range(1,r+1):
                for _ in range(4):
                    M=random_matching(C,q,rng)
                    if M is None: continue
                    H=C.copy();H.remove_edges_from(M)
                    pieces=list(nx.connected_components(H))
                    ds=[r*len(S)-H.subgraph(S).number_of_edges() for S in pieces]
                    assert min(dict(H.degree()).values())>=r
                    assert all(d>=0 for d in ds) and sum(ds)==q-1
                    assert all(len(S)>=k for S in pieces)
                    tests+=1;disconnected+=len(pieces)>1
        C=seed_circuit(r,1,rng)
        # Force a separating matching, including the unique clique-to-clique bridge.
        for q in range(1,r+1):
            M=[(0,k)]+[(2*j+1,2*j+2) for j in range(q-1)]
            H=C.copy();H.remove_edges_from(M)
            pieces=list(nx.connected_components(H))
            assert sorted(map(len,pieces))==[k,k]
            ds=[r*len(S)-H.subgraph(S).number_of_edges() for S in pieces]
            assert sorted(ds)==[0,q-1]
            tests+=1;disconnected+=1
    print('matching-component budget:',tests,'exact checks, including',disconnected,
          'disconnected deletions',flush=True)

def check_double_cover_identity():
    rng=random.Random(477222);checks=0;small_support=0
    for _ in range(12000):
        n=rng.randint(2,11);G=nx.gnp_random_graph(n,rng.random(),seed=rng.randrange(2**31))
        X={v for v in G if rng.randrange(2)};Y={v for v in G if rng.randrange(2)}
        I=X&Y;P=X-Y;Q=Y-X;S=X|Y
        a=rng.randint(1,8);b=rng.randint(a,9);k=a+b-1
        cross=sum(G.has_edge(u,v) for u in X for v in Y)
        potential=cross-(b-1)*len(X)-(a-1)*len(Y)
        e=lambda A:G.subgraph(A).number_of_edges()
        assert cross==e(S)+e(I)-e(P)-e(Q)
        assert 2*potential==2*(e(S)+e(I)-e(P)-e(Q))-(k-1)*(len(S)+len(I))-(b-a)*(len(P)-len(Q))
        if len(S)<=k:
            assert potential<=0;small_support+=1
        checks+=1
    print('double-cover exact identities:',checks,'; small-support nonpositivity:',small_support,flush=True)
    # Direct all-(X,Y) confirmation of the strict-circuit theorem in K6 minus 2K2.
    G=nx.complete_graph(6);G.remove_edges_from([(0,1),(2,3)])
    allv=set(G);positive=[]
    for x in range(1<<6):
        X={v for v in G if x>>v&1}
        for y in range(1<<6):
            Y={v for v in G if y>>v&1}
            q=sum(G.has_edge(u,v) for u in X for v in Y)-2*(len(X)+len(Y))
            if q>0:positive.append((x,y,q))
    assert positive==[(63,63,2)]
    print('all 4096 double-cover domain pairs in strict 2-circuit:',positive,flush=True)


def check_forest_discount_failure():
    for t in range(3,12):
        G=canon(nx.complete_bipartite_graph(t,t))
        F=canon(nx.disjoint_union(nx.star_graph(t),nx.path_graph(2)))
        assert G.number_of_nodes()>=F.number_of_nodes()
        assert min(dict(G.degree()).values())==F.number_of_edges()-1
        if t<=6:
            assert embedding(G,F) is None
        # For larger t the independent exact certificate is the bipartition:
        # either orientation of the star occupies an entire host side.
        assert sorted(len(S) for S in nx.bipartite.sets(G))==[t,t]
    print('one-unit forest degree discount fails in K_t,t for K_1,t + K2, t=3..11; exhaustive matching at t<=6',flush=True)


if __name__=='__main__':
    check_leg_lifts()
    check_internal_edge_obstruction()
    check_strict_circuit()
    check_matching_component_budget()
    check_double_cover_identity()
    check_forest_discount_failure()
