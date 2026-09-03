#!/usr/bin/env python3
"""Bounded independent searches under ALL proper-set circuit constraints.

Positive counterexamples would be checked by exact graph algorithms. A solver
limit, absence of a found witness, or floating-point infeasibility is NOT a
proof of the Erdős--Sós conjecture.
"""
import argparse
import itertools as it
import json
import random
import time
import numpy as np
import networkx as nx
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import csr_matrix
from GlobalClosingIndependentChecks import (
    HERE, canon, edge, embedding, verify_embedding, critical, critical_subsets,
    adversarial_matching,
)


def arborescence_circuit(r, n, bias, rng):
    """Choose a spanning out-tree, then fill every quota. Root reaches all.

    This samples circuits independently of matching-pinch constructions.
    """
    for attempt in range(100):
        D = nx.DiGraph()
        D.add_nodes_from(range(n))
        available = [0]
        for v in range(1, n):
            if bias == 'path':
                p = v-1
            else:
                p = rng.choice(available)
            D.add_edge(p, v)
            if D.out_degree(p) == r+(p == 0):
                available.remove(p)
            available.append(v)
        order = list(range(n)); rng.shuffle(order)
        ok = True
        hubs = set(rng.sample(range(n), r+2))
        for u in order:
            while D.out_degree(u) < r+(u == 0):
                choices = [v for v in range(n) if v != u and not D.has_edge(u,v)
                           and not D.has_edge(v,u)]
                if not choices:
                    ok = False
                    break
                weights = [15 if bias == 'hubs' and v in hubs else 1 for v in choices]
                v = rng.choices(choices, weights)[0]
                D.add_edge(u, v)
            if not ok: break
        if ok:
            G = nx.Graph(D)
            assert G.number_of_edges() == r*n+1
            assert len(nx.descendants(D, 0)) == n-1
            assert all(D.out_degree(v) == r+(v == 0) for v in D)
            assert critical(G, r)
            return canon(G)
    raise RuntimeError('quota completion retry limit')


def tree_examples(r):
    k = 2*r+1
    out = []
    # Extremely unbalanced, low-max-degree subdivided double broom.
    T = nx.path_graph(5)
    j = 5
    for p, count in [(0, r-3), (4, r-3), (2, 1)]:
        for _ in range(count):
            T.add_edge(p, j); j += 1
    assert T.number_of_edges() == k-2
    # Two extra subdivisions maintain maximum degree and change parity profiles.
    for a,b in [(0,1),(3,4)]:
        T.remove_edge(a,b); T.add_edges_from([(a,j),(j,b)]); j += 1
    out.append(canon(T))
    # Subcubic with four degree-three vertices and long intervening paths.
    length = k-6
    T = nx.path_graph(length+1)
    j = length+1
    for p, count in [(0,2),(length,2),(1,1),(length-1,1)]:
        for _ in range(count): T.add_edge(p,j);j+=1
    out.append(canon(T))
    # Uniformly sampled bounded-degree Prüfer trees with exactly k edges.
    rng = random.Random(443+r)
    while len(out) < 6:
        T = nx.from_prufer_sequence([rng.randrange(k+1) for _ in range(k-1)])
        if max(dict(T.degree()).values()) <= min(r,4): out.append(canon(T))
    assert all(len(T) == k+1 and nx.is_tree(T) for T in out)
    return out


def independent_resilience(samples):
    rng = random.Random(477210)
    stats = dict(hosts=0, instances=0, cuts=0, milp_infeasible=0, exact_no_matching=0,
                 solver_limit=0, cut_limit=0, exact_obstruction=0)
    start = time.monotonic()
    for r in [3,4,5,6]:
        ts = tree_examples(r) if r >= 4 else [canon(T) for T in nx.nonisomorphic_trees(8)
                                             if max(dict(T.degree()).values()) <= 3]
        for j in range(samples):
            n = 2*r+3+(j*7) % (4*r+1)
            G = arborescence_circuit(r,n,['plain','path','hubs'][j % 3],rng)
            stats['hosts'] += 1
            for T in ts:
                stats['instances'] += 1
                result = adversarial_matching(G,T,r,max_cuts=300)
                stats[result['status']] += 1
                stats['cuts'] += result['cuts']
                if result['status'] == 'exact_obstruction':
                    out = dict(r=r,n=n,G=list(G.edges()),T=list(T.edges()),result=result)
                    (HERE/'GlobalClosingResilienceObstruction.json').write_text(json.dumps(out))
                    print('EXACT MATCHING-RESILIENCE OBSTRUCTION',out,flush=True)
                    return
            print('independent-circuit checkpoint',r,j,stats,
                  'seconds',round(time.monotonic()-start,2),flush=True)
    print('independent-circuit result',stats,'seconds',round(time.monotonic()-start,2),flush=True)


def varied_embedding(G,T,rng):
    p = list(G);rng.shuffle(p)
    P = nx.relabel_nodes(G,{u:p[u] for u in G})
    f = embedding(P,T)
    if f is None: return None
    inverse = {p[u]:u for u in G}
    ans = [inverse[v] for v in f]
    verify_embedding(G,T,ans)
    return ans


def actual_search(r,n,T,seconds=90,batch=30):
    """Search directly for an actual ES counterexample; no virtual-edge relaxation.

    Uses exact r-circuit edge count, all proper induced-set inequalities,
    and delta>=r+1. Vertex 0 is high; vertex 1 has the low degree forced by
    failure of the already proved apex criterion. Fixed labels cause no loss
    since these vertices necessarily have distinct degrees.
    """
    assert n >= 2*r+2 and len(T) == 2*r+2
    start=time.monotonic(); rng=random.Random(477222+r+n)
    k=2*r+1; Delta=max(dict(T.degree()).values())
    E=list(it.combinations(range(n),2)); eid={a:i for i,a in enumerate(E)}
    m=len(E)
    rows=[]; lb=[]; ub=[]
    def addrow(indices,lower,upper):
        row={j:1 for j in indices};rows.append(row);lb.append(lower);ub.append(upper)
    addrow(range(m),r*n+1,r*n+1)
    for v in range(n):
        addrow([j for j,a in enumerate(E) if v in a],
               k if v == 0 else r+1,
               k-Delta if v == 1 else n-1)
    # All smaller proper sets are sparse by simplicity. No subset omitted.
    for size in range(2*r+2,n):
        for S in it.combinations(range(n),size):
            ss=set(S)
            addrow([j for j,(u,v) in enumerate(E) if u in ss and v in ss],
                   -np.inf,r*size)
    structural_rows=len(rows); iterations=0; cuts=set(); candidates=0
    solver_status='time_budget'
    while time.monotonic()-start < seconds:
        rr=[];cc=[];vv=[]
        for i,row in enumerate(rows):
            for j,v in row.items():rr.append(i);cc.append(j);vv.append(v)
        A=csr_matrix((vv,(rr,cc)),shape=(len(rows),m))
        remaining=seconds-(time.monotonic()-start)
        if remaining <= 0: break
        c=np.array([rng.uniform(-1,1) for _ in E])
        sol=milp(c,integrality=np.ones(m),bounds=Bounds(np.zeros(m),np.ones(m)),
                 constraints=LinearConstraint(A,np.array(lb),np.array(ub)),
                 options={'time_limit':min(remaining,15),'mip_rel_gap':0})
        iterations+=1
        if sol.status == 2:
            solver_status='milp_infeasible_not_formal_certificate';break
        if sol.x is None:
            solver_status='solver_limit';break
        X=[int(round(x)) for x in sol.x]
        assert all(abs(x-y)<1e-5 for x,y in zip(sol.x,X))
        # Independently verify all constraints, without tolerance.
        for row,lo,hi in zip(rows,lb,ub):
            a=sum(X[j]*v for j,v in row.items())
            assert lo <= a <= hi
        G=nx.Graph();G.add_nodes_from(range(n));G.add_edges_from(E[j] for j in range(m) if X[j])
        assert critical(G,r)
        candidates+=1
        for _ in range(batch):
            f=varied_embedding(G,T,rng)
            if f is None:
                assert critical_subsets(G,r)
                assert not nx.algorithms.isomorphism.GraphMatcher(G,T).subgraph_is_monomorphic()
                out=dict(r=r,n=n,k=k,G=list(G.edges()),T=list(T.edges()))
                (HERE/'GlobalClosingActualCounterexample.json').write_text(json.dumps(out))
                print('ACTUAL ES COUNTEREXAMPLE VERIFIED',out,flush=True)
                return out
            ce=tuple(sorted(eid[edge(f[u],f[v])] for u,v in T.edges()))
            if ce not in cuts:
                cuts.add(ce);addrow(ce,-np.inf,k-1)
        if candidates % 5 == 0:
            print('actual-search checkpoint',r,n,'candidates',candidates,'copy cuts',len(cuts),
                  'seconds',round(time.monotonic()-start,2),flush=True)
    out=dict(r=r,n=n,k=k,Delta=Delta,structural_rows=structural_rows,
             candidates=candidates,copy_cuts=len(cuts),iterations=iterations,
             solver_status=solver_status,seconds=round(time.monotonic()-start,2))
    print('actual-search result (NO COMPLETE THEOREM)',out,flush=True)
    return out


if __name__ == '__main__':
    p=argparse.ArgumentParser()
    p.add_argument('mode',choices=['resilience','actual'])
    p.add_argument('--samples',type=int,default=8)
    p.add_argument('--seconds',type=float,default=90)
    args=p.parse_args()
    if args.mode == 'resilience':independent_resilience(args.samples)
    else:
        for r,n,ti in [(5,15,1),(6,17,0)]:
            actual_search(r,n,tree_examples(r)[ti],args.seconds)
