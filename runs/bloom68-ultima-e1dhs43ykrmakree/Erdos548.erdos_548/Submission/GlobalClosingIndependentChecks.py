#!/usr/bin/env python3
"""Independent exact checks for global ES closing attempts.

No finite search is treated as a proof of Erdős--Sós.  Containment is
non-induced.  All concrete reported certificates are independently checked.
"""
from __future__ import annotations
import argparse
import itertools as it
import json
import random
import time
from pathlib import Path
import networkx as nx
import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp

HERE = Path(__file__).resolve().parent


def canon(G):
    return nx.convert_node_labels_to_integers(G)


def edge(u, v):
    return tuple(sorted((u, v)))


def embedding(G, T, M=(), prescribed=None, domains=None):
    """Exact backtracking: at most one M-edge, required to be pendant in T.

    With M empty this is ordinary (also disconnected-forest) containment.
    """
    n, t = len(G), len(T)
    assert set(G) == set(range(n)) and set(T) == set(range(t))
    if t > n:
        return None
    adj = [sum(1 << v for v in G[u]) for u in range(n)]
    tadj = [list(T[u]) for u in range(t)]
    deg = [G.degree(u) for u in range(n)]
    td = [T.degree(u) for u in range(t)]
    base = [sum(1 << v for v in range(n) if deg[v] >= td[u]) for u in range(t)]
    if domains:
        for u, A in domains.items():
            base[u] &= sum(1 << v for v in A)
    if prescribed:
        for u, v in prescribed.items():
            base[u] &= 1 << v
    mb = [0] * n
    for u, v in M:
        mb[u] |= 1 << v
        mb[v] |= 1 << u
    f = [-1] * t
    full = (1 << n) - 1

    def dfs(done, used, defect):
        if done == t:
            return f.copy()
        best = None
        for u in range(t):
            if f[u] >= 0:
                continue
            cand = base[u] & (full ^ used)
            parents = [w for w in tadj[u] if f[w] >= 0]
            for w in parents:
                cand &= adj[f[w]]
                if defect or (td[u] != 1 and td[w] != 1):
                    cand &= ~mb[f[w]]
            count = cand.bit_count()
            if count == 0:
                return None
            key = (count, -len(parents), -td[u])
            if best is None or key < best[0]:
                best = (key, u, cand, parents)
        _, u, cand, parents = best
        while cand:
            b = cand & -cand
            cand -= b
            v = b.bit_length() - 1
            new_defect = defect + sum(bool(mb[v] & (1 << f[w])) for w in parents)
            if new_defect > 1:
                continue
            if (adj[v] & (full ^ (used | b))).bit_count() < td[u] - len(parents):
                continue
            f[u] = v
            ans = dfs(done + 1, used | b, new_defect)
            if ans is not None:
                return ans
            f[u] = -1
        return None

    ans = dfs(0, 0, 0)
    if ans is not None:
        verify_embedding(G, T, ans, M, prescribed, domains)
    return ans


def verify_embedding(G, T, f, M=(), prescribed=None, domains=None):
    assert len(f) == len(T) and len(set(f)) == len(T)
    assert all(G.has_edge(f[u], f[v]) for u, v in T.edges())
    marked = {edge(*a) for a in M}
    hit = [(u, v) for u, v in T.edges() if edge(f[u], f[v]) in marked]
    assert len(hit) <= 1
    assert all(T.degree(u) == 1 or T.degree(v) == 1 for u, v in hit)
    if prescribed:
        assert all(f[u] == v for u, v in prescribed.items())
    if domains:
        assert all(f[u] in A for u, A in domains.items())


def critical(G, r):
    """Exact integral flow plus reachability, equivalent to r-criticality."""
    n = len(G)
    if not n or G.number_of_edges() != r*n + 1:
        return False
    F = nx.DiGraph()
    source, sink = ('source',), ('sink',)
    for j, (u, v) in enumerate(G.edges()):
        a = ('e', j)
        F.add_edge(source, a, capacity=1)
        F.add_edge(a, ('v', u), capacity=1)
        F.add_edge(a, ('v', v), capacity=1)
    z = next(iter(G))
    for u in G:
        F.add_edge(('v', u), sink, capacity=r+(u == z))
    value, flow = nx.maximum_flow(F, source, sink)
    if value != G.number_of_edges():
        return False
    D = nx.DiGraph()
    D.add_nodes_from(G)
    for j, (u, v) in enumerate(G.edges()):
        if flow[('e', j)][('v', u)]:
            D.add_edge(u, v)
        else:
            D.add_edge(v, u)
    assert all(D.out_degree(v) == r+(v == z) for v in G)
    return len(nx.descendants(D, z)) == n-1


def critical_subsets(G, r):
    n = len(G)
    if G.number_of_edges() != r*n+1:
        return False
    adj = [sum(1 << v for v in G[u]) for u in G]
    for S in range(1, (1 << n)-1):
        e = sum((adj[u] & S).bit_count() for u in G if S >> u & 1)//2
        if e > r*S.bit_count():
            return False
    return True


def pinch(C, r, M, B):
    M = [edge(*x) for x in M]
    U = {v for a in M for v in a}
    assert len(U) == 2*len(M) and 1 <= len(M) <= r
    assert len(B) == r-len(M) and not U.intersection(B)
    assert all(C.has_edge(*a) for a in M)
    G = C.copy()
    z = len(G)
    G.remove_edges_from(M)
    G.add_node(z)
    G.add_edges_from((z, u) for u in U.union(B))
    assert critical(G, r)
    return G


def random_matching(G, q, rng):
    E = list(G.edges())
    rng.shuffle(E)
    M, used = [], set()
    for u, v in E:
        if u not in used and v not in used:
            M.append(edge(u, v))
            used.update((u, v))
            if len(M) == q:
                return M
    return None


def seed_circuit(r, typ, rng):
    k = 2*r+1
    if typ == 0:
        G = nx.complete_graph(k+1)
        G.remove_edges_from((2*j, 2*j+1) for j in range(r))
    elif typ == 1:
        G = nx.disjoint_union(nx.complete_graph(k), nx.complete_graph(k))
        G.add_edge(0, k)
    else:
        n = k+1+rng.randrange(0, 7)
        G = nx.random_regular_graph(2*r, n, seed=rng.randrange(2**31))
        while not nx.is_connected(G):
            G = nx.random_regular_graph(2*r, n, seed=rng.randrange(2**31))
        G.add_edge(*rng.choice(list(nx.non_edges(G))))
    assert critical(G, r)
    return canon(G)


def circuit_sample(r, typ, steps, rng):
    G = seed_circuit(r, typ, rng)
    for _ in range(steps):
        q = rng.randint(1, r)
        M = random_matching(G, q, rng)
        if M is None:
            continue
        used = {u for a in M for u in a}
        B = rng.sample(sorted(set(G)-used), r-q)
        G = pinch(G, r, M, B)
    return G


def exact_matching_cut_feasibility(E, copy_rows, r, node_limit=2000000):
    """Exact integer search for a matching satisfying all bad-copy inequalities.

    Returns ('infeasible', nodes, None), ('feasible', nodes, matching), or a
    node limit. An infeasible result certifies the finite copy family against
    EVERY matching of size at most r, without trusting MILP arithmetic.
    """
    m = len(E)
    conflicts = [sum(1 << j for j,b in enumerate(E) if set(a).intersection(b))
                 for a in E]
    rows = []
    for row in copy_rows:
        ones = sum(1 << j for j,w in enumerate(row) if w == 1)
        twos = sum(1 << j for j,w in enumerate(row) if w == 2)
        assert ones & twos == 0
        rows.append((ones,twos))
    nodes = 0
    class Limit(Exception): pass
    def search(chosen, available, remaining):
        nonlocal nodes
        nodes += 1
        if nodes > node_limit: raise Limit
        pending = []
        for ones,twos in rows:
            need = 2 - (chosen & ones).bit_count() - 2*(chosen & twos).bit_count()
            if need <= 0: continue
            a1, a2 = available & ones, available & twos
            options = a1 | a2
            minimum = 1 if need <= 1 or a2 else 2
            if minimum > remaining or a1.bit_count()+2*a2.bit_count() < need:
                return None
            pending.append((options.bit_count(), minimum, options, a2))
        if not pending: return chosen
        pending.sort(key=lambda x:(x[0],-x[1]))
        # Pairwise edge-disjoint unfinished constraints require separate choices.
        union = 0; lower = 0
        for _,cost,options,_ in pending:
            if not (options & union):
                lower += cost; union |= options
        if lower > remaining: return None
        _,_,options,twos = pending[0]
        # Partition solutions by their first selected edge of this unfinished row.
        ordered = []
        for bits in [twos, options & ~twos]:
            while bits:
                b=bits & -bits; bits-=b; ordered.append(b.bit_length()-1)
        avail = available
        for j in ordered:
            b = 1 << j
            result = search(chosen | b, avail & ~conflicts[j], remaining-1)
            if result is not None: return result
            avail &= ~b
        return None
    try:
        result = search(0,(1 << m)-1,r)
    except Limit:
        return 'node_limit',nodes,None
    if result is None: return 'infeasible',nodes,None
    M = [E[j] for j in range(m) if result >> j & 1]
    assert len(M) <= r and len({v for a in M for v in a}) == 2*len(M)
    assert all(sum(row[j] for j in range(m) if result >> j & 1) >= 2
               for row in copy_rows)
    return 'feasible',nodes,M


def adversarial_matching(G, T, r, max_cuts=300):
    """Finite cutting-plane search over ALL matchings of size <= r.

    For each actual copy f add 2*(internal marked edges) +
    (pendant marked edges) >= 2, exactly the condition for that copy to
    fail the permitted-edge rule. MILP infeasibility is independently audited
    by an exact integer matching search; a node limit is distinguished from
    an exact certificate. Positive witnesses use exact embedding backtracking.
    """
    E = [edge(*a) for a in G.edges()]
    eid = {a: j for j, a in enumerate(E)}
    m = len(E)
    rows, lbs, ubs = [], [], []
    copy_rows = []
    for v in G:
        rows.append([int(v in a) for a in E])
        lbs.append(-np.inf)
        ubs.append(1)
    rows.append([1]*m)
    lbs.append(0)
    ubs.append(r)
    for j in range(max_cuts):
        res = milp(np.zeros(m), integrality=np.ones(m),
                   bounds=Bounds(np.zeros(m), np.ones(m)),
                   constraints=LinearConstraint(np.array(rows, dtype=float),
                                                np.array(lbs), np.array(ubs)),
                   options={'time_limit': 20})
        if res.status == 2:
            exact,nodes,M = exact_matching_cut_feasibility(E,copy_rows,r)
            assert exact != 'feasible', ('MILP result contradicted by exact search',M)
            return {'status': 'exact_no_matching' if exact == 'infeasible' else 'milp_infeasible',
                    'cuts': j, 'exact_nodes': nodes}
        if res.x is None:
            return {'status': 'solver_limit', 'cuts': j}
        X = [int(round(x)) for x in res.x]
        assert all(abs(x-y) < 1e-5 for x, y in zip(res.x, X))
        assert sum(X) <= r
        M = [E[i] for i in range(m) if X[i]]
        assert len({v for a in M for v in a}) == 2*len(M)
        f = embedding(G, T, M)
        if f is None:
            return {'status': 'exact_obstruction', 'cuts': j, 'M': M}
        row = [0]*m
        for u, v in T.edges():
            row[eid[edge(f[u], f[v])]] = 1 if min(T.degree(u), T.degree(v)) == 1 else 2
        assert sum(a*b for a, b in zip(row, X)) < 2
        rows.append(row)
        copy_rows.append(row)
        lbs.append(2)
        ubs.append(np.inf)
    return {'status': 'cut_limit', 'cuts': max_cuts}


def selftest():
    rng = random.Random(73214)
    tests = 0
    atlas = [canon(G) for G in nx.graph_atlas_g() if len(G) >= 2]
    for _ in range(800):
        G = rng.choice(atlas)
        T = rng.choice(list(nx.nonisomorphic_trees(rng.randint(2, min(7, len(G))))))
        T = canon(T)
        got = embedding(G, T)
        ref = nx.algorithms.isomorphism.GraphMatcher(G, T).subgraph_is_monomorphic()
        assert (got is not None) == ref
        tests += 1
    for r in (1, 2):
        for G in atlas:
            if G.number_of_edges() == r*len(G)+1:
                assert critical(G, r) == critical_subsets(G, r)
                tests += 1
    # Exhaustive constrained embedding comparison for small hosts/trees.
    for _ in range(160):
        G = rng.choice(atlas)
        t = rng.randint(2, min(6, len(G)))
        T = canon(rng.choice(list(nx.nonisomorphic_trees(t))))
        M = random_matching(G, min(2, G.number_of_edges()), rng) or []
        mm = set(M)
        ref = False
        for g in nx.algorithms.isomorphism.GraphMatcher(G, T).subgraph_monomorphisms_iter():
            f = [next(v for v, u in g.items() if u == j) for j in range(t)]
            hit = [(u, v) for u, v in T.edges() if edge(f[u], f[v]) in mm]
            if len(hit) <= 1 and all(min(T.degree(u), T.degree(v)) == 1 for u, v in hit):
                ref = True
                break
        assert (embedding(G, T, M) is not None) == ref
        tests += 1
    for j in range(500):
        n=rng.randint(2,7)
        G=nx.gnp_random_graph(n,rng.random(),seed=rng.randrange(100000))
        E=list(G.edges()); r=rng.randint(0,3)
        rows=[[rng.choice([0,0,0,1,2]) for _ in E]
              for _ in range(rng.randint(0,10))]
        expected=False
        for q in range(r+1):
            for ids in it.combinations(range(len(E)),q):
                M=[E[i] for i in ids]
                if len({v for a in M for v in a})<2*q: continue
                if all(sum(row[i] for i in ids)>=2 for row in rows):
                    expected=True; break
            if expected: break
        status,_,_=exact_matching_cut_feasibility(E,rows,r)
        assert status != 'node_limit'
        assert (status=='feasible')==expected
        tests += 1
    print('selftest: independent comparisons passed:', tests,
          '(including 500 exact matching-cut/enumeration comparisons)', flush=True)


def resilience(samples=30):
    rng = random.Random(660381)
    stats = {'instances': 0, 'random_matchings': 0, 'exact_obstruction': 0,
             'milp_infeasible': 0, 'exact_no_matching': 0, 'solver_limit': 0, 'cut_limit': 0, 'cuts': 0}
    start = time.monotonic()
    for r in (2, 3, 4):
        ts = [canon(T) for T in nx.nonisomorphic_trees(2*r+2)
              if max(dict(T.degree()).values()) <= r]
        for j in range(samples):
            G = circuit_sample(r, j % 3, j % 13, rng)
            selected = ts if r <= 3 else rng.sample(ts, min(9, len(ts)))
            for T in selected:
                stats['instances'] += 1
                for _ in range(4):
                    M = random_matching(G, r, rng)
                    if M is None:
                        continue
                    assert embedding(G, T, M) is not None, (r, list(G.edges()), list(T.edges()), M)
                    stats['random_matchings'] += 1
                # Search the complete matching choice space on selected instances.
                if j % 5 == 0:
                    out = adversarial_matching(G, T, r)
                    stats[out['status']] += 1
                    stats['cuts'] += out['cuts']
                    if out['status'] == 'exact_obstruction':
                        payload = dict(r=r, G=list(G.edges()), T=list(T.edges()), result=out)
                        (HERE/'GlobalClosingResilienceObstruction.json').write_text(json.dumps(payload))
                        print('OBSTRUCTION', payload, flush=True)
                        return
            if j % 5 == 0:
                print('resilience checkpoint', r, j, stats,
                      'seconds', round(time.monotonic()-start, 2), flush=True)
    print('resilience result', stats, 'seconds', round(time.monotonic()-start, 2), flush=True)


def forest_candidates(e):
    """All forest isomorphism types with e edges, no isolates, >=2 components."""
    trees = [(j-1, canon(T)) for j in range(2, e+1) for T in nx.nonisomorphic_trees(j)]
    def rec(left, low, pieces):
        if left == 0:
            if len(pieces) >= 2:
                yield canon(nx.disjoint_union_all(pieces))
            return
        for i in range(low, len(trees)):
            a, T = trees[i]
            if a <= left:
                yield from rec(left-a, i, pieces+[T])
    yield from rec(e, 0, [])


def forest_discount():
    """Probe whether delta=e-1 can replace delta=e in unrestricted forest packing."""
    rng = random.Random(454543)
    tests = 0
    for e in range(3, 8):
        fs = list(forest_candidates(e))
        hosts = [canon(G) for G in nx.graph_atlas_g()
                 if len(G) >= e+2 and min(dict(G.degree()).values(), default=0) >= e-1]
        for n in range(e+2, 2*e+4):
            for _ in range(35):
                H = nx.gnp_random_graph(n, max(.3, e/(n-1)), seed=rng.randrange(2**31))
                while min(dict(H.degree()).values(), default=0) < e-1:
                    u = min(H, key=H.degree)
                    cand = list(set(H)-{u}-set(H[u]))
                    H.add_edge(u, rng.choice(cand))
                hosts.append(canon(H))
        hosts += [nx.disjoint_union(nx.complete_graph(e), nx.complete_graph(e))]
        for G in hosts:
            for F in fs:
                if len(F) > len(G):
                    continue
                if all(d == 1 for _, d in F.degree()):
                    continue  # the known odd two-clique matching exception
                tests += 1
                if embedding(G, F) is None:
                    out = {'e': e, 'G': list(G.edges()), 'F': list(F.edges()),
                           'nG': len(G), 'nF': len(F)}
                    print('forest discount obstruction', out, flush=True)
                    (HERE/'GlobalClosingForestObstruction.json').write_text(json.dumps(out))
                    return
        print('forest discount checkpoint', e, 'forests', len(fs), 'hosts', len(hosts),
              'tests', tests, flush=True)
    print('forest discount no unlisted obstruction in', tests, 'tests', flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('mode', choices=['selftest', 'resilience', 'forest'])
    p.add_argument('--samples', type=int, default=30)
    args = p.parse_args()
    if args.mode == 'selftest': selftest()
    elif args.mode == 'resilience': resilience(args.samples)
    else: forest_discount()
