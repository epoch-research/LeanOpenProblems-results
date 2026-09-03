#!/usr/bin/env python3
"""Exact parity-kernel checks; no host-graph assumptions.

python3 Submission/TreeExactKernelChecks.py verify 12
python3 Submission/TreeExactKernelChecks.py exhaustive 22
python3 Submission/TreeExactKernelChecks.py structured
python3 Submission/TreeExactKernelChecks.py certificates 12
python3 Submission/TreeExactKernelChecks.py counterexample

A state is exact odd cardinality -> minimum connected core size.  Unlike the
old at-most-cost DP, no feasible odd cardinalities are discarded.
"""
import itertools
import random
import sys
import time
import networkx as nx


def exact_profile(T, root=0, rooted=False):
    """Minimum |R| for each exact odd-distance count, including R=V(T)."""
    n = len(T)
    assert set(T) == set(range(n))
    adj = [list(T[u]) for u in range(n)]
    parent = [-1] * n
    color = [0] * n
    order = [root]
    parent[root] = root
    for u in order:
        for v in adj[u]:
            if v != parent[u]:
                parent[v] = u
                color[v] = 1 - color[u]
                order.append(v)
    counts = [color.count(0), color.count(1)]
    a = [1] * n  # vertices with the same color as the subtree root
    b = [0] * n
    dp = [None] * n
    best = {}
    for u in reversed(order):
        D = {0: 1}
        for v in adj[u]:
            if parent[v] != u:
                continue
            E = dict(dp[v])
            E[a[v]] = 0  # drop all of this branch (dominates a nonempty core)
            F = {}
            for x, s in D.items():
                for y, t in E.items():
                    z, sz = x + y, s + t
                    if sz < F.get(z, n + 1):
                        F[z] = sz
            D = F
            a[u] += b[v]
            b[u] += a[v]
        dp[u] = D
        up = counts[1 - color[u]] - b[u]
        if not rooted or u == root:
            for x, s in D.items():
                z = x + up
                if s < best.get(z, n + 1):
                    best[z] = s
    return best, counts


def eligible(T):
    P, counts = exact_profile(T)
    n = len(T)
    return P, range(1, min(min(counts), (n - 1) // 2) + 1)


def verify_certificate(T, R, c, root=None):
    R = set(R)
    assert R and nx.is_connected(T.subgraph(R))
    D = nx.multi_source_dijkstra_path_length(T, R, weight=None)
    U = {v for v in T if D[v] % 2}
    W = set(T) - R - U
    assert len(U) == c and len(W) >= c, (list(T.edges()), R, c, U, W)
    assert all(not (u in U and v in U) for u, v in T.edges())
    assert all(set(T[w]) <= U for w in W)
    assert sum(T.degree(u) for u in U) == len(U) + len(W)
    if root is not None:
        assert root in R
    return U, W


def direct_profiles(T):
    """Independent subset enumeration and BFS; checks every connected R."""
    n = len(T)
    adj = [sum(1 << v for v in T[u]) for u in range(n)]
    full = (1 << n) - 1
    P = {}
    Pr = [{} for _ in T]
    excess = sum(max(T.degree(v) - 2, 0) for v in T)
    leaves = sum(T.degree(v) == 1 for v in T)
    assert excess + 2 == leaves

    def neighbors(F):
        A = 0
        while F:
            bit = F & -F
            F -= bit
            A |= adj[bit.bit_length() - 1]
        return A

    for R in range(1, full + 1):
        seen = R & -R
        front = seen
        while front:
            front = neighbors(front) & R & ~seen
            seen |= front
        if seen != R:
            continue
        seen = front = R
        U = parity = 0
        while seen != full:
            front = neighbors(front) & ~seen
            seen |= front
            parity ^= 1
            if parity:
                U |= front
        W = full & ~(R | U)
        c, s = U.bit_count(), R.bit_count()
        P[c] = min(s, P.get(c, n + 1))
        for r in T:
            if R >> r & 1:
                Pr[r][c] = min(s, Pr[r].get(c, n + 1))
        assert all(not (adj[v] & U) for v in T if U >> v & 1)
        assert all(not (adj[v] & ~U) for v in T if W >> v & 1)
        removed = n - s
        assert sum(T.degree(v) for v in T if U >> v & 1) == removed
        assert removed <= c * max(dict(T.degree()).values())
        assert removed <= 2 * c + excess
    return P, Pr


def verify(maxn):
    start = time.time()
    trees = roots = 0
    for n in range(3, maxn + 1):
        for T in nx.nonisomorphic_trees(n):
            P, Pr = direct_profiles(T)
            Q, _ = exact_profile(T)
            assert P == Q
            for r in T:
                Q, counts = exact_profile(T, r, True)
                assert Pr[r] == Q
                assert set(Q) == set(range(max(Q) + 1))
                assert max(Q) >= max(counts[0] - 1, counts[1])
                roots += 1
            trees += 1
        print('DIRECT/DP VERIFIED n', n, 'trees', trees, 'root profiles', roots,
              'seconds', round(time.time() - start, 3), flush=True)


def exhaustive(maxn):
    start = time.time()
    trees = parameters = 0
    for n in range(3, maxn + 1):
        for T in nx.nonisomorphic_trees(n):
            P, cs = eligible(T)
            for c in cs:
                parameters += 1
                assert P.get(c, n + 1) <= n - 2 * c, (n, c, list(T.edges()), P)
            trees += 1
        print('EXACT UNROOTED PASS n', n, 'trees', trees, 'parameters', parameters,
              'seconds', round(time.time() - start, 3), flush=True)


def classes(T):
    coloring = nx.bipartite.color(T)
    A = {v for v in T if coloring[v] == 0}
    B = set(T) - A
    if len(A) > len(B):
        A, B = B, A
    return A, B


def leafless_small_core(T, A, c, r):
    """The paper construction: connected X in the half-square on A."""
    a0 = r if r in A else next(iter(T[r]))
    order = [a0]
    seen = {a0}
    for u in order:
        for w in T[u]:
            for v in T[w]:
                if v not in seen:
                    seen.add(v)
                    order.append(v)
    X = set(order[:len(A) - c])
    return X | {w for x in X for w in T[x]}


def two_kernel(T):
    H = T.subgraph([v for v in T if T.degree(v) > 1])
    assert len(H) >= 2
    s, t = [v for v in H if H.degree(v) == 1][:2]
    if len(H) >= 3:
        removed = {s, t} | {v for u in [s, t] for v in T[u] if T.degree(v) == 1}
        return set(T) - removed
    Ls = {v for v in T[s] if T.degree(v) == 1}
    Lt = {v for v in T[t] if T.degree(v) == 1}
    if len(Ls) < 2:
        s, t, Ls, Lt = t, s, Lt, Ls
    assert len(Ls) >= 2 and Lt
    return {t} | (Lt - {next(iter(Lt))})


def certificates(maxn):
    # Rooted obstruction: 0-1-2-3, two leaves at each endpoint.
    T = nx.Graph([(0, 1), (1, 2), (2, 3), (0, 4), (0, 5), (3, 6), (3, 7)])
    P, C = exact_profile(T, 1, True)
    assert C == [4, 4] and P[3] == 3 > 8 - 2 * 3
    values = []
    for R in [{1}, {0, 1}, {1, 2}]:
        D = nx.multi_source_dijkstra_path_length(T, R, weight=None)
        values.append(sum(d % 2 for d in D.values()))
    assert values == [4, 5, 2]
    U, W = verify_certificate(T, {0, 4}, 3)
    assert U == {1, 3, 5} and W == {2, 6, 7}
    print('ROOTED COUNTER VERIFIED: n=8,c=3,r=1; possible small-core costs', values,
          '; unrooted R={0,4},U={1,3,5},W={2,6,7}.', flush=True)
    count = 0
    for n in range(3, maxn + 1):
        for T in nx.nonisomorphic_trees(n):
            A, B = classes(T)
            m, delta = len(A), len(B) - len(A)
            if m < len(B):
                verify_certificate(T, {next(iter(B))}, m)
                count += 1
            if m >= 2:
                x = min(A, key=T.degree)
                assert T.degree(x) <= delta + 1
                verify_certificate(T, {x} | set(T[x]), m - 1)
                count += 1
            if n >= 5 and m >= 2:
                verify_certificate(T, two_kernel(T), 2)
                count += 1
            if all(T.degree(x) >= 2 for x in A):
                for c in range(1, m):
                    for r in T:
                        R = leafless_small_core(T, A, c, r)
                        verify_certificate(T, R, c, r)
                        count += 1
        print('POSITIVE CONSTRUCTIONS PASS n', n, 'certificates', count, flush=True)


def base_families():
    for n in [3, 4, 5, 8, 15, 32, 65, 100, 201]:
        yield 'star', nx.star_graph(n - 1)
    for arms in [2, 3, 4, 7, 16]:
        for length in [1, 2, 3, 4, 7, 12]:
            T = nx.empty_graph(1)
            for _ in range(arms):
                u = 0
                for __ in range(length):
                    v = len(T)
                    T.add_edge(u, v)
                    u = v
            yield 'uniform spider', T
    for r in [2, 3, 4]:
        for h in range(1, 6 if r == 2 else 5):
            yield 'full r-ary', nx.balanced_tree(r, h)
    for length in [2, 3, 5, 10, 20, 35]:
        for pattern in [(1,), (2,), (3,), (1, 4), (0, 3, 0, 0, 5), (7, 0, 0, 1)]:
            T = nx.path_graph(length)
            for u in range(length):
                for _ in range(pattern[u % len(pattern)]):
                    T.add_edge(u, len(T))
            yield 'caterpillar', T
            for subdiv in [1, 2, 3]:
                S = nx.Graph()
                S.add_nodes_from(T)
                for u, v in T.edges():
                    w = u
                    for _ in range(subdiv):
                        z = len(S)
                        S.add_edge(w, z)
                        w = z
                    S.add_edge(w, v)
                yield 'subdivided caterpillar', S
    rng = random.Random(31082026)
    for n in [20, 31, 50, 75, 100, 150, 250]:
        for _ in range(10):
            yield 'Pruefer', nx.random_tree(n, seed=rng.randrange(1 << 30))


def custom_families():
    for levels in itertools.chain(itertools.product(range(1, 11), repeat=2),
                                 itertools.product(range(1, 9), repeat=3)):
        T = nx.empty_graph(1)
        last = [0]
        for l in levels:
            new = []
            for u in last:
                for _ in range(l):
                    v = len(T)
                    T.add_edge(u, v)
                    new.append(v)
            last = new
        yield ('spherical', levels), T
    for a, b, length in itertools.product(range(1, 16), range(1, 16), range(1, 10)):
        T = nx.path_graph(length + 1)
        for _ in range(a):
            T.add_edge(0, len(T))
        for _ in range(b):
            T.add_edge(length, len(T))
        yield ('double-broom', a, b, length), T
    rng = random.Random(184971)
    for i in range(10000):
        n = rng.randrange(3, 151)
        T = nx.random_tree(n, seed=rng.randrange(1 << 32))
        mode = i % 6
        if mode == 0:
            for u in list(T):
                if T.degree(u) == 1:
                    for _ in range(rng.randrange(15)):
                        T.add_edge(u, len(T))
        elif mode == 1:
            for u in list(T):
                for _ in range(rng.randrange(5)):
                    T.add_edge(u, len(T))
        elif mode == 2:
            S = nx.empty_graph(n)
            for u, v in T.edges():
                for _ in range(rng.randrange(4)):
                    w = len(S)
                    S.add_edge(u, w)
                    u = w
                S.add_edge(u, v)
            T = S
        elif mode == 3:
            T = nx.empty_graph(n)
            for v in range(1, n):
                T.add_edge(v, rng.randrange(v))
        elif mode == 4:
            T = nx.path_graph(n)
            for u in list(T):
                for _ in range(rng.randrange(12)):
                    T.add_edge(u, len(T))
        yield ('random', i, mode), T


def structured():
    start = time.time()
    count = checks = maxn = 0
    for name, T in itertools.chain(base_families(), custom_families()):
        T = nx.convert_node_labels_to_integers(T)
        P, cs = eligible(T)
        n = len(T)
        for c in cs:
            checks += 1
            assert P.get(c, n + 1) <= n - 2 * c, (name, n, c, list(T.edges()))
        count += 1
        maxn = max(maxn, n)
        if count % 1000 == 0:
            print('STRUCTURED progress', count, checks, maxn,
                  round(time.time() - start, 3), flush=True)
    print('STRUCTURED EXACT PASS', count, 'trees', checks, 'parameters',
          'max order', maxn, 'seconds', round(time.time() - start, 3), flush=True)


def double_cherry_star(d):
    """Two adjacent hubs, each with d supports carrying two leaves."""
    T = nx.path_graph(2)
    for hub in [0, 1]:
        for _ in range(d):
            support = len(T)
            T.add_edge(hub, support)
            T.add_edge(support, len(T))
            T.add_edge(support, len(T))
    return T


def double_cherry_profile(d):
    """Closed form from classifying cores by the number of retained hubs."""
    m = 3 * d + 1
    P = {}
    for t in range(-d, m + 1):
        candidates = []
        if t in [0, 1, 2]:
            candidates.append(t + 1)  # core lies in a single cherry
        if -d <= t <= d:
            candidates.append(1 - t if t <= 0 else 1 + 3 * t)
        if 1 - d <= t <= m:
            candidates.append(d + 3 - t if t <= d + 1 else 3 * t - 3 * d - 1)
        assert candidates
        P[m - t] = min(candidates)
    return P


def small_connected_cores(T, bound):
    """Independent exhaustive generation: every connected set up to bound."""
    previous = {frozenset([v]) for v in T}
    for size in range(1, bound + 1):
        yield from previous
        if size == bound:
            break
        following = set()
        for R in previous:
            boundary = {v for u in R for v in T[u]} - R
            for v in boundary:
                following.add(R | {v})
        previous = following


def counterexample():
    T = double_cherry_star(7)
    P, C = exact_profile(T)
    assert nx.is_tree(T) and len(T) == 44 and T.number_of_edges() == 43
    assert C == [22, 22] and max(dict(T.degree()).values()) == 8
    assert P[19] == 7 and 44 - 2 * 19 == 6
    spectrum = set()
    counts = [0] * 7
    for R in small_connected_cores(T, 6):
        assert R and nx.is_connected(T.subgraph(R))
        distances = nx.multi_source_dijkstra_path_length(T, R, weight=None)
        odd = sum(v % 2 for v in distances.values())
        spectrum.add(odd)
        counts[len(R)] += 1
        assert odd != 19
    assert spectrum == set(range(13, 19)) | set(range(20, 28))
    print('UNROOTED COUNTEREXAMPLE VERIFIED: n=44,k=43,classes=22+22,c=19,Delta=8.')
    print('Complete direct enumeration of connected cores of size <=6:', counts[1:],
          'total', sum(counts), '; odd spectrum', sorted(spectrum))
    print('Exact DP minimum core size for odd=19:', P[19], '; required at most 6.')
    # Original at-most lemma is sharp here at odd cardinality 18.
    R = {0, 1, 2, 5, 8, 11}
    U, W = verify_certificate(T, R, 18)
    assert len(U) == 18 and len(W) == 20 and len(U) + len(W) == 38
    print('At-most certificate R=', sorted(R), 'has |U|=18, |W|=20, removed=38.')
    checks = 0
    for d in range(1, 101):
        T = double_cherry_star(d)
        Q, C = exact_profile(T)
        assert C == [3 * d + 1, 3 * d + 1]
        assert Q == double_cherry_profile(d)
        good = {c for c in range(1, 3 * d + 1) if Q[c] <= len(T) - 2 * c}
        assert good == set(range(1, 8 * d // 3 + 1)) | {3 * d - 1, 3 * d}
        if d >= 7:
            c = 3 * d - 2
            best = max(q for q in Q if q <= c and Q[q] <= 6)
            assert best == 2 * d + 4 and c - best == d - 6
        checks += len(Q)
    print('FULL CLOSED-FORM PROFILES VERIFIED for d=1..100:', checks,
          'exact-cardinality states; max order 602.')
    print('Good admissible c for T_d: [1,floor(8*d/3)] union {3*d-1,3*d}.')
    print('At c=3*d-2 (d>=7), best odd<=c under removal>=2*c is 2*d+4; deficit=d-6=Delta-7.')


if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'certificates'
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 12
    if mode == 'verify':
        verify(n)
    elif mode == 'exhaustive':
        exhaustive(n)
    elif mode == 'structured':
        structured()
    elif mode == 'certificates':
        certificates(n)
    elif mode == 'counterexample':
        counterexample()
    else:
        raise SystemExit('Unknown mode ' + mode)
