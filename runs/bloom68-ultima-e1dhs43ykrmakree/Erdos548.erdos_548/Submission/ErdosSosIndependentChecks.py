"""Finite checks of specific Erdős–Sós reductions, not a proof of the conjecture.

Uses non-induced subgraph monomorphisms. Run with Python 3 and NetworkX.
"""
from collections import Counter
from itertools import combinations

import networkx as nx


def contains(host, tree):
    return nx.algorithms.isomorphism.GraphMatcher(
        host, tree
    ).subgraph_is_monomorphic()


def incident_margin(host, k, vertices):
    vertices = set(vertices)
    incident = sum(u in vertices or v in vertices for u, v in host.edges())
    return 2 * incident - (k - 1) * len(vertices)


# Minimum degree ceil(k/2) and maximum degree k alone do not suffice.
host = nx.disjoint_union(nx.complete_graph(3), nx.complete_graph(3))
host.add_edges_from((6, v) for v in range(6))
tree = nx.Graph([(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (3, 6)])
assert nx.is_tree(tree) and tree.number_of_edges() == 6
assert min(dict(host.degree()).values()) == 3
assert max(dict(host.degree()).values()) == 6
assert not contains(host, tree)
print("Verified: two K4s sharing a vertex omit the subdivided claw.")

# Even a density-minimal host need not embed a given root at a high-degree vertex.
host = nx.complete_bipartite_graph(2, 7)
tree = nx.Graph([(0, 1), (0, 2), (1, 3), (2, 4)])
root_images = Counter()
for embedding in nx.algorithms.isomorphism.GraphMatcher(
    host, tree
).subgraph_monomorphisms_iter():
    root_images[next(v for v in embedding if embedding[v] == 0)] += 1
assert root_images == Counter({v: 60 for v in range(2, 9)})
assert min(
    incident_margin(host, 4, subset)
    for size in range(1, 10)
    for subset in combinations(host, size)
) == 1
print("Verified: K2,7 has 420 labelled P5s, all centered in its degree-2 part.")
print("Verified: every nonempty subset of K2,7 has positive incidence surplus.")

# A bipartite reduction cannot preserve the target density in general.
host = nx.Graph([(0, 1), (1, 2), (2, 0), (0, 3), (3, 4), (4, 0)])
assert host.number_of_edges() > host.number_of_nodes()
edges = list(host.edges())
for mask in range(1 << len(edges)):
    subgraph = nx.Graph()
    subgraph.add_nodes_from(host)
    subgraph.add_edges_from(e for i, e in enumerate(edges) if (mask >> i) & 1)
    if nx.is_bipartite(subgraph):
        assert nx.is_forest(subgraph)
print("Verified: all bipartite subgraphs of the two-triangle bowtie are forests.")

# Exhaustive small checks of the asymmetric bipartite-core extraction.
checks = 0
for host in nx.graph_atlas_g():
    if not len(host) or not nx.is_bipartite(host):
        continue
    coloring = nx.bipartite.color(host)
    left = {v for v in host if coloring[v] == 0}
    right = set(host) - left
    if len(left) < len(right):
        left, right = right, left
    for a in range(1, 5):
        for b in range(a, 7):
            if 2 * host.number_of_edges() <= (a + b - 2) * len(host):
                continue
            core = host.copy()
            while True:
                vertex = next(
                    (v for v in core if core.degree[v] < (a if v in left else b)),
                    None,
                )
                if vertex is None:
                    break
                core.remove_node(vertex)
            assert core.number_of_edges() > 0
            assert all(core.degree[v] >= (a if v in left else b) for v in core)
            checks += 1
assert checks == 332
print(f"Verified {checks} asymmetric bipartite-core instances.")
