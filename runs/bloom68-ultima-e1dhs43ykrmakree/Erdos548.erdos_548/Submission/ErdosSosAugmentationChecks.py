"""Exact finite checks of augmentation findings, NOT an Erdős--Sós proof.

Uses non-induced subgraph monomorphisms throughout.
Run: python3 Submission/ErdosSosAugmentationChecks.py
"""
from collections import Counter
from itertools import combinations, islice

import networkx as nx


def embeddings(host, tree):
    for inverse in nx.algorithms.isomorphism.GraphMatcher(
        host, tree
    ).subgraph_monomorphisms_iter():
        yield {t: h for h, t in inverse.items()}


def incident_margin(host, k, vertices):
    vertices = set(vertices)
    return 2 * sum(a in vertices or b in vertices for a, b in host.edges()) - (
        k - 1
    ) * len(vertices)


# 1. A genuinely branched version of the spider path-rerouting lemma is false.
# a,b are the only adjacent host vertices both of degree at least three.
# z has degree four, but all its neighbors have degree two.
a, b, x1, x2, y1, y2, z = range(7)
host = nx.Graph(
    [(a, b), (a, x1), (a, x2), (b, y1), (b, y2)]
    + [(z, v) for v in (x1, x2, y1, y2)]
)
tree = nx.Graph(
    [(a, b), (a, x1), (a, x2), (x2, z), (b, y1), (b, y2)]
)
assert nx.is_tree(tree)
all_embeddings = list(embeddings(host, tree))
support = {f[z] for f in all_embeddings}
assert len(all_embeddings) == 8 and support == {z}
colors = nx.bipartite.color(tree)
assert sum(colors[v] == colors[z] for v in tree) == 4
score = 2 * host.degree(z) - len(set(host[z]) & support)
assert score == 8 > len(tree) == 7
assert {f[z] for f in all_embeddings if f[a] == a} == {z}
print("Branch rerouting: 8 embeddings; designated majority-color leaf support {z}; 2d-d_S=8>7.")


# 2. Incidence density does not make bounded local embedding moves complete.
host = nx.complete_bipartite_graph(2, 7)
small = {0, 1}
partial = nx.path_graph(4)
states = sorted({tuple(f[i] for i in range(4)) for f in embeddings(host, partial)})
assert len(states) == 168
augmentable = {
    state for state in states if set(host[state[3]]) - set(state)
}
assert len(augmentable) == 84
state_graph = nx.Graph()
state_graph.add_nodes_from(states)
for i, state in enumerate(states):
    for other in states[i + 1 :]:
        changed = sum(x != y for x, y in zip(state, other))
        if changed <= 3:
            # A common fixed label determines the bipartition orientation.
            assert (state[0] in small) == (other[0] in small)
            assert (state in augmentable) == (other in augmentable)
        if changed == 1:
            state_graph.add_edge(state, other)
components = list(nx.connected_components(state_graph))
assert sorted(map(len, components)) == [42, 42, 42, 42]
assert sum(not (component & augmentable) for component in components) == 2
assert min(
    incident_margin(host, 4, subset)
    for size in range(1, 10)
    for subset in combinations(host, size)
) == 1
print("Local states in K2,7: 168 states, four 42-state components, two completely blocked.")
print("No move changing at most 3 labels crosses from a blocked to an augmentable state.")


# 3. The two-vertex pruning/extension construction is valid for arbitrary trees.
# This host has ONLY the smaller tree, one spare vertex, and a universal vertex;
# hence checking it also checks that the construction uses no extra host edges.
checks = 0
for k in range(2, 11):
    for tree in nx.nonisomorphic_trees(k + 1):
        paths = dict(nx.all_pairs_shortest_path(tree))
        diameter_path = max(
            (p for from_vertex in paths.values() for p in from_vertex.values()),
            key=len,
        )
        parent = diameter_path[1]
        sibling_leaves = [v for v in tree[parent] if tree.degree(v) == 1]
        if len(sibling_leaves) >= 2:
            removed = sibling_leaves[:2]
            mode = "cherry"
        else:
            assert tree.degree(parent) == 2
            removed = diameter_path[:2]
            mode = "pendant2"
        smaller = tree.copy()
        smaller.remove_nodes_from(removed)
        assert nx.is_tree(smaller) and len(smaller) == k - 1
        spare, universal = k + 1, k + 2
        host = smaller.copy()
        host.add_node(spare)
        host.add_edges_from((universal, v) for v in list(host))
        image = {v: v for v in smaller}
        if mode == "cherry":
            image[parent] = universal
            image[removed[0]] = parent
            image[removed[1]] = spare
        else:
            image[removed[0]] = spare
            image[removed[1]] = universal
        assert len(host) == k + 1
        assert len(set(image.values())) == len(tree)
        assert all(host.has_edge(image[v], image[w]) for v, w in tree.edges())
        checks += 1
assert checks == 434
print("Universal-vertex extension: explicit injections verified for 434 tree types, 2<=k<=10.")


# 4. One cannot replace 'universal' by 'degree >= k' in that particular
# two-vertex extension algorithm, even in a density-minimal host.
tree = nx.path_graph(7)
tree.add_edges_from([(2, 7), (4, 8)])
k = tree.number_of_edges()
assert k == 8
colors = nx.bipartite.color(tree)
classes = [{v for v in tree if colors[v] == i} for i in (0, 1)]
large_tree, small_tree = sorted(classes, key=len, reverse=True)
assert large_tree == {1, 3, 5, 7, 8}
assert small_tree == {0, 2, 4, 6}
cherry_parents = {
    p for p in tree if sum(tree.degree(v) == 1 for v in tree[p]) >= 2
}
pendant2_parents = {
    p for p in tree if tree.degree(p) == 2 and any(tree.degree(v) == 1 for v in tree[p])
}
assert not cherry_parents and pendant2_parents == {1, 5}
assert pendant2_parents <= large_tree
host = nx.complete_bipartite_graph(4, 29)
assert 2 * host.number_of_edges() - 7 * len(host) == 1
# Complete bipartite symmetry reduces ALL induced subsets/deleted subsets to
# 5*30 possible pairs of class cardinalities. This is not a sample.
for x in range(5):
    for y in range(30):
        if (x, y) != (4, 29):
            assert 2 * x * y <= 7 * (x + y)
        if x + y:
            incident = 4 * 29 - (4 - x) * (29 - y)
            assert 2 * incident > 7 * (x + y)
image = dict(zip(sorted(small_tree), range(4)))
image.update(zip(sorted(large_tree), range(4, 9)))
assert all(host.has_edge(image[v], image[w]) for v, w in tree.edges())
# An embedding sending either eligible parent into the four-vertex host class
# would send all FIVE vertices of large_tree into that class, impossibly.
assert len(large_tree) > 4
print("K4,29 is density-minimal for k=8; T embeds, but no eligible two-step parent can be high-degree.")


# 5. The exact Hall criterion for extending a FIXED leaf-deleted core.
def fixed_core_extension(host, tree, core_image):
    host = host.copy()
    tree = tree.copy()
    nx.set_node_attributes(host, {v: ("free",) for v in host}, "tag")
    nx.set_node_attributes(tree, {v: ("free",) for v in tree}, "tag")
    for t, h in core_image.items():
        host.nodes[h]["tag"] = ("core", t)
        tree.nodes[t]["tag"] = ("core", t)
    return nx.algorithms.isomorphism.GraphMatcher(
        host, tree, node_match=lambda a, b: a["tag"] == b["tag"]
    ).subgraph_is_monomorphic()


checks = 0
failures = 0
for host in nx.graph_atlas_g():
    if not (3 <= len(host) <= 6) or not nx.is_connected(host):
        continue
    for k in range(2, min(5, len(host) - 1) + 1):
        for tree in nx.nonisomorphic_trees(k + 1):
            leaves = {v for v in tree if tree.degree(v) == 1}
            core = tree.subgraph(set(tree) - leaves).copy()
            leaf_counts = Counter(next(iter(tree[v])) for v in leaves)
            parents = list(leaf_counts)
            for core_image in islice(embeddings(host, core), 3):
                used = set(core_image.values())
                hall_ok = True
                for size in range(1, len(parents) + 1):
                    for subset in combinations(parents, size):
                        available = set().union(
                            *(set(host[core_image[p]]) for p in subset)
                        ) - used
                        if len(available) < sum(leaf_counts[p] for p in subset):
                            hall_ok = False
                assert hall_ok == fixed_core_extension(host, tree, core_image)
                checks += 1
                failures += not hall_ok
print(f"Fixed-core Hall criterion: {checks} exact instances checked, including {failures} nonextendible cores.")


# The Hall obstruction from a bad fixed core is NOT already an incidence
# certificate. Here there are two leaf slots but only one available neighbor.
host = nx.complete_bipartite_graph(2, 7)
tree = nx.path_graph(5)
core_image = {1: 2, 2: 0, 3: 3}
assert all(host.has_edge(core_image[u], core_image[v]) for u, v in [(1, 2), (2, 3)])
assert not fixed_core_extension(host, tree, core_image)
parent_images = {2, 3}
assert (set(host[2]) | set(host[3])) - set(core_image.values()) == {1}
assert incident_margin(host, 4, parent_images) == 2 > 0
print("A Hall-deficient parent set in K2,7 has positive, not nonpositive, incidence surplus.")


# 6. The edge-splitting formulation is realized exactly in K2,7: scale by 9.
# Every edge gives 2/9 to its endpoint in the small class, 7/9 to the other.
host = nx.complete_bipartite_graph(2, 7)
loads_times_nine = {v: 0 for v in host}
for u, v in host.edges():
    for endpoint in (u, v):
        loads_times_nine[endpoint] += 2 if endpoint < 2 else 7
assert set(loads_times_nine.values()) == {14}
assert 2 * 14 > 3 * 9  # load 14/9 > (k-1)/2 = 3/2
print("Fractional orientation: every vertex in K2,7 has exact balanced load 14/9>3/2.")
print("All checks passed. None of these finite checks proves the unrestricted conjecture.")
