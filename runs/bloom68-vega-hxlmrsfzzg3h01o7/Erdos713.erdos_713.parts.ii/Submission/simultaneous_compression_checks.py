"""Exact finite checks for simultaneous-compression working lemmas.

These are not a proof or a counterexample to Erdos 713. No floating-point
search for the extremal exponent is performed. The new lemmas' mathematical
proofs, rather than these finite checks, justify their general statements.
"""
from itertools import combinations, permutations


def all_matchings(vertices):
    if not vertices:
        yield ()
        return
    u, *rest = vertices
    yield from all_matchings(rest)
    for i, v in enumerate(rest):
        remainder = rest[:i] + rest[i + 1:]
        for matching in all_matchings(remainder):
            yield ((u, v),) + matching


def cycle_masks(n, length, edge_index):
    if n < length:
        return ()
    masks = set()
    for vertices in combinations(range(n), length):
        first = vertices[0]
        for rest in permutations(vertices[1:]):
            if rest[0] > rest[-1]:
                continue
            order = (first,) + rest
            mask = 0
            for i, u in enumerate(order):
                v = order[(i + 1) % length]
                mask |= 1 << edge_index[tuple(sorted((u, v)))]
            masks.add(mask)
    return tuple(masks)


def compress(edges, matching):
    image = {v: u for u, v in matching}
    quotient = set()
    for u, v in edges:
        u, v = image.get(u, u), image.get(v, v)
        if u != v:
            quotient.add(tuple(sorted((u, v))))
    return quotient


def has_cycle(edges, length):
    vertices = sorted({v for edge in edges for v in edge})
    if len(vertices) < length:
        return False
    adjacency = {v: set() for v in vertices}
    for u, v in edges:
        adjacency[u].add(v)
        adjacency[v].add(u)

    def walk(start, path):
        if len(path) == length:
            return start in adjacency[path[-1]]
        return any(
            walk(start, path + [v])
            for v in adjacency[path[-1]]
            if v > start and v not in path
        )

    return any(walk(v, [v]) for v in vertices)


def check_native_bound(n=6):
    possible_edges = tuple(combinations(range(n), 2))
    edge_index = {edge: i for i, edge in enumerate(possible_edges)}
    matching_data = []
    for matching in all_matchings(list(range(n))):
        mask = sum(1 << edge_index[edge] for edge in matching)
        matching_data.append((matching, mask))
    cycles = {r: cycle_masks(n, 2 * r, edge_index) for r in (2, 3, 4)}
    counts = {r: 0 for r in cycles}
    for mask in range(1 << len(possible_edges)):
        free_r = [r for r, cms in cycles.items()
                  if not any(mask & cm == cm for cm in cms)]
        if not free_r:
            continue
        edges = {edge for i, edge in enumerate(possible_edges)
                 if mask & (1 << i)}
        adjacency = [0] * n
        for u, v in edges:
            adjacency[u] |= 1 << v
            adjacency[v] |= 1 << u
        for matching, mmask in matching_data:
            if mask & mmask != mmask:
                continue
            k = len(matching)
            loss = len(edges) - len(compress(edges, matching))
            single_losses = sum(
                1 + (adjacency[u] & adjacency[v]).bit_count()
                for u, v in matching
            )
            for r in free_r:
                assert 2 * loss <= 2 * single_losses + (r - 2) * k, (
                    n, r, edges, matching, loss, single_losses
                )
                counts[r] += 1
    return counts


def check_mixed_obligation_examples():
    for r in (2, 3, 4):
        n = 2 * r + 2
        edges = {tuple(sorted((i, (i + 1) % n))) for i in range(n)}
        matching = ((0, 1), (3, 4))
        assert not has_cycle(edges, 2 * r)
        for pair in matching:
            assert not has_cycle(compress(edges, (pair,)), 2 * r)
        quotient = compress(edges, matching)
        assert has_cycle(quotient, 2 * r)
        assert len(edges) - len(quotient) == 2
        print(f'C{n}: both single contractions C{2*r}-free; '
              f'simultaneous quotient contains C{2*r}')


if __name__ == '__main__':
    counts = check_native_bound()
    for r, count in counts.items():
        print(f'C{2*r}-free old-edge native-loss bound: '
              f'{count} graph/matching pairs checked exhaustively on 6 vertices')
    check_mixed_obligation_examples()
