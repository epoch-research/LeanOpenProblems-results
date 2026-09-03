#!/usr/bin/env python3
"""Finite checks for CubeGlobalHallReduction.md; not a Ramsey proof.

No dependency beyond the Python standard library.  The abstract matching
checks are exhaustive for all feasible list systems with 1 <= m <= 3 and
m <= a <= 4, all nonempty moving-label sets, and all root red neighborhoods.
"""
from itertools import permutations, product
from math import comb
from random import Random


def subsets(mask):
    sub = mask
    while True:
        yield sub
        if not sub:
            break
        sub = (sub - 1) & mask


def union_domains(domains, labels):
    result = 0
    for i, d in enumerate(domains):
        if labels >> i & 1:
            result |= d
    return result


def matching_rank(domains, allowed):
    # Enumerate the reachable used-vertex sets, allowing each label to be skipped.
    states = {0}
    for d in domains:
        nxt = set(states)
        for used in states:
            free = d & allowed & ~used
            while free:
                bit = free & -free
                free -= bit
                nxt.add(used | bit)
        states = nxt
    return max(s.bit_count() for s in states)


def matching_assignments(domains, a):
    for assignment in permutations(range(a), len(domains)):
        if all(domains[i] >> v & 1 for i, v in enumerate(assignment)):
            yield assignment


def image_mask(assignment, labels):
    return sum(1 << assignment[i] for i in range(len(assignment))
               if labels >> i & 1)


def check_abstract_systems():
    systems = root_tests = base_tests = 0
    for m in range(1, 4):
        all_labels = (1 << m) - 1
        for a in range(m, 5):
            ground = (1 << a) - 1
            masks = range(1 << a)
            case_systems = 0
            for domains in product(masks, repeat=m):
                assignments = list(matching_assignments(domains, a))
                if not assignments:
                    continue
                systems += 1
                case_systems += 1
                unions = [union_domains(domains, s) for s in range(1 << m)]
                slack = [unions[s].bit_count() - s.bit_count()
                         for s in range(1 << m)]
                assert min(slack) == 0  # Hall, including the empty set.
                for moving in range(1, 1 << m):
                    frozen = all_labels ^ moving
                    r = moving.bit_count()
                    d_moving = [domains[i] for i in range(m) if moving >> i & 1]
                    d_frozen = [domains[i] for i in range(m) if frozen >> i & 1]
                    rank1 = [matching_rank(d_moving, s) for s in masks]
                    rank0 = [matching_rank(d_frozen, s) for s in masks]
                    rank2 = [min(r, s.bit_count() - (m-r) + rank0[ground ^ s])
                             for s in masks]
                    assert rank1[ground] == rank2[ground] == r
                    # Direct interpretation of reserve independence and its rank.
                    reserve_independent = [s for s in masks
                                           if s.bit_count() <= r
                                           and rank0[ground ^ s] == m-r]
                    for s in masks:
                        direct_rank = max(t.bit_count() for t in reserve_independent
                                          if t & ~s == 0)
                        assert rank2[s] == direct_rank
                    # Common bases are precisely the moving images in ALL full matchings.
                    common_bases = {s for s in masks if s.bit_count() == r
                                    and rank1[s] == rank2[s] == r}
                    actual_images = {image_mask(f, moving) for f in assignments}
                    assert common_bases == actual_images
                    base_tests += 1
                    # A large uniform restriction of the reserve matroid.
                    free_pool = ground ^ image_mask(assignments[0], frozen)
                    assert free_pool.bit_count() == a-m+r
                    for s in subsets(free_pool):
                        assert rank2[s] == min(r, s.bit_count())
                    flats1 = [s for s in masks if all(
                        rank1[s | (1 << v)] > rank1[s]
                        for v in range(a) if not s >> v & 1)]
                    flats2 = [s for s in masks if all(
                        rank2[s | (1 << v)] > rank2[s]
                        for v in range(a) if not s >> v & 1)]
                    flat_pairs = [(f1, f2) for f1 in flats1 for f2 in flats2
                                  if rank1[f1] + rank2[f2] < r]
                    count_bound = sum(comb(2*a, j) for j in range(r))
                    assert len(flat_pairs) <= count_bound
                    for f2 in flats2:
                        if rank2[f2] < r:
                            assert (f2 & free_pool).bit_count() <= rank2[f2]
                    for red in masks:
                        root_tests += 1
                        extends = any(s & ~red == 0 for s in common_bases)
                        d_new = [d & red if moving >> i & 1 else d
                                 for i, d in enumerate(domains)]
                        assert extends == (matching_rank(d_new, ground) == m)
                        minmax_rank = min(rank1[s] + rank2[red ^ s]
                                          for s in subsets(red))
                        assert extends == (minmax_rank == r)
                        flat_failure = any(red & ~(f1 | f2) == 0
                                           for f1, f2 in flat_pairs)
                        assert flat_failure == (not extends)
                        has_hall_certificate = False
                        for p in subsets(frozen):
                            for t in subsets(moving):
                                if not t:
                                    continue
                                reservoir = unions[t] & ~unions[p]
                                red_count = (red & reservoir).bit_count()
                                if slack[p] + red_count >= t.bit_count():
                                    continue
                                has_hall_certificate = True
                                assert 0 <= slack[p] <= t.bit_count()-1
                                assert reservoir.bit_count() == (
                                    t.bit_count() - slack[p] + slack[p | t])
                                blue_count = (reservoir & ~red).bit_count()
                                assert blue_count >= slack[p | t] + 1
                                # This is the direct Hall proof of the rank dual.
                                assert rank2[unions[p]] <= slack[p]
                                s = red & ~unions[p]
                                assert rank1[s] + rank2[red & unions[p]] < r
                        assert has_hall_certificate == (not extends)
            print(f"Abstract systems m={m}, a={a}: {case_systems} feasible systems")
    print(f"TOTAL: {systems} list systems; {base_tests} common-base identities; "
          f"{root_tests} root-neighborhood tests")


def cube(n):
    even = [x for x in range(1 << n) if x.bit_count() % 2 == 0]
    odd = [x for x in range(1 << n) if x.bit_count() % 2 == 1]
    nb = {x: {x ^ (1 << i) for i in range(n)} for x in range(1 << n)}
    return even, odd, nb


def check_cube_balls():
    tests = 0
    for n in range(1, 13):
        even, odd, nb = cube(n)
        y = odd[0]
        for s in range(n // 2 + 1):
            z = {v for v in odd if (v ^ y).bit_count() <= 2*s}
            u = set().union(*(nb[v] for v in z))
            expected_u = {v for v in even if (v ^ y).bit_count() <= 2*s+1}
            assert u == expected_u
            assert len(z) == sum(comb(n, 2*j) for j in range(s+1) if 2*j <= n)
            assert len(u) == sum(comb(n, 2*j+1) for j in range(s+1) if 2*j+1 <= n)
            surplus = comb(n-1, 2*s+1) if 2*s+1 <= n-1 else 0
            assert len(u)-len(z) == surplus
            for x in u:
                d = (x ^ y).bit_count()
                if d <= 2*s-1:
                    assert nb[x] <= z
                else:
                    assert d == 2*s+1
                    assert len(nb[x] - z) == n-2*s-1
            tests += 1
    print(f"Cube-ball identities: {tests} (n,s) pairs through n=12")


def check_batch_reconfigurations():
    rng = Random(1812026)
    tests = 0
    # Larger list systems are checked by independent matching computations.
    for n in (2, 3, 4):
        xlabels, ylabels, nb = cube(n)
        m = len(xlabels)
        a = m + 2
        b = m + 1
        ground = (1 << a) - 1
        for _ in range(180):
            red = [[rng.random() < .72 for _ in range(b)] for _ in range(a)]
            j = set(rng.sample(ylabels, rng.randrange(m+1)))
            g = dict(zip(j, rng.sample(range(b), len(j))))
            def domains(frozen_g, added_h=None):
                assigned = dict(frozen_g)
                if added_h:
                    assigned.update(added_h)
                return [sum(1 << v for v in range(a)
                            if all(red[v][assigned[y]]
                                   for y in nb[x] if y in assigned))
                        for x in xlabels]
            initial = domains(g)
            if matching_rank(initial, ground) < m:
                continue
            j0 = {y for y in j if rng.random() < .55}
            frozen_g = {y: g[y] for y in j0}
            available_labels = sorted(set(ylabels) - j0)
            if not available_labels:
                continue
            z = set(rng.sample(available_labels, rng.randrange(1, len(available_labels)+1)))
            available_host = sorted(set(range(b)) - set(frozen_g.values()))
            h = dict(zip(z, rng.sample(available_host, len(z))))
            base = domains(frozen_g)
            new = domains(frozen_g, h)
            moving = {x for y in z for x in nb[y]}
            r = len(moving)
            frozen_indices = [i for i, x in enumerate(xlabels) if x not in moving]
            moving_indices = [i for i, x in enumerate(xlabels) if x in moving]
            assert all(new[i] == base[i] for i in frozen_indices)
            dm = [new[i] for i in moving_indices]
            df = [base[i] for i in frozen_indices]
            extends = matching_rank(new, ground) == m
            common_base = False
            for s in range(1 << a):
                if s.bit_count() != r:
                    continue
                if matching_rank(dm, s) == r and matching_rank(df, ground ^ s) == m-r:
                    common_base = True
                    break
            assert extends == common_base
            if not extends:
                # Direct Hall witness yields the dual-rank certificate.
                witness_found = False
                for label_mask in range(1, 1 << m):
                    images = union_domains(new, label_mask)
                    if images.bit_count() >= label_mask.bit_count():
                        continue
                    p = sum(1 << i for i in frozen_indices if label_mask >> i & 1)
                    t = label_mask ^ p
                    p_images = union_domains(base, p)
                    sigma = p_images.bit_count() - p.bit_count()
                    assert 0 <= sigma < t.bit_count()
                    s = ground ^ p_images
                    rank_m = matching_rank(dm, s)
                    rank_f_complement = matching_rank(df, ground ^ p_images)
                    rank_reserve = min(r, p_images.bit_count() - (m-r) + rank_f_complement)
                    assert rank_m + rank_reserve <= r-1
                    witness_found = True
                    break
                assert witness_found
            tests += 1
    print(f"Random genuine-cube batch reconfigurations: {tests}")


def best_partial_assignment(domains, a):
    states = {0: {}}
    for label, d in enumerate(domains):
        nxt = dict(states)
        for used, assignment in states.items():
            for v in range(a):
                if d >> v & 1 and not used >> v & 1:
                    nxt[used | (1 << v)] = {**assignment, label: v}
        states = nxt
    used = max(states, key=int.bit_count)
    return states[used]


def check_global_optima():
    rng = Random(181)
    cases = obstructed = batch_tests = 0
    for n, a, b, samples in ((2, 3, 3, None), (3, 5, 5, 40)):
        xlabels, ylabels, nb = cube(n)
        xindex = {x: i for i, x in enumerate(xlabels)}
        m = len(xlabels)
        if samples is None:
            colorings = range(1 << (a*b))
        else:
            colorings = [rng.getrandbits(a*b) for _ in range(samples)]
        for coloring in colorings:
            red = [[bool(coloring >> (v*b+w) & 1) for w in range(b)]
                   for v in range(a)]
            best_g = {}
            for f in permutations(range(a), m):
                lists = [sum(1 << w for w in range(b)
                             if all(red[f[xindex[x]]][w] for x in nb[y]))
                         for y in ylabels]
                candidate = best_partial_assignment(lists, b)
                if len(candidate) > len(best_g):
                    best_g = {ylabels[i]: w for i, w in candidate.items()}
                if len(best_g) == m:
                    break
            cases += 1
            if len(best_g) == m:
                continue
            obstructed += 1
            missing = set(ylabels) - set(best_g)
            for zmask in range(1, 1 << m):
                z = {ylabels[i] for i in range(m) if zmask >> i & 1}
                if not z & missing:
                    continue
                frozen = {y: w for y, w in best_g.items() if y not in z}
                available = sorted(set(range(b)) - set(frozen.values()))
                for values in permutations(available, len(z)):
                    reassignment = {**frozen, **dict(zip(sorted(z), values))}
                    domains = [sum(1 << v for v in range(a)
                                   if all(red[v][reassignment[y]]
                                          for y in nb[x] if y in reassignment))
                               for x in xlabels]
                    assert matching_rank(domains, (1 << a)-1) < m
                    batch_tests += 1
    print(f"Global-optimality tests: {cases} colorings; {obstructed} deficient optima; "
          f"{batch_tests} improving odd reassignments rejected under full even rematching")



if __name__ == '__main__':
    check_abstract_systems()
    check_cube_balls()
    check_batch_reconfigurations()
    check_global_optima()
    print('All checks passed. No assertion of a dimension-uniform Ramsey bound.')
