#!/usr/bin/env python3
"""Audit the proved certificate/entropy lemmas, not EL or the Ramsey claim.

No optimizer or floating-point test is used to assert asymptotic existence.
The finite matrix and packing support checks use integers/Fractions; Shannon
identities are checked numerically after those exact partitions are built.
"""
from __future__ import annotations

from collections import defaultdict
from fractions import Fraction
from itertools import combinations, permutations, product
from math import comb, exp, fsum, log


def close(x: float, y: float, tol: float = 2e-10) -> None:
    assert abs(x-y) <= tol * max(1.0, abs(x), abs(y)), (x, y)


def subsets(xs, size):
    return combinations(tuple(xs), size)


def certificate_count_audit():
    cases = 0
    for m in range(1, 31):
        for n in range(2*m, 4*m+6):
            direct = sum(comb(m, i)*comb(n, i-1) for i in range(1, m+1))
            assert direct == comb(n+m, m-1)
            if m >= 2:
                # n/h = C with h=2m; deliberately use the loose proved bound.
                C = Fraction(n, 2*m)
                assert log(direct) <= m*log(6*exp(1)*float(C)) + 1e-10
            cases += 1
    return cases


def has_matching(lists):
    def rec(i, used):
        if i == len(lists):
            return True
        return any(rec(i+1, used | {v}) for v in lists[i] if v not in used)
    return rec(0, set())


def hall_certificate(lists, columns):
    """Return a deterministic (I,S), |S|=|I|-1, or None.

    The catalogue may contain extra columns not appearing in any row list.
    Enlarging the union to S retains the Hall assertion.
    """
    m = len(lists)
    for i in range(1, m+1):
        for I in combinations(range(m), i):
            union = set().union(*(lists[y] for y in I))
            if len(union) < i:
                S = set(union)
                for v in sorted(set(columns)-S):
                    if len(S) == i-1:
                        break
                    S.add(v)
                assert len(S) == i-1
                assert all(lists[y] <= S for y in I)
                return I, tuple(sorted(S))
    return None


def hall_support_audit():
    # Every 3 by 5 support matrix, not a selected family of sectors.
    rows, cols = 3, 5
    good = 0
    bad = 0
    for mask in range(1 << (rows*cols)):
        lists = [set(v for v in range(cols) if mask & (1 << (y*cols+v)))
                 for y in range(rows)]
        cert = hall_certificate(lists, range(cols))
        matching = has_matching(lists)
        assert matching == (cert is None)
        good += matching
        bad += not matching
    return good, bad


def q2_kernel(n, mode):
    a = [[Fraction(0) for _ in range(n)] for _ in range(n)]
    for x in range(n):
        for y in range(x+1, n):
            if mode == 'complete':
                w = Fraction(1)
            elif mode == 'cycle':
                w = Fraction(1) if (y-x in (1, n-1)) else Fraction(0)
            elif mode == 'bipartite':
                w = Fraction(1) if (x < n//2) != (y < n//2) else Fraction(0)
            elif mode == 'weighted':
                # Nonconstant, rational weights and genuine zeros.
                v = (x*x+3*x*y+y*y+2*x+y) % 7
                w = (Fraction(0), Fraction(1, 3), Fraction(1, 2),
                     Fraction(1), Fraction(2, 3), Fraction(1), Fraction(0))[v]
            elif mode == 'nearly_complete':
                w = Fraction(0) if (x, y) in {(0, 1), (1, 2), (2, 3)} else Fraction(1)
            else:
                raise ValueError(mode)
            a[x][y] = a[y][x] = w
    return a


def entropy(weights):
    Z = sum(weights, Fraction(0))
    if Z == 0:
        return 0.0
    return -fsum(float(w/Z)*log(float(w/Z)) for w in weights if w)


def packing_audit(n, mode):
    # Full Q_2 label set: internal edges 01,23; outer edges 02,13.
    # Full parity E={0,3}; O={1,2}. There are TWO genuine disjoint Q_1 blocks.
    a = q2_kernel(n, mode)
    omega = {}
    final_count = Fraction(0)
    for phi in permutations(range(n), 4):
        w = a[phi[0]][phi[1]] * a[phi[2]][phi[3]]
        if w:
            omega[phi] = w
            final_count += w*a[phi[0]][phi[2]]*a[phi[1]][phi[3]]
    if not omega:
        return 0, 0, 0
    Z0 = sum(omega.values(), Fraction(0))
    M = sum((a[x][y] for x in range(n) for y in range(n)), Fraction(0))
    assert M*M >= Z0
    packing_cost = log(float(M*M/Z0))
    fibres = defaultdict(dict)
    sector_weights = defaultdict(lambda: Fraction(0))
    for phi, w in omega.items():
        f = phi[0], phi[3]
        available = set(range(n))-set(f)
        common = {v for v in available if a[f[0]][v] and a[f[1]][v]}
        cert = hall_certificate([common, common], available)
        sector_weights[f] += w
        if cert is not None:
            fibres[cert][phi] = w
    # Independently sum the actual weighted injective odd extensions.
    parity_sum = Fraction(0)
    for x, z in permutations(range(n), 2):
        X = set(range(n))-{x, z}
        cs = [a[x][v]*a[z][v] for v in X]
        parity_sum += sum(cs, Fraction(0))**2-sum((v*v for v in cs), Fraction(0))
    assert parity_sum == final_count
    bad_Z = sum((sum(v.values(), Fraction(0)) for v in fibres.values()), Fraction(0))
    assert len(fibres) <= comb(n+2, 1)
    if final_count == 0:
        assert bad_Z == Z0
        assert max(sum(v.values(), Fraction(0)) for v in fibres.values())*comb(n+2, 1) >= Z0
    else:
        assert bad_Z < Z0

    # Exact B for these finite examples: minimum one-free-block partition
    # over all outside-block values having positive packing probability.
    B_values = []
    for free in range(2):
        outs = {phi[2*(1-free):2*(1-free)+2] for phi in omega}
        for outside in outs:
            U = set(range(n))-set(outside)
            z = sum((a[x][y] for x in U for y in U if x != y), Fraction(0))
            assert z > 0
            B_values.append(z)
    B = min(B_values)
    log_B = log(float(B))
    local_checks = 0
    fibres_checked = 0
    for cert, cell in fibres.items():
        Zc = sum(cell.values(), Fraction(0))
        pcell = Zc/Z0
        H = entropy(list(cell.values()))
        energy = fsum(float(w/Zc)*log(float(w)) for w in cell.values())
        close(H+energy, log(float(Zc)))
        marginal_entropies = 0.0
        marginal_KLs = 0.0
        for i in range(2):
            masses = defaultdict(lambda: Fraction(0))
            for phi, w in cell.items():
                masses[phi[2*i:2*i+2]] += w
            marginal_entropies += entropy(list(masses.values()))
            for block, mass in masses.items():
                p = mass/Zc
                q = a[block[0]][block[1]]/M
                marginal_KLs += float(p)*log(float(p/q))
        total_correlation = marginal_entropies-H
        assert total_correlation >= -1e-10
        close(marginal_KLs+total_correlation, packing_cost-log(float(pcell)))
        assert max(cell.values())/Zc <= 1/Zc
        # Selecting a certificate changes only the sector marginal, not
        # the conditional law of the original injective extension.
        f_selected = { (phi[0], phi[3]) for phi in cell }
        assert sum((sector_weights[f] for f in f_selected), Fraction(0)) == Zc
        for f in f_selected:
            assert all(phi in cell for phi in omega if (phi[0], phi[3]) == f)

        chain = 0.0
        for i in range(2):
            ref_h = defaultdict(lambda: Fraction(0))
            ref_hx = defaultdict(lambda: Fraction(0))
            cell_h = defaultdict(lambda: Fraction(0))
            cell_hx = defaultdict(lambda: Fraction(0))
            for phi, w in omega.items():
                history = phi[:2*i]
                block = phi[2*i:2*i+2]
                ref_h[history] += w
                ref_hx[(history, block)] += w
            for phi, w in cell.items():
                history = phi[:2*i]
                block = phi[2*i:2*i+2]
                cell_h[history] += w
                cell_hx[(history, block)] += w
            for history, zh in cell_h.items():
                D = 0.0
                Hi = 0.0
                Ei = 0.0
                for (hh, block), z in cell_hx.items():
                    if hh != history:
                        continue
                    p = z/zh
                    q = ref_hx[(history, block)]/ref_h[history]
                    wi = a[block[0]][block[1]]
                    # This is a past-conditioned bound, not just a bound
                    # conditional on all the other blocks.
                    assert q <= wi/B
                    D += float(p)*log(float(p/q))
                    Hi -= float(p)*log(float(p))
                    Ei += float(p)*log(float(wi))
                assert D >= -1e-11
                assert Hi+Ei >= log_B-D-2e-10
                chain += float(zh/Zc)*D
                local_checks += 1
        close(chain, -log(float(pcell)))
        fibres_checked += 1
    return len(omega), fibres_checked, local_checks


def selected_scale_audit():
    tests = 0
    worst_margin = float('inf')
    # The analytic lower bound is normalized by h, so no exponential
    # host adjacency matrix or giant count is materialized.
    for K in (512, 1024, 8192, 65536):
        for C in (K, 2*K, 16*K):
            rho = 0.5-4/K
            for d in (4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048):
                low = max(1, (64*d + K-1)//K)
                if low > d//4:
                    continue
                for k in sorted({low, (low+d//4)//2, d//4}):
                    b_inv = exp(-k*log(2))
                    # binom(b,2) <= b^2/2 is the proved error bound.
                    log_eta_up = (2*k-d-1)*log(2)-log(C-1)-k*log(rho)
                    eta_up = exp(log_eta_up) if log_eta_up > -745 else 0.0
                    assert eta_up < 0.5
                    assert eta_up <= 1/(2*(C-1)) + 1e-15
                    budget = (d*log(2)+log(C-1)
                              +(d-k/2)*log(rho)
                              +b_inv*log(1-eta_up)
                              -0.5*log(6*exp(1)*C))
                    margin = budget-k/5
                    assert margin >= -1e-10, (K, C, d, k, margin)
                    worst_margin = min(worst_margin, margin)
                    tests += 1
    # Elementary constants used in the all-dimensional proof.
    assert Fraction(56, 81) > Fraction(109, 160)
    assert Fraction(512, 63) < 9
    return tests, worst_margin


def main():
    c = certificate_count_audit()
    good, bad = hall_support_audit()
    packings = fibres = local = cases = 0
    for n in (4, 5, 6, 7):
        for mode in ('complete', 'cycle', 'bipartite', 'weighted', 'nearly_complete'):
            pp, ff, ll = packing_audit(n, mode)
            packings += pp
            fibres += ff
            local += ll
            cases += 1
    scales, margin = selected_scale_audit()
    print('PASS: exact Hall catalogue identity:', c, 'parameter pairs')
    print('PASS: all 32768 Boolean 3x5 list matrices:', good, 'matchable,', bad, 'Hall-certified')
    print('PASS: full integral Q_1-packing audits:', cases, 'weighted host cases,', packings, 'positive configurations')
    print('PASS: certificate-fibre entropy identities:', fibres, 'fibres;', local, 'conditional history inequalities')
    print('PASS: selected-scale, certificate-subtracted surplus:', scales, 'parameter choices')
    print('Smallest audited lower-bound margin over k/5, per h:', format(margin, '.12g'))
    print('NO CLAIM: summed EL, a uniform-in-T pressure bound, and R(Q_d)=O(2^d) remain unproved.')


if __name__ == '__main__':
    main()
