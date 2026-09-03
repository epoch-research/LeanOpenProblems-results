#!/usr/bin/env python3
"""Audit the terminal-cut obstruction, not the Erdős--Gallai conjecture.

No files are written. All arithmetic is integral or rational. The general
optimality and impossibility claims are proved in ResearchGlobalAbsorption.md;
finite checks here verify certificates and algebra, not a universal conjecture.
"""
import sys
sys.dont_write_bytecode = True

from collections import Counter
from fractions import Fraction
import hashlib
import json
from pathlib import Path

BASE = Path(__file__).resolve().parent
ALLOWED = {"ResearchGlobalAbsorption.md", "ResearchGlobalAbsorptionCheck.py"}
BASELINE_COUNT = 46
BASELINE_SHA256 = "2533c9865919368f7c1601baab8a11a9e77ea5bdee6b9b1c86f6e97b7e014c4d"
SPEC_SHA256 = "429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde"


def edge(a, b):
    assert a != b, "loop"
    return (a, b) if a < b else (b, a)


def piece_edges(vertices, closed):
    vertices = tuple(vertices)
    assert len(vertices) >= (3 if closed else 2)
    assert len(vertices) == len(set(vertices)), "not vertex-simple"
    result = [edge(a, b) for a, b in zip(vertices, vertices[1:])]
    if closed:
        result.append(edge(vertices[-1], vertices[0]))
    assert len(set(result)) == len(result)
    return result


def verify_partition(edges, vertices, cycles, paths=()):
    used = Counter()
    for pieces, closed in ((cycles, True), (paths, False)):
        for piece in pieces:
            assert set(piece) <= vertices
            used.update(piece_edges(piece, closed))
    assert used == Counter({e: 1 for e in edges}), "not an exact edge partition"


def degrees(vertices, edges):
    result = {v: 0 for v in vertices}
    for a, b in edges:
        assert a < b and a in result and b in result
        result[a] += 1
        result[b] += 1
    return result


def component_count(vertices, edges):
    adj = {v: set() for v in vertices}
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)
    unseen = set(vertices)
    count = 0
    while unseen:
        count += 1
        stack = [unseen.pop()]
        while stack:
            v = stack.pop()
            for w in adj[v]:
                if w in unseen:
                    unseen.remove(w)
                    stack.append(w)
    return count


def cut(edges, side):
    return {e for e in edges if (e[0] in side) != (e[1] in side)}


def build(k, h):
    assert k >= 1 and h >= 1
    uL, uR, u0 = range(3)
    next_id = 3

    def allocate(n):
        nonlocal next_id
        result = tuple(range(next_id, next_id + n))
        next_id += n
        return result

    AL, AR = allocate(6*k), allocate(6*k)
    BL, BR = allocate(2*k), allocate(2*k)
    WL, WR = AL + BL, AR + BR
    W = WL + WR
    R_vertices = set(range(next_id))
    junction = allocate(h+1)
    strands = tuple(allocate(8*k) for _ in range(h))
    G_vertices = set(range(next_id))
    root = next_id
    J_vertices = (G_vertices - {uL, uR, u0}) | {root}

    R = {edge(uL, w) for w in AL} | {edge(uR, w) for w in AR}
    R |= {edge(u, w) for u in (uL, uR, u0) for w in BL + BR}
    arms = {edge(junction[0], w) for w in WL}
    arms |= {edge(junction[-1], w) for w in WR}
    chain_edges = set()
    chain_paths = []
    for i in range(8*k):
        path = [junction[0]]
        for j in range(h):
            y = strands[j][i]
            chain_edges.add(edge(junction[j], y))
            chain_edges.add(edge(y, junction[j+1]))
            path.extend((y, junction[j+1]))
        chain_paths.append(tuple(path))
    H = arms | chain_edges
    G = H | R
    J = H | {edge(root, w) for w in W}
    assert not (H & R)

    x0, xh = junction[0], junction[-1]
    outside_paths = []
    for i in range(2*k):
        outside_paths.extend([
            (x0, AL[i], uL, BR[i], xh),
            (x0, BL[i], uR, AR[i], xh),
            (x0, AL[2*k+i], uL, BL[i], u0, BR[i], uR, AR[2*k+i], xh),
        ])
    outside_cycles = []
    for j in range(k):
        outside_cycles.extend([
            (x0, AL[4*k+2*j], uL, AL[4*k+2*j+1]),
            (xh, AR[4*k+2*j], uR, AR[4*k+2*j+1]),
        ])

    long_cycles = []
    for P, Q in zip(chain_paths[:6*k], outside_paths):
        assert P[0] == Q[0] == x0 and P[-1] == Q[-1] == xh
        assert set(P) & set(Q) == {x0, xh}
        long_cycles.append(P + tuple(reversed(Q[1:-1])))
    local_cycles = []
    for j in range(h):
        for i in range(6*k, 8*k, 2):
            local_cycles.append((junction[j], strands[j][i],
                                 junction[j+1], strands[j][i+1]))
    G_cycles = long_cycles + local_cycles + outside_cycles
    J_cycles = [(root, WL[i]) + chain_paths[i] + (WR[i],)
                for i in range(8*k)]

    return {
        "U": {uL, uR, u0}, "uL": uL, "uR": uR, "u0": u0,
        "AL": AL, "AR": AR, "BL": BL, "BR": BR,
        "W": W, "WL": WL, "WR": WR,
        "R_vertices": R_vertices, "G_vertices": G_vertices,
        "J_vertices": J_vertices, "H_vertices": G_vertices - {uL, uR, u0},
        "R": R, "H": H, "G": G, "J": J, "O": R | arms,
        "root": root, "junction": junction, "strands": strands,
        "outside_paths": outside_paths, "outside_cycles": outside_cycles,
        "long_cycles": long_cycles, "local_cycles": local_cycles,
        "G_cycles": G_cycles, "J_cycles": J_cycles,
    }


def audit_instance(k, h):
    d = build(k, h)
    b, tau = 8*k, 6*k
    Rdeg = degrees(d["R_vertices"], d["R"])
    Gdeg = degrees(d["G_vertices"], d["G"])
    Jdeg = degrees(d["J_vertices"], d["J"])
    Hdeg = degrees(d["H_vertices"], d["H"])
    assert component_count(d["R_vertices"], d["R"]) == 1
    assert component_count(d["G_vertices"], d["G"]) == 1
    assert component_count(d["J_vertices"], d["J"]) == 1
    assert all(v > 0 and v % 2 == 0 for v in Gdeg.values())
    assert all(v > 0 and v % 2 == 0 for v in Jdeg.values())
    assert {v for v, degree in Hdeg.items() if degree % 2} == set(d["W"])
    assert all(Hdeg[w] == 1 for w in d["W"])
    assert all(Rdeg[u] % 2 == 0 for u in d["U"])
    assert all(Rdeg[w] % 2 == 1 for w in d["W"])
    assert min(Fraction(Rdeg[u], len(d["W"])) for u in d["U"]) == Fraction(1, 4)
    assert min(Fraction(Rdeg[w], len(d["U"])) for w in d["W"]) == Fraction(1, 3)
    assert len(d["U"]) == 3 and len(d["W"]) == 16*k
    assert len(d["R"]) == 24*k
    assert len(d["G_vertices"]) == (8*k+1)*h + 16*k + 4
    assert len(d["J_vertices"]) == (8*k+1)*h + 16*k + 2
    assert len(d["G"]) == 16*k*h + 40*k
    assert len(d["J"]) == 16*k*h + 32*k
    assert len(d["G_vertices"]) - len(d["J_vertices"]) == 2

    side = {d["uL"]} | set(d["WL"])
    assert len(side & set(d["W"])) == b
    assert len(cut(d["R"], side)) == tau
    outside_side = side | {d["junction"][0]}
    outside_cut = cut(d["O"], outside_side)
    assert len(outside_cut) == tau
    for Q in d["outside_paths"]:
        assert len(set(piece_edges(Q, False)) & outside_cut) == 1
    assert len(d["outside_paths"]) == tau
    verify_partition(d["O"], d["R_vertices"] | {d["junction"][0], d["junction"][-1]},
                     d["outside_cycles"], d["outside_paths"])
    verify_partition(d["G"], d["G_vertices"], d["G_cycles"])
    verify_partition(d["J"], d["J_vertices"], d["J_cycles"])
    assert len(d["G_cycles"]) == 8*k + k*h
    assert len(d["J_cycles"]) == 8*k
    assert len(d["G_cycles"]) == b + h*(b-tau)//2
    # Integer-scaled signed-edge lower certificate. The paper's exhaustive
    # structural cycle classification proves validity for ALL simple cycles.
    # Here independently check its total and tightness on the exact partition.
    arms = d["O"] - d["R"]
    strand_edges = d["H"] - arms
    weight4 = {e: 0 for e in d["G"]}
    weight4.update({e: 1 for e in strand_edges})
    weight4.update({e: 2 for e in arms})
    weight4.update({e: -2*h for e in cut(d["R"], side)})
    assert sum(weight4.values()) == 4*(b + h*(b-tau)//2)
    assert all(sum(weight4[e] for e in piece_edges(C, True)) == 4
               for C in d["G_cycles"])
    assert Jdeg[d["root"]]//2 == len(d["J_cycles"])
    assert Counter(map(len, d["long_cycles"])) == Counter({2*h+4: 4*k, 2*h+8: 2*k})
    assert all(len(C) == 4 for C in d["local_cycles"] + d["outside_cycles"])
    assert 2*len(d["G_cycles"]) < len(d["G_vertices"])

    # Audit the three cycle classes in the exhibited partition.
    strand_segment = {y: j for j, row in enumerate(d["strands"]) for y in row}
    ell = t = 0
    local_counts = Counter()
    x0, xh = d["junction"][0], d["junction"][-1]
    outside_end_counts = Counter()
    for C in d["G_cycles"]:
        used = Counter(strand_segment[y] for y in C if y in strand_segment)
        if not used:
            for x in (x0, xh):
                outside_end_counts[x] += (x in C)
            t += (x0 in C and xh in C)
        elif len(used) == h and all(v == 1 for v in used.values()):
            ell += 1
        else:
            assert len(used) == 1 and list(used.values()) == [2] and len(C) == 4
            local_counts[next(iter(used))] += 1
    assert ell == tau and t == 0
    assert all(local_counts[j] == (b-ell)//2 == k for j in range(h))
    assert outside_end_counts[x0] == outside_end_counts[xh] == (b-ell)//2
    assert ell + 2*t <= tau

    share = sum((Fraction(Rdeg[v], Gdeg[v]) for v in d["R_vertices"]), Fraction())
    assert share == 9*k+3
    return {
        "k": k, "h": h, "n_G": len(d["G_vertices"]), "m_G": len(d["G"]),
        "c_G_certificate_and_proved_lower_bound": len(d["G_cycles"]),
        "c_J_certificate_and_root_lower_bound": len(d["J_cycles"]),
        "surcharge": k*h, "rank_deleted": 2, "reservoir_degree_share": str(share),
        "surcharge_per_deleted_rank": str(Fraction(k*h, 2)),
        "surcharge_per_reservoir_share": str(Fraction(k*h, share)),
    }


def exhaustive_reservoir_cuts():
    """All 2^19-2 nontrivial cuts, independent of the conductance proof."""
    d = build(1, 1)
    n = len(d["R_vertices"])
    assert n == 19 and d["R_vertices"] == set(range(n))
    adj = [0]*n
    degree = [0]*n
    for a, b in d["R"]:
        adj[a] |= 1 << b
        adj[b] |= 1 << a
        degree[a] += 1
        degree[b] += 1
    full = (1 << n)-1
    terminal_mask = full ^ 7
    volume = [0]*(1 << n)
    boundary = [0]*(1 << n)
    total_volume = sum(degree)
    best_num, best_den = 1, 1
    balanced_min = len(d["R"])
    count = balanced_count = 0
    for mask in range(1, full):
        bit = mask & -mask
        v = bit.bit_length()-1
        previous = mask ^ bit
        volume[mask] = volume[previous] + degree[v]
        boundary[mask] = boundary[previous] + degree[v] - 2*(adj[v] & previous).bit_count()
        den = min(volume[mask], total_volume-volume[mask])
        assert den > 0 and 4*boundary[mask] >= den
        if boundary[mask]*best_den < best_num*den:
            best_num, best_den = boundary[mask], den
        terminal_count = (mask & terminal_mask).bit_count()
        assert boundary[mask] % 2 == terminal_count % 2
        if terminal_count == 8:
            balanced_min = min(balanced_min, boundary[mask])
            balanced_count += 1
        count += 1
    assert Fraction(best_num, best_den) == Fraction(1, 4)
    assert balanced_min == 6 and count == (1 << 19)-2
    return {"nontrivial_cuts": count, "balanced_terminal_cuts": balanced_count,
            "exact_conductance": str(Fraction(best_num, best_den)),
            "minimum_balanced_terminal_cut": balanced_min}


def audit_ledger_algebra():
    """Check the lower-bound arithmetic on feasible integer ledgers."""
    count = 0
    for b in range(1, 33):
        for tau in range(b % 2, b, 2):
            for ell in range(b % 2, tau+1, 2):
                for t in range((tau-ell)//2+1):
                    assert ell + 2*t <= tau and (b-ell) % 2 == 0
                    for h in range(1, 9):
                        raw = ell + h*(b-ell)//2 + b-ell-t
                        middle = b + (h*(b-ell)-(tau-ell))//2
                        target = b + h*(b-tau)//2
                        assert raw >= middle >= target
                        assert middle-target == (h-1)*(tau-ell)//2
                        count += 1
    return count


def preserved_files():
    h = hashlib.sha256()
    count = 0
    for p in sorted(BASE.rglob("*")):
        relative = p.relative_to(BASE).as_posix()
        if p.is_file() and relative not in ALLOWED:
            h.update(("Submission/" + relative).encode() + b"\0" +
                     hashlib.sha256(p.read_bytes()).digest())
            count += 1
    assert count == BASELINE_COUNT, (count, BASELINE_COUNT)
    assert h.hexdigest() == BASELINE_SHA256, "pre-existing Submission files changed"
    assert hashlib.sha256((BASE / "Spec.lean").read_bytes()).hexdigest() == SPEC_SHA256
    return count


def main():
    protected = preserved_files()
    parameters = [(k, h) for k in list(range(1, 9)) + [16, 32]
                  for h in (1, 2, 3, 7, 20)]
    parameters += [(1, 1000), (32, 50), (100, 4)]
    instances = [audit_instance(k, h) for k, h in parameters]
    report = {
        "status": "Selected GA lemma refuted by the parametric paper proof; no universal EG constant proved.",
        "exact_partition_instance_checks": len(instances),
        "exhaustive_R1_cut_audit": exhaustive_reservoir_cuts(),
        "feasible_integer_ledger_checks": audit_ledger_algebra(),
        "stress_certificates": instances[-3:],
        "preexisting_Submission_files_unchanged": protected,
        "Spec_SHA256": SPEC_SHA256,
        "verification_scope": "Finite audits of explicit certificates and algebra; not finite-test settlement or an independent optimizer.",
    }
    assert preserved_files() == protected
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
