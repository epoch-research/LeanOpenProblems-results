#!/usr/bin/env python3
"""Independent verifier for the Singer half-tag audit.

Does not import the generator or invoke/trust the C++ solver. Reconstructs the
finite field, perfect differences, all triple constraints, and signed fibers.
UNSAT certificates are exhaustive search trees with independently recomputed
one-variable domains (roots tested by enumeration, not modular division).
SAT witnesses are checked by all repeated triples directly in Z/(v*k).
Only Python's standard library is used; q=17 tree checking defaults to the
separate native checker for speed. --python-trees avoids even that dependency.
"""
from __future__ import annotations
import argparse
from collections import Counter
from functools import lru_cache
import gzip
import hashlib
import itertools
import json
import math
from pathlib import Path
import subprocess
import tempfile
import time

HERE = Path(__file__).resolve().parent
OUT = HERE / "singer_half_tag_results"
SPEC_SHA256 = "fa08ffd0daf6d26c138eb7da5a4186d0abd9155428d0c4528526a570b398d860"
FAST_Q17_TREES = True  # --python-trees uses the same transparent checker as q=11 instead.
FAST_CHECKER = Path(tempfile.gettempdir()) / "singer_half_tag_tree_checker"


def sha(data):
    return hashlib.sha256(data).hexdigest()


def check_construction(c):
    q, v, k, S = (c[x] for x in ("q", "v", "k", "S"))
    assert q % 6 == 5 and v == q*q+q+1 and k == (q-1)//2 and c["M"] == v*k
    assert math.gcd(v, k) == 1 and all(q % d for d in range(2, math.isqrt(q)+1))
    a, b, d = c["polynomial_low_coefficients"]
    assert all((x*x*x+d*x*x+b*x+a) % q != 0 for x in range(q))
    # Independent closed-form reduction using x^3=-a-bx-dx^2,
    # x^4=da+(db-a)x+(d^2-b)x^2.
    def mul(u, w):
        h0 = u[0]*w[0]
        h1 = u[0]*w[1]+u[1]*w[0]
        h2 = u[0]*w[2]+u[1]*w[1]+u[2]*w[0]
        h3 = u[1]*w[2]+u[2]*w[1]
        h4 = u[2]*w[2]
        return ((h0-a*h3+d*a*h4) % q,
                (h1-b*h3+(d*b-a)*h4) % q,
                (h2-d*h3+(d*d-b)*h4) % q)
    def power(u, e):
        w = (1, 0, 0)
        for digit in bin(e)[2:]:
            w = mul(w, w)
            if digit == "1":
                w = mul(w, u)
        return w
    g = tuple(c["generator_coefficients"])
    assert c["generator_encoded"] == sum(x*q**i for i, x in enumerate(g))
    z = (1, 0, 0)
    seen, logs = set(), []
    for exponent in range(q**3-1):
        assert z not in seen and z != (0, 0, 0)
        seen.add(z)
        zq = power(z, q)
        zqq = power(zq, q)
        tr = tuple((z[i]+zq[i]+zqq[i]) % q for i in range(3))
        assert tr[1:] == (0, 0)
        if tr == (0, 0, 0):
            logs.append(exponent % v)
        z = mul(z, g)
    assert z == (1, 0, 0) and len(seen) == q**3-1
    assert sorted(set(logs)) == S and Counter(logs) == Counter({s: q-1 for s in S})
    assert len(S) == q+1
    differences = [0]*v
    for x in S:
        for y in S:
            if x != y:
                differences[(x-y) % v] += 1
    assert differences == [0]+[1]*(v-1) == c["perfect_difference_counts"]
    return {"q": q, "primitive_cycle_checked": q**3-1,
            "trace_zero_nonzero_elements": len(logs), "nonzero_differences_once": v-1}


def canonical(row):
    out = tuple(row)
    if next(x for x in out if x) < 0:
        out = tuple(-x for x in out)
    return out


def reconstruct(c, record):
    deleted = record["deleted_indices"]
    S, v, k = c["S"], c["v"], c["k"]
    assert deleted == sorted(set(deleted)) and all(0 <= i < len(S) for i in deleted)
    retained = [i for i in range(len(S)) if i not in deleted]
    T = [S[i] for i in retained]
    n = len(T)
    assert record["T"] == T and record["n"] == n
    assert record["deleted_points"] == [S[i] for i in deleted]
    assert record["retained_indices"] == retained
    fibers = [[] for _ in range(v)]
    for i in range(n):
        for j in range(i, n):
            for l in range(j, n):
                counts = [0]*n
                for t in (i, j, l):
                    counts[t] += 1
                fibers[(T[i]+T[j]+T[l]) % v].append(counts)
    constraints = set()
    raw = 0
    for triples in fibers:
        for i in range(len(triples)):
            for j in range(i+1, len(triples)):
                raw += 1
                constraints.add(canonical(x-y for x, y in zip(triples[i], triples[j])))
    rows = sorted(constraints)
    assert record["triple_multisets"] == sum(map(len, fibers)) == math.comb(n+2, 3)
    assert record["raw_collision_pairs"] == raw
    hist = {str(size): count for size, count in sorted(Counter(map(len, fibers)).items())}
    assert record["triple_fiber_histogram"] == hist
    # Independently enumerate all ordered signed triples and reduce to vectors.
    signed = [set() for _ in range(v)]
    for i in range(n):
        for j in range(n):
            for l in range(n):
                row = [0]*n
                row[i] += 1
                row[j] += 1
                row[l] -= 1
                signed[(T[i]+T[j]-T[l]) % v].add(tuple(row))
    assert sum(map(len, signed)) == n*n*(n-1)//2+n
    hist = {str(size): count for size, count in sorted(Counter(map(len, signed)).items())}
    assert record["signed_fiber_histogram"] == hist
    assert record["signed_fiber_max"] == max(map(len, signed))
    text = f"{n} {k} {len(rows)}\n" + "".join(" ".join(map(str, r))+"\n" for r in rows)
    assert sha(text.encode()) == record["input_sha256"]
    return T, rows, signed


@lru_cache(None)
def compile_fast_checker():
    subprocess.run(["g++", "-O3", "-std=c++17", "-Wall", "-Wextra", "-pedantic",
                    str(HERE/"singer_half_tag_verify_tree.cpp"), "-o", str(FAST_CHECKER)], check=True)


def fast_tree(n, k, rows, record, raw):
    compile_fast_checker()
    text = f"{n} {k} {len(rows)}\n" + "".join(" ".join(map(str, r))+"\n" for r in rows)
    with tempfile.TemporaryDirectory(prefix="singer_tree_check_") as td:
        input_path, proof_path = Path(td)/"independent_input.txt", Path(td)/"proof.txt"
        input_path.write_text(text)
        proof_path.write_bytes(raw)
        answer = json.loads(subprocess.check_output([str(FAST_CHECKER), str(input_path), str(proof_path)]))
    assert answer["covered_assignments"] == k**(n-1) == record["normalized_assignments"]
    assert all(answer[key] == record[key] for key in answer)
    return answer


def check_tree(n, k, rows, record):
    raw = (OUT / record["proof"]).read_bytes()
    raw = gzip.decompress(raw)
    assert sha(raw) == record["proof_sha256_uncompressed"]
    assert len(raw) == record["proof_bytes_uncompressed"]
    if FAST_Q17_TREES and k == 8:
        return fast_tree(n, k, rows, record, raw)
    header, *lines = raw.decode().splitlines()
    assert header == f"SHTC1 {n} {k} {len(rows)}"
    tokens = iter(map(int, lines))
    terms = [[(i, a) for i, a in enumerate(r) if a] for r in rows]
    values = [None]*n
    values[0] = 0
    full = (1 << k)-1
    # This table enumerates the roots; it is independent of the gcd algorithm.
    roots = [[sum(1 << x for x in range(k) if (a*x+b) % k == 0)
              for b in range(k)] for a in range(k)]
    stats = {"nodes": 0, "conflict_leaves": 0, "max_depth_after_fixed_tag": 0}

    def visit(assigned):
        token = next(tokens)  # A truncated proof raises StopIteration.
        stats["nodes"] += 1
        stats["max_depth_after_fixed_tag"] = max(stats["max_depth_after_fixed_tag"], assigned-1)
        domains = [full]*n
        conflict = False
        for row in terms:
            unassigned = []
            total = 0
            for i, a in row:
                if values[i] is None:
                    unassigned.append((i, a))
                else:
                    total += a*values[i]
            if not unassigned and total % k == 0:
                conflict = True
                break
            if len(unassigned) == 1:
                i, a = unassigned[0]
                domains[i] &= ~roots[a % k][total % k]
                if domains[i] == 0:
                    conflict = True
                    break
        if conflict:
            assert token == -1, "conflict node must be a leaf"
            stats["conflict_leaves"] += 1
            return k**(n-assigned)
        assert 0 <= token < n and values[token] is None, "branch on an unassigned variable"
        assert assigned < n, "a purported refutation reached a satisfying assignment"
        allowed = [x for x in range(k) if domains[token] & (1 << x)]
        covered = (k-len(allowed))*k**(n-assigned-1)
        for x in allowed:
            values[token] = x
            covered += visit(assigned+1)
        values[token] = None
        assert covered == k**(n-assigned)
        return covered

    covered = visit(1)
    assert next(tokens, None) is None, "surplus proof nodes"
    assert covered == k**(n-1) == record["covered_assignments"] == record["normalized_assignments"]
    assert all(stats[key] == record[key] for key in stats)
    return dict(stats, covered_assignments=covered)


def check_sat(T, k, v, record):
    tags = record["tags"]
    n = len(T)
    assert len(tags) == n and tags[0] == 0 and all(0 <= c < k for c in tags)
    M = k*v
    inverse_k = pow(k, -1, v)
    A = [c+k*((s-c)*inverse_k % v) for s, c in zip(T, tags)]
    assert len(set(A)) == n
    assert all(0 <= a < M and a % v == s and a % k == c for a, s, c in zip(A, T, tags))
    sums = set()
    for i in range(n):
        for j in range(i, n):
            for l in range(j, n):
                residue = (A[i]+A[j]+A[l]) % M
                assert residue not in sums, ("repeated-triple collision", i, j, l)
                sums.add(residue)
    pairs = set()
    for i in range(n):
        for j in range(i, n):
            residue = (A[i]+A[j]) % M
            assert residue not in pairs
            pairs.add(residue)
    assert len(sums) == math.comb(n+2, 3)
    expected = {"CRT_A_in_T_order": A, "M": M, "distinct_triple_sums": len(sums),
                "triple_multisets": len(sums), "distinct_pair_sums": len(pairs), "strong_B3": True}
    assert record["verification"] == expected
    return {"n": n, "M": M, "triple_sums_checked": len(sums)}


def check_saturated_linear(k, rows, signed, cert):
    if not cert or cert["target_constraint"] is None:
        return False
    n = len(rows[0])
    total = [0]*n
    core = {cert["target_constraint"]}
    by_row = {r: i for i, r in enumerate(rows)}
    for term in cert["fiber_multipliers"]:
        vectors = signed[term["h"]]
        assert len(vectors) == k
        for vector in vectors:
            total = [x+term["multiplier"]*y for x, y in zip(total, vector)]
        for a, b in itertools.combinations(vectors, 2):
            core.add(by_row[canonical(x-y for x, y in zip(a, b))])
    assert all((x-y) % k == 0 for x, y in zip(total, rows[cert["target_constraint"]]))
    assert k*(k-1)//2 % k == 0
    assert cert["core_constraint_ids"] == sorted(core)
    return True


def independent_rank(rows, p):
    matrix = [[x % p for x in row] for row in rows]
    rank = 0
    for col in range(len(matrix[0])):
        pivots = [j for j in range(rank, len(matrix)) if matrix[j][col]]
        if not pivots:
            continue
        j = pivots[0]
        matrix[rank], matrix[j] = matrix[j], matrix[rank]
        inv = pow(matrix[rank][col], -1, p)
        matrix[rank] = [x*inv % p for x in matrix[rank]]
        for j in range(len(matrix)):
            if j != rank:
                scale = matrix[j][col]
                matrix[j] = [(x-scale*y) % p for x, y in zip(matrix[j], matrix[rank])]
        rank += 1
    return rank


def verify_cores():
    data = json.loads((OUT/"q11_cores.json").read_text())
    c = data["construction"]
    construction = check_construction(c)
    summary = []
    for case in data["cases"]:
        T, rows, signed = reconstruct(c, case)
        k, n = c["k"], len(T)
        core = case["core"]
        ids = core["constraint_ids"]
        assert ids == sorted(set(ids)) and all(0 <= j < len(rows) for j in ids)
        selected = [rows[j] for j in ids]
        assert [list(r) for r in selected] == core["rows"]
        text = f"{n} {k} {len(selected)}\n" + "".join(" ".join(map(str, r))+"\n" for r in selected)
        assert sha(text.encode()) == core["input_sha256"]
        assert core["status"] == "UNSAT"
        checked = check_tree(n, k, selected, core)
        for row, witness in zip(selected, core["witnesses"]):
            left, right = witness["left"], witness["right"]
            assert len(left) == len(right) == 3 and left != right
            assert all(0 <= j < n for j in left+right)
            assert sum(T[j] for j in left) % c["v"] == witness["base_sum"] == sum(T[j] for j in right) % c["v"]
            assert tuple(left.count(j)-right.count(j) for j in range(n)) == row
        assert core["rank_mod_5"] == independent_rank(selected, k)
        assert {x["removed_constraint"] for x in core["criticality_witnesses"]} == set(ids)
        for item in core["criticality_witnesses"]:
            tags = item["tags_satisfying_other_core_constraints"]
            assert len(tags) == n and tags[0] == 0 and all(0 <= t < k for t in tags)
            for j in ids:
                value = sum(x*y for x, y in zip(rows[j], tags)) % k
                assert (value == 0) == (j == item["removed_constraint"])
        expected_saturated = [{"h": h, "vectors": [list(row) for row in sorted(signed[h])],
                               "sum_row": [sum(row[j] for row in signed[h]) for j in range(n)],
                               "rhs": k*(k-1)//2 % k}
                              for h in range(c["v"]) if len(signed[h]) == k]
        assert case["saturated_fibers"] == expected_saturated
        check_saturated_linear(k, rows, signed, case["saturated_linear_test"])
        cert = core["D4_certificate"]
        if cert is not None:
            forms = cert["twice_linear_forms"]
            assert k == 5 and len(forms) == 4 and all(len(row) == n for row in forms)
            pairs = {(i, j, sign) for i in range(4) for j in range(i+1, 4) for sign in (1, -1)}
            assert {(x["i"], x["j"], x["sign"]) for x in cert["pair_mapping"]} == pairs
            assert {x["constraint_id"] for x in cert["pair_mapping"]} == set(ids)
            for item in cert["pair_mapping"]:
                i, j, sign = item["i"], item["j"], item["sign"]
                rhs = rows[item["constraint_id"]]
                assert item["row_sign"] in (-1, 1)
                assert all(a+sign*b == 2*item["row_sign"]*d for a, b, d in zip(forms[i], forms[j], rhs))
            orbits = {tuple(sorted({x, (-x) % k})) for x in range(k)}
            assert sorted(orbits) == [tuple(x) for x in cert["negation_orbits_mod_5"]]
            assert len(orbits) < len(forms) and math.gcd(2, k) == 1
            assert not any(all((xs[i]+sign*xs[j]) % k for i, j, sign in pairs)
                           for xs in itertools.product(range(k), repeat=4))
        summary.append({"deleted_indices": case["deleted_indices"], "constraints": len(ids),
                        "rank_mod_5": core["rank_mod_5"], "inclusion_minimal": True,
                        "D4_identity_checked": cert is not None, "tree_nodes": checked["nodes"]})
    return {"file": "q11_cores.json", "construction": construction, "cores_checked": summary}


def verify_q17_scope(data):
    c = data["construction"]
    S, q, v, k = (c[key] for key in ("S", "q", "v", "k"))
    assert (q, v, k) == (17, 307, 8) and math.gcd(q, c["M"]) == 1 and q % k == 1
    permutation = [S.index(q*s % v) for s in S]
    assert permutation == data["symmetry"]["permutation_of_S_indices"]
    expected = {}
    for deletion in itertools.combinations(range(18), 3):
        orbit = {tuple(sorted(S.index(pow(q, e, v)*S[i] % v) for i in deletion)) for e in range(3)}
        assert len(orbit) in (1, 3)
        expected[min(orbit)] = sorted(orbit)
    actual = data["symmetry"]["orbit_partition"]
    assert len(actual) == len(expected) == 276
    assert {tuple(o["representative"]): [tuple(d) for d in o["members"]] for o in actual} == expected
    assert sum(map(len, expected.values())) == math.comb(18, 3)
    profiles = {tuple(p["representative"]): p for p in data["profiles"]}
    assert len(data["profiles"]) == len(profiles) == len(expected) and set(profiles) == set(expected)
    # Independently check the capacity/profile claims, including unsearched orbits.
    for deletion, profile in profiles.items():
        T = [s for i, s in enumerate(S) if i not in deletion]
        fibers = [[] for _ in range(v)]
        for triple in itertools.combinations_with_replacement(range(15), 3):
            row = tuple(triple.count(j) for j in range(15))
            fibers[sum(T[i] for i in triple) % v].append(row)
        rows = {canonical(x-y for x, y in zip(a, b)) for fiber in fibers for a, b in itertools.combinations(fiber, 2)}
        signed = [set() for _ in range(v)]
        for a, b, d in itertools.product(range(15), repeat=3):
            vector = [0]*15
            vector[a] += 1
            vector[b] += 1
            vector[d] -= 1
            signed[(T[a]+T[b]-T[d]) % v].add(tuple(vector))
        assert profile["constraints"] == len(rows)
        assert profile["signed_fiber_max"] == max(map(len, signed)) <= k
        assert profile["saturated_fibers"] == sum(len(f) == k for f in signed)
    seen = {tuple(r["deleted_indices"]) for r in data["instances"]}
    assert seen <= set(expected)
    order = [tuple(d) for d in data["requested_representative_order"]]
    assert len(order) == len(set(order)) == 276 and set(order) == set(expected)
    assert [tuple(r["deleted_indices"]) for r in data["instances"]] == order[:len(seen)]
    priority = [tuple(d) for d in data["target_priority_representatives"]]
    assert priority == order[:len(priority)]
    assert {tuple(d) for d in data["unattempted_representatives"]} == set(expected)-seen
    weighted = Counter()
    for r in data["instances"]:
        assert r["n"] == 15 and len(r["deleted_indices"]) == 3
        assert [tuple(d) for d in r["orbit_members"]] == expected[tuple(r["deleted_indices"])]
        weighted[r["status"]] += len(r["orbit_members"])
        assert 0 < r["timeout_ms"] <= data["per_representative_cap_ms"] == 5000
    weighted["UNTESTED_BUDGET"] = sum(len(orbit) for rep, orbit in expected.items() if rep not in seen)
    summary = data["summary"]
    assert dict(weighted) == summary["original_deletion_status_counts_via_valid_symmetry"]
    assert sum(weighted.values()) == 816
    assert summary["representative_status_counts"] == dict(Counter(r["status"] for r in data["instances"]))
    assert summary["all_816_deletions_UNSAT"] == (weighted["UNSAT"] == 816)
    assert summary["representatives_attempted"] == len(seen)
    assert summary["unattempted_representatives"] == 276-len(seen)
    assert summary["phase_wall_seconds"] <= data["budget_seconds"] == 300
    assert summary["max_signed_fiber_all_deletions_via_symmetry"] == max(p["signed_fiber_max"] for p in profiles.values())
    return {"Frobenius_orbits_independently_checked": len(expected),
            "all_deletions_in_partition": 816, "original_deletion_status_counts_via_valid_symmetry": dict(weighted),
            "time_cap_seconds": data["budget_seconds"], "recorded_search_phase_seconds": summary["phase_wall_seconds"]}


@lru_cache(None)
def verify_results(filename):
    if filename == "q11_cores.json":
        return verify_cores()
    data = json.loads((OUT/filename).read_text())
    c = data["construction"]
    construction = check_construction(c)
    counts = Counter()
    nodes, covered, linear = 0, 0, 0
    seen = set()
    for record in data["instances"]:
        key = tuple(record["deleted_indices"])
        assert key not in seen
        seen.add(key)
        T, rows, signed = reconstruct(c, record)
        if record["status"] == "SAT":
            check_sat(T, c["k"], c["v"], record)
        elif record["status"] == "UNSAT":
            checked = check_tree(len(T), c["k"], rows, record)
            nodes += checked["nodes"]
            covered += checked["covered_assignments"]
        else:
            assert record["status"] == "TIMEOUT" and "proof" not in record
        linear += check_saturated_linear(c["k"], rows, signed, record.get("saturated_linear_test"))
        counts[record["status"]] += 1
    if filename == "q11_three_deletions.json":
        assert seen == set(itertools.combinations(range(12), 3)), "all 220 deletions required"
        assert data["summary"]["status_counts"] == dict(counts)
        assert data["summary"]["saturated_linear_obstructions"] == linear
    report = {"file": filename, "construction": construction, "instances": len(seen),
              "status_counts": dict(counts), "UNSAT_tree_nodes_checked": nodes,
              "UNSAT_normalized_assignments_covered": covered, "linear_obstructions_checked": linear}
    if filename == "q11_retention.json":
        upper = verify_results("q11_three_deletions.json")
        assert upper["status_counts"] == {"UNSAT": 220}
        maximum = data["summary"]["exact_maximum_retention"]
        assert maximum <= 8
        assert any(r["status"] == "SAT" and r["n"] == maximum for r in data["instances"])
        for n in range(maximum+1, 9):
            excluded = {tuple(r["deleted_indices"]) for r in data["instances"] if r["n"] == n and r["status"] == "UNSAT"}
            assert excluded == set(itertools.combinations(range(12), 12-n))
        assert not any(r["status"] == "SAT" and r["n"] > maximum for r in data["instances"])
        report["exact_maximum_retention_verified"] = maximum
    if filename == "q17_three_deletions.json":
        report.update(verify_q17_scope(data))
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("files", nargs="*", default=["q11_three_deletions.json", "q11_retention.json", "q11_cores.json", "q17_three_deletions.json"])
    parser.add_argument("--python-trees", action="store_true", help="check q=17 trees in Python too (much slower)")
    parser.add_argument("--write-report", action="store_true", help="overwrite the saved verification.json; default only prints")
    args = parser.parse_args()
    global FAST_Q17_TREES
    FAST_Q17_TREES = not args.python_trees
    start = time.monotonic()
    assert sha((HERE/"Spec.lean").read_bytes()) == SPEC_SHA256
    results = [verify_results(f) for f in args.files]
    report = {"status": "PASS", "results": results, "seconds": time.monotonic()-start,
              "Spec_unchanged_sha256": SPEC_SHA256}
    if args.write_report:
        (OUT/"verification.json").write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
